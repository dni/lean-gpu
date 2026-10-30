/* farkas [--certs] PROBLEMS [OUT] [ITERS]
 *
 * Reads a batch of linear systems, searches all of them for Farkas
 * certificates at once (on the GPU when built with `make cuda`), turns each
 * result into an exact integer certificate (exact.c), and writes a Lean file that proves
 * every system it found a certificate for infeasible. With --certs, OUT gets
 * one line per problem instead, `name c1 ... cm` or `name -` (used by the
 * farkas tactic).
 *
 * Input format: blank lines and `#` comments are ignored. Each problem is a
 * header line `name m n` followed by m lines of n coefficients and a bound,
 * meaning a1*x1 + ... + an*xn <= bound. */
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "farkas.h"
#include "exact.h"

static int next_token(FILE *f, char *buf, size_t len) {
    int c;
    for (;;) {
        while ((c = fgetc(f)) != EOF && isspace(c)) {}
        if (c != '#') break;
        while ((c = fgetc(f)) != EOF && c != '\n') {}
    }
    if (c == EOF) return 0;
    size_t k = 0;
    do {
        if (k + 1 < len) buf[k++] = (char)c;
    } while ((c = fgetc(f)) != EOF && !isspace(c));
    buf[k] = 0;
    return 1;
}

static long long next_int(FILE *f) {
    char tok[64];
    if (!next_token(f, tok, sizeof tok)) {
        fprintf(stderr, "unexpected end of input\n");
        exit(1);
    }
    return strtoll(tok, NULL, 10);
}

static void read_batch(FILE *f, Batch *bt) {
    int cap = 16, capA = 256, capB = 64, totA = 0, totB = 0;
    memset(bt, 0, sizeof *bt);
    bt->m = malloc(sizeof(int) * cap);
    bt->n = malloc(sizeof(int) * cap);
    bt->offA = malloc(sizeof(int) * cap);
    bt->offB = malloc(sizeof(int) * cap);
    bt->name = malloc(sizeof(*bt->name) * cap);
    bt->A = malloc(sizeof(long long) * capA);
    bt->b = malloc(sizeof(long long) * capB);

    char tok[64];
    while (next_token(f, tok, sizeof tok)) {
        if (bt->count == cap) {
            cap *= 2;
            bt->m = realloc(bt->m, sizeof(int) * cap);
            bt->n = realloc(bt->n, sizeof(int) * cap);
            bt->offA = realloc(bt->offA, sizeof(int) * cap);
            bt->offB = realloc(bt->offB, sizeof(int) * cap);
            bt->name = realloc(bt->name, sizeof(*bt->name) * cap);
        }
        int p = bt->count++;
        snprintf(bt->name[p], sizeof bt->name[p], "%s", tok);
        int m = (int)next_int(f), n = (int)next_int(f);
        bt->m[p] = m;
        bt->n[p] = n;
        bt->offA[p] = totA;
        bt->offB[p] = totB;
        while (totA + m * n > capA) bt->A = realloc(bt->A, sizeof(long long) * (capA *= 2));
        while (totB + m > capB) bt->b = realloc(bt->b, sizeof(long long) * (capB *= 2));
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) bt->A[totA + i * n + j] = next_int(f);
            bt->b[totB + i] = next_int(f);
        }
        totA += m * n;
        totB += m;
    }
}

static void lean_ident(const char *name, char *out, size_t len) {
    size_t k = 0;
    if (!isalpha((unsigned char)name[0])) out[k++] = 'p';
    for (; *name && k + 1 < len; name++)
        out[k++] = isalnum((unsigned char)*name) ? *name : '_';
    out[k] = 0;
}

/* Problems up to this many numbers are written as readable lists; larger
 * ones are packed into single Nat literals (see LeanGpu/Packed.lean), which
 * Lean elaborates and checks much faster. */
#define PLAIN_MAX 64

static void emit_plain(FILE *out, const char *id, const long long *A, const long long *b,
                       int m, int n, mpz_t *cert) {
    fprintf(out, "\ndef %s_rows : List Row := [\n", id);
    for (int i = 0; i < m; i++) {
        fprintf(out, "  ⟨[");
        for (int j = 0; j < n; j++) fprintf(out, "%s%lld", j ? ", " : "", A[i * n + j]);
        fprintf(out, "], %lld⟩%s\n", b[i], i + 1 < m ? "," : "]");
    }
    fprintf(out, "\ntheorem %s_infeasible : ∀ x : List Int, ¬ ∀ r ∈ %s_rows, r.Holds x :=\n", id, id);
    fprintf(out, "  farkas_sound %d %s_rows [", n, id);
    for (int i = 0; i < m; i++) gmp_fprintf(out, "%s%Zd", i ? ", " : "", cert[i]);
    fprintf(out, "] (by decide +kernel)\n");
}

/* code = sum of d[i] * 2^(bits * i); returns bits, the smallest that fits every digit. */
static size_t pack(mpz_t code, mpz_t *d, int k) {
    size_t bits = 1;
    for (int i = 0; i < k; i++)
        if (mpz_sgn(d[i]) && mpz_sizeinbase(d[i], 2) > bits) bits = mpz_sizeinbase(d[i], 2);
    mpz_set_ui(code, 0);
    for (int i = k - 1; i >= 0; i--) {
        mpz_mul_2exp(code, code, bits);
        mpz_add(code, code, d[i]);
    }
    return bits;
}

static void emit_packed(FILE *out, const char *id, const long long *A, const long long *b,
                        int m, int n, mpz_t *cert) {
    int k = m * (n + 1);
    mpz_t *zz = malloc(sizeof(mpz_t) * k), code, ccode;
    mpz_inits(code, ccode, NULL);
    for (int i = 0; i < m; i++)
        for (int j = 0; j <= n; j++) { /* row i is [b, a1, ..., an], zigzagged */
            mpz_t *z = &zz[i * (n + 1) + j];
            mpz_init_set_si(*z, j == 0 ? b[i] : A[i * n + j - 1]);
            if (mpz_sgn(*z) >= 0) mpz_mul_2exp(*z, *z, 1);
            else { mpz_neg(*z, *z); mpz_mul_2exp(*z, *z, 1); mpz_sub_ui(*z, *z, 1); }
        }
    size_t bits = pack(code, zz, k), cbits = pack(ccode, cert, m);
    gmp_fprintf(out, "\n/-- %d × %d system, packed (see `LeanGpu.decodeRows`). -/\n", m, n);
    gmp_fprintf(out, "def %s_rows : List Row := decodeRows %d %d (2 ^ %zu)\n  %Zd\n", id, m, n, bits, code);
    fprintf(out, "\ntheorem %s_infeasible : ∀ x : List Int, ¬ ∀ r ∈ %s_rows, r.Holds x :=\n", id, id);
    gmp_fprintf(out, "  checkPacked_sound %d %d (2 ^ %zu) _ (digits (2 ^ %zu) %d\n    %Zd)\n    (by decide +kernel)\n",
                m, n, bits, cbits, m, ccode);
    for (int i = 0; i < k; i++) mpz_clear(zz[i]);
    free(zz);
    mpz_clears(code, ccode, NULL);
}

int main(int argc, char **argv) {
    int certs_only = argc > 1 && strcmp(argv[1], "--certs") == 0;
    if (certs_only) { argv[1] = argv[0]; argv++; argc--; }
    if (argc < 2) {
        fprintf(stderr, "usage: %s [--certs] PROBLEMS [OUT] [ITERS]\n", argv[0]);
        return 2;
    }
    FILE *in = fopen(argv[1], "r");
    if (!in) { perror(argv[1]); return 1; }
    Batch bt;
    read_batch(in, &bt);
    fclose(in);
    if (bt.count == 0) { fprintf(stderr, "no problems in %s\n", argv[1]); return 1; }

    FILE *out = argc > 2 ? fopen(argv[2], "w") : stdout;
    if (!out) { perror(argv[2]); return 1; }
    int iters = argc > 3 ? atoi(argv[3]) : 20000;

    int totB = bt.offB[bt.count - 1] + bt.m[bt.count - 1];
    double *lam = malloc(sizeof(double) * totB);
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
#ifdef USE_CUDA
    solve_batch_cuda(&bt, lam, iters);
#else
    solve_batch_cpu(&bt, lam, iters);
#endif
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double solve_ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;

    if (!certs_only) {
        fprintf(out, "import LeanGpu.Packed\n\n");
        /* Basename only: a path like /tmp/-x would open a nested Lean comment. */
        const char *src = strrchr(argv[1], '/') ? strrchr(argv[1], '/') + 1 : argv[1];
        fprintf(out, "/-! Generated by `gpu/build/farkas` from `%s`. Do not edit. -/\n\n", src);
        fprintf(out, "namespace LeanGpu.Generated\nopen LeanGpu\n");
    }

    int found = 0;
    for (int p = 0; p < bt.count; p++) {
        int m = bt.m[p], n = bt.n[p];
        const long long *A = bt.A + bt.offA[p], *b = bt.b + bt.offB[p];
        mpz_t *cert = malloc(sizeof(mpz_t) * m);
        for (int i = 0; i < m; i++) mpz_init(cert[i]);
        char id[80];
        lean_ident(bt.name[p], id, sizeof id);

        if (!exact_certificate(A, b, m, n, lam + bt.offB[p], cert)) {
            if (certs_only) fprintf(out, "%s -\n", bt.name[p]);
            else fprintf(out, "\n-- %s: no certificate found (feasible, or needs a better search)\n", id);
            if (!certs_only) fprintf(stderr, "%-16s no certificate\n", id);
            for (int i = 0; i < m; i++) mpz_clear(cert[i]);
            free(cert);
            continue;
        }
        found++;
        if (!certs_only) fprintf(stderr, "%-16s certificate found\n", id);

        if (certs_only) {
            fprintf(out, "%s", bt.name[p]);
            for (int i = 0; i < m; i++) gmp_fprintf(out, " %Zd", cert[i]);
            fprintf(out, "\n");
        } else if (m * (n + 1) <= PLAIN_MAX) emit_plain(out, id, A, b, m, n, cert);
        else emit_packed(out, id, A, b, m, n, cert);
        for (int i = 0; i < m; i++) mpz_clear(cert[i]);
        free(cert);
    }
    if (!certs_only) fprintf(out, "\nend LeanGpu.Generated\n");
    if (out != stdout) fclose(out);
    fprintf(stderr, "%d/%d problems proved infeasible (search %.1f ms)\n", found, bt.count, solve_ms);
    return 0;
}
