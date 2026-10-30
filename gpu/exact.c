/* Turn an approximate certificate from the solver into an exact one.
 *
 * The solver tells us which rows matter (the support). Purification shrinks
 * the support until its rows are linearly independent (a vertex), first in
 * floating point (fast), then exactly. On the vertex we solve
 * A_S^T lam = 0, b_S^T lam = -1 over the rationals with GMP and scale the
 * solution to integers (of any size). Nothing here is trusted: Lean re-checks the result. */
#include <gmp.h>
#include <math.h>
#include <stdlib.h>
#include <string.h>
#include "farkas.h"
#include "exact.h"

#define MAX_SCALE 64
#define FLOAT_EPS 1e-9

int exact_check(const long long *A, const long long *b, int m, int n, mpz_t *lam) {
    mpz_t s, t;
    mpz_inits(s, t, NULL);
    int ok = 1;
    for (int j = 0; j <= n && ok; j++) {
        mpz_set_ui(s, 0);
        for (int i = 0; i < m; i++) {
            mpz_set_si(t, j == n ? b[i] : A[i * n + j]);
            mpz_mul(t, t, lam[i]);
            mpz_add(s, s, t);
        }
        ok = j == n ? mpz_sgn(s) < 0 : mpz_sgn(s) == 0;
    }
    mpz_clears(s, t, NULL);
    return ok;
}

/* Entry (row j, column k) of the support system [A_S^T ; b_S^T | 0 ; -1]. */
static long long entry(const long long *A, const long long *b, int n,
                       const int *cols, int s, int j, int k) {
    if (k == s) return j == n ? -1 : 0;
    return j == n ? b[cols[k]] : A[cols[k] * n + j];
}

/* A null direction of the support system: d with d[free] = 1 and the basic
 * entries from the reduced row echelon form. Returns 0 if every column pivots
 * (the support is a vertex). The float version uses partial pivoting. */
static int null_dir_float(const long long *A, const long long *b, int n,
                          const int *cols, int s, double *d) {
    int rows = n + 1, w = s + 1;
    double *T = malloc(sizeof(double) * rows * w);
    int *pivot_row = malloc(sizeof(int) * s);
    double scale = 0;
    for (int j = 0; j < rows; j++)
        for (int k = 0; k < w; k++) {
            T[j * w + k] = (double)entry(A, b, n, cols, s, j, k);
            if (fabs(T[j * w + k]) > scale) scale = fabs(T[j * w + k]);
        }
    int r = 0, free_k = -1;
    for (int k = 0; k < s; k++) {
        pivot_row[k] = -1;
        if (r >= rows) {
            if (free_k < 0) free_k = k;
            continue;
        }
        int pr = r;
        for (int j = r + 1; j < rows; j++) if (fabs(T[j * w + k]) > fabs(T[pr * w + k])) pr = j;
        if (fabs(T[pr * w + k]) <= FLOAT_EPS * scale) {
            if (free_k < 0) free_k = k;
            continue;
        }
        for (int c = 0; c < w; c++) { double t = T[r * w + c]; T[r * w + c] = T[pr * w + c]; T[pr * w + c] = t; }
        double pv = T[r * w + k];
        for (int c = 0; c < w; c++) T[r * w + c] /= pv;
        for (int j = 0; j < rows; j++) {
            if (j == r || T[j * w + k] == 0) continue;
            double f = T[j * w + k];
            for (int c = 0; c < w; c++) T[j * w + c] -= f * T[r * w + c];
        }
        pivot_row[k] = r++;
    }
    if (free_k >= 0)
        for (int k = 0; k < s; k++)
            d[k] = k == free_k ? 1 : pivot_row[k] < 0 ? 0 : -T[pivot_row[k] * w + free_k];
    free(T);
    free(pivot_row);
    return free_k >= 0;
}

/* Exact reduced row echelon form. Returns 0 if the system is inconsistent. */
static int rref_exact(const long long *A, const long long *b, int n,
                      const int *cols, int s, mpq_t *T, int *pivot_row) {
    int rows = n + 1, w = s + 1, r = 0;
    mpq_t f, t;
    mpq_inits(f, t, NULL);
    for (int j = 0; j < rows; j++)
        for (int k = 0; k < w; k++) mpq_set_si(T[j * w + k], entry(A, b, n, cols, s, j, k), 1);
    for (int k = 0; k < s; k++) {
        pivot_row[k] = -1;
        int pr = -1;
        for (int j = r; j < rows; j++) if (mpq_sgn(T[j * w + k]) != 0) { pr = j; break; }
        if (pr < 0) continue;
        for (int c = 0; c < w; c++) mpq_swap(T[r * w + c], T[pr * w + c]);
        mpq_set(f, T[r * w + k]);
        for (int c = 0; c < w; c++) mpq_div(T[r * w + c], T[r * w + c], f);
        for (int j = 0; j < rows; j++) {
            if (j == r || mpq_sgn(T[j * w + k]) == 0) continue;
            mpq_set(f, T[j * w + k]);
            for (int c = 0; c < w; c++) {
                mpq_mul(t, f, T[r * w + c]);
                mpq_sub(T[j * w + c], T[j * w + c], t);
            }
        }
        pivot_row[k] = r++;
    }
    int ok = 1;
    for (int j = r; j < rows; j++) if (mpq_sgn(T[j * w + s]) != 0) ok = 0;
    mpq_clears(f, t, NULL);
    return ok;
}

/* Exact version of null_dir_float. On a vertex (returns 0) it also writes the
 * integer certificate to out, or sets *bad if there is none on this support. */
static int null_dir_exact(const long long *A, const long long *b, int m, int n,
                          const int *cols, int s, double *d, mpz_t *out, int *bad) {
    int rows = n + 1, w = s + 1, free_k = -1;
    mpq_t *T = malloc(sizeof(mpq_t) * rows * w);
    int *pivot_row = malloc(sizeof(int) * s);
    for (int i = 0; i < rows * w; i++) mpq_init(T[i]);
    *bad = !rref_exact(A, b, n, cols, s, T, pivot_row);
    for (int k = 0; k < s && !*bad; k++) if (pivot_row[k] < 0) { free_k = k; break; }

    if (!*bad && free_k >= 0) {
        for (int k = 0; k < s; k++)
            d[k] = k == free_k ? 1 : pivot_row[k] < 0 ? 0 : -mpq_get_d(T[pivot_row[k] * w + free_k]);
    } else if (!*bad) {
        /* lam_k = rhs of row k, scaled by the lcm of the denominators. */
        mpz_t l;
        mpz_init_set_ui(l, 1);
        for (int k = 0; k < s; k++) {
            mpq_srcptr v = T[pivot_row[k] * w + s];
            if (mpq_sgn(v) < 0) *bad = 1;
            mpz_lcm(l, l, mpq_denref(v));
        }
        for (int i = 0; i < m; i++) mpz_set_ui(out[i], 0);
        for (int k = 0; k < s && !*bad; k++) {
            mpq_srcptr v = T[pivot_row[k] * w + s];
            mpz_divexact(out[cols[k]], l, mpq_denref(v));
            mpz_mul(out[cols[k]], out[cols[k]], mpq_numref(v));
        }
        mpz_clear(l);
    }
    for (int i = 0; i < rows * w; i++) mpq_clear(T[i]);
    free(T);
    free(pivot_row);
    return free_k >= 0;
}

/* Move wt along +-d until a weight hits zero and drop that row. */
static void step_and_drop(int *cols, double *wt, int *s, const double *d) {
    int drop = -1;
    double theta = 0;
    for (int sign = -1; sign <= 1 && drop < 0; sign += 2) {
        for (int k = 0; k < *s; k++) {
            double dk = sign * d[k];
            if (dk < 0 && (drop < 0 || wt[k] / -dk < theta)) { theta = wt[k] / -dk; drop = k; }
        }
        if (drop >= 0) for (int k = 0; k < *s; k++) wt[k] += theta * sign * d[k];
    }
    (*s)--;
    cols[drop] = cols[*s];
    wt[drop] = wt[*s];
    for (int k = 0; k < *s; k++) if (wt[k] < 0) wt[k] = 0;
}

static int purify(const long long *A, const long long *b, int m, int n,
                  int *cols, double *wt, int s, mpz_t *out) {
    double *d = malloc(sizeof(double) * s);
    while (s > 0 && null_dir_float(A, b, n, cols, s, d)) step_and_drop(cols, wt, &s, d);
    int bad = 0, ok = 0;
    while (s > 0) {
        if (null_dir_exact(A, b, m, n, cols, s, d, out, &bad)) step_and_drop(cols, wt, &s, d);
        else { ok = !bad && exact_check(A, b, m, n, out); break; }
        if (bad) break;
    }
    free(d);
    return ok;
}

int exact_certificate(const long long *A, const long long *b, int m, int n,
                      const double *l, mpz_t *out) {
    double lmax = 0;
    for (int i = 0; i < m; i++) if (l[i] > lmax) lmax = l[i];
    if (lmax <= 0) return 0;

    int *cols = malloc(sizeof(int) * m);
    double *wt = malloc(sizeof(double) * m);
    static const double thresholds[] = {1e-6, 1e-4, 1e-2};
    for (int t = 0; t < 3; t++) {
        int s = 0;
        for (int i = 0; i < m; i++)
            if (l[i] >= thresholds[t] * lmax) { cols[s] = i; wt[s] = l[i]; s++; }
        if (purify(A, b, m, n, cols, wt, s, out)) { free(cols); free(wt); return 1; }
    }
    free(cols);
    free(wt);

    /* Fallback: lam * k / max(lam) for small k. */
    for (int k = 1; k <= MAX_SCALE; k++) {
        for (int i = 0; i < m; i++)
            mpz_set_si(out[i], l[i] < 1e-6 * lmax ? 0 : llround(k * l[i] / lmax));
        if (exact_check(A, b, m, n, out)) return 1;
    }
    return 0;
}
