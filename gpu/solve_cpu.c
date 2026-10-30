#include <math.h>
#include <stdlib.h>
#include "farkas.h"

/* r = [A^T y ; b^T y + 1], returns ||r||^2. */
static double residual(const long long *A, const long long *b, int m, int n,
                       const double *y, double *r) {
    double f = 0;
    for (int j = 0; j <= n; j++) {
        double s = j == n ? 1.0 : 0.0;
        for (int i = 0; i < m; i++) s += (j == n ? b[i] : A[i * n + j]) * y[i];
        r[j] = s;
        f += s * s;
    }
    return f;
}

/* Reference implementation. gpu/solve.cu does the same steps in parallel. */
void solve_batch_cpu(const Batch *bt, double *lam, int iters) {
    for (int p = 0; p < bt->count; p++) {
        int m = bt->m[p], n = bt->n[p];
        const long long *A = bt->A + bt->offA[p], *b = bt->b + bt->offB[p];
        double *l = lam + bt->offB[p];
        double *y = malloc(sizeof(double) * m);
        double *r = malloc(sizeof(double) * (n + 1));

        /* Step 1/L, with L bounded by the squared Frobenius norm of [A b]. */
        double fro = 0;
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < n; j++) fro += (double)A[i * n + j] * A[i * n + j];
            fro += (double)b[i] * b[i];
        }
        double step = fro > 0 ? 1.0 / fro : 0;

        for (int i = 0; i < m; i++) l[i] = y[i] = 1.0 / m;
        double t = 1;
        for (int it = 0; it < iters; it++) {
            double f = residual(A, b, m, n, y, r);
            if (f < SOLVE_TOL) break;
            /* lam' = max(0, y - step * [A b] r), then Nesterov momentum with
             * gradient restart (O'Donoghue & Candes). */
            double t2 = (1 + sqrt(1 + 4 * t * t)) / 2, restart = 0;
            for (int i = 0; i < m; i++) {
                double g = b[i] * r[n];
                for (int j = 0; j < n; j++) g += A[i * n + j] * r[j];
                double v = y[i] - step * g;
                v = v > 0 ? v : 0;
                restart += (y[i] - v) * (v - l[i]);
                y[i] = v + (t - 1) / t2 * (v - l[i]);
                l[i] = v;
            }
            t = t2;
            if (restart > 0) {
                t = 1;
                for (int i = 0; i < m; i++) y[i] = l[i];
            }
        }
        free(y);
        free(r);
    }
}
