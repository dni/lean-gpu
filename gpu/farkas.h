#ifndef FARKAS_H
#define FARKAS_H

/* A batch of linear systems A x <= b, stored back to back in flat arrays.
 * Problem p has m[p] rows and n[p] columns; its row-major A starts at
 * A[offA[p]], its b and lambda start at b[offB[p]] / lam[offB[p]]. */
typedef struct {
    int count;
    int *m, *n;
    int *offA, *offB;
    long long *A, *b; /* exact integer data */
    char (*name)[64];
} Batch;

/* Search for lam >= 0 with A^T lam = 0 and b^T lam = -1 by accelerated
 * projected gradient descent on ||A^T lam||^2 + (b^T lam + 1)^2, stopping
 * early once the squared residual drops below SOLVE_TOL. Every iteration is
 * two matrix-vector products per problem, so the whole batch is GPU friendly.
 * The result is approximate; exact.c turns it into an exact certificate. */
#define SOLVE_TOL 1e-16

void solve_batch_cpu(const Batch *bt, double *lam, int iters);
#ifdef USE_CUDA
void solve_batch_cuda(const Batch *bt, double *lam, int iters);
#endif

#endif
