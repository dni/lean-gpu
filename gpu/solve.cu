// CUDA version of solve_cpu.c (same algorithm, step for step): one thread block
// per problem, threads split the rows and columns of each matrix-vector product.
// Untested: written on a machine without nvcc. Build with `make cuda`.
#include <cuda_runtime.h>
#include <stdio.h>
#include <stdlib.h>

extern "C" {
#include "farkas.h"
}

#define CHECK(x) do { cudaError_t e = (x); if (e != cudaSuccess) { \
    fprintf(stderr, "cuda: %s (%s:%d)\n", cudaGetErrorString(e), __FILE__, __LINE__); exit(1); } } while (0)

// Block-wide sum of v; every thread gets the result. red has blockDim.x slots.
__device__ double block_sum(double v, double *red) {
    red[threadIdx.x] = v;
    __syncthreads();
    for (int s = blockDim.x / 2; s > 0; s >>= 1) {
        if ((int)threadIdx.x < s) red[threadIdx.x] += red[threadIdx.x + s];
        __syncthreads();
    }
    double total = red[0];
    __syncthreads();
    return total;
}

__global__ void solve_kernel(const int *ms, const int *ns, const int *offA, const int *offB,
                             const long long *Ag, const long long *bg, double *lamg, double *yg,
                             int iters) {
    int p = blockIdx.x;
    int m = ms[p], n = ns[p];
    const long long *A = Ag + offA[p], *b = bg + offB[p];
    double *l = lamg + offB[p], *y = yg + offB[p];

    extern __shared__ double sh[];
    double *r = sh;           // n + 1 entries
    double *red = sh + n + 1; // blockDim.x entries, for reductions

    // Step 1/L from the squared Frobenius norm of [A b].
    double part = 0;
    for (int k = threadIdx.x; k < m * n; k += blockDim.x) part += (double)A[k] * A[k];
    for (int i = threadIdx.x; i < m; i += blockDim.x) part += (double)b[i] * b[i];
    double fro = block_sum(part, red);
    double step = fro > 0 ? 1.0 / fro : 0;

    for (int i = threadIdx.x; i < m; i += blockDim.x) l[i] = y[i] = 1.0 / m;
    __syncthreads();

    double t = 1;
    for (int it = 0; it < iters; it++) {
        // r = [A^T y ; b^T y + 1]
        part = 0;
        for (int j = threadIdx.x; j <= n; j += blockDim.x) {
            double s = j == n ? 1.0 : 0.0;
            for (int i = 0; i < m; i++) s += (j == n ? b[i] : A[i * n + j]) * y[i];
            r[j] = s;
            part += s * s;
        }
        if (block_sum(part, red) < SOLVE_TOL) break; // uniform across the block
        // lam' = max(0, y - step * [A b] r), Nesterov momentum, gradient restart.
        double t2 = (1 + sqrt(1 + 4 * t * t)) / 2;
        part = 0;
        for (int i = threadIdx.x; i < m; i += blockDim.x) {
            double g = b[i] * r[n];
            for (int j = 0; j < n; j++) g += A[i * n + j] * r[j];
            double v = y[i] - step * g;
            v = v > 0 ? v : 0;
            part += (y[i] - v) * (v - l[i]);
            y[i] = v + (t - 1) / t2 * (v - l[i]);
            l[i] = v;
        }
        t = t2;
        if (block_sum(part, red) > 0) {
            t = 1;
            for (int i = threadIdx.x; i < m; i += blockDim.x) y[i] = l[i];
        }
        __syncthreads();
    }
}

template <typename T>
static T *upload(const T *h, size_t count) {
    T *d;
    CHECK(cudaMalloc(&d, sizeof(T) * count));
    CHECK(cudaMemcpy(d, h, sizeof(T) * count, cudaMemcpyHostToDevice));
    return d;
}

extern "C" void solve_batch_cuda(const Batch *bt, double *lam, int iters) {
    int P = bt->count, maxN = 0;
    for (int p = 0; p < P; p++) if (bt->n[p] > maxN) maxN = bt->n[p];
    size_t totA = bt->offA[P - 1] + (size_t)bt->m[P - 1] * bt->n[P - 1];
    size_t totB = bt->offB[P - 1] + bt->m[P - 1];

    int *dm = upload(bt->m, P), *dn = upload(bt->n, P);
    int *doA = upload(bt->offA, P), *doB = upload(bt->offB, P);
    long long *dA = upload(bt->A, totA), *db = upload(bt->b, totB);
    double *dl, *dy;
    CHECK(cudaMalloc(&dl, sizeof(double) * totB));
    CHECK(cudaMalloc(&dy, sizeof(double) * totB));

    const int threads = 128; // power of two, for the reduction
    size_t shmem = sizeof(double) * (maxN + 1 + threads);
    solve_kernel<<<P, threads, shmem>>>(dm, dn, doA, doB, dA, db, dl, dy, iters);
    CHECK(cudaGetLastError());
    CHECK(cudaMemcpy(lam, dl, sizeof(double) * totB, cudaMemcpyDeviceToHost));

    cudaFree(dm); cudaFree(dn); cudaFree(doA); cudaFree(doB);
    cudaFree(dA); cudaFree(db); cudaFree(dl); cudaFree(dy);
}
