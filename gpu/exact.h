#ifndef EXACT_H
#define EXACT_H

/* exact.c: certificates are arbitrary-size integers (GMP), since vertex
 * certificates of larger systems routinely exceed 64 bits. */
#include <gmp.h>
int exact_check(const long long *A, const long long *b, int m, int n, mpz_t *lam);
int exact_certificate(const long long *A, const long long *b, int m, int n,
                      const double *l, mpz_t *out);

#endif
