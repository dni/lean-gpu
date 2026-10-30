"""Generate random benchmark problems for gpu/build/farkas.

    python3 scripts/gen.py COUNT M N [SEED] > problems/bench.txt

Half the problems are infeasible with a hidden certificate that uses about
half the rows; the other half are feasible (built around a random point).
"""
import random
import sys


def infeasible(rng, m, n):
    k = max(2, m // 2)  # rows in the certificate
    lam = [rng.randint(1, 5) for _ in range(k - 1)] + [1]
    rows = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(k - 1)]
    bounds = [rng.randint(-20, 20) for _ in range(k - 1)]
    # Last certificate row cancels the others, so sum(lam * a) = 0.
    rows.append([-sum(l * r[j] for l, r in zip(lam, rows)) for j in range(n)])
    bounds.append(-sum(l * b for l, b in zip(lam, bounds)) - rng.randint(1, 10))
    # Noise rows that are not part of the certificate.
    for _ in range(m - k):
        rows.append([rng.randint(-9, 9) for _ in range(n)])
        bounds.append(rng.randint(0, 50))
    order = list(range(m))
    rng.shuffle(order)
    return [rows[i] for i in order], [bounds[i] for i in order]


def feasible(rng, m, n):
    x = [rng.randint(-5, 5) for _ in range(n)]
    rows = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(m)]
    bounds = [sum(a * xi for a, xi in zip(r, x)) + rng.randint(0, 5) for r in rows]
    return rows, bounds


def main():
    count, m, n = (int(a) for a in sys.argv[1:4])
    rng = random.Random(int(sys.argv[4]) if len(sys.argv) > 4 else 0)
    for p in range(count):
        kind = "inf" if p % 2 == 0 else "feas"
        rows, bounds = (infeasible if kind == "inf" else feasible)(rng, m, n)
        print(f"{kind}{p} {m} {n}")
        for r, b in zip(rows, bounds):
            print(" ".join(map(str, r + [b])))


if __name__ == "__main__":
    main()
