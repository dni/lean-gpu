# lean-gpu

Prove many numeric facts at once: **the GPU finds certificates, Lean checks them.**

The GPU does the expensive search in big batches using matrix-vector products.
Lean checks each certificate with a small checker that has a soundness proof.
If the GPU code has a bug, the worst case is a missing proof, never a wrong one.

## First target: infeasible linear systems

A system `aᵢ · x ≤ bᵢ` has no solution if there are weights `λᵢ ≥ 0` with
`Σ λᵢ aᵢ = 0` and `Σ λᵢ bᵢ < 0` (a Farkas certificate). Finding `λ` is an
optimisation problem. Checking `λ` is one multiply-and-add per entry.

```
problems/*.txt ──► gpu/build/farkas ─────────────────────────► LeanGpu/Generated.lean ──► lake build
                   1. batch search (GPU, floats)                one theorem per problem    kernel checks
                   2. purify to a vertex, solve exactly (GMP)   with its certificate       each certificate
```

| File | Role | Trusted? |
|---|---|---|
| `LeanGpu/Farkas.lean` | `check` plus the `farkas_sound` proof | proved in Lean |
| `LeanGpu/Packed.lean` | `Nat`-only checker for packed problems, `checkPacked_sound` | proved in Lean |
| `LeanGpu/Linear.lean` | linear expressions for the tactic, `leRow_holds` | proved in Lean |
| `LeanGpu/Tactic.lean` | the `farkas` tactic | no (output re-checked by the kernel) |
| `gpu/solve.cu` | batched search, one CUDA block per problem | no |
| `gpu/solve_cpu.c` | the same search on the CPU (reference) | no |
| `gpu/exact.c` | approximate `λ` → exact integer certificate | no |
| `gpu/main.c` | parse, run, emit Lean | no |
| `LeanGpu/Generated.lean` | generated theorems | checked by Lean |

The generated theorems depend only on `propext`, `Classical.choice` and
`Quot.sound` (no `native_decide`).

## How it works

**Search** (`solve_cpu.c`, `solve.cu`): minimise `‖Aᵀλ‖² + (bᵀλ + 1)²` over
`λ ≥ 0` with accelerated projected gradient descent (Nesterov momentum,
gradient restart, early stop). Each iteration is two matrix-vector products per
problem, so a batch is one thread block per problem on the GPU.

**Exact certificate** (`exact.c`): the float `λ` is close to valid but not
exact, and usually uses more rows than there are equations.
1. Purification: step along null-space directions of the support and drop a
   row each time, until the support rows are independent (a vertex).
   Done in floats first (fast), then exactly.
2. Solve the vertex system over the rationals with GMP and scale it to integers.
   Vertex certificates of larger systems often have 25+ digits, which is fine for
   Lean's `Nat`.

**Lean checking** (`Packed.lean`): systems with more than 64 numbers are
written as one packed `Nat` literal (zigzag signs, base `2^k` digits), and
`checkPacked` uses only `Nat` arithmetic, which the kernel runs with GMP.
`checkPacked_sound` reduces it to `farkas_sound`. Small systems stay readable
lists (see `LeanGpu/Generated.lean`).

## The `farkas` tactic

```lean
import LeanGpu.Tactic

example (x y : Int) (h1 : x ≥ 2) (h2 : y > 0) : 2 * x + y * 3 ≥ 7 := by farkas
```

It reads `≤ < ≥ > =` hypotheses over `Int` (and their negations), built from
`+ - *numeral` with any other subterm as an atom, and negates a linear goal.
Each hypothesis becomes a row by reflection (`LExpr.eval` unfolds back to the
original term), so the proof is `farkas_sound` plus one `leRow_holds` per
hypothesis. It does not use `omega`. Tests: `lake build Test`.

Certificates are cached in `.farkas/cache.txt` (commit it: a cache hit needs no
solver, and a rebuild works without the binary). On a cache miss:

* **direct** (default): run `gpu/build/farkas` on this goal and cache the result.
* **batch** (`set_option farkas.batch true`): queue the goal and admit it with a
  warning, then solve the whole queue in one solver run:

```sh
lake build                  # pass 1: goals queued in .farkas/pending.txt
scripts/farkas-batch.sh     # one batched GPU/CPU solve → .farkas/cache.txt
touch <files using farkas>; lake build   # pass 2: everything closes from the cache
```

Tested with 40 generated 8 × 4 goals: pass 1 queued 40, one solver run (27 ms)
solved 40/40, pass 2 closed all of them.

Limits: only `Int` (no `Nat` hypotheses yet). Certificates prove rational
infeasibility, so goals that need integrality (e.g. `2x ≤ 1, 2x ≥ 1`) fail; use
`omega` for those.

## Run it

```sh
make -C gpu            # CPU build (needs GMP); `make -C gpu cuda` for the GPU build (needs nvcc)
./gpu/build/farkas problems/example.txt LeanGpu/Generated.lean
lake build
scripts/bench.sh 1000  # random batches; scripts/gen.py writes problem files
```

## Results (CPU reference, one core)

`scripts/bench.sh 1000`: 1000 random systems per size, half infeasible.

| Size (rows × vars) | Certificates found | Search time |
|---|---|---|
| 12 × 6 | 500 / 500 | 1.7 s |
| 30 × 10 | 500 / 500 | 5.9 s |
| 60 × 20 | 500 / 500 | 22 s |

No feasible system is ever claimed infeasible (everything is checked exactly,
then again by Lean). Most of the search time goes to the feasible half, which
runs the full iteration budget because there is nothing to converge to.

How each step changed the 30 × 10 result: plain gradient descent with
rounding found 51 / 500; exact support solving and purification brought it
to 500 / 500. At 60 × 20, fixed-size integers (128-bit rationals, 64-bit output) overflowed
and found 0 / 100; GMP made it 100 / 100.

Lean check per 60 × 20 proof: about 2 s with `List Int` literals and `decide`;
about 0.5 s packed, with `decide +kernel`.

## Status of the plan

1. **GPU run: not done.** `gpu/solve.cu` implements the same algorithm as
   the CPU version and passes a C++ syntax check, but it has never been compiled
   with `nvcc` or run on a GPU (no GPU on the dev machine). Next step on a GPU
   box: `make -C gpu cuda && scripts/bench.sh 10000` and compare with the CPU numbers.
2. **Faster batched solver: done** (accelerated projected gradient with
   restart and early stop). PDHG / cuPDLP-style methods are an option if
   feasible problems need to be rejected faster.
3. **Exact rounding: done** (purification + GMP rational solve).
4. **Faster Lean checking: done** (packed `Nat` encoding, about 4× faster).
5. **Tactic: done.** `farkas`, with a certificate cache, direct mode and two-pass batch mode.
6. **Sums of squares: not started.** Polynomial inequalities via Gram-matrix
   certificates. This needs an SDP solver, which is much bigger than the LP search here.
