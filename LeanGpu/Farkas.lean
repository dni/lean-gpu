/-!
# Farkas certificates for integer linear systems

A system of constraints `aᵢ · x ≤ bᵢ` has no solution if there are weights
`λᵢ ≥ 0` with `Σ λᵢ aᵢ = 0` and `Σ λᵢ bᵢ < 0`: adding up the weighted
constraints would give `0 ≤ (negative number)`.

Finding `λ` is the expensive part and happens outside Lean (on the GPU).
Checking `λ` is cheap and happens here, in `check`. `farkas_sound` turns a
successful check into a proof, so the GPU code never has to be trusted.
-/

namespace LeanGpu

/-- Dot product. Extra entries of the longer list are ignored. -/
def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- One linear constraint `coeffs · x ≤ bound`. -/
structure Row where
  coeffs : List Int
  bound : Int
  deriving Repr, DecidableEq

/-- `x` satisfies the constraint. -/
def Row.Holds (r : Row) (x : List Int) : Prop :=
  dot r.coeffs x ≤ r.bound

/-- `Σ λᵢ aᵢ`, as a vector of length `n`. -/
def combCoeffs (n : Nat) : List Nat → List Row → List Int
  | l :: ls, r :: rs => List.zipWith (· + ·) (r.coeffs.map ((l : Int) * ·)) (combCoeffs n ls rs)
  | _, _ => List.replicate n 0

/-- `Σ λᵢ bᵢ`. -/
def combBound : List Nat → List Row → Int
  | l :: ls, r :: rs => (l : Int) * r.bound + combBound ls rs
  | _, _ => 0

/-- `Σ λᵢ (aᵢ · x)`. Only used in proofs. -/
def combDot (x : List Int) : List Nat → List Row → Int
  | l :: ls, r :: rs => (l : Int) * dot r.coeffs x + combDot x ls rs
  | _, _ => 0

/-- The certificate checker. This is the only thing Lean has to run. -/
def check (n : Nat) (rows : List Row) (lam : List Nat) : Bool :=
  rows.all (·.coeffs.length == n) &&
  combCoeffs n lam rows == List.replicate n 0 &&
  decide (combBound lam rows < 0)

theorem dot_zipWith_add :
    ∀ (u v x : List Int), u.length = v.length →
      dot (List.zipWith (· + ·) u v) x = dot u x + dot v x
  | [], [], _, _ => by simp [dot]
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | _ :: _, _ :: _, [], _ => by simp [dot]
  | a :: u, b :: v, y :: x, h => by
    simp only [List.zipWith_cons_cons, dot]
    rw [dot_zipWith_add u v x (by simpa using h), Int.add_mul]
    omega

theorem dot_map_mul (c : Int) :
    ∀ (u x : List Int), dot (u.map (c * ·)) x = c * dot u x
  | [], _ => by simp [dot]
  | _ :: _, [] => by simp [dot]
  | a :: u, y :: x => by
    simp only [List.map_cons, dot]
    rw [dot_map_mul c u x, Int.mul_add, Int.mul_assoc]

theorem dot_replicate_zero : ∀ (n : Nat) (x : List Int), dot (List.replicate n 0) x = 0
  | 0, _ => by simp [dot]
  | _ + 1, [] => by simp [List.replicate_succ, dot]
  | n + 1, _ :: x => by simp [List.replicate_succ, dot, dot_replicate_zero n x]

theorem length_combCoeffs (n : Nat) :
    ∀ (lam : List Nat) (rows : List Row), (∀ r ∈ rows, r.coeffs.length = n) →
      (combCoeffs n lam rows).length = n
  | [], _, _ => by simp [combCoeffs]
  | _ :: _, [], _ => by simp [combCoeffs]
  | l :: ls, r :: rs, h => by
    simp only [combCoeffs, List.length_zipWith, List.length_map]
    rw [h r (by simp), length_combCoeffs n ls rs (fun r' hr' => h r' (by simp [hr']))]
    simp

theorem dot_combCoeffs (n : Nat) (x : List Int) :
    ∀ (lam : List Nat) (rows : List Row), (∀ r ∈ rows, r.coeffs.length = n) →
      dot (combCoeffs n lam rows) x = combDot x lam rows
  | [], _, _ => by simp [combCoeffs, combDot, dot_replicate_zero]
  | _ :: _, [], _ => by simp [combCoeffs, combDot, dot_replicate_zero]
  | l :: ls, r :: rs, h => by
    have hrs : ∀ r' ∈ rs, r'.coeffs.length = n := fun r' hr' => h r' (by simp [hr'])
    simp only [combCoeffs, combDot]
    rw [dot_zipWith_add _ _ _ (by rw [List.length_map, h r (by simp),
        length_combCoeffs n ls rs hrs]),
      dot_map_mul, dot_combCoeffs n x ls rs hrs]

theorem combDot_le (x : List Int) :
    ∀ (lam : List Nat) (rows : List Row), (∀ r ∈ rows, r.Holds x) →
      combDot x lam rows ≤ combBound lam rows
  | [], _, _ => by simp [combDot, combBound]
  | _ :: _, [], _ => by simp [combDot, combBound]
  | l :: ls, r :: rs, h => by
    simp only [combDot, combBound]
    have h1 : (l : Int) * dot r.coeffs x ≤ (l : Int) * r.bound :=
      Int.mul_le_mul_of_nonneg_left (h r (by simp)) (Int.natCast_nonneg l)
    have h2 := combDot_le x ls rs (fun r' hr' => h r' (by simp [hr']))
    omega

/-- **Soundness.** If `check` accepts the certificate, the system has no integer solution. -/
theorem farkas_sound (n : Nat) (rows : List Row) (lam : List Nat)
    (h : check n rows lam = true) : ∀ x : List Int, ¬ ∀ r ∈ rows, r.Holds x := by
  intro x hx
  simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hlen, hzero⟩, hneg⟩ := h
  have hle := combDot_le x lam rows hx
  rw [← dot_combCoeffs n x lam rows hlen, hzero, dot_replicate_zero] at hle
  omega

end LeanGpu
