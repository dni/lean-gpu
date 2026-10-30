import LeanGpu.Farkas

/-!
# Linear expressions, for the `farkas` tactic

The tactic reads hypotheses like `2 * x + y < z` as `LExpr` terms over a list
of atoms `ρ`. `LExpr.eval ρ e` unfolds back to the original term, so a
hypothesis proves `lhs.eval ρ ≤ rhs.eval ρ` as is, and `leRow_holds` turns it
into a `Row` for `farkas_sound`.
-/

namespace LeanGpu

/-- Linear integer expressions over atoms `ρ[i]`. -/
inductive LExpr where
  | atom (i : Nat)
  | const (c : Int)
  | add (a b : LExpr)
  | sub (a b : LExpr)
  | neg (a : LExpr)
  /-- `c * a` -/
  | mulL (c : Int) (a : LExpr)
  /-- `a * c` -/
  | mulR (a : LExpr) (c : Int)
  deriving Repr, Inhabited

namespace LExpr

def eval (ρ : List Int) : LExpr → Int
  | atom i => ρ.getD i 0
  | const c => c
  | add a b => a.eval ρ + b.eval ρ
  | sub a b => a.eval ρ - b.eval ρ
  | neg a => -a.eval ρ
  | mulL c a => c * a.eval ρ
  | mulR a c => a.eval ρ * c

/-- The `i`-th unit vector of length `n`. -/
def unit : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, 0 => 1 :: List.replicate n 0
  | n + 1, i + 1 => 0 :: unit n i

/-- Coefficients of the atoms, as a vector of length `n`. -/
def lin (n : Nat) : LExpr → List Int
  | atom i => unit n i
  | const _ => List.replicate n 0
  | add a b => List.zipWith (· + ·) (a.lin n) (b.lin n)
  | sub a b => List.zipWith (· + ·) (a.lin n) ((b.lin n).map ((-1) * ·))
  | neg a => (a.lin n).map ((-1) * ·)
  | mulL c a => (a.lin n).map (c * ·)
  | mulR a c => (a.lin n).map (c * ·)

/-- The constant term. -/
def cst : LExpr → Int
  | atom _ => 0
  | const c => c
  | add a b => a.cst + b.cst
  | sub a b => a.cst - b.cst
  | neg a => -a.cst
  | mulL c a => c * a.cst
  | mulR a c => a.cst * c

theorem length_unit : ∀ (n i : Nat), (unit n i).length = n
  | 0, _ => rfl
  | _ + 1, 0 => by simp [unit]
  | n + 1, i + 1 => by simp [unit, length_unit n i]

theorem length_lin (n : Nat) : ∀ e : LExpr, (e.lin n).length = n
  | atom i => length_unit n i
  | const _ => by simp [lin]
  | add a b => by simp [lin, length_lin n a, length_lin n b]
  | sub a b => by simp [lin, length_lin n a, length_lin n b]
  | neg a => by simp [lin, length_lin n a]
  | mulL _ a => by simp [lin, length_lin n a]
  | mulR a _ => by simp [lin, length_lin n a]

theorem dot_unit : ∀ (n i : Nat) (ρ : List Int), ρ.length = n → dot (unit n i) ρ = ρ.getD i 0
  | 0, _, [], _ => by simp [unit, dot]
  | 0, _, _ :: _, h => by simp at h
  | _ + 1, _, [], h => by simp at h
  | _ + 1, 0, a :: ρ, _ => by simp [unit, dot, dot_replicate_zero]
  | n + 1, i + 1, _ :: ρ, h => by simp [unit, dot, dot_unit n i ρ (by simpa using h)]

theorem eval_eq (n : Nat) (ρ : List Int) (hρ : ρ.length = n) :
    ∀ e : LExpr, e.eval ρ = dot (e.lin n) ρ + e.cst
  | atom i => by simp [eval, lin, cst, dot_unit n i ρ hρ]
  | const c => by simp [eval, lin, cst, dot_replicate_zero]
  | add a b => by
    simp only [eval, lin, cst]
    rw [dot_zipWith_add _ _ _ (by simp [length_lin]), eval_eq n ρ hρ a, eval_eq n ρ hρ b]
    omega
  | sub a b => by
    simp only [eval, lin, cst]
    rw [dot_zipWith_add _ _ _ (by simp [length_lin]), dot_map_mul,
      eval_eq n ρ hρ a, eval_eq n ρ hρ b]
    omega
  | neg a => by
    simp only [eval, lin, cst]
    rw [dot_map_mul, eval_eq n ρ hρ a]
    omega
  | mulL c a => by
    simp only [eval, lin, cst]
    rw [dot_map_mul, eval_eq n ρ hρ a, Int.mul_add]
  | mulR a c => by
    simp only [eval, lin, cst]
    rw [dot_map_mul, eval_eq n ρ hρ a, Int.add_mul, Int.mul_comm c]

end LExpr

/-- The row `lhs - rhs ≤ 0`. -/
def leRow (n : Nat) (lhs rhs : LExpr) : Row :=
  ⟨(LExpr.sub lhs rhs).lin n, -(LExpr.sub lhs rhs).cst⟩

theorem leRow_holds (n : Nat) (ρ : List Int) (hρ : ρ.length = n) (lhs rhs : LExpr)
    (h : lhs.eval ρ ≤ rhs.eval ρ) : (leRow n lhs rhs).Holds ρ := by
  have := LExpr.eval_eq n ρ hρ (.sub lhs rhs)
  have hsub : (LExpr.sub lhs rhs).eval ρ = lhs.eval ρ - rhs.eval ρ := rfl
  show dot ((LExpr.sub lhs rhs).lin n) ρ ≤ -(LExpr.sub lhs rhs).cst
  omega

theorem holds_nil (ρ : List Int) : ∀ r ∈ ([] : List Row), r.Holds ρ := by simp

theorem holds_cons {ρ : List Int} {r : Row} {rs : List Row} (h : r.Holds ρ)
    (hs : ∀ r' ∈ rs, r'.Holds ρ) : ∀ r' ∈ r :: rs, r'.Holds ρ := by
  intro r' hr'
  simp only [List.mem_cons] at hr'
  rcases hr' with rfl | hr'
  · exact h
  · exact hs r' hr'

end LeanGpu
