import LeanGpu.Tactic

/-! Tests for the `farkas` tactic. -/

-- Goal `False` from hypotheses.
example (x y : Int) (h1 : x + y ≤ 1) (h2 : 1 ≤ x) (h3 : 1 ≤ y) : False := by farkas

-- Strict inequalities and a cycle.
example (x y z : Int) (h1 : x < y) (h2 : y < z) (h3 : z < x) : False := by farkas

-- A linear goal, proved by contradiction; numerals on either side of `*`.
example (x y : Int) (h1 : x ≥ 2) (h2 : y > 0) : 2 * x + y * 3 ≥ 7 := by farkas

-- Equalities, subtraction, negation and negated hypotheses.
example (a b : Int) (h1 : a - b = 3) (h2 : ¬ a ≤ b + 5) (h3 : -a ≥ -10) (h4 : ¬ b > 1) :
    False := by farkas

-- Non-linear subterms become atoms.
example (f : Int → Int) (x : Int) (h1 : f x + x * x ≤ 0) (h2 : f x ≥ 1) (h3 : x * x ≥ 0) :
    False := by farkas

-- Hypotheses that are not over Int are ignored.
example (n : Nat) (x : Int) (_ : n ≤ 5) (h1 : x ≤ 0) (h2 : x ≥ 1) : False := by farkas

-- Satisfiable: the tactic must fail.
example (x : Int) (_h1 : x ≤ 3) (_h2 : x ≥ 0) : x = x := by
  fail_if_success farkas
  rfl

-- Infeasible over Int but not over ℚ: Farkas certificates cannot prove it.
example (x : Int) (_h1 : 2 * x ≤ 1) (_h2 : 2 * x ≥ 1) : x = x := by
  fail_if_success farkas
  rfl

theorem axioms_check (x y : Int) (h1 : x < y) (h2 : y < x) : False := by farkas

/-- info: 'axioms_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms axioms_check
