import LeanGpu.Farkas

/-!
# Packed problems and a `Nat`-only checker

Large problems are slow to check as `List Int` literals: elaborating the
literals costs more than the proof. Here a whole problem is one `Nat`, and
the checker only does `Nat` arithmetic, which the kernel runs with GMP.

Encoding: every integer `v` becomes a natural number by the zigzag map
(`0, -1, 1, -2, … ↦ 0, 1, 2, 3, …`). Row `i` is the digit list
`[b, a₁, …, aₙ]` in base `B` (bound first), and the rows are the base-`B^(n+1)`
digits of `code`. `checkPacked_sound` reduces everything to `farkas_sound`.
-/

namespace LeanGpu

/-- Inverse of the zigzag map. -/
def unzz (k : Nat) : Int :=
  cond (k % 2 == 0) ((k / 2 : Nat) : Int) (-((k + 1) / 2 : Nat))

/-- The lowest `count` base-`B` digits of `code`, least significant first. -/
def digits (B : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | c + 1, code => code % B :: digits B c (code / B)

/-- `m` rows of `w` base-`B` digits each; `Bw = B ^ w`. -/
def unpack (B Bw w : Nat) : Nat → Nat → List (List Nat)
  | 0, _ => []
  | m + 1, code => digits B w (code % Bw) :: unpack B Bw w m (code / Bw)

/-- A packed row `[b, a₁, …, aₙ]`. -/
def toRow : List Nat → Row
  | b :: as => ⟨as.map unzz, unzz b⟩
  | [] => ⟨[], 0⟩

/-- The `m × n` system packed in `code` with digit base `B`. -/
def decodeRows (m n B code : Nat) : List Row :=
  (unpack B (B ^ (n + 1)) (n + 1) m code).map toRow

/-- Add `l * unzz z` to a (positive part, negative part) accumulator. -/
def step (l z : Nat) (pq : Nat × Nat) : Nat × Nat :=
  cond (z % 2 == 0) (pq.1 + l * (z / 2), pq.2) (pq.1, pq.2 + l * ((z + 1) / 2))

/-- `Σ λᵢ rowᵢ` as (positive, negative) pairs; mirrors `combCoeffs`. -/
def accN (w : Nat) : List Nat → List (List Nat) → List (Nat × Nat)
  | l :: ls, r :: rs => List.zipWith (step l) r (accN w ls rs)
  | _, _ => List.replicate w (0, 0)

/-- Packed counterpart of `check`, using only `Nat` arithmetic. -/
def checkPacked (m n B code : Nat) (lam : List Nat) : Bool :=
  match accN (n + 1) lam (unpack B (B ^ (n + 1)) (n + 1) m code) with
  | pq :: cols => Nat.blt pq.1 pq.2 && cols.all (fun c => c.1 == c.2)
  | [] => false

/-- Value of an accumulator. -/
def val (pq : Nat × Nat) : Int := (pq.1 : Int) - pq.2

theorem val_step (l z : Nat) (pq : Nat × Nat) : val (step l z pq) = l * unzz z + val pq := by
  unfold val step unzz
  cases z % 2 == 0
  · simp only [Bool.cond_false]
    push_cast
    rw [Int.mul_neg]
    omega
  · simp only [Bool.cond_true]
    push_cast
    omega

theorem map_val_zipWith_step (l : Nat) :
    ∀ (r : List Nat) (acc : List (Nat × Nat)),
      (List.zipWith (step l) r acc).map val =
        List.zipWith (· + ·) ((r.map unzz).map ((l : Int) * ·)) (acc.map val)
  | [], _ => by simp
  | _ :: _, [] => by simp
  | z :: r, pq :: acc => by
    simp only [List.zipWith_cons_cons, List.map_cons, val_step, map_val_zipWith_step l r acc]

theorem length_digits (B : Nat) : ∀ (c code : Nat), (digits B c code).length = c
  | 0, _ => rfl
  | c + 1, code => by simp [digits, length_digits B c]

theorem length_of_mem_unpack (B Bw w : Nat) :
    ∀ (m code : Nat), ∀ r ∈ unpack B Bw w m code, r.length = w
  | 0, _, r, h => by simp [unpack] at h
  | m + 1, code, r, h => by
    simp only [unpack, List.mem_cons] at h
    rcases h with rfl | h
    · exact length_digits B w _
    · exact length_of_mem_unpack B Bw w m _ r h

/-- The accumulators compute exactly `Σ λᵢ bᵢ :: Σ λᵢ aᵢ`. -/
theorem map_val_accN (n : Nat) :
    ∀ (lam : List Nat) (zrs : List (List Nat)), (∀ r ∈ zrs, r.length = n + 1) →
      (accN (n + 1) lam zrs).map val =
        combBound lam (zrs.map toRow) :: combCoeffs n lam (zrs.map toRow)
  | [], _, _ => by
    simp [accN, combBound, combCoeffs, val, List.replicate_succ]
  | _ :: _, [], _ => by
    simp [accN, combBound, combCoeffs, val, List.replicate_succ]
  | l :: ls, r :: rs, h => by
    have ih := map_val_accN n ls rs (fun r' hr' => h r' (by simp [hr']))
    obtain ⟨b, as, rfl⟩ : ∃ b as, r = b :: as := by
      cases r with
      | nil => simp at h
      | cons b as => exact ⟨b, as, rfl⟩
    simp only [accN, List.map_cons, combBound, combCoeffs, toRow]
    rw [map_val_zipWith_step, ih]
    simp [List.map_map, Function.comp_def]

theorem checkPacked_check (m n B code : Nat) (lam : List Nat)
    (h : checkPacked m n B code lam = true) : check n (decodeRows m n B code) lam = true := by
  have hlen := length_of_mem_unpack B (B ^ (n + 1)) (n + 1) m code
  have hv := map_val_accN n lam _ hlen
  unfold checkPacked at h
  split at h
  · rename_i pq cols hacc
    rw [hacc, List.map_cons] at hv
    obtain ⟨hb, hc⟩ := List.cons.inj hv
    simp only [Bool.and_eq_true, Nat.blt_eq, List.all_eq_true, beq_iff_eq] at h
    obtain ⟨hlt, hcols⟩ := h
    have hrows : ∀ r ∈ decodeRows m n B code, r.coeffs.length = n := by
      intro r hr
      simp only [decodeRows, List.mem_map] at hr
      obtain ⟨zr, hzr, rfl⟩ := hr
      have := hlen zr hzr
      cases zr with
      | nil => simp at this
      | cons b as => simpa [toRow] using this
    simp only [check, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
    refine ⟨⟨hrows, ?_⟩, ?_⟩
    · rw [List.eq_replicate_iff]
      refine ⟨length_combCoeffs n lam _ hrows, fun x hx => ?_⟩
      rw [decodeRows, ← hc] at hx
      simp only [List.mem_map] at hx
      obtain ⟨c, hc', rfl⟩ := hx
      simp [val, hcols c hc']
    · simp only [decodeRows, ← hb, val]
      omega
  · simp at h

/-- **Soundness** of the packed checker. -/
theorem checkPacked_sound (m n B code : Nat) (lam : List Nat)
    (h : checkPacked m n B code lam = true) :
    ∀ x : List Int, ¬ ∀ r ∈ decodeRows m n B code, r.Holds x :=
  farkas_sound n _ lam (checkPacked_check m n B code lam h)

end LeanGpu
