/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.Placement
import Complexity.Computability.Complexity.FineGrained.PPZ

/-! PPSZ placements: values of the depth recursion, Beta integrals, the placement identity for
three variables, and instances of the Harris inequality and of one recursion step. -/

namespace ComplexityTests.PPSZPlacement

open Finset Cslib.Complexity.PPSZ

/-! ### The depth recursion -/

/-- Depth one recovers the PPZ bound `1 / k`. -/
example : qbar 3 1 = 1 / 3 := by
  rw [qbar_one (by norm_num)]
  norm_num

-- The library value `qbar 3 2 = 31 / 70` lies strictly between the depth-one bounds for
-- `k = 3` and `k = 2`.
example : qbar 3 1 < qbar 3 2 ∧ qbar 3 2 < qbar 2 1 := by
  rw [qbar_three_two, qbar_one (by norm_num), qbar_one (by norm_num)]
  norm_num

/-- `qbar 4 2 = 39653 / 120120`. -/
theorem qbar_four_two : qbar 4 2 = 39653 / 120120 := by
  let c : ℕ → ℝ := fun i => [0, 0, 0, 1, 0, 3, -3, 3, -6, 4, -3, 3, -1].getD i 0
  rw [qbar, intervalIntegral.integral_congr (g := fun r => ∑ i ∈ range 13, c i * r ^ i)
    fun r _ => by
      simp only [Q_succ, Q_zero, sum_range_succ, sum_range_zero, c, List.getD_cons_succ,
        List.getD_cons_zero]
      ring, integral_sum_mul_pow]
  norm_num [sum_range_succ, c]

/-- The bound grows with the depth. -/
example : qbar 3 1 ≤ qbar 3 2 := monotone_qbar (by norm_num)

/-! ### The Beta integral -/

example : ∫ r in (0 : ℝ)..1, r ^ 2 * (1 - r) ^ 3 = 1 / 60 := by
  rw [integral_pow_mul_one_sub_pow]
  norm_num [Nat.factorial]

example : ∫ r in (0 : ℝ)..1, (1 - r) ^ 4 = 1 / 5 := by
  rw [show (fun r : ℝ => (1 - r) ^ 4) = fun r => r ^ 0 * (1 - r) ^ 4 by
    funext r
    simp, integral_pow_mul_one_sub_pow]
  norm_num [Nat.factorial]

/-! ### Placements -/

/-- The set placed before `x` is the set PPZ has processed when it reaches `x`. -/
example {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n) :
    placedBefore π x = Cslib.Complexity.PPZ.prefixSet π (π.symm x) := rfl

/-- Exactly one of the six orders of three variables places only `1` before `0`. -/
example : #(univ.filter fun π : Equiv.Perm (Fin 3) => placedBefore π 0 = {1}) = 1 := by
  rw [card_filter_placedBefore_eq (by decide)]
  rfl

/-- Two orders place nothing before `0`, as `2 * (3 * C(2, 0)) = 3!`. -/
example : #(univ.filter fun π : Equiv.Perm (Fin 3) => placedBefore π 0 = ∅) * (3 * 1) = 6 := by
  simpa [Nat.factorial] using
    card_filter_placedBefore_mul_choose (n := 3) (x := 0) (S := ∅) (by simp)

/-- Variable `1` comes before variable `0` in half of the orders, by the placement integral. -/
example : #(univ.filter fun π : Equiv.Perm (Fin 3) => (1 : Fin 3) ∈ placedBefore π 0) = 3 := by
  have h := card_filter_placedBefore_div_factorial_eq_integral (0 : Fin 3) fun S => 1 ∈ S
  rw [intervalIntegral.integral_congr (g := fun r => r) fun r _ =>
    bernoulliProb_mem (by decide)] at h
  simp only [integral_id, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sub_zero, Nat.factorial, Nat.succ_eq_add_one, zero_add, mul_one] at h
  have : (#(univ.filter fun π : Equiv.Perm (Fin 3) => (1 : Fin 3) ∈ placedBefore π 0) : ℝ) = 3 := by
    linarith
  exact_mod_cast this

/-! ### Masks and subsets -/

/-- Through the bridge to masks, `BitString.bernoulliAverage_coordinate` gives the probability
that a fixed element is included. -/
example {U : Finset ℕ} {v : ℕ} (hv : v ∈ U) (r : ℝ) : bernoulliProb U r (fun S => v ∈ S) = r := by
  rw [bernoulliProb_eq_bernoulliAverage]
  refine Eq.trans ?_ (Cslib.BitString.bernoulliAverage_coordinate r (⟨v, hv⟩ : U))
  congr 1
  funext s
  have h : v ∈ ({i | s i} : Finset U).map (Function.Embedding.subtype (· ∈ U)) ↔ s ⟨v, hv⟩ := by
    simp [hv]
  simp only [h]

/-! ### Harris and the recursion step -/

/-- Two increasing events on three variables. -/
example {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    r * r ≤ bernoulliProb (univ : Finset (Fin 3)) r fun S => 1 ∈ S ∧ 2 ∈ S := by
  have h := bernoulliProb_mul_le (U := (univ : Finset (Fin 3))) hr
    (E := fun S => (1 : Fin 3) ∈ S) (F := fun S => (2 : Fin 3) ∈ S)
    (fun _ _ h h1 => h h1) (fun _ _ h h2 => h h2)
  rwa [bernoulliProb_mem (mem_univ _), bernoulliProb_mem (mem_univ _)] at h

/-- One recursion step from depth zero for `k = 3`: both children placed before the root. -/
example {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    Q 3 1 r ≤ bernoulliProb (univ : Finset (Fin 3)) r
      fun S => ∀ i ∈ ({1, 2} : Finset (Fin 3)), id i ∈ S ∨ False :=
  Q_succ_le_bernoulliProb_forall_or hr (fun i _ => mem_univ _) (fun _ _ _ _ _ h => h)
    (fun _ _ _ => Iff.rfl) (by decide) fun _ _ => by simp

end ComplexityTests.PPSZPlacement
