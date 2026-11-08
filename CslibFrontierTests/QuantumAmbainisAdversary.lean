/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Symmetric
import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.Tribes
import CslibFrontier.Computability.QueryComplexity.Quantum.AmbainisAdversary.WeightLayers
import CslibFrontier.Computability.QueryComplexity.Quantum.UnknownSearch
import CslibFrontierTests.QuantumPolynomial

/-! Ambainis's adversary method: a concrete relation that meets the counting hypotheses of the
core bound (with nonempty `R`), and the parity, threshold, majority, Tribes, `AND`-of-`OR`s and
weight-layer (Nayak–Wu) bounds applied to the exact one-query algorithm `readBit` and to the
`OR_N` algorithm `orSearch`. This shows that their hypotheses are satisfiable by non-constant
functions. -/

namespace ComplexityTests.QuantumAmbainisAdversary

open Cslib Cslib.Quantum Cslib.BitString Finset
open ComplexityTests.QuantumPolynomial

/-! ### The core bound on a concrete relation

The single-bit-flip relation between the odd and the even strings of two bits: every first input
has two partners, every second input has two, and along each coordinate each input has one. -/

/-- The four related pairs `(10, 00)`, `(10, 11)`, `(01, 00)`, `(01, 11)`. -/
def parityPairs : Finset (BitString 2 × BitString 2) :=
  {(![true, false], ![false, false]), (![true, false], ![true, true]),
    (![false, true], ![false, false]), (![false, true], ![true, true])}

theorem parityPairs_nonempty : parityPairs.Nonempty := by decide

theorem two_le_card_fst : ∀ p ∈ parityPairs, 2 ≤ #{q ∈ parityPairs | q.1 = p.1} := by decide

theorem two_le_card_snd : ∀ p ∈ parityPairs, 2 ≤ #{q ∈ parityPairs | q.2 = p.2} := by decide

theorem card_mul_card_le_one : ∀ p ∈ parityPairs, ∀ i, p.1 i ≠ p.2 i →
    #{q ∈ parityPairs | q.1 i ≠ q.2 i ∧ q.1 = p.1} *
      #{q ∈ parityPairs | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ 1 := by decide

-- Theorem 6 on this relation: `(1 - δ) √(2 · 2) ≤ 2T √1` for any algorithm on two bits.
example {W : Type} [Fintype W] (U : ℕ → State 2 W →ₗᵢ[ℂ] State 2 W) {ψ : State 2 W}
    (hψ : ‖ψ‖ = 1) (T : ℕ) {δ : ℝ}
    (hδ : ∀ p ∈ parityPairs, ‖inner ℂ (run U ψ p.1 T) (run U ψ p.2 T)‖ ≤ δ) :
    (1 - δ) * √((2 : ℕ) * (2 : ℕ)) ≤ 2 * T * √(1 : ℕ) :=
  one_sub_mul_sqrt_le_two_mul_mul_sqrt U hψ T parityPairs_nonempty hδ two_le_card_fst
    two_le_card_snd card_mul_card_le_one

/-! ### Parity, threshold and majority -/

-- `readBit` computes `PARITY_1` exactly, so it meets the bounded-error hypothesis.
example : 1 ≤ 36 * 1 :=
  card_le_thirty_six_mul_of_parity readBit norm_ψ₀ 1 accept fun x => by
    rw [measureProb_readBit]
    have : parity 1 x = x 0 := by
      cases h : x 0 <;> simp [parity, parityOn_eq_sum, h]
    rw [this, sub_self, abs_zero]
    norm_num

/-- `readBit` accepts every string of weight `1` with certainty. -/
theorem readBit_weight_one (x : BitString 1) (hx : weight x = 1) :
    1 - (0 : ℝ) ≤ measureProb (run readBit ψ₀ x 1) accept := by
  rw [measureProb_readBit]
  have : x 0 = true := by
    by_contra h
    rw [weight, card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => by
      rw [Subsingleton.elim i 0]
      simpa using h)] at hx
    exact zero_ne_one hx
  rw [this, bitVal_true]
  norm_num

/-- `readBit` rejects every string of weight `0` with certainty. -/
theorem readBit_weight_zero (y : BitString 1) (hy : weight y = 0) :
    measureProb (run readBit ψ₀ y 1) accept ≤ 0 := by
  rw [measureProb_readBit]
  have : y 0 = false := by
    by_contra h
    have : 1 ≤ weight y := card_pos.2 ⟨0, by simpa using h⟩
    omega
  rw [this, bitVal_false]

-- `readBit` tells weight `1` from weight `0` on one bit with error `0`.
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √((1 : ℕ) * ((1 : ℕ) + 1 - (1 : ℕ))) ≤ 2 * (1 : ℕ) :=
  one_sub_mul_sqrt_le_two_mul_of_weight readBit norm_ψ₀ 1 accept (k := 1) (ε := 0)
    readBit_weight_one (fun y hy => readBit_weight_zero y (by omega)) (by norm_num)

-- `readBit` computes `MAJ_1`, the threshold function `Th^1_1`, exactly.
example : 1 ≤ 72 * 1 :=
  card_le_seventy_two_mul_of_majority readBit norm_ψ₀ 1 accept fun x => by
    rw [majority, measureProb_readBit_threshold, sub_self, abs_zero]
    norm_num

-- `orSearch` computes `OR_N = Th^N_1` with error `1/3` in `T = 2 · orRange N` queries, so the
-- threshold bound gives the `Ω(√N)` search lower bound `(1 - 2√(2/9)) √N ≤ 2T`.
example (N : ℕ) (hN : 0 < N) :
    (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) * √((1 : ℕ) * (N + 1 - (1 : ℕ))) ≤
      2 * (orRange N + orRange N : ℕ) :=
  one_sub_mul_sqrt_le_two_mul_of_threshold (orSearch N) (norm_orSearchInit hN) _ (orAccept N)
    (abs_measureProb_run_orSearch_sub_le hN) (by norm_num)

/-! ### Tribes and the `AND` of `OR`s -/

/-- With one tribe of one bit, Tribes reads the bit. -/
theorem tribes_one_one (x : BitString (1 * 1)) : tribes 1 1 x = x 0 := by
  have h : ∀ (j i : Fin 1), finProdFinEquiv (j, i) = (0 : Fin (1 * 1)) := by decide
  cases hx : x 0 <;> simp [tribes, h, hx]

/-- With one block of one bit, the `AND` of `OR`s reads the bit. -/
theorem forall_exists_one_one (x : BitString (1 * 1)) :
    decide (∀ j : Fin 1, ∃ i : Fin 1, x (finProdFinEquiv (j, i)) = true) = x 0 := by
  have h : ∀ (j i : Fin 1), finProdFinEquiv (j, i) = (0 : Fin (1 * 1)) := by decide
  cases hx : x 0 <;> simp [h, hx]

example : 1 * 1 ≤ 1296 * 1 ^ 2 :=
  mul_le_mul_sq_of_tribes (w := 1) (s := 1) readBit norm_ψ₀ 1 accept fun x _ => by
    rw [measureProb_readBit, tribes_one_one, sub_self, abs_zero]
    norm_num

example : 1 * 1 ≤ 1296 * 1 ^ 2 :=
  mul_le_mul_sq_of_forall_exists (w := 1) (s := 1) readBit norm_ψ₀ 1 accept fun x _ => by
    rw [measureProb_readBit, forall_exists_one_one, sub_self, abs_zero]
    norm_num

/-! ### Two weight layers and the Nayak–Wu bound -/

-- Weight `1` against weight `0` on `readBit`, error `0`: `√((1 - 0) · 1) ≤ 2 · 1 · |1 - 0|`.
example : (1 - 2 * √((0 : ℝ) * (1 - 0))) * √(((1 : ℕ) - (min 1 0 : ℕ)) * (max 1 0 : ℕ)) ≤
    2 * (1 : ℕ) * |((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)| :=
  one_sub_mul_sqrt_le_two_mul_mul_abs_sub_of_weight readBit norm_ψ₀ 1 accept (by decide) le_rfl
    (Nat.zero_le _) readBit_weight_one readBit_weight_zero (by norm_num)

-- Weights on both sides of `N/2 = 1/2` on `readBit`: `1 ≤ 4 · 1 · |1 - 0|`.
example : (1 - 2 * √((0 : ℝ) * (1 - 0))) * ((1 : ℕ) : ℝ) ≤
    4 * (1 : ℕ) * |((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)| :=
  one_sub_mul_card_le_four_mul_mul_abs_sub_of_weight readBit norm_ψ₀ 1 accept (by decide)
    (by decide) (by decide) le_rfl (Nat.zero_le _) readBit_weight_one readBit_weight_zero
    (by norm_num)

-- The Nayak–Wu bound on `orSearch`, which tells weight `1` from weight `0` with error `1/3`:
-- with `m = 0` it gives the search lower bound `(1 - 2√(2/9)) √N ≤ 4T`.
example (N : ℕ) (hN : 0 < N) :
    (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) *
        (√(N * |((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)|) + √(((0 : ℕ) : ℝ) * (N - ((0 : ℕ) : ℝ)))) ≤
      4 * (orRange N + orRange N : ℕ) * |((1 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)| := by
  refine one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight (orSearch N) (norm_orSearchInit hN) _
    (orAccept N) (k := 1) (k' := 0) (by decide) hN (Nat.zero_le _) (fun x hx => ?_)
    (fun y hy => ?_) (by norm_num) (Nat.zero_le _) (Nat.zero_le _)
  · have := (abs_le.1 (abs_measureProb_run_orSearch_sub_le hN x)).1
    rw [threshold_apply, decide_eq_true hx.ge, bitVal_true] at this
    linarith
  · have := (abs_le.1 (abs_measureProb_run_orSearch_sub_le hN y)).2
    rw [threshold_apply, decide_eq_false (by omega), bitVal_false] at this
    linarith

-- The Nayak–Wu bound on `orSearch` for weight `2` against weight `0` (`Δ = 2`), with `m = 1`:
-- `(1 - 2√(2/9)) (√(2N) + √(N - 1)) ≤ 8T`.
example (N : ℕ) (hN : 2 ≤ N) :
    (1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3))) *
        (√(N * |((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)|) + √(((1 : ℕ) : ℝ) * (N - ((1 : ℕ) : ℝ)))) ≤
      4 * (orRange N + orRange N : ℕ) * |((2 : ℕ) : ℝ) - ((0 : ℕ) : ℝ)| := by
  have hN0 : 0 < N := by omega
  refine one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight (orSearch N) (norm_orSearchInit hN0) _
    (orAccept N) (k := 2) (k' := 0) (by decide) hN (Nat.zero_le _) (fun x hx => ?_)
    (fun y hy => ?_) (by norm_num) (by decide) (by decide)
  · have := (abs_le.1 (abs_measureProb_run_orSearch_sub_le hN0 x)).1
    rw [threshold_apply, decide_eq_true (by omega), bitVal_true] at this
    linarith
  · have := (abs_le.1 (abs_measureProb_run_orSearch_sub_le hN0 y)).2
    rw [threshold_apply, decide_eq_false (by omega), bitVal_false] at this
    linarith

end ComplexityTests.QuantumAmbainisAdversary
