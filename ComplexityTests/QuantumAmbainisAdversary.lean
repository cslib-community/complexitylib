/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.AmbainisAdversary.Symmetric
import Complexity.Computability.QueryComplexity.Quantum.AmbainisAdversary.Tribes
import Complexity.Computability.QueryComplexity.Quantum.UnknownSearch
import ComplexityTests.QuantumPolynomial

/-! Ambainis's adversary method: a concrete relation that meets the counting hypotheses of the
core bound (with nonempty `R`), and the parity, threshold, majority, Tribes and `AND`-of-`OR`s
bounds applied to the exact one-query algorithm `readBit` and to the `OR_N` algorithm `orSearch`.
This shows that their hypotheses are satisfiable by non-constant functions. -/

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

-- `readBit` tells weight `1` from weight `0` on one bit with error `0`.
example :
    (1 - 2 * √((0 : ℝ) * (1 - 0))) * √((1 : ℕ) * ((1 : ℕ) + 1 - (1 : ℕ))) ≤ 2 * (1 : ℕ) := by
  refine one_sub_mul_sqrt_le_two_mul_of_weight readBit norm_ψ₀ 1 accept (k := 1) (ε := 0)
    (fun x hx => ?_) (fun y hy => ?_) (by norm_num)
  · rw [measureProb_readBit]
    have : x 0 = true := by
      by_contra h
      rw [weight, card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ => by
        rw [Subsingleton.elim i 0]
        simpa using h)] at hx
      exact zero_ne_one hx
    rw [this, bitVal_true]
    norm_num
  · rw [measureProb_readBit]
    have : y 0 = false := by
      by_contra h
      have : 1 ≤ weight y := card_pos.2 ⟨0, by simpa using h⟩
      omega
    rw [this, bitVal_false]

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

end ComplexityTests.QuantumAmbainisAdversary
