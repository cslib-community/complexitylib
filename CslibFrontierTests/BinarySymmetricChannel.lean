/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Code.BallVolume
import CslibFrontier.Probability.BitString.BinarySymmetricChannel.Achievability
import Mathlib.Tactic.NormNum

/-!
# Tests: the binary symmetric channel and Shannon achievability

* The channel `BSC_{1/4}` delivers a word at distance one from the input with probability
  `(1/4) (3/4)² = 9/64`.
* Over the noiseless channel `BSC_0` every nearest codeword decoder of an injective code is exact.
* The length-three repetition code: every nearest codeword decoder errs exactly when at least two
  bits flip, so its error probability is `3 p² (1 - p) + p³`; a constant decoder is not a nearest
  codeword decoder.
* The finite random-coding bound gives an explicit code with two codewords of length seven whose
  maximal error on `BSC_{1/100}` is below `1/2`.
* The entropy bounds on Hamming balls at small parameters.
* The asymptotic theorem is not vacuous: rate `1/2` over `BSC_0`, and rate `(1 - h₂(p)) / 2 > 0`
  for every `p < 1/2`.
-/

namespace ComplexityTests.BinarySymmetricChannel

open Cslib Cslib.BitString Finset Real
open scoped unitInterval

/-! ### The channel -/

/-- `BSC_{1/4}` turns `000` into `100` with probability `(1/4) (3/4)² = 9/64`. -/
example : (bsc (⟨1 / 4, by norm_num, by norm_num⟩ : I) ![false, false, false]
    ![true, false, false]).toReal = 9 / 64 := by
  rw [bsc_apply_toReal]
  have h : hammingDist ![false, false, false] ![true, false, false] = 1 := by decide
  rw [h, Fintype.card_fin]
  norm_num

/-! ### The noiseless channel -/

/-- Over `BSC_0` a nearest codeword decoder of an injective code never errs. -/
example {M : Type*} {n : ℕ} {E : M → BitString n} {D : BitString n → M}
    (hD : IsNearestDecoder E D) (hE : Function.Injective E) (m : M) :
    decodingError 0 E D m = 0 :=
  decodingError_zero_eq_zero (hD.leftInverse hE) m

/-! ### The repetition code of length three -/

/-- The repetition code of length three. -/
private def rep3 (b : Bool) : BitString 3 := fun _ => b

/-- A constant decoder is not a nearest codeword decoder of the repetition code. -/
example : ¬ IsNearestDecoder rep3 (fun _ => true) := fun h => by
  have := h (rep3 false) false
  revert this
  decide

/-- The distances from the received word `rep3 b + e` to the two codewords. -/
private theorem hammingDist_rep3 (b : Bool) (e : BitString 3) :
    hammingDist (rep3 b) (rep3 b + e) = weight e ∧
      hammingDist (rep3 (!b)) (rep3 b + e) = 3 - weight e := by
  revert b e
  decide

/-- A nearest codeword decoder of the repetition code errs exactly when at least two bits flip. -/
private theorem decode_rep3_ne_iff {D : BitString 3 → Bool} (hD : IsNearestDecoder rep3 D)
    (b : Bool) (e : BitString 3) : D (rep3 b + e) ≠ b ↔ 1 < weight e := by
  obtain ⟨h₁, h₂⟩ := hammingDist_rep3 b e
  have hw : weight e ≤ 3 := (weight_le e).trans_eq (Fintype.card_fin 3)
  have hb := hD (rep3 b + e) b
  have hnb := hD (rep3 b + e) (!b)
  rw [h₁] at hb
  rw [h₂] at hnb
  constructor
  · intro hne
    have hD' : D (rep3 b + e) = !b := by cases b <;> simpa using hne
    rw [hD', h₂] at hb
    omega
  · intro hlt heq
    rw [heq, h₁] at hnb
    omega

/-- The error probability of every nearest codeword decoder of the repetition code of length three
on `BSC_p` is `3 p² (1 - p) + p³`. -/
example {D : BitString 3 → Bool} (hD : IsNearestDecoder rep3 D) (p : I) (b : Bool) :
    decodingError p rep3 D b = 3 * p ^ 2 * (1 - p) + p ^ 3 := by
  rw [decodingError_eq_bernoulliAverage]
  have h : (fun e : BitString 3 => if D (rep3 b + e) ≠ b then (1 : ℝ) else 0) =
      fun e => if 1 < weight e then 1 else 0 :=
    funext fun e => if_congr (decode_rep3_ne_iff hD b e) rfl rfl
  rw [h, bernoulliAverage_lt_weight, Fintype.card_fin]
  simp only [sum_filter, sum_range_succ, range_zero, sum_empty]
  norm_num

/-! ### An explicit instance of the finite bound -/

/-- Some code with two codewords of length seven has maximal error below `1/2` on `BSC_{1/100}`,
for every nearest codeword decoder: the finite bound at radius one. -/
example : ∃ E : Fin 2 → BitString 7, ∀ D, IsNearestDecoder E D → ∀ k,
    decodingError ⟨1 / 100, by norm_num, by norm_num⟩ E D k < 1 / 2 := by
  obtain ⟨E, hE⟩ := exists_code_decodingError_le (ι := Fin 7)
    (⟨1 / 100, by norm_num, by norm_num⟩ : I) 1 2
  refine ⟨E, fun D hD k => (hE D hD k).trans_lt ?_⟩
  simp only [Fintype.card_fin, sum_filter, sum_range_succ, range_zero, sum_empty]
  norm_num [Nat.choose]

/-! ### Entropy bounds on Hamming balls -/

/-- `C(4, 0) + C(4, 1) = 5 ≤ exp (4 h(1/4))`. -/
example : (∑ j ∈ range 2, ((4 : ℕ).choose j : ℝ)) ≤ exp (4 * binEntropy (1 / 4)) := by
  have h := sum_choose_le_exp_mul_binEntropy (n := 4) (r := 1) (α := 1 / 4) (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-- The ball of radius one about any word of `Fin 2 → Fin 3` has at most `exp (2 H₃(1/2))` words.
-/
example (x : Fin 2 → Fin 3) :
    (#{y : Fin 2 → Fin 3 | hammingDist x y ≤ 1} : ℝ) ≤ exp (2 * qaryEntropy 3 (1 / 2)) := by
  have h := Code.card_filter_hammingDist_le_le_exp_mul_qaryEntropy (β := fun _ : Fin 2 => Fin 3)
    (q := 3) (r := 1) (α := 1 / 2) (by norm_num) (fun _ => Fintype.card_fin 3) x (by norm_num)
    (by norm_num) (by norm_num)
  simpa using h

/-! ### Nonvacuity of the asymptotic theorem -/

/-- Over the noiseless channel, rate `1/2` is achievable with any error `ε > 0`. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ E : Fin (2 ^ ⌈(1 / 2 : ℝ) * n⌉₊) → BitString n,
      ∀ D, IsNearestDecoder E D → ∀ k, decodingError 0 E D k ≤ ε := by
  have hR : (1 / 2 : ℝ) < 1 - binEntropy ((0 : I) : ℝ) / log 2 := by
    rw [Set.Icc.coe_zero, binEntropy_zero, zero_div, sub_zero]
    norm_num
  exact eventually_exists_code_decodingError_le 0 (by norm_num) hR hε

/-- For every `p < 1/2` the rate `(1 - h₂(p)) / 2` is positive and achievable with an exponentially
small maximal error. -/
example (p : I) (hp : (p : ℝ) < 1 / 2) :
    0 < (1 - binEntropy p / log 2) / 2 ∧
      ∃ δ > 0, ∀ n : ℕ, ∃ E : Fin (2 ^ ⌈(1 - binEntropy p / log 2) / 2 * n⌉₊) → BitString n,
        ∀ D, IsNearestDecoder E D → ∀ k, decodingError p E D k ≤ 10 * exp (-(δ * n)) := by
  have hcap : 0 < 1 - binEntropy p / log 2 := by
    rw [sub_pos, div_lt_one (log_pos one_lt_two)]
    exact binEntropy_lt_log_two.mpr (by linarith)
  exact ⟨by linarith, exists_pos_forall_exists_code_decodingError_le_exp p hp (by linarith)⟩

end ComplexityTests.BinarySymmetricChannel
