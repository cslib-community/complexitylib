/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.DenseCore
import Mathlib.Tactic

/-! Theorem 1.7 of submission 865: the threshold and a nonvacuous instance. -/

namespace CslibFrontierTests.CircuitDenseCore
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication Formula

/-- At `m = 2` and relative density exactly `(1 + 2^{1-2})/3 = 1/2`, the accuracy bound of
Lemma 6.2 is exactly `2/3`: the strict hardness of `S` is what excludes the depth. -/
example : (1 : ℝ) / 2 + (2 ^ 2 * ((1 + 2 / (2 : ℝ) ^ 2) / 3) - 1) / (2 * (2 ^ 2 - 1)) = 2 / 3 := by
  norm_num

/-- The threshold lemma at `m = 2` and density `1/2`. -/
example : (2 : ℝ) / 3 ≤ 1 / 2 + (2 ^ 2 * (1 / 2) - 1) / (2 * (2 ^ 2 - 1)) :=
  two_thirds_le_half_add (m := 2) (by norm_num) (by norm_num)

private theorem pow_lt_two_mul_two_pow {a b c : ℕ} (ha : a ≤ 2 ^ 9) (hbc : 9 * b ≤ c) :
    a ^ b < 2 * 2 ^ c := by
  have h₁ : a ^ b ≤ 2 ^ c :=
    (Nat.pow_le_pow_left ha b).trans ((pow_mul 2 9 b).symm.le.trans
      (Nat.pow_le_pow_right two_pos hbc))
  have h₂ : 0 < 2 ^ c := pow_pos two_pos c
  omega

/-- `coreLoss 80 = 4 · 7 + 9 + 33 = 70`. -/
private theorem coreLoss_eighty : coreLoss 80 = 70 := by
  simp only [coreLoss, show Nat.clog 2 80 = 7 by decide, show Nat.clog 2 (4 * 80 + 4) = 9 by decide]

/-- **A nonvacuous instance.** Some function on `80` bits has formula depth above `76`, by
counting. For it, one nonempty `S` makes every dense `X ⊆ Sᵐ`, for every `m ≥ 1`, need at least
`77 - 70 = 7` bits. -/
private theorem exists_deep_core : ∃ g : BooleanFunction 80, ∃ S : Finset (BitString 80),
    S.Nonempty ∧ ∀ m, 1 ≤ m → ∀ X : Finset (Fin m → BitString 80), (∀ Z ∈ X, ∀ i, Z i ∈ S) →
      (2 ^ (m - 1) + 1) * S.card ^ m ≤ 3 * 2 ^ (m - 1) * X.card →
        (7 : ℕ∞) ≤ Protocol.ecomplexity (composeKW g) (X : Set (Fin m → BitString 80))
          (X : Set (Fin m → BitString 80)) := by
  obtain ⟨g, hg⟩ := exists_lt_formulaDepth (n := 80) (t := 76)
    (pow_lt_two_mul_two_pow (by norm_num) (by norm_num))
  obtain ⟨S, hS, h⟩ := exists_core g
  refine ⟨g, S, hS, fun m hm X hXS hX => ?_⟩
  have h' := h m hm X hXS hX
  rw [coreLoss_eighty] at h'
  generalize Protocol.ecomplexity (composeKW g) (X : Set (Fin m → BitString 80))
    (X : Set (Fin m → BitString 80)) = c at h' ⊢
  induction c using ENat.recTopCoe with
  | top => exact le_top
  | coe k =>
    have : formulaDepth g ≤ k + 70 := by exact_mod_cast h'
    exact_mod_cast (show 7 ≤ k by omega)

/-- **At the density threshold.** For that `S`, a subset of `S²` with half of its matrices,
rounded up, meets the hypothesis `3 |S|² ≤ 6 |X|`. That is exactly relative density
`(1 + 2^{1-2})/3 = 1/2` when `|S|²` is even, and it still needs `7` bits. -/
example : ∃ g : BooleanFunction 80, ∃ S : Finset (BitString 80),
    ∃ X : Finset (Fin 2 → BitString 80),
    (∀ Z ∈ X, ∀ i, Z i ∈ S) ∧ X.card = (S.card ^ 2 + 1) / 2 ∧
      (7 : ℕ∞) ≤ Protocol.ecomplexity (composeKW g) (X : Set (Fin 2 → BitString 80))
        (X : Set (Fin 2 → BitString 80)) := by
  obtain ⟨g, S, hS, h⟩ := exists_deep_core
  have hcard : (Fintype.piFinset fun _ : Fin 2 => S).card = S.card ^ 2 := by simp
  obtain ⟨X, hXS, hX⟩ := Finset.exists_subset_card_eq
    (s := Fintype.piFinset fun _ : Fin 2 => S) (n := (S.card ^ 2 + 1) / 2) (by rw [hcard]; omega)
  have hsub : ∀ Z ∈ X, ∀ i, Z i ∈ S := fun Z hZ i => Fintype.mem_piFinset.1 (hXS hZ) i
  exact ⟨g, S, X, hsub, hX, h 2 (by norm_num) X hsub (by rw [hX]; norm_num; omega)⟩

end CslibFrontierTests.CircuitDenseCore
