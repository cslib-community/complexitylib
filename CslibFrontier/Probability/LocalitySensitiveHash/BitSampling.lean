/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.LocalitySensitiveHash
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Probability.PMF.Uniform

/-!
# Bit sampling for the Hamming distance

The bit-sampling family of Indyk and Motwani [IndykMotwani1998] hashes a word `x : n → β` to one
coordinate `x i`, where the index `i` is uniform. Two words collide with probability
`1 - d_H(x, y) / |n|` (`Cslib.Probability.collisionProb_bitSampling`), so the family is
`(r₁, r₂, 1 - r₁ / |n|, 1 - r₂ / |n|)`-sensitive for the Hamming distance
(`Cslib.Probability.isLocalitySensitive_bitSampling`; [LeskovecRajaramanUllman2020], Section
3.7.1). The coordinates may take values in any alphabet `β`, not only bits.

## Main results

* `Cslib.Probability.collisionProb_bitSampling`: the exact collision probability.
* `Cslib.Probability.isLocalitySensitive_bitSampling`: sensitivity for the Hamming distance.

## References

* [P. Indyk, R. Motwani, *Approximate nearest neighbors: towards removing the curse of
  dimensionality*][IndykMotwani1998]
* [J. Leskovec, A. Rajaraman, J. D. Ullman,
  *Mining of Massive Datasets*][LeskovecRajaramanUllman2020], Section 3.7.1.
-/

public section

namespace Cslib.Probability

variable {n : Type*} [Fintype n] [Nonempty n] {β : Type*} [DecidableEq β]

/-- **Bit sampling** [IndykMotwani1998]: a uniformly random coordinate separates two words with
probability their relative Hamming distance. -/
theorem collisionProb_bitSampling (x y : n → β) :
    collisionProb (PMF.uniformOfFintype n) (fun i (z : n → β) => z i) x y =
      1 - (hammingDist x y : ℝ) / Fintype.card n := by
  classical
  rw [collisionProb, PMF.toOuterMeasure_uniformOfFintype_toReal]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset n)) (fun i => x i = y i)
  have hcard : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Set.mem_ofPred_eq]
  rw [hammingDist, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hcard]
  exact_mod_cast hsplit.trans Finset.card_univ

/-- Bit sampling is `(r₁, r₂, 1 - r₁ / |n|, 1 - r₂ / |n|)`-sensitive for the Hamming distance
([IndykMotwani1998]; [LeskovecRajaramanUllman2020], Section 3.7.1). -/
theorem isLocalitySensitive_bitSampling (r₁ r₂ : ℝ) :
    IsLocalitySensitive (collisionProb (PMF.uniformOfFintype n) (fun i (z : n → β) => z i))
      (fun x y => (hammingDist x y : ℝ) ≤ r₁) (fun x y => r₂ ≤ (hammingDist x y : ℝ))
      (1 - r₁ / Fintype.card n) (1 - r₂ / Fintype.card n) where
  le_of_near x y h := by
    rw [collisionProb_bitSampling]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)) 1
  le_of_far x y h := by
    rw [collisionProb_bitSampling]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg _)) 1

end Cslib.Probability
