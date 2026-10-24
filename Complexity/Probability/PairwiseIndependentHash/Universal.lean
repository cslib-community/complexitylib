/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.UniversalHash
public import Complexity.Probability.PairwiseIndependentHash
import Complexity.Probability.PMF.Uniform
import Complexity.Probability.PMF

/-!
# Pairwise independent families are universal

A pairwise independent (strongly universal) family with a uniform seed is `1 / |Y|`-universal
and, when `Y` is an additive group, `1 / |Y|`-Δ-universal: for distinct inputs, the pair of
hashes is uniform on `Y × Y`, so every relation `h i x = g (h i x')` with `g : Y → Y` holds on a
`1 / |Y|` fraction of the seeds [CarterWegman1979], [WegmanCarter1981]. Every pairwise independent
family of the library, such as the affine and Toeplitz families and polynomial hashing of degree
at least one, is therefore universal and Δ-universal.

## Main results

* `Cslib.Probability.IsPairwiseIndependentHash.isUniversalHash`,
  `Cslib.Probability.IsPairwiseIndependentHash.isTwoUniversal`: pairwise independence implies
  `1 / |Y|`-universality (two-universality).
* `Cslib.Probability.IsPairwiseIndependentHash.isDeltaUniversalHash`: pairwise independence
  implies `1 / |Y|`-Δ-universality.

## References

* [J. L. Carter, M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
-/

@[expose] public section

namespace Cslib.Probability.IsPairwiseIndependentHash

open Finset
open scoped ENNReal

variable {ι X Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq Y] {h : ι → X → Y}

/-- For distinct inputs, the pair of hashes under a uniform seed is uniform on `Y × Y`. -/
theorem map_pair_eq_uniform [Nonempty ι] [Nonempty Y] (hh : IsPairwiseIndependentHash h)
    {x x' : X} (hx : x ≠ x') :
    (PMF.uniformOfFintype ι).map (fun i => (h i x, h i x')) = PMF.uniformOfFintype (Y × Y) := by
  ext ⟨a, b⟩
  have hd := hh.dens_filter_apply_eq_and_apply_eq hx a b
  have hcard : #{i | h i x = a ∧ h i x' = b} * Fintype.card Y ^ 2 = Fintype.card ι := by
    have hι : (Fintype.card ι : ℚ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hY : (Fintype.card Y : ℚ≥0) ^ 2 ≠ 0 := by
      exact pow_ne_zero _ (by exact_mod_cast Fintype.card_ne_zero)
    rw [dens, div_eq_iff hι] at hd
    have hq : (#{i | h i x = a ∧ h i x' = b} : ℚ≥0) * (Fintype.card Y : ℚ≥0) ^ 2 =
        Fintype.card ι := by
      rw [hd, mul_comm, ← mul_assoc, mul_inv_cancel₀ hY, one_mul]
    exact_mod_cast hq
  have hpos : #{i | h i x = a ∧ h i x' = b} ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hcard
    exact Fintype.card_ne_zero hcard.symm
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    PMF.uniformOfFintype_apply, Fintype.card_prod]
  have hpre : (fun i => (h i x, h i x')) ⁻¹' {(a, b)} = {i | h i x = a ∧ h i x' = b} := by
    ext i
    simp
  rw [hpre, PMF.toOuterMeasure_uniformOfFintype, ← hcard]
  simp only [Set.mem_ofPred_eq]
  push_cast
  rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast hpos)) (Or.inl (ENNReal.natCast_ne_top _)),
    ← mul_assoc, ENNReal.mul_inv_cancel (by exact_mod_cast hpos) (ENNReal.natCast_ne_top _),
    one_mul, sq]

/-- For distinct inputs and any `g : Y → Y`, a uniform seed gives `h i x = g (h i x')` with
probability exactly `1 / |Y|`. -/
theorem toOuterMeasure_apply_eq_comp [Nonempty ι] (hh : IsPairwiseIndependentHash h) {x x' : X}
    (hx : x ≠ x') (g : Y → Y) :
    (PMF.uniformOfFintype ι).toOuterMeasure {i | h i x = g (h i x')} =
      (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  classical
  have : Nonempty Y := ⟨h (Classical.arbitrary ι) x⟩
  have hpre : {i | h i x = g (h i x')} =
      (fun i => (h i x, h i x')) ⁻¹' {p : Y × Y | p.1 = g p.2} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, hh.map_pair_eq_uniform hx,
    PMF.toOuterMeasure_uniformOfFintype, Fintype.card_prod]
  have hcount : #(univ.filter fun p : Y × Y => p ∈ {p : Y × Y | p.1 = g p.2}) =
      Fintype.card Y := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr
      { toFun := fun p => p.1.2
        invFun := fun y => ⟨(g y, y), by simp⟩
        left_inv := fun ⟨⟨a, b⟩, hp⟩ => by
          simp only [mem_filter, mem_univ, Set.mem_ofPred_eq, true_and] at hp
          simp [hp]
        right_inv := fun _ => rfl }
  have hY : (Fintype.card Y : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hcount]
  push_cast
  rw [ENNReal.mul_inv (Or.inl hY) (Or.inl (ENNReal.natCast_ne_top _)), ← mul_assoc,
    ENNReal.mul_inv_cancel hY (ENNReal.natCast_ne_top _), one_mul]

/-- A pairwise independent family with a uniform seed is `1 / |Y|`-universal. -/
theorem isUniversalHash [Nonempty ι] (hh : IsPairwiseIndependentHash h) :
    IsUniversalHash (PMF.uniformOfFintype ι) h (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  fun _ _ hx => (hh.toOuterMeasure_apply_eq_comp hx id).le

/-- A pairwise independent family with a uniform seed is two-universal. -/
theorem isTwoUniversal [Nonempty ι] (hh : IsPairwiseIndependentHash h) :
    IsTwoUniversal (PMF.uniformOfFintype ι) h :=
  hh.isUniversalHash

/-- A pairwise independent family with a uniform seed, into an additive group, is
`1 / |Y|`-Δ-universal. -/
theorem isDeltaUniversalHash [AddGroup Y] [Nonempty ι] (hh : IsPairwiseIndependentHash h) :
    IsDeltaUniversalHash (PMF.uniformOfFintype ι) h (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  fun x x' hx d => by
    have hset : {i | h i x - h i x' = d} = {i | h i x = d + h i x'} := by
      ext i
      exact sub_eq_iff_eq_add
    rw [hset]
    exact (hh.toOuterMeasure_apply_eq_comp hx (d + ·)).le

end Cslib.Probability.IsPairwiseIndependentHash
