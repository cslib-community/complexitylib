/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Histogram
public import Complexity.Algorithms.ThreeSum.ChanHe.Collisions

/-!
# Histogram collision counts for Chan–He

The native histogram counts ordered pairs of different input positions. For an injective
array of integers and its Euclidean residue keys, this is exactly the existing Chan–He
collision count. Injectivity is required because the mathematical reduction operates on sets.
Equal input values must first be handled by the distinct-position frontend.

## Main results

* `coll_eq_histogramPairs`: the existing `coll` is the counter computed by the histogram.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

open Finset
open Cslib.Algorithms.ThreeSum.ChanHe

/-- For distinct array values, histogramming Euclidean residues computes exactly the
ordered distinct-element collision count of the existing Chan–He reduction. -/
theorem coll_eq_histogramPairs (values : ℕ → ℤ) (n M : ℕ) (hM : 0 < M)
    (hinj : Set.InjOn values (↑(range n) : Set ℕ)) :
    coll ((range n).image values) M =
      Histogram.pairs (fun i => (values i % (M : ℤ)).toNat) n := by
  rw [Histogram.pairs_eq_card]
  symm
  refine card_bij (fun p _ => (values p.1, values p.2)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp, heq⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂, hne⟩ := mem_offDiag.mp hp
    refine mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_image.mpr ⟨p.1, hp₁, rfl⟩,
      mem_image.mpr ⟨p.2, hp₂, rfl⟩, fun h => hne (hinj hp₁ hp₂ h)⟩, ?_⟩
    apply (natCast_dvd_sub_iff_emod_eq M _ _).mpr
    change values p.1 % (M : ℤ) = values p.2 % (M : ℤ)
    have hpos : (0 : ℤ) < M := by exact_mod_cast hM
    have h₁ := Int.emod_nonneg (values p.1) (ne_of_gt hpos)
    have h₂ := Int.emod_nonneg (values p.2) (ne_of_gt hpos)
    omega
  · intro p hp q hq heq
    have hp' := mem_offDiag.mp (mem_filter.mp hp).1
    have hq' := mem_offDiag.mp (mem_filter.mp hq).1
    exact Prod.ext (hinj hp'.1 hq'.1 (congrArg Prod.fst heq))
      (hinj hp'.2.1 hq'.2.1 (congrArg Prod.snd heq))
  · intro p hp
    obtain ⟨hp, hdvd⟩ := mem_filter.mp hp
    obtain ⟨hp₁, hp₂, hne⟩ := mem_offDiag.mp hp
    obtain ⟨i, hi, hival⟩ := mem_image.mp hp₁
    obtain ⟨j, hj, hjval⟩ := mem_image.mp hp₂
    refine ⟨(i, j), mem_filter.mpr ⟨mem_offDiag.mpr ⟨hi, hj, ?_⟩, ?_⟩, ?_⟩
    · intro hij
      change i = j at hij
      apply hne
      rw [← hival, ← hjval, hij]
    · have heq := (natCast_dvd_sub_iff_emod_eq M _ _).mp hdvd
      change (values i % (M : ℤ)).toNat = (values j % (M : ℤ)).toNat
      rw [hival, hjval, heq]
    · exact Prod.ext hival hjval

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe
