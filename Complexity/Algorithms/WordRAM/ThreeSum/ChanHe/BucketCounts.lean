/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.Collisions

/-!
# Histogram buckets for the native Chan–He node construction

These bridges identify position counts with the existing set-based buckets. Injectivity is
essential: two positions containing the same integer do not make that integer heavy.
The proofs are original; no source machine semantics is used.

## Main definitions

* `residueKey`: the unsigned Euclidean key already computed by `Count.program`.

## Main results

* `count_eq_card_bucket`: histogram counts equal bucket cardinalities.
* `mem_heavy_iff_count`: the native count test recognizes the existing heavy subset.

## References

* [T. M. Chan and Q. He, *Reducing 3SUM to Convolution-3SUM*][ChanHe2020]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

open Finset Cslib.Algorithms.ThreeSum.ChanHe

/-- The ordinary unsigned remainder of an integer modulo a positive natural modulus. -/
def residueKey (M : ℕ) (z : ℤ) : ℕ := (z % (M : ℤ)).toNat

/-- Interpreting a key as an integer recovers its Euclidean remainder. -/
theorem residueKey_cast {M : ℕ} (hM : 0 < M) (z : ℤ) :
    (residueKey M z : ℤ) = z % (M : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

/-- Every key is a valid histogram address offset. -/
theorem residueKey_lt {M : ℕ} (hM : 0 < M) (z : ℤ) : residueKey M z < M := by
  have := residueKey_cast hM z
  have := Int.emod_lt_of_pos z (show (0 : ℤ) < M by omega)
  omega

/-- Filtering positions before taking their image gives exactly the existing bucket. -/
theorem bucket_image (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M) (b : ℕ) :
    bucket ((range n).image values) M b =
      ({i ∈ range n | residueKey M (values i) = b}).image values := by
  ext z
  simp only [bucket, mem_filter, mem_image]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hb⟩
    exact ⟨i, ⟨hi, by rw [residueKey, hb]; simp⟩, rfl⟩
  · rintro ⟨i, ⟨hi, hb⟩, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, by rw [← residueKey_cast hM, hb]⟩

/-- Injective input enumeration makes the native histogram a set-cardinality computation. -/
theorem count_eq_card_bucket (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(range n) : Set ℕ)) (b : ℕ) :
    Histogram.count (fun i => residueKey M (values i)) n b =
      (bucket ((range n).image values) M b).card := by
  rw [bucket_image values n hM b, card_image_of_injOn (hinj.mono (by
    intro i hi
    exact (mem_filter.mp hi).1))]
  rfl

/-- A member is heavy precisely when its residue bucket has at least two elements. -/
theorem mem_heavy_iff_bucket {S : Finset ℤ} {M : ℕ} {z : ℤ} (hz : z ∈ S) :
    z ∈ heavy S M ↔ 1 < (bucket S M (z % (M : ℤ))).card := by
  have hzB : z ∈ bucket S M (z % (M : ℤ)) := mem_filter.mpr ⟨hz, rfl⟩
  rw [heavy, mem_filter, and_iff_right hz]
  constructor
  · rintro ⟨y, hy, hne, hd⟩
    have hyB : y ∈ bucket S M (z % (M : ℤ)) :=
      mem_filter.mpr ⟨hy, ((natCast_dvd_sub_iff_emod_eq M z y).mp hd).symm⟩
    have hsub : {z, y} ⊆ bucket S M (z % (M : ℤ)) := by
      intro a ha
      rcases mem_insert.mp ha with rfl | ha
      · exact hzB
      · exact (mem_singleton.mp ha) ▸ hyB
    have := card_le_card hsub
    have hc : 2 ≤ (bucket S M (z % (M : ℤ))).card := by simpa [hne.symm] using this
    omega
  · intro hc
    have hnot : ¬bucket S M (z % (M : ℤ)) ⊆ {z} := by
      intro h
      have := card_le_card h
      simp only [card_singleton] at this
      omega
    obtain ⟨y, hy, hne⟩ := not_subset.mp hnot
    obtain ⟨hyS, hyR⟩ := mem_filter.mp hy
    exact ⟨y, hyS, by simpa only [mem_singleton] using hne,
      (natCast_dvd_sub_iff_emod_eq M z y).mpr hyR.symm⟩

/-- The count test in the native scan selects exactly `ChanHe.heavy`. -/
theorem mem_heavy_iff_count (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(range n) : Set ℕ)) {i : ℕ} (hi : i < n) :
    values i ∈ heavy ((range n).image values) M ↔
      1 < Histogram.count (fun j => residueKey M (values j)) n (residueKey M (values i)) := by
  rw [count_eq_card_bucket values n hM hinj, residueKey_cast hM]
  exact mem_heavy_iff_bucket (mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩)

/-- An input position contributes at least one to its own bucket. -/
theorem count_residue_pos (values : ℕ → ℤ) (n M : ℕ) {i : ℕ} (hi : i < n) :
    0 < Histogram.count (fun j => residueKey M (values j)) n (residueKey M (values i)) := by
  exact card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_range.mpr hi, rfl⟩⟩

/-- A singleton histogram bucket gives the exact set and hence its unique light value. -/
theorem bucket_eq_singleton_of_count (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M)
    (hinj : Set.InjOn values (↑(range n) : Set ℕ)) {i : ℕ} (hi : i < n)
    (hc : Histogram.count (fun j => residueKey M (values j)) n
      (residueKey M (values i)) = 1) :
    bucket ((range n).image values) M (residueKey M (values i)) = {values i} := by
  have hm : values i ∈ bucket ((range n).image values) M (residueKey M (values i)) :=
    mem_filter.mpr ⟨mem_image.mpr ⟨i, mem_range.mpr hi, rfl⟩,
      (residueKey_cast hM _).symm⟩
  have hcard := (count_eq_card_bucket values n hM hinj (residueKey M (values i))).symm.trans hc
  obtain ⟨z, hz⟩ := card_eq_one.mp hcard
  rw [hz, mem_singleton] at hm
  exact hz.trans (congrArg singleton hm.symm)

/-- No two distinct positions can be light in the same bucket, even before injectivity is used. -/
theorem eq_of_count_one (values : ℕ → ℤ) (n M : ℕ) {i j : ℕ}
    (hi : i < n) (hj : j < n)
    (hc : Histogram.count (fun k => residueKey M (values k)) n (residueKey M (values i)) = 1)
    (he : residueKey M (values i) = residueKey M (values j)) : i = j := by
  have hi' : i ∈ {k ∈ range n | residueKey M (values k) = residueKey M (values i)} :=
    mem_filter.mpr ⟨mem_range.mpr hi, rfl⟩
  have hj' : j ∈ {k ∈ range n | residueKey M (values k) = residueKey M (values i)} :=
    mem_filter.mpr ⟨mem_range.mpr hj, he.symm⟩
  obtain ⟨k, hk⟩ := card_eq_one.mp hc
  rw [hk, mem_singleton] at hi' hj'
  exact hi'.trans hj'.symm

/-- Residue equality is unchanged by simultaneous negation. -/
theorem residueKey_neg_eq_iff {M : ℕ} (hM : 0 < M) (a b : ℤ) :
    residueKey M (-a) = residueKey M (-b) ↔ residueKey M a = residueKey M b := by
  rw [← Int.natCast_inj, residueKey_cast hM, residueKey_cast hM,
    ← Int.natCast_inj, residueKey_cast hM, residueKey_cast hM]
  change -a ≡ -b [ZMOD (M : ℤ)] ↔ a ≡ b [ZMOD (M : ℤ)]
  exact Int.neg_modEq_neg

/-- A histogram built on original residues also classifies the negated third set exactly. -/
theorem count_neg_residue (values : ℕ → ℤ) (n : ℕ) {M : ℕ} (hM : 0 < M) (i : ℕ) :
    Histogram.count (fun j => residueKey M (-values j)) n (residueKey M (-values i)) =
      Histogram.count (fun j => residueKey M (values j)) n (residueKey M (values i)) := by
  simp only [Histogram.count, residueKey_neg_eq_iff hM]

/-- Every bucket at an index beyond the modulus is empty. -/
theorem bucket_eq_empty_of_le (S : Finset ℤ) {M i : ℕ} (hM : 0 < M) (hi : M ≤ i) :
    bucket S M i = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have he := (mem_filter.mp hz).2
  have := Int.emod_lt_of_pos z (show (0 : ℤ) < M by omega)
  omega

/-- The first two light arrays equal their prescribed padding beyond the modulus. -/
theorem arrXY_eq_pad_of_le (S : Finset ℤ) {M i : ℕ} (hM : 0 < M) (hi : M ≤ i) (U : ℕ) :
    arrXY S M U i = pad U := by
  simp [arrXY, arr, bucket_eq_empty_of_le S hM hi]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe
