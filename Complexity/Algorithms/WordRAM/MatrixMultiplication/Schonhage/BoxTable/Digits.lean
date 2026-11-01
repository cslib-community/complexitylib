/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.BoxValues
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Meaning
public import Mathlib.Data.Nat.Count

/-!
# Geometry digits for the shared native box table

The flat leaf numbering is exactly the existing native encoder's numbering, with
level zero least significant and P0 digit nine. `population` and `starStride` describe
the scalar results of the native digit loop. Neither definition contains execution,
time, rank, layout or table hypotheses.

The canonical boxes are those of [AlmanWilliams2026, Section 4.2], already adapted in
`BoxValues`. The shared dense directory and compact enumeration are a new native
representation; their one-time setup is distinct from the source's per-tile trie.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Decode a complete leaf using the existing native encoder's finite digit dictionary. -/
@[expose] def leafAt {L : ℕ} (c : Fin (10 ^ L)) : Leaf L :=
  fun ℓ => Encoding.termDigits (finFunctionFinEquiv.symm c ℓ)

/-- Decoding and re-encoding uses the same actual flat array position. -/
@[simp] theorem leafIndex_leafAt {L : ℕ} (c : Fin (10 ^ L)) :
    Encoding.leafIndex (leafAt c) = c := by
  simp [Encoding.leafIndex, leafAt]

/-- Decoding an existing leaf index recovers every original term. -/
@[simp] theorem leafAt_leafIndex {L : ℕ} (τ : Leaf L) :
    leafAt (Encoding.leafIndex τ) = τ := by
  funext ℓ
  simp [leafAt, Encoding.leafIndex]

/-- The raw decimal digit at a level, in the existing least-significant-first layout. -/
@[expose] def digitAt (c k : ℕ) : ℕ := c / 10 ^ k % 10

/-- Number of P0 digits in the first `k` levels. -/
@[expose] def population (c k : ℕ) : ℕ := Nat.count (fun i => digitAt c i = 9) k

/-- The e-th P0 place value found by the scan; zero until that occurrence has been found. -/
@[expose] def starStride (c e : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if digitAt c k = 9 ∧ population c k + 1 = e then 10 ^ k else starStride c e k

/-- A leaf uses P0 at a level precisely when the actual native digit is nine. -/
theorem leafAt_eq_P0_iff {L : ℕ} (c : Fin (10 ^ L)) (ℓ : Fin L) :
    leafAt c ℓ = .P0 ↔ digitAt c.val ℓ.val = 9 := by
  have hd := finFunctionFinEquiv_symm_apply_val c ℓ
  constructor
  · intro h
    have h' := congrArg Encoding.termDigits.symm h
    simp only [leafAt, Equiv.symm_apply_apply] at h'
    change (finFunctionFinEquiv.symm c ℓ) = 9 at h'
    simp [digitAt, ← hd, h']
  · intro h
    have h' : finFunctionFinEquiv.symm c ℓ = 9 := Fin.ext (hd.trans h)
    simp [leafAt, h', Encoding.termDigits, Encoding.termAt]

/-- The scan's population is the existing finite P0-coordinate cardinality. -/
theorem population_eq_card_P0Levels {L : ℕ} (c : Fin (10 ^ L)) :
    population c.val L = (P0Levels (leafAt c)).card := by
  rw [population, Nat.count_eq_card_filter_range]
  symm
  refine card_bij (fun ℓ _ => ℓ.val) ?_ ?_ ?_
  · intro ℓ hℓ
    exact mem_filter.mpr ⟨mem_range.mpr ℓ.isLt,
      (leafAt_eq_P0_iff c ℓ).mp (mem_P0Levels.mp hℓ)⟩
  · intro ℓ _ ℓ' _ h
    exact Fin.ext h
  · intro k hk
    obtain ⟨hkL, hkd⟩ := mem_filter.mp hk
    exact ⟨⟨k, mem_range.mp hkL⟩,
      mem_P0Levels.mpr ((leafAt_eq_P0_iff c _).mpr hkd), rfl⟩

/-- A prefix scan counts precisely the P0 coordinates below its native level. -/
theorem population_eq_card_P0Levels_filter {L k : ℕ} (c : Fin (10 ^ L)) (hk : k ≤ L) :
    population c.val k = ((P0Levels (leafAt c)).filter fun ℓ => ℓ.val < k).card := by
  rw [population, Nat.count_eq_card_filter_range]
  symm
  refine card_bij (fun ℓ _ => ℓ.val) ?_ ?_ ?_
  · intro ℓ hℓ
    obtain ⟨hp, hlt⟩ := mem_filter.mp hℓ
    exact mem_filter.mpr ⟨mem_range.mpr hlt,
      (leafAt_eq_P0_iff c ℓ).mp (mem_P0Levels.mp hp)⟩
  · intro ℓ _ ℓ' _ h
    exact Fin.ext h
  · intro i hi
    obtain ⟨hilt, hid⟩ := mem_filter.mp hi
    have hiL : i < L := (mem_range.mp hilt).trans_le hk
    exact ⟨⟨i, hiL⟩, mem_filter.mpr
      ⟨mem_P0Levels.mpr ((leafAt_eq_P0_iff c _).mpr hid), mem_range.mp hilt⟩, rfl⟩

/-- No scan prefix contains more P0 digits than scanned levels. -/
theorem population_le (c k : ℕ) : population c k ≤ k := Nat.count_le _

@[simp] theorem population_zero (c : ℕ) : population c 0 = 0 := rfl

/-- Extend the ordinary Mathlib count by the next native digit test. -/
theorem population_succ (c k : ℕ) :
    population c (k + 1) = population c k + if digitAt c k = 9 then 1 else 0 := by
  simp [population, Nat.count_succ]

/-- A recorded stride fits below the final power used by the scan. -/
theorem starStride_le (c e k : ℕ) : starStride c e k ≤ 10 ^ k := by
  induction k with
  | zero => simp [starStride]
  | succ k ih =>
    rw [starStride]
    split
    · exact Nat.pow_le_pow_right (by decide) (by omega)
    · exact ih.trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Once the e-th P0 coordinate is reached, later digits preserve its exact place value. -/
theorem starStride_of_rank {c e j k : ℕ} (hjk : j < k)
    (hd : digitAt c j = 9) (hrank : population c (j + 1) = e) :
    starStride c e k = 10 ^ j := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hj : j = k
    · subst j
      rw [starStride]
      have hr : population c k + 1 = e := by simpa [population_succ, hd] using hrank
      simp [hd, hr]
    · have hjk' : j < k := by omega
      have hmono : e ≤ population c k := by
        rw [← hrank]
        exact Nat.count_monotone _ (by omega)
      rw [starStride, ite_eq_right (by omega : ¬(digitAt c k = 9 ∧ population c k + 1 = e))]
      exact ih hjk'

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
