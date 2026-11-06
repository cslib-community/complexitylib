/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Digits
import Complexity.Foundations.Data.Nat.Radix

/-!
# Raw cube digits for native box-table lookup

Terms use the existing encoder's ten digits; a star uses eleven-symbol digit ten.
`lookupCompletion` is the prefix value actually accumulated by the native lookup,
replacing stars by P0 digit nine. The full readback and order lemmas use the existing
cube and box notions, without introducing another membership or ordering predicate.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Finset Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- A raw cube digit uses ten for a star and the existing native digit for a term. -/
@[expose] def cubeDigit {L : ℕ} (π : Cube L) (k : Fin L) : ℕ :=
  match π k with
  | .star => 10
  | .term lam => (Encoding.termDigits.symm lam).val

/-- Extend the real cube digits by zero outside its finite input span. -/
@[expose] def rawCubeDigit {L : ℕ} (π : Cube L) (k : ℕ) : ℕ :=
  if h : k < L then cubeDigit π ⟨k, h⟩ else 0

/-- The completion code accumulated in the first `k` native lookup iterations. -/
@[expose] def lookupCompletion (raw : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lookupCompletion raw k + (if raw k = 10 then 9 else raw k) * 10 ^ k

/-- Every actual cube symbol fits the eleven-symbol input alphabet. -/
theorem cubeDigit_le_ten {L : ℕ} (π : Cube L) (k : Fin L) : cubeDigit π k ≤ 10 := by
  cases h : π k with
  | star => simp [cubeDigit, h]
  | term lam => simpa only [cubeDigit, h] using (Encoding.termDigits.symm lam).isLt.le

@[simp] theorem rawCubeDigit_fin {L : ℕ} (π : Cube L) (k : Fin L) :
    rawCubeDigit π k.val = cubeDigit π k := by simp [rawCubeDigit, k.isLt]

/-- The zero extension obeys the same digit bound at every natural index. -/
theorem rawCubeDigit_le_ten {L : ℕ} (π : Cube L) (k : ℕ) : rawCubeDigit π k ≤ 10 := by
  by_cases h : k < L
  · simpa only [rawCubeDigit, dite_eq_left h] using cubeDigit_le_ten π ⟨k, h⟩
  · simp [rawCubeDigit, h]

/-- Ten denotes precisely a star. -/
@[simp] theorem cubeDigit_eq_ten_iff {L : ℕ} (π : Cube L) (k : Fin L) :
    cubeDigit π k = 10 ↔ π k = .star := by
  cases h : π k with
  | star => simp [cubeDigit, h]
  | term lam =>
    have hlt := (Encoding.termDigits.symm lam).isLt
    simp [cubeDigit, h, Nat.ne_of_lt hlt]

/-- Nine denotes precisely a fixed P0 term. -/
@[simp] theorem cubeDigit_eq_nine_iff {L : ℕ} (π : Cube L) (k : Fin L) :
    cubeDigit π k = 9 ↔ π k = .term .P0 := by
  cases h : π k with
  | star => simp [cubeDigit, h]
  | term lam =>
    have he : (Encoding.termDigits.symm lam).val = 9 ↔ lam = .P0 := by
      constructor
      · intro hh
        have hf : Encoding.termDigits.symm lam = 9 := Fin.ext hh
        calc
          lam = Encoding.termDigits (Encoding.termDigits.symm lam) :=
            (Encoding.termDigits.apply_symm_apply lam).symm
          _ = Encoding.termDigits 9 := congrArg Encoding.termDigits hf
          _ = .P0 := by decide
      · intro hh
        simp [hh, Encoding.termDigits]
    simpa [cubeDigit, h] using he

/-- Native prefix completion is the ordinary little-endian weighted digit sum. -/
theorem lookupCompletion_eq_sum (raw : ℕ → ℕ) (k : ℕ) :
    lookupCompletion raw k =
      ∑ i ∈ range k, (if raw i = 10 then 9 else raw i) * 10 ^ i := by
  induction k with
  | zero => simp [lookupCompletion]
  | succ k ih => rw [lookupCompletion, sum_range_succ, ih]

/-- Every completed prefix is a genuine decimal code, including empty input. -/
theorem lookupCompletion_lt {raw : ℕ → ℕ} {k : ℕ} (hraw : ∀ i < k, raw i ≤ 10) :
    lookupCompletion raw k < 10 ^ k := by
  induction k with
  | zero => simp [lookupCompletion]
  | succ k ih =>
    have hk := ih (fun i hi => hraw i (by omega))
    have hd : (if raw k = 10 then 9 else raw k) ≤ 9 := by
      split <;> have h := hraw k (by omega) <;> omega
    calc
      lookupCompletion raw (k + 1) <
          10 ^ k + (if raw k = 10 then 9 else raw k) * 10 ^ k :=
        Nat.add_lt_add_right hk _
      _ ≤ 10 ^ k + 9 * 10 ^ k := Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _
      _ = 10 ^ (k + 1) := by rw [pow_succ]; omega

/-- Actual completion of all input digits is exactly the encoder's existing leaf index. -/
theorem lookupCompletion_rawCubeDigit {L : ℕ} (π : Cube L) :
    lookupCompletion (rawCubeDigit π) L = (Encoding.leafIndex π.starsToP0).val := by
  rw [lookupCompletion_eq_sum, ← Fin.sum_univ_eq_sum_range, Encoding.leafIndex,
    finFunctionFinEquiv_apply]
  apply sum_congr rfl
  intro k _
  rw [rawCubeDigit_fin]
  cases h : π k with
  | star => simp [cubeDigit, Cube.starsToP0, h, Encoding.termDigits]
  | term lam =>
    have hn : (Encoding.termDigits.symm lam).val ≠ 10 :=
      Nat.ne_of_lt (Encoding.termDigits.symm lam).isLt
    simp [cubeDigit, Cube.starsToP0, h, hn]

private theorem count_rawCubeDigit {L : ℕ} (π : Cube L) (p : ℕ → Prop) [DecidablePred p] :
    Nat.count (fun i => p (rawCubeDigit π i)) L =
      (univ.filter fun k : Fin L => p (cubeDigit π k)).card := by
  rw [Nat.count_eq_card_filter_range]
  symm
  refine card_bij (fun k _ => k.val) ?_ ?_ ?_
  · intro k hk
    exact mem_filter.mpr ⟨mem_range.mpr k.isLt, by
      simpa only [rawCubeDigit_fin] using (mem_filter.mp hk).2⟩
  · intro k _ k' _ hh
    exact Fin.ext hh
  · intro i hi
    obtain ⟨hiL, hp⟩ := mem_filter.mp hi
    refine ⟨⟨i, mem_range.mp hiL⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    simpa only [rawCubeDigit, dite_eq_left (mem_range.mp hiL)] using hp

/-- The native star counter reads the actual finite cube's star count. -/
theorem count_rawCubeDigit_stars {L : ℕ} (π : Cube L) :
    Nat.count (fun i => rawCubeDigit π i = 10) L = π.starLevels.card := by
  rw [count_rawCubeDigit π (fun d => d = 10)]
  congr 1
  ext k
  simp

/-- The native population counter reads fixed P0 terms plus stars completed with P0. -/
theorem count_rawCubeDigit_population {L : ℕ} (π : Cube L) :
    Nat.count (fun i => rawCubeDigit π i = 9 ∨ rawCubeDigit π i = 10) L =
      π.starLevels.card + π.P0Levels.card := by
  rw [count_rawCubeDigit π (fun d => d = 9 ∨ d = 10)]
  have hf : (univ.filter fun k : Fin L => cubeDigit π k = 9 ∨ cubeDigit π k = 10) =
      π.starLevels ∪ π.P0Levels := by
    ext k
    simp [or_comm]
  rw [hf, card_union_of_disjoint π.disjoint_starLevels_P0Levels]

/-- Completing stars preserves the population counted by the native lookup scan. -/
theorem population_lookupCompletion {L : ℕ} (π : Cube L) :
    population (lookupCompletion (rawCubeDigit π) L) L =
      π.starLevels.card + π.P0Levels.card := by
  rw [lookupCompletion_rawCubeDigit]
  simpa only [leafAt_leafIndex, card_P0Levels_starsToP0] using
    population_eq_card_P0Levels (Encoding.leafIndex π.starsToP0)

/-- A canonical box never has a fixed P0 before a later starred coordinate. -/
theorem no_fixed_before_star {L m t : ℕ} {π : Cube L} (hπ : IsBox m t π)
    (k : Fin L) (hk : π k = .star) :
    ¬ ∃ i : Fin L, i < k ∧ cubeDigit π i = 9 := by
  rintro ⟨i, hik, hi⟩
  have hki := hπ.2 k (Cube.mem_starLevels.mpr hk) i
    (Cube.mem_P0Levels.mpr ((cubeDigit_eq_nine_iff π i).mp hi))
  exact lt_asymm hik hki

/-- Natural-index form of the order invariant consumed by the native lookup scan. -/
theorem rawCubeDigit_no_fixed_before_star {L m t : ℕ} {π : Cube L} (hπ : IsBox m t π)
    {k : ℕ} (hk : k < L) (hs : rawCubeDigit π k = 10) :
    ¬ ∃ i < k, rawCubeDigit π i = 9 := by
  rintro ⟨i, hik, hi⟩
  have hiL : i < L := hik.trans hk
  apply no_fixed_before_star hπ ⟨k, hk⟩
    ((cubeDigit_eq_ten_iff π _).mp (by simpa only [rawCubeDigit, dite_eq_left hk] using hs))
  exact ⟨⟨i, hiL⟩, hik, by simpa only [rawCubeDigit, dite_eq_left hiL] using hi⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
