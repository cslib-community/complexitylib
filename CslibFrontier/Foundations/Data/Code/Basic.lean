/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ENat.Lattice
public import Mathlib.InformationTheory.Hamming
import Mathlib.Order.SuccPred.ENat

/-!
# The minimum distance of a code

A *code* is a set `C` of words `∀ i, β i` over the alphabets `β i` at the finitely many
coordinates `i : ι`. Its *minimum distance* `Cslib.Code.minDist C` is the least Hamming distance
between two distinct codewords, and `⊤` when `C` has at most one codeword
[MacWilliams and Sloane, Chapter 1][MacWilliamsSloane1977]. A bound `d ≤ minDist C` says exactly
that distinct codewords differ on at least `d` coordinates (`Cslib.Code.le_minDist_iff`). When `C`
has two distinct codewords the minimum is attained (`Cslib.Code.exists_hammingDist_eq_minDist`).

A word within distance `e` of two codewords determines them when `2 e < minDist C`: the code
*uniquely decodes* up to `e` errors (`Cslib.Code.eq_of_hammingDist_le_of_two_mul_lt_minDist`).

## Main definitions

* `Cslib.Code.minDist`: the minimum distance of a code.

## Main results

* `Cslib.Code.le_minDist_iff`, `Cslib.Code.natCast_lt_minDist_iff`: lower bounds on the minimum
  distance.
* `Cslib.Code.minDist_eq_top_iff`: the minimum distance is `⊤` exactly for codes with at most one
  word.
* `Cslib.Code.exists_hammingDist_eq_minDist`: the minimum distance is attained.
* `Cslib.Code.eq_of_hammingDist_le_of_two_mul_lt_minDist`: unique decoding below half the minimum
  distance.

## References

* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.Code

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, DecidableEq (β i)]

/-- The *minimum distance* of a code `C`: the least Hamming distance between two distinct
codewords, or `⊤` when `C` has at most one codeword. -/
noncomputable def minDist (C : Set (∀ i, β i)) : ℕ∞ :=
  ⨅ x ∈ C, ⨅ y ∈ C, ⨅ _ : x ≠ y, (hammingDist x y : ℕ∞)

variable {C D : Set (∀ i, β i)} {x y : ∀ i, β i} {d : ℕ∞}

/-- The minimum distance is at least `d` iff distinct codewords differ on at least `d`
coordinates. -/
theorem le_minDist_iff : d ≤ minDist C ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hammingDist x y := by
  simp only [minDist, le_iInf_iff]

/-- The minimum distance exceeds `r` iff distinct codewords differ on more than `r`
coordinates. -/
theorem natCast_lt_minDist_iff {r : ℕ} :
    (r : ℕ∞) < minDist C ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → r < hammingDist x y := by
  rw [← ENat.natCast_add_one_le_iff, le_minDist_iff]
  simp only [ENat.natCast_add_one_le_iff, Nat.cast_lt]

/-- Distinct codewords are separated by at least the minimum distance of the code. -/
theorem minDist_le_hammingDist (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    minDist C ≤ hammingDist x y :=
  le_minDist_iff.1 le_rfl x hx y hy hxy

/-- A subcode has at least the minimum distance of the code. -/
theorem minDist_anti (h : C ⊆ D) : minDist D ≤ minDist C :=
  le_minDist_iff.2 fun _ hx _ hy hxy => minDist_le_hammingDist (h hx) (h hy) hxy

/-- The minimum distance is `⊤` exactly for codes with at most one codeword. -/
theorem minDist_eq_top_iff : minDist C = ⊤ ↔ C.Subsingleton := by
  rw [← top_le_iff, le_minDist_iff]
  refine ⟨fun h x hx y hy => ?_, fun h x hx y hy hxy => absurd (h hx hy) hxy⟩
  by_contra hxy
  exact ENat.natCast_ne_top _ (top_le_iff.1 (h x hx y hy hxy))

/-- The empty code has minimum distance `⊤`. -/
@[simp]
theorem minDist_empty : minDist (∅ : Set (∀ i, β i)) = ⊤ :=
  minDist_eq_top_iff.2 Set.subsingleton_empty

/-- A singleton code has minimum distance `⊤`. -/
@[simp]
theorem minDist_singleton (x : ∀ i, β i) : minDist {x} = ⊤ :=
  minDist_eq_top_iff.2 Set.subsingleton_singleton

/-- A code with two distinct codewords has two codewords at exactly the minimum distance. -/
theorem exists_hammingDist_eq_minDist (h : C.Nontrivial) :
    ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ (hammingDist x y : ℕ∞) = minDist C := by
  let S : Set ℕ := {n | ∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hammingDist x y = n}
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  have hS : S.Nonempty := ⟨_, x, hx, y, hy, hxy, rfl⟩
  obtain ⟨x, hx, y, hy, hxy, hmin⟩ := Nat.sInf_mem hS
  refine ⟨x, hx, y, hy, hxy, le_antisymm ?_ (minDist_le_hammingDist hx hy hxy)⟩
  refine le_minDist_iff.2 fun x' hx' y' hy' hxy' => ?_
  rw [hmin]
  exact Nat.cast_le.2 (Nat.sInf_le ⟨x', hx', y', hy', hxy', rfl⟩)

/-- A code with two distinct codewords has minimum distance at most the number of
coordinates. -/
theorem minDist_le_card (h : C.Nontrivial) : minDist C ≤ Fintype.card ι := by
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact (minDist_le_hammingDist hx hy hxy).trans (Nat.cast_le.2 (hammingDist_le_card_fintype))

/-- **Unique decoding.** If `2 e` is less than the minimum distance, a word is within distance `e`
of at most one codeword. -/
theorem eq_of_hammingDist_le_of_two_mul_lt_minDist {e : ℕ} (he : 2 * (e : ℕ∞) < minDist C)
    {w : ∀ i, β i} (hx : x ∈ C) (hy : y ∈ C) (hxw : hammingDist x w ≤ e)
    (hyw : hammingDist y w ≤ e) : x = y := by
  by_contra hxy
  have hle : hammingDist x y ≤ 2 * e := by
    have := hammingDist_triangle x w y
    rw [hammingDist_comm w y] at this
    omega
  have := (minDist_le_hammingDist hx hy hxy).trans (Nat.cast_le.2 hle)
  push_cast at this
  exact absurd he (not_lt.2 this)

end Cslib.Code
