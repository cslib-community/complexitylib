/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Code.Johnson
import CslibFrontier.Foundations.Data.Code.ReedSolomon
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree

/-!
# Tests: the Johnson bound

The Reed–Solomon code of dimension two over `ZMod 5`, of length five and minimum distance four,
uniquely decodes one error. The Johnson bound applies at radius two, beyond half the minimum
distance: a Hamming ball of radius two contains at most ten codewords, and listing them list
decodes the code up to radius `2 / 5`. The q-ary Johnson bound, which uses the alphabet size five,
reaches radius three, where the alphabet-free bound says nothing: a Hamming ball of radius three
contains at most sixteen codewords.
-/

namespace CslibFrontierTests.Code.Johnson

open Cslib Cslib.Code Finset Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The five points of `ZMod 5`. -/
private def points5 : Fin 5 → ZMod 5 := fun i => (i : ℕ)

private theorem minDist_rs : minDist (reedSolomon points5 2 : Set (Fin 5 → ZMod 5)) = 4 :=
  minDist_reedSolomon (by decide) (by norm_num) (by simp)

open Classical in
/-- The Reed–Solomon codewords within distance two of any word: at most ten, since
`5 * (5 - 4) < (5 - 2) ^ 2`. -/
example (w : Fin 5 → ZMod 5) :
    #{c : Fin 5 → ZMod 5 | c ∈ reedSolomon points5 2 ∧ hammingDist c w ≤ 2} ≤ 10 := by
  have h := card_filter_hammingDist_le_le (C := {c | c ∈ reedSolomon points5 2}) (d := 4)
    (e := 2) (by simpa using minDist_rs.ge) (by decide) w
  rw [Finset.filter_filter] at h
  simpa using h

/-- Messages `m` are encoded by the values of the polynomial `m 0 + m 1 * X`. -/
private def rsEncode (m : Fin 2 → ZMod 5) : Fin 5 → ZMod 5 := fun i => m 0 + m 1 * points5 i

private theorem rsEncode_injective : Function.Injective rsEncode := by
  intro m m' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [rsEncode, points5, Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero,
    add_zero, mul_one] at h0 h1
  funext j
  fin_cases j
  · exact h0
  · exact add_left_cancel (h0 ▸ h1 : m' 0 + m 1 = m' 0 + m' 1)

private theorem range_rsEncode_subset :
    Set.range rsEncode ⊆ (reedSolomon points5 2 : Set (Fin 5 → ZMod 5)) := by
  rintro _ ⟨m, rfl⟩
  refine mem_reedSolomon.2 ⟨C (m 0) + C (m 1) * X, by compute_degree!, ?_⟩
  funext i
  simp [rsEncode]

/-- **List decoding beyond half the minimum distance.** Some decoder with lists of ten messages
list decodes the Reed–Solomon code up to radius `2 / 5`. -/
example : ∃ C : ListCode (Fin 2 → ZMod 5) (Fin 5) (ZMod 5) 10,
    C.encode = rsEncode ∧ C.ListDecodes (2 / 5) := by
  have h := exists_listCode_listDecodes rsEncode_injective (d := 4) (e := 2)
    (minDist_rs.ge.trans (minDist_anti range_rsEncode_subset)) (by decide)
  simp only [Fintype.card_fin] at h
  norm_num at h
  exact h

/-- The alphabet-free Johnson bound does not apply at radius three: `5 * (5 - 4) < (5 - 3) ^ 2`
fails. -/
example : ¬ 5 * (5 - 4) < (5 - 3) ^ 2 := by decide

open Classical in
/-- **The q-ary Johnson bound at radius three.** With `q = 5`, `n = 5`, `d = 4` and `e = 3`, the
radius satisfies `q e ≤ (q - 1) n`, and the bound reads
`M (4 * 2 ^ 2 + 3 ^ 2 - 4 * 5 * 1) ≤ 4 * 5 * 4`, so a Hamming ball of radius three contains at most
sixteen Reed–Solomon codewords. -/
example (w : Fin 5 → ZMod 5) :
    #{c : Fin 5 → ZMod 5 | c ∈ reedSolomon points5 2 ∧ hammingDist c w ≤ 3} ≤ 16 := by
  have h := card_filter_hammingDist_le_mul_le_of_mul_le
    (C := {c | c ∈ reedSolomon points5 2}) (d := 4) (by simpa using minDist_rs.ge) w (e := 3)
    (by simp)
  rw [Finset.filter_filter] at h
  simp only [ZMod.card, Fintype.card_fin] at h
  omega

end CslibFrontierTests.Code.Johnson
