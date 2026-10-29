/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.BerlekampWelch
import Complexity.Foundations.Data.Code.Hadamard
import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Foundations.Data.Code.ReedMuller
import Complexity.Foundations.Data.Code.Singleton
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: algebraic codes

The minimum distance of the binary repetition code and of codes with at most one word; the
Singleton and Hamming bounds on the repetition code, which meets both; the Gilbert–Varshamov
bound; the minimum distance of a Hadamard code; the Singleton bound on a Reed–Solomon code, which
meets it; the distance and
dimension of a Reed–Solomon code over `ZMod 5`, the zero code of dimension zero, and unique
decoding below half its distance; the distance of a Reed–Muller code over `ZMod 3`; and a
complete Berlekamp–Welch decoding over `ZMod 7` with two errors, the largest number it corrects
at that length and dimension.
-/

namespace ComplexityTests.Code

open Cslib Cslib.Code Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-! ### Minimum distance -/

/-- The binary repetition code of length three. -/
private def repetition : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

private theorem minDist_repetition : minDist (repetition : Set (Fin 3 → Bool)) = 3 := by
  refine le_antisymm ((minDist_le_hammingDist (x := fun _ => false) (y := fun _ => true)
    (by simp [repetition]) (by simp [repetition]) (by decide)).trans_eq ?_) ?_
  · rw [show hammingDist (fun _ : Fin 3 => false) (fun _ => true) = 3 by decide]
    rfl
  · rw [le_minDist_iff]
    rintro x hx y hy hxy
    simp only [repetition, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact absurd rfl hxy | (rw [show hammingDist _ _ = 3 by decide]; rfl)

/-- Minimum distance of empty/singleton sets, Singleton and Hamming bounds on the repetition code,
the Gilbert–Varshamov bound, and the minimum distance of the Hadamard code. -/
example :
    minDist (∅ : Set (Fin 3 → Bool)) = ⊤ ∧
    minDist ({fun _ => true} : Set (Fin 3 → Bool)) = ⊤ ∧
    -- Singleton is tight: two repetition words equal 2^(3 - 3 + 1).
    repetition.card ≤ 2 ^ (3 - 3 + 1) ∧
    -- Hamming is tight: two radius-one balls, each with four words, fill all eight words.
    repetition.card * ∑ j ∈ Finset.range 2, (3).choose j * (2 - 1) ^ j ≤ 2 ^ 3 ∧
    -- Gilbert–Varshamov gives at least 8 / 4 words at length three and distance two.
    (∃ C : Finset (Fin 3 → Bool), (2 : ℕ∞) ≤ minDist (C : Set (Fin 3 → Bool)) ∧
      2 ^ 3 ≤ C.card * ∑ j ∈ Finset.range 2, (3).choose j * (2 - 1) ^ j) ∧
    minDist (Set.range (BitString.hadamardCode (ι := Fin 3))) = 4 :=
  ⟨minDist_empty,
    minDist_singleton _,
    by simpa using card_le_pow_of_le_minDist (d := 3) minDist_repetition.ge,
    by
      simpa using card_mul_sum_choose_le_of_two_mul_lt_minDist (β := fun _ : Fin 3 => Bool) (q := 2)
        (fun _ => rfl) (r := 1) (by rw [minDist_repetition]; decide),
    by
      simpa using exists_le_minDist_and_pow_le_card_mul_sum_choose (β := fun _ : Fin 3 => Bool)
        (q := 2) (fun _ => rfl) (d := 2) (by norm_num),
    by simpa using BitString.minDist_range_hadamardCode (ι := Fin 3)⟩

/-! ### Reed–Solomon codes over `ZMod 5` -/

/-- The five points of `ZMod 5`. -/
private def points5 : Fin 5 → ZMod 5 := fun i => (i : ℕ)

private theorem points5_injective : Function.Injective points5 := by decide

private theorem minDist_rs : minDist (reedSolomon points5 2 : Set (Fin 5 → ZMod 5)) = 4 :=
  minDist_reedSolomon points5_injective (by norm_num) (by simp)

private theorem finrank_rs : Module.finrank (ZMod 5) (reedSolomon points5 2) = 2 :=
  finrank_reedSolomon points5_injective (by simp)

/-- The Reed–Solomon code is not the zero code: it contains the constant word `1`. -/
private theorem rs_ne_bot : reedSolomon points5 2 ≠ ⊥ := by
  intro h
  have h1 : (fun i => (1 : (ZMod 5)[X]).eval (points5 i)) ∈ reedSolomon points5 2 :=
    eval_mem_reedSolomon points5 (by rw [degree_one]; exact_mod_cast (by norm_num : 0 < 2))
  rw [h, Submodule.mem_bot] at h1
  exact absurd (congrFun h1 0) (by simp)

/-- **Reed–Solomon codes are maximum distance separable**: the Singleton bound holds with
equality, dimension zero is the zero code with `minDist = ⊤`, and unique decoding holds below half
the distance. -/
example {x y w : Fin 5 → ZMod 5} (hx : x ∈ reedSolomon points5 2) (hy : y ∈ reedSolomon points5 2)
    (hxw : hammingDist x w ≤ 1) (hyw : hammingDist y w ≤ 1) :
    Module.finrank (ZMod 5) (reedSolomon points5 2) + 4 = Fintype.card (Fin 5) + 1 ∧
    Module.finrank (ZMod 5) (reedSolomon points5 2) + 4 ≤ Fintype.card (Fin 5) + 1 ∧
    minDist (reedSolomon points5 0 : Set (Fin 5 → ZMod 5)) = ⊤ ∧
    x = y := by
  refine ⟨by rw [finrank_rs]; simp,
    finrank_add_le_card_add_one rs_ne_bot minDist_rs.ge,
    ?_,
    eq_of_hammingDist_le_of_two_mul_lt_minDist (by rw [minDist_rs]; decide) hx hy hxw hyw⟩
  refine minDist_eq_top_iff.2 fun u hu v hv => ?_
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hu
  obtain ⟨q, hq, rfl⟩ := mem_reedSolomon.1 hv
  rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hp hq
  rw [hp, hq]

/-! ### Reed–Muller codes over `ZMod 3` -/

/-- Minimum distance `(3 - 1) * 3 = 6` of the degree-1 Reed–Muller code in two variables over
`ZMod 3`, and distance `≥ 9` between distinct codewords of degree two in three variables. -/
example {f g : (Fin 3 → ZMod 3) → ZMod 3} (hf : f ∈ reedMuller (ZMod 3) 3 2)
    (hg : g ∈ reedMuller (ZMod 3) 3 2) (hfg : f ≠ g) :
    minDist (reedMuller (ZMod 3) 2 1 : Set ((Fin 2 → ZMod 3) → ZMod 3)) = 6 ∧
    9 ≤ hammingDist f g := by
  refine ⟨?_, ?_⟩
  · have := minDist_reedMuller (F := ZMod 3) (m := 1) (d := 1) (by simp [ZMod.card])
    simpa [ZMod.card] using this
  · have := card_sub_mul_pow_le_mul_hammingDist_of_mem_reedMuller hf hg hfg
    simp only [ZMod.card] at this
    omega

/-! ### Berlekamp–Welch decoding over `ZMod 7` -/

/-- The seven points of `ZMod 7`. -/
private def points7 : Fin 7 → ZMod 7 := fun i => (i : ℕ)

private theorem points7_injective : Function.Injective points7 := by decide

/-- The values `1, 2, 5, 3, 3, 5, 2` of `X ^ 2 + 1` at the points, with errors at the points `2`
and `6`. -/
private def received : Fin 7 → ZMod 7 := ![1, 2, 0, 3, 3, 5, 4]

private theorem hammingDist_received :
    hammingDist (fun i => (X ^ 2 + 1 : (ZMod 7)[X]).eval (points7 i)) received ≤ 2 := by
  have : (fun i => (X ^ 2 + 1 : (ZMod 7)[X]).eval (points7 i)) = fun i => points7 i ^ 2 + 1 := by
    funext i
    simp
  rw [this]
  decide

private theorem degree_lt : (X ^ 2 + 1 : (ZMod 7)[X]).degree < (3 : ℕ) := by
  compute_degree!

/-- Existence of a key-equation solution and unique Berlekamp–Welch recovery of `X ^ 2 + 1` from two
errors among seven points at dimension three. -/
example :
    (∃ E Q, BerlekampWelch.IsSolution points7 received 2 3 E Q) ∧
    berlekampWelch points7 2 3 received = some (X ^ 2 + 1) :=
  ⟨BerlekampWelch.exists_isSolution degree_lt hammingDist_received,
    berlekampWelch_eq_some points7_injective (by simp) degree_lt hammingDist_received⟩

end ComplexityTests.Code
