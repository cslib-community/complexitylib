/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.Hadamard
import Complexity.Foundations.Data.Code.Plotkin
import Complexity.Foundations.Data.Code.Plotkin.Asymptotic
import Mathlib.Data.ZMod.Defs

/-!
# Tests: the Plotkin bound

Codes that attain the Plotkin bound with equality:

* the Hadamard code of `k ≥ 1` bit messages, whose `2 ^ k` codewords all vanish at the zero input
  and so agree outside the other `2 ^ k - 1` coordinates (the simplex code), at distance
  `2 ^ (k - 1)`: the bound `q d / (q d - (q - 1) (2 ^ k - 1))` is `2 ^ k`;
* the binary repetition code of length three: at `d = n = 3` the bound is `6 / 3 = 2`;
* the ternary code `{(a, b, a + b)}` of length three and distance two, at relative distance
  `1 - 1 / q`: the bound `q n` is `9`;
* the binary even-weight code of length four and distance two: the bound `2 n` is `8`.

The asymptotic Plotkin bound applies to the binary repetition codes, of relative distance one: at
`δ = 1 / 2` it bounds their rate by `o(1)`.
-/

namespace ComplexityTests.Code.Plotkin

open Cslib Cslib.Code Cslib.BitString Finset

/-! ### The Hadamard (simplex) code -/

section Hadamard

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
/-- Every Hadamard codeword vanishes at the zero input. -/
private theorem hadamardCode_zero (x : ι → Bool) : hadamardCode x 0 = false := by
  rw [hadamardCode_apply, dotProduct_zero]
  rfl

/-- **The simplex code meets the Plotkin bound.** The `2 ^ k` codewords of the Hadamard code of
`k ≥ 1` bit messages agree outside the `2 ^ k - 1` nonzero inputs, and the Plotkin bound for such
codes, at distance `2 ^ (k - 1)`, is exactly their number `2 ^ k`. -/
example :
    #(univ.image (hadamardCode (ι := ι))) *
        (Fintype.card Bool * 2 ^ (Fintype.card ι - 1) -
          (Fintype.card Bool - 1) * #((univ : Finset (ι → Bool)).erase 0)) =
      Fintype.card Bool * 2 ^ (Fintype.card ι - 1) := by
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  have hcard : #(univ.image (hadamardCode (ι := ι))) = 2 ^ Fintype.card ι := by
    rw [card_image_of_injective _ hadamardCode_injective, card_univ, Fintype.card_fun,
      Fintype.card_bool]
  have hT : #((univ : Finset (ι → Bool)).erase 0) = 2 ^ Fintype.card ι - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun, Fintype.card_bool]
  have h2 : 2 * 2 ^ (Fintype.card ι - 1) = 2 ^ Fintype.card ι := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  have hpos : 1 ≤ 2 ^ Fintype.card ι := Nat.one_le_two_pow
  have h1 : 2 ^ Fintype.card ι - (2 - 1) * (2 ^ Fintype.card ι - 1) = 1 := by omega
  rw [hcard, hT, Fintype.card_bool, h2, h1, mul_one]

/-- The Plotkin bound applies to the simplex code, and by the computation above it is attained. -/
example :
    #(univ.image (hadamardCode (ι := ι))) *
        (Fintype.card Bool * 2 ^ (Fintype.card ι - 1) -
          (Fintype.card Bool - 1) * #((univ : Finset (ι → Bool)).erase 0)) ≤
      Fintype.card Bool * 2 ^ (Fintype.card ι - 1) := by
  refine card_mul_sub_le_of_le_minDist_of_forall_notMem_eq ?_ ?_
  · rw [coe_image, coe_univ, Set.image_univ, minDist_range_hadamardCode]
  · intro x hx y hy i hi
    obtain ⟨a, -, rfl⟩ := mem_image.1 hx
    obtain ⟨b, -, rfl⟩ := mem_image.1 hy
    have hi0 : i = 0 := by
      by_contra h
      exact hi (mem_erase.2 ⟨h, mem_univ _⟩)
    rw [hi0, hadamardCode_zero, hadamardCode_zero]

end Hadamard

/-! ### The repetition code at `d = n` -/

/-- The binary repetition code of length three. -/
private def repetition3 : Finset (Fin 3 → Bool) := {fun _ => false, fun _ => true}

private theorem le_minDist_repetition3 :
    ((3 : ℕ) : ℕ∞) ≤ minDist (repetition3 : Set (Fin 3 → Bool)) := by
  rw [le_minDist_iff]
  intro x hx y hy hxy
  have h : ∀ x ∈ repetition3, ∀ y ∈ repetition3, x ≠ y → 3 ≤ hammingDist x y := by decide
  exact_mod_cast h x hx y hy hxy

/-- At `d = n = 3` the Plotkin bound `q d / (q d - (q - 1) n)` is `2`, the size of the repetition
code. -/
example : #repetition3 ≤ 2 := by
  have h := card_le_div_of_le_minDist le_minDist_repetition3 (by decide)
  simpa using h

example : #repetition3 = 2 := by decide

/-! ### A ternary code at relative distance `1 - 1 / q` -/

/-- The ternary code `{(a, b, a + b)}` of length three: nine codewords at distance two. -/
private def ternary : Finset (Fin 3 → ZMod 3) :=
  univ.image fun p : ZMod 3 × ZMod 3 => ![p.1, p.2, p.1 + p.2]

private theorem le_minDist_ternary :
    ((2 : ℕ) : ℕ∞) ≤ minDist (ternary : Set (Fin 3 → ZMod 3)) := by
  rw [le_minDist_iff]
  intro x hx y hy hxy
  have h : ∀ x ∈ ternary, ∀ y ∈ ternary, x ≠ y → 2 ≤ hammingDist x y := by decide
  exact_mod_cast h x hx y hy hxy

/-- With `q = 3`, `n = 3` and `d = 2`, `q d = (q - 1) n`, and the Plotkin bound `q n = 9` is the
size of the code. -/
example : #ternary ≤ 9 := by
  have h := card_le_mul_of_le_minDist_of_mul_eq le_minDist_ternary (by decide) (by decide)
  simpa using h

example : #ternary = 9 := by decide

/-! ### The binary even-weight code of length `2 d` -/

/-- The binary words of length four with an even number of ones: eight codewords at distance
two. -/
private def evenWeight : Finset (Fin 4 → Bool) := {x | Even #{i | x i = true}}

private theorem le_minDist_evenWeight :
    ((2 : ℕ) : ℕ∞) ≤ minDist (evenWeight : Set (Fin 4 → Bool)) := by
  rw [le_minDist_iff]
  intro x hx y hy hxy
  have h : ∀ x ∈ evenWeight, ∀ y ∈ evenWeight, x ≠ y → 2 ≤ hammingDist x y := by decide
  exact_mod_cast h x hx y hy hxy

/-- A binary code of length `4 = 2 d` has at most `2 n = 8` codewords, as many as the even-weight
code. -/
example : #evenWeight ≤ 8 := by
  have h := card_le_two_mul_of_le_minDist_of_card_eq le_minDist_evenWeight (by decide)
    (by decide)
  simpa using h

example : #evenWeight = 8 := by decide

/-! ### The Plotkin bound below relative distance `1 - 1 / q` -/

/-- Shortening: a binary code of length ten and distance four, shortened to its last
`m = 7` coordinates (where `q d - (q - 1) m = 1`), has at most `2 ^ 3 * 8 = 64` codewords. -/
example (C : Finset (Fin 10 → Bool)) (hC : ((4 : ℕ) : ℕ∞) ≤ minDist (C : Set (Fin 10 → Bool))) :
    #C ≤ 64 := by
  have h := card_mul_sub_le_pow_mul_of_le_minDist hC (m := 7) (by decide)
  simpa using h

/-! ### The asymptotic Plotkin bound -/

/-- The binary repetition code of length `n + 1`. -/
private def repetition (n : ℕ) : Finset (Fin (n + 1) → Bool) := {fun _ => false, fun _ => true}

private theorem hammingDist_repetition (n : ℕ) :
    ∀ x ∈ repetition n, ∀ y ∈ repetition n, x ≠ y → hammingDist x y = n + 1 := by
  intro x hx y hy hxy
  simp only [repetition, mem_insert, mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact absurd rfl hxy
  · simp [hammingDist]
  · simp [hammingDist]
  · exact absurd rfl hxy

/-- The repetition codes have relative distance `1 ≥ δ = 1 / 2 = 1 - 1 / q`, so the asymptotic
Plotkin bound gives `log_2 |C| ≤ ε n` eventually, for every `ε > 0`. -/
example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop, Real.logb (Fintype.card Bool) #(repetition n) ≤
      (1 - Fintype.card Bool / (Fintype.card Bool - 1) * (1 / 2) + ε) *
        Fintype.card (Fin (n + 1)) :=
  eventually_logb_card_le_of_le_hammingDist (ιs := fun n => Fin (n + 1)) (by norm_num)
    (by norm_num)
    (fun n x hx y hy hxy => by
      rw [hammingDist_repetition n x hx y hy hxy, Fintype.card_fin]
      push_cast
      linarith)
    (by simpa using Filter.tendsto_add_atTop_nat 1) hε

end ComplexityTests.Code.Plotkin
