/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Code.FlipDecoding

/-!
# Tests: expander codes on the Fano plane

The incidence graph of the Fano plane, points `Fin 7` against lines `Fin 7` with point `i` on line
`j` iff `i - j ∈ {0, 1, 3}` (a perfect difference set mod `7`), is `(3, 3)`-biregular. Two points
share exactly one line, so every pair of points has `5` neighbouring lines: the graph expands sets
of at most `2` points by `α = 5 / 2 > (3 / 4) · 3`. The expansion fails for the three points of a
line, which have only `7 < 7.5` neighbours.

The expander code is the `[7, 3, 4]` simplex code (the complements of the lines and `0`). The
distance bound `2 α k ≤ c · d` gives `d ≥ 10 / 3`, i.e. `d ≥ 4`, which is tight, and the flip
decoder corrects one error, by computation and by the general theorem. Two errors can be
ambiguous: a word at distance `2` from two codewords.
-/

namespace ComplexityTests.ExpanderCode

open Finset Cslib Cslib.Bipartite Cslib.BitString Cslib.BitString.ExpanderCode

/-- Point `i` lies on line `j` iff `i - j ∈ {0, 1, 3}`. -/
def fano (i j : Fin 7) : Prop := i - j = 0 ∨ i - j = 1 ∨ i - j = 3

instance (i j : Fin 7) : Decidable (fano i j) := inferInstanceAs (Decidable (_ ∨ _))

/-! ### The expansion hypothesis -/

theorem fano_isBiregular : IsBiregular fano 3 3 := by
  unfold IsBiregular; decide

theorem fano_isLeftBounded : IsLeftBounded fano 3 := fano_isBiregular.isLeftBounded

/-- Sets of at most two points have at least `5 / 2` neighbours per point. -/
theorem fano_isVertexExpander : IsVertexExpander fano 2 (5 / 2) := by
  have h : ∀ S : Finset (Fin 7), #S ≤ 2 → 5 * #S ≤ 2 * #(neighbors fano S) := by decide +kernel
  intro S hS
  have : (5 * #S : ℝ) ≤ 2 * #(neighbors fano S) := by exact_mod_cast h S hS
  linarith

/-- The decoding hypothesis `3 c < 4 α` holds: `9 < 10`. -/
example : (3 : ℝ) * (3 : ℕ) < 4 * (5 / 2) := by norm_num

/-- Unique neighbours: two points share exactly one line, so they have `4` unique neighbours,
matching `(2 α - c) |S| = 2 · 2 = 4`. -/
example : #(uniqueNeighbors fano {0, 1}) = 4 := by decide

/-- Expansion fails for the three collinear points `{0, 1, 3}` of line `0`. -/
theorem fano_not_isVertexExpander_three : ¬ IsVertexExpander fano 3 (5 / 2) := by
  intro h
  have h1 := h {0, 1, 3} (by decide)
  rw [show #(neighbors fano {0, 1, 3}) = 7 by decide,
    show #({0, 1, 3} : Finset (Fin 7)) = 3 by decide] at h1
  norm_num at h1

/-! ### The code -/

/-- The complement of line `0 = {0, 1, 3}`. -/
def c₁ : Fin 7 → Bool := ![false, false, true, false, true, true, true]

/-- The complement of line `4 = {4, 5, 0}`. -/
def c₂ : Fin 7 → Bool := ![false, true, true, true, false, false, true]

theorem c₁_mem : c₁ ∈ code fano := by
  rw [mem_code_iff_unsat_eq_empty]; decide

theorem c₂_mem : c₂ ∈ code fano := by
  rw [mem_code_iff_unsat_eq_empty]; decide

/-- A word outside the code. -/
example : ![true, false, false, false, false, false, false] ∉ code fano := by
  rw [mem_code_iff_unsat_eq_empty]; decide

/-- **Distance.** Distinct codewords differ in at least `4` positions, from `2 α k ≤ c · d`. -/
theorem four_le_hammingDist {x w : Fin 7 → Bool} (hx : x ∈ code fano) (hw : w ∈ code fano)
    (hxw : x ≠ w) : 4 ≤ hammingDist x w := by
  have h := two_mul_mul_le_hammingDist fano_isLeftBounded fano_isVertexExpander (by norm_num)
    hx hw hxw
  have : (3 : ℝ) < hammingDist x w := by push_cast at h; linarith
  exact_mod_cast this

/-- The distance bound is tight. -/
example : hammingDist c₁ 0 = 4 := by decide

/-- The bound from `lt_minDist` alone is `d > 2`. -/
example : (2 : ℕ∞) < Code.minDist (code fano : Set (Fin 7 → Bool)) :=
  lt_minDist fano_isLeftBounded fano_isVertexExpander (by norm_num)

/-- **Rate.** The trivial bound `1 - c / d = 0` for this square graph. -/
example : 1 - (3 : ℝ) / 3 ≤ Real.logb 2 (Nat.card (code fano)) / 7 := by
  simpa using one_sub_div_le_rate_of_isBiregular fano_isBiregular (by norm_num) (by decide)

/-! ### Flip decoding -/

/-- The pivot rule: the first flippable point. -/
abbrev pick : (Fin 7 → Bool) → Option (Fin 7) := firstFlippable fano (List.finRange 7)

theorem isFlipRule_pick : IsFlipRule fano pick :=
  isFlipRule_firstFlippable List.mem_finRange

/-- `c₁` with point `0` flipped. -/
def y₁ : Fin 7 → Bool := ![true, false, true, false, true, true, true]

/-- Three checks are violated, and point `0` is flippable. -/
example : #(unsat fano y₁) = 3 ∧ IsFlippable fano y₁ 0 := by decide

/-- The decoder flips point `0` back, by computation. -/
example : decode pick 3 y₁ = c₁ := by decide

/-- **Flip decoding corrects every single error**, by the general theorem. -/
theorem decode_eq_of_hammingDist_le_one {x w : Fin 7 → Bool} (hw : w ∈ code fano)
    (hx : hammingDist x w ≤ 1) : decode pick 3 x = w := by
  refine decode_eq fano_isLeftBounded fano_isVertexExpander (by norm_num) hw ?_ isFlipRule_pick
    ((card_unsat_le fano_isLeftBounded hw).trans (by omega))
  have : (hammingDist x w : ℝ) ≤ 1 := by exact_mod_cast hx
  push_cast
  nlinarith

/-- The same via `decode_eq_of_two_mul_le`, with `3 · d(x, w)` rounds. -/
example {x w : Fin 7 → Bool} (hw : w ∈ code fano) (hx : hammingDist x w ≤ 1) :
    decode pick (3 * hammingDist x w) x = w :=
  decode_eq_of_two_mul_le fano_isLeftBounded fano_isVertexExpander (by norm_num) (by norm_num) hw
    (by omega) isFlipRule_pick

/-- Two errors can be ambiguous: this word is at distance `2` from both `c₁` and `c₂`. -/
example : hammingDist ![false, true, true, false, true, false, true] c₁ = 2 ∧
    hammingDist ![false, true, true, false, true, false, true] c₂ = 2 := by
  decide

end ComplexityTests.ExpanderCode
