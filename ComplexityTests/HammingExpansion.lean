/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Hamming.Expansion
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

/-!
# Tests: expansion of the line closure

In `Bool ^ 2`, the line closure of one point is the point and its two neighbours, and the line
closure of the line `x 0 = false` is the whole square. In `(Fin 3) ^ 2` the closure of one point
has `1 + 2 * 2 = 5` points, and the Expansion Lemma asks for at least `5 / 4` of a point beyond
the set. The full square shows that the hypothesis `|S| ≤ |X| ^ n / 2` cannot be dropped: it is
its own closure.
-/

namespace ComplexityTests.HammingExpansion

open Cslib Finset

/-- The origin of `Bool ^ 2`. -/
private def origin : Finset (Fin 2 → Bool) := {![false, false]}

-- One point: its closure is the point and its two neighbours.
example : #(lineClosure origin) = 3 := by decide

/-- The line `x 0 = false` of `Bool ^ 2`. -/
private def line0 : Finset (Fin 2 → Bool) := {x | x 0 = false}

-- A line: its closure is the whole square, two points beyond the line.
example : #(lineClosure line0 \ line0) = 2 := by decide

-- The Expansion Lemma for the line, with `|S| = 2 ≤ 4 / 2`.
example : #line0 ≤ 2 * 2 * #(lineClosure line0 \ line0) :=
  card_le_two_mul_card_lineClosure_sdiff (by decide)

/-- The origin of `(Fin 3) ^ 2`. -/
private def origin3 : Finset (Fin 2 → Fin 3) := {![0, 0]}

-- Its closure has five points.
example : #(lineClosure origin3) = 5 := by decide

-- The Expansion Lemma in the form `|S̄| ≥ |S| (1 + 1 / (2 n))`.
example : (2 * 2 + 1) * #origin3 ≤ 2 * 2 * #(lineClosure origin3) :=
  card_lineClosure_ge (by norm_num) (by decide)

-- Without the size hypothesis the conclusion fails: the whole square is its own closure.
example : ¬#(univ : Finset (Fin 2 → Bool)) ≤
    2 * 2 * #(lineClosure (univ : Finset (Fin 2 → Bool)) \ univ) := by
  decide

end ComplexityTests.HammingExpansion
