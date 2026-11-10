/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.BitString.CyclicDifference
import Complexity.Foundations.Data.BitString.DeltaMatroid.Basic
import Mathlib.Data.Fin.VecNotation

/-! Concrete checks for ordered cyclic differences and their degenerate arities. -/

open Cslib Cslib.BitString

example : cyclicDifference ![false, true, true] = ![true, false, true] := by decide

example : cyclicDifference ![true, false, false] = ![true, false, true] := by decide

example : (![false, true, true] : Fin 3 → Bool) ≠ ![true, false, false] := by decide

example : cyclicDifference ![true] = ![false] := by decide

example : cyclicDifference (fun _ : Fin 0 => true) = fun _ => false := by decide

example : parityOn Finset.univ (cyclicDifference ![true, false, true, false]) = false := by
  decide

example : cyclicIntegral ![true, false, true] = ![false, true, true] := by decide

example : ¬ ∃ x : Fin 3 → Bool, cyclicDifference x = ![true, true, true] := by
  rw [exists_cyclicDifference_eq_iff]
  decide

example : ∃ x : Fin 0 → Bool, cyclicDifference x = fun _ => false := by
  exact ⟨fun _ => false, by decide⟩

example : IsSelfComplementary {x : Fin 3 → Bool | x 0 ≠ x 1 ∨ x 1 ≠ x 2} := by
  unfold IsSelfComplementary
  decide

example : ¬ IsSelfComplementary ({fun _ : Fin 1 => false} : Set (Fin 1 → Bool)) := by
  unfold IsSelfComplementary
  decide

example : IsSelfComplementary (∅ : Set (Fin 0 → Bool)) := by
  unfold IsSelfComplementary
  decide

example : cyclicDifference ![false, false, true, true] ≠
    cyclicDifference ![false, true, false, true] := by decide

-- Ternary NAE becomes the three tuples of weight two under cyclic differences.
private def naeThree : Set (Fin 3 → Bool) := {x | x 0 ≠ x 1 ∨ x 1 ≠ x 2}

private theorem naeThree_difference : cyclicDifferenceRelation naeThree =
    {d : Fin 3 → Bool | parityOn Finset.univ d = false ∧ d ≠ fun _ => false} := by
  apply Set.ext
  change ∀ d, (∃ x : Fin 3 → Bool, (x 0 ≠ x 1 ∨ x 1 ≠ x 2) ∧
    cyclicDifference x = d) ↔ parityOn Finset.univ d = false ∧ d ≠ fun _ => false
  decide

example : IsEvenDeltaMatroid (cyclicDifferenceRelation naeThree) := by
  rw [naeThree_difference]
  constructor
  · constructor
    · exact ⟨![true, true, false], by decide⟩
    · decide
  · decide

-- NAE itself is not even: it contains tuples of both parities.
example : ¬ IsEvenDeltaMatroid naeThree := by
  intro h
  have hp := h.parity_eq (x := ![true, false, false]) (y := ![true, true, false])
    (by change true ≠ false ∨ false ≠ false; decide)
    (by change true ≠ true ∨ true ≠ false; decide)
  contradiction
