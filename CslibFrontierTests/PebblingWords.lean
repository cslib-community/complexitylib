/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of pebble configurations as words)

public import CslibFrontier.Computability.Pebbling.Words
import Mathlib.Tactic.FinCases

/-!
# Deciding a pebble game by Savitch's recursion

On the path `0 → 1`, vertex `1` is ready when vertex `0` carries a pebble. Evaluating the midpoint
recursion on two-bit words shows that `1` is pebblable with two pebbles and not with one, and
`Cslib.Pebbling.reach_wordStep_iff_blackPebblable` turns both evaluations into statements about
the game.
-/

@[expose] public section

namespace CslibFrontierTests.PebblingWords

open Cslib.BitString Cslib.Pebbling Cslib.Reachability

/-- The path `0 → 1`. -/
def path : Digraph (Fin 2) where
  Adj u v := u = 0 ∧ v = 1

/-- Vertex `1` is ready when bit `0` is set; vertex `0` is a source. -/
def ready (w : List Bool) (i : ℕ) : Bool := i != 1 || w.getD 0 false

theorem ready_iff (C : Finset (Fin 2)) (i : Fin 2) :
    ready (indicatorList C) i = true ↔ ∀ u, path.Adj u i → u ∈ C := by
  have h0 := getD_indicatorList C 0
  simp only [Fin.val_zero] at h0
  simp only [ready, h0]
  fin_cases i <;> simp [path]

-- Two pebbles suffice for vertex `1`.
example : BlackPebblable path 2 1 :=
  (reach_wordStep_iff_blackPebblable ready_iff).1 (by rw [indicatorList_singleton]; decide)

-- One pebble does not.
example : ¬ BlackPebblable path 1 1 := fun h => by
  have := (reach_wordStep_iff_blackPebblable ready_iff).2 h
  rw [indicatorList_singleton] at this
  revert this
  decide

end CslibFrontierTests.PebblingWords
