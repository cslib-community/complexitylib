/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

import Complexity.Foundations.Combinatorics.BalancedSchedules
import Mathlib.Tactic.NormNum

open Cslib.BalancedSchedules
open scoped BigOperators

-- The uniform two-label schedule has zero collision variance.
example : potential (fun a : Bool => a) = 0 := by
  norm_num [potential, occupancy, Fintype.card_subtype]

-- Concentrating both objects in one label retains both diagonal and off-diagonal collisions.
example : (∑ u : Bool, occupancy (fun _ : Bool => false) u ^ 2) = 4 := by
  norm_num [potential, occupancy, Fintype.card_subtype]
example : potential (fun _ : Bool => false) = 2 := by
  norm_num [potential, occupancy, Fintype.card_subtype]

-- Empty sources and an empty label space cause no division or nonempty-fiber assumption.
example : potential (fun a : Fin 0 => a) = 0 := by
  norm_num [potential, occupancy, Fintype.card_subtype]
example : (∑ u : Bool, occupancy (fun a : Fin 0 => Fin.elim0 a) u) = 0 := by
  norm_num [potential, occupancy, Fintype.card_subtype]

-- A label with no preimage has zero occupancy.
example : occupancy (fun _ : Bool => false) true = 0 := by
  norm_num [potential, occupancy, Fintype.card_subtype]

-- Both incidences of the same original variable use the same variable label.
-- There are two factors and only one original variable, not two Boolean clones.
example (a : Unit → Bool) (d : Bool → Bool) :
    ((fun p : Bool × Unit => (a p.2, d p.1)) (false, ())).1 =
      ((fun p : Bool × Unit => (a p.2, d p.1)) (true, ())).1 := rfl

-- A real nonuniform example satisfies the sharp rational potential criterion.
example : occupancy (fun a : Fin 3 => decide (a.val < 2)) true * 2 ≤ 2 * 3 := by
  decide

-- Dropping the potential/size restriction cannot give a universal twice-the-mean bound.
example : ¬ ∀ label : Fin 3 → Fin 3, ∀ u,
    occupancy label u * Fintype.card (Fin 3) ≤ 2 * Fintype.card (Fin 3) := by
  intro h
  have hbad := h (fun _ => 0) 0
  norm_num [occupancy, Fintype.card_subtype] at hbad

-- The two normalization factors remain independent.
example : (6 : ℚ) ≤ 2 * 4 ∧ (15 : ℚ) ≤ 2 * 30 := by
  exact components_le_of_normalized_le_two (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
