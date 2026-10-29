/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Complexity.Foundations.Combinatorics.GreedySchedules
import Mathlib.Tactic.NormNum

public section

open Cslib.BalancedSchedules
open Finset

namespace Cslib.Tests.GreedySchedules

local instance : DecidableEq (Fin 1) := FinEnum.decEq
local instance : DecidableEq (Fin 2) := FinEnum.decEq
local instance : DecidableEq (Fin 64) := FinEnum.decEq

private def edge (v : Fin 2) : Fin 1 × Fin 2 := (0, v)
private abbrev Word := Fin 1 → Fin 2
private def words : List Word := [fun _ => 0, fun _ => 1]
private def initial : (Fin 2 → Option Word) × (Fin 1 → Option Word) :=
  (fun _ => none, fun _ => none)
private def slots : List (Fin 2 ⊕ Fin 1) := [.inl 0, .inl 1, .inr 0]

private def edgeWithEmptyFactor (v : Fin 2) : Fin 2 × Fin 2 := (0, v)

/-- Complete two-variable run produces distinct single-bit words. -/
theorem two_variables_run :
    List.ofFn (fun v => List.ofFn
      ((greedySchedules (T := Fin 1) (G := Fin 2)
        (fun v : Fin 2 => ((0 : Fin 1), v)) 2 0).1 v)) = [[0], [1]] := by
  decide +kernel

-- Normalized partial scores, tie-breaking, repeated/fixed slots, incomplete inputs,
-- empty-scope factors, coordinate enumeration, and empty variable/factor regimes.
example :
    List.ofFn ((greedySchedules (T := Fin 1) (G := Fin 2) edge 2 0).2 0) = [0] ∧
    normalizedPartialScore edge
      (fun v => some ((greedySchedules (T := Fin 1) (G := Fin 2) edge 2 0).1 v))
      (fun f => some ((greedySchedules (T := Fin 1) (G := Fin 2) edge 2 0).2 f)) 2 = 1 / 4 ∧
    normalizedPartialScore edge initial.1 initial.2 2 = 1 ∧
    (((greedyLabelPass edge 2 words.reverse slots initial).1 0).map (fun w => w 0) = some 1 ∧
      ((greedyLabelPass edge 2 words.reverse slots initial).1 1).map (fun w => w 0) = some 0) ∧
    List.ofFn (fun v => ((greedyLabelPass edge 2 words
      [.inl 0, .inl 0, .inl 1, .inr 0, .inl 0] initial).1 v).map (fun w => w 0)) =
      [some 0, some 1] ∧
    ((greedyLabelPass edge 2 words [.inl 0]
      (fun _ => some (fun _ => 1), fun _ => none)).1 0).map (fun w => w 0) = some 1 ∧
    ((greedyLabelPass edge 2 words [.inl 0] initial).1 1 = none ∧
      (greedyLabelPass edge 2 [] slots initial).1 0 = none) ∧
    List.ofFn ((greedySchedules (T := Fin 1) (G := Fin 2)
      edgeWithEmptyFactor 2 1).2 1) = [1] ∧
    List.ofFn ((greedySchedules (T := Fin 1) (G := Fin 2)
      edgeWithEmptyFactor 2 1).2 0) = [0] ∧
    (List.Pi.enum (fun _ : Fin 2 => Fin 2)).map List.ofFn =
      [[0, 0], [0, 1], [1, 0], [1, 1]] ∧
    List.ofFn (fun v => List.ofFn
      ((greedySchedules (T := Fin 0) (G := Fin 2) edge 2 0).1 v)) = [[], []] ∧
    List.ofFn (fun v => List.ofFn ((greedySchedules (T := Fin 1) (G := Fin 2)
      (Fin.elim0 : Fin 0 → Fin 0 × Fin 0) 0 (0 : Fin 2)).1 v)) = [] := by
  refine ⟨?_, (by decide +kernel), (by decide +kernel), (by decide +kernel),
    (by decide +kernel), (by decide +kernel), (by decide +kernel), ?_, ?_, (by decide +kernel),
    (by decide +kernel), (by decide +kernel)⟩
  · dsimp only [greedySchedules]
    simp only [show (0 : Fin 1) = (edge (0 : Fin 2)).1 from rfl]
    rw [@normalizeEmptyFactors_factorOf (Fin 2) inferInstance (Fin 1) (Fin 1) (Fin 2)
      FinEnum.decEq (fun e => (edge e).1) 0 _ (0 : Fin 2)]
    decide +kernel
  · rw [greedySchedules_empty_factor _ _ _ (by decide +kernel)]
    rfl
  · dsimp only [greedySchedules]
    change List.ofFn (normalizeEmptyFactors (T := Fin 1)
      (fun e => (edgeWithEmptyFactor e).1) 1 _ (edgeWithEmptyFactor (0 : Fin 2)).1) = [0]
    rw [@normalizeEmptyFactors_factorOf (Fin 2) inferInstance (Fin 2) (Fin 1) (Fin 2)
      FinEnum.decEq (fun e => (edgeWithEmptyFactor e).1) 1 _ (0 : Fin 2)]
    decide +kernel

-- A genuine matching incidence family satisfies both of the manuscript's size hypotheses.
-- Applying the algorithmic theorem here avoids reducing the entire 128-slot program in a test.
private def matching (v : Fin 64) : Fin 64 × Fin 64 := (v, v)
example : @occupancy (Fin 64) (Fin 2) (Fin.fintype 64)
    (fun a b => @FinEnum.decEq (Fin 2) (@FinEnum.fin 2) a b) (fun v =>
    (greedySchedules (T := Fin 1) (G := Fin 2) matching (1 + 1) 0).1 v 0) 0 *
      Fintype.card (Fin 2) ≤ 2 * Fintype.card (Fin 64) := by
  have hb (e : Fin 64) : #{e' : Fin 64 | (matching e').2 = (matching e).2} ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
  have hw (e : Fin 64) : #{e' : Fin 64 | (matching e').1 = (matching e).1} ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    exact (mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm
  have h := greedySchedules_balanced (T := Fin 1) (G := Fin 2) matching hb hw
    (by decide) (by norm_num [Fintype.card_fun]) (by norm_num) 0
  exact h.2 0 0

end Cslib.Tests.GreedySchedules
