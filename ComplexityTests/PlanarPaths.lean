/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Computability.Complexity.Problems.SAT.Planar.Paths.Occupancy

/-! Source occurrence indices retain multiplicity and literal order. -/

open Cslib.Logic.PL Cslib.Complexity.SAT.PlanarCompile

private def repeated : CNF ℕ := [[(0, true), (0, false), (0, true)], []]

example : (Cslib.Logic.PL.occurrences repeated).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences repeated).length = 3 := by decide

example : (Cslib.Logic.PL.occurrences repeated).map (occurrencePath repeated) = paths repeated :=
  occurrencePaths_eq_paths _

example : (Cslib.Logic.PL.occurrences ([] : CNF ℕ)).Nodup := Cslib.Logic.PL.occurrences_nodup _

example : (Cslib.Logic.PL.occurrences ([[]] : CNF ℕ)).map (occurrencePath [[]]) = paths [[]] :=
  occurrencePaths_eq_paths _

-- This client imports no global Geometry or degree-count module.
private def single : CNF ℕ := [[(0, true)]]

private theorem single_width : ∀ c ∈ single, c.length ≤ 3 := by
  intro c hc
  simp only [single, List.mem_singleton] at hc
  subst c
  decide

private theorem single_count : ∀ v, single.vars.count v ≤ 3 := by
  intro v
  by_cases hv : v = 0
  · subst v
    decide
  · simp [single, CNF.vars, Ne.symm hv]

example : ((paths single).filter fun r => r.contains (3, 4)).length ≤ 1 :=
  paths_filter_length_le_one single_width single_count (by decide +kernel) (by decide)

example : ((paths single).filter fun r => r.contains (3, 4)).length = 1 := by decide +kernel

-- Canonical path certificates are available from the shared path API alone.
private def singleOccurrence : Occurrence ℕ := (0, 0, (0, true))

private theorem single_mem : singleOccurrence ∈ Cslib.Logic.PL.occurrences single := by decide

-- The one incidence edge yields one 33-point path in both APIs.
example : (paths single).map List.length = [33] := by
  rw [paths_eq_unitPaths]
  decide +kernel

example : (occurrencePath single singleOccurrence).length = 33 := by
  rw [occurrencePath_eq_unitPath]
  decide +kernel

example :
    (Cslib.Logic.PL.occurrences single).idxOf singleOccurrence = 0 ∧
    (Cslib.Logic.PL.occurrences single).idxOf singleOccurrence < 1 :=
  ⟨by decide, occurrence_index_lt single_mem⟩

-- The source center is (4, 4), and the only clause center is (12, 12).
example :
    (occurrencePath single singleOccurrence).head? = some (4, 4) ∧
    (occurrencePath single singleOccurrence).getLast? = some (12, 12) := by
  convert occurrencePath_endpoints single_mem using 1 <;> decide +kernel

example :
    (occurrencePath single singleOccurrence).Nodup ∧
    occurrencePath single singleOccurrence ≠ [] ∧
    2 ≤ (occurrencePath single singleOccurrence).length :=
  ⟨occurrencePath_nodup single_mem, occurrencePath_ne_nil single_mem,
    occurrencePath_length_ge_two single_mem⟩

-- The first and last segments are actual unit steps, not supplied path hypotheses.
example : Cslib.Orthogonal.length (4, 4) (3, 4) = 1 :=
  occurrencePath_unit single_mem (e := ((4, 4), (3, 4))) (by decide +kernel)

example :
    let r := occurrencePath single singleOccurrence
    r.getD (r.length - 2) (0, 0) = (11, 12) ∧
    r.getLastD (0, 0) = (12, 12) ∧
    Cslib.Orthogonal.length (r.getD (r.length - 2) (0, 0)) (r.getLastD (0, 0)) = 1 :=
  ⟨by decide +kernel, by decide +kernel, occurrencePath_last_unit single_mem⟩
