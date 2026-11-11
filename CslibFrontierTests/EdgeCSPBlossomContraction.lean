/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Reference
import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Size
import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Optimality
import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom
import Mathlib.Tactic.FinCases

/-! Whole-instance contraction on actual fresh-search events, with sparse binary names,
constraint-LCA preparation, repeated originals and exact finite size/defect accounting. -/

namespace CslibFrontierTests.EdgeCSPBlossomContraction

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest
open Cslib.Logic.PL.CSP.Blossom

private def starTable : Table :=
  ⟨3, [[false, false, false], [true, true, false], [true, false, true]]⟩
private def equalTable : Table := ⟨2, [[false, false], [true, true]]⟩
private def trueTable : Table := ⟨1, [[true]]⟩
private def oddTable : Table := ⟨2, [[false, true], [true, false]]⟩
private def falseTable : Table := ⟨1, [[false]]⟩
private abbrev x₀ : ℕ := 2 ^ 100
private abbrev x₁ : ℕ := 2 ^ 200
private abbrev x₂ : ℕ := 2 ^ 250
private abbrev star : CSP Table ℕ :=
  [(starTable, [x₀, x₁, x₂]), (equalTable, [x₁, x₂]), (trueTable, [x₀])]
private def initial : OccurrenceLabeling star Bool := fun o => o.1.val == 2
private abbrev sp (j : Fin 3) : Occurrence star := ⟨0, j⟩
private abbrev dp (j : Fin 2) : Occurrence star := ⟨1, j⟩
private def meeting : Meeting star :=
  ⟨[x₀], [⟨sp 0, [sp 1, sp 2]⟩], ⟨dp 0, []⟩, dp 1⟩
private def data : BlossomData star :=
  ⟨.inr (0, 0), ⟨x₀, [(sp 0, sp 1)]⟩,
    ⟨x₁, [(dp 0, dp 1), (sp 2, sp 1)]⟩, [1, 0], 1, some (sp 1), some (sp 2)⟩
private def prepared : OccurrenceLabeling star Bool := data.prepare.flip initial
private abbrev inside : List ℕ := internal data.cycle
private def output : CSP Table ℕ := contract prepared inside
private def outputLabels : OccurrenceLabeling output Bool := reference prepared inside

private theorem star_edge : EdgeInstance star := by unfold EdgeInstance; decide +kernel
private theorem star_valid : ValidLabeling Table.sem initial := by unfold ValidLabeling; decide
private theorem star_even : EdgeInstance.EvenConstraints Table.sem star := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem run : search Table.sem initial = .blossom meeting := by decide +kernel
private theorem extracted : meeting.blossomData = some data := by rfl
private theorem prepared_spec : data.cycle.IsBlossom Table.sem prepared ∧
    ValidLabeling Table.sem prepared ∧ (defects prepared).card = (defects initial).card := by
  obtain ⟨b, hb, hc, hv, hn⟩ := search_blossom_correct Table.sem initial
    star_edge star_valid star_even run
  cases Option.some.inj (hb.symm.trans extracted)
  exact ⟨hc, hv, hn⟩

-- This is the constraint-LCA branch, with an actual preparatory flip and copied timestamps.
example : data.ancestor = .inr (0, 0) ∧ data.prepare.steps.length = 1 ∧
    data.times = [1, 0] ∧ data.pivot = 1 ∧ prepared (sp 0) = true := by decide

-- Every touched constraint contributes exactly one connector, even though the raw cycle
-- uses two ports at each. The untouched original unary constraint keeps its position and name.
example : output =
    [(oddTable, [x₀, x₂ + 1]), (falseTable, [x₂ + 2]), (trueTable, [x₀]),
      (Table.exactlyOne [x₂ + 1, x₂ + 2], [x₂ + 1, x₂ + 2])] := by decide +kernel

example : EdgeInstance output ∧ EdgeInstance.EvenConstraints Table.sem output ∧
    ValidLabeling Table.sem outputLabels := by
  exact ⟨edge_contract star_edge prepared inside,
    even_contract prepared_spec.2.1 star_even inside (touched_ne_nil _ prepared_spec.1.2.2.1),
    valid_reference prepared_spec.2.1 inside (touched_ne_nil _ prepared_spec.1.2.2.1)⟩

-- Contraction can retain the variable count. Counting only variables would not justify recursion.
example : star.numVars = 3 ∧ output.numVars = 3 ∧ star.positiveCount = 3 ∧
    output.positiveCount = 4 ∧ star.contractionMeasure = 3 ∧ output.contractionMeasure = 2 := by
  decide +kernel

example : output.numVars + inside.toFinset.card = star.numVars + (touched star inside).length ∧
    output.contractionMeasure < star.contractionMeasure := by
  exact ⟨numVars_contract_add prepared inside (internal_subset_vars _),
    contractionMeasure_contract_lt star_edge prepared_spec.1⟩

-- The one internal defect becomes exactly one fresh connector defect. The all-zero central
-- row is rejected, and the actual finite reference buffer contains a valid central one-hot row.
example : defects prepared = {x₁} ∧ defects outputLabels = {x₂ + 1} ∧
    output[3].1.sem [false, false] = false ∧
    output[3].1.sem [true, false] = true ∧
    output[0].1.sem [false, true] = true ∧ output[0].1.sem [false, false] = false := by
  decide +kernel

example : (defects outputLabels).card = (defects initial).card := by
  exact (card_defects_reference_blossom star_edge prepared_spec.1).trans prepared_spec.2.2

private theorem output_optimal : IsOptimalLabeling Table.sem outputLabels := by
  have hv := valid_reference prepared_spec.2.1 inside (touched_ne_nil _ prepared_spec.1.2.2.1)
  have hG := edge_contract star_edge prepared inside
  have hM := even_contract prepared_spec.2.1 star_even inside
    (touched_ne_nil _ prepared_spec.1.2.2.1)
  refine ⟨hv, ?_⟩
  intro g hg
  have hp := hG.card_defects_mod_two_eq hM hv hg
  have hc : (defects outputLabels).card = 1 := by decide +kernel
  change (defects outputLabels).card % 2 = (defects g).card % 2 at hp
  rw [hc] at hp ⊢
  omega

-- The actual recursively returned reference optimum transfers across the nonempty
-- constraint-LCA preparation. Odd common parity forces its one unavoidable defect.
example : IsOptimalLabeling Table.sem prepared := by
  exact isOptimal_of_reference star_edge prepared_spec.1 prepared_spec.2.1 star_even output_optimal

-- This surviving sparse outside port has its prepared value, not its unprepared zero value.
example : outputLabels (oldPort prepared inside (sp 0) (by decide +kernel)) = true := by
  change reference prepared inside (oldPort prepared inside (sp 0) (by decide +kernel)) = true
  rw [reference_oldPort]
  decide

private def pairTable : Table :=
  ⟨4, [[false, false, false, false], [true, true, false, false],
    [false, false, true, true], [true, true, true, true]]⟩
private abbrev repeated : CSP Table ℕ :=
  [(pairTable, [0, 1, 2, 3]), (equalTable, [1, 2]), (oddTable, [3, 0])]
private def repeatedLabels : OccurrenceLabeling repeated Bool :=
  fun o => o.1.val == 2 && o.2.val == 1

private def repeatedContraction : Option (CSP Table ℕ) :=
  match search Table.sem repeatedLabels with
  | .blossom m => m.blossomData.map fun b =>
      contract (b.prepare.flip repeatedLabels) (internal b.cycle)
  | _ => none

-- The actual fresh-search cycle revisits original constraint zero. All four of its internal
-- positions are gathered in a single simultaneous table contraction, with only one connector.
example : repeatedContraction = some
    [(falseTable, [4]), (falseTable, [5]), (falseTable, [6]),
      (Table.exactlyOne [4, 5, 6], [4, 5, 6])] := by decide +kernel

-- Nullary constraints remain present and consume no units of the positive-count resource.
example : CSP.positiveCount
    ([(⟨0, [[]]⟩, []), (⟨0, [[]]⟩, [])] : CSP Table ℕ) = 0 := by decide

end CslibFrontierTests.EdgeCSPBlossomContraction
