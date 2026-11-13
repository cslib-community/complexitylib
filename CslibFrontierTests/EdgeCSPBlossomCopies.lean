/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom
import CslibFrontier.Logics.Propositional.CSP.Table.DeltaMatroid
import Mathlib.Tactic.FinCases

/-! A shared copied node satisfies the old graph conditions but invalidates Lemma 40.
The copy distinction is required even for even delta-matroid tables and a genuine edge instance.
The five-bit relation and the counterexample are original finite constructions.
-/

namespace CslibFrontierTests.EdgeCSPBlossomCopies

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.DAG

private def row (mask : ℕ) : List Bool := (List.range 5).map mask.testBit
private def repeatedTable : Table :=
  ⟨5, [0, 3, 5, 9, 10, 12, 18, 20, 27, 29].map row⟩
private def equalTable : Table := ⟨2, [[false, false], [true, true]]⟩
private def oddTable : Table := ⟨2, [[false, true], [true, false]]⟩
private def trueTable : Table := ⟨1, [[true]]⟩
private abbrev badCSP : CSP Table ℕ :=
  [⟨repeatedTable, [0, 1, 2, 3, 4]⟩, ⟨equalTable, [1, 2]⟩,
    ⟨oddTable, [3, 0]⟩, ⟨trueTable, [4]⟩]
private def labels : OccurrenceLabeling badCSP Bool :=
  fun o => o.1.val == 3 || (o.1.val == 2 && o.2.val == 1)
private abbrev cp (j : Fin 5) : Occurrence badCSP := ⟨0, j⟩
private abbrev dp (j : Fin 2) : Occurrence badCSP := ⟨1, j⟩
private abbrev ep (j : Fin 2) : Occurrence badCSP := ⟨2, j⟩
private def cycle : Walk badCSP :=
  ⟨0, [(cp 0, cp 1), (dp 0, dp 1), (cp 2, cp 3), (ep 0, ep 1)]⟩
private def graph : DAG badCSP := blossomDAG cycle [1, 2, 1, 0] 2
private def rank : Node badCSP → ℕ
  | .inl 0 => 0
  | .inl 3 => 2
  | .inl _ => 4
  | .inr c => if c.1.val == 2 then 1 else if c.1.val == 0 then 3 else 5

private theorem edge : EdgeInstance badCSP := by unfold EdgeInstance; decide
private theorem valid : ValidLabeling Table.sem labels := by unfold ValidLabeling; decide
private theorem even : EdgeInstance.EvenConstraints Table.sem badCSP := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := {
      nonempty := by
        change ∃ t, _
        decide +kernel
      exchange := by decide +kernel }
    parity_eq := by decide +kernel }

private theorem graph_isFDAG : graph.IsFDAG Table.sem labels := by
  refine ⟨valid, ?_, ?_, ?_, ⟨?_, ⟨rank, ?_⟩⟩, ?_, ?_⟩
  · exact blossomDAG_supported _ _ _
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy, cp, dp, ep, Occurrence.var]
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy, cp, dp, ep, Occurrence.var]
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy]
  · intro x y hxy
    rcases hxy with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, hlt, rfl, rfl⟩
    · simp only [graph, blossomDAG, blossomArcs, cycle, List.mem_toFinset,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · simp only [graph, blossomDAG, blossomArcs, cycle, List.map_cons, List.map_nil,
        List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hc hd
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [Arc.copy] at hlt <;> decide
  · intro a ha b hb hai hab
    simp only [graph, blossomDAG, blossomArcs, cycle, List.mem_toFinset,
      List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num at hai <;> norm_num [Arc.copy, cp, dp, ep] at hab <;>
      unfold ValidLabeling <;> decide +kernel
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy]

-- Every condition of the original `IsBlossom`, with the actual timestamp list made explicit.
example : cycle.IsWalk ∧ cycle.finish = cycle.start ∧ cycle.steps ≠ [] ∧
    Inconsistent labels cycle.start ∧ Walk.InternallyConsistent labels cycle.steps ∧
    [1, 2, 1, 0].length = cycle.steps.length ∧
    0 < (2 : ℕ) ∧ 2 ≤ cycle.steps.length ∧ graph.IsFDAG Table.sem labels := by
  refine ⟨by simp only [cycle, Walk.IsWalk, Walk.Linked]; decide, by decide, by decide, by decide,
    by simp only [cycle, Walk.InternallyConsistent]; decide,
    rfl, by decide, by decide, graph_isFDAG⟩

-- Lemma 40 requires this proper variable-ended prefix to be an f-walk. It is invalid:
-- the repeated five-ary relation receives 11110, which is not a stored row.
example : ¬ ValidLabeling Table.sem ((cycle.take 3).flip labels) := by
  intro h
  have hh := h 0
  have hn : badCSP[0].rel.sem (localTuple ((cycle.take 3).flip labels) 0) = false := by decide
  exact Bool.false_ne_true (hn.symm.trans hh)

example : ¬ [1, 2, 1, 0].Nodup := by decide

-- Reusing an original constraint is permitted, but reusing the same copied step is not.
example : ¬ cycle.DistinctCopies [1, 2, 1, 0] := by
  unfold Walk.DistinctCopies Walk.copies
  decide

-- This is also a counterexample to applying whole-blossom SAT lifting under the old
-- conditions: the original instance has no model, while its source §5.3 table contraction does.
example : ¬ badCSP.Satisfiable Table.sem := by
  rintro ⟨σ, hσ⟩
  have hn : ∀ a b c d e : Bool, ¬ (repeatedTable.sem [a, b, c, d, e] = true ∧
      equalTable.sem [b, c] = true ∧ oddTable.sem [d, a] = true ∧
      trueTable.sem [e] = true) := by decide +kernel
  apply hn (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)
  simpa [CSP.eval, badCSP, Constraint.eval] using hσ

private def badContraction : CSP Table ℕ :=
  [⟨repeatedTable.contract (row 0) [0, 1, 2, 3], [4, 5]⟩,
    ⟨equalTable.contract [false, false] [0, 1], [6]⟩,
    ⟨oddTable.contract [false, true] [0, 1], [7]⟩,
    ⟨trueTable, [4]⟩, ⟨Table.exactlyOne [5, 6, 7], [5, 6, 7]⟩]

example : badContraction.Satisfiable Table.sem := by
  refine ⟨fun v => v == 4 || v == 5, ?_⟩
  decide

private def pairedTable : Table :=
  ⟨4, [[false, false, false, false], [true, true, false, false],
    [false, false, true, true], [true, true, true, true]]⟩
private abbrev freshCSP : CSP Table ℕ :=
  [⟨pairedTable, [0, 1, 2, 3]⟩, ⟨equalTable, [1, 2]⟩, ⟨oddTable, [3, 0]⟩]
private def freshLabels : OccurrenceLabeling freshCSP Bool :=
  fun o => o.1.val == 2 && o.2.val == 1
private theorem fresh_edge : EdgeInstance freshCSP := by unfold EdgeInstance; decide
private theorem fresh_valid : ValidLabeling Table.sem freshLabels := by
  unfold ValidLabeling
  decide
private theorem fresh_even : EdgeInstance.EvenConstraints Table.sem freshCSP := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

-- A real fresh-search blossom visits original constraint zero twice. Both copies remain
-- present, with distinct timestamps; the repair does not prohibit repeated originals.
theorem fresh_repeated_blossom : match Forest.search Table.sem freshLabels with
    | .blossom m => ∃ b, m.blossomData = some b ∧
        b.cycle.IsBlossom Table.sem (b.prepare.flip freshLabels) ∧
        (b.cycle.steps.map (fun (input, _) => input.1.val)).count 0 = 2 ∧ b.times.Nodup
    | _ => False := by
  have hc : (match Forest.search Table.sem freshLabels with
      | .blossom m => m.blossomData.any fun b =>
          (b.cycle.steps.map (fun (input, _) => input.1.val)).count 0 == 2
      | _ => false) = true := by decide +kernel
  cases hs : Forest.search Table.sem freshLabels with
  | exhausted es => simp [hs] at hc
  | augment m => simp [hs] at hc
  | blossom m =>
    obtain ⟨b, hb, hbl, _, _⟩ := Forest.search_blossom_correct Table.sem freshLabels
      fresh_edge fresh_valid fresh_even hs
    have ht := Forest.search_trace Table.sem freshLabels fresh_edge
    rw [hs] at ht
    refine ⟨b, hb, hbl, ?_, ht.blossom_times_nodup hb⟩
    simpa only [hs, hb, Option.any_some, beq_iff_eq] using hc

end CslibFrontierTests.EdgeCSPBlossomCopies
