/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Blossom.Optimality
import Mathlib.Tactic.FinCases

/-! A nonempty outside prefix changes an original constraint before the blossom is lifted.
The original two defects disappear; the resulting outside values differ from the reference. -/

namespace CslibFrontierTests.EdgeCSPBlossomLifting

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.DAG
open Cslib.Logic.PL.CSP.Blossom

private def starTable : Table :=
  ⟨3, [[false, false, false], [true, true, false], [true, false, true]]⟩
private def equalTable : Table := ⟨2, [[false, false], [true, true]]⟩
private def falseTable : Table := ⟨1, [[false]]⟩
private abbrev x₀ : ℕ := 2 ^ 100
private abbrev x₁ : ℕ := 2 ^ 200
private abbrev x₂ : ℕ := 2 ^ 250
private abbrev y : ℕ := 2 ^ 120
private abbrev csp : CSP Table ℕ :=
  [(starTable, [x₀, x₁, x₂]), (equalTable, [x₁, x₂]),
    (equalTable, [x₀, y]), (falseTable, [y])]
private def labels : OccurrenceLabeling csp Bool :=
  fun o => (o.1.val == 0 && o.2.val < 2) || o.1.val == 2
private abbrev cp (j : Fin 3) : Occurrence csp := ⟨0, j⟩
private abbrev dp (j : Fin 2) : Occurrence csp := ⟨1, j⟩
private abbrev ep (j : Fin 2) : Occurrence csp := ⟨2, j⟩
private def cycle : Walk csp := ⟨x₁, [(dp 0, dp 1), (cp 2, cp 1)]⟩
private def outside : Walk csp := ⟨y, [(ep 1, ep 0)]⟩
private def graph : DAG csp := blossomDAG cycle [1, 0] 1
private def rank : Node csp → ℕ
  | .inl v => if v == x₁ then 0 else 2
  | .inr c => if c.1.val == 0 then 1 else 3

private theorem edge : EdgeInstance csp := by unfold EdgeInstance; decide +kernel
private theorem valid : ValidLabeling Table.sem labels := by unfold ValidLabeling; decide
private theorem even : EdgeInstance.EvenConstraints Table.sem csp := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

private theorem graph_isFDAG : graph.IsFDAG Table.sem labels := by
  refine ⟨valid, blossomDAG_supported _ _ _, ?_, ?_, ⟨?_, ⟨rank, ?_⟩⟩, ?_, ?_⟩
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy, cp, dp, Occurrence.var]
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy, cp, dp, Occurrence.var]
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy]
  · intro x z hxz
    rcases hxz with ⟨a, ha, rfl, rfl⟩ | ⟨c, hc, d, hd, hlt, rfl, rfl⟩
    · simp only [graph, blossomDAG, blossomArcs, cycle, List.mem_toFinset,
        List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide +kernel
    · simp only [graph, blossomDAG, blossomArcs, cycle, List.map_cons, List.map_nil,
        List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hc hd
      rcases hc with rfl | rfl | rfl | rfl <;>
        rcases hd with rfl | rfl | rfl | rfl <;> norm_num [Arc.copy] at hlt <;> decide
  · intro a ha b hb hai hab
    simp only [graph, blossomDAG, blossomArcs, cycle, List.mem_toFinset,
      List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl | rfl <;>
      norm_num at hai <;> norm_num [Arc.copy, cp, dp] at hab <;>
      unfold ValidLabeling <;> decide +kernel
  · simp [graph, blossomDAG, blossomArcs, cycle, Arc.copy]

private theorem blossom : cycle.IsBlossom Table.sem labels := by
  refine ⟨by simp only [cycle, Walk.IsWalk, Walk.Linked]; decide +kernel,
    by decide, by decide, by decide +kernel,
    by simp only [cycle, Walk.InternallyConsistent]; decide +kernel,
    [1, 0], 1, by unfold Walk.DistinctCopies Walk.copies; decide, by decide, by decide, ?_⟩
  have hi : instDecidableEqNat = Classical.decEq ℕ := Subsingleton.elim _ _
  exact congrArg (fun d => @blossomDAG Table ℕ csp d cycle [1, 0] 1) hi ▸ graph_isFDAG

-- Lemma 40 now follows from the repaired copied-step certificate.
example : ValidLabeling Table.sem ((cycle.take 1).flip labels) := by
  exact blossomDAG_valid_take graph_isFDAG blossom.1
    (by unfold Walk.DistinctCopies Walk.copies; decide) even 1

example : defects labels = {x₁, y} ∧ (outside.flip labels) (ep 0) = false ∧
    labels (ep 0) = true := by decide +kernel

-- The first feasible exit is genuinely after the nonempty outside prefix.
example : (firstExit labels cycle outside).map Exit.length = some 1 := by decide +kernel

private theorem lifted : ∃ g, liftPrefix labels cycle outside = some g ∧
    ValidLabeling Table.sem g ∧ (defects g).card + 2 = (defects labels).card := by
  apply liftPrefix_spec edge blossom even
  · simp only [outside, Walk.IsFPrefix, Walk.IsWalk, Walk.Linked, Walk.InternallyConsistent,
      Walk.PrefixValid]
    decide +kernel
  · exact Or.inr (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [outside, Walk.edges, Walk.edgesOf, List.flatMap_cons, List.flatMap_nil,
      List.mem_cons, List.not_mem_nil, or_false, List.append_nil]
    intro o ho
    rcases ho with rfl | rfl <;> decide +kernel
  · refine ⟨1, by decide, ?_⟩
    decide +kernel

-- The computed finite labels are all zero, so the lifted result is optimal and changes the
-- old outside values. The row and defect assertions exercise the actual constructor.
example : (liftPrefix labels cycle outside).map
    (fun g => (incidenceList csp).map g) = some (List.replicate 8 false) := by
  decide +kernel

example : ∃ g, liftPrefix labels cycle outside = some g ∧ IsOptimalLabeling Table.sem g ∧
    g (ep 0) ≠ labels (ep 0) := by
  obtain ⟨g, hg, hv, hn⟩ := lifted
  have hc : (defects labels).card = 2 := by decide +kernel
  have hz : (defects g).card = 0 := by omega
  refine ⟨g, hg, ⟨hv, fun h _ => by rw [hz]; omega⟩, ?_⟩
  have hh : (liftPrefix labels cycle outside).map (fun h => h (ep 0)) = some false := by
    decide +kernel
  rw [hg] at hh
  have he := Option.some.inj hh
  change g (ep 0) = false at he
  change g (ep 0) ≠ true
  rw [he]
  decide

private abbrev contracted : CSP Table ℕ := contract labels (internal cycle)
private def comparison : OccurrenceLabeling contracted Bool := fun o =>
  (o.1.val == 0 && o.2.val == 1) || (o.1.val == 4 && o.2.val == 0)
private theorem comparison_valid : ValidLabeling Table.sem comparison := by
  unfold ValidLabeling
  decide +kernel

-- This actual returned optimum changes the old outside equality row from 11 to 00. Both
-- connector occurrences at the central relation are genuinely one-hot, and all edges agree.
example : IsOptimalLabeling Table.sem comparison ∧
    comparison (oldPort labels (internal cycle) (ep 0) (by decide +kernel)) = false ∧
    reference labels (internal cycle)
      (oldPort labels (internal cycle) (ep 0) (by decide +kernel)) = true := by
  have hz : (defects comparison).card = 0 := by decide +kernel
  exact ⟨⟨comparison_valid, fun g _ => by rw [hz]; omega⟩, by decide +kernel, by decide +kernel⟩

-- This tests the full Lemma 31 comparison-to-walk construction followed by the whole-instance
-- lifting constructor. The first connector lies after a nonempty outside prefix.
example : (liftComparison labels cycle comparison).map
    (fun g => (incidenceList csp).map g) = some (List.replicate 8 false) := by
  decide +kernel

example : ∃ g, liftComparison labels cycle comparison = some g ∧
    IsOptimalLabeling Table.sem g ∧ g (ep 0) ≠ labels (ep 0) := by
  obtain ⟨g, hg, hv, hc⟩ := liftComparison_spec edge blossom valid even comparison comparison_valid
    (by decide +kernel)
  have href : (defects labels).card = 2 := by decide +kernel
  have hz : (defects g).card = 0 := by omega
  refine ⟨g, hg, ⟨hv, fun h _ => by rw [hz]; omega⟩, ?_⟩
  have hh : (liftComparison labels cycle comparison).map (fun h => h (ep 0)) = some false := by
    decide +kernel
  rw [hg] at hh
  have he := Option.some.inj hh
  change g (ep 0) = false at he
  change g (ep 0) ≠ true
  rw [he]
  decide

private def forwardFromZero : Option (OccurrenceLabeling contracted Bool) := do
  let p ← EdgeInstance.augmentingWalk Table.sem labels (fun _ => false) cycle.start
  projectAugmentation labels cycle p

-- The reverse optimality argument also has an executable forward construction. Its actual
-- central row indicates the touched original constraint containing the first internal port.
example : forwardFromZero.map (fun g => (incidenceList contracted).map g) =
    some [false, true, false, false, false, false, true, false] := by decide +kernel

end CslibFrontierTests.EdgeCSPBlossomLifting
