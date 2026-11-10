/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Blossom
import Mathlib.Tactic.FinCases

/-! Actual returned events: odd parity, both LCAs, nonempty preparation and repeated copies. -/

namespace CslibFrontierTests.EdgeCSPForestEvents

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest
open Cslib.Logic.PL.CSP.DAG

private def binarySem (odd : Bool) : List Bool → Bool
  | [a, b] => if odd then a != b else a == b
  | _ => false

private abbrev wide : CSP Bool ℕ :=
  [(false, [2 ^ 100, 2 ^ 200]), (false, [2 ^ 100, 2 ^ 200])]
private def wideLabels : wide.OccurrenceLabeling Bool := fun o => o.1.val == 1
private abbrev widePort (j : Fin 2) : wide.Occurrence := ⟨0, j⟩
private def wideMeeting : Meeting wide :=
  ⟨[2 ^ 100, 2 ^ 200], [], ⟨widePort 0, []⟩, widePort 1⟩
private theorem wide_edge : EdgeInstance wide := by unfold EdgeInstance; decide
private theorem wide_valid : ValidLabeling binarySem wideLabels := by unfold ValidLabeling; decide
private theorem wide_even : EdgeInstance.EvenConstraints binarySem wide := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem wide_run : search binarySem wideLabels = .augment wideMeeting := by
  decide +kernel

-- Neither endpoint label contributes to a variable-universe scan or termination bound.
example : ValidLabeling binarySem (wideMeeting.walk.flip wideLabels) ∧
    (defects (wideMeeting.walk.flip wideLabels)).card = 0 := by
  have hh := search_augment_correct binarySem wideLabels wide_edge wide_valid wide_even wide_run
  refine ⟨hh.2.1, ?_⟩
  have hc : (defects wideLabels).card = 2 := by decide
  omega

private abbrev triangle : CSP Bool ℕ :=
  [(true, [0, 1]), (false, [1, 2]), (false, [2, 0])]
private def triangleLabels : triangle.OccurrenceLabeling Bool :=
  fun o => o.1.val == 0 && o.2.val == 0
private abbrev tp (i : Fin 3) (j : Fin 2) : triangle.Occurrence :=
  ⟨i, ⟨j.val, by fin_cases i <;> exact j.isLt⟩⟩
private def triangleMeeting : Meeting triangle :=
  ⟨[0], [⟨tp 1 0, [tp 1 1]⟩, ⟨tp 0 0, [tp 0 1]⟩], ⟨tp 2 0, []⟩, tp 2 1⟩
private def triangleData : BlossomData triangle :=
  ⟨.inl 0, ⟨0, []⟩, triangleMeeting.walk, [0, 1, 2], 3, none, none⟩
private theorem triangle_edge : EdgeInstance triangle := by unfold EdgeInstance; decide
private theorem triangle_valid : ValidLabeling binarySem triangleLabels := by
  unfold ValidLabeling
  decide
private theorem triangle_even : EdgeInstance.EvenConstraints binarySem triangle := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem triangle_run : search binarySem triangleLabels = .blossom triangleMeeting := by
  decide +kernel
private theorem triangle_data : triangleMeeting.blossomData = some triangleData := by
  rfl

example : (triangleMeeting.left.walk.take
    ((triangleMeeting.commonNodes.length - 1) / 2)).steps = [] := by
  have ht := search_trace binarySem triangleLabels triangle_edge
  rw [triangle_run] at ht
  exact ht.variable_prepare_empty triangle_edge triangle_valid (v := 0) (by decide)

example : triangleData.cycle.IsBlossom binarySem (triangleData.prepare.flip triangleLabels) ∧
    ValidLabeling binarySem (triangleData.prepare.flip triangleLabels) ∧
    (defects (triangleData.prepare.flip triangleLabels)).card = (defects triangleLabels).card := by
  obtain ⟨b, hb, hc, hv, hn⟩ := search_blossom_correct binarySem triangleLabels
    triangle_edge triangle_valid triangle_even triangle_run
  cases Option.some.inj (hb.symm.trans triangle_data)
  exact ⟨hc, hv, hn⟩

-- The first relation has odd common parity; the source does not require even-weight tuples.
example : binarySem true [true, false] = true ∧ binarySem true [false, false] = false := by decide

private def starSem (r : Fin 3) : List Bool → Bool
  | [a, b, c] => r == 0 &&
      ([[false, false, false], [true, true, false], [true, false, true]].contains [a, b, c])
  | [a, b] => r == 1 && a == b
  | [a] => r == 2 && a
  | _ => false
private abbrev star : CSP (Fin 3) ℕ := [(0, [0, 1, 2]), (1, [1, 2]), (2, [0])]
private def starLabels : star.OccurrenceLabeling Bool := fun o => o.1.val == 2
private abbrev sp (j : Fin 3) : star.Occurrence := ⟨0, j⟩
private abbrev sb (j : Fin 2) : star.Occurrence := ⟨1, j⟩
private def starMeeting : Meeting star := ⟨[0], [⟨sp 0, [sp 1, sp 2]⟩], ⟨sb 0, []⟩, sb 1⟩
private def starData : BlossomData star :=
  ⟨.inr (0, 0), ⟨0, [(sp 0, sp 1)]⟩, ⟨1, [(sb 0, sb 1), (sp 2, sp 1)]⟩,
    [1, 0], 1, some (sp 1), some (sp 2)⟩
private theorem star_edge : EdgeInstance star := by unfold EdgeInstance; decide
private theorem star_valid : ValidLabeling starSem starLabels := by unfold ValidLabeling; decide
private theorem star_even : EdgeInstance.EvenConstraints starSem star := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem star_run : search starSem starLabels = .blossom starMeeting := by decide +kernel
private theorem star_data : starMeeting.blossomData = some starData := by rfl

-- This test requires the complete prepared f-DAG, including feasibility after the
-- final child-port pair. Merely closing the cycle or validating its final flip is insufficient.
example : (blossomDAG starData.cycle starData.times starData.pivot).IsFDAG starSem
    (starData.prepare.flip starLabels) := by
  have ht := search_trace starSem starLabels star_edge
  rw [star_run] at ht
  exact ht.blossom_isFDAG star_edge star_valid star_even star_data

example : starData.cycle.IsBlossom starSem (starData.prepare.flip starLabels) ∧
    Inconsistent (starData.prepare.flip starLabels) 1 := by
  obtain ⟨b, hb, hc, _, _⟩ := search_blossom_correct starSem starLabels
    star_edge star_valid star_even star_run
  cases Option.some.inj (hb.symm.trans star_data)
  exact ⟨hc, hc.2.2.2.1⟩

private abbrev extended : CSP (Fin 3) ℕ :=
  [(1, [3, 0]), (0, [0, 1, 2]), (1, [1, 2]), (2, [3])]
private def extendedLabels : extended.OccurrenceLabeling Bool := fun o => o.1.val == 3
private abbrev ep0 (j : Fin 2) : extended.Occurrence := ⟨0, j⟩
private abbrev ep1 (j : Fin 3) : extended.Occurrence := ⟨1, j⟩
private abbrev ep2 (j : Fin 2) : extended.Occurrence := ⟨2, j⟩
private def extendedMeeting : Meeting extended :=
  ⟨[3], [⟨ep1 0, [ep1 1, ep1 2]⟩, ⟨ep0 0, [ep0 1]⟩], ⟨ep2 0, []⟩, ep2 1⟩
private def extendedData : BlossomData extended :=
  ⟨.inr (1, 1), ⟨3, [(ep0 0, ep0 1), (ep1 0, ep1 1)]⟩,
    ⟨1, [(ep2 0, ep2 1), (ep1 2, ep1 1)]⟩, [2, 1], 1, some (ep1 1), some (ep1 2)⟩
private theorem extended_edge : EdgeInstance extended := by unfold EdgeInstance; decide
private theorem extended_valid : ValidLabeling starSem extendedLabels := by
  unfold ValidLabeling
  decide
private theorem extended_even : EdgeInstance.EvenConstraints starSem extended := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem extended_run : search starSem extendedLabels = .blossom extendedMeeting := by
  decide +kernel
private theorem extended_data : extendedMeeting.blossomData = some extendedData := by rfl

-- The root path contains a step before the LCA step; preparation must flip both.
example : extendedData.prepare.steps.length = 2 ∧
    extendedData.cycle.IsBlossom starSem (extendedData.prepare.flip extendedLabels) ∧
    ValidLabeling starSem (extendedData.prepare.flip extendedLabels) ∧
    (defects (extendedData.prepare.flip extendedLabels)).card = (defects extendedLabels).card := by
  obtain ⟨b, hb, hc, hv, hn⟩ := search_blossom_correct starSem extendedLabels
    extended_edge extended_valid extended_even extended_run
  cases Option.some.inj (hb.symm.trans extended_data)
  exact ⟨rfl, hc, hv, hn⟩

private def repeatedSem (r : Fin 4) : List Bool → Bool
  | [a, b, c, d] => r == 0 && a == b && c == d
  | [a, b] => r == 1 && a == b
  | [a] => (r == 2 || r == 3) && a
  | _ => false
private abbrev repeated : CSP (Fin 4) ℕ :=
  [(0, [0, 1, 2, 3]), (1, [1, 2]), (2, [0]), (3, [3])]
private def repeatedLabels : repeated.OccurrenceLabeling Bool :=
  fun o => o.1.val == 2 || o.1.val == 3
private abbrev rp0 (j : Fin 4) : repeated.Occurrence := ⟨0, j⟩
private abbrev rp1 (j : Fin 2) : repeated.Occurrence := ⟨1, j⟩
private def repeatedMeeting : Meeting repeated :=
  ⟨[0, 3], [⟨rp0 3, [rp0 2]⟩, ⟨rp0 0, [rp0 1]⟩], ⟨rp1 0, []⟩, rp1 1⟩
private theorem repeated_edge : EdgeInstance repeated := by unfold EdgeInstance; decide
private theorem repeated_valid : ValidLabeling repeatedSem repeatedLabels := by
  unfold ValidLabeling
  decide
private theorem repeated_even : EdgeInstance.EvenConstraints repeatedSem repeated := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }
private theorem repeated_run : search repeatedSem repeatedLabels = .augment repeatedMeeting := by
  decide +kernel

-- Original constraint zero occurs twice on the returned path, at times zero and one.
-- These copies must remain distinct for Corollary 36 and the no-shortcut conditions.
example : repeatedMeeting.walk.steps.map (fun s => s.1.1.val) = [0, 1, 0] ∧
    repeatedMeeting.left.times = [0] ∧ repeatedMeeting.right.times = [1] ∧
    repeatedMeeting.copy = (1, 2) := by decide

example : repeatedMeeting.walk.IsAugmenting repeatedSem repeatedLabels ∧
    ValidLabeling repeatedSem (repeatedMeeting.walk.flip repeatedLabels) ∧
    (defects (repeatedMeeting.walk.flip repeatedLabels)).card = 0 := by
  have hh := search_augment_correct repeatedSem repeatedLabels
    repeated_edge repeated_valid repeated_even repeated_run
  refine ⟨hh.1, hh.2.1, ?_⟩
  have hc : (defects repeatedLabels).card = 2 := by decide
  omega

end CslibFrontierTests.EdgeCSPForestEvents
