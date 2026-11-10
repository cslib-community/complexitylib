/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Search
import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Invariant
import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Ancestry
import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.Frontier
import CslibFrontier.Algorithms.Lean.EdgeCSP.Forest.BlossomData
import Mathlib.Tactic.FinCases

/-! Executable forest runs, actual cycles, repeated original constraints and sparse labels. -/

namespace CslibFrontierTests.EdgeCSPForest

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest
open Cslib.Logic.PL.CSP.DAG

-- Equality depends on positional ports, not equality of relation symbols or variable names.
private abbrev opaqueNames : CSP (ℕ → Bool) (ℕ → Bool) :=
  [(fun _ => false, [fun _ => false, fun _ => true])]
private abbrev opaquePort (j : Fin 2) : opaqueNames.Occurrence := ⟨0, j⟩

example : (⟨opaquePort 0, [opaquePort 1]⟩ : Expansion opaqueNames) =
    ⟨opaquePort 0, [opaquePort 1]⟩ := by decide
example : (⟨opaquePort 0, []⟩ : Expansion opaqueNames) ≠ ⟨opaquePort 1, []⟩ := by decide
example : (ScanResult.continued [opaquePort 0]) ≠
    ScanResult.meeting [] (opaquePort 1) := by decide

private abbrev opaqueRelations : CSP (ℕ → Bool) ℕ := [(fun _ => false, [0, 1])]
private abbrev opaqueRelationPort (j : Fin 2) : opaqueRelations.Occurrence := ⟨0, j⟩
private abbrev opaqueMeeting : Meeting opaqueRelations :=
  ⟨[0], [], ⟨opaqueRelationPort 0, []⟩, opaqueRelationPort 1⟩

example : opaqueMeeting = opaqueMeeting := by decide
example : Result.augment opaqueMeeting ≠ Result.blossom opaqueMeeting := by decide

private def binarySem (odd : Bool) : List Bool → Bool
  | [a, b] => if odd then a != b else a == b
  | _ => false

private abbrev augmentInstance : CSP Bool ℕ :=
  [(false, [2 ^ 100, 2 ^ 200]), (false, [2 ^ 100, 2 ^ 200])]

private def augmentLabels : augmentInstance.OccurrenceLabeling Bool := fun o => o.1.val == 1

example : EdgeInstance augmentInstance := by unfold EdgeInstance; decide
example : ValidLabeling binarySem augmentLabels := by unfold ValidLabeling; decide
example : roots augmentLabels = [2 ^ 100, 2 ^ 200] := by decide

-- Sparse binary variable names have no influence on the clock or scan range.
example : (match search binarySem augmentLabels with
    | .augment m => decide (m.left.walk.start = 2 ^ 100 ∧ m.right.walk.start = 2 ^ 200 ∧
        m.walk.steps.length = 1 ∧ m.ancestor? = none)
    | _ => false) = true := by
  decide +kernel

example : (match search binarySem augmentLabels with
    | .augment m => decide (ValidLabeling binarySem (m.walk.flip augmentLabels) ∧
        (defects (m.walk.flip augmentLabels)).card = 0)
    | _ => false) = true := by
  decide +kernel

private abbrev triangle : CSP Bool ℕ :=
  [(true, [0, 1]), (false, [1, 2]), (false, [2, 0])]

private def triangleLabels : triangle.OccurrenceLabeling Bool :=
  fun o => o.1.val == 0 && o.2.val == 0

example : EdgeInstance triangle := by unfold EdgeInstance; decide
example : ValidLabeling binarySem triangleLabels := by unfold ValidLabeling; decide

-- A variable LCA produces the actual three-step cycle with no preparatory flip.
example : (match search binarySem triangleLabels with
    | .blossom m => match m.blossomData with
      | some b => decide (b.ancestor = .inl 0 ∧ b.prepare.steps = [] ∧
          b.cycle.start = 0 ∧ b.cycle.finish = 0 ∧ b.cycle.steps.length = 3 ∧
          b.times = [0, 1, 2] ∧ b.pivot = 3)
      | none => false
    | _ => false) = true := by
  decide +kernel

private def starSem (r : Fin 3) : List Bool → Bool
  | [a, b, c] => r == 0 &&
      ([[false, false, false], [true, true, false], [true, false, true]].contains [a, b, c])
  | [a, b] => r == 1 && a == b
  | [a] => r == 2 && a
  | _ => false

private abbrev star : CSP (Fin 3) ℕ := [(0, [0, 1, 2]), (1, [1, 2]), (2, [0])]
private def starLabels : star.OccurrenceLabeling Bool := fun o => o.1.val == 2

example : EdgeInstance star := by unfold EdgeInstance; decide
example : ValidLabeling starSem starLabels := by unfold ValidLabeling; decide

-- The common copied constraint is included in the preparatory flip, and the cycle's final
-- step joins its two actual child ports.
example : (match search starSem starLabels with
    | .blossom m => match m.blossomData with
      | some b => decide (b.ancestor = .inr (0, 0) ∧ b.prepare.steps.length = 1 ∧
          b.cycle.start = 1 ∧ b.cycle.finish = 1 ∧ b.cycle.steps.length = 2 ∧
          b.times = [1, 0] ∧ b.leftPort.isSome ∧ b.rightPort.isSome)
      | none => false
    | _ => false) = true := by
  decide +kernel

example : (match search starSem starLabels with
    | .blossom m => match m.blossomData with
      | some b => decide (ValidLabeling starSem (b.prepare.flip starLabels) ∧
          Inconsistent (b.prepare.flip starLabels) b.cycle.start)
      | none => false
    | _ => false) = true := by
  decide +kernel

private def repeatedSem (r : Fin 4) : List Bool → Bool
  | [a, b, c, d] => r == 0 && a == b && c == d
  | [a, b] => r == 1 && a == b
  | [a] => if r == 2 then a else r == 3 && !a
  | _ => false

private abbrev repeated : CSP (Fin 4) ℕ :=
  [(0, [0, 1, 2, 3]), (1, [1, 2]), (2, [0]), (3, [3])]
private def repeatedLabels : repeated.OccurrenceLabeling Bool := fun o => o.1.val == 2

private theorem repeated_edge : EdgeInstance repeated := by unfold EdgeInstance; decide
private theorem repeated_valid : ValidLabeling repeatedSem repeatedLabels := by
  unfold ValidLabeling
  decide

private theorem repeated_even : EdgeInstance.EvenConstraints repeatedSem repeated := by
  intro i
  fin_cases i <;> exact {
    isDeltaMatroid := { nonempty := by change ∃ t, _; decide, exchange := by decide }
    parity_eq := by decide }

-- The same original constraint is genuinely expanded at times zero and two. Copy nodes
-- remain distinct. One isolated inconsistency is not mistaken for an augmentation.
example : (match search repeatedSem repeatedLabels with
    | .exhausted es => decide (es.length = 5 ∧ es.used.length = 8 ∧
        ((es.arcs.filter fun a => a.occurrence.1.val == 0).map Arc.time).eraseDups = [2, 0])
    | _ => false) = true := by
  decide +kernel

-- Every completed DAG invariant, including the cross-copy no-shortcut condition, comes from
-- the fresh executable run rather than a hand-constructed graph hypothesis.
example : (search repeatedSem repeatedLabels).Logs
    (fun es => (es.toDAG (roots repeatedLabels)).IsFDAG repeatedSem repeatedLabels) :=
  search_completed_isFDAG _ _ repeated_edge repeated_valid

-- Source 4b ignores timestamp differences at the same ORIGINAL constraint.
private abbrev ra (j : Fin 4) : repeated.Occurrence := ⟨0, j⟩
private abbrev old : Log repeated := [⟨ra 0, [ra 1]⟩]
example : old.SameParent 1 0 := by decide
example : scan [0] old (ra 2) [] [ra 1] = .continued [] := by decide
example : ¬ old.SameParent 1 1 := by decide

private abbrev repeatedLog : Log repeated :=
  [⟨⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩, []⟩,
    ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, []⟩, ⟨ra 2, [ra 3]⟩,
    ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, [⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩]⟩,
    ⟨ra 0, [ra 1]⟩]

private theorem repeated_run : search repeatedSem repeatedLabels = .exhausted repeatedLog := by
  decide +kernel

example : ∀ o : repeated.Occurrence,
    repeatedLog.Visited (roots repeatedLabels) o.var → o ∈ repeatedLog.used :=
  search_exhausted_frontier repeatedSem repeatedLabels repeated_run

private theorem repeated_grown : Grown repeatedSem repeatedLabels (roots repeatedLabels)
    repeatedLog := by
  simpa only [repeated_run, Result.Logs] using search_grown repeatedSem repeatedLabels repeated_edge

-- The actual parent path to variable three revisits constraint zero at another timestamp.
example : (repeatedLog.ancestry 3).walk.steps.length = 3 ∧
    (repeatedLog.ancestry 3).times = [0, 1, 2] := by decide

example (n : ℕ) : ValidLabeling repeatedSem
    (((repeatedLog.ancestry 3).walk.take n).flip repeatedLabels) :=
  repeated_grown.ancestry_valid_take repeated_edge repeated_valid repeated_even (by decide) n

-- Positional reuse and a feasible cross-copy shortcut are rejected as distinct failures.
example : ¬ Grown repeatedSem repeatedLabels [0] ([⟨ra 0, []⟩, ⟨ra 0, [ra 1]⟩] : Log repeated) := by
  intro hg
  have hn := hg.used_nodup
  have hbad : ¬ (Log.used ([⟨ra 0, []⟩, ⟨ra 0, [ra 1]⟩] : Log repeated)).Nodup := by decide
  exact hbad hn

private abbrev sp (j : Fin 3) : star.Occurrence := ⟨0, j⟩
private abbrev shortcut : Log star := [⟨sp 2, []⟩, ⟨sp 0, [sp 1]⟩]

example : ¬ (shortcut.toDAG [0]).IsFDAG starSem starLabels := by
  intro h
  have hn := h.noShortcut (⟨sp 0, 0, true⟩ : Arc star) (by decide)
    (⟨sp 2, 1, true⟩ : Arc star) (by decide) rfl rfl (by decide)
  apply hn
  unfold ValidLabeling
  decide

private def pruneSem (r : Bool) : List Bool → Bool
  | [a, b, c] => !r &&
      ([[false, false, false], [true, true, false], [true, false, true]].contains [a, b, c])
  | [a] => a == r
  | _ => false

private abbrev pruneInstance : CSP Bool ℕ :=
  [(false, [0, 1, 2]), (true, [0]), (false, [1]), (true, [2])]
private def pruneLabels : pruneInstance.OccurrenceLabeling Bool :=
  fun o => o.1.val == 1 || o.1.val == 3
private abbrev pp (j : Fin 3) : pruneInstance.Occurrence := ⟨0, j⟩

example : EdgeInstance pruneInstance := by unfold EdgeInstance; decide
example : ValidLabeling pruneSem pruneLabels := by unfold ValidLabeling; decide

-- The terminal star copy has already acquired child one before meeting root two. The
-- moreover graph must remove that child: its exchange with the second input would be 011.
example : (match search pruneSem pruneLabels with
    | .augment m => decide (m.current.outputs = [pp 1] ∧
        (m.toDAG.arcs.filter fun a => a.copy == m.copy && !a.incoming).card = 1 ∧
        (m.prunedDAG.arcs.filter fun a => a.copy == m.copy && !a.incoming).card = 0)
    | _ => false) = true := by
  decide +kernel

example : ¬ ValidLabeling pruneSem (pairFlip pruneLabels (pp 2) (pp 1)) := by
  unfold ValidLabeling
  decide

-- An input incidence at an undiscovered variable is not a permitted frontier choice.
example : ¬ Grown repeatedSem repeatedLabels [0] ([⟨ra 2, []⟩] : Log repeated) := by
  intro hg
  cases hg with
  | cons _ hv => exact (by decide : ¬ Log.Visited [0] ([] : Log repeated) (ra 2).var) hv

-- An empty input has no roots and no expansions, even with an evaluator rejecting nullary
-- constraints. Validity is a separate hypothesis of the correctness theorem.
example : (match search (fun (_ : Unit) (_ : List Bool) => false)
      (F := ([] : CSP Unit ℕ)) (fun _ => false) with
    | .exhausted es => decide (es = [])
    | _ => false) = true := by
  decide +kernel

private abbrev rejected : CSP Unit ℕ := [((), [])]
example : ¬ ValidLabeling (fun _ _ => false) (F := rejected) (fun _ => false) := by
  unfold ValidLabeling
  decide

end CslibFrontierTests.EdgeCSPForest
