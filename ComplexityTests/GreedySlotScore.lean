/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.GreedySlotScore
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.NormNum

/-!
# Concrete tests for greedy slot-score arithmetic and streaming candidate selection
-/

namespace ComplexityTests.GreedySlotScore

open Finset Cslib.BalancedSchedules Cslib.GenericRAM Turing.MultiTapeTM

-- Boundary regimes: Q = 0, r = 1, r = 0 (with Q > 0 triggering r ^ Q = 0 fallback), E = 0, C = 0.
example : decodeLabelWord 3 0 17 = [] := rfl
example : decodeLabelWord 1 4 29 = [0, 0, 0, 0] := by decide
example : streamBestSlotLabel 2 3 0 4 [(0, 1)] ([none, none], [none]) (false, 0) = [0, 0, 0] := by
  decide
example : clearedJointScore 0 2 3 4 [] [] [] = 0 := by decide
example : clearedJointScore 3 2 2 0 [(0, 1)] [some [1, 0], none, none] [none] =
    clearedGroupPotential 3 2 2 [some [1, 0], none, none] * (4 ^ 2 * 1) := by decide
example : scoreDenom 0 0 2 3 0 = 81 * 1 * 3 * 1 := by decide

-- Radix-r candidate codec round-trips and full r ^ Q = 9 bijection at r = 3, Q = 2.
example : decodeLabelWord 3 3 19 = [1, 0, 2] := by decide
example : Nat.ofDigits 3 (decodeLabelWord 3 3 19) = 19 := by decide
example : ((List.range 9).map fun j => Nat.ofDigits 3 (decodeLabelWord 3 2 j)) =
    List.range 9 := by decide
example : (List.ofFn fun j : Fin (3 ^ 2) =>
    scheduleToWord (wordToSchedule (by decide : 1 ≤ 3) 2 (decodeLabelWord 3 2 j.val))) =
    (List.ofFn fun j : Fin (3 ^ 2) =>
      scheduleToWord ((finFunctionFinEquiv (m := 3) (n := 2)).symm j)) := by
  congr 1; funext j; rw [wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm]

-- Out-of-range digit clamping in wordToSchedule defaults digits ≥ r to 0.
example : scheduleToWord (wordToSchedule (by decide : 1 ≤ 3) 3 [2, 7, 1]) = [2, 0, 1] := by decide

-- Concrete clearedPartialCollision cases: diagonal, matching, distinct, and unassigned.
example : clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 2 2 = 4 := rfl
example : clearedPartialCollision 4 [some [1, 0], some [1, 0], none] 0 1 = 4 := by decide
example : clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 0 1 = 0 := by decide
example : clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 0 2 = 1 := by decide

-- Concrete 2-variable, 2-factor hypergraph on r = 2, Q = 2: exact rational bridge check.
private def testEdge : Fin 3 → Fin 2 × Fin 2
  | ⟨0, _⟩ => (0, 0) | ⟨1, _⟩ => (0, 1) | ⟨2, _⟩ => (1, 0)
private def testVars : Fin 2 → Option (Fin 2 → Fin 2) | ⟨0, _⟩ => some ![0, 1] | ⟨1, _⟩ => none
private def testFacs : Fin 2 → Option (Fin 2 → Fin 2) | ⟨0, _⟩ => some ![1, 0] | ⟨1, _⟩ => none

example : edgesOfFin testEdge = [(0, 0), (0, 1), (1, 0)] := by decide
example : partialScheduleListOfFin testVars = [some [0, 1], none] := by decide
example : normalizedPartialScore testEdge testVars testFacs 4 = 51 / 64 := by
  rw [normalizedPartialScore_eq_clearedJointScore_div (by decide) testEdge testVars testFacs 4,
    show clearedJointScore 2 2 2 4 (edgesOfFin testEdge)
      (partialScheduleListOfFin testVars) (partialScheduleListOfFin testFacs) = 1224 by decide,
    show scoreDenom 3 2 2 2 4 = 1536 by decide]; norm_num

-- Strictly better candidate reduces clearedJointScore; symmetric slot breaks ties by index 0.
example : decodeLabelWord 2 2 1 = [1, 0] ∧ decodeLabelWord 2 2 2 = [0, 1] := by decide
example : let scheds := (partialScheduleListOfFin testVars, partialScheduleListOfFin testFacs)
    candidateSlotScore 2 2 2 4 (edgesOfFin testEdge) scheds (false, 1) 1 <
      candidateSlotScore 2 2 2 4 (edgesOfFin testEdge) scheds (false, 1) 2 := by decide
example : let emptyScheds := ([none, none], [none, none])
    candidateSlotScore 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) 0 =
      candidateSlotScore 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) 3 ∧
      streamBestSlotLabel 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) = [0, 0] := by decide

-- Concrete evaluation of bestVariableLabel and bestFactorLabel via streamBestSlotLabel bridges.
example : bestVariableLabel testEdge testVars testFacs 4 ⟨1, by decide⟩
    (candidateScheduleList (by decide : 1 ≤ 2) 2) = some ![1, 0] := by
  rw [← streamBestSlotLabel_false_eq_bestVariableLabel (by decide) testEdge testVars testFacs 4
    ⟨1, by decide⟩, Option.some.injEq]
  apply scheduleToWord_inj (by decide : 1 ≤ 2)
  rw [scheduleToWord_wordToSchedule (by decide) (length_streamBestSlotLabel ..)
    (fun _ hx => mem_streamBestSlotLabel_lt (by decide) _ _ _ _ _ _ hx)]; decide

example : bestFactorLabel testEdge testVars testFacs 4 ⟨1, by decide⟩
    (candidateScheduleList (by decide : 1 ≤ 2) 2) = some ![0, 0] := by
  rw [← streamBestSlotLabel_true_eq_bestFactorLabel (by decide) testEdge testVars testFacs 4
    ⟨1, by decide⟩, Option.some.injEq]
  apply scheduleToWord_inj (by decide : 1 ≤ 2)
  rw [scheduleToWord_wordToSchedule (by decide) (length_streamBestSlotLabel ..)
    (fun _ hx => mem_streamBestSlotLabel_lt (by decide) _ _ _ _ _ _ hx)]; decide

-- Concrete all-prefix live-state bit-length bound check across j = 0 .. 4.
example : ∀ j ≤ 2 ^ 2,
    (encPair encNat encSlotSelectAcc
      (IndexFold.run selectSlotStep j (((2, 2), (2, 4), [(0, 0), (0, 1)]),
        ((false, 1), (([some [0, 1], none], [none]), none))))).length ≤
      2 * (encStreamSlotIn (((2, 2), (2, 4), [(0, 0), (0, 1)]),
        ((false, 1), ([some [0, 1], none], [none])))).length + 96 :=
  fun _ hj => (length_encSlotSelectState_run_le 2 2 2 4 [(0, 0), (0, 1)]
    ([some [0, 1], none], [none]) (false, 1) hj).trans (by
      simp only [Nat.add_assoc]; exact Nat.add_le_add_left (by decide) _)

-- Compositional fun_prop and polynomial-space checks on nontrivial expressions.
example : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => decodeLabelWord (p.1.1 + 1) p.1.2 p.2)
    (encPair (encPair encNat encUnary) encNat) (encList encNat) := by fun_prop
example : ComputableInPolyTime (fun p : ((Bool × ℕ) × Option (List ℕ)) ×
      (List (Option (List ℕ)) × List (Option (List ℕ))) =>
      readSlotSchedule p.1.1 (updateSlotSchedules p.1.1 p.1.2 p.2))
    (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
      encPartialSchedules) (encOption (encList encNat)) := by fun_prop
example : ComputableInPolySpace (fun p : StreamSlotIn × ℕ =>
      streamBestSlotLabel p.1.1.1.1 p.1.1.1.2 p.1.1.2.1.1 p.1.1.2.1.2 p.1.1.2.2 p.1.2.2 p.1.2.1)
    (encPair encStreamSlotIn encNat) (encList encNat) :=
  computableInPolySpace_streamBestSlotLabel.comp
    (.of_polyTime (ComputableInPolyTime.fst encStreamSlotIn encNat))

end ComplexityTests.GreedySlotScore
