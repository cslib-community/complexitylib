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

-- Boundary regimes: Q = 0, r = 1, r = 0 (with Q > 0 triggering r ^ Q = 0 fallback), E = 0, C = 0,
-- radix-r candidate codec round-trips, out-of-range digit clamping, and `clearedPartialCollision`.
example :
    (decodeLabelWord 3 0 17 = [] ∧
      decodeLabelWord 1 4 29 = [0, 0, 0, 0] ∧
      streamBestSlotLabel 2 3 0 4 [(0, 1)] ([none, none], [none]) (false, 0) = [0, 0, 0] ∧
      clearedJointScore 0 2 3 4 [] [] [] = 0 ∧
      clearedJointScore 3 2 2 0 [(0, 1)] [some [1, 0], none, none] [none] =
        clearedGroupPotential 3 2 2 [some [1, 0], none, none] * (4 ^ 2 * 1) ∧
      scoreDenom 0 0 2 3 0 = 81 * 1 * 3 * 1) ∧
    (decodeLabelWord 3 3 19 = [1, 0, 2] ∧
      Nat.ofDigits 3 (decodeLabelWord 3 3 19) = 19 ∧
      ((List.range 9).map fun j => Nat.ofDigits 3 (decodeLabelWord 3 2 j)) = List.range 9 ∧
      (List.ofFn fun j : Fin (3 ^ 2) =>
        scheduleToWord (wordToSchedule (by decide : 1 ≤ 3) 2 (decodeLabelWord 3 2 j.val))) =
      (List.ofFn fun j : Fin (3 ^ 2) =>
        scheduleToWord ((finFunctionFinEquiv (m := 3) (n := 2)).symm j))) ∧
    scheduleToWord (wordToSchedule (by decide : 1 ≤ 3) 3 [2, 7, 1]) = [2, 0, 1] ∧
    (clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 2 2 = 4 ∧
      clearedPartialCollision 4 [some [1, 0], some [1, 0], none] 0 1 = 4 ∧
      clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 0 1 = 0 ∧
      clearedPartialCollision 4 [some [1, 0], some [1, 1], none] 0 2 = 1) := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, ?_⟩, by decide, by decide⟩
  congr 1; funext j; rw [wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm]

-- Concrete 2-variable, 2-factor hypergraph on r = 2, Q = 2: exact rational bridge check.
private def testEdge : Fin 3 → Fin 2 × Fin 2
  | ⟨0, _⟩ => (0, 0) | ⟨1, _⟩ => (0, 1) | ⟨2, _⟩ => (1, 0)
private def testVars : Fin 2 → Option (Fin 2 → Fin 2) | ⟨0, _⟩ => some ![0, 1] | ⟨1, _⟩ => none
private def testFacs : Fin 2 → Option (Fin 2 → Fin 2) | ⟨0, _⟩ => some ![1, 0] | ⟨1, _⟩ => none

example :
    edgesOfFin testEdge = [(0, 0), (0, 1), (1, 0)] ∧
    partialScheduleListOfFin testVars = [some [0, 1], none] ∧
    normalizedPartialScore testEdge testVars testFacs 4 = 51 / 64 ∧
    (decodeLabelWord 2 2 1 = [1, 0] ∧ decodeLabelWord 2 2 2 = [0, 1]) ∧
    (let scheds := (partialScheduleListOfFin testVars, partialScheduleListOfFin testFacs);
      candidateSlotScore 2 2 2 4 (edgesOfFin testEdge) scheds (false, 1) 1 <
        candidateSlotScore 2 2 2 4 (edgesOfFin testEdge) scheds (false, 1) 2) ∧
    (let emptyScheds := ([none, none], [none, none]);
      candidateSlotScore 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) 0 =
        candidateSlotScore 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) 3 ∧
        streamBestSlotLabel 2 2 2 4 [(0, 0), (1, 1)] emptyScheds (false, 0) = [0, 0]) ∧
    bestVariableLabel testEdge testVars testFacs 4 ⟨1, by decide⟩
      (candidateScheduleList (by decide : 1 ≤ 2) 2) = some ![1, 0] ∧
    bestFactorLabel testEdge testVars testFacs 4 ⟨1, by decide⟩
      (candidateScheduleList (by decide : 1 ≤ 2) 2) = some ![0, 0] := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, by decide, ?_, ?_⟩
  · rw [normalizedPartialScore_eq_clearedJointScore_div (by decide) testEdge testVars testFacs 4,
      show clearedJointScore 2 2 2 4 (edgesOfFin testEdge)
        (partialScheduleListOfFin testVars) (partialScheduleListOfFin testFacs) = 1224 by decide,
      show scoreDenom 3 2 2 2 4 = 1536 by decide]; norm_num
  · rw [← streamBestSlotLabel_false_eq_bestVariableLabel (by decide) testEdge testVars testFacs 4
      ⟨1, by decide⟩, Option.some.injEq]
    apply scheduleToWord_inj (by decide : 1 ≤ 2)
    rw [scheduleToWord_wordToSchedule (by decide) (length_streamBestSlotLabel ..)
      (fun _ hx => mem_streamBestSlotLabel_lt (by decide) _ _ _ _ _ _ hx)]; decide
  · rw [← streamBestSlotLabel_true_eq_bestFactorLabel (by decide) testEdge testVars testFacs 4
      ⟨1, by decide⟩, Option.some.injEq]
    apply scheduleToWord_inj (by decide : 1 ≤ 2)
    rw [scheduleToWord_wordToSchedule (by decide) (length_streamBestSlotLabel ..)
      (fun _ hx => mem_streamBestSlotLabel_lt (by decide) _ _ _ _ _ _ hx)]; decide

-- Concrete all-prefix live-state bit-length bound check across j = 0 .. 4, plus compositional
-- fun_prop and polynomial-space checks.
example :
    (∀ j ≤ 2 ^ 2,
      (encPair encNat encSlotSelectAcc
        (IndexFold.run selectSlotStep j (((2, 2), (2, 4), [(0, 0), (0, 1)]),
          ((false, 1), (([some [0, 1], none], [none]), none))))).length ≤
        2 * (encStreamSlotIn (((2, 2), (2, 4), [(0, 0), (0, 1)]),
          ((false, 1), ([some [0, 1], none], [none])))).length + 96) ∧
    ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => decodeLabelWord (p.1.1 + 1) p.1.2 p.2)
      (encPair (encPair encNat encUnary) encNat) (encList encNat) ∧
    ComputableInPolyTime (fun p : ((Bool × ℕ) × Option (List ℕ)) ×
        (List (Option (List ℕ)) × List (Option (List ℕ))) =>
        readSlotSchedule p.1.1 (updateSlotSchedules p.1.1 p.1.2 p.2))
      (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
        encPartialSchedules) (encOption (encList encNat)) ∧
    ComputableInPolySpace (fun p : StreamSlotIn × ℕ =>
        streamBestSlotLabel p.1.1.1.1 p.1.1.1.2 p.1.1.2.1.1 p.1.1.2.1.2 p.1.1.2.2 p.1.2.2 p.1.2.1)
      (encPair encStreamSlotIn encNat) (encList encNat) :=
  ⟨fun _ hj => (length_encSlotSelectState_run_le 2 2 2 4 [(0, 0), (0, 1)]
     ([some [0, 1], none], [none]) (false, 1) hj).trans (by
       simp only [Nat.add_assoc]; exact Nat.add_le_add_left (by decide) _),
   by fun_prop,
   by fun_prop,
   computableInPolySpace_streamBestSlotLabel.comp
     (.of_polyTime (ComputableInPolyTime.fst encStreamSlotIn encNat))⟩

end ComplexityTests.GreedySlotScore
