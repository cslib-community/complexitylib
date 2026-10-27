/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.GreedyLabelSchedule
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Concrete tests for runtime balanced label schedules
-/

namespace ComplexityTests.GreedyLabelSchedule

open Finset Cslib.BalancedSchedules Cslib.GenericRAM Turing.MultiTapeTM

-- Outer index decoding, capping, no-op on assigned/out-of-range slots, and Q=0/r=0/r=1/E=0 regimes.
example : slotOfIndex 3 2 1 = some (false, 1) ∧ slotOfIndex 3 2 4 = some (true, 1) ∧
    slotOfIndex 3 2 5 = none ∧ slotOfIndex 3 2 99 = none ∧
    pendingSlotOfState (0, (((2, 1, 2), (2, 4), [(0, 0)]), ([some [1, 0], none], [none]))) =
      none := by decide +kernel
example : greedySlotStepBody (0, (((2, 1, 2), (2, 4), [(0, 0)]), ([some [1, 0], none], [none]))) =
    (((2, 1, 2), (2, 4), [(0, 0)]), ([some [1, 0], none], [none])) := rfl
example : greedySlotStepBody (7, (((2, 1, 2), (2, 4), [(0, 0)]), ([some [1, 0], none], [none]))) =
    (((2, 1, 2), (2, 4), [(0, 0)]), ([some [1, 0], none], [none])) := rfl
example : constructBalancedSchedules 2 3 0 2 4 [(0, 1)] = ([[], []], [[], [], []]) ∧
    constructBalancedSchedules 2 2 2 0 4 [(0, 1)] = ([[0, 0], [0, 0]], [[0, 0], [0, 0]]) ∧
    constructBalancedSchedules 2 2 3 1 2 [(0, 0)] =
      ([[0, 0, 0], [0, 0, 0]], [[0, 0, 0], [0, 0, 0]]) ∧
    constructBalancedSchedules 2 3 2 3 4 [] =
      ([[0, 0], [1, 1]], [[0, 0], [0, 0], [0, 0]]) := by decide +kernel

-- Nontrivial 2-variable, 4-factor hypergraph with non-empty factors 0, 2 and empty factors 1, 3.
private def testEdges : List (ℕ × ℕ) := [(0, 0), (0, 1), (2, 0), (2, 1)]
private def testEdge : Fin 4 → Fin 4 × Fin 2
  | ⟨0, _⟩ => (0, 0) | ⟨1, _⟩ => (0, 1) | ⟨2, _⟩ => (2, 0) | ⟨3, _⟩ => (2, 1)

example : edgesOfFin testEdge = testEdges ∧
    normalizeEmptyFactorSchedules 2 testEdges [[1, 1], [1, 0], [0, 1], [1, 1]] =
      [[1, 1], [0, 0], [0, 1], [0, 0]] ∧
    greedySchedulePass 2 4 2 2 4 testEdges =
      ([some [0, 0], some [1, 1]], [some [0, 0], some [0, 0], some [1, 0], some [0, 0]]) ∧
    constructBalancedSchedules 2 4 2 2 4 testEdges =
      ([[0, 0], [1, 1]], [[0, 0], [0, 0], [1, 0], [0, 0]]) := by decide +kernel
-- Exact evaluation of greedyLabelPass and concrete occupancy bounds on testEdge.
example : (let slots : List (Fin 2 ⊕ Fin 4) :=
      (List.ofFn fun v : Fin 2 => Sum.inl v) ++ (List.ofFn fun f : Fin 4 => Sum.inr f)
    let res := greedyLabelPass testEdge 4 (candidateScheduleList (by decide : 1 ≤ 2) 2) slots
      (fun _ => none, fun _ => none)
    (partialScheduleListOfFin res.1, partialScheduleListOfFin res.2)) =
    ([some [0, 0], some [1, 1]], [some [0, 0], some [0, 0], some [1, 0], some [0, 0]]) := by
  rw [← greedySchedulePass_eq_greedyLabelPass (by decide : 1 ≤ 2) testEdge 4]
  change greedySchedulePass 2 4 2 2 4 testEdges = _; decide +kernel
example : let a := constructedVarSchedule (by decide : 1 ≤ 2) 2 4 2 4 (edgesOfFin testEdge)
    let d := constructedFactorSchedule (by decide : 1 ≤ 2) 2 4 2 4 (edgesOfFin testEdge)
    (∀ u : (Fin 2 → Fin 2) × (Fin 2 → Fin 2),
      occupancy (fun e => (a (testEdge e).2, d (testEdge e).1)) u ≤ 1) ∧
    (∀ t : Fin 2, ∀ g : Fin 2, occupancy (fun v => a v t) g ≤ 1) := by decide +kernel
-- Nonvacuous Lemma 4.5 instance (r=2, Q=1, n=96, m=50, E=96, b=1, w=2; empty factors 48, 49).
private def balancedEdge (e : Fin 96) : Fin 50 × Fin 96 := (⟨e.val / 2, by omega⟩, e)
private abbrev balA := constructedVarSchedule (by decide : 1 ≤ 2) 96 50 1 (1 + 2)
  (edgesOfFin balancedEdge)
private abbrev balD := constructedFactorSchedule (by decide : 1 ≤ 2) 96 50 1 (1 + 2)
  (edgesOfFin balancedEdge)
example : balD ⟨48, by decide⟩ 0 = 0 ∧ balD ⟨49, by decide⟩ 0 = 0 ∧
    (∀ u, occupancy (fun e => (balA (balancedEdge e).2, balD (balancedEdge e).1)) u ≤ 48) ∧
    (∀ g, occupancy (fun v => balA v 0) g ≤ 96) := by
  have hb : ∀ e : Fin 96, #{e' : Fin 96 | (balancedEdge e').2 = (balancedEdge e).2} ≤ 1 := fun e =>
    (Finset.card_le_card fun _ he' => Finset.mem_singleton.mpr (Finset.mem_filter.mp he').2).trans
      (by simp only [Finset.card_singleton, le_rfl])
  have hw : ∀ e : Fin 96, #{e' : Fin 96 | (balancedEdge e').1 = (balancedEdge e).1} ≤ 2 := fun e =>
    (Finset.card_le_card (t := {⟨2 * (e.val / 2), by omega⟩, ⟨2 * (e.val / 2) + 1, by omega⟩})
      fun _ he' => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, balancedEdge, Fin.ext_iff] at he'
        simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]; omega).trans
      Finset.card_le_two
  obtain ⟨hemp, hinc, hgrp⟩ := constructBalancedSchedules_balanced
    (by decide : 1 ≤ 2) (by decide : 1 ≤ 1) (by decide : 1 ≤ 96) balancedEdge hb hw
    (by decide : 0 < 1 + 2) (by decide : 2 * (1 + 2) * ((2 ^ 1) ^ 2) ^ 2 ≤ 96)
    (by decide : 2 * 1 * 2 ^ 2 ≤ 96)
  have h48 := congrFun (hemp ⟨48, by decide⟩ fun ⟨_, he⟩ => by
    simp only [balancedEdge, Fin.ext_iff] at he; omega) 0
  have h49 := congrFun (hemp ⟨49, by decide⟩ fun ⟨_, he⟩ => by
    simp only [balancedEdge, Fin.ext_iff] at he; omega) 0
  exact ⟨h48, h49, fun u => by have := hinc u; dsimp only [balA, balD]; omega,
    fun g => by have := hgrp 0 g; dsimp only [balA]; omega⟩
-- All-prefix outer state bit-length bound, fun_prop, and concrete certificate bounds at testParams.
example : ∀ s ≤ 2 + 4, (encPair encNat encOuterAcc
      (IndexFold.run greedySlotStepBody s
        (((2, 4, 2), (2, 4), testEdges), (List.replicate 2 none, List.replicate 4 none)))).length ≤
      2100 :=
  fun _ hs => (length_encOuterState_run_valid_le (n := 2) (m := 4) (Q := 2) (r := 2) (C := 4)
    (edges := testEdges) hs (by decide +kernel)).trans (by decide +kernel)
example : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => (slotOfIndex p.1.1 p.1.2 p.2).isSome)
    (encPair (encPair encUnary encUnary) encNat) encBool := by fun_prop
private def testParams : ScheduleParams := ((2, 4, 2), (2, 4), testEdges)
/-- info: constructBalancedSchedulesCertificate.time testParams : ℕ -/
#guard_msgs in
#check constructBalancedSchedulesCertificate.time testParams
example : ∃ poly : ℕ → ℕ, Cslib.PolynomiallyBounded poly ∧
    greedySchedulePassCertificate.time testParams ≤ 5 * poly (encScheduleParams testParams).length ∧
    greedySchedulePassCertificate.space testParams ≤ poly (encScheduleParams testParams).length ∧
    constructBalancedSchedulesCertificate.time testParams ≤
      5 * poly (encScheduleParams testParams).length ∧
    constructBalancedSchedulesCertificate.space testParams ≤
      poly (encScheduleParams testParams).length := by
  obtain ⟨p1, hp1, _, hb1⟩ := greedySchedulePassCertificate_bounds
  obtain ⟨p2, hp2, _, hb2⟩ := constructBalancedSchedulesCertificate_bounds
  set L := (encScheduleParams testParams).length
  have h1t : greedySchedulePassCertificate.time testParams ≤ 5 * p1 L := (hb1 testParams).1
  have h2t : constructBalancedSchedulesCertificate.time testParams ≤ 5 * p2 L := (hb2 testParams).1
  refine ⟨fun n => p1 n + p2 n, by fun_prop, ?_, (hb1 testParams).2.trans (Nat.le_add_right _ _),
    ?_, (hb2 testParams).2.trans (Nat.le_add_left _ _)⟩ <;> dsimp only <;> omega

end ComplexityTests.GreedyLabelSchedule
