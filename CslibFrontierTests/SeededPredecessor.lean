/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.PolyTime.SeededPredecessor

open Cslib Cslib.SeededPredecessor Turing.MultiTapeTM

-- The linear polynomial hashes the two tagged keys differently at nonzero label width.
private def input : Input := ⟨2, 1, 0, 1, 0, 0, 3, 1, 0, 1, 0, 1⟩

example : test input = true := by
  simp only [test, SeededPredecessor.hash, input, TrinomialArithmetic.runSelected,
    TrinomialArithmetic.hash4, TrinomialArithmetic.eval4, TrinomialArithmetic.mul,
    TrinomialArithmetic.reduce, clmul_eq_foldr_bits, Probability.trinomialStep,
    Probability.trinomialTargetBits, Probability.trinomialStepAux_eq_findGreatest]
  decide

-- Changing just one endpoint excludes the candidate from this class.
example : test { input with candidateRow := 1 } = false := by
  simp only [test, SeededPredecessor.hash, input, TrinomialArithmetic.runSelected,
    TrinomialArithmetic.hash4, TrinomialArithmetic.eval4, TrinomialArithmetic.mul,
    TrinomialArithmetic.reduce, clmul_eq_foldr_bits, Probability.trinomialStep,
    Probability.trinomialTargetBits, Probability.trinomialStepAux_eq_findGreatest]
  decide

-- Equal endpoints never make an edge its own strict predecessor.
example : test { input with candidate := 3 } = false := by
  simp [test, input]

example : ComputableInPolyTime test encInput encBool := computableInPolyTime_test

-- A parallel earlier edge is counted for every shared seed, at positive label width.
example (vertex : Unit ⊕ Unit ↪ Fin 2)
    (seed : BalancedSchedules.SeededLabels.Seed 2 6) :
    test (ofEdges 2 1 vertex (fun _ : Fin 4 => ()) (fun _ => ()) seed 3 1) = true := by
  rw [test_ofEdges]
  simp [PacketPacking.Seeded.predecessor]

-- Exact equality covers empty labels, including the zero-bit hash case.
example (vertex : Unit ⊕ Unit ↪ Fin 2)
    (seed : BalancedSchedules.SeededLabels.Seed 2 0) :
    test (ofEdges 2 0 vertex (fun _ : Fin 1 => ()) (fun _ => ()) seed 0 0) = false := by
  rw [test_ofEdges]
  simp [PacketPacking.Seeded.predecessor]

-- With no label coordinates, even distinct endpoints share the unique pair label.
example {R C : Type*} (U : ℕ) (vertex : R ⊕ C ↪ Fin U)
    (rowOf : Fin 2 → R) (colOf : Fin 2 → C)
    (seed : BalancedSchedules.SeededLabels.Seed U 0) :
    test (ofEdges U 0 vertex rowOf colOf seed 1 0) = true := by
  rw [test_ofEdges]
  simp only [PacketPacking.Seeded.predecessor]
  have hr : PacketPacking.Seeded.label U 0 seed (vertex (.inl (rowOf 0))) =
      PacketPacking.Seeded.label U 0 seed (vertex (.inl (rowOf 1))) := Subsingleton.elim _ _
  have hc : PacketPacking.Seeded.label U 0 seed (vertex (.inr (colOf 0))) =
      PacketPacking.Seeded.label U 0 seed (vertex (.inr (colOf 1))) := Subsingleton.elim _ _
  simp [hr, hc]
