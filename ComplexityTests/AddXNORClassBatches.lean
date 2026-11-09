/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (restarted class-batch source integration regression tests)

public import Complexity.Cryptanalysis.AddXNORMatcherResources
import all Complexity.Cryptanalysis.AddXNORJoinedDissection
import all Complexity.Cryptanalysis.AddXNORClassBatches
import all Complexity.Cryptanalysis.AddXNORJoinedProbe
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
The source fixture really chooses the fallback. Its completed batches are
materialized separately and released; no feed buffer is a per-pair state.
Window boundaries deliberately cut a Cartesian row. The complete existing
JoinedDissection client also checks original inverse arithmetic, collisions,
returned witness semantics, exhaustive misses and all source residue cases.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- A real residual cut with a much larger opposite class. -/
def restartFixture : Source.Input := ((0, 0), List.replicate 16 0)

/-- Original input computes the retained dictionary and orientation, not advice. -/
def restartContext : JoinedProbe.Context :=
  JoinedDissection.probeContext (Source.prepare restartFixture) 0

example : JoinedDissection.materialize (Source.prepare restartFixture) 0 = false := by
  decide +kernel
example : ClassBatches.quarterVolume restartContext = 72 := by decide +kernel
example : ClassBatches.capacity restartContext = 137 := by decide +kernel
example : ClassBatches.batchCount restartContext 0 = 4 := by decide +kernel
example : (ClassBatches.labels restartContext 0).length = 8 := by decide +kernel
example : (List.range 4).map (fun i => (ClassBatches.batch restartContext 0 i).length) =
    [144, 136, 136, 96] := by decide +kernel
example : ClassBatches.matchLabel restartContext 0 4 = none := by decide +kernel
example : (ClassBatches.run restartContext 0).isSome = true := by decide +kernel
example : (JoinedDissection.run restartFixture).2.isSome = true := by decide +kernel

/-- The last operand uses genuinely non-self-inverse addition in the fallback. -/
def restartArithmeticHit : Source.Input := ((3, 0), List.replicate 15 0 ++ [1])

/-- Full states remain separated despite complete projected collisions and unequal halves. -/
def restartArithmeticMiss : Source.Input := ((5, 0), [2] ++ List.replicate 14 0 ++ [1])

example : JoinedDissection.materialize (Source.prepare restartArithmeticHit) 0 = false := by
  decide +kernel
example : ((JoinedDissection.run restartArithmeticHit).2.map
    (fun ops => natEval 3 (ops.zip (List.replicate 14 0 ++ [1])) 0)) = some 0 := by
  decide +kernel
example : JoinedDissection.materialize (Source.prepare restartArithmeticMiss) 0 = false := by
  decide +kernel
example : (JoinedDissection.run restartArithmeticMiss).2 = none := by decide +kernel

/-- A genuine source class selects backward retention but still needs restarted forward batches. -/
def restartBackward : Source.Input := ((6, 5), List.replicate 11 0 ++ List.range' 1 10)

example : ClassBalance.retainRight (Source.prepare restartBackward) 0 = true := by
  decide +kernel
example : JoinedDissection.materialize (Source.prepare restartBackward) 0 = false := by
  decide +kernel
example : ClassBatches.capacity (JoinedDissection.probeContext (Source.prepare restartBackward) 0) =
    93 := by decide +kernel
example : ((JoinedDissection.search (Source.prepare restartBackward) 0).map (fun out =>
    natEval 6 ((SortedMeet.decodeWitness (JoinedDissection.halves (Source.prepare restartBackward))
      out).zip (List.replicate 10 0 ++ List.range' 1 10)) 0)) = some 0 := by
  decide +kernel

-- Row alignment includes the full right run; an interval inside a prior row emits nothing.
example : KeyJoinBatch.window (0, 1) [[(0, 0), (0, 2), (0, 1), (0, 3)]] =
    [(0, 0), (0, 1)] := by decide +kernel
example : KeyJoinBatch.window (1, 1) [[(0, 0), (0, 2), (0, 1), (0, 3)]] = [] := by
  decide +kernel
example : KeyJoinBatch.window (2, 1) [[(0, 0), (0, 2), (0, 1), (0, 3)]] =
    [(1, 0), (1, 1)] := by decide +kernel
example : KeyJoinBatch.window (0, 0) [[(0, 0), (0, 1)], [], [(0, 2)]] = [] := by
  decide +kernel
example : ClassBatches.run (((((0, 0), (0, 0)), (([], []), ([], []))), false),
    ((0, (true, [])), 0)) 0 = none := by decide +kernel

example (context : JoinedProbe.Context) (g i : ℕ) := ClassBatches.batch_length context g i
example (context : JoinedProbe.Context) (g : ℕ) := ClassBatches.copyAllowance context g
example (context : JoinedProbe.Context) (g : ℕ) := ClassBatches.labels_wire context g
example (input : ClassBalance.Input) (g i n : ℕ) (hg : g < 2 ^ ClassBalance.depth input) :=
  JoinedDissection.restart_prefix_records input g i n hg
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m)
    (g : BitVec p) (i n : ℕ) := JoinedDissection.restart_prefix_wire hp as bs cs ds s g i n
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :=
  JoinedDissection.sum_restartCopyWork hp as bs cs ds s
example := KeyJoinBatch.windowCertificate.computes
example := ClassBatches.batchCertificate.computes
example := ClassBatches.runCertificate.computes
example := JoinedDissection.sourceCertificate.computes

-- One fixed polynomial handles real non-unit-width collision records in both orientations.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∀ right : Bool,
      BatchedAccess.matchCertificate.time ((3, (right, [(0, 0), (0, 1)])), [(0, 2), (7, 3)]) +
        BatchedAccess.matchCertificate.space ((3, (right, [(0, 0), (0, 1)])), [(0, 2), (7, 3)]) ≤
          5 * P 20 := by
  obtain ⟨P, hP, mono, bound⟩ := MatcherResources.matchCertificate_bounds
  refine ⟨P, hP, mono, ?_⟩
  intro right
  exact bound 3 20 right [(0, 0), (0, 1)] [(0, 2), (7, 3)] (by omega) (by decide +kernel)

example := MatcherResources.original_restart_bounds
