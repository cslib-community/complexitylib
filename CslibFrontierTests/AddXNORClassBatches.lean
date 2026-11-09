/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (restarted class-batch source integration regression tests)

public import CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Cryptanalysis.AddXNORSearchResources
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORClassBatches
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

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

-- Real generation/counting includes inverse addition and collisions, and the empty quarter.
example : ClassJoin.count (((3, 2), ([1], [1])), 5) = 2 := by decide +kernel
example : ClassJoin.count (((0, 0), ([], [])), 0) = 1 := by decide +kernel

-- A fixed physical-width polynomial covers both non-unit-width and zero-width producers.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ClassJoin.countCertificate.time (((3, 2), ([1], [1])), 5)+
        ClassJoin.countCertificate.space (((3, 2), ([1], [1])), 5) ≤
      5*P ((ClassJoin.encoding (((3, 2), ([1], [1])), 5)).length+1) ∧
    ClassJoin.countCertificate.time (((0, 0), ([], [])), 0)+
        ClassJoin.countCertificate.space (((0, 0), ([], [])), 0) ≤
      3*P ((ClassJoin.encoding (((0, 0), ([], [])), 0)).length+1) := by
  obtain ⟨P, hP, mono, bound⟩ := ProducerResources.countCertificate_bounds
  exact ⟨P, hP, mono, bound (((3, 2), ([1], [1])), 5), bound (((0, 0), ([], [])), 0)⟩

example := ProducerResources.original_count_bounds
example := ProducerResources.original_restarted_count_bounds
example := ProducerResources.original_reconstruction_sum

-- The phase resource theorem applies to the genuine installed arithmetic fallback above.
example (i : ℕ) : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ProducerResources.reconstructionAllowance (Source.prepare restartArithmeticHit) 0 i ≤
      2*(ClassBalance.balance (Source.prepare restartArithmeticHit)+
        JoinedDissection.quarterBudget (Source.prepare restartArithmeticHit)+1)*
          P ((ClassBalance.encoding (Source.prepare restartArithmeticHit)).length+16) := by
  have sourceEq : Source.prepare restartArithmeticHit = ProgramGeneration.originalSource 0
      (List.replicate 3 (0 : BitVec 3)) (List.replicate 3 0) (List.replicate 3 0)
        (List.replicate 5 0 ++ [1]) 0 0 := by decide +kernel
  obtain ⟨P, hP, mono, bound⟩ := ProducerResources.original_reconstruction_sum
  refine ⟨P, hP, mono, ?_⟩
  rw [sourceEq]
  exact (bound (by decide : 0 ≤ 3) (List.replicate 3 0) (List.replicate 3 0)
    (List.replicate 3 0) (List.replicate 5 0 ++ [1]) 0).2 (0 : BitVec 0) i

-- These numeric envelopes include the initial prefix and non-unit record/copy wires.
private def resetStep (_ : Bool) (_ _ : ℕ) : ℕ := 0
private def resetBody : Cslib.GenericRAM.NativeCertificate
    (fun _ : (Bool × ℕ) × ℕ => 0) (encPair (encPair encBool encNat) encNat) encNat := .const 0

example : Cslib.GenericRAM.NativeCertificate.foldStateWidth encNat resetStep
    (false, (3, [1, 2])) = 2 := by decide +kernel
example : Cslib.GenericRAM.NativeCertificate.foldTimeBudget encBool encNat encNat resetStep
    resetBody (false, (3, [1, 2])) = 56 := by decide +kernel
example : Cslib.GenericRAM.NativeCertificate.foldSpaceBudget encBool encNat encNat resetStep
    resetBody (false, (3, [1, 2])) = 34 := by decide +kernel
example : Cslib.GenericRAM.NativeCertificate.foldTimeBudget encBool encNat encNat resetStep
    resetBody (false, (3, [])) = 13 := by decide +kernel
example : Cslib.GenericRAM.NativeCertificate.foldSpaceBudget encBool encNat encNat resetStep
    resetBody (false, (3, [])) = 12 := by decide +kernel

-- Apply the whole installed source-certificate envelope to the real arithmetic fallback.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    let original := restartArithmeticHit
    let prepared := Source.prepare original
    let classes := 2^ClassBalance.depth prepared
    JoinedDissection.sourceCertificate.time original ≤
        ClassBalance.balanceCertificate.time prepared+
          (WholeRunResources.classTime prepared+classes+1)*P ((Source.encoding original).length) ∧
      JoinedDissection.sourceCertificate.space original ≤
        ClassBalance.balanceCertificate.space prepared+
          (WholeRunResources.classSpace prepared+classes+1)*
            P ((Source.encoding original).length) := by
  have originalEq : restartArithmeticHit =
      Source.ofWords 0 (0 : BitVec 3) (List.replicate 14 0 ++ [1]) := by decide +kernel
  obtain ⟨P, hP, mono, bound⟩ := WholeRunResources.sourceCertificate_bounds
  refine ⟨P, hP, mono, ?_⟩
  rw [originalEq]
  with_reducible exact bound 3 0 0 (List.replicate 14 0 ++ [1])

-- Both scalar prepasses execute and compute the actual maximum, including the zero-width case.
example : ClassBalance.balance (Source.prepare restartArithmeticHit) = 64 := by decide +kernel
example : ClassBalance.balance (Source.prepare (Source.ofWords 9 (0 : BitVec 0) [])) = 1 := by
  decide +kernel

-- One polynomial covers the actual fallback and zero-width/no-operator capped input.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    (ClassBalance.balanceCertificate.time (Source.prepare restartArithmeticHit) ≤
        128*P ((Source.encoding restartArithmeticHit).length) ∧
      ClassBalance.balanceCertificate.space (Source.prepare restartArithmeticHit) ≤
        8*P ((Source.encoding restartArithmeticHit).length)) ∧
    (let original := Source.ofWords 9 (0 : BitVec 0) [];
      ClassBalance.balanceCertificate.time (Source.prepare original) ≤
          P ((Source.encoding original).length) ∧
        ClassBalance.balanceCertificate.space (Source.prepare original) ≤
          P ((Source.encoding original).length)) := by
  obtain ⟨P, hP, mono, bound⟩ := BalanceResources.source_balance_bounds
  refine ⟨P, hP, mono, ?_, ?_⟩
  · have originalEq : restartArithmeticHit =
        Source.ofWords 0 (0 : BitVec 3) (List.replicate 14 0 ++ [1]) := by decide +kernel
    rw [originalEq]
    have instantiated := bound 3 0 0 (List.replicate 14 0 ++ [1])
    have timePow : (2 : ℕ)^((List.replicate 14 (0 : BitVec 3) ++ [1]).length/2) = 128 := by
      decide +kernel
    have spacePow : (2 : ℕ)^((List.replicate 14 (0 : BitVec 3) ++ [1]).length/4) = 8 := by
      decide +kernel
    dsimp only at instantiated
    with_reducible
      rw [timePow, spacePow] at instantiated
      exact instantiated
  · simpa only [List.length_nil, Nat.zero_div, pow_zero, one_mul] using
      bound 0 9 0 []

-- The original source run has its prepass closed; search clocks/workspaces remain explicit.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    let prepared := Source.prepare restartArithmeticHit
    JoinedDissection.sourceCertificate.time restartArithmeticHit ≤
        (WholeRunResources.classTime prepared+128)*
          P ((Source.encoding restartArithmeticHit).length) ∧
      JoinedDissection.sourceCertificate.space restartArithmeticHit ≤
        (WholeRunResources.classSpace prepared+8)*
          P ((Source.encoding restartArithmeticHit).length) := by
  obtain ⟨P, hP, mono, bound⟩ := BalanceResources.sourceCertificate_search_bounds
  refine ⟨P, hP, mono, ?_⟩
  have originalEq : restartArithmeticHit =
      Source.ofWords 0 (0 : BitVec 3) (List.replicate 14 0 ++ [1]) := by decide +kernel
  rw [originalEq]
  have instantiated := bound 3 0 0 (List.replicate 14 0 ++ [1])
  have timePow : (2 : ℕ)^((List.replicate 14 (0 : BitVec 3) ++ [1]).length/2) = 128 := by
    decide +kernel
  have spacePow : (2 : ℕ)^((List.replicate 14 (0 : BitVec 3) ++ [1]).length/4) = 8 := by
    decide +kernel
  dsimp only at instantiated
  with_reducible
    rw [timePow, spacePow] at instantiated
    exact instantiated

-- Both low-bit classes have collisions, and computed counts select the actual direct branch.
/-- Original four-operator input whose two computed classes select direct matching. -/
def directSource : Source.Input := Source.ofWords 1 (0 : BitVec 3) [1, 1, 1, 1]

example : (List.range 2).map (JoinedDissection.materialize (Source.prepare directSource)) =
    [true, true] := by decide +kernel
example : ClassBalance.balance (Source.prepare directSource) = 2 := by decide +kernel
example : (JoinedDissection.run directSource).2.isSome = true := by decide +kernel
/-- Non-unit full states miss despite complete projected collisions in the direct branch. -/
def directMiss : Source.Input := Source.ofWords 0 (2 : BitVec 5) [0, 0, 0, 1]

example : JoinedDissection.materialize (Source.prepare directMiss) 0 = true := by decide +kernel
example : ClassBalance.balance (Source.prepare directMiss) = 4 := by decide +kernel
example : (JoinedDissection.run directMiss).2 = none := by decide +kernel

example : SearchResources.restartTime (Source.prepare directSource) = 0 := by rfl
example : SearchResources.restartSpace (Source.prepare directSource) = 0 := by rfl

-- The residual keeps the actual fallback costs when its branch is selected.
example : SearchResources.restartTime (Source.prepare restartArithmeticHit) =
    WholeRunResources.classTime (Source.prepare restartArithmeticHit) := by
  have depthEq : ClassBalance.depth (Source.prepare restartArithmeticHit) = 0 := by decide +kernel
  have selected : JoinedDissection.materialize (Source.prepare restartArithmeticHit) 0 = false := by
    decide +kernel
  dsimp only [SearchResources.restartTime, WholeRunResources.classTime]
  rw [depthEq]
  simp only [pow_zero, Finset.range_one, Finset.sum_singleton, selected,
    Bool.false_eq_true, ite_false]
example : SearchResources.restartSpace (Source.prepare restartArithmeticHit) =
    WholeRunResources.classSpace (Source.prepare restartArithmeticHit) := by
  have depthEq : ClassBalance.depth (Source.prepare restartArithmeticHit) = 0 := by decide +kernel
  have selected : JoinedDissection.materialize (Source.prepare restartArithmeticHit) 0 = false := by
    decide +kernel
  dsimp only [SearchResources.restartSpace, WholeRunResources.classSpace]
  rw [depthEq]
  simp only [pow_zero, Finset.range_one, Finset.sup_singleton, selected,
    Bool.false_eq_true, ite_false]

-- An actual original-input run closes both resource bounds here, without runtime premises.
-- This checked direct-only input is not a substitute for the missing general restart bound.
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    JoinedDissection.sourceCertificate.time directSource ≤
        4*P ((Source.encoding directSource).length) ∧
      JoinedDissection.sourceCertificate.space directSource ≤
        4*P ((Source.encoding directSource).length) := by
  obtain ⟨P, hP, mono, bound⟩ := SearchResources.sourceCertificate_restart_bounds
  refine ⟨P, hP, mono, ?_⟩
  have instantiated := bound 3 1 0 [1, 1, 1, 1]
  have timeEq : SearchResources.restartTime (Source.prepare directSource) = 0 := by rfl
  have spaceEq : SearchResources.restartSpace (Source.prepare directSource) = 0 := by rfl
  have balanceEq : ClassBalance.balance (Source.prepare directSource) = 2 := by decide +kernel
  dsimp only at instantiated
  rw [show Source.ofWords 1 (0 : BitVec 3) [1, 1, 1, 1] = directSource from rfl] at instantiated
  have timePow : (2 : ℕ)^(([1, 1, 1, 1] : List (BitVec 3)).length/2) = 4 := by decide +kernel
  have spacePow : (2 : ℕ)^(([1, 1, 1, 1] : List (BitVec 3)).length/4) = 2 := by decide +kernel
  with_reducible
    rw [timePow, spacePow, timeEq, spaceEq, balanceEq] at instantiated
    simpa only [Nat.zero_add, Nat.reduceAdd] using instantiated
