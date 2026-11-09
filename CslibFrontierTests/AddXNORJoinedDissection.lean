/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (joined original-input dissection integration regression tests)

public import CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORJoinedProbe
import all CslibFrontier.Cryptanalysis.AddXNORJoinedDissection
import all CslibFrontier.Cryptanalysis.AddXNORClassBalance
import all CslibFrontier.Cryptanalysis.AddXNORClassJoin
import all CslibFrontier.Cryptanalysis.AddXNORBatchedAccess
import all CslibFrontier.Cryptanalysis.AddXNORClassStreaming
import all CslibFrontier.Cryptanalysis.AddXNORSource
import all CslibFrontier.Cryptanalysis.AddXNORSortedMeet
import all CslibFrontier.Cryptanalysis.AddXNORSortedQuarterMachine
import all CslibFrontier.Cryptanalysis.AddXNORDecision
import all CslibFrontier.Cryptanalysis.AddXNORNativeEnumeration
import all CslibFrontier.Cryptanalysis.AddXNORProgramGeneration
import all CslibFrontier.Cryptanalysis.AddXNORBitInput
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
The complete original-input route computes both populations/balance, generates
the smaller class, executes bounded-batch probing/release and decodes a complete
original witness. The fixtures exercise genuine inverse arithmetic and collisions,
backward retention, exhaustive absence, quarter residue and zero/empty input.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- Backward retention is selected in the first class, with colliding full-state records. -/
def joinedFixture : Source.Input := ((3, 2), [0, 0, 0, 0, 0, 1, 2, 3, 4])

example : (JoinedDissection.run joinedFixture).1 = 6 := by decide +kernel
example : ((JoinedDissection.run joinedFixture).2.map
    (fun ops => natEval 3 (ops.zip [0, 0, 0, 0, 1, 2, 3, 4]) 0)) = some 0 := by
  decide +kernel
example : JoinedDissection.run ((3, 2), [0, 0, 0, 0, 0, 0, 0, 0, 2]) =
    (0, none) := by decide +kernel
example : JoinedDissection.run ((2, 0), [0, 1]) = (1, none) := by decide +kernel
example : JoinedDissection.run ((0, 8), []) = (1, some []) := by decide +kernel
example : JoinedDissection.run ((3, 8), [2]) = (1, none) := by decide +kernel
example : ((JoinedDissection.run ((3, 1), [0, 1, 2, 3, 4, 5])).2.map
    (fun ops => natEval 3 (ops.zip [1, 2, 3, 4, 5]) 0)) = some 0 := by decide +kernel
example : JoinedDissection.search
    (Source.prepare ((3, 2), [0, 1, 2, 3, 4, 0, 0, 0, 0])) 1 = none := by decide +kernel

example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :=
  JoinedDissection.original_correct p s tail
example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :=
  JoinedDissection.original_balance p s tail
example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) (n : ℕ)
    (hn : n ≤ 2 ^ ClassBalance.depth (Source.prepare (Source.ofWords p s tail))) :=
  JoinedDissection.source_count_prefix_wire p s tail n hn
example (input : ClassBalance.Input) (g n : ℕ) (hg : g < 2 ^ ClassBalance.depth input) :=
  JoinedDissection.simultaneous_records input g n hg
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m))
    (s : BitVec m) (g : BitVec p) (n : ℕ) :=
  JoinedDissection.simultaneous_wire hp as bs cs ds s g n
example (input : ClassBalance.Input) (g : ℕ) (rows : List (ℕ × ℕ)) :=
  JoinedDissection.probe_recordWork input g rows

-- One actual uniform machine includes preparation, both-direction prepass and original readback.
-- Its space profile includes temporaries; no sharp source resource inequality is a premise.
example := JoinedDissection.sourceCertificate.computes
example := JoinedDissection.searchCertificate.computes
example := JoinedDissection.allCertificate.computes

-- Produced iteration slots total actual opposite class sizes, rather than half words per class.
example : (List.range 4).map
    (JoinedDissection.pairVisits (Source.prepare joinedFixture)) = [8, 0, 0, 8] := by
  decide +kernel
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :=
  JoinedDissection.sum_pairVisits hp as bs cs ds s
example : (JoinedDissection.buffer (Source.prepare joinedFixture) 0 6).length = 6 := by
  decide +kernel
example : (JoinedDissection.buffer (Source.prepare joinedFixture) 0 7).length = 0 := by
  decide +kernel

example (input : ClassBalance.Input) := JoinedDissection.allSearch_eq_fold input
-- The actually generated class-index data is quarter scale at the source frontend's depth.
example (input : ClassBalance.Input) :=
  SortedQuarterMachine.indices_wire (ClassBalance.depth input)

-- Actual counts select one dictionary read/match for a fitting colliding class.
example : JoinedDissection.materialize (Source.prepare joinedFixture) 0 = true := by
  decide +kernel
example : (JoinedDissection.directPrefix (Source.prepare joinedFixture) 0 100).length = 8 := by
  decide +kernel
example : JoinedDissection.directRecordWork (Source.prepare joinedFixture) 0 = 14 := by
  decide +kernel
example : JoinedDissection.materialize (Source.prepare joinedFixture) 1 = false := by
  decide +kernel

/-- Fourth-quarter residue makes the opposite population exceed the computed allowance. -/
def joinedFallback : Source.Input := ((0, 0), List.replicate 16 0)

example : JoinedDissection.materialize (Source.prepare joinedFallback) 0 = false := by
  decide +kernel
example : (JoinedDissection.run joinedFallback).1 = 64 := by decide +kernel
example : (JoinedDissection.run joinedFallback).2.isSome = true := by decide +kernel
example : JoinedDissection.directRecordWork (Source.prepare joinedFallback) 0 = 0 := by
  decide +kernel

example (input : ClassBalance.Input) (g n : ℕ) (hg : g < 2 ^ ClassBalance.depth input) :=
  JoinedDissection.direct_prefix_records input g n hg
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m)
    (g : BitVec p) (n : ℕ) := JoinedDissection.direct_prefix_wire hp as bs cs ds s g n
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :=
  JoinedDissection.sum_directRecordWork hp as bs cs ds s
example {m : ℕ} (p : ℕ) (s : BitVec m) (tail : List (BitVec m)) :=
  JoinedDissection.quarterBudget_source p s tail
example {m p : ℕ} (hp : p ≤ m) (as bs cs ds : List (BitVec m)) (s : BitVec m) :=
  JoinedDissection.allSearch_wire hp as bs cs ds s
example := JoinedDissection.halvesCertificate.computes
example := JoinedDissection.readbackCertificate.computes
example := JoinedDissection.preparation_readback_bounds
