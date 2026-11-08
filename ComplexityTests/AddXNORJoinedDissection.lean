/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (joined original-input dissection integration regression tests)

public import Complexity.Cryptanalysis.AddXNORJoinedDissection
import all Complexity.Cryptanalysis.AddXNORJoinedDissection
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORClassStreaming
import all Complexity.Cryptanalysis.AddXNORSource
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORDecision
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

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
    (s : BitVec m) (g : BitVec p) (n : ℕ)
    (hn : let input := ProgramGeneration.originalSource p as bs cs ds s 0
      n ≤ ClassStreaming.limit (JoinedDissection.classInput input g.toNat)
        (!ClassBalance.retainRight input g.toNat)) :=
  JoinedDissection.simultaneous_wire hp as bs cs ds s g n hn
example (input : ClassBalance.Input) (g : ℕ) (rows : List (ℕ × ℕ)) :=
  JoinedDissection.probe_recordWork input g rows

-- One actual uniform machine includes preparation, both-direction prepass and original readback.
-- Its space profile includes temporaries; no sharp source resource inequality is a premise.
example := JoinedDissection.sourceCertificate.computes
example := JoinedDissection.searchCertificate.computes
example := JoinedDissection.allCertificate.computes
