/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (generated opposite-class nested consumer regression tests)

public import Complexity.Cryptanalysis.AddXNORJoinedProbe
import all Complexity.Cryptanalysis.AddXNORJoinedProbe
import all Complexity.Cryptanalysis.AddXNORClassBalance
import all Complexity.Cryptanalysis.AddXNORClassJoin
import all Complexity.Cryptanalysis.AddXNORBatchedAccess
import all Complexity.Cryptanalysis.AddXNORProgramGeneration
import all Complexity.Cryptanalysis.AddXNORBitInput
import all Complexity.Cryptanalysis.AddXNORSortedMeet
import all Complexity.Cryptanalysis.AddXNORSortedQuarterMachine
import all Complexity.Cryptanalysis.AddXNORNativeEnumeration
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.SortedMatch
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
Real generated quarter matches enter bounded batches directly. The tests cover
full flush/parking, final partial flush, zero width/quarters, empty dictionaries,
empty classes and a total zero-capacity raw consumer. Complete original-input
witness/miss and both orientations are tested in AddXNORJoinedDissection.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- Zero forward operands collide; the backward half includes non-self-inverse additions. -/
def onlineSource : ClassBalance.Input :=
  (((3, 2), (0, 0)), (([0, 0], [0, 0]), ([1, 2], [3, 4])))

/-- A real generated retained dictionary, not an asserted semantic dictionary. -/
def onlineContext : JoinedProbe.Context :=
  ((onlineSource, false), ((3, (true, ClassBalance.records onlineSource true 0)), 7))

example : JoinedProbe.visits onlineContext 0 = 8 := by decide +kernel
example : (JoinedProbe.buffer onlineContext 0 6).length = 6 := by decide +kernel
example : JoinedProbe.buffer onlineContext 0 7 = [] := by decide +kernel
example : JoinedProbe.buffer onlineContext 0 20 = [] := by decide +kernel
example : (JoinedProbe.run onlineContext 0).isSome = true := by decide +kernel
example : JoinedProbe.visits ((onlineSource, false), ((3, (true, [])), 1)) 0 = 0 := by
  decide +kernel
example : JoinedProbe.run ((onlineSource, false), ((3, (true, [])), 1)) 0 = none := by
  decide +kernel
example : JoinedProbe.run ((onlineSource, false), ((3, (true, [])), 0)) 0 = none := by
  decide +kernel
example : JoinedProbe.run onlineContext 1 = none := by decide +kernel

/-- Empty quarters still have one packed empty word in the unique zero-width class. -/
def zeroContext : JoinedProbe.Context :=
  (((((0, 0), (0, 0)), (([], []), ([], []))), false), ((0, (true, [(0, 0)])), 2))

example : JoinedProbe.visits zeroContext 0 = 1 := by decide +kernel
example : JoinedProbe.run zeroContext 0 = some (0, 0) := by decide +kernel
example : JoinedProbe.buffer zeroContext 0 100 = [(0, 0)] := by decide +kernel

example (context : JoinedProbe.Context) (groups : List (List SortedMatch.Record))
    (hc : let (_, (_, capacity)) := context; 0 < capacity) :=
  JoinedProbe.consume_valid context groups hc
example := JoinedProbe.consumeCertificate.computes
example := JoinedProbe.runCertificate.computes
