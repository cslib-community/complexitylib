/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Dictionary.CuckooHashing.Memory

/-! Tests for cuckoo hashing over the memory oracle: the hypotheses of the headline theorem are
satisfiable, and it determines the answer of a concrete client. -/

@[expose] public section

namespace ComplexityTests.CuckooHashingMemory

open Cslib Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.CuckooHashing.Memory
open Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

/-- Store `1 ↦ 5`, then look up `1`. -/
def client : OracleComp (Dictionary.Op.Result (U := 4)) (Option ℕ) :=
  .liftBind (.insert 1 5) fun _ => .liftBind (.get 1) fun r => .pure r

/-- From the empty memory, the run from allocation answers `some 5`, with certainty. -/
example :
    ((Memory.spec 64).toRandomized.withCoins.run
        (run 4 (tableBits 2) 2 (maxEvictions 2) (attemptsFor 4 2) client)
        ⟨fun _ => 0, 0⟩).map Prod.fst = PMF.pure (some 5) :=
  (run_tableBits (V := 8) (by decide) (by decide) (by decide) client
    ⟨⟨Or.inl (by decide), by decide⟩, trivial, trivial⟩).1

end ComplexityTests.CuckooHashingMemory
