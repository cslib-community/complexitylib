/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Complexity.Classes.NP.Image
import Complexity.Computability.Complexity.Classes.Oracle.BoundedQuery
import Complexity.Computability.Complexity.Problems.SAT.PolyTime

/-! # Bounded-query oracle classes and `P^{NP[O(log n)]}` -/

namespace ComplexityTests.OracleBoundedQuery

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

-- One request decides the oracle language itself, with the bound `1` at every length.
open Classical in
example (A : Set (List Bool)) :
    ComputableInPolyTimeWithOracleQueries A (fun _ => 1) (fun w => decide (w ∈ A)) encBits
      encBool :=
  computableInPolyTimeWithOracleQueries_query ComputableInPolyTime.id' A

-- The single-request program asks exactly the word it decides: one request, answered by `A`.
example (A : Set (List Bool)) (w : List Bool) :
    OracleComp.queriesWith (languageOracle A) (queryBit w) = [((), w)] := by
  simp

open Classical in
example : OracleComp.interpret (m := Id) (languageOracle {[true]}) (queryBit [true]) = true := by
  rw [interpret_queryBit]
  simp

-- `SAT` and its complement are in `P^{NP[O(log n)]}`.
example : SAT ∈ PNPLog encCNF := NP_subset_PNPLog encCNF SAT.mem_NP

example : SATᶜ ∈ PNPLog encCNF := compl_mem_PNPLog (NP_subset_PNPLog encCNF SAT.mem_NP)

-- `SAT` is decided by one request to the encodings of the satisfiable formulas, and so lies in
-- `P` relative to that oracle.
example : SAT ∈ PWithOracleQueries (encCNF '' SAT) (fun _ => 1) encCNF :=
  NP_subset_PWithOracleQueries_image_SAT encCNF SAT.mem_NP

example : SAT ∈ PWithOracle (encCNF '' SAT) encCNF :=
  PWithOracleQueries_subset_PWithOracle (NP_subset_PWithOracleQueries_image_SAT encCNF SAT.mem_NP)

-- The classes grow with the bound on the requests.
example : PWithOracleQueries (encCNF '' SAT) (fun _ => 1) encCNF ⊆
    PWithOracleQueries (encCNF '' SAT) (fun n => Nat.log 2 n + 1) encCNF :=
  PWithOracleQueries_mono fun _ => by omega

-- A polynomial-time problem needs no request at all: the bound `0` suffices.
example : (Set.univ : Set (List Bool)) ∈ PWithOracleQueries ∅ (fun _ => 0) encBits :=
  P_subset_PWithOracleQueries ∅ _ encBits ⟨fun _ => true, ComputableInPolyTime.const true,
    fun _ => by simp⟩

end ComplexityTests.OracleBoundedQuery
