/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.MPC.OTCommitment.Extraction
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Foundations.Data.BitString.List.Operations
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.FinRange

/-!
# Native polynomial-time OT commitment extractor

The extractor's input is an explicit framed list of bit pairs, not a lookup oracle or an
unencoded finite function. The bridge `extractPairs_ofFn` identifies that list algorithm with
`extract` on the actual OT sender inputs. Only this deterministic extractor is certified here;
the unrestricted adversary and the complete simulator have no polynomial-time claim.

## Main definitions

* `OTCommitment.extractPairs`: strict majority of the parities of an explicit pair list.

## Main results

* `OTCommitment.extractPairs_ofFn`: bridge from actual OT input tables.
* `OTCommitment.extractPairs_polyTime`: native machine certificate with honest list encoding.
-/

public section

namespace Cslib.Crypto.Protocols.MPC.OTCommitment

open Turing.MultiTapeTM Turing.MultiTapeTM.Encodings

/-- Strict majority of pair parities, computed by counting them in an explicitly encoded list.
The strict comparison resolves empty lists and ties to false. -/
@[expose] def extractPairs (pairs : List (Bool × Bool)) : Bool :=
  BitString.listStrictMajority (pairs.map (fun p => p.1 ^^ p.2))

/-- The encoded-list extractor computes the same bit as strict majority of actual OT inputs. -/
theorem extractPairs_ofFn {k : ℕ} (ts : Fin k → Fin 4 → Bool) :
    extractPairs (List.ofFn (fun i =>
      (ts i (boolPairToFin4 (false, false)), ts i (boolPairToFin4 (false, true))))) =
      extract ts := by
  simp [extractPairs, extract, List.ofFn_eq_map, List.map_map,
    BitString.listStrictMajority_map _ (List.nodup_finRange k),
    strictMajority_eq_strictMajorityOn, Function.comp_def]

/-- Polynomial-time extraction from a framed list of framed pairs of single bits. This measures
ordinary encoded input size and provides independent polynomial time and space bounds. -/
theorem extractPairs_polyTime :
    ComputableInPolyTime extractPairs (encList (encPair encBool encBool)) encBool := by
  exact ComputableInPolyTime.bitsStrictMajority.comp
    (.mapToBitsWithInput (enc := encPair encBool encBool) .id'
      (ComputableInPolyTime.bool_xor.comp (.snd _ _)))

end Cslib.Crypto.Protocols.MPC.OTCommitment
