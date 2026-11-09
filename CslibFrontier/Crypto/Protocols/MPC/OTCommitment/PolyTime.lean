/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Extraction
public import CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Equivocation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Foundations.Data.BitString.List.Operations
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.FinRange

/-!
# Native polynomial-time OT commitment operations

The extractor's input is an explicit framed list of bit pairs, not a lookup oracle or an
unencoded finite function. The bridge `extractPairs_ofFn` identifies that list algorithm with
`extract` on the actual OT sender inputs. The equivocation map similarly processes an explicit
list of full OT indices and answers.
Only these deterministic operations are certified here; the unrestricted adversary and complete
simulators have no polynomial-time claim.

## Main definitions

* `OTCommitment.extractPairs`: strict majority of the parities of an explicit pair list.
* `OTCommitment.equivocatePairs`: opening pairs from an explicit OT receipt list.

## Main results

* `OTCommitment.extractPairs_ofFn`: bridge from actual OT input tables.
* `OTCommitment.extractPairs_polyTime`: native machine certificate with honest list encoding.
* `OTCommitment.equivocatePairs_ofFn`, `OTCommitment.equivocatePairs_polyTime`: the equivocation
  bridge and native certificate, retaining all four possible OT indices.
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

/-- Apply the existing equivocation operation to a list of full OT indices and received bits.
Each list element produces one pair; no lookup oracle or padded fixed-dimension carrier is used. -/
@[expose] def equivocatePairs (b : Bool) (receipts : List (Fin 4 × Bool)) : List (Bool × Bool) :=
  receipts.map fun receipt =>
    let pair := equivocate b (fun _ : Fin 1 => receipt) 0
    (pair false, pair true)

/-- The list operation agrees with every pair in the actual full-index transcript reconstruction. -/
theorem equivocatePairs_ofFn {k : ℕ} (b : Bool) (transcript : Fin k → Fin 4 × Bool) :
    equivocatePairs b (List.ofFn transcript) =
      List.ofFn (fun i => (equivocate b transcript i false, equivocate b transcript i true)) := by
  simp [equivocatePairs, List.map_ofFn, equivocate, opening, Function.comp_def]

/-- Native polynomial-time equivocation on an honestly encoded receipt list. The four-valued
index encoding has constant size; both transcript length and every received bit are charged. -/
theorem equivocatePairs_polyTime :
    ComputableInPolyTime
      (fun input : Bool × List (Fin 4 × Bool) => equivocatePairs input.1 input.2)
      (encPair encBool (encList (encPair (encFinEnum (Fin 4)) encBool)))
      (encList (encPair encBool encBool)) := by
  let encReceipt := encPair (encFinEnum (Fin 4)) encBool
  let encInput := encPair encBool (encList encReceipt)
  let op := fun p : Bool × (Fin 4 × Bool) =>
    let pair := equivocate p.1 (fun _ : Fin 1 => p.2) 0
    (pair false, pair true)
  have hop : ComputableInPolyTime op (encPair encBool encReceipt)
      (encPair encBool encBool) := ComputableInPolyTime.of_finite op
  have hparam : ComputableInPolyTime
      (fun p : (Bool × List (Fin 4 × Bool)) × (Fin 4 × Bool) => (p.1.1, p.2))
      (encPair encInput encReceipt) (encPair encBool encReceipt) :=
    ((ComputableInPolyTime.fst encBool (encList encReceipt)).comp
      (ComputableInPolyTime.fst encInput encReceipt)).prod
      (ComputableInPolyTime.snd encInput encReceipt)
  change ComputableInPolyTime
    (fun input : Bool × List (Fin 4 × Bool) => input.2.map (fun receipt => op (input.1, receipt)))
    encInput (encList (encPair encBool encBool))
  exact ComputableInPolyTime.mapWithInput (encA := encReceipt)
    (encB := encPair encBool encBool) (encIn := encInput)
    (f := fun input receipt => op (input.1, receipt)) (list := Prod.snd)
    (ComputableInPolyTime.snd encBool (encList encReceipt)) (hop.comp hparam)

end Cslib.Crypto.Protocols.MPC.OTCommitment
