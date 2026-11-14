/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxCut.Derandomized
public import CslibFrontier.Computability.PolyTime.PessimisticEstimator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Tactic.EncLen

/-!
# Polynomial-time certificate for deterministic conditional-expectations `MaxCut`

Instantiates `Cslib.Computability.PolyTimeGreedyInput` for the deterministic
conditional-expectations `MaxCut` algorithm (`Cslib.Algorithms.Lean.MaxCut.derandomizedCut`) over
binary-encoded weighted multigraphs (`encList Cslib.Complexity.MaxCut.encWeightedEdge`).

Each greedy round prepends one vertex from `distinctVertices edges` to either `trueSide` or
`falseSide` of `PartialCut`, growing `encPartialCut` by at most
`4 * (encList encNat (distinctVertices edges)).length + 4` bits, while `distinctVertices`,
`assignVertex`, and `scaledUncut` are `ComputableInPolyTime`.

## Main definitions

* `Cslib.Algorithms.Lean.MaxCut.encPartialCut`: framed-tuple encoding of `PartialCut`.
* `Cslib.Algorithms.Lean.MaxCut.maxCutGreedyInput`: `PolyTimeGreedyInput` bundle for weighted
  `MaxCut` derandomization.

## Main results

* `Cslib.Algorithms.Lean.MaxCut.computableInPolyTime_distinctVertices`: deduplicating vertex
  endpoints runs in polynomial time.
* `Cslib.Algorithms.Lean.MaxCut.computableInPolyTime_scaledUncut`: evaluating twice the expected
  uncut weight runs in polynomial time.
* `Cslib.Algorithms.Lean.MaxCut.computableInPolyTime_derandomizedCutState`,
  `Cslib.Algorithms.Lean.MaxCut.computableInPolyTime_derandomizedCut`: deterministic
  conditional-expectations `MaxCut` runs in polynomial time on multi-tape Turing machines.
-/

public section

namespace Cslib.Algorithms.Lean.MaxCut

open Cslib.Complexity Cslib.Complexity.MaxCut Cslib.Computability
open Turing.MultiTapeTM ComputableInPolyTime

/-- Framed-pair encoding of `PartialCut` with binary-encoded vertex lists (`encList encNat`). -/
enc_structure encPartialCut : PartialCut where
  trueSide : (encList encNat), falseSide : (encList encNat)

attribute [fun_prop] encPartialCut_trueSide_polyTime encPartialCut_falseSide_polyTime
  encPartialCut_mk_polyTime

/-- `PolyTimeGreedyInput` bundle for deterministic conditional-expectations `MaxCut`. -/
@[expose] def maxCutGreedyInput :
    PolyTimeGreedyInput (List WeightedEdge) ℕ PartialCut ℕ where
  rounds := distinctVertices
  init _ := PartialCut.empty
  branch _ := assignVertex
  estimate := scaledUncut

/-- Extracting the deduplicated endpoint list `distinctVertices` is polynomial-time. -/
theorem computableInPolyTime_distinctVertices :
    ComputableInPolyTime distinctVertices (encList encWeightedEdge) (encList encNat) := by
  unfold distinctVertices endpoints
  fun_prop

private theorem computableInPolyTime_assignVertex :
    ComputableInPolyTime
      (fun p : (((List WeightedEdge × PartialCut) × ℕ) × Bool) =>
        assignVertex p.1.2 p.2 p.1.1.2)
      (PolyTimeGreedyInput.encBranchInput (encList encWeightedEdge) encPartialCut encNat)
      encPartialCut := by
  unfold PolyTimeGreedyInput.encBranchInput assignVertex
  fun_prop

/-- Evaluating `scaledUncut` on `(edges, s)` is polynomial-time. -/
theorem computableInPolyTime_scaledUncut :
    ComputableInPolyTime (fun p : List WeightedEdge × PartialCut => scaledUncut p.1 p.2)
      (encPair (encList encWeightedEdge) encPartialCut) encNat := by
  unfold scaledUncut edgeScaledUncut
  fun_prop

private theorem length_encPartialCut_assignVertex_le (edges : List WeightedEdge) (s : PartialCut)
    (v : ℕ) (b : Bool) (hv : v ∈ distinctVertices edges) :
    (encPartialCut (assignVertex v b s)).length ≤
      (encPartialCut s).length +
        (4 * (encList encNat (distinctVertices edges)).length + 4) := by
  have hv_len : (encNat v).length ≤ (encList encNat (distinctVertices edges)).length :=
    SizedListEncoding.length_elem_le (distinctVertices edges) v hv
  cases b
  · enc_len [assignVertex, Bool.false_eq_true, ite_false, encPartialCut_apply, encPartialCutFields]
  · enc_len [assignVertex, ite_true, encPartialCut_apply, encPartialCutFields]

/-- Computing `derandomizedCutState` is polynomial-time via
`PolyTimeGreedyInput.computableInPolyTime_run_nat`. -/
theorem computableInPolyTime_derandomizedCutState :
    ComputableInPolyTime derandomizedCutState (encList encWeightedEdge) encPartialCut := by
  have hrounds := computableInPolyTime_distinctVertices
  have hpoly :
      PolyBounded (fun edges => (encList encWeightedEdge edges).length)
        (fun edges => 4 * (encList encNat (distinctVertices edges)).length + 4) :=
    ((PolyBounded.const 4).mul hrounds.polyBounded_length).add (.const 4)
  exact maxCutGreedyInput.computableInPolyTime_run_nat hrounds (const PartialCut.empty)
    computableInPolyTime_assignVertex computableInPolyTime_scaledUncut hpoly
    length_encPartialCut_assignVertex_le

/-- **Deterministic conditional-expectations `MaxCut` runs in polynomial time** on multi-tape
Turing machines. -/
theorem computableInPolyTime_derandomizedCut :
    ComputableInPolyTime derandomizedCut (encList encWeightedEdge) (encList encNat) := by
  have hstate := computableInPolyTime_derandomizedCutState
  unfold derandomizedCut
  fun_prop

end Cslib.Algorithms.Lean.MaxCut
