/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Replay.Oracle
public import CslibFrontier.Probability.AdaptiveWeights
import CslibFrontier.Computability.Complexity.Classes.SharpP.Products
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# GapP weights for finite oracle replay

An instruction-indexed transcript supplies a Boolean reply at each machine instruction. Query
instructions use a GapP numerator, while local instructions assign zero weight to `true`.
Each pair of branch weights sums to a per-instance GapP denominator `D a`. Summing the accepting
transcript products gives an ordinary GapP function by uniform indexed products and uniform
Boolean sums. AWPP lowness uses the dyadic denominator `D a = 2 ^ R a`; the exact `SPP` and `LWPP`
simulations use `D a = 1` and a length-dependent product of targets.

## Main definitions

* `weightedReplay`: the accepting integer weight of a clocked native oracle computation.

## Main results

* `GapP.weightedReplay_mem`: polynomial-time input, a unary clock and a GapP denominator give
  ordinary GapP membership, uniformly for every GapP request numerator.

## References

* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003].
-/

@[expose] public section

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapeMachine
  _root_.Turing.MultiTapePTM
open Probability.AdaptiveWeights Finset

variable {α : Type} {enc : α ↪ List Bool}
variable {k : ℕ} {Control Operation : Type} [DecidableEq Operation]

/-- Total accepting weight of the instruction-indexed replay tree with per-instance integer
denominator `D a`. Query instructions use the request numerator `H (a, w)`, while local
instructions assign zero weight to `true` and weight `D a` to the canonical padding bit
`false`. -/
def weightedReplay (machine : MultiTapePTM k Bool Control Operation)
    (input : α → List Bool) (T : α → ℕ) (D : α → ℤ) (H : α × List Bool → ℤ) (a : α) : ℤ :=
  acceptWeight (D a)
    (fun cfg => if (machine.pendingQuery cfg).isSome then H (a, machine.pendingRequest cfg) else 0)
    machine.replyStep (fun cfg => cfg.tapes.output.headD false) (T a)
    (FiniteConfig.init machine.initial (input a))

/-- A finite oracle computation with a GapP denominator and GapP request numerators has an
ordinary GapP accepting weight. The clock is computed in unary; no oracle closure axiom or
positivity assumption on the numerators is needed. -/
theorem GapP.weightedReplay_mem [Finite Control] [Finite Operation]
    (machine : MultiTapePTM k Bool Control Operation)
    {input : α → List Bool} {T : α → ℕ} {D : α → ℤ} {H : α × List Bool → ℤ}
    (hinput : Turing.MultiTapeTM.ComputableInPolyTime input enc encBits)
    (hT : Turing.MultiTapeTM.ComputableInPolyTime T enc encUnary)
    (hD : D ∈ GapP enc)
    (hH : H ∈ GapP (encPair enc encBits)) :
    weightedReplay machine input T D H ∈ GapP enc := by
  -- reindex to the argument shape of the replay-prefix polynomial-time lemmas; the
  -- compositions are elaborated without an expected type, which keeps unification first-order
  have hreplay : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => ((input x.1.1, x.1.2), x.2))
      (encPair (encPair enc encBits) encUnary) (encPair (encPair encBits encBits) encUnary) := by
    fun_prop
  have hquery := machine.replayPrefix_isQuery_pt.comp hreplay
  have hrequest := ((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod
    (machine.replayPrefix_pendingRequest_pt.comp hreplay)
  let p : (α × List Bool) × ℕ → ℤ := fun x =>
    let cfg := machine.replayPrefix (input x.1.1) x.1.2 x.2
    if (machine.pendingQuery cfg).isSome then H (x.1.1, machine.pendingRequest cfg) else 0
  have hp : p ∈ GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.ite_mem hquery (GapP.comp_mem hH hrequest) GapP.zero_mem
  have hdenom : (fun x : (α × List Bool) × ℕ => D x.1.1) ∈
      GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.comp_mem hD (by fun_prop)
  have hbit : ComputableInPolyTime
      (fun x : (α × List Bool) × ℕ => x.1.2.getD x.2 false)
      (encPair (encPair enc encBits) encUnary) encBool := by fun_prop
  have hfactor := GapP.ite_mem hbit hp (GapP.sub_mem' hdenom hp)
  have hprod := GapP.prod_range_mem hfactor
    (r := fun x : α × List Bool => x.2.length) (by fun_prop)
  have hout : ComputableInPolyTime
      (fun x : α × List Bool => (machine.replayOutput (input x.1) x.2).headD false)
      (encPair enc encBits) encBool := by
    have hreindex : ComputableInPolyTime
        (fun x : α × List Bool => (input x.1, x.2))
        (encPair enc encBits) (encPair encBits encBits) := by fun_prop
    exact (ComputableInPolyTime.headD false).comp
      (machine.computableInPolyTime_replayOutput.comp hreindex)
  have hmask : (fun x : α × List Bool =>
      if (machine.replayOutput (input x.1) x.2).headD false then (1 : ℤ) else 0) ∈
      GapP (encPair enc encBits) := GapP.ite_mem hout GapP.one_mem GapP.zero_mem
  have hsum := GapP.sum_bits_mem (GapP.mul_mem hprod hmask) hT
  convert hsum using 1
  funext a
  rw [weightedReplay, acceptWeight_eq_sum]
  apply sum_congr rfl
  intro w _
  rw [pathWeight_eq_prod]
  rfl

end Cslib.Complexity
