/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.MCSP.MultiNPHard.Reduction
import CslibFrontier.Computability.MCSP.MultiNPHard.PolyTime
import CslibFrontier.Computability.PCP.Approximation.SetCover.LundYannakakis

/-!
# Multi-output MCSP is NP-hard under randomized reductions

Ilango, Loff and Oliveira [IlangoLoffOliveira2020, Theorem 4, p. 22:5]: every problem in `NP`
reduces to Multi-output MCSP (`MultiMCSP`) by a polynomial-time randomized reduction with one-sided
error. Yes-instances always map to yes-instances, and no-instances map to no-instances with
probability at least `2/3` (`Complexity.PromiseProblem.RPReducible`).

The results hold over every `Boolean.DeMorganBasis`. Over `Boolean.DeMorgan.interpretation`, the
constant-free basis, Multi-MCSP on positive instances (`MultiMCSP.Instance.Positive`) is exactly
Definition 1 of the source [p. 22:3], so `MultiMCSP.rpHard_pos` is the source's statement;
`Boolean.interpretation` gives the library variant with constants.

**The library route.** The proof composes the library's `NP`-hardness of `GapSetCover 3`
(`Complexity.GapSetCover_npHard`) with the reduction `MultiMCSP.Reduction.reduce` of the source's
§4.2 [pp. 22:20–22:21], which `MultiMCSP.Reduction.computableInPolyTime_reduce` shows runs in
polynomial time. It deviates from the source in four places, none of which changes the statement:

* The source reduces from Trevisan's `r`-bounded Set Cover; here the source problem is the
  library's `GapSetCover 3`.
* Soundness counts the cheap tables with a union bound over small circuits
  (`MultiMCSP.Window.three_mul_card_cheap_lift_le`), in place of the compression argument of
  Lemma 16.
* Each window is an OR chain sharing negations and prefix conjunctions, in place of a canonical
  DNF [pp. 22:19–22:20]; the locality is the same.
* The elements to cover are the positions of the ground list, rather than its distinct elements;
  repeated elements repeat a covering obligation and change no cover.

The reduction lands in Definition 1's positive instances (`MultiMCSP.rpHard_pos`); forgetting that
restriction gives hardness for Multi-MCSP itself (`MultiMCSP.rpHard`).

## Main results

* `Cslib.MultiMCSP.rpReducible_gapSetCover`: `GapSetCover 3` reduces to Multi-MCSP on positive
  instances.
* `Cslib.MultiMCSP.rpHard`, `Cslib.MultiMCSP.rpHard_pos`: every `NP` problem reduces to Multi-MCSP,
  and to Multi-MCSP on positive instances.
* `Cslib.MultiMCSP.NP_subset_BPP_of_mem_BPP`, `Cslib.MultiMCSP.NP_subset_coRP_of_mem_coRP`:
  conditional consequences. If Multi-MCSP is in `BPP` (respectively `coRP`), so is all of `NP`.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib

open Circuits Complexity PromiseProblem

namespace MultiMCSP

universe v

variable {σ : Signature.{v}} {I : Interpretation σ Bool} [Boolean.DeMorganBasis I]
  {α : Type} {encA : α ↪ List Bool}

/-- **`GapSetCover 3` reduces to Multi-MCSP** on Definition 1's positive instances, by a
polynomial-time randomized reduction with one-sided error [IlangoLoffOliveira2020, §4.2,
pp. 22:20–22:21], over any `Boolean.DeMorganBasis`. Soundness uses the library's union bound in
place of the source's Lemma 16. -/
theorem rpReducible_gapSetCover :
    RPReducible encSetCover encInstance (GapSetCover 3)
      ((ofSet (MultiMCSP I)).restrict {x | x.Positive}) :=
  Reduction.rpReducible_of_computableInPolyTime Reduction.computableInPolyTime_reduce

/-- **Multi-MCSP is `NP`-hard under randomized reductions, on positive instances**
[IlangoLoffOliveira2020, Theorem 4, p. 22:5]: every problem in `NP` reduces to Multi-MCSP
restricted to Definition 1's positive instances, by a polynomial-time randomized reduction with
one-sided error. `Boolean.DeMorgan.interpretation` gives the source's Definition 1 exactly. The
proof composes `GapSetCover_npHard` with `rpReducible_gapSetCover` (the library route). -/
theorem rpHard_pos : ∀ A ∈ NP encA,
    RPReducible encA encInstance (ofSet A) ((ofSet (MultiMCSP I)).restrict {x | x.Positive}) :=
  fun A hA => (GapSetCover_npHard (by norm_num : (1 : ℝ) < 3) encA A hA).trans_rpReducible
    rpReducible_gapSetCover

/-- **Multi-MCSP is `NP`-hard under randomized reductions** [IlangoLoffOliveira2020, Theorem 4,
p. 22:5]: every problem in `NP` reduces to Multi-MCSP by a polynomial-time randomized reduction
with one-sided error. This forgets the positivity restriction of `rpHard_pos`, which is the form
that matches Definition 1 exactly over `Boolean.DeMorgan.interpretation`; `Boolean.interpretation`
gives the library variant with constants. The proof is the library route of `rpHard_pos`. -/
theorem rpHard : ∀ A ∈ NP encA, RPReducible encA encInstance (ofSet A) (ofSet (MultiMCSP I)) :=
  fun A hA => (rpHard_pos (I := I) A hA).of_subset Set.inter_subset_left Set.inter_subset_left

/-- **If Multi-MCSP is in `BPP`, then `NP ⊆ BPP`.** A conditional consequence of `rpHard`; the
source does not state it separately. -/
theorem NP_subset_BPP_of_mem_BPP (h : MultiMCSP I ∈ BPP encInstance) : NP encA ⊆ BPP encA :=
  NP_subset_BPP_of_forall_rpReducible rpHard (ofSet_mem_PromiseBPP.mpr h)

/-- **If Multi-MCSP is in `coRP`, then `NP ⊆ coRP`.** A conditional consequence of `rpHard`, whose
one-sided error preserves `coRP`; the source does not state it separately. -/
theorem NP_subset_coRP_of_mem_coRP (h : MultiMCSP I ∈ coRP encInstance) : NP encA ⊆ coRP encA :=
  NP_subset_coRP_of_forall_rpReducible rpHard (ofSet_mem_PromiseCoRP.mpr h)

end MultiMCSP

end Cslib
