/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Computability.Probabilistic.Sampling
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.RejectionSampling
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Probability.PMF.Map

/-!
# Uniform strict PPT certificates for capped block rejection

Capped block-rejection programs (`sampleBlockTrials`, `sampleSeededTrials`, `sampleBlockCapped`)
are uniformly strict probabilistic polynomial time (`Cslib.Probability.IsPPTOn`) whenever the
per-trial bit width and the trial cap are computed in unary (`encUnary`) and the single-block
decoder `attempt` is deterministic polynomial time (`ComputableInPolyTime`).

On words of length `trials * width`, `BlockRejectionSpec.decodeTrials` agrees with folding over
`Cslib.BitString.listRows trials width` while keeping the first `some` result. Once a block
succeeds, later steps leave the optional accumulator unchanged, so its encoded length never
accumulates across trials.

## Main results

* `Cslib.Probability.BlockRejectionSpec.decodeTrials_eq_foldl_listRows`: row-fold representation of
  `decodeTrials` on words of length at least `trials * width`.
* `Cslib.Probability.isPPTOn_sampleSeededTrials`, `Cslib.Probability.isPPTOn_sampleBlockTrials`:
  strict PPT certificates for capped `t`-trial block rejection.
* `Cslib.Probability.isPPTOn_sampleBlockCapped`: strict PPT certificate for capped rejection with a
  computed fallback value.
-/

public section

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM ComputableInPolyTime

namespace BlockRejectionSpec

private theorem foldl_elim_some {α : Type} (attempt : List Bool → Option α) (a : α) :
    ∀ rows : List (List Bool),
      rows.foldl (fun acc row => acc.elim (attempt row) some) (some a) = some a
  | [] => rfl
  | _ :: rs => foldl_elim_some attempt a rs

/-- On any bit string of length at least `trials * spec.width`, `decodeTrials` agrees with folding
over `BitString.listRows trials spec.width`. -/
theorem decodeTrials_eq_foldl_listRows {α : Type} (spec : BlockRejectionSpec α) :
    ∀ (trials : ℕ) {w : List Bool}, trials * spec.width ≤ w.length →
      spec.decodeTrials trials w =
        (BitString.listRows trials spec.width w).foldl
          (fun acc row => acc.elim (spec.attempt row) some) none
  | 0, w, _ => by simp [BitString.listRows]
  | t + 1, w, hw => by
    have hw1 : spec.width ≤ w.length := by
      rw [Nat.succ_mul] at hw
      omega
    have hsplit : w = w.take spec.width ++ w.drop spec.width := (List.take_append_drop _ _).symm
    have hlen : (w.take spec.width).length = spec.width := List.length_take_of_le hw1
    have hrows : BitString.listRows (t + 1) spec.width w =
        w.take spec.width :: BitString.listRows t spec.width (w.drop spec.width) := by
      conv_lhs => rw [hsplit]
      exact BitString.listRows_succ_append t spec.width hlen (w.drop spec.width)
    rw [decodeTrials_succ, hrows, List.foldl_cons, Option.elim_none]
    cases hatt : spec.attempt (w.take spec.width) with
    | some a => exact (foldl_elim_some spec.attempt a _).symm
    | none =>
      refine decodeTrials_eq_foldl_listRows spec t ?_
      rw [List.length_drop]
      rw [Nat.succ_mul] at hw
      omega

end BlockRejectionSpec

private def decodeRows {β : Type} (spec : BlockRejectionSpec β) (trials : ℕ) (w : List Bool) :
    Option β :=
  (BitString.listRows trials spec.width w).foldl
    (fun acc row => acc.elim (spec.attempt row) some) none

private theorem computableInPolyTime_decodeRows {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {spec : α → BlockRejectionSpec β} {trials : α → ℕ}
    (htrials : ComputableInPolyTime trials input encUnary)
    (hwidth : ComputableInPolyTime (fun a => (spec a).width) input encUnary)
    (hattempt : ComputableInPolyTime (fun p : α × List Bool => (spec p.1).attempt p.2)
      (encPair input encBits) (encOption output)) :
    ComputableInPolyTime (fun p : α × List Bool => decodeRows (spec p.1) (trials p.1) p.2)
      (encPair input encBits) (encOption output) := by
  let encIn := encPair input encBits
  have hfst : ComputableInPolyTime Prod.fst encIn input := fst input encBits
  have hsnd : ComputableInPolyTime Prod.snd encIn encBits := snd input encBits
  have hlist : ComputableInPolyTime
      (fun p : α × List Bool => BitString.listRows (trials p.1) ((spec p.1).width) p.2)
      encIn (encList encBits) :=
    bitsRowsWithInput (htrials.comp hfst) (hwidth.comp hfst) hsnd
  have hinit : ComputableInPolyTime (fun _ : α × List Bool => (none : Option β))
      encIn (encOption output) :=
    const none
  let encStep := encPair (encPair encIn (encOption output)) encBits
  have hacc : ComputableInPolyTime (fun q : ((α × List Bool) × Option β) × List Bool => q.1.2)
      encStep (encOption output) :=
    (fst (encPair encIn (encOption output)) encBits).snd'
  have hcall : ComputableInPolyTime
      (fun q : ((α × List Bool) × Option β) × List Bool => (spec q.1.1.1).attempt q.2)
      encStep (encOption output) :=
    hattempt.comp (((fst (encPair encIn (encOption output)) encBits).fst'.fst').prod (snd _ _))
  have hbody : ComputableInPolyTime
      (fun r : (((α × List Bool) × Option β) × List Bool) × β => (some r.2 : Option β))
      (encPair encStep output) (encOption output) :=
    (optionSome output).comp (snd encStep output)
  have hstep : ComputableInPolyTime
      (fun q : ((α × List Bool) × Option β) × List Bool =>
        q.1.2.elim ((spec q.1.1.1).attempt q.2) some)
      encStep (encOption output) :=
    optionElimWithInput hacc hcall hbody
  obtain ⟨ca, da, ha⟩ := hattempt.polyBounded_length.exists_le
  obtain ⟨cw, dw, hw⟩ := hwidth.polyBounded_length.exists_le
  let growth : α × List Bool → ℕ := fun p =>
    ca * (2 * (input p.1).length + cw * ((input p.1).length + 1) ^ dw + 3) ^ da
  have hpoly : PolyBounded (fun p : α × List Bool => (encIn p).length) growth := by
    have hp1 : PolyBounded (fun p : α × List Bool => (encIn p).length)
        (fun p => (input p.1).length) :=
      hfst.polyBounded_length
    have hw_pb : PolyBounded (fun p : α × List Bool => (encIn p).length)
        (fun p => cw * ((input p.1).length + 1) ^ dw) :=
      (PolyBounded.const cw).mul ((hp1.add (.const 1)).pow dw)
    have hinner : PolyBounded (fun p : α × List Bool => (encIn p).length)
        (fun p => 2 * (input p.1).length + cw * ((input p.1).length + 1) ^ dw + 3) :=
      (((PolyBounded.const 2).mul hp1).add hw_pb).add (.const 3)
    exact (PolyBounded.const ca).mul (hinner.pow da)
  refine foldlWithInput_of_bounded_growth hinit ⟨hlist, hstep, inferInstance, inferInstance⟩
    ⟨hpoly, fun p state row hrow => ?_⟩
  cases state with
  | some b =>
    simp only [Option.elim_some]
    omega
  | none =>
    simp only [Option.elim_none]
    have hrow_len : row.length = (spec p.1).width := BitString.length_of_mem_listRows hrow
    have hw_le : (spec p.1).width ≤ cw * ((input p.1).length + 1) ^ dw := by
      simpa only [encUnary_apply, List.length_replicate] using hw p.1
    have ha_le := ha (p.1, row)
    simp only [length_encPair, encBits, Function.Embedding.coe_refl, id_eq, hrow_len] at ha_le
    have hbase : 2 * (input p.1).length + 1 + (spec p.1).width + 1 ≤
        2 * (input p.1).length + cw * ((input p.1).length + 1) ^ dw + 3 := by omega
    have hg : (encOption output ((spec p.1).attempt row)).length ≤ growth p :=
      ha_le.trans (Nat.mul_le_mul_left ca (Nat.pow_le_pow_left hbase da))
    omega

/-- Single-tape capped block rejection `sampleSeededTrials` is uniformly strict PPT for unary
`trials` and `width` and polynomial-time `attempt`. -/
theorem isPPTOn_sampleSeededTrials {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {spec : α → BlockRejectionSpec β} {trials : α → ℕ}
    (htrials : ComputableInPolyTime trials input encUnary)
    (hwidth : ComputableInPolyTime (fun a => (spec a).width) input encUnary)
    (hattempt : ComputableInPolyTime (fun p : α × List Bool => (spec p.1).attempt p.2)
      (encPair input encBits) (encOption output)) :
    IsPPTOn input (encOption output) (fun a => sampleSeededTrials (spec a) (trials a)) := by
  have hcount : ComputableInPolyTime (fun a => trials a * (spec a).width) input encUnary :=
    .of_tidy (ComputableTidilyInPolyTime.unary_mul.comp (htrials.tidy.prod hwidth.tidy))
  have hdecode := computableInPolyTime_decodeRows htrials hwidth hattempt
  have hseeded := IsPPTOn.of_seeded hcount hdecode
  refine hseeded.congr fun a => ?_
  simp only [sampleSeededTrials, ProbComp.eval_map, BitString.eval_sampleList]
  apply PMF.map_congr_on_support
  intro w hw
  have hlen : w.length = trials a * (spec a).width :=
    BitString.length_of_mem_support_uniformList hw
  exact (BlockRejectionSpec.decodeTrials_eq_foldl_listRows (spec a) (trials a) hlen.ge).symm

/-- Sequential capped block rejection `sampleBlockTrials` is uniformly strict PPT under the same
hypotheses. -/
theorem isPPTOn_sampleBlockTrials {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {spec : α → BlockRejectionSpec β} {trials : α → ℕ}
    (htrials : ComputableInPolyTime trials input encUnary)
    (hwidth : ComputableInPolyTime (fun a => (spec a).width) input encUnary)
    (hattempt : ComputableInPolyTime (fun p : α × List Bool => (spec p.1).attempt p.2)
      (encPair input encBits) (encOption output)) :
    IsPPTOn input (encOption output) (fun a => sampleBlockTrials (spec a) (trials a)) :=
  (isPPTOn_sampleSeededTrials htrials hwidth hattempt).congr fun a =>
    (eval_sampleBlockTrials_eq_seeded (spec a) (trials a)).symm

/-- Capped block rejection with a polynomial-time fallback value is uniformly strict PPT. -/
theorem isPPTOn_sampleBlockCapped {α β : Type} {input : α ↪ List Bool}
    {output : β ↪ List Bool} {spec : α → BlockRejectionSpec β} {fallback : α → β}
    {trials : α → ℕ}
    (htrials : ComputableInPolyTime trials input encUnary)
    (hwidth : ComputableInPolyTime (fun a => (spec a).width) input encUnary)
    (hattempt : ComputableInPolyTime (fun p : α × List Bool => (spec p.1).attempt p.2)
      (encPair input encBits) (encOption output))
    (hfallback : ComputableInPolyTime fallback input output) :
    IsPPTOn input output (fun a => sampleBlockCapped (spec a) (fallback a) (trials a)) := by
  have hget : ComputableInPolyTime (fun p : α × Option β => p.2.getD (fallback p.1))
      (encPair input (encOption output)) output :=
    optionGetDWithInput (snd input (encOption output))
      (hfallback.comp (fst input (encOption output)))
  have h := IsPPTOn.map_with (f := fun a (o : Option β) => o.getD (fallback a))
    (isPPTOn_sampleSeededTrials htrials hwidth hattempt) hget
  simpa only [sampleBlockCapped, bind_pure_comp] using h

end Cslib.Probability
