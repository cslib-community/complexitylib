/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Probabilistic.Oracle.Composition
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Strict PPT list folds

An ordinary `List.foldlM` is strict PPT when its list and initial accumulator are computable in
polynomial time, its step is strict PPT, and every supported step increases the encoded
accumulator by at most a constant. The oracle rule charges request construction and reply access,
and preserves shared oracle state. The closed rule specializes it without introducing a second
fold implementation.

## Main results

* `Cslib.Probability.IsOraclePPTOn.foldlM_of_bounded_growth`: certify an oracle list fold.
* `Cslib.Probability.IsPPTOn.foldlM_of_bounded_growth`: certify a closed list fold.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

private def foldStep {ι : Type} {spec : OracleSpec ι} {Item Acc : Type} (fallback : Item)
    (step : Acc → Item → OracleComp spec Acc) (state : List Item × Acc) :
    OracleComp spec (List Item × Acc) :=
  (fun next => (state.1.tail, next)) <$> step state.2 (state.1.headD fallback)

private theorem iterate_foldStep_eq_foldlM {ι : Type} {spec : OracleSpec ι} {Item Acc : Type}
    (fallback : Item) (step : Acc → Item → OracleComp spec Acc) (list : List Item) (acc : Acc) :
    Prod.snd <$> OracleComp.iterate list.length (foldStep fallback step) (list, acc) =
      list.foldlM step acc := by
  induction list generalizing acc with
  | nil => simp
  | cons item rest ih =>
    simp [OracleComp.iterate_succ_bind, foldStep, List.foldlM_cons,
      ← ih, map_bind, bind_map_left]

/-- Fold a strict oracle PPT step over an efficiently computed list. Constant growth bounds every
supported outcome, including under arbitrary external replies. The fallback only totalizes the
internal loop step; an empty list never executes it. -/
theorem IsOraclePPTOn.foldlM_of_bounded_growth
    {Operation α Item Acc : Type} [DecidableEq Operation]
    {input : α ↪ List Bool} {element : Item ↪ List Bool} {output : Acc ↪ List Bool}
    (fallback : Item) {list : α → List Item} {initial : α → Acc}
    {step : Acc → Item → WordOracleComp Operation Acc}
    (hlist : ComputableInPolyTime list input (encList element))
    (hinitial : ComputableInPolyTime initial input output)
    (hstep : IsOraclePPTOn (encPair output element) output (Function.uncurry step))
    {growth : ℕ} (hgrowth : ∀ acc item, ∀ next ∈ OracleComp.support (step acc item),
      (output next).length ≤ (output acc).length + growth) :
    IsOraclePPTOn input output (fun a => (list a).foldlM step (initial a)) := by
  have hcount : ComputableInPolyTime (fun a => (list a).length) input encUnary :=
    (ComputableInPolyTime.length_list element).comp hlist
  have hprepare : ComputableInPolyTime
      (fun state : List Item × Acc => (state.2, state.1.headD fallback))
      (encPair (encList element) output) (encPair output element) :=
    (ComputableInPolyTime.snd _ _).prod
      ((ComputableInPolyTime.headD fallback).comp (ComputableInPolyTime.fst _ _))
  have htail : ComputableInPolyTime
      (fun state : List Item × Acc => state.1.tail)
      (encPair (encList element) output) (encList element) :=
    .of_tidy ((ComputableTidilyInPolyTime.listTail element).comp
      (ComputableTidilyInPolyTime.fst _ _))
  have hloopStep : IsOraclePPTOn (encPair (encList element) output)
      (encPair (encList element) output) (foldStep fallback step) :=
    (hstep.preprocess' hprepare).pair' htail
  have hloop := IsOraclePPTOn.iterate_of_bounded_growth' hcount (hlist.prod hinitial) hloopStep
    (growth := growth) fun ⟨items, acc⟩ next hnext => by
      obtain ⟨nextAcc, hnextAcc, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      have htail : (encList element items.tail).length ≤ (encList element items).length :=
        ((List.tail_sublist items).flatMap (frame ∘ element)).length_le
      have hacc := hgrowth acc (items.headD fallback) nextAcc hnextAcc
      simp only [encPair_apply, List.length_append, length_frame]
      omega
  simpa only [iterate_foldStep_eq_foldlM] using
    hloop.map' (ComputableInPolyTime.snd (encList element) output)

/-- Fold a strict PPT step over an efficiently computed list, with a constant bound on the
encoded accumulator's growth on every supported execution. -/
theorem IsPPTOn.foldlM_of_bounded_growth
    {α Item Acc : Type}
    {input : α ↪ List Bool} {element : Item ↪ List Bool} {output : Acc ↪ List Bool}
    (fallback : Item) {list : α → List Item} {initial : α → Acc}
    {step : Acc → Item → ProbComp Acc}
    (hlist : ComputableInPolyTime list input (encList element))
    (hinitial : ComputableInPolyTime initial input output)
    (hstep : IsPPTOn (encPair output element) output (Function.uncurry step))
    {growth : ℕ} (hgrowth : ∀ acc item,
      ∀ next ∈ (ProbComp.eval (step acc item)).support,
      (output next).length ≤ (output acc).length + growth) :
    IsPPTOn input output (fun a => (list a).foldlM step (initial a)) := by
  have hloop := IsOraclePPTOn.foldlM_of_bounded_growth (Operation := Empty) fallback
    (step := fun acc item => ProbOracleComp.sample (step acc item))
    hlist hinitial hstep.isOraclePPTOn
    (fun acc item next hnext => hgrowth acc item next
      ((ProbOracleComp.support_sample _).subset hnext))
  have hsample (items : List Item) (acc : Acc) :
      ProbOracleComp.sample (spec := fun _ : Empty × List Bool => List Bool)
        (items.foldlM step acc) =
      items.foldlM (fun acc item => ProbOracleComp.sample (step acc item)) acc := by
    induction items generalizing acc with
    | nil => rfl
    | cons item rest ih =>
      simp only [List.foldlM_cons, ProbOracleComp.sample_bind, ih]
  apply IsOraclePPTOn.isPPTOn
  simpa only [← hsample] using hloop

end Cslib.Probability
