/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeResidualOracle
public import CslibFrontier.Probability.StochasticOracle.NativeRetention.GuardedStartup
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Mathlib.Tactic

/-!
# Runtime source-role routing for the residual selector

[Wang2027], Theorem 6 setup (2)--(3), PDF pp. 12--13. The PTM knows
which specialist accepts each subuniverse, but not the hidden exact covers.
The runtime private input therefore contains the role subuniverses, framed
before any response history. The native planner compares the actual retained
residual with those subuniverses and issues the corresponding preformed query.
It does not assume that original point labels order the specialist roles.

`controller` uses the approved clockless feedback compiler and the original
`GuardedStartup.encoding` input used by the native optimum. The adaptive and
all-specialist modes are two fixed programs on that same input, not separately
compiled response-dependent continuations. This module alone does not establish
source attainment or an optimum equality.

## Main definitions

* `roleWord`, `roles`: framed runtime role metadata and its actual decoding.
* `slots`, `request`: pre-response routing from original instance and retained history.
* `controller`: uniform native code for either source strategy.

## Main results

* `roles_afterReply`: response updates preserve the original routing metadata.
* `computable_request`: actual native compilation of the routing computation.
* `controller_law`: clockless whole-state joint execution from original input.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeResidualRouting
open Turing Turing.MultiTapeTM NativeOpenExecution NativeRetention ConcurrentBatch
open Turing.MultiTapeTM.ComputableInPolyTime

/-- Framed list of role universes, each encoded as a list of unary point labels.
No candidate family, exact-cover witness or execution state is included. -/
@[expose] def roleWord (universes : List (List ℕ)) : Word :=
  frame (encList (encList encUnary) universes)

/-- Decode the original role metadata at the front of the private runtime word.
The trailing frames added by responses are excluded by `unframe`. -/
@[expose] def roles (state : RuntimeControl.State) : List (List ℕ) :=
  (Decoder.list (Decoder.list Decoder.unary)).decode (unframe state.privateWord)

/-- Equality of subuniverses ignores list order and repeated point labels. -/
@[expose] def sameUniverse (xs ys : List ℕ) : Bool :=
  xs.all (fun e => decide (e ∈ ys)) && ys.all (fun e => decide (e ∈ xs))

/-- The executed comparison means equality of the two finite subuniverses. -/
theorem sameUniverse_eq (xs ys : List ℕ) :
    sameUniverse xs ys = true ↔ xs.toFinset = ys.toFinset := by
  simp only [sameUniverse, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    ext e
    simpa using ⟨h.1 e, h.2 e⟩
  · intro h
    constructor
    · intro e he
      have hm : e ∈ ys.toFinset := h ▸ List.mem_toFinset.mpr he
      exact List.mem_toFinset.mp hm
    · intro e he
      have hm : e ∈ xs.toFinset := h.symm ▸ List.mem_toFinset.mpr he
      exact List.mem_toFinset.mp hm


/-- The first framed role table survives arbitrary appended response words. -/
theorem roles_afterReply (state : RuntimeControl.State) (universes : List (List ℕ))
    (h : state.privateWord = roleWord universes) (reply : Word) :
    roles (RuntimeControl.afterReply state reply) = universes := by
  simp [roles, RuntimeControl.afterReply, h, roleWord, unframe_frame_append, Decoder.decode_enc]

/-- First query the near role with two turns; with one turn and no earlier
report query all specialists. Otherwise query only a specialist whose known
subuniverse equals the actual retained residual. -/
@[expose] def selected (state : RuntimeControl.State) (i : ℕ) : Bool :=
  if state.turns = 2 then decide (i = 0) else
    decide (state.turns = 1) && decide (0 < i) &&
      (state.work.history.isEmpty || sameUniverse ((roles state).getD i [])
        (NativeResidualSelector.residual state))

/-- All queries use the original WSC data and the known universe of their role.
The requests are formed before any response of this batch is sampled. -/
@[expose] def slots (state : RuntimeControl.State) : Fin state.work.opportunities → Option Word :=
  fun i => if selected state i.val then
    some (NativeResidualSelector.queryEncoding
      ⟨state.work.system, (roles state).getD i.val []⟩) else none

/-- Actual source batch bytes, from one complete runtime routing scan. -/
@[expose] def request (state : RuntimeControl.State) : Word :=
  (List.range state.work.opportunities).flatMap fun i =>
    if selected state i then true :: Kolmogorov.selfDelimitingCode
      (NativeResidualSelector.queryEncoding ⟨state.work.system, (roles state).getD i []⟩)
    else [false]

/-- The native list scan produces exactly the source codec for all runtime slots. -/
theorem request_eq (state : RuntimeControl.State) :
    request state = encodeSlots state.work.opportunities (slots state) := by
  rw [encodeSlots_flatMap, List.ofFn_eq_map, List.flatMap_map]
  unfold request
  rw [← List.map_coe_finRange_eq_range, List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  simp only [slots]
  split_ifs <;> rfl

private theorem fields : ComputableInPolyTime
    (fun s : RuntimeControl.State => (s.work, s.requests, s.privateWord,
      s.turns, s.opportunities, s.allotments)) RuntimeControl.encoding
    (encPair Packets.encWork (encPair (encList encBits)
      (encPair encBits (encPair encUnary (encPair encUnary encUnary))))) := .of_eq fun _ => rfl

private theorem computable_roles : ComputableInPolyTime roles RuntimeControl.encoding
    (encList (encList encUnary)) :=
  (Decoder.list (Decoder.list Decoder.unary)).computableInPolyTime.comp
    (ComputableInPolyTime.unframe.comp RuntimeControl.computable_privateWord)

private theorem computable_sameUniverse : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => sameUniverse p.1 p.2)
    (encPair (encList encUnary) (encList encUnary)) encBool := by
  let enc := encPair (encList encUnary) (encList encUnary)
  have hfst : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.1) enc
      (encList encUnary) := fst _ _
  have hsnd : ComputableInPolyTime (fun p : List ℕ × List ℕ => p.2) enc
      (encList encUnary) := snd _ _
  have he : ComputableInPolyTime (fun p : (List ℕ × List ℕ) × ℕ => p.2)
      (encPair enc encUnary) encUnary := snd _ _
  have hleft := allWithInput (test := fun p e => decide (e ∈ p.2)) hfst
    (decide_mem (hsnd.comp (fst _ _)) he)
  have hright := allWithInput (test := fun p e => decide (e ∈ p.1)) hsnd
    (decide_mem (hfst.comp (fst _ _)) he)
  exact bool_and.comp (hleft.prod hright)

private theorem computable_selected : ComputableInPolyTime
    (fun p : RuntimeControl.State × ℕ => selected p.1 p.2)
    (encPair RuntimeControl.encoding encUnary) encBool := by
  have hf : ComputableInPolyTime (fun p : RuntimeControl.State × ℕ => p.1)
      (encPair RuntimeControl.encoding encUnary) RuntimeControl.encoding := fst _ _
  have hi : ComputableInPolyTime (fun p : RuntimeControl.State × ℕ => p.2)
      (encPair RuntimeControl.encoding encUnary) encUnary := snd _ _
  have ht := fields.snd'.snd'.snd'.fst'.comp hf
  have hh := Packets.work_fields.snd'.snd'.comp (fields.fst'.comp hf)
  have hr := listGetDWithInput (computable_roles.comp hf) hi ([] : List ℕ)
  have he := (listIsEmpty (encA := encBits)).comp hh
  have hm := computable_sameUniverse.comp
    (hr.prod (NativeResidualSelector.computable_residual.comp hf))
  have hz := decide_eq' hi (const (0 : ℕ))
  have hp := unary_lt.comp ((const (0 : ℕ)).prod hi)
  have hlast := bool_and.comp ((bool_and.comp
    ((decide_eq' ht (const (1 : ℕ))).prod hp)).prod (bool_or.comp (he.prod hm)))
  exact ite_decide (decide_eq' ht (const (2 : ℕ))) hz hlast

private theorem computable_queryAt : ComputableInPolyTime
    (fun p : RuntimeControl.State × ℕ => NativeResidualSelector.queryEncoding
      ⟨p.1.work.system, (roles p.1).getD p.2 []⟩)
    (encPair RuntimeControl.encoding encUnary) encBits := by
  have hf : ComputableInPolyTime (fun p : RuntimeControl.State × ℕ => p.1)
      (encPair RuntimeControl.encoding encUnary) RuntimeControl.encoding := fst _ _
  have hi : ComputableInPolyTime (fun p : RuntimeControl.State × ℕ => p.2)
      (encPair RuntimeControl.encoding encUnary) encUnary := snd _ _
  have hs := Packets.work_fields.fst'.comp (fields.fst'.comp hf)
  have hr := listGetDWithInput (computable_roles.comp hf) hi ([] : List ℕ)
  have hpair := hs.prod hr
  exact hpair.of_enc_eq fun _ => rfl

/-- Native polynomial routing over runtime role metadata and actual residuals. -/
theorem computable_request : ComputableInPolyTime request
    (RuntimeControl.encoding.trans NativeReplyContext.framedBits) encBits := by
  have hcount := Packets.work_fields.snd'.fst'.comp fields.fst'
  have hbody : ComputableInPolyTime
      (fun p : RuntimeControl.State × ℕ => if selected p.1 p.2 then
        true :: Kolmogorov.selfDelimitingCode (NativeResidualSelector.queryEncoding
          ⟨p.1.work.system, (roles p.1).getD p.2 []⟩) else [false])
      (encPair RuntimeControl.encoding encUnary) encBits :=
    computable_selected.ite (bitsCons (const true)
      (selfDelimitingCode.comp computable_queryAt)) (const [false])
  have he : ComputableInPolyTime request RuntimeControl.encoding encBits :=
    flatMapToBitsWithInput (ComputableInPolyTime.range.comp hcount) hbody
  exact he.comp RuntimeControl.computable_unframe

/-- Both strategies start from the same original runtime input. Their local
budgets are fixed by the chosen algorithm, without installing a prepared context. -/
@[expose] def initial (adaptive : Bool) (data : GuardedStartup.Input) : RuntimeControl.State :=
  { GuardedStartup.state data with turns := if adaptive then 2 else 1, allotments := 2 }

private theorem computable_initial (adaptive : Bool) : ComputableInPolyTime (initial adaptive)
    GuardedStartup.encoding RuntimeControl.encoding := by
  have hf := fields.comp GuardedStartup.computable_state
  have ht : ComputableInPolyTime (fun _ : GuardedStartup.Input => if adaptive then (2 : ℕ) else 1)
      GuardedStartup.encoding encUnary := const _
  have ha : ComputableInPolyTime (fun _ : GuardedStartup.Input => (2 : ℕ))
      GuardedStartup.encoding encUnary := const _
  have he := hf.fst'.prod (hf.snd'.fst'.prod (hf.snd'.snd'.fst'.prod
    (ht.prod (hf.snd'.snd'.snd'.snd'.fst'.prod ha))))
  exact he.of_enc_eq fun _ => rfl

/-- One actual native implementation, with a derived whole-state joint law. -/
structure Controller (adaptive : Bool) where
  /-- Ordinary work tapes. -/
  tapes : ℕ
  /-- Finite native controls. -/
  Controls : Type
  /-- Control finiteness. -/
  finite : Finite Controls
  /-- Actual program, uniform in runtime instance and roles. -/
  program : MultiTapePTM tapes Bool Controls Unit
  /-- Reserved context tape. -/
  context : Fin tapes
  /-- Actual clockless law from original input, with complete shared memory. -/
  law : ∀ (P : Type) (env : Environment Unit P) (data : GuardedStartup.Input)
    (memory : Memory Unit P),
    (NativeUnboundedExecution.terminal program env
      ⟨program.initialConfig (GuardedStartup.encoding data), memory⟩).map
        (Option.map (NativeReplyContext.observe context)) =
      (Feedback.run env (if adaptive then 2 else 1) (initial adaptive data)
        (fun _ => ⟨[], [], 0⟩) memory request).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state, outcome.memory⟩ : NativeReplyContext.Observation P)

private theorem controller_nonempty (adaptive : Bool) : Nonempty (Controller adaptive) := by
  obtain ⟨time, space, _, _, hc⟩ := computable_initial adaptive
  obtain ⟨tapes, R, hR, code, context, hlaw⟩ :=
    Feedback.exists_native_controller_from_state GuardedStartup.encoding (initial adaptive)
      (fun x => time (GuardedStartup.encoding x).length)
      (fun x => space (GuardedStartup.encoding x).length) hc request computable_request
  exact ⟨⟨tapes, R, hR, code, context, fun P env data memory => by
    simpa only [initial] using hlaw P env data memory⟩⟩

/-- One fixed program per strategy; selection does not recompile continuations
from externally supplied responses or hidden exact covers. -/
def controller (adaptive : Bool) : Controller adaptive :=
  Classical.choice (controller_nonempty adaptive)

/-- The named implementation retains its actual joint tape-output/oracle-memory law. -/
theorem controller_law (adaptive : Bool) (P : Type) (env : Environment Unit P)
    (data : GuardedStartup.Input) (memory : Memory Unit P) :
    (NativeUnboundedExecution.terminal (controller adaptive).program env
      ⟨(controller adaptive).program.initialConfig (GuardedStartup.encoding data), memory⟩).map
        (Option.map (NativeReplyContext.observe (controller adaptive).context)) =
      (Feedback.run env (if adaptive then 2 else 1) (initial adaptive data)
        (fun _ => ⟨[], [], 0⟩) memory request).map fun outcome =>
          some (⟨tapeOfList (RuntimeControl.packet outcome.state),
            RuntimeControl.result outcome.state, outcome.memory⟩ :
              NativeReplyContext.Observation P) :=
  (controller adaptive).law P env data memory

end Cslib.Probability.StochasticOracle.NativeResidualRouting
