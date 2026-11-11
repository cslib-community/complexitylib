/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchPlanner
import Mathlib.Tactic

/-!
# Source admission of the executed native fresh-block controller

[Wang2027], model pp. 4--6, Theorem 5 p. 12/App. A.5 p. 16. Every live iteration
of the constructed block planner decodes to a preformed nonempty batch, consumes
fresh labels and is accepted by the same stateful concurrent oracle. Per-call
cutoffs and the configured whole-run allotment imply deadline feasibility; a
scalar reservation counter is not treated as an observed clock. Native local
computation remains outside this physical oracle-duration convention.

The theorem concerns the concrete finite labeled block scheduler, not arbitrary
scheduler compilation or the source productivity/expected-bill envelopes.

## Main results

* `admit_request`, `run_aligned`: derived admission/accounting for every supported round.
* `result_provenance`: actual computed output families come from returned source calls.
* `admitted_controller`: the constructed native program has the source invariant.
* `selectionOnly_controller`: every-prefix native selection admission is derived.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchAdmission
open Turing Turing.MultiTapeTM Turing.MultiTapeMachine NativeOpenExecution ConcurrentBatch
open scoped NNReal
variable {n : ℕ} {Private : Type}

/-- Derived synchronization between runtime counters/history and actual accepted
source events. `RuntimeControl.requests` remains a cache of old State frames;
actual source requests are the native ledger's batch-codec words. -/
structure Aligned (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private)) : Prop where
  /-- Same actual token/duration/provenance ledger as the concurrent source. -/
  invariant : NativeBatch.Invariant limits memory
  /-- The native report parser reads the source opportunity interface size. -/
  opportunityInterface : state.work.opportunities = n
  /-- Each transaction consumes one consecutive block allowance, not one label. -/
  opportunityCount : state.opportunities + memory.privateState.history.length = n
  /-- Remaining turns agree with the actual accepted source turn count. -/
  turnCount : state.turns + memory.privateState.history.length = budget
  /-- Source labels consumed so far are exactly the earlier blocks. -/
  used : memory.privateState.used =
    BatchPlanner.consumed n width memory.privateState.history.length
  /-- The actual duration bound follows from configured call cutoffs. -/
  duration : memory.privateState.elapsed ≤ memory.privateState.history.length * ell
  /-- Stored replies are actual oracle replies, rather than supplied proposals. -/
  history : state.work.history = memory.events.map (fun e => e.reply.word)
  /-- There are no rejected or fabricated source turns in the actual native ledger. -/
  events : memory.events.length = memory.privateState.history.length
  /-- Every stored report has the source parser's exact candidate-family meaning. -/
  packets : ∀ m word, word ∈ state.work.history →
    Packets.families n m word = (parseProposals n m word).map sourceIndices
  /-- Exact receipt order and full raw reports, including cancellation/metadata.
  This strengthens provenance-set equality to a history law usable by retention. -/
  reports : state.work.history =
    memory.privateState.history.map (fun receipt => (replyOf receipt).word)

/-- Fresh original input, not a preinstalled State/history, establishes alignment. -/
theorem initial_aligned (limits : Limits n) (width : ℕ) (ell : ℝ≥0)
    (data : GuardedStartup.Input) (seed : Private) (hn : data.startup.opportunities = n) :
    Aligned limits width data.startup.turns ell (GuardedStartup.state data)
      ⟨ConcurrentBatch.initial seed, []⟩ := by
  refine ⟨NativeBatch.initial_invariant limits seed, hn, ?_, ?_, ?_, ?_, rfl, rfl,
    by intros; contradiction, rfl⟩
  · simpa [GuardedStartup.state, RuntimeControl.initial, ConcurrentBatch.initial] using hn
  · simp [GuardedStartup.state, RuntimeControl.initial, ConcurrentBatch.initial]
  · simp [ConcurrentBatch.initial, BatchPlanner.consumed]
  · simp [ConcurrentBatch.initial]

private theorem stage_eq (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (h : Aligned limits width budget ell state memory) :
    BatchPlanner.stage n state = memory.privateState.history.length := by
  have hc := h.opportunityCount
  unfold BatchPlanner.stage
  omega

/-- The concrete planner passes the checked source guard before sampling, without
assuming request validity, acceptance, or a scheduler-realization contract. -/
theorem admit_request (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (hw : 0 < width) (hc : budget * width ≤ n) (ht : budget ≤ limits.turns)
    (he : 0 < ell) (hd : (budget : ℝ≥0) * ell ≤ limits.deadline)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory)
    (hs : RuntimeControl.stopped state = false) :
    ∃ batch : Batch n, batch.slots = BatchPlanner.slots n width state ∧
      admit limits memory.privateState (BatchPlanner.request n width state) = some batch := by
  have hstage := stage_eq limits width budget ell state memory ha
  have hturn := ha.turnCount
  have hlive : state.turns ≠ 0 := by
    intro hz
    simp [RuntimeControl.stopped, hz] at hs
  have hlt : memory.privateState.history.length < budget := by omega
  have hcap : BatchPlanner.stage n state * width < n := by
    rw [hstage]
    exact (Nat.mul_lt_mul_of_pos_right hlt hw).trans_le hc
  have htime : memory.privateState.elapsed < limits.deadline := by
    have hcast : (memory.privateState.history.length : ℝ≥0) < budget := by exact_mod_cast hlt
    exact (ha.duration.trans_lt (mul_lt_mul_of_pos_right hcast he)).trans_le hd
  have hdisj := BatchPlanner.fresh n width state
  rw [hstage, ← ha.used] at hdisj
  refine ⟨⟨BatchPlanner.slots n width state, BatchPlanner.nonempty n width state hw hcap⟩,
    rfl, ?_⟩
  unfold admit
  rw [BatchPlanner.decode_request n width state hw hcap]
  simp only [htime, (hlt.trans_le ht), hdisj, and_self, ↓reduceIte]

private theorem observe_duration_cutoff (limits : Limits n) (ell : ℝ≥0)
    (hcut : ∀ i, limits.cutoff i ≤ ell) (remaining : ℝ≥0) (b : Batch n)
    (paths : Fin n → CallTrace) : (observe limits remaining b paths).duration ≤ ell := by
  apply Finset.sup_le
  intro i _
  change (if (b.slots i).isSome then
    (paths i).stop (min (limits.cutoff i) remaining) else 0) ≤ ell
  split_ifs
  · exact ((paths i).stop_le _).trans ((min_le_left _ _).trans (hcut i))
  · exact zero_le

/-- One actual correlated source response advances exactly the computed block,
updates authenticated runtime history and retains the joint charged resources. -/
theorem after_reply_aligned (limits : Limits n) (sample : Sampler n Private)
    (width budget : ℕ) (ell : ℝ≥0) (hw : 0 < width) (hc : budget * width ≤ n)
    (ht : budget ≤ limits.turns) (he : 0 < ell)
    (hcut : ∀ i, limits.cutoff i ≤ ell) (hd : (budget : ℝ≥0) * ell ≤ limits.deadline)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory)
    (hs : RuntimeControl.stopped state = false) (reply : Reply) (next : ServerState n Private)
    (hr : (reply, next) ∈
      (environment limits sample ((), BatchPlanner.request n width state) memory).support) :
    Aligned limits width budget ell (RuntimeControl.afterReply state reply.word)
      (memory.record ((), BatchPlanner.request n width state) reply next) := by
  obtain ⟨batch, hslots, haccept⟩ :=
    admit_request limits width budget ell hw hc ht he hd state memory ha hs
  rcases batch with ⟨slots, nonempty⟩
  dsimp only at hslots
  subst slots
  have hinv := NativeBatch.serve_invariant limits sample memory ha.invariant
    (BatchPlanner.request n width state) reply next hr
  change (reply, next) ∈ (serve limits sample _ memory.privateState).support at hr
  rw [serve_accepted _ _ _ _ _ haccept, PMF.mem_support_map_iff] at hr
  obtain ⟨⟨paths, privateState⟩, _, hpair⟩ := hr
  cases hpair
  have hstage := stage_eq limits width budget ell state memory ha
  have hopps := ha.opportunityCount
  have hturn := ha.turnCount
  have hlive : state.turns ≠ 0 := by
    intro hz
    simp [RuntimeControl.stopped, hz] at hs
  have hpositive : state.opportunities ≠ 0 := by
    intro hz
    simp [RuntimeControl.stopped, hz] at hs
  refine ⟨hinv, ha.opportunityInterface, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RuntimeControl.afterReply, Memory.record, commit, List.length_cons]
    omega
  · simp only [RuntimeControl.afterReply, Memory.record, commit, List.length_cons]
    omega
  · simp only [Memory.record, commit, List.length_cons, observe]
    rw [ha.used, ← hstage, BatchPlanner.consumed_succ]
  · change memory.privateState.elapsed + (observe limits _ _ paths).duration ≤
      (memory.privateState.history.length + 1 : ℕ) * ell
    calc
      _ ≤ memory.privateState.history.length * ell + ell :=
        add_le_add ha.duration (observe_duration_cutoff limits ell hcut _ _ paths)
      _ = _ := by simp [add_mul]
  · simpa [RuntimeControl.afterReply, Memory.record] using congrArg
      (List.cons (replyOf (observe limits (limits.deadline - memory.privateState.elapsed)
        ⟨BatchPlanner.slots n width state, nonempty⟩ paths)).word) ha.history
  · simpa [Memory.record, commit] using congrArg Nat.succ ha.events
  · intro m word hword
    rcases List.mem_cons.mp hword with rfl | hword
    · simp only [replyOf, Packets.families_report, parseProposals_report]
    · exact ha.packets m word hword
  · simpa only [RuntimeControl.afterReply, Memory.record, commit, List.map_cons] using
      congrArg (List.cons (replyOf (observe limits
        (limits.deadline - memory.privateState.elapsed)
        ⟨BatchPlanner.slots n width state, nonempty⟩ paths)).word) ha.reports

/-- Actual retained-source input equals the validated source-history construction;
caller-supplied proposals do not acquire provenance. -/
theorem assemble_eq (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory) :
    Packets.assemble state.work = Selector.data n state.work.system
      ⟨state.work.history, false, state.requests, state.privateWord⟩ := by
  have hp : state.work.history.reverse.flatMap
      (Packets.families n state.work.system.rows.length) =
      state.work.history.reverse.flatMap (fun word =>
        (parseProposals n state.work.system.rows.length word).map sourceIndices) := by
    apply List.flatMap_congr
    intro word hword
    exact ha.packets _ word (List.mem_reverse.mp hword)
  simp only [Packets.assemble, ha.opportunityInterface, Selector.data, hp, List.map_flatMap]

/-- Every candidate in the computed output mask was actually returned by a
selected noncanceled source call. Standard WSC promises concern only the original
instance; provenance and successful output are not hypotheses. -/
theorem output_provenance (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory) (hx : Valid state.work.system) :
    outputFamily (Selector.data n state.work.system
      ⟨state.work.history, false, state.requests, state.privateWord⟩) ⊆
      NativeBatch.sourceAvailable state.work.system.rows.length memory.privateState.history := by
  have hp := Selector.provenance n state.work.system hx
    ⟨state.work.history, false, state.requests, state.privateWord⟩
  have hav : Selector.available n state.work.system.rows.length state.work.history =
      NativeBatch.nativeAvailable (n := n) state.work.system.rows.length memory.events := by
    rw [ha.history]
    induction memory.events with
    | nil => rfl
    | cons event events ih =>
      simp only [List.map_cons, Selector.available, NativeBatch.nativeAvailable, ih]
  obtain ⟨_, _, _, hsource⟩ := ha.invariant
  simpa only [hav, hsource] using hp

/-- Every family decoded from the actual final output word has source provenance,
including empty-ground success and failed-output normalization. -/
theorem result_provenance (limits : Limits n) (width budget : ℕ) (ell : ℝ≥0)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory) (hx : Valid state.work.system)
    (C : Finset (Fin state.work.system.rows.length))
    (hC : decodeFamily state.work.system.rows.length (RuntimeControl.result state) = some C) :
    C ⊆ NativeBatch.sourceAvailable state.work.system.rows.length memory.privateState.history := by
  unfold RuntimeControl.result Packets.decision at hC
  rw [assemble_eq limits width budget ell state memory ha] at hC
  split_ifs at hC with hc
  · dsimp only [Prod.snd] at hC
    have hout := decode_output (Selector.data n state.work.system
      ⟨state.work.history, false, state.requests, state.privateWord⟩)
    simp only [Selector.data] at hout hC
    rw [hout] at hC
    cases hC
    exact output_provenance limits width budget ell state memory ha hx
  · simp only [decodeFamily, List.length_nil] at hC
    split_ifs at hC
    cases hC
    simp

/-- Source alignment is preserved throughout the same repeated native kernel,
including cancellation, hidden correlation and computed early completion. -/
theorem run_aligned (limits : Limits n) (sample : Sampler n Private)
    (width budget : ℕ) (ell : ℝ≥0) (hw : 0 < width) (hc : budget * width ≤ n)
    (ht : budget ≤ limits.turns) (he : 0 < ell)
    (hcut : ∀ i, limits.cutoff i ≤ ell) (hd : (budget : ℝ≥0) * ell ≤ limits.deadline)
    (fuel : ℕ) (state : RuntimeControl.State) (channels : Unit → Channel Bool)
    (memory : Memory Unit (ServerState n Private))
    (ha : Aligned limits width budget ell state memory) (outcome : Feedback.Outcome _)
    (ho : outcome ∈ (Feedback.run (environment limits sample) fuel state channels memory
      (BatchPlanner.request n width)).support) :
    Aligned limits width budget ell outcome.state outcome.memory := by
  induction fuel generalizing state channels memory outcome with
  | zero =>
    simp only [Feedback.run, PMF.mem_support_pure_iff] at ho
    cases ho
    exact ha
  | succ fuel ih =>
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [Feedback.run, hs, ↓reduceIte, PMF.mem_support_pure_iff] at ho
      cases ho
      exact ha
    | false =>
      simp only [Feedback.run, hs, Bool.false_eq_true, ↓reduceIte,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at ho
      obtain ⟨⟨reply, next⟩, hr, ho⟩ := ho
      exact ih _ _ _ (after_reply_aligned limits sample width budget ell hw hc ht he
        hcut hd state memory ha hs reply next hr) _ ho

/-- The constructed same-code native program, starting with original encoded input
and blank work tapes, has only authenticated accepted batch events. Its output,
source used-set, cancellation charges and concurrent physical duration are jointly
those of the actual final source memory. No admission or execution law is a premise.
The supported scheduler has fixed positive block width/interface, fitting turn
budget and configured cutoff allotments; this is not the unrestricted upper theorem. -/
theorem admitted_controller (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
    let context := impl.context
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n) (_ : data.startup.turns ≤ limits.turns)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (observation : Option (NativeReplyContext.Observation (ServerState n Private)))
        (_ : observation ∈ ((NativeUnboundedExecution.terminal program (environment limits sample)
          ⟨program.initialConfig (GuardedStartup.encoding data),
            ⟨ConcurrentBatch.initial seed, []⟩⟩).map
          (Option.map (NativeReplyContext.observe context))).support),
        ∃ (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private)),
          observation = some ⟨tapeOfList (RuntimeControl.packet state),
            RuntimeControl.result state, memory⟩ ∧
          Aligned limits width data.startup.turns ell state memory ∧
          state.work.system = data.startup.system := by
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let context := impl.context
  have hlaw := impl.law
  dsimp only
  intro Private limits sample data seed ell hn hw hc ht he hcut hd observation ho
  rw [hlaw] at ho
  simp only [PMF.mem_support_map_iff] at ho
  obtain ⟨outcome, houtcome, rfl⟩ := ho
  refine ⟨outcome.state, outcome.memory, rfl, ?_, ?_⟩
  · exact run_aligned limits sample width data.startup.turns ell hw hc ht he hcut hd _ _ _ _
      (initial_aligned limits width ell data seed hn) outcome houtcome
  · exact Feedback.run_original_system _ _ _ _ _ _ outcome houtcome

/-- The constructed finite native controller is admitted by the existing
`SelectionOnly` API at every instruction prefix. All decoded final families have
actual selected-response provenance. The premise is the ordinary original WSC
promise, not a provenance, scheduler-execution or successful-output contract. -/
theorem selectionOnly_controller (width : ℕ) :
    let impl := BatchPlanner.controller n width
    let program := impl.program
      ∀ (Private : Type) (limits : Limits n) (sample : Sampler n Private)
        (data : GuardedStartup.Input) (seed : Private) (ell : ℝ≥0)
        (_ : data.startup.opportunities = n) (_ : 0 < width)
        (_ : data.startup.turns * width ≤ n) (_ : data.startup.turns ≤ limits.turns)
        (_ : 0 < ell) (_ : ∀ i, limits.cutoff i ≤ ell)
        (_ : (data.startup.turns : ℝ≥0) * ell ≤ limits.deadline)
        (_ : Valid data.startup.system),
        NativeUnboundedExecution.SelectionOnly program (environment limits sample)
          (NativeBatch.candidateParser (n := n) data.startup.system.rows.length)
          (decodeFamily data.startup.system.rows.length) (fun _ => true)
          ⟨program.initialConfig (GuardedStartup.encoding data),
            ⟨ConcurrentBatch.initial seed, []⟩⟩ := by
  let impl := BatchPlanner.controller n width
  let program := impl.program
  let context := impl.context
  have hp := admitted_controller (n := n) width
  dsimp only
  intro Private limits sample data seed ell hn hw hc ht he hcut hd hx fuel world hworld C hC _
  cases hcontrol : world.config.tapes.state with
  | some control => simp [NativeOpenSelection.result, hcontrol] at hC
  | none =>
    have hterminal := (NativeUnboundedExecution.terminal_support program
      (environment limits sample) _ world).mpr ⟨hcontrol, fuel, hworld⟩
    have hobservation := (PMF.mem_support_map_iff
      (Option.map (NativeReplyContext.observe context)) _ _).mpr
      ⟨some world, hterminal, rfl⟩
    obtain ⟨state, memory, hobs, ha, hsystem⟩ := hp Private limits sample data seed ell
      hn hw hc ht he hcut hd _ hobservation
    have houtput := congrArg (Option.map NativeReplyContext.Observation.output) hobs
    have hmemory := congrArg (Option.map NativeReplyContext.Observation.memory) hobs
    simp only [Option.map_some, Option.some.injEq, NativeReplyContext.observe] at houtput hmemory
    have hvalid : Valid state.work.system := by simpa only [hsystem] using hx
    have hprovenance : ∀ (family : Finset (Fin state.work.system.rows.length)),
        decodeFamily state.work.system.rows.length (RuntimeControl.result state) = some family →
        family ⊆ NativeBatch.nativeAvailable (n := n) state.work.system.rows.length
          memory.events := by
      intro family hfamily
      obtain ⟨_, _, _, hsource⟩ := ha.invariant
      rw [hsource]
      exact result_provenance limits width data.startup.turns ell state memory ha hvalid
        family hfamily
    rw [hsystem] at hprovenance
    rw [NativeBatch.candidateParser_proposals, hmemory]
    apply hprovenance C
    simpa only [NativeOpenSelection.result, hcontrol, Option.isNone_none, ↓reduceIte,
      houtput] using hC

end Cslib.Probability.StochasticOracle.NativeRetention.BatchAdmission
