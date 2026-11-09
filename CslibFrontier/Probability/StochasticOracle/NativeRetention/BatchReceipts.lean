/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchStopping
public import CslibFrontier.Computability.Probabilistic.NativeBatch.Retained
import Mathlib.Tactic

/-!
# Actual source receipts and the executed native retention guard

[Wang2027], Theorem 5, PDF p. 12, Appendix A.5 p. 16. The native quantitative
retention API accepts an explicit parser. Here it is the actual source report
parser, with finite row indices embedded into the original natural-number instance.
No alphabet truncation or finite hidden-state abstraction is performed.

`BatchAdmission.Aligned.reports` authenticates the entire raw runtime reply history
against the actual accepted source receipts. `completion_eq` consequently identifies
the executed guard with the exact receipt event in `NativeBatch.Retained`, rather
than assuming a representation identity. `BatchUpper` proves native selected-epoch
stopping and numerical progress/survival-sum bill bounds. Complete certified-output
success/deadline transfer and the common-oracle optimum comparison remain open.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchReceipts
open Turing NativeOpenExecution ConcurrentBatch PartialCover AdaptiveSelection
open NativeBatch.Trace
open scoped NNReal
variable {n : ℕ}

/-- Full raw source replies, newest first. A no-call decision contributes no reply. -/
@[expose] def words (records : List (Record n)) : List Word :=
  (records.filterMap id).map fun receipt => (replyOf receipt).word

/-- Execute exactly the runtime parser on an actual completed concurrent receipt.
No-call halt/divergence records contribute no candidate proposal. -/
@[expose] def proposal (x : Input) (_ : List (Record n)) (record : Record n) : List (Finset ℕ) :=
  record.elim [] fun receipt =>
    BatchStopping.proposal ⟨x, n, []⟩ [] (replyOf receipt).word

/-- A source candidate mask normalizes to precisely its original row indices. -/
theorem normalize_sourceIndices (x : Input) (C : Finset (Fin x.rows.length)) :
    (normalize x (sourceIndices C)).toFinset = C.image Fin.val := by
  ext j
  simp only [normalize, population, List.mem_toFinset, List.mem_filter, List.mem_range,
    decide_eq_true_eq, sourceIndices_mem, Finset.mem_image]
  constructor
  · rintro ⟨_, i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i.isLt, i, hi, rfl⟩

/-- The concrete packet implementation agrees with source proposals, including
all completed concurrent calls and no proposal from a canceled call. -/
theorem proposal_eq (x : Input) (history : List (Record n)) (record : Record n) :
    proposal x history record = record.elim [] (fun receipt =>
      (ConcurrentBatch.proposals x.rows.length receipt.report).map (Finset.image Fin.val)) := by
  cases record with
  | none => rfl
  | some receipt =>
    simp only [proposal, Option.elim_some, BatchStopping.proposal, replyOf,
      Packets.families_report, List.map_map]
    apply List.map_congr_left
    intro C _
    exact normalize_sourceIndices x C

/-- Deleting no-call records and reading raw reports preserves the entire retained
family, not just the union of revealed candidates. Correlation is unrestricted. -/
theorem selected_eq (x : Input) (hx : Valid x) (records : List (Record n)) :
    selected (instanceOf x hx) x.rho
        (BatchStopping.proposal ⟨x, n, words records⟩) (words records) =
      selected (instanceOf x hx) x.rho (proposal x) records := by
  change selected (instanceOf x hx) x.rho
    (BatchStopping.proposal ⟨x, n, []⟩) (words records) = _
  induction records with
  | nil => rfl
  | cons record records ih =>
    cases record with
    | none => simpa only [words, List.filterMap_cons, id_eq, List.map_cons,
        Option.elim_none, selected, proposal, Instance.retain] using ih
    | some receipt =>
      simp only [words, List.filterMap_cons, id_eq, List.map_cons, selected, proposal,
        Option.elim_some] at ih ⊢
      rw [ih]
      rfl

/-- The generalized actual native receipt completion is exactly the computed
runtime completion bit when the raw words come from those receipts. -/
theorem completion_eq (x : Input) (hx : Valid x) (records : List (Record n)) :
    (Packets.decision ⟨x, n, words records⟩).1 =
      NativeBatch.Retained.complete (instanceOf x hx) x.rho (proposal x) records := by
  have hc := BatchStopping.completion_iff ⟨x, n, words records⟩ hx
  rw [selected_eq x hx records] at hc
  unfold NativeBatch.Retained.complete
  exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hc)

/-- The actual admitted native feedback state reads precisely its own source
receipt history. No supplied runtime-history/receipt correspondence is a premise. -/
theorem aligned_completion_eq {Private : Type} (limits : Limits n)
    (width budget : ℕ) (ell : ℝ≥0) (state : RuntimeControl.State)
    (memory : Memory Unit (ServerState n Private))
    (ha : BatchAdmission.Aligned limits width budget ell state memory)
    (hx : Valid state.work.system) :
    (Packets.decision state.work).1 = NativeBatch.Retained.complete
      (instanceOf state.work.system hx) state.work.system.rho (proposal state.work.system)
        (memory.privateState.history.map some) := by
  have hw : state.work = ⟨state.work.system, n,
      words (memory.privateState.history.map some)⟩ := by
    cases h : state.work with
    | mk system opportunities history =>
      have hn := ha.opportunityInterface
      have hh := ha.reports
      simp only [h] at hn hh ⊢
      subst opportunities
      simp only [words, List.filterMap_map, Function.comp_def, id_eq, List.filterMap_some]
      congr 1
  have hc := completion_eq state.work.system hx (memory.privateState.history.map some)
  rw [← hw] at hc
  exact hc

/-- Every accepted batch was issued before the computed retained cover completed.
Histories are newest first, so each tail is the actual history before that batch. -/
@[expose] def Safe (x : Input) : List (Exchange n) → Prop
  | [] => True
  | _ :: history => Safe x history ∧
      (Packets.decision ⟨x, n, history.map (fun receipt => (replyOf receipt).word)⟩).1 = false

/-- The accepted source history and interface completely determine the actual guard. -/
theorem aligned_decision {Private : Type} (limits : Limits n)
    (width budget : ℕ) (ell : ℝ≥0) (state : RuntimeControl.State)
    (memory : Memory Unit (ServerState n Private))
    (ha : BatchAdmission.Aligned limits width budget ell state memory) :
    Packets.decision state.work = Packets.decision
      ⟨state.work.system, n, memory.privateState.history.map (fun r => (replyOf r).word)⟩ := by
  have hw : state.work =
      ⟨state.work.system, n, memory.privateState.history.map (fun r => (replyOf r).word)⟩ := by
    cases h : state.work with
    | mk system opportunities history =>
      have hn := ha.opportunityInterface
      have hh := ha.reports
      simp only [h] at hn hh ⊢
      subst opportunities
      congr 1
  rw [hw]

/-- An actual supported source response extends the safe history because the
executed pre-response guard was live, not because safety was assumed for that call. -/
theorem safe_after_reply {Private : Type} (limits : Limits n) (sample : Sampler n Private)
    (width budget : ℕ) (ell : ℝ≥0) (hw : 0 < width) (hc : budget * width ≤ n)
    (ht : budget ≤ limits.turns) (he : 0 < ell)
    (hd : (budget : ℝ≥0) * ell ≤ limits.deadline)
    (state : RuntimeControl.State) (memory : Memory Unit (ServerState n Private))
    (ha : BatchAdmission.Aligned limits width budget ell state memory)
    (hs : RuntimeControl.stopped state = false)
    (hprior : Safe state.work.system memory.privateState.history)
    (reply : Reply) (next : ServerState n Private)
    (hr : (reply, next) ∈
      (environment limits sample ((), BatchPlanner.request n width state) memory).support) :
    Safe state.work.system next.history := by
  obtain ⟨batch, _, haccept⟩ :=
    BatchAdmission.admit_request limits width budget ell hw hc ht he hd state memory ha hs
  change (reply, next) ∈ (serve limits sample _ memory.privateState).support at hr
  rw [serve_accepted _ _ _ _ _ haccept, PMF.mem_support_map_iff] at hr
  obtain ⟨⟨paths, privateState⟩, _, hpair⟩ := hr
  cases hpair
  refine ⟨hprior, ?_⟩
  rw [← aligned_decision limits width budget ell state memory ha]
  exact (Bool.or_eq_false_iff.mp hs).2

/-- Safety is preserved by the very kernel in the same-code native execution law,
with actual correlated source responses and authenticated receipt order. -/
theorem run_safe {Private : Type} (limits : Limits n) (sample : Sampler n Private)
    (width budget : ℕ) (ell : ℝ≥0) (hw : 0 < width) (hc : budget * width ≤ n)
    (ht : budget ≤ limits.turns) (he : 0 < ell)
    (hcut : ∀ i, limits.cutoff i ≤ ell) (hd : (budget : ℝ≥0) * ell ≤ limits.deadline)
    (fuel : ℕ) (state : RuntimeControl.State)
    (channels : Unit → Turing.MultiTapeMachine.Channel Bool)
    (memory : Memory Unit (ServerState n Private))
    (ha : BatchAdmission.Aligned limits width budget ell state memory)
    (hprior : Safe state.work.system memory.privateState.history) (outcome : Feedback.Outcome _)
    (ho : outcome ∈ (Feedback.run (environment limits sample) fuel state channels memory
      (BatchPlanner.request n width)).support) :
    Safe state.work.system outcome.memory.privateState.history := by
  induction fuel generalizing state channels memory outcome with
  | zero =>
    simp only [Feedback.run, PMF.mem_support_pure_iff] at ho
    cases ho
    exact hprior
  | succ fuel ih =>
    cases hs : RuntimeControl.stopped state with
    | true =>
      simp only [Feedback.run, hs, ↓reduceIte, PMF.mem_support_pure_iff] at ho
      cases ho
      exact hprior
    | false =>
      simp only [Feedback.run, hs, Bool.false_eq_true, ↓reduceIte,
        PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at ho
      obtain ⟨⟨reply, next⟩, hr, ho⟩ := ho
      exact ih _ _ _ (BatchAdmission.after_reply_aligned limits sample width budget ell hw hc
        ht he hcut hd state memory ha hs reply next hr)
        (safe_after_reply limits sample width budget ell hw hc ht he hd state memory ha hs
          hprior reply next hr) _ ho

/-- With original allowances covering the turn budget, a complete executed run
ends either at computed completion or after exactly that many actual transactions. -/
theorem run_end {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Turing.MultiTapeMachine.Channel Bool)
    (memory : Memory Unit P) (request : RuntimeControl.State → Word)
    (hf : state.turns ≤ fuel) (hopps : state.turns ≤ state.opportunities)
    (hallot : state.turns ≤ state.allotments) (outcome : Feedback.Outcome P)
    (ho : outcome ∈ (Feedback.run env fuel state channels memory request).support) :
    (Packets.decision outcome.state.work).1 = true ∨
      outcome.memory.events.length = state.turns + memory.events.length := by
  have hs := Feedback.run_stopped_with_request env fuel state channels memory hf outcome request ho
  have hb := Feedback.run_allowances env fuel state channels memory request outcome ho
  by_cases hd : (Packets.decision outcome.state.work).1 = true
  · exact Or.inl hd
  · right
    by_contra h
    have ht : outcome.state.turns ≠ 0 := by omega
    have hp : outcome.state.opportunities ≠ 0 := by omega
    have ha : outcome.state.allotments ≠ 0 := by omega
    simp [RuntimeControl.stopped, ht, hp, ha, hd] at hs

end Cslib.Probability.StochasticOracle.NativeRetention.BatchReceipts
