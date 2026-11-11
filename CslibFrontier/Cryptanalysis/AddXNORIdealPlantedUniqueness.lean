/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealGuessing
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind

/-!
# Actual planted verification uniqueness

The complete native experiment includes planting, adversary calls and verification. Its
collision predicate therefore charges planting too; it is not the source's cheaper post-query
collision event. No law for the frontier sampler is used.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.experiment`: actual execution
  retaining an accepted candidate.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.RemainingCharge`: the exact
  open joint-event budget for the concrete phase-separated audit.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.audit_guess_bound`: the actual
  audit stopped guessing probability is at most `2^(-q)`.
* `PlantedUniqueness.source_theorem_eight_of_remaining_charge`:
  explicitly conditional final assembly; the joint charge remains an open premise.

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.search_transport`: the actual
  source success probability is bounded by the two audit events, without a charge premise.

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.accepted_eq`: actual accepted
  candidates equal the planted word when the complete ledger is collision-free.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness

open Probability OracleComp RandomPermutation
open scoped ENNReal

/-- Plant, run the actual adversary, and retain its candidate only on successful verification. -/
@[expose] def experiment {q : ℕ} {Word : Type} [DecidableEq Word]
    (seed : Word) (bits : Operators q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    ProbOracleComp (Spec q Word) (Option (Operators q)) := do
  let target ← liftRight (walk (List.ofFn fun i => (i, bits i)) seed)
  let candidate ← adversary seed target
  let endpoint ← liftRight (walk (List.ofFn fun i => (i, candidate i)) seed)
  return if endpoint = target then some candidate else none

/-- A collision-free actual planted execution cannot accept a different operator word.
The collision ledger includes the experiment-internal planting queries. -/
theorem accepted_eq {q : ℕ} {Word : Type} [Finite Word] [DecidableEq Word] [Nonempty Word]
    (perms : Label q → Equiv.Perm Word) (seed : Word) (bits candidate : Operators q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (final : Replay.State (Label q) Word)
    (hout : (some candidate, final) ∈ (ProbOracleComp.runWith Replay.answer
      (experiment seed bits adversary) ⟨[], [], perms⟩).support)
    (hc : Forest.NoCollision {seed} final.records) : candidate = bits := by
  let _ : Fintype Word := Fintype.ofFinite Word
  have hrecorded := Replay.run_recorded perms _ (some candidate) final hout
  rw [experiment, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hout
  obtain ⟨⟨target, planted⟩, hplant, hrest⟩ := hout
  have hsub := Replay.run_records_suffix _ planted (some candidate) final hrest
  have hp := Reveal.path_follows false (List.ofFn fun i => (i, bits i)) seed
    ⟨[], [], perms⟩ target planted hplant (Replay.run_recorded perms _ target planted hplant)
  simp only [Reveal.directionRecords, Bool.false_eq_true, ↓reduceIte] at hp
  have hp' := hp.mono hsub.subset
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hrest
  obtain ⟨⟨chosen, middle⟩, _, hverify⟩ := hrest
  rw [ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff] at hverify
  obtain ⟨⟨endpoint, last⟩, hwalk, hpure⟩ := hverify
  rw [ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff] at hpure
  by_cases he : endpoint = target
  · simp only [he, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at hpure
    obtain ⟨hchosen, hlast⟩ := hpure
    subst chosen
    subst last
    subst endpoint
    have hv := Reveal.path_follows false (List.ofFn fun i => (i, candidate i)) seed
      middle target final hwalk hrecorded
    simp only [Reveal.directionRecords, Bool.false_eq_true, ↓reduceIte] at hv
    have h₁ := Forest.follows_witness {seed} seed (Finset.mem_singleton_self _) final.records hc hv
    have h₂ := Forest.follows_witness {seed} seed (Finset.mem_singleton_self _) final.records hc hp'
    have heq := List.ofFn_injective (Option.some.inj (h₁.symm.trans h₂))
    funext i
    exact congrArg Prod.snd (congrFun heq i)
  · simp [he] at hpure

/-- Separate acceptance, guessing, original-query stopping, and full-ledger collisions. -/
structure AuditResult where
  /-- Actual candidate verification outcome. -/
  accepted : Bool
  /-- Whether the candidate is the hidden word. -/
  guessed : Bool
  /-- Answer disagreement during the adversary phase only. -/
  stopped : Bool
  /-- A collision anywhere, including the planting walk. -/
  collided : Bool

open scoped Classical in
/-- Execute all phases in the genuinely reprogrammed permutation family, retaining phase
boundaries so internal planting queries never enter the adversary's stopped transcript. -/
@[expose] noncomputable def audit {q : ℕ} {Word : Type}
    [DecidableEq Word] (draw : Challenge q Word) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) : PMF AuditResult := do
  let changed := draw.changed k
  let (target, planted) ← ProbOracleComp.runWith Replay.answer
    (liftRight (walk (List.ofFn fun i => (i, draw.bits i)) draw.seed)) ⟨[], [], changed⟩
  let (candidate, middle) ← ProbOracleComp.runWith Replay.answer
    (adversary draw.seed target) planted
  let (endpoint, final) ← ProbOracleComp.runWith Replay.answer
    (liftRight (walk (List.ofFn fun i => (i, candidate i)) draw.seed)) middle
  return {
      accepted := decide (endpoint = target)
      guessed := decide (candidate = draw.bits)
      stopped := Visible.traceBad draw.perms changed
        (middle.trace.take (middle.trace.length - planted.trace.length))
      collided := decide (¬Forest.NoCollision {draw.seed} final.records) }

private theorem replay_output {q : ℕ} {Word Output : Type} [Finite Word]
    [DecidableEq Word] (perms : Label q → Equiv.Perm Word)
    (program : ProbOracleComp (Spec q Word) Output) :
    (ProbOracleComp.runWith Replay.answer program ⟨[], [], perms⟩).map Prod.fst =
      interpret (Family.probEval perms) program := by
  let _ : Fintype Word := Fintype.ofFinite Word
  have h₁ := congrArg (PMF.map Prod.fst) (Replay.erase_records program
    (⟨[], [], perms⟩ : Replay.State (Label q) Word))
  have h₂ := congrArg (PMF.map Prod.fst) (Visible.attach_flag perms perms program)
  rw [Visible.output_law] at h₂
  simp only [PMF.map_comp, Function.comp_def] at h₁ h₂
  exact h₁.trans h₂

/-- Audit erasure recovers precisely the actual planted oracle program in the changed family.
The stopped and collision observations never alter answers or the candidate. -/
theorem audit_accepted {q : ℕ} {Word : Type} [Finite Word] [DecidableEq Word]
    (draw : Challenge q Word) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    (audit draw k adversary).map AuditResult.accepted =
      interpret (Family.probEval (draw.changed k))
        (plantedProgram draw.seed draw.bits adversary) := by
  have he : (audit draw k adversary).map AuditResult.accepted =
      (ProbOracleComp.runWith Replay.answer
        (plantedProgram draw.seed draw.bits adversary)
        ⟨[], [], draw.changed k⟩).map Prod.fst := by
    simp only [audit, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_map, pmf_norm,
      plantedProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_pure]
  exact he.trans (replay_output _ _)

/-- Actual audit acceptance forces guessing or a collision in its complete ledger. -/
theorem audit_acceptance_implies {q : ℕ} {Word : Type} [Finite Word]
    [DecidableEq Word] [Nonempty Word] (draw : Challenge q Word) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (r : AuditResult) (hr : r ∈ (audit draw k adversary).support) (ha : r.accepted = true) :
    r.guessed = true ∨ r.collided = true := by
  classical
  simp only [audit, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff,
    Probability.PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff] at hr
  obtain ⟨⟨target, planted⟩, hp, ⟨⟨candidate, middle⟩, hm,
    ⟨⟨endpoint, final⟩, hv, he⟩⟩⟩ := hr
  cases he
  have heq : endpoint = target := of_decide_eq_true ha
  by_cases hc : Forest.NoCollision {draw.seed} final.records
  · left
    have hout : (some candidate, final) ∈ (ProbOracleComp.runWith Replay.answer
        (experiment draw.seed draw.bits adversary) ⟨[], [], draw.changed k⟩).support := by
      simp only [experiment, ProbOracleComp.runWith_bind, PMF.mem_support_bind_iff]
      refine ⟨(target, planted), hp, (candidate, middle), hm, (endpoint, final), hv, ?_⟩
      simp [ProbOracleComp.runWith_pure, heq]
    exact decide_eq_true (accepted_eq _ _ _ _ _ _ hout hc)
  · exact Or.inr (decide_eq_true hc)

/-- Averaging the valid cut law gives the original planted-search acceptance distribution. -/
theorem audit_search_law {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word]
    [Nonempty Word] (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    (challenges.bind fun draw => audit draw k adversary).map AuditResult.accepted =
      plantedSearch adversary := by
  simp only [challenges, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.pure_bind, audit_accepted,
    Challenge.changed, pmf_norm, plantedSearch]
  congr 1 with seed : 1
  congr 1 with bits : 1
  have h := source_uniform_splice bits k seed (fun perms _ =>
    interpret (Family.probEval perms) (plantedProgram seed bits adversary))
  rw [h]
  simp only [interpret_plantedProgram, PMF.monad_bind_eq_bind]
  rfl

/-- Actual planted-search transport to the audit events.
No query-budget or numerical charge is assumed. -/
theorem search_transport {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word]
    [Nonempty Word] (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    ((plantedSearch adversary) true).toReal ≤
      (((challenges.bind fun draw => audit draw k adversary).map
        (fun r => r.stopped || r.collided)) true).toReal +
      (((challenges.bind fun draw => audit draw k adversary).map
        (fun r => r.guessed && !r.stopped)) true).toReal := by
  have h := Probability.PMF.map_true_le_add (challenges.bind fun draw => audit draw k adversary)
    (E := AuditResult.accepted) (A := fun r => r.stopped || r.collided)
    (B := fun r => r.guessed && !r.stopped) (fun r hr ha => by
      rw [PMF.mem_support_bind_iff] at hr
      obtain ⟨draw, _, hr⟩ := hr
      rcases audit_acceptance_implies draw k adversary r hr ha with hg | hc
      · cases r.stopped <;> simp [hg]
      · exact Or.inl (by simp [hc]))
  rw [audit_search_law] at h
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩) h
  simpa only [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] using ht

private theorem replay_phase_trace {q : ℕ} {Word Output : Type} [Finite Word]
    [DecidableEq Word] (program : ProbOracleComp (Spec q Word) Output)
    (initial : Replay.State (Label q) Word) :
    (ProbOracleComp.runWith Replay.answer program initial).map
      (fun (out, next) => (out, ((), next.trace.take
        (next.trace.length - initial.trace.length)))) =
      ProbOracleComp.runWith (withTranscript (Visible.reader initial.perms)) program ((), []) := by
  let _ : Fintype Word := Fintype.ofFinite Word
  let reader := withTranscript (Visible.reader initial.perms)
  have happ := ProbOracleComp.runWith_map_state reader reader
    (fun state => (state.1, state.2 ++ initial.trace))
    (fun query state => by simp [reader, withTranscript, Visible.reader]) program ((), [])
  have he := congrArg (PMF.map (fun (entry : Output × Visible.State (Label q) Word) =>
      let (out, state) := entry;
      (out, ((), state.2.take (state.2.length - initial.trace.length)))))
    (Replay.erase_records program initial)
  simp only [PMF.map_comp, Function.comp_def] at he
  dsimp only [reader] at happ
  simp only [List.nil_append] at happ
  rw [← happ] at he
  have heta : (fun (x : Output × Visible.State (Label q) Word) => (x.1, ((), x.2.2))) = id := by
    funext ⟨out, memory, trace⟩
    cases memory
    rfl
  simpa only [PMF.map_comp, Function.comp_def, List.length_append,
    Nat.add_sub_cancel, List.take_left, reader, heta, PMF.map_id] using he

/-- Erasing verification and the planting log gives the adversary-only stopped guessing law. -/
theorem audit_guess_law {q : ℕ} {Word : Type} [Finite Word] [DecidableEq Word]
    (draw : Challenge q Word) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    (audit draw k adversary).map (fun r => r.guessed && !r.stopped) =
      (ProbOracleComp.runWith (Visible.handler false draw.perms (draw.changed k))
        (adversary draw.seed draw.target) (((), []), false)).map
          (fun (candidate, _, flag) => decide (candidate = draw.bits) && !flag) := by
  classical
  let changed := draw.changed k
  have ht (target : Word) (planted : Replay.State (Label q) Word)
      (hp : (target, planted) ∈ (ProbOracleComp.runWith Replay.answer
        (liftRight (walk (List.ofFn fun i => (i, draw.bits i)) draw.seed))
        ⟨[], [], changed⟩).support) : target = draw.target ∧ planted.perms = changed := by
    have hπ := (Replay.run_trace_eval changed _ target planted hp).1
    have he := Reveal.path_endpoint false (List.ofFn fun i => (i, draw.bits i)) draw.seed
      ⟨[], [], changed⟩ target planted hp
    have hs := (sourceCut draw.bits k).endpoint_splice draw.perms draw.seed draw.target
    rw [sourceCut_endpoint] at hs
    refine ⟨?_, hπ⟩
    simp only [Bool.false_eq_true, ↓reduceIte, pathEquiv_apply] at he
    exact he.trans hs
  simp only [audit, pmf_norm, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  let result : PMF Bool := (ProbOracleComp.runWith
    (Visible.handler false draw.perms (draw.changed k))
    (adversary draw.seed draw.target) (((), []), false)).map
      (fun (candidate, _, flag) => decide (candidate = draw.bits) && !flag)
  change _ = result
  have hconst := PMF.bind_const (ProbOracleComp.runWith Replay.answer
    (liftRight (walk (List.ofFn fun i => (i, draw.bits i)) draw.seed))
    (⟨[], [], changed⟩ : Replay.State (Label q) Word)) result
  rw [← hconst]
  apply PMF.bind_congr_on_support
  rintro ⟨target, planted⟩ hp
  obtain ⟨rfl, hπ⟩ := ht target planted hp
  have he := congrArg (PMF.map (fun (entry : Operators q × Visible.State (Label q) Word) =>
      let (candidate, state) := entry;
      decide (candidate = draw.bits) &&
        !Visible.traceBad draw.perms changed state.2))
    (replay_phase_trace (adversary draw.seed draw.target) planted)
  simp only [PMF.map_comp, Function.comp_def, hπ] at he
  dsimp only
  simp only [PMF.map, Function.comp_def, changed] at he
  trans (ProbOracleComp.runWith (withTranscript (Visible.reader changed))
    (adversary draw.seed draw.target) ((), [])).map
      (fun (candidate, state) => decide (candidate = draw.bits) &&
        !Visible.traceBad draw.perms changed state.2)
  · convert he using 1; simp only [PMF.map, Function.comp_def, changed]
  · have hs : Visible.handler true changed draw.perms =
        Visible.handler false draw.perms changed := by
      funext query state
      simp [Visible.handler, withBadFlag, Visible.step, ne_comm]
    have htrace (trace : Transcript (Spec q Word)) :
        Visible.traceBad changed draw.perms trace = Visible.traceBad draw.perms changed trace := by
      unfold Visible.traceBad
      congr 1
      funext entry
      exact decide_eq_decide.mpr ne_comm
    have hf := congrArg (PMF.map (fun (candidate, _, flag) =>
        decide (candidate = draw.bits) && !flag))
      (Visible.attach_flag changed draw.perms (adversary draw.seed draw.target))
    simp only [PMF.map_comp, Function.comp_def, htrace, hs] at hf
    simpa only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, result] using hf


/-- The guessing half of the actual phase-separated audit is at most `2^(-q)`.
The phase erasure is proved above; no guessed-candidate or stopping bound is a premise. -/
theorem audit_guess_bound {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word]
    [Nonempty Word] (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    (((challenges.bind fun draw => audit draw k adversary).map
      (fun r => r.guessed && !r.stopped)) true).toReal ≤ 1 / (2 : ℝ) ^ q := by
  classical
  have hp : ((challenges.bind fun draw => audit draw k adversary).map
      (fun r => r.guessed && !r.stopped)) true ≤ 1 / (2 : ℝ≥0∞) ^ q := by
    simp only [challenges, pmf_norm, PMF.map_bind, audit_guess_law, Challenge.changed]
    apply Probability.PMF.bind_apply_le_on_support
    intro seed _
    rw [PMF.bind_comm (PMF.uniformOfFintype (Operators q))
      (PMF.uniformOfFintype (Label q → Equiv.Perm Word))]
    apply Probability.PMF.bind_apply_le_on_support
    intro perms _
    rw [PMF.bind_comm (PMF.uniformOfFintype (Operators q)) (PMF.uniformOfFintype Word)]
    apply Probability.PMF.bind_apply_le_on_support
    intro target _
    exact Guessing.stopped_guess_le perms seed target k (adversary seed target)
  have ht := ENNReal.toReal_mono (by finiteness : (1 / (2 : ℝ≥0∞) ^ q) ≠ ⊤) hp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using ht

/-- OPEN joint stopping/collision charge for the concrete audit. The guessing half has
been proved as `audit_guess_bound`. This is not an axiom or an established source bound. -/
@[expose] def RemainingCharge : Prop :=
  ∀ (q m T : ℕ) (hq : 3 ≤ q) (_hodd : q % 2 = 1)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q)),
    (∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T) →
    max q 4 ≤ T → T ≤ 2 ^ (m - 3) →
    let observations := challenges.bind fun draw => audit draw (Security.middleIndex q hq) adversary
    ((observations.map fun r => r.stopped || r.collided) true).toReal ≤
      3 * T / 2 ^ ((q + 1) / 2) + 10 * (T : ℝ) ^ 2 / 2 ^ m

/-- Conditional assembly only: a proof of the open joint charge would complete literal
Theorem 8. This theorem explicitly exposes that remaining premise; it does not prove it. -/
theorem source_theorem_eight_of_remaining_charge (hcharge : RemainingCharge)
    {q : ℕ} (hq : 3 ≤ q) (m T : ℕ)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (hT : max q 4 ≤ T) (hlimit : T ≤ 2 ^ (m - 3)) :
    ((plantedSearch adversary) true).toReal ≤
      3 * T / 2 ^ ((q + 1) / 2) + 10 * (T : ℝ) ^ 2 / 2 ^ m + 1 / (2 : ℝ) ^ q := by
  by_cases heven : q % 2 = 0
  · exact VerificationCovering.source_theorem_eight_even hq heven m T adversary hbudget hT hlimit
  · have hc := hcharge q m T hq (by omega) adversary hbudget hT hlimit
    have hg := audit_guess_bound (Security.middleIndex q hq) adversary
    have ht := search_transport (Security.middleIndex q hq) adversary
    dsimp only at hc
    linarith

end Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness
