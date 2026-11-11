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

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.search_transport`: the actual
  source success probability is bounded by the two audit events, without a charge premise.

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness.accepted_eq`: actual accepted
  candidates equal the planted word when the complete ledger is collision-free.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness

open Probability OracleComp RandomPermutation

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

/-- The requested actual-game transport. No query-budget or numerical charge is assumed. -/
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

/-- OPEN quantitative obligation for this concrete audit. This is not a proved simulator or
an assumption of a security theorem. It charges the union once and separately budgets the
stopped guess. Because `collided` includes planting, this may be stronger than necessary;
a repair may instead prove a more selective joint charge with a derived uniqueness theorem. -/
@[expose] def RemainingCharge : Prop :=
  ∀ (q m T : ℕ) (hq : 3 ≤ q) (_hodd : q % 2 = 1)
    (adversary : Fin (2 ^ m) → Fin (2 ^ m) →
      ProbOracleComp (Spec q (Fin (2 ^ m))) (Operators q)),
    (∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T) →
    max q 4 ≤ T → T ≤ 2 ^ (m - 3) →
    let observations := challenges.bind fun draw => audit draw (Security.middleIndex q hq) adversary
    (((observations.map fun r => r.stopped || r.collided) true).toReal ≤
        3 * T / 2 ^ ((q + 1) / 2) + 10 * (T : ℝ) ^ 2 / 2 ^ m) ∧
      (((observations.map fun r => r.guessed && !r.stopped) true).toReal ≤
        1 / (2 : ℝ) ^ q)

end Cslib.Cryptanalysis.AddXNOR.IdealChain.PlantedUniqueness
