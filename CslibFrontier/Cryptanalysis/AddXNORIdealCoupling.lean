/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORIdealCut
public import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bool

/-!
# A visible stopped coupling for the actual ideal-chain games

The two worlds differ by a hidden single-cut image swap. Their handlers record only visible
external queries and replies. A sticky flag is set exactly when their replies differ; private
coins neither change the log nor set the flag. `identicalUntilBad` is proved from these concrete
handlers, not supplied as a simulation/security contract.

This module reduces the actual decision advantage to its actual visible bad-flag experiment.
`AddXNORIdealSecurity` bounds that experiment using the actual charged reveal: it proves
Corollary 4 and a weaker-constant search inequality, without validating the source's false
literal Lemma 10 simulation claim.

## Main definitions

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.State`: visible transcript state.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.handler`: a concrete logged, flagged handler.

## Main results

* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.identicalUntilBad`: the stopped coupling.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.output_law`: flag/log erasure preserves
  the game.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible.badGame_trace`: exact visible stopping event.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.coupledDecision_planted`: the coupled world is
  the actual planted decision experiment.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.decision_advantage_le_visibleBad`: decision game hop.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.verifiedAdversary_queryBound`: the visible `T+q` budget.
* `Cslib.Cryptanalysis.AddXNOR.IdealChain.search_comparison`: the actual planted search game hop.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible

open Probability OracleComp RandomPermutation Crypto

/-- Only the adversary's external calls and answers are stored, in reverse chronological order.
The unit component matches the library's stateful transcript interface. -/
abbrev State (Index Word : Type) := Unit × Transcript (Family.Spec Index Word)

variable {Index Word : Type} [DecidableEq Word]

/-- The original reader before adding the transcript and bad flag. -/
@[expose] noncomputable def reader (perms : Index → Equiv.Perm Word)
    (query : Index × PermQuery Word) : StateT Unit PMF Word :=
  fun _ => PMF.pure (Family.eval perms query, ())

/-- A visible transition. `original = true` selects the unmodified family. Both worlds flag
exactly the same query-disagreement predicate, independently of which reply they return. -/
@[expose] noncomputable def step (original : Bool) (perms changed : Index → Equiv.Perm Word)
    (query : Index × PermQuery Word) (state : State Index Word) :
    PMF (Word × (State Index Word × Bool)) :=
  let before := Family.eval perms query
  let after := Family.eval changed query
  let reply := if original then before else after
  PMF.pure (reply, (((), ⟨query, reply⟩ :: state.2), decide (before ≠ after)))

/-- The sticky flag is independent of the visible log. Hidden setup calls never enter this
handler: it runs the adversary (and, for search, its explicit visible verification continuation). -/
@[expose] noncomputable def handler (original : Bool) (perms changed : Index → Equiv.Perm Word) :=
  withBadFlag (step original perms changed)

/-- The actual logged handlers agree until the first answer disagreement. The library lifts
this external-call coupling over arbitrary private randomness. -/
theorem identicalUntilBad (perms changed : Index → Equiv.Perm Word) :
    ProbOracleComp.IdenticalUntilBad (handler true perms changed) (handler false perms changed)
      FlagBad := by
  apply ProbOracleComp.identicalUntilBad_withBadFlag
  intro query state reply state'
  by_cases heq : Family.eval perms query = Family.eval changed query
  · simp [step, heq]
  · simp [step, heq, PMF.pure_apply]

/-- Dropping the sticky flag recovers the exact visible transcript of the chosen family. -/
theorem erase_flag (original : Bool) (perms changed : Index → Equiv.Perm Word)
    {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (ProbOracleComp.runWith (handler original perms changed) program (((), []), false)).map
        (Prod.map id Prod.fst) =
      ProbOracleComp.runWith (withTranscript (reader (if original then perms else changed)))
        program ((), []) := by
  apply ProbOracleComp.runWith_withBadFlag_map_fst
  intro query state
  cases original <;> simp [step, reader, withTranscript]

/-- The flagged/logged run has precisely the original eager output law; no change to the
adversary or its private coins is hidden in the stopping construction. -/
theorem output_law (original : Bool) (perms changed : Index → Equiv.Perm Word)
    {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (ProbOracleComp.runWith (handler original perms changed) program (((), []), false)).map
        Prod.fst = interpret (Family.probEval (if original then perms else changed)) program := by
  have hflag := congrArg (PMF.map Prod.fst) (erase_flag original perms changed program)
  have hlog := congrArg (PMF.map Prod.fst)
    (ProbOracleComp.run_interpret_withTranscript (reader (if original then perms else changed))
      program () [])
  simp only [PMF.map_comp, Function.comp_def] at hflag hlog
  change (ProbOracleComp.runWith (handler original perms changed) program
    (((), []), false)).map Prod.fst = _ at hflag
  change (ProbOracleComp.runWith (withTranscript
    (reader (if original then perms else changed))) program ((), [])).map Prod.fst = _ at hlog
  rw [hflag, hlog]
  have hreader : reader (if original then perms else changed) =
      (fun query => StateT.lift (σ := Unit)
        (PMF.pure (Family.eval (if original then perms else changed) query))) := by
    funext query state
    cases state
    simp [reader, StateT.lift]
  rw [hreader]
  have hr := ProbOracleComp.runWith_lift
    (fun query => PMF.pure (Family.eval (if original then perms else changed) query)) program ()
  simpa only [reader, StateT.lift, Family.probEval, OracleComp.evalWith, pmf_norm,
    PMF.map, Function.comp_def, PMF.bind_pure] using congrArg (PMF.map Prod.fst) hr

/-- Every visible transcript of the stopped run respects the external-call budget. -/
theorem transcript_length {Output : Type}
    (original : Bool) (perms changed : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Output) (T : ℕ)
    (hT : ProbOracleComp.IsQueryBounded program T)
    (out : Output) (state : State Index Word) (flag : Bool)
    (hout : (out, state, flag) ∈
      (ProbOracleComp.runWith (handler original perms changed) program (((), []), false)).support) :
    state.2.length ≤ T := by
  have hm : (out, state) ∈
      ((ProbOracleComp.runWith (handler original perms changed) program (((), []), false)).map
        (Prod.map id Prod.fst)).support :=
    by
      rw [PMF.mem_support_map_iff]
      exact ⟨(out, state, flag), hout, rfl⟩
  rw [erase_flag] at hm
  exact hT.length_transcript_le (reader (if original then perms else changed)) hm

/-- Concrete bad-event game: the visible run reaches an answer that changes under the swap. -/
@[expose] noncomputable def badGame (perms changed : Index → Equiv.Perm Word)
    {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) : Game :=
  (ProbOracleComp.runWith (handler true perms changed) program (((), []), false)).map
    (fun (_, _, flag) => flag)

/-- Recompute the actual stopping predicate from visible requests alone. The replies in the
transcript are retained for the later collision/forest analysis. -/
@[expose] def traceBad (perms changed : Index → Equiv.Perm Word)
    (trace : Transcript (Family.Spec Index Word)) : Bool :=
  trace.any fun entry => decide (Family.eval perms entry.1 ≠ Family.eval changed entry.1)

/-- The sticky flag is exactly the disjunction of answer disagreements in the visible log.
This law removes the coupling instrumentation without observing any hidden setup query. -/
theorem attach_flag (perms changed : Index → Equiv.Perm Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    (ProbOracleComp.runWith (withTranscript (reader perms)) program ((), [])).map
        (fun (out, state) => (out, (state, traceBad perms changed state.2))) =
      ProbOracleComp.runWith (handler true perms changed) program (((), []), false) := by
  have h := ProbOracleComp.runWith_map_state (withTranscript (reader perms))
    (handler true perms changed) (fun state => (state, traceBad perms changed state.2))
    (fun query state => by
      obtain ⟨memory, trace⟩ := state
      cases memory
      simp [reader, withTranscript, handler, step, withBadFlag, traceBad, Bool.or_comm])
    program ((), [])
  simpa only [traceBad, List.any_nil] using h

/-- The actual bad game equals the changed-request predicate on the independent reader's
ordinary visible transcript. This is an equality of executed experiments, not an assumed bound. -/
theorem badGame_trace (perms changed : Index → Equiv.Perm Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    badGame perms changed program =
      (ProbOracleComp.runWith (withTranscript (reader perms)) program ((), [])).map
        (fun (_, state) => traceBad perms changed state.2) := by
  rw [badGame, ← attach_flag, PMF.map_comp]
  rfl

open scoped Classical in
/-- The visible transcript hits one of the four concrete cut points. This game is evaluated
in the original independent family, with no hidden installation calls in its transcript. -/
@[expose] noncomputable def cutHitGame (cut : Cut Index)
    (perms : Index → Equiv.Perm Word) (seed target : Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) : Game :=
  (ProbOracleComp.runWith (withTranscript (reader perms)) program ((), [])).map
    (fun (_, state) => decide (∃ entry ∈ state.2, cut.affected perms seed target entry.1))

/-- A visible answer disagreement must hit one of the actual cut points. In particular, a
repeated query that the swap does not change cannot spuriously contribute to this upper bound. -/
theorem badGame_le_cutHit [DecidableEq Index] (cut : Cut Index)
    (perms : Index → Equiv.Perm Word) (seed target : Word) {Output : Type}
    (program : ProbOracleComp (Family.Spec Index Word) Output) :
    badGame perms (cut.splice perms seed target) program true ≤
      cutHitGame cut perms seed target program true := by
  classical
  rw [badGame_trace]
  apply PMF.map_true_mono
  rintro ⟨out, memory, trace⟩ _ hbad
  obtain ⟨entry, hentry, hchange⟩ := List.any_eq_true.mp hbad
  apply decide_eq_true_eq.mpr
  refine ⟨entry, hentry, ?_⟩
  by_contra hnot
  have heq := cut.eval_splice_eq_of_not_affected perms seed target entry.1 hnot
  exact (of_decide_eq_true hchange) heq.symm

/-- The probability of the actual sticky flag is its bad-event measure. -/
theorem badGame_apply (perms changed : Index → Equiv.Perm Word)
    {Output : Type} (program : ProbOracleComp (Family.Spec Index Word) Output) :
    badGame perms changed program true =
      (ProbOracleComp.runWith (handler true perms changed) program (((), []), false)).toOuterMeasure
        {out | FlagBad out.2} := by
  rw [badGame, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  rfl

/-- Mutual acceptance bounds for the actual output laws, charged to the actual visible flag.
There is no numerical bad-probability or simulation premise. -/
theorem apply_le (perms changed : Index → Equiv.Perm Word)
    (program : ProbOracleComp (Family.Spec Index Word) Bool) (b : Bool) :
    interpret (Family.probEval perms) program b ≤
        interpret (Family.probEval changed) program b + badGame perms changed program true ∧
      interpret (Family.probEval changed) program b ≤
        interpret (Family.probEval perms) program b + badGame perms changed program true := by
  have hi := identicalUntilBad perms changed
  have h₁ := hi.bind_apply_le program (((), []), false) (fun out => PMF.pure out.1) b
  have h₂ := hi.symm.bind_apply_le program (((), []), false) (fun out => PMF.pure out.1) b
  rw [← hi.bad_eq program (((), []), false)] at h₂
  change ((ProbOracleComp.runWith (handler true perms changed) program
    (((), []), false)).map Prod.fst) b ≤
    ((ProbOracleComp.runWith (handler false perms changed) program
      (((), []), false)).map Prod.fst) b + _ at h₁
  change ((ProbOracleComp.runWith (handler false perms changed) program
    (((), []), false)).map Prod.fst) b ≤
    ((ProbOracleComp.runWith (handler true perms changed) program
      (((), []), false)).map Prod.fst) b + _ at h₂
  simpa only [output_law, Bool.true_eq, Bool.false_eq_true, ↓reduceIte, badGame_apply]
    using And.intro h₁ h₂

end Cslib.Cryptanalysis.AddXNOR.IdealChain.Visible

namespace Cslib.Cryptanalysis.AddXNOR.IdealChain

open Probability OracleComp RandomPermutation Crypto

/-- The independent world before the hidden cut is forced. All fields are private except the
seed and target given to the adversary. The word determines the hidden cut label and paths. -/
structure Challenge (q : ℕ) (Word : Type) where
  /-- Public initial state. -/
  seed : Word
  /-- Private uniformly selected operator string. -/
  bits : Operators q
  /-- Private independent uniform permutation family. -/
  perms : Label q → Equiv.Perm Word
  /-- Public target, independently sampled before reprogramming. -/
  target : Word

variable {q : ℕ} {Word : Type} [Fintype Word] [DecidableEq Word] [Nonempty Word]

/-- Actual independent draws for the coupling; no planted path is part of the visible log. -/
@[expose] noncomputable def challenges : PMF (Challenge q Word) := do
  let seed ← PMF.uniformOfFintype Word
  let bits ← PMF.uniformOfFintype (Operators q)
  let perms ← PMF.uniformOfFintype (Label q → Equiv.Perm Word)
  let target ← PMF.uniformOfFintype Word
  return ⟨seed, bits, perms, target⟩

/-- The changed family is computed by the actual image-swap construction. -/
@[expose] def Challenge.changed (draw : Challenge q Word) (k : Fin q) :
    Label q → Equiv.Perm Word :=
  (sourceCut draw.bits k).splice draw.perms draw.seed draw.target

/-- Two worlds on common independent initial draws, differing only at the hidden cut. -/
@[expose] noncomputable def coupledDecision (original : Bool) (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) : Game :=
  challenges.bind fun draw =>
    interpret (Family.probEval (if original then draw.perms else draw.changed k))
      (adversary draw.seed draw.target)

/-- The unmodified coupling world is the source's independent-target decision experiment. -/
theorem coupledDecision_original (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) :
    coupledDecision true k adversary = decision false adversary := by
  simp only [coupledDecision, challenges, decision, pmf_norm, Bool.false_eq_true,
    ↓reduceIte, PMF.bind_const]
  congr 1 with seed : 1
  exact PMF.bind_comm _ _ _

/-- The changed coupling world is exactly the actual planted decision experiment, including
all subsequent adaptive observations. This is derived from the cut involution. -/
theorem coupledDecision_planted (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) :
    coupledDecision false k adversary = decision true adversary := by
  simp only [coupledDecision, challenges, decision, pmf_norm, Bool.false_eq_true,
    ↓reduceIte, PMF.bind_const]
  congr 1 with seed : 1
  congr 1 with bits : 1
  exact source_uniform_splice bits k seed fun perms target =>
    interpret (Family.probEval perms) (adversary seed target)

/-- The concrete experiment that runs the original world and detects a changed visible answer.
It contains only adversary calls, not the preinstalled path's sampling calls. -/
@[expose] noncomputable def visibleBadGame (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) : Game :=
  challenges.bind fun draw =>
    Visible.badGame draw.perms (draw.changed k) (adversary draw.seed draw.target)

/-- Actual planted-versus-independent decision advantage is bounded by the actual visible
stopping event. No bound on this event, coupling law or security conclusion is a premise. -/
theorem decision_advantage_le_visibleBad (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) Bool) :
    Game.advantage (decision true adversary) (decision false adversary) ≤
      Game.succProbability (visibleBadGame k adversary) := by
  rw [← coupledDecision_planted k, ← coupledDecision_original k, Game.advantage_comm]
  exact Game.advantage_bind_le_succProbability_bind challenges _ _ _ fun draw =>
    Visible.apply_le draw.perms (draw.changed k) (adversary draw.seed draw.target) true

/-- A search adversary followed by its actual verification walk. Only this continuation's
`q` calls, not hidden planting calls, augment the visible adversary transcript. -/
@[expose] def verifiedAdversary
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q))
    (seed target : Word) : ProbOracleComp (Spec q Word) Bool := do
  let bits ← adversary seed target
  let endpoint ← liftRight (walk (List.ofFn fun i => (i, bits i)) seed)
  return decide (endpoint = target)

omit [Fintype Word] [Nonempty Word] in
/-- The visible search-and-verification continuation has budget `T+q`, not `T+2*q`. -/
theorem verifiedAdversary_queryBound
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) (T : ℕ)
    (hT : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) T)
    (seed target : Word) :
    ProbOracleComp.IsQueryBounded (verifiedAdversary adversary seed target) (T + q) := by
  have hwalk (bits : Operators q) := walk_queryBound (List.ofFn fun i => (i, bits i)) seed
  simp only [List.length_ofFn] at hwalk
  simpa only [verifiedAdversary, Nat.add_zero] using
    (hT seed target).bind fun bits => (hwalk bits).bind fun endpoint =>
      IsCostBounded.pure (decide (endpoint = target)) 0

/-- The actual planted search game is the planted decision law applied to real verification.
No witness or execution correctness conclusion is assumed. -/
theorem plantedSearch_eq_verifiedDecision
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    plantedSearch adversary = decision true (verifiedAdversary adversary) := by
  simp only [plantedSearch, decision, verifiedAdversary, interpret_bind, interpret_pure,
    Family.probEval, interpret_sumHandler_liftRight, (walk_correct _ _ _).2, chain,
    pmf_norm, PMF.bind_const, ↓reduceIte]
  rfl

/-- Search and its independent-target counterpart are related by the proved visible coupling.
The first game's success is the actual original planted search success. Bounding the independent
verification probability and the visible stopping probability is still necessary for Theorem 8. -/
theorem search_comparison (k : Fin q)
    (adversary : Word → Word → ProbOracleComp (Spec q Word) (Operators q)) :
    Game.advantage (plantedSearch adversary) (decision false (verifiedAdversary adversary)) ≤
      Game.succProbability (visibleBadGame k (verifiedAdversary adversary)) := by
  rw [plantedSearch_eq_verifiedDecision]
  exact decision_advantage_le_visibleBad k (verifiedAdversary adversary)

end Cslib.Cryptanalysis.AddXNOR.IdealChain
