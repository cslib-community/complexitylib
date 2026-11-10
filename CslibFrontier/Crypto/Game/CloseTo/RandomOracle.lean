/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Languages.Probabilistic.RandomOracle
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
public import CslibFrontier.Languages.Probabilistic.Transcript
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF.Bind

/-!
# The visible effect of one overwritten oracle entry

The result of a memoized oracle computation can change only if it queries the overwritten key.
The comparison projects away the private cache and charges the query probability in the
unmodified execution. It includes overwriting an existing entry with a different value.

## Main results

* `closeTo_run_interpret_memoize_cons`: visible-output closeness after prepending one entry.
* `entry_mem_iff_lookup_isSome`: transcript query membership agrees with key lookup on the pair
  projection.
* `coe_advantage_lazyProgramHandler_overwriteProgramHandler_choose_two_le`,
  `advantage_lazyProgramHandler_overwriteProgramHandler_choose_two_le`,
  `advantage_lazyProgramHandler_overwriteProgramHandler_le`,
  `advantage_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two_le`: `Game.advantage`
  corollaries of the min-entropy adaptive random-oracle programming hop.

This is an original application of the existing identical-until-bad and random-oracle laws.
-/

public section

namespace Cslib.RandomOracle

open Crypto Probability OracleComp Interactive
open scoped ENNReal NNReal

variable {Query Value α : Type} [DecidableEq Query]

omit [DecidableEq Query] in
private theorem visible_closeTo_of_untilBad {State : Type}
    {first second : Query → StateT State PMF Value} {bad : State → Prop}
    (h : IdenticalUntilBad first second bad) (program : OracleComp (fun _ : Query => Value) α)
    (state : State) :
    CloseTo (((interpret first program).run state).map Prod.fst)
      (((interpret second program).run state).map Prod.fst)
      (((interpret second program).run state).toOuterMeasure {out | bad out.2}) := by
  rw [← h.bad_eq]
  exact (h.closeTo_run program state).map Prod.fst

private noncomputable def replaceAnswer (distribution : Query → PMF Value)
    (target : Query) (value : Value) (q : Query) :
    StateT (Cache (fun _ : Query => Value)) PMF Value :=
  fun cache => if q = target then PMF.pure (value, Function.update cache target (some value))
    else answer distribution q cache

private theorem replaceAnswer_map (distribution : Query → PMF Value)
    (target : Query) (value : Value) (q : Query) (cache : Cache (fun _ : Query => Value)) :
    (replaceAnswer distribution target value q cache).map
        (fun out => (out.1, Function.update out.2 target (some value))) =
      answer distribution q (Function.update cache target (some value)) := by
  classical
  by_cases hq : q = target
  · subst q
    simp [replaceAnswer, answer]
  · simp only [replaceAnswer, hq, ↓reduceIte, answer,
      Function.update_of_ne hq]
    cases hc : cache q with
    | some v => simp
    | none =>
      simp only [PMF.map_comp, Function.comp_def]
      congr 1 with v : 1
      congr 1
      exact Function.update_comm hq _ _ _

private theorem replaceAnswer_run (distribution : Query → PMF Value)
    (target : Query) (value : Value) (program : OracleComp (fun _ : Query => Value) α)
    (cache : Cache (fun _ : Query => Value)) :
    ((interpret (replaceAnswer distribution target value) program).run cache).map
        (fun out => (out.1, Function.update out.2 target (some value))) =
      (interpret (answer distribution) program).run
        (Function.update cache target (some value)) := by
  exact run_interpret_map_state (replaceAnswer distribution target value) (answer distribution)
    (fun cache => Function.update cache target (some value))
    (replaceAnswer_map distribution target value) program cache

omit [DecidableEq Query] in
private theorem transcript_absorb
    (handler : Query → StateT (Cache (fun _ : Query => Value)) PMF Value)
    (target : Query) (q : Query) (state : Cache (fun _ : Query => Value) ×
      Transcript (fun _ : Query => Value))
    (h : ∃ entry ∈ state.2, entry.1 = target) :
    ∀ out ∈ (withTranscript handler q state).support,
      ∃ entry ∈ out.2.2, entry.1 = target := by
  intro out hout
  obtain ⟨⟨reply, cache⟩, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨entry, he, ht⟩ := h
  exact ⟨entry, List.mem_cons_of_mem _ he, ht⟩

private theorem replaceAnswer_untilBad (distribution : Query → PMF Value)
    (target : Query) (value : Value) :
    IdenticalUntilBad
      (withTranscript (replaceAnswer distribution target value))
      (withTranscript (answer distribution))
      (fun state => ∃ entry ∈ state.2, entry.1 = target) where
  agree q state _ reply next hgood := by
    classical
    by_cases hq : q = target
    · subst q
      have hz (handler : Query → StateT (Cache (fun _ : Query => Value)) PMF Value) :
          withTranscript handler target state (reply, next) = 0 := by
        by_contra hnonzero
        have hmem := (PMF.mem_support_iff _ _).mpr hnonzero
        obtain ⟨⟨r, cache⟩, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hmem
        cases he
        exact hgood ⟨⟨target, reply⟩, List.mem_cons_self, rfl⟩
      rw [hz, hz]
    · simp only [withTranscript, replaceAnswer, hq, ↓reduceIte]
  absorb_first q state hs := transcript_absorb _ target q state hs
  absorb_second q state hs := transcript_absorb _ target q state hs

private theorem closeTo_answer_update (distribution : Query → PMF Value)
    (target : Query) (value : Value) (program : OracleComp (fun _ : Query => Value) α)
    (cache : Cache (fun _ : Query => Value)) :
    CloseTo
      (((interpret (answer distribution) program).run
        (Function.update cache target (some value))).map Prod.fst)
      (((interpret (answer distribution) program).run cache).map Prod.fst)
      (((interpret (withTranscript (answer distribution)) program).run (cache, [])).toOuterMeasure
        {out | ∃ entry ∈ out.2.2, entry.1 = target}) := by
  have h := visible_closeTo_of_untilBad (replaceAnswer_untilBad distribution target value)
    program (cache, [])
  have hl := congrArg (PMF.map Prod.fst)
    (run_interpret_withTranscript (replaceAnswer distribution target value) program cache [])
  have hr := congrArg (PMF.map Prod.fst)
    (run_interpret_withTranscript (answer distribution) program cache [])
  have hp := congrArg (PMF.map Prod.fst)
    (replaceAnswer_run distribution target value program cache)
  simp only [PMF.map_comp, Function.comp_def] at hl hr hp
  rw [hl, hr, hp] at h
  exact h

/-- Prepending one entry changes the visible result law by at most the probability that the
unmodified execution queries its key. The final private caches are not compared. -/
theorem closeTo_run_interpret_memoize_cons (distribution : Query → PMF Value)
    (target : Query) (value : Value) (program : OracleComp (fun _ : Query => Value) α)
    (cache : List (Query × Value)) :
    CloseTo
      (((interpret (memoize distribution) program).run ((target, value) :: cache)).map Prod.fst)
      (((interpret (memoize distribution) program).run cache).map Prod.fst)
      (((interpret (withTranscript (memoize distribution)) program).run (cache, [])).toOuterMeasure
        {out | ∃ entry ∈ out.2.2, entry.1 = target}) := by
  classical
  have h := closeTo_answer_update distribution target value program (ofList cache)
  have hl := congrArg (PMF.map Prod.fst)
    (run_interpret_memoize distribution program ((target, value) :: cache))
  have hr := congrArg (PMF.map Prod.fst) (run_interpret_memoize distribution program cache)
  simp only [PMF.map_comp, Function.comp_def, ofList_cons] at hl hr
  have htrace :
      ((interpret (withTranscript (memoize distribution)) program).run (cache, [])).map
        (fun out => (out.1, ofList out.2.1, out.2.2)) =
      (interpret (withTranscript (answer distribution)) program).run (ofList cache, []) := by
    apply run_interpret_map_state (withTranscript (memoize distribution))
      (withTranscript (answer distribution)) (fun state => (ofList state.1, state.2))
    intro q state
    have hq := run_interpret_memoize distribution (OracleComp.query q) state.1
    simp only [run_interpret_query] at hq
    have hm := congrArg (PMF.map (fun out => (out.1, out.2, ⟨q, out.1⟩ :: state.2))) hq
    simpa only [withTranscript, PMF.map_comp, Function.comp_def] using hm
  have he := congrArg (fun μ => μ.toOuterMeasure
    {out | ∃ entry ∈ out.2.2, entry.1 = target}) htrace
  rw [PMF.toOuterMeasure_map_apply] at he
  rw [← hl, ← hr, ← he] at h
  exact h

/-- Transcript query membership agrees with key lookup on the pair projection. -/
theorem entry_mem_iff_lookup_isSome {Query Value : Type} [DecidableEq Query]
    (tr : List (Σ _ : Query, Value)) (target : Query) :
    (∃ entry ∈ tr, entry.1 = target) ↔
      ((tr.map fun entry : (Σ _ : Query, Value) => (entry.1, entry.2)).lookup target).isSome := by
  constructor
  · rintro ⟨entry, hmem, rfl⟩
    have hp : (entry.1, entry.2) ∈ tr.map (fun entry => (entry.1, entry.2)) :=
      List.mem_map.mpr ⟨entry, hmem, rfl⟩
    exact List.lookup_isSome_iff.mpr ⟨(entry.1, entry.2), hp, beq_self_eq_true entry.1⟩
  · intro h
    obtain ⟨p, hp, he⟩ := List.lookup_isSome_iff.mp h
    have heq : target = p.1 := eq_of_beq he
    obtain ⟨entry, hmem, rfl⟩ := List.mem_map.mp hp
    subst heq
    exact ⟨entry, hmem, rfl⟩

/-! ### `Game.advantage` bounds for adaptive random-oracle programming -/

section AdvantageProgramming

variable {Req Digest Log : Type} {Reply : Req → Type} {Coins : Req → Type}

omit [DecidableEq Query] in
/-- **Sharpened adaptive RO programming `Game.advantage` bound in `ℝ≥0∞` (`OracleComp`)**:
postprocessing `lazyProgramHandler` vs. `overwriteProgramHandler` by `next` changes the game's
acceptance probability by at most `(q_S * cache.length + q_S * q_H + q_S.choose 2) * δ`. -/
theorem coe_advantage_lazyProgramHandler_overwriteProgramHandler_choose_two_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0∞} (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ δ)
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log)
    (next : α × (List (Query × Digest) × Log) → Game) :
    (Game.advantage
      (((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next)
      (((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next) : ℝ≥0∞) ≤
      (q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ :=
  Game.coe_advantage_bind_le_of_closeTo
    (closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two dist active inactive
      samplePre point finish hminEnt hqS hqH cache log) next

omit [DecidableEq Query] in
/-- **Sharpened adaptive RO programming `Game.advantage` bound in `ℝ≥0` (`OracleComp`)**. -/
theorem advantage_lazyProgramHandler_overwriteProgramHandler_choose_two_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0}
    (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ (δ : ℝ≥0∞))
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log)
    (next : α × (List (Query × Digest) × Log) → Game) :
    Game.advantage
      (((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next)
      (((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next) ≤
      (q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ := by
  have h := coe_advantage_lazyProgramHandler_overwriteProgramHandler_choose_two_le dist active
    inactive samplePre point finish hminEnt hqS hqH cache log next
  exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using h)

omit [DecidableEq Query] in
/-- **Rectangular adaptive RO programming `Game.advantage` bound in `ℝ≥0` (`OracleComp`)**:
`(q_S * (cache.length + q_S + q_H)) * δ` form. -/
theorem advantage_lazyProgramHandler_overwriteProgramHandler_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0}
    (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ (δ : ℝ≥0∞))
    {program : OracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program q_H)
    (cache : List (Query × Digest)) (log : Log)
    (next : α × (List (Query × Digest) × Log) → Game) :
    Game.advantage
      (((interpret (lazyProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next)
      (((interpret (overwriteProgramHandler dist active inactive samplePre point finish)
        program).run (cache, log)).bind next) ≤
      (q_S * (cache.length + q_S + q_H) : ℕ) * δ := by
  have h := Game.coe_advantage_bind_le_of_closeTo
    (closeTo_run_lazyProgramHandler_overwriteProgramHandler dist active inactive samplePre point
      finish hminEnt hqS hqH cache log) next
  exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using h)

omit [DecidableEq Query] in
/-- **Sharpened adaptive RO programming `Game.advantage` bound in `ℝ≥0`
(`ProbOracleComp.runWith`)**. -/
theorem advantage_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two_le
    [BEq Query] [LawfulBEq Query]
    (dist : PMF Digest) (active : Req → Bool)
    (inactive : (req : Req) → active req = false → Log → PMF (Reply req × Log))
    (samplePre : (req : Req) → PMF (Coins req))
    (point : (req : Req) → Coins req → Query)
    (finish : (req : Req) → Coins req → Digest → Log → Reply req × Log)
    {δ : ℝ≥0}
    (hminEnt : ∀ req, active req = true → ∀ q, ((samplePre req).map (point req)) q ≤ (δ : ℝ≥0∞))
    {program : ProbOracleComp (Reply ⊕ₒ fun _ : Query => Digest) α} {q_S q_H : ℕ}
    (hqS : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 1) (fun _ => 0))) program q_S)
    (hqH : IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) program q_H)
    (cache : List (Query × Digest)) (log : Log)
    (next : α × (List (Query × Digest) × Log) → Game) :
    Game.advantage
      ((ProbOracleComp.runWith
        (lazyProgramHandler dist active inactive samplePre point finish) program
          (cache, log)).bind next)
      ((ProbOracleComp.runWith
        (overwriteProgramHandler dist active inactive samplePre point finish) program
          (cache, log)).bind next) ≤
      (q_S * cache.length + q_S * q_H + q_S.choose 2 : ℕ) * δ := by
  have h := Game.coe_advantage_bind_le_of_closeTo
    (closeTo_runWith_lazyProgramHandler_overwriteProgramHandler_choose_two dist active inactive
      samplePre point finish hminEnt hqS hqH cache log) next
  exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_mul, ENNReal.coe_natCast] using h)

end AdvantageProgramming

end Cslib.RandomOracle
