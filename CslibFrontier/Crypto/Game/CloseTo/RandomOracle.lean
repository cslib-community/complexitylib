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
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# The visible effect of one overwritten oracle entry

The result of a memoized oracle computation can change only if it queries the overwritten key.
The comparison projects away the private cache and charges the query probability in the
unmodified execution. It includes overwriting an existing entry with a different value.

## Main results

* `closeTo_run_interpret_memoize_cons`: visible-output closeness after prepending one entry.
* `closeTo_runWith_memoize_cons`: visible-output closeness for `ProbOracleComp.runWith` after
  prepending one fresh cache entry.
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

section RunWithMemoize

variable {Query Value : Type} [BEq Query] [LawfulBEq Query]

omit [LawfulBEq Query] in
private theorem lookup_isSome_of_mem_support_memoize {dist : Query → PMF Value}
    {k : Query} {cache : List (Query × Value)} {v : Value} {cache' : List (Query × Value)}
    (hstep : (v, cache') ∈ (memoize dist k cache).support) :
    ∀ x, (cache.lookup x).isSome = true → (cache'.lookup x).isSome = true := by
  intro x hx
  rcases (mem_support_memoize_iff dist k cache (v, cache')).mp hstep with
    ⟨-, hc⟩ | ⟨-, -, hc⟩
  · dsimp only at hc
    rw [hc]
    exact hx
  · dsimp only at hc
    rw [hc]
    simp only [List.lookup]
    cases (x == k) with
    | true => rfl
    | false => exact hx

omit [LawfulBEq Query] in
private theorem lookup_isSome_of_mem_support_runWith_memoize {α : Type}
    (dist : Query → PMF Value) (prog : ProbOracleComp (fun _ : Query => Value) α)
    {cache cache' : List (Query × Value)} {res : α}
    (hmem : (res, cache') ∈ (ProbOracleComp.runWith (memoize dist) prog cache).support) :
    ∀ x, (cache.lookup x).isSome = true → (cache'.lookup x).isSome = true := by
  refine ProbOracleComp.runWith_invariant (memoize dist)
    (fun c => ∀ x, (cache.lookup x).isSome = true → (c.lookup x).isSome = true)
    (fun k c hinv ans c' hstep x hx =>
      lookup_isSome_of_mem_support_memoize hstep x (hinv x hx))
    prog cache (fun _ h => h) res cache' hmem

private theorem closeTo_runWith_memoize_equiv {α : Type} (dist : Query → PMF Value)
    (target : Query) (value : Value) (prog : ProbOracleComp (fun _ : Query => Value) α)
    {c₁ c₂ : List (Query × Value)}
    (h1 : c₁.lookup target = some value)
    (h2 : c₂.lookup target = none)
    (hdiff : ∀ k ≠ target, c₁.lookup k = c₂.lookup k) :
    CloseTo
      ((ProbOracleComp.runWith (memoize dist) prog c₁).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog c₂).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog c₂).toOuterMeasure
        {x | (x.2.lookup target).isSome = true}) := by
  induction prog using ProbOracleComp.induction generalizing c₁ c₂ with
  | pure a =>
    simp only [ProbOracleComp.runWith_pure, PMF.pure_map]
    intro E
    exact le_add_of_nonneg_right zero_le
  | sample_bind n cont ih =>
    simp only [ProbOracleComp.runWith_sample_bind, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
    exact CloseTo.bind_right_tsum _ fun a _ => ih a h1 h2 hdiff
  | query_bind key cont ih =>
    by_cases hkey : key = target
    · subst hkey
      have hprob1 : (ProbOracleComp.runWith (memoize dist)
          (ProbOracleComp.query key >>= cont) c₂).toOuterMeasure
          {x | (x.2.lookup key).isSome = true} = 1 := by
        rw [PMF.toOuterMeasure_apply_eq_one_iff]
        rintro ⟨res, cache'⟩ hmem
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          PMF.mem_support_bind_iff] at hmem
        obtain ⟨⟨d, c₂'⟩, hstep, hcont⟩ := hmem
        dsimp only at hcont
        rcases (mem_support_memoize_iff dist key c₂ (d, c₂')).mp hstep with
          ⟨hsome, _⟩ | ⟨-, -, hc⟩
        · dsimp only at hsome
          rw [h2] at hsome
          exact False.elim (Option.some_ne_none _ hsome.symm)
        · dsimp only at hc
          have hlook : (c₂'.lookup key).isSome = true := by rw [hc]; simp
          exact lookup_isSome_of_mem_support_runWith_memoize dist (cont d) hcont key hlook
      rw [hprob1]
      intro E
      exact (Probability.PMF.toOuterMeasure_le_one _ E).trans le_add_self
    · have hlookup_eq : c₁.lookup key = c₂.lookup key := hdiff key hkey
      cases hcase : c₂.lookup key with
      | some ans =>
        have hcase1 : c₁.lookup key = some ans := hlookup_eq.trans hcase
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          memoize_of_some dist key c₁ ans hcase1, memoize_of_some dist key c₂ ans hcase,
          Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
        exact ih ans h1 h2 hdiff
      | none =>
        have hcase1 : c₁.lookup key = none := hlookup_eq.trans hcase
        simp only [ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
          memoize_of_none dist key c₁ hcase1, memoize_of_none dist key c₂ hcase,
          Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
          PMF.bind_bind, PMF.pure_bind, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
        refine CloseTo.bind_right_tsum (dist key) fun ans _ => ?_
        have hkey' : target ≠ key := Ne.symm hkey
        have hb : (target == key) = false := beq_false_of_ne hkey'
        refine ih ans ?_ ?_ ?_
        · simp [List.lookup, hb, h1]
        · simp [List.lookup, hb, h2]
        · intro k hk
          simp only [List.lookup]
          cases hbeq : (k == key) with
          | true => rfl
          | false => exact hdiff k hk

/-- **Prepending a fresh random-oracle cache entry (`ProbOracleComp.runWith`)**: inserting a single
entry `(target, value)` into a cache with `cache.lookup target = none` changes the output marginal
by at most the probability that the unmodified execution queries `target` (equivalently leaves
`target` present in its final cache). -/
theorem closeTo_runWith_memoize_cons {α : Type} (dist : Query → PMF Value)
    {cache : List (Query × Value)} {target : Query} (value : Value)
    (hnone : cache.lookup target = none)
    (prog : ProbOracleComp (fun _ : Query => Value) α) :
    CloseTo
      ((ProbOracleComp.runWith (memoize dist) prog ((target, value) :: cache)).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog cache).map Prod.fst)
      ((ProbOracleComp.runWith (memoize dist) prog cache).toOuterMeasure
        {x | (x.2.lookup target).isSome = true}) :=
  closeTo_runWith_memoize_equiv dist target value prog
    (by simp) hnone (fun k hk => by
      simp only [List.lookup]
      cases hbeq : (k == target) with
      | true => exact absurd (beq_iff_eq.mp hbeq) hk
      | false => rfl)

end RunWithMemoize

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
