/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game.CloseTo
public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Languages.Probabilistic.Transcript
import Complexity.Languages.Probabilistic.UntilBad
import Complexity.Probability.PMF.Bind

/-!
# The visible effect of one overwritten oracle entry

The result of a memoized oracle computation can change only if it queries the overwritten key.
The comparison projects away the private cache and charges the query probability in the
unmodified execution. It includes overwriting an existing entry with a different value.

## Main results

* `closeTo_run_interpret_memoize_cons`: visible-output closeness after prepending one entry.

This is an original application of the existing identical-until-bad and random-oracle laws.
-/

public section

namespace Cslib.RandomOracle

open Crypto Probability OracleComp Interactive
open scoped ENNReal

variable {Query Value α : Type} [DecidableEq Query]

omit [DecidableEq Query] in
private theorem visible_closeTo_of_untilBad {State : Type}
    {first second : Query → StateT State PMF Value} {bad : State → Prop}
    (h : IdenticalUntilBad first second bad) (program : OracleComp (fun _ : Query => Value) α)
    (state : State) :
    CloseTo (((interpret first program).run state).map Prod.fst)
      (((interpret second program).run state).map Prod.fst)
      (((interpret second program).run state).toOuterMeasure {out | bad out.2}) := by
  classical
  intro event
  let test : α × State → PMF Bool := fun out => PMF.pure (decide (out.1 ∈ event))
  have ht (μ : PMF (α × State)) :
      (μ.bind test) true = (μ.map Prod.fst).toOuterMeasure event := by
    change (μ.map (fun out => decide (out.1 ∈ event))) true = _
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext out
    simp
  have hb := h.bind_apply_le program state test true
  rw [ht, ht, h.bad_eq] at hb
  exact hb

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
      congr 1
      funext v
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

/-- Pointwise error bounds on mixtures under `CloseTo`. -/
theorem closeTo_bind_of_le {β γ : Type} (μ : PMF β) (f g : β → PMF γ) (err : β → Game)
    (h : ∀ a ∈ μ.support, ∀ test : γ → Bool,
      ((f a).map test) true ≤ ((g a).map test) true + err a true ∧
      ((g a).map test) true ≤ ((f a).map test) true + err a true) :
    CloseTo (μ.bind f) (μ.bind g) ((μ.bind err) true) := by
  classical
  let g' : β → PMF γ := fun a => if a ∈ μ.support then g a else f a
  have hg : μ.bind g' = μ.bind g := Probability.PMF.bind_congr_on_support μ _ _
    (fun a ha => by simp only [g', ha, ↓reduceIte])
  rw [← hg]
  apply Game.closeTo_of_coe_advantage_decide_le
  intro event
  let test : γ → Bool := fun b => decide (b ∈ event)
  have he (a : β) :
      ((f a).map test) true ≤ ((g' a).map test) true + err a true ∧
      ((g' a).map test) true ≤ ((f a).map test) true + err a true := by
    by_cases ha : a ∈ μ.support
    · simpa only [g', ha, ↓reduceIte] using h a ha test
    · simp only [g', ha, ↓reduceIte]
      exact ⟨le_add_of_nonneg_right zero_le,
        le_add_of_nonneg_right zero_le⟩
  have hadv := Game.advantage_bind_le_succProbability_bind μ
    (fun a => (f a).map test) (fun a => (g' a).map test) err he
  have hc := ENNReal.coe_le_coe.mpr hadv
  rw [Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at hc
  simpa only [PMF.map_bind] using hc

end Cslib.RandomOracle
