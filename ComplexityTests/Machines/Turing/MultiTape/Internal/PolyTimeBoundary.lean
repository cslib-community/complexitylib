/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PolyTime

/-!
# Plain automation from a source-only import

This module imports the tactic directly, without compiled program certificates whose proof
bodies might make its internal construction lemmas available incidentally. The named shrinking
step has the same nonincreasing fold contract used by the GGM evaluator.
-/

public section

open Turing.MultiTapeTM

namespace ComplexityTests.PolyTimePlainSource

/-- A total step which truncates a routine output to the current state length. -/
@[expose] def shrinkingStep (routine : List Bool → List Bool) (state : List Bool) (_ : Bool) :
    List Bool :=
  (routine state).take state.length

private theorem shrinkingStep_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime (fun p : List Bool × Bool => shrinkingStep routine p.1 p.2)
      (encPair encBits encBool) encBits := by
  fun_prop [shrinkingStep]

private theorem shrinkingStep_length (routine : List Bool → List Bool)
    (state : List Bool) (bit : Bool) :
    (shrinkingStep routine state bit).length ≤ state.length := by
  simp only [shrinkingStep, List.length_take]
  exact Nat.min_le_left _ _

/-- Source-only named folding uses the runtime helper declarations from the tactic import. -/
theorem shrinkingFold_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => p.2.foldl (shrinkingStep routine) p.1)
      (encPair encBits encBits) encBits := by
  have hstep := shrinkingStep_polyTime hroutine
  have hgrowth := shrinkingStep_length routine
  polytime

/-- The framed-query variant exercises the separate framed-list fold adapter. -/
theorem shrinkingFramedFold_polyTime {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime
      (fun p : List Bool × List Bool => p.2.foldl (shrinkingStep routine) p.1)
      (encPair encBits (encList encBool)) encBits := by
  have hstep := shrinkingStep_polyTime hroutine
  have hgrowth := shrinkingStep_length routine
  polytime

example {routine : List Bool → List Bool}
    (hroutine : ComputableInPolyTime routine encBits encBits) (growth : ℕ) :
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
      (encPair encBits encBits) encBits ∧
    ComputableInPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
      (encPair (encList encBool) (encList encBool)) (encList encBool) ∧
    ComputableInPolyTime (fun p : Bool × List Bool => p.1 :: p.2)
      (encPair encBool (encList encBool)) (encList encBool) ∧
    ComputableInPolyTime (fun p : Bool × List Bool => p.1 :: p.2)
      (encPair encBool encBits) encBits ∧
    ComputableInPolyTime
      (fun p : ℕ × List Bool => (fun state => shrinkingStep routine state true)^[p.1] p.2)
      (encPair encUnary encBits) encBits := by
  have hstep : ComputableInPolyTime (fun state => shrinkingStep routine state true)
      encBits encBits := by fun_prop [shrinkingStep]
  have hgrowth : ∀ state, (shrinkingStep routine state true).length ≤ state.length + growth := by
    intro state
    exact (shrinkingStep_length routine state true).trans (Nat.le_add_right _ _)
  exact ⟨by polytime, by polytime, by polytime, by polytime, by polytime⟩

-- A reducible full-arity alias must not disguise a raw search transition.
/-- This routine has only a global raw certificate and stays opaque to plain search. -/
@[irreducible] def rawOnlyReverseProbe (word : List Bool) : List Bool := word.reverse

/-- Construction evidence does not automatically become a plain search rule. -/
@[fun_prop] theorem rawOnlyReverseProbe_tidy :
    ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits := by
  unfold rawOnlyReverseProbe
  exact ComputableInPolyTime.bitsReverse.tidy

/-- All predicate arguments are explicit, as in an ordinary client-defined abbreviation. -/
abbrev RawAliasFull {α β : Type*} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ComputableTidilyInPolyTime f input output

/-- Even an explicitly registered alias transition must not enable raw search in plain mode. -/
@[fun_prop] theorem rawAliasFull_toPlain {α β : Type*} {f : α → β}
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : RawAliasFull f input output) : ComputableInPolyTime f input output :=
  .of_tidy h

/-- Function-table rules must respect the same boundary as transition rules. -/
@[irreducible] def aliasRoutine (routine : List Bool → List Bool) (word : List Bool) :
    List Bool := routine word

/-- The explicit proof API remains usable, while its aliased raw premise excludes global search. -/
@[fun_prop] theorem aliasRoutine_plain {routine : List Bool → List Bool}
    (h : RawAliasFull routine encBits encBits) :
    ComputableInPolyTime (aliasRoutine routine) encBits encBits := by
  unfold aliasRoutine
  exact .of_tidy h

-- Explicit proofs and ordinary global search run in separate conjuncts and local contexts.
example :
    ComputableInPolyTime rawOnlyReverseProbe encBits encBits ∧
    ComputableInPolyTime (aliasRoutine rawOnlyReverseProbe) encBits encBits ∧
    ComputableInPolyTime (aliasRoutine rawOnlyReverseProbe) encBits encBits := by
  refine ⟨?_, ?_, ?_⟩
  · fail_if_success polytime
    exact .of_tidy rawOnlyReverseProbe_tidy
  · fail_if_success polytime
    exact aliasRoutine_plain rawOnlyReverseProbe_tidy
  · fail_if_success polytime
    fun_prop

/-- A distinct opaque result makes implication consumption, rather than fact conversion,
decisive. -/
@[irreducible] def localImplicationResult (word : List Bool) : List Bool := word

-- Without the raw fact, a local implication cannot launch global raw search. Ordinary
-- `fun_prop` still uses the same implication and existing global construction proof afterward.
-- The supplied-raw `polytime` check is a separate conjunct from that `fun_prop` fallback.
example (h : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits →
      ComputableInPolyTime localImplicationResult encBits encBits)
    (hf : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits)
    (hprobe : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits →
      ComputableInPolyTime rawOnlyReverseProbe encBits encBits)
    (halias : RawAliasFull rawOnlyReverseProbe encBits encBits →
      ComputableInPolyTime localImplicationResult encBits encBits) :
    ComputableInPolyTime localImplicationResult encBits encBits ∧
    ComputableInPolyTime localImplicationResult encBits encBits ∧
    ComputableInPolyTime rawOnlyReverseProbe encBits encBits ∧
    ComputableInPolyTime localImplicationResult encBits encBits := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · clear hprobe halias
    fail_if_success (clear hf; polytime)
    clear hf
    fun_prop
  · clear hprobe halias
    polytime
  · clear h hf halias
    fail_if_success polytime
    exact hprobe rawOnlyReverseProbe_tidy
  · clear h hf hprobe
    fail_if_success polytime
    fun_prop

/-- The index is visible to local theorem matching, rather than an unconstrained parameter. -/
@[irreducible] def indexedRawOnly (_index : ℕ) (word : List Bool) : List Bool := word.reverse

/-- Global raw evidence exists for every index, so the quantified negative is not vacuous. -/
@[fun_prop] theorem indexedRawOnly_tidy (index : ℕ) :
    ComputableTidilyInPolyTime (indexedRawOnly index) encBits encBits := by
  unfold indexedRawOnly
  exact ComputableInPolyTime.bitsReverse.tidy

/-- The corresponding result has no public global certificate. -/
@[irreducible] def indexedLocalResult (_index : ℕ) (word : List Bool) : List Bool := word

-- Quantified fallback and supplied-evidence search are likewise checked independently.
example (h : ∀ index, RawAliasFull (indexedRawOnly index) encBits encBits →
      ComputableInPolyTime (indexedLocalResult index) encBits encBits)
    (hf : ∀ index, RawAliasFull (indexedRawOnly index) encBits encBits)
    (routine : ℕ → List Bool → List Bool)
    (hplain : ∀ index, ComputableInPolyTime (routine index) encBits encBits)
    (htidy : ∀ index, ComputableTidilyInPolyTime (routine index) encBits encBits)
    (index : ℕ) :
    ComputableInPolyTime (indexedLocalResult 0) encBits encBits ∧
    ComputableInPolyTime (indexedLocalResult 0) encBits encBits ∧
    ComputableInPolyTime (routine index) encBits encBits ∧
    ComputableTidilyInPolyTime (routine index) encBits encBits := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · clear routine hplain htidy index
    fail_if_success (clear hf; polytime)
    clear hf
    fun_prop
  · clear routine hplain htidy index
    polytime
  · clear h hf htidy
    fail_if_success (clear hplain; polytime)
    polytime
  · clear h hf hplain
    fail_if_success (clear htidy; polytime)
    polytime

/-- A named result is opaque to generic decomposition. -/
@[irreducible] def namedConditionalResult (word : List Bool) : List Bool := rawOnlyReverseProbe word

/-- The explicit conditional API is valid, but cannot initiate raw search in plain automation. -/
@[program_certificate h]
theorem namedConditional_plain
    (h : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits) :
    ComputableInPolyTime namedConditionalResult encBits encBits := by
  unfold namedConditionalResult
  exact .of_tidy h

/-- A separate named target isolates the full-arity alias variant. -/
@[irreducible] def namedAliasResult (word : List Bool) : List Bool := rawOnlyReverseProbe word

/-- Alias normalization also applies to named certificate premises. -/
@[program_certificate h]
theorem namedAlias_plain (h : RawAliasFull rawOnlyReverseProbe encBits encBits) :
    ComputableInPolyTime namedAliasResult encBits encBits := by
  unfold namedAliasResult
  exact .of_tidy h

/-- The matching raw construction key must retain its conditional certificate. -/
@[program_certificate h]
theorem namedConditional_raw (h : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits) :
    ComputableTidilyInPolyTime namedConditionalResult encBits encBits := by
  unfold namedConditionalResult
  exact h

/-- This ordinary plain certificate has a genuine eager callback obligation. -/
@[irreducible] def safeNamedResult (routine : List Bool → List Bool) (word : List Bool) :
    List Bool := routine word

/-- Production named lookup must retain ordinary plain premises and their eager contract. -/
@[program_certificate h]
theorem safeNamed_plain {routine : List Bool → List Bool}
    (h : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime (safeNamedResult routine) encBits encBits := by
  unfold safeNamedResult
  exact h

private meta def plainNamedOnly : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``ComputableInPolyTime

private meta def rawNamedOnly : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``ComputableTidilyInPolyTime

-- The explicit named API must not put its conclusion in scope for the global search check.
example (routine : List Bool → List Bool)
    (h : ComputableInPolyTime routine encBits encBits) :
    ComputableInPolyTime namedConditionalResult encBits encBits ∧
    ComputableInPolyTime namedConditionalResult encBits encBits ∧
    ComputableInPolyTime namedAliasResult encBits encBits ∧
    ComputableInPolyTime (safeNamedResult routine) encBits encBits ∧
    ComputableTidilyInPolyTime namedConditionalResult encBits encBits := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · clear routine h
    fail_if_success polytime
    exact namedConditional_plain rawOnlyReverseProbe_tidy
  · clear routine h
    fail_if_success polytime
    fun_prop
  · clear routine h
    fail_if_success polytime
    exact namedAlias_plain rawOnlyReverseProbe_tidy
  · fail_if_success (clear h; polytime)
    fail_if_success aesop
    run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        aesop (rule_sets := [-builtin, -default]) (add unsafe 100% tactic plainNamedOnly)))
  · clear routine h
    fail_if_success aesop
    run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        aesop (rule_sets := [-builtin, -default]) (add unsafe 100% tactic rawNamedOnly)))

/-- A genuine plain eager premise starts its own nested certificate search. -/
@[irreducible] def eagerLocalResult (word : List Bool) : List Bool := localImplicationResult word

/-- The eager contract itself is plain and must remain registered. -/
@[program_certificate h]
theorem eagerLocal_plain (h : ComputableInPolyTime localImplicationResult encBits encBits) :
    ComputableInPolyTime eagerLocalResult encBits encBits := by
  unfold eagerLocalResult
  exact h

/-- The reverse conversion likewise uses only an existing local plain certificate. -/
abbrev PlainAliasFull {α β : Type*} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ComputableInPolyTime f input output

/-- Ordinary plain contracts remain a supported transition source. -/
@[irreducible] def RoutineContract (f : List Bool → List Bool) : Prop :=
  ComputableInPolyTime f encBits encBits

attribute [fun_prop] RoutineContract

/-- The plain transition remains available after raw alias transitions are registered. -/
@[fun_prop] theorem RoutineContract.computable {f : List Bool → List Bool}
    (hf : RoutineContract f) : ComputableInPolyTime f encBits encBits := by
  unfold RoutineContract at hf
  exact hf

-- The explicit eager API and nested supplied-evidence search have independent proof contexts.
example (h : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits →
      ComputableInPolyTime localImplicationResult encBits encBits)
    (hf : ComputableTidilyInPolyTime rawOnlyReverseProbe encBits encBits)
    (routine : List Bool → List Bool)
    (hplain : ComputableInPolyTime routine encBits encBits)
    (hrawAlias : RawAliasFull routine encBits encBits)
    (hplainAlias : PlainAliasFull routine encBits encBits)
    (hc : RoutineContract routine)
    (hcImp : RoutineContract routine →
      ComputableInPolyTime localImplicationResult encBits encBits) :
    ComputableInPolyTime eagerLocalResult encBits encBits ∧
    ComputableInPolyTime eagerLocalResult encBits encBits ∧
    (ComputableInPolyTime routine encBits encBits ∧
      ComputableInPolyTime localImplicationResult encBits encBits) ∧
    ComputableInPolyTime localImplicationResult encBits encBits ∧
    ComputableInPolyTime routine encBits encBits ∧
    ComputableTidilyInPolyTime routine encBits encBits ∧
    ComputableInPolyTime rawOnlyReverseProbe encBits encBits ∧
    ComputableInPolyTime routine encBits encBits ∧
    ComputableInPolyTime localImplicationResult encBits encBits := by
  refine ⟨?_, ?_, ?_, ?_, by clear h hf hplain hplainAlias hc hcImp; polytime,
    by clear h hf hplain hrawAlias hc hcImp; polytime, ?_,
    by clear h hf hplain hrawAlias hplainAlias hcImp; polytime, ?_⟩
  · clear routine hplain hrawAlias hplainAlias hc hcImp
    fail_if_success (clear hf; polytime)
    exact eagerLocal_plain (h rawOnlyReverseProbe_tidy)
  · clear routine hplain hrawAlias hplainAlias hc hcImp
    polytime
  · clear hf hrawAlias hplainAlias hc hcImp
    fail_if_success (clear hplain; polytime)
    refine ⟨by polytime, ?_⟩
    fail_if_success polytime
    aesop (rule_sets := [PolyTime])
  · clear hf routine hplain hrawAlias hplainAlias hc hcImp
    run_tac do
      try
        Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
          throwError "test scoped restoration"
      catch _ => pure ()
      Lean.Elab.Tactic.evalTactic (← `(tactic| aesop (rule_sets := [PolyTime])))
  · clear h hf routine hplain hrawAlias hplainAlias hc hcImp
    fail_if_success polytime
    exact .of_tidy rawOnlyReverseProbe_tidy
  · clear h hf hplain hrawAlias hplainAlias
    fail_if_success (clear hc; polytime)
    polytime

end ComplexityTests.PolyTimePlainSource

-- A specialized raw Boolean fold does not block the generic direct captured-fold recipe.
section
variable {γ α β : Type} (input : γ ↪ List Bool) (element : α ↪ List Bool)
    (stateEncoding : β ↪ List Bool) (listEncoding : List α ↪ List Bool)
    [ListEncoding element listEncoding] [SizedListEncoding element listEncoding]
    (list : γ → List α) (initial : γ → β) (step : γ → β → α → β)
    (hlist : ComputableTidilyInPolyTime list input listEncoding)
    (hinitial : ComputableTidilyInPolyTime initial input stateEncoding)
    (hstep : ComputableTidilyInPolyTime (fun p : (γ × β) × α => step p.1.1 p.1.2 p.2)
      (encPair (encPair input stateEncoding) element) stateEncoding)
    (growth : γ → ℕ) (hpoly : PolyBounded (fun x => (input x).length) growth)
    (hgrowth : ∀ x state value, value ∈ list x →
      (stateEncoding (step x state value)).length ≤ (stateEncoding state).length + growth x)

example : ComputableTidilyInPolyTime
    (fun x => (list x).foldl (fun state value => step x state value) (initial x))
      input stateEncoding := by
  polytime

end
