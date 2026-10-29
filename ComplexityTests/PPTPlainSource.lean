/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Tactic.PPT

/-!
# Source-only probabilistic automation

Named calls with literal parameters retain their callback obligations; branch rules apply to
actual conditionals. Nested plain callbacks use the same raw-transition boundary as `polytime`.
Only the normal tactic module is imported, without compiled program producers.
-/

public section

open Cslib Cslib.Probability Turing.MultiTapeTM

namespace ComplexityTests.PPTPlainSource

/-- Fixed parameters for the named client programs. -/
structure Parameters where
  useCallback : Bool

/-- A named deterministic probabilistic program with a fixed branch parameter. -/
@[expose] def run (parameters : Parameters) (callback : List Bool → List Bool)
    (word : List Bool) : ProbComp (List Bool) :=
  pure (if parameters.useCallback then callback word else word)

/-- The named certificate requires a plain callback, independently of its implementation. -/
@[program_certificate hcallback]
theorem run_ppt (parameters : Parameters) {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (run parameters callback) := by
  have hcallback := hcallback.tidy
  fun_prop [run]

/-- The second named program captures one sampled fair bit. -/
@[expose] noncomputable def train (parameters : Parameters) (callback : List Bool → List Bool)
    (word : List Bool) : ProbComp (List Bool) := do
  let bit ← ProbComp.uniform Bool
  run parameters callback (bit :: word)

/-- Training has the same explicit plain callback obligation. -/
@[program_certificate hcallback]
theorem train_ppt (parameters : Parameters) {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (train parameters callback) := by
  have hcallback := hcallback.tidy
  fun_prop [train, run]

example (callback : List Bool → List Bool)
    (hcallback : ComputableInPolyTime callback encBits encBits)
    (condition : List Bool → Bool) (yes no : List Bool → ProbComp (List Bool))
    (hcondition : ComputableInPolyTime condition encBits encBool)
    (hyes : IsPPTOn encBits encBits yes) (hno : IsPPTOn encBits encBits no)
    (propCond : List Bool → Prop) [∀ word, Decidable (propCond word)]
    (hpropCond : ComputableInPolyTime (fun word => decide (propCond word)) encBits encBool) :
    IsPPTOn encBits encBits (run ⟨true⟩ callback) ∧
    IsPPTOn encBits encBits (train ⟨true⟩ callback) ∧
    IsPPTOn encBits encBits (fun word => if condition word then yes word else no word) ∧
    IsPPTOn encBits encBits (fun word => if propCond word then yes word else no word) := by
  refine ⟨?_, ?_, by ppt, by ppt⟩
  · fail_if_success (clear hcallback; ppt)
    ppt
  · fail_if_success (clear hcallback; ppt)
    ppt

/-- Opacity makes the nested plain certificate, rather than the program body, decisive. -/
@[irreducible] def consume (callback : List Bool → List Bool) (word : List Bool) :
    ProbComp (List Bool) := pure (callback word)

/-- A plain-premise named certificate for testing nested deterministic search. -/
@[program_certificate hcallback]
theorem consume_ppt {callback : List Bool → List Bool}
    (hcallback : ComputableInPolyTime callback encBits encBits) :
    IsPPTOn encBits encBits (consume callback) := by
  unfold consume
  exact hcallback.tidy.isPPTOn

/-- The global raw certificate cannot satisfy a nested plain callback obligation. -/
@[irreducible] def rawOnlyReverse (word : List Bool) : List Bool := word.reverse

/-- Construction evidence exists, so the negative checks search policy rather than impossibility. -/
@[fun_prop] theorem rawOnlyReverse_tidy :
    ComputableTidilyInPolyTime rawOnlyReverse encBits encBits := by
  unfold rawOnlyReverse
  fun_prop

/-- A complete predicate alias exercises the same boundary inside probabilistic search. -/
abbrev RawAliasFull {α β : Type*} (f : α → β)
    (input : α ↪ List Bool) (output : β ↪ List Bool) : Prop :=
  ComputableTidilyInPolyTime f input output

/-- Registering this transition must not expose raw search to the nested plain obligation. -/
@[fun_prop] theorem rawAlias_toPlain {α β : Type*} {f : α → β}
    {input : α ↪ List Bool} {output : β ↪ List Bool}
    (h : RawAliasFull f input output) : ComputableInPolyTime f input output :=
  .of_tidy h

/-- A future function rule may also hide its construction premise behind a full alias. -/
@[irreducible] def aliasPure (callback : List Bool → List Bool) (word : List Bool) :
    ProbComp (List Bool) := pure (callback word)

/-- This explicit construction theorem remains usable, but is not a public search fallback. -/
@[fun_prop] theorem aliasPure_raw {callback : List Bool → List Bool}
    (hcallback : RawAliasFull callback encBits encBits) :
    IsPPTOn encBits encBits (aliasPure callback) := by
  unfold aliasPure
  exact hcallback.isPPTOn

/-- An opaque plain contract is a legitimate source of a nested deterministic certificate. -/
@[irreducible] def PlainContract (callback : List Bool → List Bool) : Prop :=
  ComputableInPolyTime callback encBits encBits

attribute [fun_prop] PlainContract

/-- This ordinary plain transition remains available to the shared backend. -/
@[fun_prop] theorem PlainContract.computable {callback : List Bool → List Bool}
    (h : PlainContract callback) : ComputableInPolyTime callback encBits encBits := by
  unfold PlainContract at h
  exact h

-- Literal pure programs, `consume`, `aliasPure`, and `PlainContract` boundary checks.
example (callback : List Bool → List Bool)
    (hplain : ComputableInPolyTime callback encBits encBits)
    (hcontract : PlainContract callback) :
    IsPPTOn encBits encBits (fun word => pure (rawOnlyReverse word)) ∧
    IsPPTOn encBits encBits (fun word => pure (callback word)) ∧
    IsPPTOn encBits encBits (consume rawOnlyReverse) ∧
    IsPPTOn encBits encBits (consume callback) ∧
    IsPPTOn encBits encBits (aliasPure rawOnlyReverse) := by
  refine ⟨?_, by clear hcontract; ppt, ?_,
    by clear hplain; ppt, ?_⟩
  · fail_if_success (clear hplain hcontract; ppt)
    fun_prop
  · fail_if_success (clear hplain hcontract; ppt)
    exact consume_ppt (.of_tidy rawOnlyReverse_tidy)
  · fail_if_success (clear hplain hcontract; ppt)
    fun_prop

-- The raw-premise API is checked independently of the ordinary global-search example above.
example : IsPPTOn encBits encBits (aliasPure rawOnlyReverse) := by
  fail_if_success ppt
  exact aliasPure_raw rawOnlyReverse_tidy

/-- A reducible client wrapper keeps the actual iteration operation visible to dispatch. -/
abbrev wrappedIterate {State : Type} (count : ℕ) (step : State → ProbComp State)
    (initial : State) : ProbComp State :=
  OracleComp.iterate count step initial

example (step : List Bool → ProbComp (List Bool))
    (hstep : IsPPTOn encBits encBits step)
    (hshrink : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      next.length ≤ state.length)
    (growth : ℕ)
    (hgrowth : ∀ state next, next ∈ (ProbComp.eval (step state)).support →
      next.length ≤ state.length + growth)
    (step2 : List Bool → List Bool → ProbComp (List Bool))
    (hstep2 : IsPPTOn (encPair encBits encBits) encBits (fun pair => step2 pair.1 pair.2))
    (growth2 : List Bool → ℕ) (hpoly2 : PolyBounded List.length growth2)
    (hgrowth2 : ∀ word state next, next ∈ (ProbComp.eval (step2 word state)).support →
      next.length ≤ state.length + growth2 word) :
    IsPPTOn encBits encBits (fun word => OracleComp.iterate word.length step word) ∧
    IsPPTOn encBits encBits (fun word => OracleComp.iterate word.length step word) ∧
    IsPPTOn encBits encBits (fun word => wrappedIterate word.length step word) ∧
    IsPPTOn encBits encBits (fun word => wrappedIterate word.length step word) ∧
    IsPPTOn encBits encBits (fun word => wrappedIterate word.length (step2 word) word) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- Direct iteration with shrinking state.
  · clear growth hgrowth step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hstep; ppt)
    fail_if_success (clear hshrink; ppt)
    ppt
  -- Direct iteration with additive growth; shrinking evidence is unavailable.
  · clear hshrink step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hgrowth; ppt)
    ppt
  -- The wrapper also supports additive growth.
  · clear hshrink step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hgrowth; ppt)
    ppt
  -- Wrapped iteration with shrinking state; additive-growth evidence is unavailable.
  · clear growth hgrowth step2 hstep2 growth2 hpoly2 hgrowth2
    fail_if_success (clear hshrink; ppt)
    ppt
  -- Captured inputs have a polynomially bounded growth allowance.
  · clear step hstep hshrink growth hgrowth
    fail_if_success (clear hstep2; ppt)
    fail_if_success (clear hpoly2; ppt)
    fail_if_success (clear hgrowth2; ppt)
    ppt

/-- A distinct opaque result separates implication application
from direct certificate conversion. -/
@[irreducible] def implicationResult (word : List Bool) : ProbComp (List Bool) := pure word

/-- A global named theorem with a raw premise is an explicit construction API only. -/
@[program_certificate _h]
theorem implicationResult_raw (_h : RawAliasFull rawOnlyReverse encBits encBits) :
    IsPPTOn encBits encBits implicationResult := by
  unfold implicationResult
  fun_prop

-- Explicit construction and ordinary unfiltered search are independent of supplied evidence.
example : IsPPTOn encBits encBits implicationResult := by
  fail_if_success ppt
  exact implicationResult_raw rawOnlyReverse_tidy

example : IsPPTOn encBits encBits implicationResult := by
  fail_if_success ppt
  fun_prop

-- A local implication alone cannot launch raw search during nested preprocessing.
example (h : RawAliasFull rawOnlyReverse encBits encBits →
    ComputableInPolyTime rawOnlyReverse encBits encBits) :
    IsPPTOn (encPair encBits encBool) encBits (fun p => consume rawOnlyReverse p.1) := by
  fail_if_success ppt
  exact consume_ppt (h rawOnlyReverse_tidy) |>.preprocess
    (ComputableInPolyTime.fst encBits encBool)

-- Implication application, quantified families, global raw premises, and nested preprocessing.
example (h : RawAliasFull rawOnlyReverse encBits encBits →
      IsPPTOn encBits encBits implicationResult)
    (hf : RawAliasFull rawOnlyReverse encBits encBits)
    (family : ℕ → List Bool → List Bool)
    (hfamily : ∀ n, RawAliasFull (family n) encBits encBits) (n : ℕ)
    (callback : List Bool → List Bool) (hcb : RawAliasFull callback encBits encBits) :
    IsPPTOn encBits encBits implicationResult ∧
    IsPPTOn encBits encBits (consume (family n)) ∧
    IsPPTOn (encPair encBits encBool) encBits (fun p => consume callback p.1) ∧
    IsPPTOn (encPair encBits encBool) encBits (fun p => consume (family n) p.1) ∧
    IsPPTOn (encPair encBits encBool) encBits (fun p => consume rawOnlyReverse p.1) := by
  refine ⟨?_, by ppt, by ppt, by ppt, ?_⟩
  · fail_if_success (clear hf; ppt)
    ppt
  · fail_if_success (clear h hf hfamily hcb; ppt)
    exact consume_ppt (.of_tidy rawOnlyReverse_tidy) |>.preprocess
      (ComputableInPolyTime.fst encBits encBool)

-- Forced production dispatch retains every compatible supplied callback encoding, and without
-- local callback evidence the ordinary generic scan alternative remains available.
private meta def scanTwoLocalCallbacks : Aesop.RuleTac := fun input => do
  let result ← Cslib.Tactic.applyScanWithLocalCallback ``ComputableInPolyTime
    ``ComputableInPolyTime.anyWithInput input
  unless result.applications.size ≥ 2 do
    throwError "both compatible callback applications must survive"
  return result

example (test : List Bool × Bool × ℕ → Bool) (list : List Bool × Bool → List ℕ)
    (_hu : ComputableInPolyTime test (encPair encBits (encPair encBool encUnary)) encBool)
    (_hb : ComputableInPolyTime test (encPair encBits (encPair encBool encNat)) encBool)
    (_hlu : ComputableInPolyTime list (encPair encBits encBool) (encList encUnary))
    (_hlb : ComputableInPolyTime list (encPair encBits encBool) (encList encNat)) :
    ComputableInPolyTime
      (fun pair : List Bool × Bool => (list pair).any fun i => test (pair.1, pair.2, i))
      (encPair encBits encBool) encBool ∧
    ComputableInPolyTime
      (fun word : List Bool => [false, true].any fun bit => bit && word.isEmpty)
      encBits encBool := by
  refine ⟨?_, ?_⟩
  · run_tac Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        aesop (rule_sets := [-builtin, -default])
          (add unsafe 100% tactic scanTwoLocalCallbacks)))
  · clear test list _hu _hb _hlu _hlb
    polytime

end ComplexityTests.PPTPlainSource
