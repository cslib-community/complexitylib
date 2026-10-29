/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Tactic.PolyTime
public import Complexity.Computability.Probabilistic.PPT.Capture
public import Complexity.Computability.Probabilistic.Sampling
public import Complexity.Computability.Probabilistic.Adaptive
public import Complexity.Computability.Probabilistic.Parameter
public import Complexity.Computability.Probabilistic.Memoize

/-!
# Certifying functional probabilistic programs

`ppt` combines the proved closed PPT rules with deterministic `polytime` automation. Programs
use ordinary `do` notation, captured inputs and conditionals. Named and local certificates are
reused, and tuple arguments are prepared with the shared routine-call
matcher. Every proof supplies the uniform strict fair-coin machine contract of `IsPPTOn`.
`IsPPT` goals and local certificates expose the standard unary-parameter/word encoding
automatically.

Unknown algorithms need certificates. Fair bits, uniform words with efficiently computed unary
lengths, memoized closed samplers and bounded loops with additive state growth polynomial in the
original input are certified here. General loop invariants
use `IsPPTOn.iterate_spec`; oracle PPT needs further rules.

## Main definitions

* `ppt`: prove a closed encoded PPT certificate using the `PPT` and `PolyTime` Aesop rule sets.

## References

Adapted from Cslib/Tactic/PPT.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the common machine realization and tidy calculus.
-/

public section

namespace Cslib.Tactic.PPT

open Lean Meta Elab Tactic Probability

attribute [aesop norm unfold (rule_sets := [PPT])] IsPPT

/-- Prepare local probabilistic routine calls through the same matcher as deterministic calls. -/
@[aesop unsafe 99% tactic (rule_sets := [PPT])]
private meta def pptKnownCall : Aesop.RuleTac :=
  Cslib.Tactic.applyKnownCall ``IsPPTOn 4 ``IsPPTOn.preprocess `prepare `hprogram

/-- Expose named probabilistic certificates as search alternatives. -/
@[aesop unsafe 99% tactic (rule_sets := [PPT])]
private meta def pptCertificate : Aesop.RuleTac :=
  Cslib.Tactic.applyCertificates ``IsPPTOn

/-- Let compositional rules finish a goal before exposing individual monadic binds. -/
@[aesop safe -20 tactic (rule_sets := [PPT])]
private meta def pptFunProp : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``IsPPTOn do
      throwError "expected an encoded-input PPT goal"
    if target.getAppArgs[2]!.hasExprMVar then
      throwError "input encoding is not yet determined"
    Cslib.Tactic.PolyTime.Internal.funPropWithPlainBoundary 128

attribute [program_certificate]
  Turing.MultiTapeTM.ComputableInPolyTime.isPPTOn
  isPPTOn_sampleList
  Turing.MultiTapeTM.ComputableInPolyTime.sampleList
  isPPTOn_uniform_bool
  IsPPTOn.memoize

/-- Expose probabilistic sequencing to Aesop's joint search, retaining alternatives for the
intermediate encoding until both the sampler and continuation have been proved. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptCaptured : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← Core.betaReduce (← instantiateMVars (← getMainTarget))).consumeMData
    unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
    let rule ← lambdaTelescope target.getAppArgs.back! fun _ body => do
      if body.isAppOf ``Bind.bind then return ``IsPPTOn.bind_with
      if body.isAppOf ``Functor.map then return ``IsPPTOn.map_with
      throwError "expected probabilistic sequencing"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Only a syntactic conditional can use branch selection. Trying these theorems on arbitrary
named programs can unfold their implementations during unification before certificate children
are explored. Named calls retain their existing alternative search. -/
private meta def pptConditional (rule : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
    let conditional? ← Cslib.Tactic.withConditionalBody? target.getAppArgs.back!
      fun _ => pure true
    unless conditional?.isSome do throwError "expected a conditional program"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Retain Boolean branch selection at its original priority. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptCond : TacticM Unit :=
  pptConditional ``IsPPTOn.cond

/-- Retain proposition branch selection as an independent search alternative. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIte : TacticM Unit :=
  pptConditional ``IsPPTOn.ite

/-- Loop rules inspect only an actual iteration, including reducible wrappers. Arbitrary named
programs must not unfold during loop-rule unification before their certificate children run. -/
private meta def pptIterate (rule : Name) : TacticM Unit :=
  withMainContext <| Term.withoutErrToSorry <| withoutRecover do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``IsPPTOn do throwError "expected an encoded-input PPT goal"
    let program ← Core.betaReduce (← etaExpand target.getAppArgs.back!)
    let iteration ← lambdaTelescope program fun _ body => do
      if body.isAppOf ``OracleComp.iterate then return true
      return (← whnfR body).isAppOf ``OracleComp.iterate
    unless iteration do throwError "expected a probabilistic iteration"
    liftMetaTactic fun goal => goal.applyConst rule

/-- Retain the nonincreasing-state iteration alternative at its original priority. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateLength : TacticM Unit :=
  pptIterate ``IsPPTOn.iterate_of_length_le

/-- Retain the fixed additive growth alternative without changing its bound obligation. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateGrowth : TacticM Unit :=
  pptIterate ``IsPPTOn.iterate_of_bounded_growth

/-- Retain captured iteration with its polynomial input-dependent growth obligation. -/
@[aesop unsafe 80% tactic (rule_sets := [PPT])]
private meta def pptIterateCaptured : TacticM Unit :=
  pptIterate ``IsPPTOn.iterateWith_of_bounded_growth

/-- Certify a probabilistic program using proved sampling, composition and deterministic rules. -/
elab "ppt" : tactic => Cslib.Tactic.PolyTime.Internal.withPlainRuleCache do
  evalTactic (← `(tactic| solve |
    aesop (config := { terminal := true, assumptionTransparency := .reducible })
      (rule_sets := [PPT, PolyTime])))

end Cslib.Tactic.PPT
