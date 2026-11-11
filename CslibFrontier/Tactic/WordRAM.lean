/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Controller
public import CslibFrontier.Computability.WordRAM.Function
public import CslibFrontier.Tactic.PolyTime
public import CslibFrontier.Tactic.Stateful

/-!
# Reusing RAM controller certificates

Named `Refines`, `ComputableInPolyTime` and `UniformComputableInPolyTime` proofs can be
registered with `program_certificate`.
The `stateful` and `polytime` tactics respectively retrieve them through the existing certificate
index. Predicate and program heads are separate keys: a RAM certificate cannot discharge a
Turing-machine polynomial-time goal. Local certificates remain ordinary hypotheses.

Use `Refines.bind`, `branch`, `prepend`, and `call` explicitly to choose intermediate assertions,
representations and charged preparation code; automation then reuses the named subroutine proofs.
No rule evaluates arbitrary host-language continuations for free or guesses an implementation.

## Main definitions

* `ramControllerCertificate`: named fixed-code refinement proofs for `stateful`.
* `ramFunctionCertificate`: named polynomial RAM-time proofs for `polytime`.
* `ramUniformFunctionCertificate`: named uniform polynomial RAM-time proofs for `polytime`.
-/

public meta section

namespace Cslib.Tactic

/-- Close a named controller certificate from local hypotheses before case splitting changes
its budget. Only complete proofs commit here; certificates with remaining obligations are
alternatives in `ramControllerAlternative`. -/
@[aesop safe -50 tactic (rule_sets := [Stateful])]
def ramControllerCertificate : Aesop.RuleTac := fun input => do
  let result ← applyCertificates ``WordRAM.Refines input
  let saved ← Lean.Meta.saveState
  for app in result.applications do
    try
      app.postState.restore
      for goal in app.goals do
        goal.mvarId.assumption
      let completed ← Lean.Meta.saveState
      saved.restore
      return ⟨#[{ app with goals := #[], postState := completed }]⟩
    catch _ => saved.restore
  throwError "no controller certificate closes from local hypotheses"

/-- Keep incomplete named controller proofs as alternatives with explicit proof obligations. -/
@[aesop unsafe 99% tactic (rule_sets := [Stateful])]
def ramControllerAlternative : Aesop.RuleTac :=
  applyCertificates ``WordRAM.Refines

/-- Reuse a named function certificate with the RAM predicate, without changing machine models. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
def ramFunctionCertificate : Aesop.RuleTac :=
  applyCertificates ``WordRAM.ComputableInPolyTime

/-- Reuse a named uniform function certificate under its own predicate key. -/
@[aesop unsafe 99% tactic (rule_sets := [PolyTime])]
def ramUniformFunctionCertificate : Aesop.RuleTac :=
  applyCertificates ``WordRAM.UniformComputableInPolyTime

end Cslib.Tactic
