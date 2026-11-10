/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Tactic.FailureNote
public meta import Lean.Elab.Tactic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-!
# Composing explicit workspace certificates

`space` proves a `ComputableInSpace` goal by the existing budget-preserving `fun_prop` rules.
`space [f, g]` unfolds the indicated program definitions. Local routine certificates are reused;
unproved size inequalities and iteration invariants are not guessed. An input-length side
condition must be reflexive or supplied in the context. When the search fails, the `fun_prop`
error ends with a note naming these inputs.

This tactic does not assert logarithmic space in the original input: the goal specifies the
encoding and budget. In particular, a Savitch callback is linear-space in the stored state,
while a separate invariant bounds that state's length by a quadratic logarithm.

During the search, `space` does not unfold a primitive encoding, a definition whose body is an
embedding `⟨fun a => …, _⟩` into `List Bool` such as `encPair`, `encList` or `encFinEnum`.
Definitions that merely name an encoding, such as `encTuple := encPair …` or
`encLab := encFinEnum Label`, still unfold. Two different primitive encodings are therefore never
unified by unfolding both: without this, matching `encPair ?e₁ ?e₂` against `encFinEnum (A × B)`
evaluates the enumeration of `A × B` until `maximum recursion depth`, and nested pair encodings
fail exponentially slowly. Nor does it unfold `decide`, which would evaluate the decision
procedure of a condition that a rule does not match. Side conditions are proved with the usual
unfolding.

Conditions built from `∧`, `∨` and `≤`, and equalities through the canonical finite encoding
(`budget_decideAnd`, `budget_decideOr`, `budget_natLe`, `budget_decideEq_encFinite`), are tried
only when a first search without them fails: registered globally, each would be tried, and fail,
on every decidable condition. A certificate that needs them pays for the failed first search,
which on a long condition chain can cost several times a hand-written proof.

## Main definitions

* `space`: compose certificates within the goal's explicit workspace budget.
-/

public meta section

open Lean Meta Elab Tactic Turing.MultiTapeTM

/-- Whether `e`, under binders, `let`s and metadata, is an embedding `⟨_, _⟩ : α ↪ List Bool`. -/
private partial def isEncodingBody (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ | .letE _ _ _ b _ => isEncodingBody b
  | e => e.isAppOfArity ``Function.Embedding.mk 4 &&
      (e.getArg! 1).isAppOfArity ``List 1 && (e.getArg! 1).appArg!.isConstOf ``Bool

/-- The unfolding predicate of `space`: the usual one, except that primitive encodings stay
folded. -/
private def spaceCanUnfold (cfg : Config) (info : ConstantInfo) : CoreM Bool := do
  if info.name == ``Decidable.decide then return false
  if let .defnInfo d := info then
    if isEncodingBody d.value then return false
  match cfg.canUnfoldPredicateConfig with
  | .default => canUnfoldDefault cfg info
  | .atMatcher => canUnfoldAtMatcher cfg info

/-- The side-condition discharger of `space`: a hypothesis or a reflexive bound, proved with the
usual unfolding. Internal to `space`. -/
syntax (name := spaceDischarge) "space_discharge" : tactic

elab_rules : tactic
  | `(tactic| space_discharge) =>
    withTheReader Meta.Context (fun ctx => { ctx with customCanUnfoldPredicate? := none }) do
      evalTactic (← `(tactic| first | assumption | exact BigOLe.refl _))

/-- Rules that `space` adds as local hypotheses, which `fun_prop` tries after the registered rules,
when a first search without them fails. Registered, each would be tried, and fail, on every
decidable condition. -/
private def spaceFallbacks : Array Name := #[
  ``ComputableInSpace.budget_decideEq_encFinite, ``ComputableInSpace.budget_decideAnd,
  ``ComputableInSpace.budget_decideOr, ``ComputableInSpace.budget_natLe]

/-- Compose explicit space certificates, optionally unfolding the named program definitions. -/
syntax (name := spaceTac) "space" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| space $[[$defs,*]]?) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOf ``Turing.MultiTapeTM.ComputableInSpace do
      throwError "space expects a ComputableInSpace goal with an explicit budget"
    let defs := (defs.map (·.getElems)).getD #[]
    Cslib.Tactic.withFailureNote m!"space composes `@[fun_prop]` rules for `ComputableInSpace` \
        within the goal's budget. Supply a certificate for each local routine, unfold a program \
        definition with `space [f]`, and supply a nontrivial input-length allowance \
        `(fun a => (encIn a).length) ≼ S` as a hypothesis." do
      withCanUnfoldPred spaceCanUnfold do
        let funProp ← `(tactic| fun_prop (config := { maxSteps := 256 })
          (disch := space_discharge) [$defs,*])
        let s ← saveState
        try
          evalTactic funProp
        catch _ =>
          s.restore
          for n in spaceFallbacks do
            evalTactic (← `(tactic| have := @$(mkCIdent n)))
          evalTactic funProp

end
