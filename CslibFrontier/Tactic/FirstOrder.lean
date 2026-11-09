/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Projection
public import CslibFrontier.Logics.FirstOrder.Reduction.QuantifierFree
public import CslibFrontier.Tactic.FirstOrder.Init

/-!
# Automation for first-order interpretations and reductions

A first-order reduction through an explicit interpretation is proved by syntactic side
conditions and a semantic argument. The tactics of this file prove the former and unfold the
latter, so that a new reduction costs only its semantic argument.

* `fo_qf` proves quantifier-freeness of formulas (`BoundedFormula.IsQF`,
  `BoundedFormula.IsAtomic`), interpretations (`Interpretation.IsQF`), projection formulas
  (`ProjectionFormula.IsQF`) and projections (`Projection.IsQF`) built from Boolean connectives,
  equality, relation symbols, the combinators of `CslibFrontier.Logics.FirstOrder.Basic`,
  relabeling,
  finite conjunctions and disjunctions, pullback and composition. It searches the Aesop rule set
  `FirstOrder`. A concrete interpretation or projection, defined as a structure instance, is
  split into its domain and relation definitions, with a case for each relation symbol of a
  concrete vocabulary.
* `fo_iso_closed` runs the same search on closure of a class under isomorphism (`IsoClosed`),
  whose lemmas are registered in the rule set `FirstOrder` too.
* `fo_simp` simplifies with the simp set `fo_realize`, unfolding the realization of formulas,
  projection formulas and the relations of interpreted structures to propositions about the
  input structure. The relation and domain formulas of concrete interpretations and projections
  are unfolded by the simprocs `reduceInterpretationDomain`, `reduceInterpretationRel`,
  `reduceProjectionNumeric` and `reduceProjectionRel`. Composites `J.comp I` are not unfolded
  into raw pullback formulas: the domains, relations and input relations of composite
  interpretations and projections are rewritten through the iterated interpretation or projection
  (`Interpretation.realize_comp_domain`, `Interpretation.relMap_comp_model`,
  `Projection.comp_numeric_domain`, `Projection.comp_numeric_rel`,
  `Projection.relMap_comp_inputStructure`), simplifying directly to the full tuple domain
  `ι → M` when `I.domain` holds of every tuple
  (`Interpretation.realize_comp_domain_tupleStructure`,
  `Interpretation.realize_comp_rel_tupleStructure`,
  `Projection.realize_comp_rel_tupleStructure`).
* `fo_reduction I` reduces a goal `FO.QFReduces K K'` or `FO.Reduces K K'` to the semantic
  statement about the interpretation `I`, proving the side conditions it can. When `K'` is
  closed under isomorphism and the domain formula of `I` always holds, the semantic statement is
  about the input universe itself (`FO.QFReduces.of_unitStructure`,
  `FO.Reduces.of_unitStructure`) for one-dimensional `I`, or about the full tuple domain `ι → M`
  (`FO.QFReduces.of_tupleStructure`, `FO.Reduces.of_tupleStructure`) for higher-dimensional or
  composite `I`.

Relation symbols inside the formulas of an interpretation should be written as terms of their
declared type `L.Relations n`, such as Mathlib's `Language.adj`, rather than as bare constructors
such as `.adj`, whose type is the inductive type of symbols: `simp` cannot instantiate its lemmas
at terms that are well typed only after unfolding the language. Patterns `| .adj => …` in the
definition of the relations are unaffected.

## Main definitions

* `fo_qf`, `fo_iso_closed`, `fo_simp`, `fo_reduction`: the tactics above.
* `reduceInterpretationDomain`, `reduceInterpretationRel`, `reduceProjectionNumeric`,
  `reduceProjectionRel`: simprocs unfolding concrete interpretations and projections.

## Implementation notes

The simprocs unfold a projection of `Interpretation` or `Projection` only when its argument
unfolds to a structure instance, and a relation definition only when the match on the relation
symbol reduces, so they never expose auxiliary matchers; for quantifier-freeness, composites are
unfolded too. Aesop's simplifier is disabled in `fo_qf`: the default simp set would rewrite the
formulas whose shape the rules inspect. Relation symbols are split by a safe rule, as Aesop's
normalisation rules may not produce several goals.

## References

The organization follows the `polytime` automation of `CslibFrontier.Tactic.PolyTime`: an Aesop
rule set declared in `CslibFrontier.Tactic.FirstOrder.Init` and populated where lemmas are proved.
-/

public section

open Lean Meta Elab Tactic Parser.Tactic

namespace Cslib.Tactic.FirstOrder

mutual

/-- Unfold `e` one definition at a time until it is an application of the constructor `ctor`.
With `stopAtComp`, composites of interpretations and projections are not unfolded. -/
private meta partial def unfoldToInstance? (stopAtComp : Bool) (ctor : Name) (e : Expr) :
    MetaM (Option Expr) := do
  let e ← whnfCore e
  if e.isAppOf ctor then return some e
  if stopAtComp && (e.isAppOf ``Cslib.Logic.FO.Interpretation.comp ||
      e.isAppOf ``Cslib.Logic.FO.Projection.comp) then
    return none
  if let some e ← reduceProjOfInstance? stopAtComp e then
    return ← unfoldToInstance? stopAtComp ctor e
  let some e ← unfoldDefinition? e | return none
  unfoldToInstance? stopAtComp ctor e

/-- The field of a structure instance selected by a projection, when the projection is applied to
a term unfolding to a structure instance and the field applied to the remaining arguments reduces
without a stuck match. Class projections are left alone. -/
private meta partial def reduceProjOfInstance? (stopAtComp : Bool) (e : Expr) :
    MetaM (Option Expr) := do
  let .const fn _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? fn | return none
  if info.fromClass then return none
  let args := e.getAppArgs
  let some struct := args[info.numParams]? | return none
  let some struct ← withDefault <| unfoldToInstance? stopAtComp info.ctorName struct
    | return none
  let some field := struct.getAppArgs[info.numParams + info.i]? | return none
  let result ← whnfCore (mkAppN field args[info.numParams + 1:]).headBeta
  if ← isMatcherApp result then return none
  return some result

end

/-- The projections of interpretations and projections that the automation unfolds. -/
private meta def isUnfoldedProjection (e : Expr) : Bool :=
  e.isAppOf ``Cslib.Logic.FO.Interpretation.domain ||
    e.isAppOf ``Cslib.Logic.FO.Interpretation.rel ||
    e.isAppOf ``Cslib.Logic.FO.Projection.numeric || e.isAppOf ``Cslib.Logic.FO.Projection.rel

/-- Unfold a projection of a concrete structure instance, other than a composite, with an explicit
equality proof so that `simp` can use the result when discharging side conditions at reducible
transparency. -/
private meta def reduceConcreteProjection (e : Expr) : SimpM Simp.Step := do
  let some e' ← reduceProjOfInstance? true e | return .continue
  return .visit { expr := e', proof? := some (← mkExpectedTypeHint (← mkEqRefl e') (← mkEq e e')) }

/-- Unfold the domain formula of a concrete interpretation, other than a composite. -/
simproc [fo_realize] reduceInterpretationDomain (Cslib.Logic.FO.Interpretation.domain _) :=
  reduceConcreteProjection

/-- Unfold a relation definition of a concrete interpretation at a relation symbol, other than a
composite. -/
simproc [fo_realize] reduceInterpretationRel (Cslib.Logic.FO.Interpretation.rel _ _) :=
  reduceConcreteProjection

/-- Unfold the numeric interpretation of a concrete projection, other than a composite. -/
simproc [fo_realize] reduceProjectionNumeric (Cslib.Logic.FO.Projection.numeric _) :=
  reduceConcreteProjection

/-- Unfold a relation definition of a concrete projection at a relation symbol, other than a
composite. -/
simproc [fo_realize] reduceProjectionRel (Cslib.Logic.FO.Projection.rel _ _) :=
  reduceConcreteProjection

/-! ### Quantifier-freeness -/

open FirstOrder.Language in
attribute [aesop safe apply (rule_sets := [FirstOrder])]
  BoundedFormula.IsQF.falsum BoundedFormula.IsQF.imp BoundedFormula.isQF_bot
  BoundedFormula.IsQF.top BoundedFormula.IsQF.not BoundedFormula.IsQF.inf BoundedFormula.IsQF.sup
  BoundedFormula.IsQF.relabel BoundedFormula.IsAtomic.equal BoundedFormula.IsAtomic.rel
  BoundedFormula.IsAtomic.relabel

-- An atomic formula is quantifier-free, but a quantifier-free formula need not be atomic.
attribute [aesop unsafe 50% apply (rule_sets := [FirstOrder])]
  FirstOrder.Language.BoundedFormula.IsAtomic.isQF

/-- Unfold the domain and relation definitions of concrete interpretations and projections,
composites included: their quantifier-freeness follows from that of the unfolded formulas. -/
@[aesop norm tactic (rule_sets := [FirstOrder])]
private meta def unfoldDefinitions : TacticM Unit := liftMetaTactic1 fun goal => do
  let target ← instantiateMVars (← goal.getType)
  let target' ← Meta.transform target (post := fun e => do
    unless isUnfoldedProjection e do return .continue
    let some e ← reduceProjOfInstance? false e | return .continue
    return .visit e)
  if target' == target then throwError "no interpretation or projection to unfold"
  goal.replaceTargetDefEq target'

/-- Split a relation symbol of a concrete vocabulary into its constructors. -/
@[aesop safe tactic (rule_sets := [FirstOrder])]
private meta def casesRelationSymbol : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    unless (← instantiateMVars decl.type).isAppOf ``FirstOrder.Language.Relations do continue
    try
      let subgoals ← goal.cases decl.fvarId
      replaceMainGoal (subgoals.map (·.mvarId)).toList
      return
    catch _ => pure ()
  throwError "no relation symbol of a concrete vocabulary"

/-- `fo_qf` proves that a formula, interpretation, projection formula or projection built from the
usual constructors is quantifier-free, searching the Aesop rule set `FirstOrder`. It fails if it
cannot close the goal. -/
macro (name := foQF) "fo_qf" : tactic => `(tactic|
  aesop (config := { terminal := true, enableSimp := false })
    (rule_sets := [-default, FirstOrder]))

/-- `fo_iso_closed` proves that a class of structures is closed under isomorphism from a lemma
registered in the Aesop rule set `FirstOrder` or a hypothesis. It runs the same search as `fo_qf`
and fails if it cannot close the goal. -/
macro (name := foIsoClosed) "fo_iso_closed" : tactic => `(tactic|
  aesop (config := { terminal := true, enableSimp := false })
    (rule_sets := [-default, FirstOrder]))

/-! ### Realization -/

open FirstOrder.Language in
attribute [fo_realize]
  BoundedFormula.realize_bot BoundedFormula.realize_not BoundedFormula.realize_bdEqual
  BoundedFormula.realize_top BoundedFormula.realize_inf BoundedFormula.realize_imp
  BoundedFormula.realize_rel BoundedFormula.realize_rel₁ BoundedFormula.realize_rel₂
  BoundedFormula.realize_sup BoundedFormula.realize_all BoundedFormula.realize_ex
  BoundedFormula.realize_iff BoundedFormula.realize_relabel BoundedFormula.realize_iSup
  BoundedFormula.realize_iInf BoundedFormula.realize_iAlls BoundedFormula.realize_iExs
  Formula.realize_not Formula.realize_bot Formula.realize_top Formula.realize_inf
  Formula.realize_imp Formula.realize_rel Formula.realize_rel₁ Formula.realize_rel₂
  Formula.realize_sup Formula.realize_iff Formula.realize_relabel Formula.realize_equal
  Formula.realize_iSup Formula.realize_iInf Formula.realize_iAlls Formula.realize_iExs
  Sentence.realize_not Sentence.realize_top Sentence.realize_inf Sentence.realize_sup
  Sentence.realize_imp Sentence.realize_iff
  LHom.realize_onBoundedFormula LHom.realize_onFormula LHom.realize_onSentence
  Term.realize_var Term.realize_relabel
  Sum.elim_inl Sum.elim_inr Function.comp_apply Unique.forall_iff PUnit.default_eq_unit
  Matrix.cons_val_zero Matrix.cons_val_one Matrix.head_cons Matrix.cons_val_fin_one
  Set.mem_ofPred_eq
  true_and and_true false_and and_false true_or or_true false_or or_false not_true_eq_false
  not_false_eq_true not_not ne_eq iff_self eq_self_iff_true implies_true true_implies
  false_implies imp_false forall_const Bool.false_eq_true exists_prop
  ite_true ite_false

/-- `fo_simp` simplifies with the simp set `fo_realize`, unfolding the realization of first-order
formulas, projection formulas and the relations of interpreted structures, and the definitions of
concrete interpretations and projections. `fo_simp [h₁, h₂] at l` adds simp lemmas and a location,
as for `simp only`. -/
syntax (name := foSimp) "fo_simp" (simpArgs)? (location)? : tactic

macro_rules
  | `(tactic| fo_simp $[[$args,*]]? $[at $location]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp only [fo_realize, $args,*] $[at $location]?)

/-! ### Reductions -/

/-- `fo_reduction I` proves a goal `FO.QFReduces K K'` or `FO.Reduces K K'` through the
interpretation `I`, leaving the semantic statement, simplified by `fo_simp`:

* `∀ M [Finite M], M ∈ K ↔ ⟨M, I.unitStructure M⟩ ∈ K'`, about the input universe itself, when
  `I` is one-dimensional, `fo_simp` proves that its domain formula holds of every element of every
  finite structure, and `fo_iso_closed` proves that `K'` is closed under isomorphism;
* `∀ M [Finite M], M ∈ K ↔ ⟨ι → M, I.tupleStructure M⟩ ∈ K'`, about the full tuple domain, when
  `I` has coordinate type `ι`, `fo_simp` proves that its domain formula holds of every tuple of
  every finite structure, and `fo_iso_closed` proves that `K'` is closed under isomorphism;
* `∀ M [Finite M], M ∈ K ↔ Bundled.of (I.Model M) ∈ K'` otherwise.

For `FO.QFReduces`, quantifier-freeness of `I` is proved by `fo_qf`, or left as a goal after the
semantic one. `fo_reduction I [h₁, h₂]` passes simp lemmas, such as membership lemmas for `K` and
`K'`, to the simplification of the semantic goal; errors in them are reported, and a goal they do
not change is left as it is. The interpretation is a single term; write `fo_reduction (J.comp I)`
for a compound one. On a goal of another form, `fo_reduction` fails. -/
syntax (name := foReduction) "fo_reduction " term:max (simpArgs)? : tactic

macro_rules
  | `(tactic| fo_reduction $I $[[$args,*]]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| (
      first
        | (refine Cslib.Logic.FO.QFReduces.of_unitStructure $I ?sem ?qf ?iso ?dom
           case' iso => fo_iso_closed
           case' dom => (intro _ _ _ _; fo_simp; done))
        | (refine Cslib.Logic.FO.QFReduces.of_tupleStructure $I ?sem ?qf ?iso ?dom
           case' iso => fo_iso_closed
           case' dom => (intro _ _ _ _; fo_simp; done))
        | refine Cslib.Logic.FO.QFReduces.of_interpretation $I ?sem ?qf
        | (refine Cslib.Logic.FO.Reduces.of_unitStructure $I ?sem ?iso ?dom
           case' iso => fo_iso_closed
           case' dom => (intro _ _ _ _; fo_simp; done))
        | (refine Cslib.Logic.FO.Reduces.of_tupleStructure $I ?sem ?iso ?dom
           case' iso => fo_iso_closed
           case' dom => (intro _ _ _ _; fo_simp; done))
        | refine Cslib.Logic.FO.Reduces.of_interpretation $I ?sem
        | fail "fo_reduction: expected `FO.Reduces K K'` or `FO.QFReduces K K'` through this \
            interpretation"
      try case' qf => fo_qf
      case' sem => simp -failIfUnchanged only [fo_realize, $args,*]))

end Cslib.Tactic.FirstOrder
