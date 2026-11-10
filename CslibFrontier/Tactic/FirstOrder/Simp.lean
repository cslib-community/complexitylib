/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Tactic.FirstOrder.Init
public import Mathlib.ModelTheory.Semantics

/-!
# The `fo_simp` tactic

`fo_simp` simplifies with the simp set `fo_realize`, which unfolds the realization of first-order
formulas to propositions about the structure they are evaluated in. This file tags Mathlib's
realization lemmas, and the propositional normalizations they need, with `fo_realize`, and
defines `fo_simp`. Lemmas about the formulas, projection formulas and interpreted structures of
this library are tagged where they are proved.

It depends only on Mathlib's semantics of first-order logic, so that the modules of
`CslibFrontier.Logics` below `CslibFrontier.Tactic.FirstOrder` can import it to prove realization
lemmas. `CslibFrontier.Tactic.FirstOrder` re-exports it, together with the simprocs that unfold
concrete interpretations and projections.

## Main definitions

* `fo_simp`: `simp only` with the simp set `fo_realize`.
-/

public section

open Lean Parser.Tactic

namespace Cslib.Tactic.FirstOrder

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
formulas, projection formulas and the relations of interpreted structures, and, where
`CslibFrontier.Tactic.FirstOrder` is imported, the definitions of concrete interpretations and
projections. `fo_simp (config := c) (disch := tac) [h₁, h₂] at l` passes a configuration,
discharger, extra simp lemmas and a location through, as for `simp only`. -/
syntax (name := foSimp) "fo_simp" optConfig (discharger)? (simpArgs)? (location)? : tactic

macro_rules
  | `(tactic| fo_simp $cfg:optConfig $[$disch]? $[[$args,*]]? $[at $location]?) =>
    let args := args.map (·.getElems) |>.getD #[]
    `(tactic| simp $cfg:optConfig $[$disch]? only [fo_realize, $args,*] $[at $location]?)

end Cslib.Tactic.FirstOrder
