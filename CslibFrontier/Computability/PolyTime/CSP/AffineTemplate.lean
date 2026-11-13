/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.AffineTemplate
public import CslibFrontier.Computability.PolyTime.CSP.ToCNF
public import CslibFrontier.Computability.PolyTime.CSP.AffineEquation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time instantiation of fixed affine templates

The finite relation alphabet and its local affine systems are fixed independently of the input.
Local positions use unary encoding for list lookup. Original variable labels use binary encoding
throughout; no array indexed by their numerical values is constructed. Each fixed template lookup,
substitution and concatenation has a native multi-tape polynomial-time certificate.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_instantiateAffine`: polynomial template compilation.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

variable {Rel : Type}

private theorem computable_equation (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime
      (fun p : Constraint Rel ℕ × AffineEquation ℕ =>
        p.2.relabel (fun i => p.1.scope.getD i 0))
      (encPair (encConstraint encRel encNat) (encAffineEquation encUnary))
      (encAffineEquation encNat) := by
  have hvars : ComputableInPolyTime
      (fun p : Constraint Rel ℕ × AffineEquation ℕ =>
        p.2.vars.map (fun i => p.1.scope.getD i 0))
      (encPair (encConstraint encRel encNat) (encAffineEquation encUnary))
      (encList encNat) := by
    refine mapWithInput (encA := encUnary) ?_ ?_
    · fun_prop
    · fun_prop
  unfold AffineEquation.relabel
  exact encAffineEquation_mk_polyTime encNat hvars (by fun_prop)

private theorem computable_constraint [Finite Rel] (encRel : Rel ↪ List Bool)
    (template : Rel → AffineSystem ℕ) :
    ComputableInPolyTime (Constraint.instantiateAffine 0 template)
      (encConstraint encRel encNat) (encList (encAffineEquation encNat)) := by
  have ht : ComputableInPolyTime template encRel
      (encList (encAffineEquation encUnary)) := of_finite _
  unfold Constraint.instantiateAffine AffineSystem.relabel
  exact mapWithInput (ht.comp (encConstraint_rel_polyTime id')) (computable_equation encRel)

/-- Fixed affine systems can be instantiated in native polynomial time, with unary local
positions and binary original variable labels. The bound may depend on the fixed language. -/
theorem computableInPolyTime_instantiateAffine [Finite Rel] (encRel : Rel ↪ List Bool)
    (template : Rel → AffineSystem ℕ) :
    ComputableInPolyTime (Cslib.Logic.PL.CSP.instantiateAffine 0 template)
      (encCSP encRel encNat) (encList (encAffineEquation encNat)) := by
  exact flatMapWithInput id' ((computable_constraint encRel template).comp (snd _ _))

end Cslib.Complexity.CSP
