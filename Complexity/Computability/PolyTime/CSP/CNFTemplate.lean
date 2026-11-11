/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.CNFTemplate
public import Complexity.Computability.PolyTime.CSP.ToCNF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time instantiation of fixed CNF templates

For a fixed finite relation alphabet, every fixed family of CNF templates can be instantiated in
native polynomial time. Local template positions use unary encoding for list lookup, whereas
the original variable labels retain their binary encoding. Templates and their sizes are fixed
independently of the input instance; no uniform complexity bound in a supplied language is
asserted.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_instantiateCNF`: native polynomial-time template
  instantiation for a finite relation alphabet.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

variable {Rel : Type}

private theorem computable_clause (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime
      (fun p : Constraint Rel ℕ × Clause ℕ =>
        p.2.relabel (fun i => p.1.2.getD i 0))
      (encPair (encConstraint encRel encNat) (encList (encPair encUnary encBool)))
      (encList (encPair encNat encBool)) := by
  unfold Clause.relabel
  refine mapWithInput (snd _ _) ?_
  change ComputableInPolyTime
    (fun p : (Constraint Rel ℕ × Clause ℕ) × Literal ℕ =>
      (p.1.1.2.getD p.2.1 0, p.2.2))
    (encPair (encPair (encConstraint encRel encNat) (encList (encPair encUnary encBool)))
      (encPair encUnary encBool)) (encPair encNat encBool)
  fun_prop

private theorem computable_constraint [Finite Rel] (encRel : Rel ↪ List Bool)
    (template : Rel → CNF ℕ) :
    ComputableInPolyTime (Constraint.instantiateCNF 0 template)
      (encConstraint encRel encNat) (encList (encList (encPair encNat encBool))) := by
  have ht : ComputableInPolyTime template encRel
      (encList (encList (encPair encUnary encBool))) := of_finite _
  unfold Constraint.instantiateCNF CNF.relabel
  exact mapWithInput (ht.comp (fst _ _)) (computable_clause encRel)

/-- Fixed CNF templates over a finite relation alphabet can be instantiated in polynomial time,
with binary variable labels and unary local positions. -/
theorem computableInPolyTime_instantiateCNF [Finite Rel] (encRel : Rel ↪ List Bool)
    (template : Rel → CNF ℕ) :
    ComputableInPolyTime (Cslib.Logic.PL.CSP.instantiateCNF 0 template)
      (encCSP encRel encNat) (encList (encList (encPair encNat encBool))) := by
  exact flatMapWithInput id' ((computable_constraint encRel template).comp (snd _ _))

end Cslib.Complexity.CSP
