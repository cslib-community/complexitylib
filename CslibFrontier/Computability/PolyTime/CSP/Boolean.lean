/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Boolean
public import CslibFrontier.Computability.PolyTime.CSP.ToCNF
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time fixed Boolean CSP syntax checks

The exact-arity guard is native polynomial-time for every fixed finite relation alphabet.
The fixed arity table uses unary values; instance variable labels retain their binary encoding.
This certificate is shared by satisfiability reductions and primitive-positive replacement.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_validArity`: native polynomial-time arity checking.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

/-- The exact-arity guard is polynomial-time for each fixed finite relation alphabet. -/
theorem computableInPolyTime_validArity {Rel : Type} [Finite Rel]
    (encRel : Rel ↪ List Bool) (arity : Rel → ℕ) :
    ComputableInPolyTime (Cslib.Logic.PL.CSP.validArity arity)
      (encCSP encRel encNat) encBool := by
  have ha : ComputableInPolyTime arity encRel encUnary := ComputableInPolyTime.of_finite _
  have ht : ComputableInPolyTime
      (fun c : Constraint Rel ℕ => decide (c.scope.length = arity c.rel))
      (encConstraint encRel encNat) encBool :=
    ComputableInPolyTime.decide_eq'
      ((ComputableInPolyTime.length_list encNat).comp
        (encConstraint_scope_polyTime ComputableInPolyTime.id'))
      (ha.comp (encConstraint_rel_polyTime ComputableInPolyTime.id'))
  change ComputableInPolyTime
    (fun F : Cslib.Logic.PL.CSP Rel ℕ => F.all (fun c => decide (c.scope.length = arity c.rel)))
    (encCSP encRel encNat) encBool
  exact ComputableInPolyTime.allWithInput ComputableInPolyTime.id'
    (ht.comp (ComputableInPolyTime.snd _ _))

end Cslib.Complexity.CSP
