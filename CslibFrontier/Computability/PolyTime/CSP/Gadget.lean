/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.PrimitivePositive.Replacement
public import CslibFrontier.Computability.PolyTime.CSP.Boolean
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.List.Enum
import Mathlib.Data.List.GetD

/-!
# Native polynomial-time fixed-gadget replacement

This module certifies native polynomial time for instantiating a template, replacing all
source constraints and applying the exact-arity guard. The replacement definitions and
semantic correctness theorems live in `Logics.Propositional.CSP.PrimitivePositive.Replacement`,
which is publicly imported here.

The native multitape certificates use binary input/output variable indices, unary local
template and constraint indices, and a finite lookup for the fixed source alphabet.
Original variable `v` becomes `2*v`; auxiliary port `j` at constraint index `i` becomes
`2*(B*i+j)+1`. Repeated variables are allowed, and the guarded compiler uses an explicit
malformed-input reject instance. The underlying replacement is the equality-free case of
[Chen2006CSP], Proposition 3.9, arXiv v1, p. 8, with encoding and rejection made explicit.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_instantiate`: native instantiation of one template.
* `Cslib.Complexity.CSP.computableInPolyTime_replaceGadgets`: native fixed-template replacement.
* `Cslib.Complexity.CSP.computableInPolyTime_replaceGadgetsGuarded`: native polynomial time
  for fixed finite source alphabets, with binary variable names.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime
open Cslib.Logic.PL.CSP

variable {Src Rel : Type}

/-- Instantiate a local template in native polynomial time. Local indices and the
constraint number are unary; scope variable names and output names are binary. -/
theorem computableInPolyTime_instantiate (encRel : Rel ↪ List Bool) (B : ℕ) :
    ComputableInPolyTime
      (fun p : (ℕ × List ℕ) × CSP Rel (Bool × ℕ) =>
        let ((index, scope), body) := p
        instantiate B index scope body)
      (encPair (encPair encUnary (encList encNat))
        (encCSP encRel (encPair encBool encUnary))) (encCSP encRel encNat) := by
  unfold instantiate relabel Constraint.relabel
  fun_prop

/-- Finite fixed gadget lookup and replacement are native polynomial time, with no
computability requirement on the process used to obtain the fixed gadgets. -/
theorem computableInPolyTime_replaceGadgets [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool) (B : ℕ)
    (templates : Src → CSP Rel (Bool × ℕ)) :
    ComputableInPolyTime (replaceGadgets B templates)
      (encCSP encSrc encNat) (encCSP encRel encNat) := by
  have ht : ComputableInPolyTime templates encSrc
      (encCSP encRel (encPair encBool encUnary)) := of_finite _
  have hi := computableInPolyTime_instantiate encRel B
  have hz : ComputableInPolyTime (fun F : CSP Src ℕ => F.zipIdx)
      (encCSP encSrc encNat) (encList (encPair (encConstraint encSrc encNat) encUnary)) :=
    .of_tidy (ComputableTidilyInPolyTime.zipIdx _)
  unfold replaceGadgets
  apply flatMapWithInput hz
  exact hi.comp (g := fun p : CSP Src ℕ × (Constraint Src ℕ × ℕ) =>
    ((p.2.2, p.2.1.2), templates p.2.1.1)) (by fun_prop)

/-- A total native polynomial-time compiler with an explicit malformed-input reject target. -/
theorem computableInPolyTime_replaceGadgetsGuarded [Finite Src]
    (encSrc : Src ↪ List Bool) (encRel : Rel ↪ List Bool)
    (srcArity : Src → ℕ) (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (reject : CSP Rel ℕ) :
    ComputableInPolyTime (replaceGadgetsGuarded srcArity B templates reject)
      (encCSP encSrc encNat) (encCSP encRel encNat) :=
  (computableInPolyTime_validArity encSrc srcArity).ite
    (computableInPolyTime_replaceGadgets encSrc encRel B templates) (const reject)

end Cslib.Complexity.CSP
