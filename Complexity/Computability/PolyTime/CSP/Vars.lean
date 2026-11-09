/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.ToCNF
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time variable occurrences of CSP instances

The variable occurrences `F.vars` of a CSP instance, their number, and the auxiliary formula
`F.varCNF` are computable in polynomial time from the framed encoding `encCSP`.

## Main results

* `Cslib.Complexity.CSP.computableInPolyTime_vars`: the occurrence list `F.vars`.
* `Cslib.Complexity.CSP.computableInPolyTime_length_vars`: its length, in unary.
* `Cslib.Complexity.CSP.computableInPolyTime_varCNF`: the auxiliary formula `F.varCNF`.
* `Cslib.Complexity.CSP.computableInPolyTime_unary_to_binary`: re-encoding natural-number
  variables from unary to binary.
-/

@[expose] public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel V : Type}

/-- Extracting the variable-occurrence list `CSP.vars` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_vars (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.vars (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList encV) := by
  unfold CSP.vars
  fun_prop

/-- The number `F.vars.length` of variable occurrences, in unary, is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_length_vars (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (fun F : CSP Rel V => F.vars.length) (encCSP encRel encV) encUnary :=
  (ComputableInPolyTime.length_list encV).comp (computableInPolyTime_vars encRel encV)

/-- Constructing the auxiliary positive-clause CNF `CSP.varCNF` is computable in polynomial
time. -/
@[fun_prop]
theorem computableInPolyTime_varCNF (encRel : Rel ↪ List Bool) (encV : V ↪ List Bool) :
    ComputableInPolyTime (CSP.varCNF (Rel := Rel) (V := V))
      (encCSP encRel encV) (encList (encList (encPair encV encBool))) := by
  unfold CSP.varCNF
  fun_prop

/-- Re-encoding the natural-number variables of a CSP instance from unary to binary is computable
in polynomial time. -/
theorem computableInPolyTime_unary_to_binary (encRel : Rel ↪ List Bool) :
    ComputableInPolyTime (fun F : CSP Rel ℕ => F) (encCSP encRel encUnary)
      (encCSP encRel encNat) := by
  have h : ComputableInPolyTime (CSP.relabel (Rel := Rel) (V := ℕ) (W := ℕ) fun n => n)
      (encCSP encRel encUnary) (encCSP encRel encNat) := by
    unfold CSP.relabel Constraint.relabel
    fun_prop
  have heq : (CSP.relabel (Rel := Rel) (V := ℕ) (W := ℕ) fun n => n) = fun F => F := by
    funext F
    induction F with
    | nil => rfl
    | cons c F ih =>
      simp only [CSP.relabel, List.map_cons, Constraint.relabel, List.map_id']
      exact congrArg (c :: ·) ih
  rwa [heq] at h

end Cslib.Complexity.CSP
