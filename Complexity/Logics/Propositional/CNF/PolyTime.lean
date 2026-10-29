/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ExactlyOne
public import Complexity.Logics.Propositional.CNF.ModelCount
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time CNF construction

The clause and formula constructors used by reductions to satisfiability are polynomial-time
for any fixed encoding of their variables. Literals use `encPair`, and clauses and formulas use
`encList`. Specializing the variable encoding to binary naturals gives the encoding of `SAT`.

These results certify the existing constructors, including the ordered-pair implementation of
exactly-one constraints. They apply to empty lists and lists with repeated variables. Relabelling
requires a polynomial-time renaming function, but does not require injectivity; injectivity is
needed separately when transferring satisfiability.

## Main definitions

* `Cslib.Logic.PL.encOccurrence`: encoding of a literal occurrence.

## Main results

* `Cslib.Logic.PL.Literal.computableInPolyTime_negate`: literal negation.
* `Cslib.Logic.PL.Clause.computableInPolyTime_impLits`,
  `Cslib.Logic.PL.Clause.computableInPolyTime_imp`: implication clauses.
* `Cslib.Logic.PL.Clause.computableInPolyTime_relabel`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_relabel`: renaming variables.
* `Cslib.Logic.PL.CNF.computableInPolyTime_atLeastOne`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_atMostOne`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_exactlyOne`: at-least-one, at-most-one and exactly-one
  constraints.
* `Cslib.Logic.PL.CNF.computableInPolyTime_vars`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_distinctVars`,
  `Cslib.Logic.PL.computableInPolyTime_occurrences`: listing variable occurrences, distinct
  variables and literal occurrences.
* `Cslib.Logic.PL.Clause.computableInPolyTime_length`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_length`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_vars_length`,
  `Cslib.Logic.PL.CNF.computableInPolyTime_numVars`: clause, formula, variable-occurrence and
  distinct-variable counts in unary.
* `Cslib.Logic.PL.CNF.computableInPolyTime_eval_bitsAssignment`: evaluating a formula under a
  numbered assignment.
* `Cslib.Logic.PL.CNF.isPolyTime_compact`: compact unary indices for arbitrary variable names.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Turing.MultiTapeTM ComputableInPolyTime

variable {V W : Type} {encV : V ↪ List Bool} {encW : W ↪ List Bool}

/-- Negating a literal changes only its polarity. -/
@[fun_prop]
theorem Literal.computableInPolyTime_negate (enc : V ↪ List Bool) :
    ComputableInPolyTime Std.Sat.Literal.negate
      (encPair enc encBool) (encPair enc encBool) := by
  unfold Std.Sat.Literal.negate
  fun_prop

/-- Construct an implication from literals, with a positive conclusion. -/
@[fun_prop]
theorem Clause.computableInPolyTime_impLits (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : List (Literal V) × V => Clause.impLits p.1 p.2)
      (encPair (encList (encPair enc encBool)) enc) (encList (encPair enc encBool)) := by
  unfold Clause.impLits
  fun_prop

/-- Construct an implication from positive hypotheses and a positive conclusion. -/
@[fun_prop]
theorem Clause.computableInPolyTime_imp (enc : V ↪ List Bool) :
    ComputableInPolyTime (fun p : List V × V => Clause.imp p.1 p.2)
      (encPair (encList enc) enc) (encList (encPair enc encBool)) := by
  unfold Clause.imp
  fun_prop

/-- Relabelling a clause is polynomial-time whenever the renaming function is. -/
@[fun_prop]
theorem Clause.computableInPolyTime_relabel {f : V → W}
    (hf : ComputableInPolyTime f encV encW) :
    ComputableInPolyTime (Clause.relabel f)
      (encList (encPair encV encBool)) (encList (encPair encW encBool)) :=
  map ((hf.comp (fst encV encBool)).prod (snd encV encBool))

/-- Relabelling a formula is polynomial-time whenever the renaming function is. -/
@[fun_prop]
theorem CNF.computableInPolyTime_relabel {f : V → W}
    (hf : ComputableInPolyTime f encV encW) :
    ComputableInPolyTime (CNF.relabel f)
      (encList (encList (encPair encV encBool)))
      (encList (encList (encPair encW encBool))) :=
  map (Clause.computableInPolyTime_relabel hf)

/-- List the variables of a formula in order, including repetitions. -/
@[fun_prop]
theorem CNF.computableInPolyTime_vars (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.vars (V := V))
      (encList (encList (encPair enc encBool))) (encList enc) := by
  unfold CNF.vars
  fun_prop

/-- The number of literals in a polynomial-time clause, in unary, is polynomial-time. -/
theorem Clause.computableInPolyTime_length {α : Type} {input : α ↪ List Bool}
    {c : α → Clause V}
    (hc : ComputableInPolyTime c input (encList (encPair encV encBool))) :
    ComputableInPolyTime (fun a => (c a).length) input encUnary :=
  (length_list (encPair encV encBool)).comp hc

/-- The number of clauses in a polynomial-time formula, in unary, is polynomial-time. -/
theorem CNF.computableInPolyTime_length {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF V}
    (hφ : ComputableInPolyTime φ input (encList (encList (encPair encV encBool)))) :
    ComputableInPolyTime (fun a => (φ a).length) input encUnary :=
  (length_list (encList (encPair encV encBool))).comp hφ

/-- The number of variable occurrences in a polynomial-time formula, in unary, is
polynomial-time. -/
theorem CNF.computableInPolyTime_vars_length {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF V}
    (hφ : ComputableInPolyTime φ input (encList (encList (encPair encV encBool)))) :
    ComputableInPolyTime (fun a => (φ a).vars.length) input encUnary :=
  (length_list encV).comp ((PL.CNF.computableInPolyTime_vars encV).comp hφ)

/-- Listing the distinct variables of a formula in order of first occurrence is
polynomial-time. -/
@[fun_prop]
theorem CNF.computableInPolyTime_distinctVars [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.distinctVars (V := V))
      (encList (encList (encPair enc encBool))) (encList enc) := by
  have hrep : ComputableInPolyTime (fun n => List.replicate n true) encUnary encBits :=
    of_eq fun _ => rfl
  unfold CNF.distinctVars Cslib.Complexity.selectDistinct
  fun_prop

/-- The number of distinct variables of a formula, in unary, is polynomial-time. -/
@[fun_prop]
theorem CNF.computableInPolyTime_numVars [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.numVars (V := V))
      (encList (encList (encPair enc encBool))) encUnary := by
  have e : (CNF.numVars (V := V)) = fun φ => φ.distinctVars.length :=
    funext fun φ => (CNF.length_distinctVars φ).symm
  rw [e]
  fun_prop

/-- Encoding of a literal occurrence: unary clause and position indices with an encoded literal. -/
def encOccurrence (enc : V ↪ List Bool) : Occurrence V ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair enc encBool))

/-- Enumerating the literal occurrences of a CNF formula is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_occurrences (enc : V ↪ List Bool) :
    ComputableInPolyTime (occurrences (V := V))
      (encList (encList (encPair enc encBool))) (encList (encOccurrence enc)) := by
  unfold occurrences encOccurrence
  fun_prop

/-- Evaluating a formula under the assignment numbered by `i` on a list of variables is
polynomial-time. -/
@[fun_prop]
theorem CNF.computableInPolyTime_eval_bitsAssignment [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime
      (fun p : (CNF V × List V) × ℕ => p.1.1.eval (bitsAssignment p.1.2 p.2))
      (encPair (encPair (encList (encList (encPair enc encBool))) (encList enc)) encNat)
      encBool := by
  have e : (fun p : (CNF V × List V) × ℕ => p.1.1.eval (bitsAssignment p.1.2 p.2)) =
      fun p => p.1.1.eval fun v => p.2.bits.getD (p.1.2.idxOf v) false := by
    funext p
    congr 1
    funext v
    exact bitsAssignment_eq_getD ..
  rw [e]
  fun_prop [CNF.eval, Clause.eval, Literal.eval]

/-- Construct the clause requiring at least one listed variable to hold. -/
@[fun_prop]
theorem CNF.computableInPolyTime_atLeastOne (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.atLeastOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  unfold CNF.atLeastOne
  fun_prop

/-- Construct the clauses forbidding two distinct listed variables from both holding.
The list may contain repeated variables. -/
@[fun_prop]
theorem CNF.computableInPolyTime_atMostOne [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.atMostOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  fun_prop [CNF.atMostOne]

/-- Construct exactly-one constraints in polynomial time, including for empty or repeated lists. -/
@[fun_prop]
theorem CNF.computableInPolyTime_exactlyOne [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.exactlyOne (V := V))
      (encList enc) (encList (encList (encPair enc encBool))) := by
  unfold CNF.exactlyOne
  fun_prop

/-- The entire input-dependent renaming is polynomial-time for any original variable encoding.
Its output indices use unary encoding and are bounded by the input's number of occurrences. -/
@[fun_prop]
theorem CNF.isPolyTime_compact [DecidableEq V] (enc : V ↪ List Bool) :
    ComputableInPolyTime (CNF.compact (V := V))
      (encList (encList (encPair enc encBool)))
      (encList (encList (encPair encUnary encBool))) := by
  unfold CNF.compact CNF.relabel Clause.relabel Prod.map
  fun_prop

end Cslib.Logic.PL
