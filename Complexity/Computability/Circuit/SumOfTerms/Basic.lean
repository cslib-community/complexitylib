/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Simulation
import Complexity.Computability.Circuit.Simulation

/-!
# Circuits adding dictionary terms

Nullary gates produce members of a prescribed dictionary, interpreted in any additive carrier.
The standard dictionary cost charges those terms and makes binary addition and wiring free.
Separate addition costs and arbitrary uniform weights are also provided.

## Main definitions

* `Cslib.Circuits.SumOfTerms.Op`, `Cslib.Circuits.SumOfTerms.Op.arity`,
  `Cslib.Circuits.SumOfTerms.signature`: operations, arities, and signature for additions and
  nullary dictionary terms.
* `Cslib.Circuits.SumOfTerms.interpretation`: interpret the dictionary in an additive carrier.
* `Cslib.Circuits.SumOfTerms.dictionaryCost`, `Cslib.Circuits.SumOfTerms.termCost`: term weights.
* `Cslib.Circuits.SumOfTerms.addCost`, `Cslib.Circuits.SumOfTerms.weightedCost`: addition counts
  and separate uniform weights for additions and terms.

## Main results

* `Cslib.Circuits.SumOfTerms.cost_weightedCost`: separate the two gate counts.

## References

* Adapted from Basis/SumOfTerms.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.SumOfTerms

universe u

/-- Free binary addition and a nullary gate for each dictionary term. -/
inductive Op (T : Type u)
  | add
  | term (value : T)
  deriving DecidableEq

/-- Addition reads two wires; dictionary terms read none. -/
abbrev Op.arity {T : Type*} : Op T → ℕ
  | .add => 2
  | .term _ => 0

/-- The signature for sums of dictionary terms. -/
abbrev signature (T : Type u) : Signature where
  Op := Op T
  Arity := Op.arity

/-- Interpret dictionary terms by their values and addition by carrier addition. -/
def interpretation {T V : Type*} [Add V] (value : T → V) : Interpretation (signature T) V
  | .add, args => args 0 + args 1
  | .term t, _ => value t

/-- Interpreting `.add` adds its two arguments in `V`. -/
@[simp] theorem interpretation_add {T V : Type*} [Add V] (value : T → V)
    (args : Fin 2 → V) : interpretation value .add args = args 0 + args 1 := rfl

/-- Interpreting `.term t` evaluates the dictionary term `t` via `value`. -/
@[simp] theorem interpretation_term {T V : Type*} [Add V] (value : T → V) (t : T)
    (args : Fin 0 → V) : interpretation value (.term t) args = value t := rfl

/-- Charge each dictionary term its weight; addition is free. -/
def dictionaryCost {T : Type*} (weight : T → ℕ) : Op T → ℕ
  | .add => 0
  | .term t => weight t

/-- Addition has `dictionaryCost` zero. -/
@[simp] theorem dictionaryCost_add {T : Type*} (weight : T → ℕ) :
    dictionaryCost weight .add = 0 := rfl

/-- The `dictionaryCost` of `.term t` is `weight t`. -/
@[simp] theorem dictionaryCost_term {T : Type*} (weight : T → ℕ) (t : T) :
    dictionaryCost weight (.term t) = weight t := rfl

/-- Count dictionary gates, with free addition. -/
abbrev termCost {T : Type*} : Op T → ℕ := dictionaryCost fun _ => 1

/-- Count additions; dictionary gates are free. -/
def addCost {T : Type*} : Op T → ℕ
  | .add => 1
  | .term _ => 0

/-- Assign one weight to additions and another to dictionary gates. -/
def weightedCost {T : Type*} (addition term : ℕ) : Op T → ℕ
  | .add => addition
  | .term _ => term

/-- Uniform weights separate into the addition and dictionary gate counts. -/
theorem cost_weightedCost {T : Type*} {n g : ℕ} (p : Program (signature T) n g)
    (addition term : ℕ) :
    p.cost (weightedCost addition term) = addition * p.cost addCost + term * p.cost termCost := by
  simp only [Program.cost_eq_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases (p.lines i).op <;> simp [weightedCost, addCost]

end Cslib.Circuits.SumOfTerms
