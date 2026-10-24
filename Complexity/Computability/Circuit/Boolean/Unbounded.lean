/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.MapOp
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Foundations.Data.BitString
import Complexity.Computability.Circuit.Simulation

/-!
# The Boolean basis with unbounded fan-in

The basis of AC⁰: negation, and conjunctions and disjunctions of any number of arguments. Circuits
and formulas over this basis of constant depth are the setting of Håstad's lower bound for parity.
The conjunction and the disjunction of no arguments are the constants `true` and `false`.

Adding one gate of every arity, computing a given family of Boolean functions `g`, gives the
bases of TC⁰ (majority gates) and AC⁰[q] (`MOD_q` gates): `extSignature` and
`extInterpretation g`, into which the unbounded fan-in basis maps by `toExt`.

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.Op`, `Cslib.Circuits.Boolean.Unbounded.Op.arity`,
  `Cslib.Circuits.Boolean.Unbounded.signature`: negation, and conjunction and disjunction of every
  arity.
* `Cslib.Circuits.Boolean.Unbounded.interpretation`: their Boolean meaning.
* `Cslib.Circuits.Boolean.Unbounded.andOrCost`: the costs of the AND/OR depth, in which
  negations are free.
* `Cslib.Circuits.Boolean.Unbounded.deMorganOp`,
  `Cslib.Circuits.Boolean.Unbounded.deMorganToUnbounded`: the De Morgan basis inside it.
* `Cslib.Circuits.Boolean.Unbounded.ExtOp`, `Cslib.Circuits.Boolean.Unbounded.ExtOp.arity`,
  `Cslib.Circuits.Boolean.Unbounded.extSignature`,
  `Cslib.Circuits.Boolean.Unbounded.extInterpretation`,
  `Cslib.Circuits.Boolean.Unbounded.toExt`: the basis with one extra gate of every arity.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.interpretation_of_op_eq_not`,
  `Cslib.Circuits.Boolean.Unbounded.interpretation_of_op_eq_and`,
  `Cslib.Circuits.Boolean.Unbounded.interpretation_of_op_eq_or`: the values of the gates of a
  program.
* `Cslib.Circuits.Boolean.Unbounded.cost_andOrCost_eq_card`: the AND/OR cost of a program is its
  number of conjunctions and disjunctions.
* `Cslib.Circuits.Boolean.Unbounded.preserves_deMorganToUnbounded`: the De Morgan basis embeds
  with its meaning.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

/-- Negation, and conjunction and disjunction of `m` arguments for every `m`. -/
inductive Op where
  /-- Negation. -/
  | not
  /-- Conjunction of `m` arguments. -/
  | and (m : ℕ)
  /-- Disjunction of `m` arguments. -/
  | or (m : ℕ)
  deriving DecidableEq

/-- The arity of an operation. -/
abbrev Op.arity : Op → ℕ
  | .not => 1
  | .and m => m
  | .or m => m

/-- The signature of negation and of conjunction and disjunction of unbounded fan-in. It is
reducible, so that case analysis on its operations sees their arities. -/
abbrev signature : Signature :=
  ⟨Op, Op.arity⟩

/-- The Boolean meaning of the operations. -/
def interpretation : Interpretation signature Bool
  | .not, x => !x (0 : Fin 1)
  | .and _, x => decide (∀ j, x j = true)
  | .or _, x => decide (∃ j, x j = true)

/-- `interpretation .not` negates its single input bit. -/
@[simp] theorem interpretation_not (x : Fin 1 → Bool) :
    interpretation .not x = !x 0 :=
  rfl

/-- `interpretation (.and m)` is `true` iff all `m` arguments are `true`. -/
@[simp] theorem interpretation_and (m : ℕ) (x : Fin m → Bool) :
    interpretation (.and m) x = decide (∀ j, x j = true) :=
  rfl

/-- `interpretation (.or m)` is `true` iff at least one of its `m` arguments is `true`. -/
@[simp] theorem interpretation_or (m : ℕ) (x : Fin m → Bool) :
    interpretation (.or m) x = decide (∃ j, x j = true) :=
  rfl

section Lines

variable {n g : ℕ}

/-- A negation gate negates its argument. -/
theorem interpretation_of_op_eq_not {l : Line signature n g} (h : l.op = .not)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = !v (l.wires ⟨0, by simp [h]⟩) := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  rfl

/-- A conjunction gate is true when all its arguments are. -/
theorem interpretation_of_op_eq_and {l : Line signature n g} {m : ℕ} (h : l.op = .and m)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = true ↔ ∀ a, v (l.wires a) = true := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  simp

/-- A disjunction gate is true when one of its arguments is. -/
theorem interpretation_of_op_eq_or {l : Line signature n g} {m : ℕ} (h : l.op = .or m)
    (v : Wire n g → Bool) :
    interpretation l.op (fun a => v (l.wires a)) = true ↔ ∃ a, v (l.wires a) = true := by
  obtain ⟨op, ws⟩ := l
  simp only at h
  subst h
  simp

end Lines

/-- The cost of an operation in the AND/OR depth: negations are free. With these costs,
`Circuit.depthWith` is the largest number of conjunctions and disjunctions on a path, the usual
depth of AC⁰ circuits, in which negations sit at the inputs.

This is the counterpart of `Boolean.binaryCost` and `Monotone.binaryCost` for the bases of fan-in
two, which charge one for AND and OR and nothing for negations and constants. It is not their
transport along `deMorganToUnbounded`: this basis has no constants, and the De Morgan constants
become the conjunction and the disjunction of no arguments, which cost one here. -/
def andOrCost : Op → ℕ
  | .not => 0
  | .and _ => 1
  | .or _ => 1

/-- Negation has zero AND/OR cost. -/
@[simp] theorem andOrCost_not : andOrCost .not = 0 := rfl

/-- Unbounded conjunction has AND/OR cost `1`. -/
@[simp] theorem andOrCost_and (m : ℕ) : andOrCost (.and m) = 1 := rfl

/-- Unbounded disjunction has AND/OR cost `1`. -/
@[simp] theorem andOrCost_or (m : ℕ) : andOrCost (.or m) = 1 := rfl

/-- Every operation in the unbounded fan-in basis has AND/OR cost at most `1`. -/
theorem andOrCost_le_one (op : Op) : andOrCost op ≤ 1 := by
  cases op <;> simp

/-- Conjunctions and disjunctions cost one in the AND/OR depth. -/
theorem andOrCost_eq_one_of_ne_not {op : Op} (hop : op ≠ .not) : andOrCost op = 1 := by
  cases op <;> simp_all

open Finset in
/-- The AND/OR cost of a program is its number of conjunctions and disjunctions. -/
theorem cost_andOrCost_eq_card {n g : ℕ} (p : Program signature n g) :
    p.cost andOrCost = #{k | (p.lines k).op ≠ .not} := by
  rw [p.cost_eq_sum, card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun k _ => ?_
  by_cases h : (p.lines k).op = .not
  · simp [h]
  · simp [h, andOrCost_eq_one_of_ne_not h]

/-- The operations of the unbounded fan-in basis, and one extra gate of every arity. -/
inductive ExtOp where
  /-- An operation of the unbounded fan-in basis. -/
  | ac (op : Op)
  /-- The extra gate of `m` arguments. -/
  | gate (m : ℕ)
  deriving DecidableEq

/-- The arity of an operation of the extended basis. -/
abbrev ExtOp.arity : ExtOp → ℕ
  | .ac op => op.arity
  | .gate m => m

/-- The signature of the unbounded fan-in basis with one extra gate of every arity. It is
reducible, so that case analysis on its operations sees their arities. -/
abbrev extSignature : Signature :=
  ⟨ExtOp, ExtOp.arity⟩

/-- The Boolean meaning of the extended basis, with the extra gate of `m` arguments computing
`g m`. -/
def extInterpretation (g : ∀ m, BooleanFunction m) : Interpretation extSignature Bool
  | .ac op, x => interpretation op x
  | .gate m, x => g m x

/-- On an `AC⁰` operation `.ac op`, `extInterpretation g` agrees with `interpretation op`. -/
@[simp] theorem extInterpretation_ac (g : ∀ m, BooleanFunction m) (op : Op)
    (x : Fin op.arity → Bool) : extInterpretation g (.ac op) x = interpretation op x :=
  rfl

/-- On an extra gate `.gate m`, `extInterpretation g` evaluates `g m`. -/
@[simp] theorem extInterpretation_gate (g : ∀ m, BooleanFunction m) (m : ℕ) (x : Fin m → Bool) :
    extInterpretation g (.gate m) x = g m x :=
  rfl

/-- The unbounded fan-in basis inside its extension. -/
def toExt : signature.Hom extSignature :=
  ⟨ExtOp.ac, fun _ => rfl⟩

/-- The inclusion `toExt` preserves Boolean semantics for every family of gate functions `g`. -/
instance preserves_toExt (g : ∀ m, BooleanFunction m) :
    toExt.Preserves interpretation (extInterpretation g) :=
  ⟨fun _ _ => rfl⟩

/-- The operations of the De Morgan basis as operations of the unbounded fan-in basis: the
constants as the conjunction and disjunction of nothing. -/
def deMorganOp : Boolean.Op → Op
  | .const true => .and 0
  | .const false => .or 0
  | .not => .not
  | .and => .and 2
  | .or => .or 2

/-- The De Morgan basis inside the unbounded fan-in basis. -/
def deMorganToUnbounded : Boolean.signature.Hom signature :=
  ⟨deMorganOp, fun op => by rcases op with (_ | _) | _ | _ | _ <;> rfl⟩

/-- `deMorganToUnbounded` acts on operations via `deMorganOp`. -/
@[simp] theorem deMorganToUnbounded_apply (op : Boolean.Op) :
    deMorganToUnbounded op = deMorganOp op :=
  rfl

/-- The embedding `deMorganToUnbounded` preserves Boolean semantics. -/
instance preserves_deMorganToUnbounded :
    deMorganToUnbounded.Preserves Boolean.interpretation interpretation :=
  ⟨fun op x => by
    rcases op with (_ | _) | _ | _ | _
    · exact decide_eq_false fun ⟨j, _⟩ => j.elim0
    · exact decide_eq_true fun j => j.elim0
    · rfl
    · change decide (∀ j : Fin 2, x (Fin.cast rfl j) = true) = (x 0 && x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.and_eq_true, Fin.forall_fin_two]
      exact Iff.rfl
    · change decide (∃ j : Fin 2, x (Fin.cast rfl j) = true) = (x 0 || x 1)
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.or_eq_true, Fin.exists_fin_two]
      exact Iff.rfl⟩

end Cslib.Circuits.Boolean.Unbounded
