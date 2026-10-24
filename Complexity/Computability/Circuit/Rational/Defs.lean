/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Formula
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.FinCases

/-!
# Rational hitting lists: the model

Noncommutative rational formulas are formulas (`Cslib.Circuits.Formula`) over the signature
`ratSignature` of rational constants, addition, ordered multiplication and inversion. They are
evaluated relationally in any ring with a rational structure map: an inverse node requires an
actual two-sided inverse of its operand's value, so evaluation is partial. A formula is
*admissible* if some substitution of square rational matrices of positive dimension lies in its
domain, and *nonzero* if some such substitution yields a nonzero value. A finite list of matrix
substitutions *hits* the formulas of node count at most `s` if every admissible nonzero such
formula has an invertible value at some substitution on the list.

The node count of a formula, the source's size measure, counts every syntax-tree node: input
leaves, constants and operations (`Formula.nodeCount`, the native gate count `Formula.size` plus
the leaf count `Formula.leafSize`).

## Main definitions

* `Cslib.Circuits.Rational.RatOp`, `Cslib.Circuits.Rational.ratSignature`,
  `Cslib.Circuits.Rational.Formula`: the operation symbols, signature, and formulas, with
  constructors `Formula.var`, `Formula.const`, `Formula.add`, `Formula.mul`, `Formula.inv` and the
  induction principle `Formula.inductionOn`.
* `Cslib.Circuits.Rational.Formula.nodeCount`: the number of syntax-tree nodes.
* `Cslib.Circuits.Rational.Formula.Eval`: partial evaluation as a relation.
* `Cslib.Circuits.Rational.Mat`, `Cslib.Circuits.Rational.Tuple`: square rational matrices and
  matrix substitutions.
* `Cslib.Circuits.Rational.Evaluates`, `Cslib.Circuits.Rational.Admissible`,
  `Cslib.Circuits.Rational.Nonzero`: evaluation on rational matrices, and its domain and support.
* `Cslib.Circuits.Rational.Output`, `Cslib.Circuits.Rational.encodeNat`,
  `Cslib.Circuits.Rational.encodeRat`, `Cslib.Circuits.Rational.encodeTuple`,
  `Cslib.Circuits.Rational.encodeOutput`: lists of matrix substitutions of a common positive
  dimension and their binary encoding.
* `Cslib.Circuits.Rational.Hits`: the hitting property.

## Main results

* `Cslib.Circuits.Rational.Formula.eval_add_iff` and its siblings: evaluation unfolds along the
  constructors.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Model.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits.Rational

universe u

/-- The operation symbols of noncommutative rational formulas. -/
inductive RatOp where
  /-- A rational constant. -/
  | const (q : ℚ)
  /-- Addition. -/
  | add
  /-- Ordered multiplication. -/
  | mul
  /-- Inversion. -/
  | inv
  deriving DecidableEq

/-- The signature of rational formulas: constants are nullary, addition and multiplication are
binary, and inversion is unary. -/
abbrev ratSignature : Signature where
  Op := RatOp
  Arity
    | .const _ => 0
    | .add | .mul => 2
    | .inv => 1

/-- A noncommutative rational formula over `n` variables and rational constants. -/
abbrev Formula (n : ℕ) := Circuits.Formula ratSignature n

namespace Formula

variable {n : ℕ}

/-- The input variable `i`. -/
abbrev var (i : Fin n) : Formula n := .input i

/-- The rational constant `q`. -/
abbrev const (q : ℚ) : Formula n := .gate (.const q) Fin.elim0

/-- The sum of two formulas. -/
abbrev add (f g : Formula n) : Formula n := .gate .add ![f, g]

/-- The ordered product of two formulas. -/
abbrev mul (f g : Formula n) : Formula n := .gate .mul ![f, g]

/-- The inverse of a formula. -/
abbrev inv (f : Formula n) : Formula n := .gate .inv ![f]

/-- Induction on rational formulas, with one case for each constructor. -/
@[elab_as_elim]
theorem inductionOn {motive : Formula n → Prop} (f : Formula n)
    (var : ∀ i, motive (var i)) (const : ∀ q, motive (const q))
    (add : ∀ f g, motive f → motive g → motive (add f g))
    (mul : ∀ f g, motive f → motive g → motive (mul f g))
    (inv : ∀ f, motive f → motive (inv f)) : motive f := by
  induction f with
  | input i => exact var i
  | gate op args ih =>
    cases op with
    | const q =>
      have h : args = Fin.elim0 := funext fun i => Fin.elim0 i
      exact h ▸ const q
    | add =>
      have h : args = ![args 0, args 1] := by funext i; fin_cases i <;> rfl
      exact h ▸ add (args 0) (args 1) (ih 0) (ih 1)
    | mul =>
      have h : args = ![args 0, args 1] := by funext i; fin_cases i <;> rfl
      exact h ▸ mul (args 0) (args 1) (ih 0) (ih 1)
    | inv =>
      have h : args = ![args 0] := by funext i; fin_cases i; rfl
      exact h ▸ inv (args 0) (ih 0)

/-- The number of syntax-tree nodes, counting input leaves, constants and operations alike: the
operation nodes `Formula.size` together with the input leaves `Formula.leafSize`. -/
def nodeCount (f : Formula n) : ℕ := f.size + f.leafSize

/-- A variable leaf has node count `1`. -/
@[simp] theorem nodeCount_var (i : Fin n) : (var i).nodeCount = 1 := rfl

/-- A rational constant node has node count `1`. -/
@[simp] theorem nodeCount_const (q : ℚ) : (const q : Formula n).nodeCount = 1 := by
  simp [nodeCount]

/-- The node count of `add f g` is `f.nodeCount + g.nodeCount + 1`. -/
@[simp] theorem nodeCount_add (f g : Formula n) :
    (add f g).nodeCount = f.nodeCount + g.nodeCount + 1 := by
  simp only [nodeCount, Circuits.Formula.size_gate, Circuits.Formula.leafSize_gate,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- The node count of `mul f g` is `f.nodeCount + g.nodeCount + 1`. -/
@[simp] theorem nodeCount_mul (f g : Formula n) :
    (mul f g).nodeCount = f.nodeCount + g.nodeCount + 1 := by
  simp only [nodeCount, Circuits.Formula.size_gate, Circuits.Formula.leafSize_gate,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  omega

/-- The node count of `inv f` is `f.nodeCount + 1`. -/
@[simp] theorem nodeCount_inv (f : Formula n) : (inv f).nodeCount = f.nodeCount + 1 := by
  simp only [nodeCount, Circuits.Formula.size_gate, Circuits.Formula.leafSize_gate,
    Fin.sum_univ_one, Matrix.cons_val_zero]
  omega

/-- A formula has at least one node. -/
theorem nodeCount_pos (f : Formula n) : 0 < f.nodeCount := by
  induction f using inductionOn <;> simp

/-- `f.Eval c X v`: the formula `f` is defined at the substitution `X` in the ring `R`, with
rational constants interpreted by `c`, and has the value `v`. An inverse node requires an actual
two-sided inverse of the value of its operand, not a totalized inverse. -/
def Eval {R : Type u} [Ring R] (c : ℚ →+* R) (X : Fin n → R) : Formula n → R → Prop
  | .input i, v => v = X i
  | .gate (.const q) _, v => v = c q
  | .gate .add args, v => ∃ a b, Eval c X (args 0) a ∧ Eval c X (args 1) b ∧ v = a + b
  | .gate .mul args, v => ∃ a b, Eval c X (args 0) a ∧ Eval c X (args 1) b ∧ v = a * b
  | .gate .inv args, v => ∃ a, Eval c X (args 0) a ∧ a * v = 1 ∧ v * a = 1

section Eval

variable {R : Type u} [Ring R] {c : ℚ →+* R} {X : Fin n → R} {f g : Formula n} {v : R}

/-- `(var i).Eval c X v` holds if and only if `v = X i`. -/
@[simp] theorem eval_var_iff {i : Fin n} : (var i).Eval c X v ↔ v = X i := Iff.rfl

/-- `(const q).Eval c X v` holds if and only if `v = c q`. -/
@[simp] theorem eval_const_iff {q : ℚ} : (const q : Formula n).Eval c X v ↔ v = c q := Iff.rfl

/-- `(add f g).Eval c X v` holds if and only if `f` and `g` evaluate to `a` and `b` with
`v = a + b`. -/
@[simp] theorem eval_add_iff :
    (add f g).Eval c X v ↔ ∃ a b, f.Eval c X a ∧ g.Eval c X b ∧ v = a + b := Iff.rfl

/-- `(mul f g).Eval c X v` holds if and only if `f` and `g` evaluate to `a` and `b` with
`v = a * b`. -/
@[simp] theorem eval_mul_iff :
    (mul f g).Eval c X v ↔ ∃ a b, f.Eval c X a ∧ g.Eval c X b ∧ v = a * b := Iff.rfl

/-- `(inv f).Eval c X v` holds if and only if `f` evaluates to a two-sided inverse `a` of `v`. -/
@[simp] theorem eval_inv_iff :
    (inv f).Eval c X v ↔ ∃ a, f.Eval c X a ∧ a * v = 1 ∧ v * a = 1 := Iff.rfl

/-- A variable evaluates to its assigned value. -/
theorem Eval.var (i : Fin n) : (Formula.var i).Eval c X (X i) := rfl

/-- A constant evaluates through the scalar homomorphism. -/
theorem Eval.const (q : ℚ) : (Formula.const q : Formula n).Eval c X (c q) := rfl

/-- Defined summands give a defined sum. -/
theorem Eval.add {a b : R} (ha : f.Eval c X a) (hb : g.Eval c X b) :
    (Formula.add f g).Eval c X (a + b) :=
  ⟨a, b, ha, hb, rfl⟩

/-- Defined factors give a defined ordered product. -/
theorem Eval.mul {a b : R} (ha : f.Eval c X a) (hb : g.Eval c X b) :
    (Formula.mul f g).Eval c X (a * b) :=
  ⟨a, b, ha, hb, rfl⟩

/-- An inverse node is defined at a two-sided inverse of the value of its operand. -/
theorem Eval.inv {a b : R} (ha : f.Eval c X a) (hab : a * b = 1) (hba : b * a = 1) :
    (Formula.inv f).Eval c X b :=
  ⟨a, ha, hab, hba⟩

end Eval

end Formula

/-- Square rational matrices of the specified dimension. -/
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℚ

/-- A matrix substitution for every input variable. -/
abbrev Tuple (n d : ℕ) := Fin n → Mat d

/-- Defined evaluation on a rational matrix tuple. -/
def Evaluates {n d : ℕ} (f : Formula n) (X : Tuple n d) (v : Mat d) : Prop :=
  f.Eval (algebraMap ℚ (Mat d)) X v

/-- Some positive-dimensional rational matrix substitution is in the formula's domain. -/
def Admissible {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v

/-- Some positive-dimensional rational matrix substitution has a defined nonzero value. -/
def Nonzero {n : ℕ} (f : Formula n) : Prop :=
  ∃ d, 0 < d ∧ ∃ (X : Tuple n d), ∃ v, Evaluates f X v ∧ v ≠ 0

/-- A finite list of matrix substitutions, all of one common positive dimension. -/
structure Output (n : ℕ) where
  /-- Common dimension of all matrix tuples. -/
  dimension : ℕ
  /-- Exclude the trivial zero-dimensional matrix ring. -/
  dimension_pos : 0 < dimension
  /-- The finite list of matrix substitutions, in output order. -/
  tuples : List (Tuple n dimension)

/-- Little-endian unsigned binary, prefixed by a unary bit-length and a zero terminator. This is a
self-delimiting binary encoding, including zero. -/
def encodeNat (a : ℕ) : List Bool :=
  let ds := (Nat.digits 2 a).map (fun b => b != 0)
  List.replicate ds.length true ++ [false] ++ ds

/-- Sign bit, binary numerator magnitude, and positive binary denominator. `Rat.num` and `Rat.den`
are the canonical reduced numerator and denominator. -/
def encodeRat (a : ℚ) : List Bool :=
  [decide (a.num < 0)] ++ encodeNat a.num.natAbs ++ encodeNat a.den

/-- Serialize a tuple in variable, row, and column order using reduced rational encodings. -/
def encodeTuple {n d : ℕ} (X : Tuple n d) : List Bool :=
  (List.finRange n).flatMap fun i =>
    (List.finRange d).flatMap fun j =>
      (List.finRange d).flatMap fun k => encodeRat (X i j k)

/-- Encode the common dimension, tuple count, and all rational matrix entries. -/
def encodeOutput {n : ℕ} (H : Output n) : List Bool :=
  encodeNat H.dimension ++ encodeNat H.tuples.length ++ H.tuples.flatMap encodeTuple

/-- Every admissible nonzero formula with at most `s` nodes has an invertible value at some
substitution on the list. -/
def Hits {n : ℕ} (s : ℕ) (H : Output n) : Prop :=
  ∀ f : Formula n, f.nodeCount ≤ s → Admissible f → Nonzero f →
    ∃ X ∈ H.tuples, ∃ v, Evaluates f X v ∧ IsUnit v

end Cslib.Circuits.Rational
