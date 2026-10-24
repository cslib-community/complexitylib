/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Unbounded
public import Complexity.Foundations.Data.BitString.Threshold

/-!
# The basis of threshold gates

The threshold gate `Th^m_j` of `m` arguments says that at least `j` of them are true
(`Cslib.threshold m j`). The threshold gates of every arity and every cutoff, together with
negation, form the basis of threshold circuits [Hajnal et al., Section 2][HMPST1993]. Here the
gates are unweighted; a gate with weights `±1` is a threshold gate reading some of its arguments
negated. As for AC⁰ circuits over the unbounded fan-in basis, negations are free in the depth that
counts threshold gates (`Threshold.thresholdCost`).

Cutoff `0` is the constant `true`, a cutoff above the arity the constant `false`
(`Cslib.threshold_zero_right`, `Cslib.threshold_eq_false_of_lt`), cutoff `1` the disjunction and
cutoff `m` the conjunction of `m` arguments (`Cslib.threshold_one_right`, `Cslib.threshold_self`).
So the unbounded fan-in basis maps into the threshold basis keeping the meaning of every operation
(`Threshold.ofUnbounded`), and its AND/OR depth becomes the threshold depth
(`Threshold.thresholdCost_ofUnbounded`). The majority gate of `m` arguments is the threshold gate
`Th^m_⌈m/2⌉` (`Cslib.majority`), so the basis of TC⁰ maps into the threshold basis too
(`Threshold.ofMajority`).

## Main definitions

* `Cslib.Circuits.Boolean.Threshold.Op`, `Cslib.Circuits.Boolean.Threshold.Op.arity`,
  `Cslib.Circuits.Boolean.Threshold.signature`: negation, and the threshold gates of every arity
  and cutoff.
* `Cslib.Circuits.Boolean.Threshold.interpretation`: their Boolean meaning.
* `Cslib.Circuits.Boolean.Threshold.thresholdCost`: the costs of the threshold depth, in which
  negations are free.
* `Cslib.Circuits.Boolean.Threshold.ofUnboundedOp`,
  `Cslib.Circuits.Boolean.Threshold.ofUnbounded`: the unbounded fan-in basis inside the threshold
  basis.
* `Cslib.Circuits.Boolean.Threshold.ofMajorityOp`,
  `Cslib.Circuits.Boolean.Threshold.ofMajority`: the basis of TC⁰, with majority gates, inside the
  threshold basis.

## Main results

* `Cslib.Circuits.Boolean.Threshold.preserves_ofUnbounded`: conjunctions and disjunctions are
  threshold gates.
* `Cslib.Circuits.Boolean.Threshold.thresholdCost_ofUnbounded`: the AND/OR depth is the threshold
  depth.
* `Cslib.Circuits.Boolean.Threshold.preserves_ofMajority`: majority gates are threshold gates.

## References

* [A. Hajnal, W. Maass, P. Pudlák, M. Szegedy, G. Turán, *Threshold circuits of bounded
  depth*][HMPST1993]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Threshold

/-- Negation, and the threshold gate of `m` arguments with cutoff `j` for every `m` and `j`. -/
inductive Op where
  /-- Negation. -/
  | not
  /-- The threshold gate `Th^m_j`: at least `j` of its `m` arguments are true. -/
  | threshold (m j : ℕ)
  deriving DecidableEq

/-- The arity of an operation. -/
abbrev Op.arity : Op → ℕ
  | .not => 1
  | .threshold m _ => m

/-- The signature of negation and of the threshold gates. It is reducible, so that case analysis
on its operations sees their arities. -/
abbrev signature : Signature :=
  ⟨Op, Op.arity⟩

/-- The Boolean meaning of the operations. -/
def interpretation : Interpretation signature Bool
  | .not, x => !x (0 : Fin 1)
  | .threshold m j, x => Cslib.threshold m j x

/-- The threshold-basis interpretation of `.not` is Boolean negation of its single argument. -/
@[simp] theorem interpretation_not (x : Fin 1 → Bool) :
    interpretation .not x = !x 0 :=
  rfl

/-- The threshold-basis interpretation of `.threshold m j` is `Cslib.threshold m j`. -/
@[simp] theorem interpretation_threshold (m j : ℕ) (x : Fin m → Bool) :
    interpretation (.threshold m j) x = Cslib.threshold m j x :=
  rfl

/-- The cost of an operation in the threshold depth: negations are free. With these costs,
`Circuit.depthWith` is the largest number of threshold gates on a path, as
`Unbounded.andOrCost` counts the AND and OR gates of circuits over the unbounded fan-in basis. -/
def thresholdCost : Op → ℕ
  | .not => 0
  | .threshold _ _ => 1

/-- Negation has `thresholdCost` equal to `0`. -/
@[simp] theorem thresholdCost_not : thresholdCost .not = 0 := rfl

/-- Every threshold gate `.threshold m j` has `thresholdCost` equal to `1`. -/
@[simp] theorem thresholdCost_threshold (m j : ℕ) : thresholdCost (.threshold m j) = 1 := rfl

/-- Every operation in the threshold basis has `thresholdCost` at most `1`. -/
theorem thresholdCost_le_one (op : Op) : thresholdCost op ≤ 1 := by
  cases op <;> simp

/-- The operations of the unbounded fan-in basis as threshold gates: the conjunction of `m`
arguments is `Th^m_m` and their disjunction is `Th^m_1`. -/
def ofUnboundedOp : Unbounded.Op → Op
  | .not => .not
  | .and m => .threshold m m
  | .or m => .threshold m 1

/-- The unbounded fan-in basis inside the threshold basis. -/
def ofUnbounded : Unbounded.signature.Hom signature :=
  ⟨ofUnboundedOp, fun op => by cases op <;> rfl⟩

/-- `ofUnbounded` acts on operations as `ofUnboundedOp`. -/
@[simp] theorem ofUnbounded_apply (op : Unbounded.Op) : ofUnbounded op = ofUnboundedOp op :=
  rfl

/-- Conjunctions and disjunctions are threshold gates. -/
instance preserves_ofUnbounded : ofUnbounded.Preserves Unbounded.interpretation interpretation :=
  ⟨fun op x => by
    cases op with
    | not => rfl
    | and m => exact threshold_self x
    | or m => exact threshold_one_right x⟩

/-- The AND/OR depth of a circuit over the unbounded fan-in basis is the threshold depth of its
translation. -/
@[simp] theorem thresholdCost_ofUnbounded (op : Unbounded.Op) :
    thresholdCost (ofUnbounded op) = Unbounded.andOrCost op := by
  cases op <;> rfl

/-- The operations of the basis of TC⁰ as threshold gates: the majority gate of `m` arguments is
`Th^m_⌈m/2⌉`. -/
def ofMajorityOp : Unbounded.ExtOp → Op
  | .ac op => ofUnboundedOp op
  | .gate m => .threshold m ((m + 1) / 2)

/-- The basis of TC⁰, the unbounded fan-in basis with majority gates, inside the threshold basis. -/
def ofMajority : Unbounded.extSignature.Hom signature :=
  ⟨ofMajorityOp, fun op => by rcases op with (_ | _ | _) | _ <;> rfl⟩

/-- `ofMajority` acts on operations as `ofMajorityOp`. -/
@[simp] theorem ofMajority_apply (op : Unbounded.ExtOp) : ofMajority op = ofMajorityOp op :=
  rfl

/-- Majority gates are threshold gates. -/
instance preserves_ofMajority :
    ofMajority.Preserves (Unbounded.extInterpretation majority) interpretation :=
  ⟨fun op x => by
    cases op with
    | ac op => exact preserves_ofUnbounded.interpret_eq op x
    | gate m => rfl⟩

end Cslib.Circuits.Boolean.Threshold
