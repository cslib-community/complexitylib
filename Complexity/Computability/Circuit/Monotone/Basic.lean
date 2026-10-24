/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.BinaryCost
public import Complexity.Computability.Circuit.MapOp
public import Mathlib.Data.Fintype.Basic

/-!
# Monotone circuits

The monotone basis has the Boolean constants, binary conjunction and binary disjunction: the De
Morgan basis (`Cslib.Circuits.Boolean.signature`) without negation. Each of its operations is
monotone (`interpretation_mono`), and so is every function computed by a monotone circuit. The
depth of monotone formulas charges AND and OR gates and lets constants be free (`binaryCost`), as
for De Morgan formulas, and the monotone basis maps into the De Morgan basis (`toDeMorgan`)
keeping meanings and these costs (`binaryCost_toDeMorgan`).

## Main definitions

* `Cslib.Circuits.Monotone.Op`, `Cslib.Circuits.Monotone.signature`,
  `Cslib.Circuits.Monotone.interpretation`.
* `Cslib.Circuits.Monotone.binaryCost`: the cost function charging one for each AND and OR gate.
* `Cslib.Circuits.Monotone.andCost`: the cost function charging only AND gates.
* `Cslib.Circuits.Monotone.toDeMorgan`: the monotone basis inside the De Morgan basis.

## Main results

* `Cslib.Circuits.Monotone.interpretation_mono`: the operations are monotone.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Chapter 9][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

/-- Operations of the monotone basis. -/
inductive Op where
  /-- A Boolean constant. -/
  | const (b : Bool)
  /-- Binary conjunction. -/
  | and
  /-- Binary disjunction. -/
  | or
  deriving DecidableEq

/-- Finite enumeration of the monotone basis operations `Op`. -/
instance : Fintype Op :=
  ⟨{.const false, .const true, .and, .or}, fun op => by rcases op with (_ | _) | _ | _ <;> simp⟩

/-- The monotone signature: constants, binary conjunction and binary disjunction. -/
abbrev signature : Signature where
  Op := Op
  Arity
    | .const _ => 0
    | .and | .or => 2

/-- The Boolean interpretation of the monotone basis. -/
def interpretation : Interpretation signature Bool
  | .const b, _ => b
  | .and, x => x 0 && x 1
  | .or, x => x 0 || x 1

/-- Under `interpretation`, `.const b` evaluates to `b`. -/
@[simp] theorem interpretation_const (b : Bool) (x : Fin 0 → Bool) :
    interpretation (.const b) x = b := rfl

/-- Under `interpretation`, `.and` evaluates to `x 0 && x 1`. -/
@[simp] theorem interpretation_and (x : Fin 2 → Bool) : interpretation .and x = (x 0 && x 1) :=
  rfl

/-- Under `interpretation`, `.or` evaluates to `x 0 || x 1`. -/
@[simp] theorem interpretation_or (x : Fin 2 → Bool) : interpretation .or x = (x 0 || x 1) :=
  rfl

/-- The operations of the monotone basis are monotone. -/
theorem interpretation_mono (op : Op) {x y : Fin (signature.Arity op) → Bool}
    (h : ∀ i, x i ≤ y i) : interpretation op x ≤ interpretation op y := by
  cases op with
  | const b => exact Bool.le_refl b
  | and | or =>
    have h0 := h 0
    have h1 := h 1
    revert h0 h1
    simp only [interpretation]
    cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;> decide

/-- The cost function charging one for each AND and OR gate and nothing for constants, the
monotone counterpart of `Boolean.binaryCost` (`binaryCost_toDeMorgan`). -/
def binaryCost : Op → ℕ
  | .and | .or => 1
  | .const _ => 0

/-- An AND gate costs one level. -/
@[simp] theorem binaryCost_and : binaryCost .and = 1 :=
  rfl

/-- An OR gate costs one level. -/
@[simp] theorem binaryCost_or : binaryCost .or = 1 :=
  rfl

/-- Constants are free. -/
@[simp] theorem binaryCost_const (b : Bool) : binaryCost (.const b) = 0 :=
  rfl

/-- Count AND gates, with constants and OR gates free. -/
def andCost : Op → ℕ
  | .and => 1
  | _ => 0

/-- An AND gate has `andCost` equal to `1`. -/
@[simp] theorem andCost_and : andCost .and = 1 := rfl

/-- An OR gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_or : andCost .or = 0 := rfl

/-- A constant gate has `andCost` equal to `0`. -/
@[simp] theorem andCost_const (b : Bool) : andCost (.const b) = 0 := rfl

/-! ### The monotone basis inside the De Morgan basis -/

/-- The monotone basis is the De Morgan basis without negation. -/
def toDeMorgan : signature.Hom Boolean.signature where
  toFun
    | .const b => .const b
    | .and => .and
    | .or => .or
  arity_eq op := by cases op <;> rfl

/-- `toDeMorgan` maps `.const b` to `.const b`. -/
@[simp] theorem toDeMorgan_const (b : Bool) : toDeMorgan (.const b) = .const b :=
  rfl

/-- `toDeMorgan` maps `.and` to `.and`. -/
@[simp] theorem toDeMorgan_and : toDeMorgan .and = .and :=
  rfl

/-- `toDeMorgan` maps `.or` to `.or`. -/
@[simp] theorem toDeMorgan_or : toDeMorgan .or = .or :=
  rfl

/-- The monotone operations mean what their De Morgan images mean. -/
instance : toDeMorgan.Preserves interpretation Boolean.interpretation :=
  ⟨fun op _ => by cases op <;> rfl⟩

/-- The De Morgan image of an operation costs what it costs in the monotone basis. -/
@[simp] theorem binaryCost_toDeMorgan (op : Op) :
    Boolean.binaryCost (toDeMorgan op) = binaryCost op := by
  cases op <;> rfl

/-- The monotone operations embed injectively into the De Morgan basis. -/
theorem toDeMorgan_injective : Function.Injective toDeMorgan := by
  intro a b h
  rcases a with (_ | _) | _ | _ <;> rcases b with (_ | _) | _ | _ <;> first | rfl | cases h


end Cslib.Circuits.Monotone
