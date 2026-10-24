/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Simulation
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Counting the binary gates of De Morgan circuits

The size of a De Morgan circuit counts every gate. The usual measure for lower bounds charges only
the AND and OR gates and lets negations and constants be free [Jukna, Section 1.2][Jukna2012]. It
is the cost of a program for `binaryCost`, and it is at most the size
(`Program.cost_binaryCost_le`).

## Main definitions

* `Cslib.Circuits.Boolean.Op.IsBinary`: AND and OR, the operations of arity two.
* `Cslib.Circuits.Boolean.binaryCost`: the cost function charging one for each AND and OR gate.

## Main results

* `Cslib.Circuits.Program.cost_binaryCost_le`: the number of binary gates is at most the size.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {n g : ℕ}

namespace Boolean

/-- The binary operations of the De Morgan basis, AND and OR. -/
def Op.IsBinary (op : Op) : Prop :=
  signature.Arity op = 2

/-- Decidability of whether a De Morgan operation is binary. -/
instance : DecidablePred Op.IsBinary :=
  fun op => inferInstanceAs (Decidable (signature.Arity op = 2))

/-- A De Morgan operation is binary if and only if it is `.and` or `.or`. -/
theorem Op.isBinary_iff {op : Op} : op.IsBinary ↔ op = .and ∨ op = .or := by
  cases op <;> simp [Op.IsBinary]

/-- The conjunction operation `.and` is binary. -/
theorem Op.isBinary_and : Op.and.IsBinary :=
  rfl

/-- The disjunction operation `.or` is binary. -/
theorem Op.isBinary_or : Op.or.IsBinary :=
  rfl

/-- The arguments of a binary operation are numbered `0` and `1`. -/
theorem Op.IsBinary.val_lt_two {op : Op} (h : op.IsBinary) (s : Fin (signature.Arity op)) :
    (s : ℕ) < 2 :=
  s.isLt.trans_eq h

/-- Two different arguments of a binary operation are all of its arguments. -/
theorem Op.IsBinary.eq_or_eq {op : Op} (h : op.IsBinary) {s t : Fin (signature.Arity op)}
    (hst : s ≠ t) (u : Fin (signature.Arity op)) : u = s ∨ u = t := by
  have hs := h.val_lt_two s
  have ht := h.val_lt_two t
  have hu := h.val_lt_two u
  rw [Ne, Fin.ext_iff] at hst
  rw [Fin.ext_iff, Fin.ext_iff]
  omega

/-- The cost function charging one for each AND and OR gate and nothing for negations and
constants. Its counterparts for the other bases are `Monotone.binaryCost`, its restriction to the
monotone basis (`Monotone.binaryCost_toDeMorgan`), and `Unbounded.andOrCost`, which also charges
the constants of the unbounded fan-in basis, its AND and OR gates of no arguments. -/
def binaryCost : Op → ℕ
  | .and | .or => 1
  | .const _ | .not => 0

/-- A conjunction gate has binary cost `1`. -/
@[simp] theorem binaryCost_and : binaryCost .and = 1 :=
  rfl

/-- A disjunction gate has binary cost `1`. -/
@[simp] theorem binaryCost_or : binaryCost .or = 1 :=
  rfl

/-- A negation gate has binary cost `0`. -/
@[simp] theorem binaryCost_not : binaryCost .not = 0 :=
  rfl

/-- A constant gate has binary cost `0`. -/
@[simp] theorem binaryCost_const (b : Bool) : binaryCost (.const b) = 0 :=
  rfl

/-- Every De Morgan operation has binary cost at most `1`. -/
theorem binaryCost_le_one (op : Op) : binaryCost op ≤ 1 := by
  cases op <;> simp

/-- The binary cost of an operation is `1` if it is binary and `0` otherwise. -/
theorem binaryCost_eq_ite (op : Op) : binaryCost op = if op.IsBinary then 1 else 0 := by
  cases op <;> simp [Op.IsBinary]

end Boolean

/-- The number of binary gates of a program is at most its number of gates. -/
theorem Program.cost_binaryCost_le (p : Program Boolean.signature n g) :
    p.cost Boolean.binaryCost ≤ g :=
  (p.cost_le_mul Boolean.binaryCost_le_one).trans_eq (one_mul g)

end Cslib.Circuits
