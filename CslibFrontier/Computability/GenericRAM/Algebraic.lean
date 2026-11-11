/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Field.ZMod

/-!
# Exact algebraic RAM instances

Values are tagged natural words or exact field elements. Only the natural arm can address
memory; a configuration `w` bounds words and control labels by `2 ^ w`. Arithmetic on words
faults on overflow, subtraction underflow, or zero divisors. Field arithmetic is exact;
division by zero faults. There is a one-way word-to-field operation, no field-to-word cast,
floor, transcendental operation, or square root.

Programs contain natural-word and rational literal symbols, never arbitrary field constants.
A rational literal faults when its denominator becomes zero in the field. Thus constants are
countable syntax even for the real model; positive characteristic is handled explicitly.

The real instance follows the separation of word addresses and exact real values in
[Erickson, van der Hoog, and Miltzow, §6.1][EricksonVanDerHoogMiltzow2024]. This is a tagged,
finite-register variant with one tagged memory, not their literal pair of word/real arrays.
It also uses checked word arithmetic rather than modular arithmetic. The real interpretation
is noncomputable mathematical semantics. Prime `ZMod` instances are executable and offer
equality, but no ordering of field elements. Every instruction uses the generic core's unit
cost; no bit-cost or Turing-machine implementation of exact real arithmetic is claimed.

## Main definitions

* `Algebraic.model`: a field with an explicitly supplied optional strict comparison.
* `Algebraic.real`: exact real arithmetic and comparison with bounded natural addresses.
* `Algebraic.primeField`: exact prime-field arithmetic with bounded natural addresses.

## References

* [Erickson, van der Hoog, and Miltzow, *Smoothing the Gap Between NP and ER*]
  [EricksonVanDerHoogMiltzow2024], §6.1.
-/

@[expose] public section

namespace Cslib.GenericRAM.Algebraic

/-- Finitely representable literal syntax, independent of arbitrary field inputs. -/
inductive Const where
  /-- A natural word, subject to the configured width. -/
  | word (n : ℕ)
  /-- A rational field literal, defined only when its denominator remains nonzero. -/
  | rational (q : ℚ)
  deriving DecidableEq

/-- Typed word and field operations. Mixed tags fault except for `toField`. -/
inductive Operation where
  /-- Natural addition, checked for overflow by result admissibility. -/
  | wordAdd
  /-- Natural subtraction, undefined on underflow. -/
  | wordSub
  /-- Natural multiplication, checked for overflow by result admissibility. -/
  | wordMul
  /-- Natural quotient, undefined at zero divisor. -/
  | wordDiv
  /-- Natural remainder, undefined at zero divisor. -/
  | wordMod
  /-- Exact addition. -/
  | add
  /-- Exact subtraction. -/
  | sub
  /-- Exact multiplication. -/
  | mul
  /-- Exact division, undefined at zero divisor. -/
  | div
  /-- Exact additive inverse. -/
  | neg
  /-- Convert a natural word to its field value, with no inverse conversion. -/
  | toField
  deriving DecidableEq

/-- Unary conversion/negation and binary arithmetic. -/
abbrev Operation.arity : Operation → ℕ
  | .neg | .toField => 1
  | _ => 2

/-- The algebraic operation signature. -/
abbrev operations : Cslib.Circuits.Signature := ⟨Operation, Operation.arity⟩

/-- Tests do not compare values with different tags. -/
inductive Test where
  /-- Equality of natural words. -/
  | wordEq
  /-- Strict order of natural words. -/
  | wordLt
  /-- Equality in the field. -/
  | eq
  /-- The supplied partial strict comparison in the field. -/
  | lt
  deriving DecidableEq

/-- Every test takes two registers. -/
abbrev tests : Cslib.Circuits.Signature := ⟨Test, fun _ => 2⟩

variable {K : Type*} [Field K] [DecidableEq K]

/-- Check natural words; exact field values have no bit bound. -/
def admissible (w : ℕ) : ℕ ⊕ K → Bool
  | .inl n => decide (n < 2 ^ w)
  | .inr _ => true

/-- Extract only a bounded natural address; even integral field values are rejected. -/
def address (w : ℕ) : ℕ ⊕ K → Option ℕ
  | .inl n => if n < 2 ^ w then some n else none
  | .inr _ => none

/-- Interpret rational symbols only when the denominator is nonzero in the field. -/
def constant : Const → Option (ℕ ⊕ K)
  | .word n => some (.inl n)
  | .rational q => if (q.den : K) = 0 then none else some (.inr (q.num / q.den))

/-- Partial arithmetic interpretation; operands must have the indicated tags. -/
def evalOp : (op : Operation) → (Fin op.arity → ℕ ⊕ K) → Option (ℕ ⊕ K)
  | .wordAdd, xs => match xs 0, xs 1 with
    | .inl a, .inl b => some (.inl (a + b))
    | _, _ => none
  | .wordSub, xs => match xs 0, xs 1 with
    | .inl a, .inl b => if b ≤ a then some (.inl (a - b)) else none
    | _, _ => none
  | .wordMul, xs => match xs 0, xs 1 with
    | .inl a, .inl b => some (.inl (a * b))
    | _, _ => none
  | .wordDiv, xs => match xs 0, xs 1 with
    | .inl a, .inl b => if b = 0 then none else some (.inl (a / b))
    | _, _ => none
  | .wordMod, xs => match xs 0, xs 1 with
    | .inl a, .inl b => if b = 0 then none else some (.inl (a % b))
    | _, _ => none
  | .add, xs => match xs 0, xs 1 with
    | .inr a, .inr b => some (.inr (a + b))
    | _, _ => none
  | .sub, xs => match xs 0, xs 1 with
    | .inr a, .inr b => some (.inr (a - b))
    | _, _ => none
  | .mul, xs => match xs 0, xs 1 with
    | .inr a, .inr b => some (.inr (a * b))
    | _, _ => none
  | .div, xs => match xs 0, xs 1 with
    | .inr a, .inr b => if b = 0 then none else some (.inr (a / b))
    | _, _ => none
  | .neg, xs => match xs 0 with
    | .inr a => some (.inr (-a))
    | _ => none
  | .toField, xs => match xs 0 with
    | .inl a => some (.inr a)
    | _ => none

/-- Partial test interpretation. Finite fields supply no order comparison. -/
def evalTest (less : K → K → Option Bool) (t : Test) (xs : Fin 2 → ℕ ⊕ K) :
    Option Bool :=
  match t, xs 0, xs 1 with
  | .wordEq, .inl a, .inl b => some (decide (a = b))
  | .wordLt, .inl a, .inl b => some (decide (a < b))
  | .eq, .inr a, .inr b => some (decide (a = b))
  | .lt, .inr a, .inr b => less a b
  | _, _, _ => none

/-- The tagged field model; `less` determines which field-order tests are available. -/
abbrev model (K : Type*) [Field K] [DecidableEq K] (less : K → K → Option Bool) : Model where
  Value := ℕ ⊕ K
  Address := ℕ
  Config := ℕ
  Const := Const
  operations := operations
  tests := tests
  constant _ := constant
  evalOp w op xs :=
    if ∀ i, admissible w (xs i) = true then evalOp op xs else none
  evalTest w t xs :=
    if ∀ i, admissible w (xs i) = true then evalTest less t xs else none
  admissible := admissible
  address := address
  validMove := admissible
  validPC w pc := decide (pc < 2 ^ w)

/-- Exact real RAM semantics, with decidable equality/order supplied classically. -/
noncomputable abbrev real : Model :=
  model ℝ (fun a b => some (decide (a < b)))

/-- An executable prime-field RAM. Its field-order test always faults. -/
abbrev primeField (p : ℕ) [Fact p.Prime] : Model :=
  model (ZMod p) (fun _ _ => none)

end Cslib.GenericRAM.Algebraic
