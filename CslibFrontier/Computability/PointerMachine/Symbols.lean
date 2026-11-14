/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PointerMachine.Data
public import CslibFrontier.Computability.PointerMachine.Renaming

/-!
# Protected symbols and integer metadata

This two-sort basis combines equality-only symbols with integer arithmetic. Sort `0` carries
symbols and sort `1` carries integers. Arithmetic operations and predicates have integer operands
only; the machine's built-in typed equality test can compare symbols. The signature contains no
symbol constants, symbol-producing primitives, packing operations, or symbol-to-integer conversion.

The distinction follows [Tarjan1979], section 2, p. 112. The weighted-union representation in
section 3, pp. 114–115 combines symbol identities, integer sizes, and parent pointers. This module
provides the data basis and opacity results, not the union-find algorithm or its lower bound.

## Main definitions

* `model`: protected symbols and integer addition, subtraction, and comparison.
* `predicate`, `closed`: any predicate on symbols is preserved by the primitive basis.
* `symbolRenaming`: every permutation of symbols preserves the basis and fixes integer data.

## Main results

* `hasSymbol_of_runs`: execution cannot introduce a symbol absent from the initial state.
-/

public section

namespace Cslib.PointerMachine.Symbols

/-- Sort `0` contains symbols; sort `1` contains integer metadata. -/
abbrev Value (Symbol : Type) : Fin 2 → Type :=
  fun t => match t with
    | ⟨0, _⟩ => Symbol
    | ⟨_ + 1, _⟩ => Int

/-- Arithmetic symbols operate only on integer data. -/
inductive Op : Fin 2 → Fin 2 → Fin 2 → Type where
  /-- Integer addition. -/
  | add : Op 1 1 1
  /-- Integer subtraction. -/
  | sub : Op 1 1 1

/-- The only extra predicate is integer comparison; typed equality is a machine instruction. -/
inductive Test : Fin 2 → Fin 2 → Type where
  /-- Strict integer order. -/
  | less : Test 1 1

/-- A mixed basis with arbitrary equality-only symbols and unbounded integer metadata.
The instruction semantics assigns one abstract unit to each primitive, not a bit-cost bound. -/
abbrev model (Symbol : Type) [DecidableEq Symbol] : Model 2 where
  Value := Value Symbol
  decValue := Fin.cases (inferInstanceAs (DecidableEq Symbol))
    (fun _ => inferInstanceAs (DecidableEq Int))
  Op := Op
  Test := Test
  evalOp := fun f => match f with
    | .add => fun (x y : Int) => some (Int.add x y)
    | .sub => fun (x y : Int) => some (Int.sub x y)
  evalTest := fun f => match f with
    | .less => fun (x y : Int) => some (decide (x < y))

variable {Symbol : Type} [DecidableEq Symbol]

/-- Require a property of symbols, leaving integer data unrestricted. -/
@[expose] def predicate (A : Symbol → Prop) : (t : Fin 2) → Value Symbol t → Prop :=
  Fin.cases A (fun _ => fun _ => True)

/-- The basis preserves every symbol predicate: it cannot manufacture or transform symbols. -/
theorem closed (A : Symbol → Prop) : (model Symbol).Closed (predicate A) := by
  intro a b c f va vb v _ _ _
  cases f <;> exact True.intro

/-- A symbol occurs in a register or in an allocated record. Inaccessible heap contents do
not supply symbols to the machine. -/
@[expose] def HasSymbol {L : Layout 2} (x : State (model Symbol) L) (v : Symbol) : Prop :=
  (∃ i, x.data 0 i = some v) ∨
  (∃ a, x.Allocated a ∧ ∃ f, (x.heap a).data 0 f = some v)

private theorem dataValid_hasSymbol {L : Layout 2} (x : State (model Symbol) L) :
    x.DataValid (predicate (HasSymbol x)) := by
  constructor
  · intro t
    refine Fin.cases ?_ (fun _ => ?_) t
    · intro i v hv
      exact Or.inl ⟨i, hv⟩
    · intro _ _ _
      exact True.intro
  · intro a ha t
    refine Fin.cases ?_ (fun _ => ?_) t
    · intro f v hv
      exact Or.inr ⟨a, ha, f, hv⟩
    · intro _ _ _
      exact True.intro

/-- Every symbol in a run's final registers or allocated heap was already present initially.
This follows from the generic data-invariant theorem, independently of numeric computations. -/
theorem hasSymbol_of_runs {L : Layout 2} {code : List (Instr (model Symbol) L)}
    {x y : State (model Symbol) L} {n : ℕ} (h : Runs code x y n) {v : Symbol}
    (hv : HasSymbol y v) : HasSymbol x v := by
  have hy := h.dataValid (closed (HasSymbol x)) (dataValid_hasSymbol x)
  rcases hv with ⟨i, hi⟩ | ⟨a, ha, f, hf⟩
  · exact hy.1 0 i v hi
  · exact hy.2 a ha 0 f v hf

/-- Every symbol permutation is a symmetry of this basis; integer values are fixed. -/
@[expose] def symbolRenaming (π : Equiv.Perm Symbol) : (model Symbol).Renaming where
  value := Fin.cases π (fun _ => Equiv.refl Int)
  operation := by
    intro a b c f va vb
    cases f <;> rfl
  test := by
    intro a b f va vb
    cases f
    rfl

end Cslib.PointerMachine.Symbols
