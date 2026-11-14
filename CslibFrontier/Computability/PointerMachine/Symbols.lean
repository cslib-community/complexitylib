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
# Symbols and integers

[Tarjan1979], §2, p. 112 calls *symbols* the data on which no operation is permitted except
testing for equality. This data basis combines symbols with integers, as in the weighted-union
representation of §3, pp. 114–115: arithmetic and order apply to integers only, and no
primitive produces a symbol or converts between symbols and integers.

## Main definitions

* `model`: symbols with equality; integers with addition, subtraction and order.
* `symbolRenaming`: every permutation of the symbols is a renaming of the model.

## Main results

* `hasSymbol_of_runs`: execution cannot introduce a symbol absent from the initial state.
-/

@[expose] public section

namespace Cslib.PointerMachine.Symbols

/-- A datum is undefined, a symbol or an integer. -/
inductive Value (Symbol : Type) where
  /-- The undefined value. -/
  | undefined
  /-- A symbol. -/
  | symbol (a : Symbol)
  /-- An integer. -/
  | int (n : ℤ)
  deriving DecidableEq

/-- Integer operations. -/
inductive Op where
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub

/-- Predicates. -/
inductive Test where
  /-- Equality of any two data. -/
  | eq
  /-- Strict order of integers. -/
  | less

variable {Symbol : Type}

/-- Arithmetic on integers; the result is undefined for any other operands. -/
def evalOp : Op → Value Symbol → Value Symbol → Value Symbol
  | .add, .int m, .int n => .int (m + n)
  | .sub, .int m, .int n => .int (m - n)
  | _, _, _ => .undefined

/-- Equality of data and order of integers; order is false for any other operands. -/
def evalTest [DecidableEq Symbol] : Test → Value Symbol → Value Symbol → Bool
  | .eq, a, b => a = b
  | .less, .int m, .int n => m < n
  | .less, _, _ => false

/-- Symbols with equality and integers with addition, subtraction and order. Each primitive
costs one unit whatever the size of the integers. -/
abbrev model (Symbol : Type) [DecidableEq Symbol] : Model where
  Value := Value Symbol
  undefined := .undefined
  Op := Op
  Test := Test
  evalOp := evalOp
  evalTest := evalTest

/-- Require a property of symbols, leaving other data unrestricted. -/
def predicate (A : Symbol → Prop) : Value Symbol → Prop
  | .symbol a => A a
  | _ => True

variable [DecidableEq Symbol]

/-- The primitives preserve every property of symbols: they produce no symbol. -/
theorem closed (A : Symbol → Prop) : (model Symbol).Closed (predicate A) := by
  refine ⟨trivial, fun o a b _ _ => ?_⟩
  cases o <;> cases a <;> cases b <;> trivial

/-- A symbol occurs in a data register or in a record. -/
def HasSymbol {L : Layout} (x : State (model Symbol) L) (a : Symbol) : Prop :=
  (∃ s, x.data s = .symbol a) ∨ ∃ n ∈ x.heap, ∃ f, n.data f = .symbol a

/-- Every symbol in a register or record after a run was already in one before it. -/
theorem hasSymbol_of_runs {L : Layout} {code : List (Instr (model Symbol) L)}
    {x y : State (model Symbol) L} {n : ℕ} (h : Runs code x y n) {a : Symbol}
    (ha : HasSymbol y a) : HasSymbol x a := by
  have hx : x.DataValid (predicate (HasSymbol x)) := by
    refine ⟨fun s => ?_, fun n hn f => ?_⟩
    · cases hv : x.data s <;> first | trivial | exact .inl ⟨s, hv⟩
    · cases hv : n.data f <;> first | trivial | exact .inr ⟨n, hn, f, hv⟩
  have hy := h.dataValid (closed (HasSymbol x)) hx
  rcases ha with ⟨s, hs⟩ | ⟨n, hn, f, hf⟩
  · simpa [hs, predicate] using hy.1 s
  · simpa [hf, predicate] using hy.2 n hn f

/-- Apply a permutation to the symbols. -/
def Value.map (π : Symbol → Symbol) : Value Symbol → Value Symbol
  | .symbol a => .symbol (π a)
  | v => v

/-- Every permutation of the symbols is a renaming: no primitive can tell symbols apart
except by equality. -/
def symbolRenaming (π : Equiv.Perm Symbol) : (model Symbol).Renaming where
  value := {
    toFun := Value.map π
    invFun := Value.map π.symm
    left_inv := by rintro (_ | _ | _) <;> simp [Value.map]
    right_inv := by rintro (_ | _ | _) <;> simp [Value.map] }
  undefined := rfl
  op := by rintro (_ | _) (_ | _ | _) (_ | _ | _) <;> rfl
  test := by
    rintro (_ | _) (_ | _ | _) (_ | _ | _) <;> simp [evalTest, Value.map]

end Cslib.PointerMachine.Symbols
