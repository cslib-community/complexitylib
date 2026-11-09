/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Positive-arity Boolean clones

A clone contains every coordinate projection and is closed under superposition. Nullary
operations are excluded; constant functions of positive arity are allowed. This is the common
algebraic interface for the Boolean Schaefer classification and Post's completeness criterion.

## Main definitions

* `Cslib.Logic.BooleanClone`: positive-arity Boolean clones.

## Main results

* `Cslib.Logic.BooleanClone.minor`: variable identification, permutation and dummy variables.
* `Cslib.Logic.BooleanClone.diagonal`: identifying every argument gives a unary operation.
-/

public section

namespace Cslib.Logic

/-- A clone of positive-arity Boolean operations. Nullary operations are excluded. -/
structure BooleanClone where
  /-- Operations of each arity. -/
  operations : (n : ℕ) → Set ((Fin n → Bool) → Bool)
  /-- There are no nullary operations. -/
  nullary : operations 0 = ∅
  /-- Every coordinate projection belongs to the clone. -/
  projection {n : ℕ} (i : Fin n) : (fun a => a i) ∈ operations n
  /-- Superposition of positive-arity operations belongs to the clone. -/
  comp {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {f : (Fin m → Bool) → Bool} {g : Fin m → (Fin n → Bool) → Bool}
    (hf : f ∈ operations m) (hg : ∀ i, g i ∈ operations n) :
    (fun a => f (fun i => g i a)) ∈ operations n

namespace BooleanClone

/-- AND as a binary operation. -/
@[expose] def andOp (a : Fin 2 → Bool) : Bool := a 0 && a 1

/-- OR as a binary operation. -/
@[expose] def orOp (a : Fin 2 → Bool) : Bool := a 0 || a 1

variable (C : BooleanClone)

/-- Identifying, permuting or adding dummy variables preserves clone membership. -/
theorem minor {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {f : (Fin m → Bool) → Bool} (hf : f ∈ C.operations m) (p : Fin m → Fin n) :
    (fun a => f (a ∘ p)) ∈ C.operations n :=
  C.comp hm hn hf (fun i => C.projection (p i))

/-- Applying an operation to a constant tuple gives a unary operation in the clone. -/
theorem diagonal {n : ℕ} (hn : 0 < n) {f : (Fin n → Bool) → Bool}
    (hf : f ∈ C.operations n) :
    (fun a : Fin 1 → Bool => f (fun _ => a 0)) ∈ C.operations 1 :=
  C.minor hn (by decide) hf (fun _ => 0)

/-- Every operation in a positive-arity clone has positive arity. -/
theorem arity_pos {n : ℕ} {f : (Fin n → Bool) → Bool} (hf : f ∈ C.operations n) : 0 < n := by
  cases n with
  | zero => simp only [C.nullary, Set.mem_empty_iff_false] at hf
  | succ n => exact Nat.succ_pos n

/-- A binary Boolean operation specified by its four truth-table entries. -/
@[expose] def binaryTable (b00 b01 b10 b11 : Bool) (a : Fin 2 → Bool) : Bool :=
  if a 0 then if a 1 then b11 else b10 else if a 1 then b01 else b00

/-- A binary operation is determined by its four truth-table entries. -/
theorem binaryTable_eq (f : (Fin 2 → Bool) → Bool) :
    f = binaryTable (f ![false, false]) (f ![false, true])
      (f ![true, false]) (f ![true, true]) := by
  funext a
  have ha : a = ![a 0, a 1] := by ext i; fin_cases i <;> rfl
  conv_lhs => rw [ha]
  cases h₀ : a 0 <;> cases h₁ : a 1 <;> simp [binaryTable, h₀, h₁]

end BooleanClone
end Cslib.Logic
