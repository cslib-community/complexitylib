/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Tactic.FunProp
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.Id

/-!
# Polynomial time on multi-tape machines

`Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut`: some machine with a binary alphabet and
finitely many states computes `f` in the sense of `Turing.MultiTapeTM.ComputableInTimeAndSpace`,
within time and space bounded by polynomially bounded functions of the length of the encoded input
[Arora and Barak, Chapter 1][AroraBarak09]. Time and space are independent bounds, as in
`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`; that a polynomial time bound already bounds
the space is a lemma about machines, not part of the definition.

The predicate is registered with `fun_prop`. It is a one-field structure rather than a definition,
so a failed unification between two instances, such as `fun_prop` trying a rule stated for other
encodings, stops at the predicate instead of unfolding the machine semantics and the encodings.
This file proves the closure rules that need no machine construction beyond upstream's: the
identity, constants, functions on finite types and changes of representation.

## Main definitions

* `Turing.MultiTapeTM.ComputableInPolyTime`: computability in polynomial time.

## Main results

* `Turing.MultiTapeTM.computableInPolyTime_def`: the unfolding of the predicate.
* `Turing.MultiTapeTM.ComputableInPolyTime.of_eq`, `Turing.MultiTapeTM.ComputableInPolyTime.id'`:
  functions that do not change the encoded word.
* `Turing.MultiTapeTM.ComputableInPolyTime.const`,
  `Turing.MultiTapeTM.ComputableInPolyTime.of_finite`: constant functions and functions on finite
  types.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Turing.MultiTapeTM

open Cslib

/-- `f` is computable in polynomial time: some machine with a binary alphabet and finitely many
states computes `f`, relative to the encodings `encIn` and `encOut`, within time and space
bounded by polynomially bounded functions of the length of the encoded input.

The predicate is a one-field structure, as Mathlib's `Continuous` is, so that unification never
unfolds it to the machine semantics when two instances fail to match syntactically (as happens
when `fun_prop` tries a rule stated for other encodings). Anonymous constructors and patterns
`⟨t, s, ht, hs, h⟩` build and destructure it as they would the existential;
`Turing.MultiTapeTM.computableInPolyTime_def` states the unfolding. -/
structure ComputableInPolyTime {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) : Prop where
  /-- Polynomially bounded time and space bounds and a machine computing `f` within them. -/
  exists_bounds : ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
    ComputableInTimeAndSpaceOfLength f encIn encOut t s

/-- The unfolding of `Turing.MultiTapeTM.ComputableInPolyTime`. -/
theorem computableInPolyTime_def {α β : Type*} {f : α → β} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} :
    ComputableInPolyTime f encIn encOut ↔ ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧
      PolynomiallyBounded s ∧ ComputableInTimeAndSpaceOfLength f encIn encOut t s :=
  ⟨fun h => h.exists_bounds, fun h => ⟨h⟩⟩

namespace ComputableInPolyTime

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- A function whose encoded values are its encoded arguments is computable in polynomial time:
the machine copies its input. -/
theorem of_eq {f : α → β} (h : ∀ a, encOut (f a) = encIn a) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨k, State, hfinite, tm, htm⟩ := computableInTimeAndSpace_id (enc := encIn)
  refine ⟨fun n => n + 1, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨1, 1, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, k, State, hfinite, tm, fun a => ?_⟩
  rw [h a]
  exact htm a

/-- Every function on a finite type is computable in polynomial time, by a lookup machine. -/
theorem of_finite [Finite α] (f : α → β) : ComputableInPolyTime f encIn encOut :=
  let ⟨c, h⟩ := computableInTimeAndSpace_of_finite (encIn := encIn) (encOut := encOut) f
  ⟨fun _ => c, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨c, 0, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, h⟩

/-! ### Automation -/

attribute [fun_prop] ComputableInPolyTime

@[fun_prop]
theorem id' : ComputableInPolyTime (fun a : α => a) encIn encIn :=
  of_eq fun _ => rfl

@[fun_prop]
theorem const (b : β) : ComputableInPolyTime (fun _ : α => b) encIn encOut :=
  let ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encOut) b
  ⟨fun _ => c, fun _ => 0, polynomiallyBounded_iff_le.mpr ⟨c, 0, fun _ => by simp⟩,
    polynomiallyBounded_iff_le.mpr ⟨0, 0, fun _ => le_rfl⟩, h⟩

end ComputableInPolyTime

end Turing.MultiTapeTM
