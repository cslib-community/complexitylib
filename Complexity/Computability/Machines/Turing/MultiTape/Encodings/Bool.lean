/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Complexity.Init
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Data.List.Basic
public import Mathlib.Logic.Embedding.Basic

/-!
# Encodings of Booleans, signs and the unit type

`Turing.MultiTapeTM.encBool` encodes a Boolean by one symbol, `Turing.MultiTapeTM.encSign` a sign,
such as a head move, by at most one symbol, and `Turing.MultiTapeTM.encUnit` the unit by the empty
word.
-/

namespace Turing.MultiTapeTM

/-- The encoding `b ↦ [b]` of `Bool`. -/
@[expose] public def encBool : Bool ↪ List Bool :=
  ⟨fun b => [b], fun _ _ h => List.head_eq_of_cons_eq h⟩

@[simp]
public lemma encBool_apply (b : Bool) : encBool b = [b] := rfl

/-- Signs: `0 ↦ []`, `-1 ↦ [false]` and `1 ↦ [true]`. -/
@[expose] public def encSign : SignType ↪ List Bool :=
  ⟨fun m => match m with | .zero => [] | .neg => [false] | .pos => [true], by
    intro a b h
    cases a <;> cases b <;> simp_all⟩

/-- The unit type, encoded by the empty word. -/
@[expose] public def encUnit : Unit ↪ List Bool := ⟨fun _ => [], fun _ _ _ => rfl⟩

@[simp]
public lemma encUnit_apply (u : Unit) : encUnit u = [] := rfl

end Turing.MultiTapeTM
