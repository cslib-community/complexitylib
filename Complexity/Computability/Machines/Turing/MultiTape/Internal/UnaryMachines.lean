/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-! # Shared unary machine constructors

The finite-state successor machine is shared by direct Degree and polynomial-time providers.
Extracted unchanged from the direct list provider by worker `/root/review_560`.
-/

@[expose] public section
namespace Turing.MultiTapeTM.Internal.Unary

/-- Prefix a unary symbol, including on empty input. -/
def unarySuccTransducer : Transducer Bool Bool where
  q₀ := true
  step q bit := (false, if q then [true, bit] else [bit])
  final q := if q then [true] else []
  length_step_le q bit := by cases q <;> simp
  length_final_le q := by cases q <;> simp

/-- The successor transducer prefixes once, then copies every remaining symbol. -/
theorem unarySuccRun (word : List Bool) :
    unarySuccTransducer.run true word = true :: word ∧
      unarySuccTransducer.run false word = word := by
  induction word with
  | nil => constructor <;> rfl
  | cons bit word ih =>
    constructor
    · change [true, bit] ++ unarySuccTransducer.run false word = true :: bit :: word
      rw [ih.2]
      rfl
    · change [bit] ++ unarySuccTransducer.run false word = bit :: word
      rw [ih.2]
      rfl

end Turing.MultiTapeTM.Internal.Unary
