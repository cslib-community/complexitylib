/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Encoding arithmetic operations

The existing arithmetic operations are a Boolean choice of addition or multiplication, or a
constant from the supplied carrier. Constants retain their supplied encoding.

## Main definitions

* `ArithOp.equivSum`: the existing operations as `Bool ⊕ F`.
* `ArithOp.encoding`: the corresponding tagged encoding.

No new circuit or field representation is introduced.
-/

@[expose] public section

namespace Cslib.Circuits.ArithOp

variable {F : Type*}

/-- Addition and multiplication are the two Boolean tags; constants carry their value. -/
def equivSum : ArithOp F ≃ Bool ⊕ F where
  toFun
    | .add => .inl false
    | .mul => .inl true
    | .const c => .inr c
  invFun
    | .inl false => .add
    | .inl true => .mul
    | .inr c => .const c
  left_inv op := by cases op <;> rfl
  right_inv op := by rcases op with (_ | _) | _ <;> rfl

instance [Finite F] : Finite (ArithOp F) :=
  Finite.of_equiv (Bool ⊕ F) equivSum.symm

/-- A sum tag, followed by the operation bit or encoded constant. -/
def encoding (eF : F ↪ List Bool) : ArithOp F ↪ List Bool :=
  equivSum.toEmbedding.trans (Turing.MultiTapeTM.encSum Turing.MultiTapeTM.encBool eF)

end Cslib.Circuits.ArithOp
