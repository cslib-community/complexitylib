/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.Boolean.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Rat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum

/-!
# Encoding arithmetic operations and rational arithmetic circuits

The existing arithmetic operations are a Boolean choice of addition or multiplication, or a
constant from the supplied carrier. Constants retain their supplied encoding. We also provide
binary encodings of rational arithmetic circuits and circuit-input pairs over
`Turing.MultiTapeTM.encRat`.

## Main definitions

* `Cslib.Circuits.ArithOp.equivSum`: the existing operations as `Bool ⊕ F`.
* `Cslib.Circuits.ArithOp.encoding`: the corresponding tagged encoding.
* `Cslib.Circuits.encRatArithCircuit`: binary encoding of rational arithmetic circuits.
* `Cslib.Circuits.encRatArithCircuitInput`: binary encoding of rational arithmetic circuit-input
  pairs.

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

namespace Cslib.Circuits

/-- Binary encoding of rational arithmetic circuits with `m` outputs over
`Turing.MultiTapeTM.encRat`. -/
abbrev encRatArithCircuit (m : ℕ) :
    (Σ n, Circuit (arithSignature ℚ) n m) ↪ List Bool :=
  Circuit.encCircuit (ArithOp.encoding Turing.MultiTapeTM.encRat) m

/-- Binary encoding of `(C, x)` pairs for rational arithmetic circuits with `m` outputs and
rational input vectors `x : List ℚ`. -/
abbrev encRatArithCircuitInput (m : ℕ) :
    (Σ n, Circuit (arithSignature ℚ) n m) × List ℚ ↪ List Bool :=
  Turing.MultiTapeTM.encPair (encRatArithCircuit m)
    (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encRat)

end Cslib.Circuits
