/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.VOLE.NativeCircuit.Basic
public import Complexity.Crypto.Protocols.VOLE.NativePPT

/-!
# Encodings for native circuit sessions

The private-input count is unary. The public circuit uses the existing gate/output encoding with
binary indices; all public field lists, auxiliary bits and retained receiver results are charged.
The scalar carrier and its encoding are fixed, while every circuit and list is runtime input.

## Main definitions

* `NativeCircuit.encInput`: the complete public runtime input.
* `NativeCircuit.encFirst`, `NativeCircuit.encView`: transmitted frames and complete receiver view.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE.NativeCircuit

open Circuits Turing.MultiTapeTM

variable {F Result : Type}

/-- Unary witness count, existing circuit code, public input/output lists and auxiliary bits. -/
def encInput (eF : F ↪ List Bool) : Input F ↪ List Bool :=
  encPair encUnary (encPair (Circuit.encCode (ArithOp.encoding eF))
    (encPair (encList eF) (encPair (encList eF) encBits)))

/-- Both sender vectors are explicitly charged, including the last fresh mask coordinate. -/
def encSenderShare (eF : F ↪ List Bool) : SenderShare F ↪ List Bool :=
  encPair (encList eF) (encList eF)

/-- Every correction and linear opening is included in the frame encoding. -/
def encFirst (eF : F ↪ List Bool) : First F ↪ List Bool :=
  encPair (encList eF) (encList eF)

/-- Full receiver share, both first-message lists, normalized weights, reply and private result. -/
def encView (eF : F ↪ List Bool) (eResult : Result ↪ List Bool) :
    View F Result ↪ List Bool :=
  encPair (Native.encShare eF) (encPair (encFirst eF)
    (encPair (encList eF) (encPair (encPair eF eF) eResult)))

end Cslib.Crypto.Protocols.VOLE.NativeCircuit
