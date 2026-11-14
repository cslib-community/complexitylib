/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128
meta import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128

/-!
# Tests for SHAKE128

The empty-message output is the first 32 bytes of NIST's official SHAKE128 0-bit-message example.
The prefix client checks the XOF contract independently of that fixed vector.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SHAKE128

open Cslib.Crypto.Keccak

set_option linter.hashCommand false

private def emptyOutput32 : List (Fin 256) :=
  [0x7F, 0x9C, 0x2B, 0xA4, 0xE8, 0x8F, 0x82, 0x7D,
    0x61, 0x60, 0x45, 0x50, 0x76, 0x05, 0x85, 0x3E,
    0xD7, 0x3B, 0x80, 0x93, 0xF6, 0xEF, 0xBC, 0x88,
    0xEB, 0x1A, 0x6E, 0xAC, 0xFA, 0x66, 0xEF, 0x26]

#guard shake128 [] 0 == []
#guard shake128 [] 32 == emptyOutput32
#guard (shake128 [] 64).take 32 == emptyOutput32

example (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake128 input n).take m = shake128 input m :=
  take_shake128 input h

end CslibFrontierTests.Crypto.SHAKE128
