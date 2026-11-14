/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128
meta import CslibFrontier.Crypto.Primitives.Hash.Keccak.SHAKE128

/-!
# Tests for SHAKE128

The fixed outputs come from NIST's official SHAKE128 0-bit- and 1600-bit-message examples. The
empty-message client also crosses the 168-byte rate boundary, while the theorem client checks the
general XOF prefix contract.
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

private def message1600Output32 : List (Fin 256) :=
  [0x13, 0x1A, 0xB8, 0xD2, 0xB5, 0x94, 0x94, 0x6B,
    0x9C, 0x81, 0x33, 0x3F, 0x9B, 0xB6, 0xE0, 0xCE,
    0x75, 0xC3, 0xB9, 0x31, 0x04, 0xFA, 0x34, 0x69,
    0xD3, 0x91, 0x74, 0x57, 0x38, 0x5D, 0xA0, 0x37]

private def emptyOutputAcrossRateBoundary : List (Fin 256) :=
  [0xAE, 0xE7, 0xEE, 0xF4, 0x7C, 0xB0, 0xFC, 0xA9, 0x76]

#guard shake128 [] 0 == []
#guard shake128 [] 32 == emptyOutput32
#guard (shake128 [] 64).take 32 == emptyOutput32

-- NIST's 1600-bit message consists of 200 repetitions of byte 0xA3.
#guard shake128 (List.replicate 200 0xA3) 32 == message1600Output32

-- Bytes 160--168 of the official empty-message output cross the 168-byte rate boundary.
#guard (shake128 [] 169).drop 160 == emptyOutputAcrossRateBoundary

example (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake128 input n).take m = shake128 input m :=
  take_shake128 input h

end CslibFrontierTests.Crypto.SHAKE128
