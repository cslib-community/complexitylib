/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.Falcon.VerificationFrontend
import CslibFrontier.Crypto.Primitives.Hash.Keccak
meta import CslibFrontier.Crypto.Computational.Falcon.VerificationFrontend
meta import CslibFrontier.Crypto.Primitives.Hash.Keccak

/-!
# Tests for Keccak-p[1600, 24] and SHAKE256

The SHAKE outputs below are the first 64 bytes of NIST's official 0-bit and 1600-bit-message
SHAKE256 examples. The latter message is 200 repetitions of byte `A3`, so absorption crosses the
136-byte SHAKE256 rate boundary. The 137-byte empty-message check crosses the first output block.

The Falcon fixture is `salt || message` from `falcon512-KAT.rsp`, `count = 0`, in the official
Falcon Round 3 v1.2 archive. Its 20-byte output is the prefix consumed by the checked fixture in
`CslibFrontierTests.Crypto.Falcon`.
-/

-- This is an ordinary import client of the public Keccak API, not a private test module.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.Keccak

open Cslib Cslib.Crypto Cslib.Crypto.Keccak

set_option linter.hashCommand false

/-! ### State and byte conventions -/

#guard roundConstants.length == 24
#guard rotationOffset 1 0 == 1
#guard rotationOffset 0 2 == 3
#guard rotationOffset 4 4 == 14

#guard byteBitsLE 0xA3 == [true, true, false, false, false, true, false, true]
#guard bitsToByteLE [true, true, false, false, false, true, false, true] == 0xA3

/-- The empty-message SHAKE suffix and padding form bytes `1F 00 ... 00 80` in the rate block,
as in NIST's official 0-bit example. -/
private def emptyPaddedRate : BitString 1088 :=
  fun i => decide (i.val < 5 ∨ i.val = 1087)

private def emptyPaddedState : State :=
  ofSpongeState (emptyPaddedRate, (0 : BitString 512))

#guard (getLane emptyPaddedState 0 0).toNat == 0x1F
#guard (getLane emptyPaddedState 1 3).toNat == 0x8000000000000000

/-! ### Official NIST SHAKE256 examples -/

private def emptyOutput64 : List (Fin 256) :=
  [0x46, 0xB9, 0xDD, 0x2B, 0x0B, 0xA8, 0x8D, 0x13, 0x23, 0x3B, 0x3F, 0xEB, 0x74, 0x3E,
    0xEB, 0x24, 0x3F, 0xCD, 0x52, 0xEA, 0x62, 0xB8, 0x1B, 0x82, 0xB5, 0x0C, 0x27, 0x64,
    0x6E, 0xD5, 0x76, 0x2F, 0xD7, 0x5D, 0xC4, 0xDD, 0xD8, 0xC0, 0xF2, 0x00, 0xCB, 0x05,
    0x01, 0x9D, 0x67, 0xB5, 0x92, 0xF6, 0xFC, 0x82, 0x1C, 0x49, 0x47, 0x9A, 0xB4, 0x86,
    0x40, 0x29, 0x2E, 0xAC, 0xB3, 0xB7, 0xC4, 0xBE]

private def message1600Output64 : List (Fin 256) :=
  [0xCD, 0x8A, 0x92, 0x0E, 0xD1, 0x41, 0xAA, 0x04, 0x07, 0xA2, 0x2D, 0x59, 0x28, 0x86,
    0x52, 0xE9, 0xD9, 0xF1, 0xA7, 0xEE, 0x0C, 0x1E, 0x7C, 0x1C, 0xA6, 0x99, 0x42, 0x4D,
    0xA8, 0x4A, 0x90, 0x4D, 0x2D, 0x70, 0x0C, 0xAA, 0xE7, 0x39, 0x6E, 0xCE, 0x96, 0x60,
    0x44, 0x40, 0x57, 0x7D, 0xA4, 0xF3, 0xAA, 0x22, 0xAE, 0xB8, 0x85, 0x7F, 0x96, 0x1C,
    0x4C, 0xD8, 0xE0, 0x6F, 0x0A, 0xE6, 0x61, 0x0B]

#guard shake256 [] 0 == []
#guard shake256 [] 64 == emptyOutput64
#guard shake256 (List.replicate 200 0xA3) 64 == message1600Output64

-- Output lengths do not change the existing XOF prefix.
#guard shake256 [] 32 == (shake256 [] 64).take 32

-- Byte 136 is the first byte after the initial 136-byte squeezing block in NIST's 0-bit sample.
#guard (shake256 [] 137).getD 136 0 == 0x94

/-! ### Public API clients -/

example (byte : Fin 256) : bitsToByteLE (byteBitsLE byte) = byte :=
  bitsToByteLE_byteBitsLE byte

example (bits : List Bool) (h : bits.length = 8) : byteBitsLE (bitsToByteLE bits) = bits :=
  byteBitsLE_bitsToByteLE bits h

example (state : SpongeState) : toSpongeState (ofSpongeState state) = state :=
  toSpongeState_ofSpongeState state

example (A : State) : ofSpongeState (toSpongeState A) = A :=
  ofSpongeState_toSpongeState A

example (input : List (Fin 256)) {m n : ℕ} (h : m ≤ n) :
    (shake256 input n).take m = shake256 input m :=
  take_shake256 input h

/-! ### Falcon Round 3 v1.2 KAT fixture -/

private def falconSalt : List (Fin 256) :=
  [0x33, 0xB3, 0xC0, 0x75, 0x07, 0xE4, 0x20, 0x17, 0x48, 0x49, 0x4D, 0x83, 0x2B, 0x6E,
    0xE2, 0xA6, 0xC9, 0x3B, 0xFF, 0x9B, 0x0E, 0xE3, 0x43, 0xB5, 0x50, 0xD1, 0xF8, 0x5A,
    0x3D, 0x0D, 0xE0, 0xD7, 0x04, 0xC6, 0xD1, 0x78, 0x42, 0x95, 0x13, 0x09]

private def falconMessage : List (Fin 256) :=
  [0xD8, 0x1C, 0x4D, 0x8D, 0x73, 0x4F, 0xCB, 0xFB, 0xEA, 0xDE, 0x3D, 0x3F, 0x8A, 0x03,
    0x9F, 0xAA, 0x2A, 0x2C, 0x99, 0x57, 0xE8, 0x35, 0xAD, 0x55, 0xB2, 0x2E, 0x75, 0xBF,
    0x57, 0xBB, 0x55, 0x6A, 0xC8]

private def falconOutput20 : List (Fin 256) :=
  [0x16, 0xE0, 0x55, 0xC9, 0x01, 0x62, 0xB5, 0xFA, 0x1D, 0x15,
    0xA8, 0x8E, 0x88, 0xE0, 0xE1, 0x90, 0x00, 0x55, 0x6F, 0x02]

#guard shake256 (falconSalt ++ falconMessage) 20 == falconOutput20

-- The concrete SHAKE prefix crosses the frontend boundary and yields the KAT-derived point prefix.
#guard Falcon.hashToPointCoefficients 12289 10 (shake256 (falconSalt ++ falconMessage) 20) ==
  some [5856, 9672, 354, 9719, 7445, 6283, 10462, 8588, 85, 3840]

end CslibFrontierTests.Crypto.Keccak
