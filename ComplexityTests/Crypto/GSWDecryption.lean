/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.Homomorphic.GSW.Decryption
import Complexity.Crypto.Computational.Homomorphic.GSW.Serialized

/-!
Raw GSW decryption regressions. The ciphertext rows below are chosen directly, without a key
generator, encryption coins or noise witness. Boundary residues check the decoder's half-open
convention; negative inner products check modular wraparound. These tests do not assert a
shallow circuit or bootstrappability.
-/

namespace ComplexityTests.GSWDecryption

open Cslib.Crypto.Homomorphic.GSW

private def rawCiphertext (w : ℕ) (a b : ZMod (2 ^ w)) : Ciphertext 1 w :=
  fun _ j => (if j.1 = 0 then a else b).val.testBit j.2.val

-- The selected row's recomposed entries are the chosen a,b, so its phase is a-b*t.
example : ([0, 1, 2, 3, 4, 5, 6, 7] : List (ZMod (2 ^ 3))).map
    (fun a => (decryptionPhase (fun _ => 0) (rawCiphertext 3 a 0) (0, 2)).val) =
      [0, 1, 2, 3, 4, 5, 6, 7] := by
  decide +kernel

example : ([0, 1, 2, 3, 4, 5, 6, 7] : List (ZMod (2 ^ 3))).map
    (fun a => decrypt (fun _ => 0) (rawCiphertext 3 a 0)) =
      [false, false, true, true, true, true, false, false] := by
  decide +kernel

-- The raw signed products -1 and -5 wrap to 7 and 3 modulo 8.
example : ([1, 5] : List (ZMod (2 ^ 3))).map
    (fun b => ((decryptionPhase (fun _ => 1) (rawCiphertext 3 0 b) (0, 2)).val,
      decrypt (fun _ => 1) (rawCiphertext 3 0 b))) = [(7, false), (3, true)] := by
  decide +kernel

example : ([0, 1] : List (ZMod (2 ^ 1))).map
    (fun a => decrypt (fun _ => 0) (rawCiphertext 1 a 0)) = [false, true] := by
  decide +kernel

example : decrypt (fun _ => 0) (rawCiphertext 0 0 0) = false := by
  decide +kernel

-- The row identity applies after separate total decoding of arbitrary input words.
example :
    decrypt (decodeSecret 1 3 [true, false, true])
      (decodeCiphertext 1 3 [false, true, true]) =
      decode 3 (decryptionPhase (decodeSecret 1 3 [true, false, true])
        (decodeCiphertext 1 3 [false, true, true]) (0, ⟨3 - 1, by omega⟩)) :=
  decrypt_eq_decode_decryptionPhase (by decide) _ _

-- At the lower boundary the two top bits differ; at the upper boundary they agree.
example : ((2 : ZMod (2 ^ 3)).val.testBit 2 ^^ (2 : ZMod (2 ^ 3)).val.testBit 1) = true ∧
    ((6 : ZMod (2 ^ 3)).val.testBit 2 ^^ (6 : ZMod (2 ^ 3)).val.testBit 1) = false := by
  decide +kernel

end ComplexityTests.GSWDecryption
