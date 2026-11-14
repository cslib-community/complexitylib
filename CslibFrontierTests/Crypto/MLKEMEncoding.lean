/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.MLKEM.SeedExpansion
meta import CslibFrontier.Crypto.Computational.SIS.MLKEM.SeedExpansion

/-!
# Tests for ML-KEM byte encoding and seed expansion

These clients pin the convention-sensitive boundaries of FIPS 203 Algorithms 5–7 and 13:
least-significant-bit-first coefficient packing, the noncanonical 12-bit range, SampleNTT's nibble
split, and the `rho || j || i` matrix suffix. They do not claim complete K-PKE serialization or
security.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MLKEMEncoding

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM

set_option linter.hashCommand false

private def coefficients10 : Coefficients width10 := fun i =>
  if i.val = 0 then 1 else if i.val = 1 then 2 else 0

-- Coefficients 1 and 2 occupy bits 0 and 11, crossing the first byte boundary at width 10.
#guard (byteEncode width10 coefficients10).toList.take 3 == [0x01, 0x08, 0x00]
#guard decide (byteDecode width10 (byteEncode width10 coefficients10) = coefficients10)

example : byteDecode width10 (byteEncode width10 coefficients10) = coefficients10 :=
  byteDecode_byteEncode width10 coefficients10

private def upperCanonical12 : Coefficients width12 := fun i =>
  if i.val = 0 then 3328 else 0

-- The largest canonical coefficient is the little-endian 12-bit value 0xD00.
#guard (byteEncode width12 upperCanonical12).toList.take 3 == [0x00, 0x0D, 0x00]
#guard decide (IsCanonical width12 (byteEncode width12 upperCanonical12))

private def noncanonical12 : EncodedBytes width12 := fun i =>
  if i.val = 0 then 0x01 else if i.val = 1 then 0x0D else 0

-- The first raw field is 0xD01 = 3329, which ByteDecode_12 reduces to zero.
#guard (byteDecode width12 noncanonical12 0).val == 0
#guard decide (¬ IsCanonical width12 noncanonical12)
#guard (byteEncode width12 (byteDecode width12 noncanonical12)).toList.take 3 == [0, 0, 0]

private def zeroSeed : Seed32 := fun _ => 0

#guard (matrixXofInput zeroSeed 1 2).toList.length == 34
#guard (matrixXofInput zeroSeed 1 2).toList.drop 32 == [2, 1]
#guard (matrixXofInput zeroSeed 1 2).toList != (matrixXofInput zeroSeed 2 1).toList

#guard (prfInput zeroSeed 7).toList.length == 33
#guard (prf eta2 zeroSeed 7).length == 128
#guard (prf eta3 zeroSeed 7).length == 192
#guard (prf eta3 zeroSeed 7).take 128 == prf eta2 zeroSeed 7

example : (prf eta3 zeroSeed 7).take 128 = prf eta2 zeroSeed 7 :=
  prf_two_eq_take_three zeroSeed 7

-- `[01, 0D, 00]` gives candidates 3329 and 0: the first is rejected and the second accepted.
#guard sampleNTTCandidates 0x01 0x0D 0x00 == (3329, 0)
#guard sampleNTTChunk 0x01 0x0D 0x00 == [0]

-- The middle byte's low nibble belongs to the first candidate and its high nibble to the second.
#guard sampleNTTCandidates 0x00 0x21 0x01 == (256, 18)
#guard sampleNTTChunk 0x00 0x21 0x01 == [256, 18]

-- Incomplete trailing input is ignored rather than treated as a total SampleNTT execution.
#guard sampleNTTPrefix [0x00, 0x21, 0x01, 0xFF] == [256, 18]

end CslibFrontierTests.Crypto.MLKEMEncoding
