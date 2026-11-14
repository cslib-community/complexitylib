/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.Address
public meta import CslibFrontier.Crypto.Primitives.SLHDSA.Address

/-! Checked layouts and serialization clients for the FIPS 205 SLH-DSA address system. -/

public section

namespace SLHDSAAddressTests

open Cslib.BitString Cslib.Crypto Cslib.Crypto.SLHDSA

set_option linter.hashCommand false

def sampleWOTSHash : Address := Address.wotsHash 1 2 3 4 5

example : sampleWOTSHash.WellFormed := by simp [sampleWOTSHash]
example : sampleWOTSHash.toBits.length = 32 * 8 := by simp
example : sampleWOTSHash.toCompressedBits.length = 22 * 8 := by simp
example : sampleWOTSHash.toBytes.toList.length = 32 := by simp
example : sampleWOTSHash.toCompressedBytes.toList.length = 22 := by simp

-- The canonical words are big-endian and occupy their FIPS 205 Figure 3 positions.
example : binaryValue (sampleWOTSHash.toBits.take 32) = 1 := by decide +kernel
example : binaryValue ((sampleWOTSHash.toBits.drop 32).take 96) = 2 := by decide +kernel
example : binaryValue ((sampleWOTSHash.toBits.drop 128).take 32) = 0 := by decide +kernel
example : binaryValue ((sampleWOTSHash.toBits.drop 160).take 32) = 3 := by decide +kernel
example : binaryValue ((sampleWOTSHash.toBits.drop 192).take 32) = 4 := by decide +kernel
example : binaryValue ((sampleWOTSHash.toBits.drop 224).take 32) = 5 := by decide +kernel

-- The byte APIs preserve those exact layouts and record their lengths in their result types.
#guard sampleWOTSHash.toBytes.toList ==
  [0, 0, 0, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2,
    0, 0, 0, 0,
    0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5]
#guard sampleWOTSHash.toCompressedBytes.toList ==
  [1, 0, 0, 0, 0, 0, 0, 0, 2, 0,
    0, 0, 0, 3, 0, 0, 0, 4, 0, 0, 0, 5]

-- All seven typed constructors satisfy the padding and fixed-layer requirements in Figures 3--9.
example : (Address.wotsHash 1 2 3 4 5).WellFormed := by simp
example : (Address.wotsPK 1 2 3).WellFormed := by simp
example : (Address.tree 1 2 3 4).WellFormed := by simp
example : (Address.forsTree 2 3 4 5).WellFormed := by simp
example : (Address.forsRoots 2 3).WellFormed := by simp
example : (Address.wotsPRF 1 2 3 4).WellFormed := by simp
example : (Address.forsPRF 2 3 4).WellFormed := by simp

-- A nonzero WOTS_PK padding word is rejected.
example : ¬ ({ Address.wotsPK 1 2 3 with word6 := 9 }).WellFormed := by decide +kernel

def stalePayload : Address := Address.wotsHash 1 2 7 8 9

-- Regression: changing a type cannot preserve stale type-dependent words.
example :
    (stalePayload.setTypeAndClear .tree).word5 = 0 ∧
      (stalePayload.setTypeAndClear .tree).word6 = 0 ∧
      (stalePayload.setTypeAndClear .tree).word7 = 0 := by
  simp

example : stalePayload.setTypeAndClear .tree ≠ { stalePayload with addressType := .tree } := by
  decide +kernel

-- The SHA2 projection is injective on the field range retained by FIPS 205 Figure 18.
example : sampleWOTSHash.FitsCompressed := by decide +kernel
example {a b : Address} (ha : a.FitsCompressed) (hb : b.FitsCompressed)
    (h : a.toCompressedBits = b.toCompressedBits) : a = b :=
  Address.toCompressedBits_injective_of_fits ha hb h

example {a b : Address} (ha : a.FitsCompressed) (hb : b.FitsCompressed)
    (h : a.toCompressedBytes = b.toCompressedBytes) : a = b :=
  Address.toCompressedBytes_injective_of_fits ha hb h

-- Outside that range the compressed format deliberately drops the high tree word.
def highTree : TreeAddress := ⟨2 ^ 64, by decide⟩

private theorem compressedOverflowBits :
    (Address.wotsHash 0 highTree 0 0 0).toCompressedBits =
      (Address.wotsHash 0 0 0 0 0).toCompressedBits := by
  decide +kernel

example :
    (Address.wotsHash 0 highTree 0 0 0).toCompressedBytes =
      (Address.wotsHash 0 0 0 0 0).toCompressedBytes := by
  exact congrArg (bitsToFixedBytesBE 22) compressedOverflowBits

example : ¬ (Address.wotsHash 0 highTree 0 0 0).FitsCompressed := by decide +kernel

-- Canonical 32-byte serialization never aliases two addresses.
example {a b : Address} (h : a.toBits = b.toBits) : a = b :=
  Address.toBits_injective h

example {a b : Address} (h : a.toBytes = b.toBytes) : a = b :=
  Address.toBytes_injective h

end SLHDSAAddressTests
