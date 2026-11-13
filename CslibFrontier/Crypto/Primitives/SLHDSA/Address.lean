/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import CslibFrontier.Init
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size

/-!
# SLH-DSA addresses

This module formalizes the address (`ADRS`) formats from FIPS 205, Sections 4.2--4.4,
Figures 2--9 and Table 1. An address consists of a 32-bit layer address, a 96-bit tree address,
a 32-bit type, and three 32-bit type-dependent words. `Address.setTypeAndClear` implements the
standard's requirement that changing the type clears the final 12 bytes.

`Address.toBits` is the canonical 32-byte, big-endian encoding used by the SHAKE parameter sets.
The SHA2 parameter sets instead use the 22-byte compressed address `Address.toCompressedBits`
from FIPS 205, Section 11.2, Figure 18 and Table 3. Compression retains only one byte of the layer,
eight bytes of the tree, and one byte of the type. `Address.FitsCompressed` records the bounds
under which that projection is injective; the unrestricted compressed encoding is deliberately
not claimed to be injective.

This is only the address-domain layer. It does not define the FIPS 205 hash instantiations,
WOTS+, XMSS, FORS, the hypertree, signing or verification, or any security reduction.

## Main definitions

* `Cslib.Crypto.SLHDSA.AddressType`: the seven FIPS 205 address types.
* `Cslib.Crypto.SLHDSA.Address`: the eight-word canonical address.
* `Cslib.Crypto.SLHDSA.Address.setTypeAndClear`: change the type and clear the final three words.
* `Cslib.Crypto.SLHDSA.Address.toBits`: the canonical 256-bit big-endian encoding.
* `Cslib.Crypto.SLHDSA.Address.toCompressedBits`: the 176-bit SHA2 address encoding.
* `Cslib.Crypto.SLHDSA.Address.WellFormed`: the type-specific padding and fixed-field conditions.

## Main results

* `Cslib.Crypto.SLHDSA.Address.toBits_injective`: canonical serialization is injective.
* `Cslib.Crypto.SLHDSA.Address.toCompressedBits_injective_of_fits`: compressed serialization is
  injective when its retained layer and tree fields do not overflow.
* `Cslib.Crypto.SLHDSA.Address.setTypeAndClear_payload`: changing type clears all 96 payload bits.
* `Cslib.Crypto.SLHDSA.Address.wellFormed_*`: each typed constructor satisfies its FIPS layout.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Sections 4.2--4.4 and 11.2]
  [NISTFIPS205]
-/

@[expose] public section

namespace Cslib.Crypto.SLHDSA

open Cslib.BitString

private theorem binaryWord_pad {small large value : ℕ} (hwidth : small ≤ large)
    (hvalue : value < 2 ^ small) :
    binaryWord large value =
      List.replicate (large - small) false ++ binaryWord small value := by
  have hbits : value.bits.length ≤ small := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.2 hvalue
  simp only [binaryWord, ← List.append_assoc, ← List.replicate_add]
  congr 2
  omega

/-- One four-byte FIPS 205 address word. -/
abbrev AddressWord := Fin (2 ^ 32)

/-- The three-word tree address in an SLH-DSA address. -/
abbrev TreeAddress := Fin (2 ^ 96)

/-- The seven address types from FIPS 205, Section 4.2, Figures 3--9. -/
inductive AddressType where
  /-- A hash step within a WOTS+ chain (type 0). -/
  | wotsHash
  /-- WOTS+ public-key compression (type 1). -/
  | wotsPK
  /-- A hash-tree node within XMSS (type 2). -/
  | tree
  /-- A node within one of the FORS trees (type 3). -/
  | forsTree
  /-- Compression of the FORS roots (type 4). -/
  | forsRoots
  /-- Generation of a WOTS+ secret value (type 5). -/
  | wotsPRF
  /-- Generation of a FORS secret value (type 6). -/
  | forsPRF
  deriving DecidableEq, Repr

namespace AddressType

/-- The integer type code specified by FIPS 205. -/
def toNat : AddressType → ℕ
  | .wotsHash => 0
  | .wotsPK => 1
  | .tree => 2
  | .forsTree => 3
  | .forsRoots => 4
  | .wotsPRF => 5
  | .forsPRF => 6

/-- Every FIPS 205 address-type code fits in one byte. -/
theorem toNat_lt_256 (t : AddressType) : t.toNat < 2 ^ 8 := by
  cases t <;> decide

/-- The type code as a four-byte address word. -/
def word (t : AddressType) : AddressWord :=
  ⟨t.toNat, Nat.lt_trans t.toNat_lt_256 (by decide)⟩

/-- Distinct address types have distinct FIPS 205 integer codes. -/
theorem toNat_injective : Function.Injective toNat := by
  intro a b h
  cases a <;> cases b <;> simp [toNat] at h ⊢

end AddressType

/-- The big-endian bits of one four-byte address word. -/
def addressWordBits (x : AddressWord) : List Bool := binaryWord 32 x

/-- A serialized four-byte address word has 32 bits. -/
@[simp] theorem length_addressWordBits (x : AddressWord) : (addressWordBits x).length = 32 :=
  length_binaryWord x.isLt

/-- Reading a serialized four-byte address word recovers its unsigned value. -/
@[simp] theorem binaryValue_addressWordBits (x : AddressWord) :
    binaryValue (addressWordBits x) = x :=
  binaryValue_binaryWord 32 x

/-- The big-endian bits of the 12-byte tree address. -/
def treeAddressBits (x : TreeAddress) : List Bool := binaryWord 96 x

/-- A serialized tree address has 96 bits. -/
@[simp] theorem length_treeAddressBits (x : TreeAddress) : (treeAddressBits x).length = 96 :=
  length_binaryWord x.isLt

/-- Reading a serialized tree address recovers its unsigned value. -/
@[simp] theorem binaryValue_treeAddressBits (x : TreeAddress) :
    binaryValue (treeAddressBits x) = x :=
  binaryValue_binaryWord 96 x

/-- A FIPS 205 address as its common fields and three type-dependent words.

The field names `word5`, `word6`, and `word7` refer to their zero-based positions in the eight-word
address. Their meanings are fixed by `addressType`; use the typed constructors below to obtain a
well-formed address for a particular purpose. -/
structure Address where
  /-- The XMSS layer, stored in word 0. -/
  layerAddress : AddressWord
  /-- The XMSS tree within the layer, stored in words 1--3. -/
  treeAddress : TreeAddress
  /-- The address type, stored in word 4. -/
  addressType : AddressType
  /-- The first type-dependent word. -/
  word5 : AddressWord
  /-- The second type-dependent word. -/
  word6 : AddressWord
  /-- The third type-dependent word. -/
  word7 : AddressWord
  deriving DecidableEq, Repr

namespace Address

/-- Two addresses are equal when all seven semantic fields agree. -/
@[ext] theorem ext {a b : Address}
    (hlayer : a.layerAddress = b.layerAddress)
    (htree : a.treeAddress = b.treeAddress)
    (htype : a.addressType = b.addressType)
    (h5 : a.word5 = b.word5) (h6 : a.word6 = b.word6) (h7 : a.word7 = b.word7) : a = b := by
  cases a
  cases b
  simp_all

/-- The big-endian four-byte encoding of an address type. -/
def typeBits (t : AddressType) : List Bool := addressWordBits t.word

/-- A serialized address type occupies one four-byte word. -/
@[simp] theorem length_typeBits (t : AddressType) : (typeBits t).length = 32 := by
  simp [typeBits]

/-- The canonical 32-byte encoding of an address (FIPS 205, Figure 2 and Table 1). -/
def toBits (a : Address) : List Bool :=
  addressWordBits a.layerAddress ++
  treeAddressBits a.treeAddress ++
  typeBits a.addressType ++
  addressWordBits a.word5 ++ addressWordBits a.word6 ++ addressWordBits a.word7

/-- A canonical SLH-DSA address encoding is exactly 32 bytes. -/
@[simp] theorem length_toBits (a : Address) : a.toBits.length = 256 := by
  simp [toBits, typeBits]

private theorem addressWordBits_injective : Function.Injective addressWordBits := by
  intro x y h
  apply Fin.ext
  simpa using congrArg binaryValue h

private theorem treeAddressBits_injective : Function.Injective treeAddressBits := by
  intro x y h
  apply Fin.ext
  simpa using congrArg binaryValue h

private theorem typeBits_injective : Function.Injective typeBits := by
  intro x y h
  apply AddressType.toNat_injective
  have hword := addressWordBits_injective h
  exact congrArg Fin.val hword

/-- The canonical 32-byte address encoding is injective. -/
theorem toBits_injective : Function.Injective toBits := by
  intro a b h
  unfold toBits at h
  obtain ⟨h, h7⟩ := List.append_inj' h (by simp)
  obtain ⟨h, h6⟩ := List.append_inj' h (by simp)
  obtain ⟨h, h5⟩ := List.append_inj' h (by simp)
  obtain ⟨h, htype⟩ := List.append_inj' h (by simp)
  obtain ⟨hlayer, htree⟩ := List.append_inj' h (by simp)
  exact ext (addressWordBits_injective hlayer) (treeAddressBits_injective htree)
    (typeBits_injective htype) (addressWordBits_injective h5)
    (addressWordBits_injective h6) (addressWordBits_injective h7)

/-- The 22-byte compressed address used by the FIPS 205 SHA2 parameter sets.

This is `ADRS[3] || ADRS[8:16] || ADRS[19] || ADRS[20:32]`: the low byte of the layer,
the low eight bytes of the tree, the low byte of the type, and all three type-dependent words. -/
def toCompressedBits (a : Address) : List Bool :=
  (addressWordBits a.layerAddress).drop 24 ++
  (treeAddressBits a.treeAddress).drop 32 ++
  (typeBits a.addressType).drop 24 ++
  addressWordBits a.word5 ++ addressWordBits a.word6 ++ addressWordBits a.word7

/-- A SHA2 compressed address encoding is exactly 22 bytes. -/
@[simp] theorem length_toCompressedBits (a : Address) : a.toCompressedBits.length = 176 := by
  simp [toCompressedBits]

/-- If a layer address fits in the retained byte, reading that byte recovers it. -/
theorem binaryValue_drop24_addressWordBits_of_lt {x : AddressWord} (h : x.val < 2 ^ 8) :
    binaryValue ((addressWordBits x).drop 24) = x := by
  rw [addressWordBits, binaryWord_pad (small := 8) (large := 32) (by decide) h]
  simp

/-- If a tree address fits in the retained eight bytes, reading those bytes recovers it. -/
theorem binaryValue_drop32_treeAddressBits_of_lt {x : TreeAddress} (h : x.val < 2 ^ 64) :
    binaryValue ((treeAddressBits x).drop 32) = x := by
  rw [treeAddressBits, binaryWord_pad (small := 64) (large := 96) (by decide) h]
  simp

/-- Reading the retained type byte recovers the FIPS 205 type code. -/
theorem binaryValue_drop24_typeBits (t : AddressType) :
    binaryValue ((typeBits t).drop 24) = t.toNat := by
  change binaryValue ((binaryWord 32 t.toNat).drop 24) = t.toNat
  rw [binaryWord_pad (small := 8) (large := 32) (by decide) t.toNat_lt_256]
  simp

/-- The bound under which the one-byte layer and eight-byte tree fields of the compressed SHA2
address lose no information. FIPS 205 parameter sets satisfy these bounds at every call site. -/
def FitsCompressed (a : Address) : Prop :=
  a.layerAddress.val < 2 ^ 8 ∧ a.treeAddress.val < 2 ^ 64

instance (a : Address) : Decidable a.FitsCompressed := by
  unfold FitsCompressed
  infer_instance

/-- Compressed SHA2 address serialization is injective when neither shortened field overflows. -/
theorem toCompressedBits_injective_of_fits {a b : Address}
    (ha : a.FitsCompressed) (hb : b.FitsCompressed)
    (h : a.toCompressedBits = b.toCompressedBits) : a = b := by
  unfold toCompressedBits at h
  obtain ⟨h, h7⟩ := List.append_inj' h (by simp)
  obtain ⟨h, h6⟩ := List.append_inj' h (by simp)
  obtain ⟨h, h5⟩ := List.append_inj' h (by simp)
  obtain ⟨h, htype⟩ := List.append_inj' h (by simp)
  obtain ⟨hlayer, htree⟩ := List.append_inj' h (by simp)
  have hlayer' : a.layerAddress.val = b.layerAddress.val := by
    have hvalue := congrArg binaryValue hlayer
    rw [binaryValue_drop24_addressWordBits_of_lt ha.1,
      binaryValue_drop24_addressWordBits_of_lt hb.1] at hvalue
    exact hvalue
  have htree' : a.treeAddress.val = b.treeAddress.val := by
    have hvalue := congrArg binaryValue htree
    rw [binaryValue_drop32_treeAddressBits_of_lt ha.2,
      binaryValue_drop32_treeAddressBits_of_lt hb.2] at hvalue
    exact hvalue
  have htype' : a.addressType = b.addressType := by
    apply AddressType.toNat_injective
    have hvalue := congrArg binaryValue htype
    rw [binaryValue_drop24_typeBits, binaryValue_drop24_typeBits] at hvalue
    exact hvalue
  exact ext (Fin.ext hlayer') (Fin.ext htree') htype' (addressWordBits_injective h5)
    (addressWordBits_injective h6) (addressWordBits_injective h7)

/-- Set the layer address, preserving every other word. -/
def setLayerAddress (a : Address) (layer : AddressWord) : Address :=
  { a with layerAddress := layer }

/-- Set the 12-byte tree address, preserving every other word. -/
def setTreeAddress (a : Address) (tree : TreeAddress) : Address :=
  { a with treeAddress := tree }

/-- Change the address type and clear all three type-dependent words (FIPS 205, Section 4.3). -/
def setTypeAndClear (a : Address) (t : AddressType) : Address :=
  { a with addressType := t, word5 := 0, word6 := 0, word7 := 0 }

/-- Set the key-pair address in word 5. -/
def setKeyPairAddress (a : Address) (keyPair : AddressWord) : Address :=
  { a with word5 := keyPair }

/-- Set the WOTS+ chain address in word 6. -/
def setChainAddress (a : Address) (chain : AddressWord) : Address :=
  { a with word6 := chain }

/-- Set the tree height in word 6. -/
def setTreeHeight (a : Address) (height : AddressWord) : Address :=
  { a with word6 := height }

/-- Set the WOTS+ hash address in word 7. -/
def setHashAddress (a : Address) (hash : AddressWord) : Address :=
  { a with word7 := hash }

/-- Set the tree index in word 7. -/
def setTreeIndex (a : Address) (index : AddressWord) : Address :=
  { a with word7 := index }

/-- Changing the type preserves the layer and tree fields. -/
@[simp] theorem setTypeAndClear_common (a : Address) (t : AddressType) :
    (a.setTypeAndClear t).layerAddress = a.layerAddress ∧
      (a.setTypeAndClear t).treeAddress = a.treeAddress :=
  ⟨rfl, rfl⟩

/-- Changing the type sets the requested type and clears all final 12 bytes. -/
@[simp] theorem setTypeAndClear_payload (a : Address) (t : AddressType) :
    (a.setTypeAndClear t).addressType = t ∧
      (a.setTypeAndClear t).word5 = 0 ∧
      (a.setTypeAndClear t).word6 = 0 ∧
      (a.setTypeAndClear t).word7 = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The padding and fixed-field requirements of FIPS 205, Figures 3--9. -/
def WellFormed (a : Address) : Prop :=
  match a.addressType with
  | .wotsHash => True
  | .wotsPK => a.word6 = 0 ∧ a.word7 = 0
  | .tree => a.word5 = 0
  | .forsTree => a.layerAddress = 0
  | .forsRoots => a.layerAddress = 0 ∧ a.word6 = 0 ∧ a.word7 = 0
  | .wotsPRF => a.word7 = 0
  | .forsPRF => a.layerAddress = 0 ∧ a.word6 = 0

instance (a : Address) : Decidable a.WellFormed := by
  unfold WellFormed
  cases a.addressType <;> infer_instance

/-- A WOTS+ hash-chain address (FIPS 205, Figure 3). -/
def wotsHash (layer : AddressWord) (tree : TreeAddress)
    (keyPair chain hash : AddressWord) : Address :=
  ⟨layer, tree, .wotsHash, keyPair, chain, hash⟩

/-- A WOTS+ public-key compression address (FIPS 205, Figure 4). -/
def wotsPK (layer : AddressWord) (tree : TreeAddress) (keyPair : AddressWord) : Address :=
  ⟨layer, tree, .wotsPK, keyPair, 0, 0⟩

/-- An XMSS hash-tree address (FIPS 205, Figure 5). -/
def tree (layer : AddressWord) (tree : TreeAddress) (height index : AddressWord) : Address :=
  ⟨layer, tree, .tree, 0, height, index⟩

/-- A FORS tree address (FIPS 205, Figure 6). The FORS layer is fixed to zero. -/
def forsTree (tree : TreeAddress) (keyPair height index : AddressWord) : Address :=
  ⟨0, tree, .forsTree, keyPair, height, index⟩

/-- A FORS roots-compression address (FIPS 205, Figure 7). -/
def forsRoots (tree : TreeAddress) (keyPair : AddressWord) : Address :=
  ⟨0, tree, .forsRoots, keyPair, 0, 0⟩

/-- A WOTS+ secret-value generation address (FIPS 205, Figure 8). -/
def wotsPRF (layer : AddressWord) (tree : TreeAddress)
    (keyPair chain : AddressWord) : Address :=
  ⟨layer, tree, .wotsPRF, keyPair, chain, 0⟩

/-- A FORS secret-value generation address (FIPS 205, Figure 9). -/
def forsPRF (tree : TreeAddress) (keyPair index : AddressWord) : Address :=
  ⟨0, tree, .forsPRF, keyPair, 0, index⟩

@[simp] theorem wellFormed_wotsHash (layer tree keyPair chain hash) :
    (wotsHash layer tree keyPair chain hash).WellFormed := by
  simp [wotsHash, WellFormed]

@[simp] theorem wellFormed_wotsPK (layer tree keyPair) :
    (wotsPK layer tree keyPair).WellFormed := by
  simp [wotsPK, WellFormed]

@[simp] theorem wellFormed_tree (layer treeAddress height index) :
    (tree layer treeAddress height index).WellFormed := by
  simp [tree, WellFormed]

@[simp] theorem wellFormed_forsTree (tree keyPair height index) :
    (forsTree tree keyPair height index).WellFormed := by
  simp [forsTree, WellFormed]

@[simp] theorem wellFormed_forsRoots (tree keyPair) :
    (forsRoots tree keyPair).WellFormed := by
  simp [forsRoots, WellFormed]

@[simp] theorem wellFormed_wotsPRF (layer tree keyPair chain) :
    (wotsPRF layer tree keyPair chain).WellFormed := by
  simp [wotsPRF, WellFormed]

@[simp] theorem wellFormed_forsPRF (tree keyPair index) :
    (forsPRF tree keyPair index).WellFormed := by
  simp [forsPRF, WellFormed]

end Address

end Cslib.Crypto.SLHDSA
