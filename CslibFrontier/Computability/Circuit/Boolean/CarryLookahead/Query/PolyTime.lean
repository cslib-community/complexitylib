/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.Query
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Uniform native decoding of carry-lookahead queries

The address layout stores a binary constructor tag, a unary round, and a binary cell index.
Rounds are at most logarithmic in width at the adder's output query. The decoder handles malformed
raw records too. Computing `2 ^ round` produces only `round + 1` binary digits.

One native multitape procedure computes each child address from runtime width, round count,
address, and branch bit. A separate operation procedure reads runtime input bits by ordinary
bounded list lookup. Neither procedure constructs a row or an adder circuit. The input lookup's
cost is charged to the actual runtime input encoding, not supplied as a free oracle.

These are polynomial-time certificates in the stated encoded lengths. They do not by themselves
supply the sharp amortized branch bound needed for the final contraction simulation.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarryLookahead.Query

open Turing.MultiTapeTM ComputableInPolyTime

/-- Raw address storage. Tags `0` through `11` follow `Address` constructor order; unused round
fields are zero in canonical encodings. Invalid tags are treated as input references. -/
structure AddressData where
  /-- Binary constructor tag. -/
  tag : ℕ
  /-- Unary carry-doubling round. -/
  round : ℕ
  /-- Binary input or cell index. -/
  index : ℕ
  deriving DecidableEq

/-- Framed tag, then framed unary round, then binary index. -/
enc_structure encAddressData : AddressData where tag : encNat, round : encUnary, index : encNat

/-- The exact address length includes both framing delimiters and every unary round bit. -/
theorem length_encAddressData (d : AddressData) :
    (encAddressData d).length = 2 * d.tag.size + 2 * d.round + d.index.size + 2 := by
  simp only [encAddressData_apply, encAddressDataFields, length_encPair, encNat_apply,
    Nat.size_eq_bits_len, encUnary_apply, List.length_replicate]
  omega

/-- The canonical raw representation of a semantic address. -/
def Address.toData : Address → AddressData
  | .input i => ⟨0, 0, i⟩
  | .generate r i => ⟨1, r, i⟩
  | .propagate r i => ⟨2, r, i⟩
  | .generateAnd r i => ⟨3, r, i⟩
  | .xorOr i => ⟨4, 0, i⟩
  | .xorAnd i => ⟨5, 0, i⟩
  | .xorNot i => ⟨6, 0, i⟩
  | .xor i => ⟨7, 0, i⟩
  | .sumOr i => ⟨8, 0, i⟩
  | .sumAnd i => ⟨9, 0, i⟩
  | .sumNot i => ⟨10, 0, i⟩
  | .sum i => ⟨11, 0, i⟩

/-- Interpret raw address storage, ignoring unused round fields. -/
def AddressData.address (d : AddressData) : Address :=
  match d.tag with
  | 1 => .generate d.round d.index
  | 2 => .propagate d.round d.index
  | 3 => .generateAnd d.round d.index
  | 4 => .xorOr d.index
  | 5 => .xorAnd d.index
  | 6 => .xorNot d.index
  | 7 => .xor d.index
  | 8 => .sumOr d.index
  | 9 => .sumAnd d.index
  | 10 => .sumNot d.index
  | 11 => .sum d.index
  | _ => .input d.index

/-- Canonical address storage preserves every semantic address. -/
@[simp] theorem Address.address_toData (a : Address) : a.toData.address = a := by
  cases a <;> rfl

/-- Canonical address storage is injective. -/
theorem Address.toData_injective : Function.Injective Address.toData :=
  Function.LeftInverse.injective Address.address_toData

/-- Encode an address by its canonical raw record: binary tag/index, unary round. -/
def encAddress : Address ↪ List Bool :=
  (⟨Address.toData, Address.toData_injective⟩ : Address ↪ AddressData).trans encAddressData

/-- A semantic address uses a constant-size tag, its unary round, and its binary cell index. -/
theorem length_encAddress_le (a : Address) :
    (encAddress a).length ≤ 2 * a.toData.round + a.toData.index.size + 10 := by
  change (encAddressData a.toData).length ≤ _
  rw [length_encAddressData]
  have ht : a.toData.tag.size ≤ 4 := by cases a <;> simp only [Address.toData] <;> decide
  omega

/-- Reading an address as its raw record changes no encoded bits. -/
theorem toData_polyTime : ComputableInPolyTime Address.toData encAddress encAddressData :=
  .of_eq fun _ => rfl

/-- The operation at a raw address, with input lookup on a runtime list. -/
def opData (w : ℕ) (input : List Bool) (d : AddressData) : Op :=
  if d.tag = 1 then if d.index < w + 1 then .or else .const false
  else if d.tag = 2 then if d.index < w + 1 then
    if d.round = 0 then if d.index < w then .or else .const false else .and
    else .const true
  else if d.tag = 3 then .and
  else if d.tag = 4 ∨ d.tag = 8 then .or
  else if d.tag = 5 ∨ d.tag = 7 ∨ d.tag = 9 ∨ d.tag = 11 then .and
  else if d.tag = 6 ∨ d.tag = 10 then .not
  else .const (input.getD d.index false)

/-- The child of a raw address, using only local arithmetic and no input bits. -/
def childData (w rounds : ℕ) (d : AddressData) (b : Bool) : AddressData :=
  if d.tag = 1 then
    if d.round = 0 then if d.index < w then ⟨3, 0, d.index⟩ else ⟨0, 0, w + w⟩
    else if b then ⟨3, d.round, d.index⟩ else ⟨1, d.round - 1, d.index⟩
  else if d.tag = 2 then
    if d.round = 0 then ⟨0, 0, if b then w + (w - 1 - d.index) else w - 1 - d.index⟩
    else ⟨2, d.round - 1,
      if b then neighbourIndex (w + 1) (2 ^ (d.round - 1)) d.index else d.index⟩
  else if d.tag = 3 then
    if d.round = 0 then ⟨0, 0, if b then w + (w - 1 - d.index) else w - 1 - d.index⟩
    else if b then ⟨1, d.round - 1, neighbourIndex (w + 1) (2 ^ (d.round - 1)) d.index⟩
      else ⟨2, d.round - 1, d.index⟩
  else if d.tag = 4 ∨ d.tag = 5 then ⟨0, 0, if b then w + d.index else d.index⟩
  else if d.tag = 6 then ⟨5, 0, d.index⟩
  else if d.tag = 7 then ⟨if b then 6 else 4, 0, d.index⟩
  else if d.tag = 8 ∨ d.tag = 9 then
    if b then ⟨1, rounds, w - d.index⟩ else ⟨7, 0, d.index⟩
  else if d.tag = 10 then ⟨9, 0, d.index⟩
  else if d.tag = 11 then ⟨if b then 10 else 8, 0, d.index⟩
  else ⟨0, 0, d.index⟩

/-- Child routing agrees exactly with the cross-layer semantic decoder. -/
theorem childData_toData (w rounds : ℕ) (u : BitString (w + w + 1)) (a : Address) (b : Bool) :
    childData w rounds a.toData b = ((decoder w rounds u).child a b).toData := by
  cases a with
  | generate r i =>
    cases r with
    | zero => by_cases hi : i < w <;> cases b <;> simp [Address.toData, childData, decoder, hi]
    | succ r => cases b <;> simp [Address.toData, childData, decoder]
  | propagate r i | generateAnd r i =>
    cases r <;> cases b <;> simp [Address.toData, childData, decoder]
  | input i | xorOr i | xorAnd i | xorNot i | xor i | sumOr i | sumAnd i | sumNot i | sum i =>
    cases b <;> simp [Address.toData, childData, decoder]

/-- Runtime input lookup agrees with the bounded bit-string lookup. -/
theorem opData_toData (w rounds : ℕ) (u : BitString (w + w + 1)) (a : Address) :
    opData w (List.ofFn u) a.toData = (decoder w rounds u).op a := by
  cases a with
  | input i =>
    change Op.const ((List.ofFn u).getD i false) = Op.const (readInput w u i)
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    by_cases hi : i < w + w + 1 <;> simp [readInput, hi]
  | propagate r i =>
    simp only [Address.toData, opData, decoder]
    rfl
  | generate r i | generateAnd r i =>
    simp [Address.toData, opData, decoder]
  | xorOr i | xorAnd i | xorNot i | xor i | sumOr i | sumAnd i | sumNot i | sum i =>
    simp [Address.toData, opData, decoder]

/-- One native decoder uniformly computes operations from runtime input and binary coordinates.
The ordinary input-list lookup is included in the polynomial time bound. -/
theorem opData_polyTime {α : Type} {enc : α ↪ List Bool}
    {w : α → ℕ} {input : α → List Bool} {d : α → AddressData}
    (hw : ComputableInPolyTime w enc encNat)
    (hi : ComputableInPolyTime input enc encBits)
    (hd : ComputableInPolyTime d enc encAddressData) :
    ComputableInPolyTime (fun a => opData (w a) (input a) (d a)) enc encOp := by
  have hget : ComputableInPolyTime (fun a => (input a).getD (d a).index false) enc encBool :=
    listGetD_binary false hi (by fun_prop)
  have hconst := (of_finite (encIn := encBool) (encOut := encOp) Op.const).comp hget
  unfold opData
  fun_prop

/-- One native decoder uniformly computes child references. Round counters are unary; all widths
and cell indices are binary, so producing the distance `2 ^ round` is charged by its bit length. -/
theorem childData_polyTime {α : Type} {enc : α ↪ List Bool}
    {w rounds : α → ℕ} {d : α → AddressData} {b : α → Bool}
    (hw : ComputableInPolyTime w enc encNat)
    (hr : ComputableInPolyTime rounds enc encUnary)
    (hd : ComputableInPolyTime d enc encAddressData)
    (hb : ComputableInPolyTime b enc encBool) :
    ComputableInPolyTime (fun a => childData (w a) (rounds a) (d a) (b a)) enc encAddressData := by
  unfold childData neighbourIndex
  fun_prop

end Cslib.Circuits.Boolean.CarryLookahead.Query
