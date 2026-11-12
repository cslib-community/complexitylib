/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CountingLeaf
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.OfBits

/-!
# Counting leaves on unnormalized tape words

The serializer can copy fixed-width counters verbatim, including redundant high zeroes.
Normalization is performed by a certified native function after serialization. The address path
remains most-significant-first; count, precision and bit-index words are least-significant-first.
-/

public section

namespace Cslib.CountingLeaf

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

/-- Physical word fields of a counting-leaf query before binary normalization. -/
structure RawInput where
  /-- Serialized predicate context. -/
  context : List Bool
  /-- Number of genuine leaves, in little-endian digits. -/
  count : List Bool
  /-- Word precision, in little-endian digits. -/
  width : List Bool
  /-- Root-to-leaf path, in most-significant-first order. -/
  path : List Bool
  /-- Carry-save component selector. -/
  carry : Bool
  /-- Bit index, in little-endian digits. -/
  bit : List Bool

/-- Five framed fields followed by the raw index; numeric words need not be canonical. -/
enc_structure encRawInput : RawInput where
  context : encBits, count : encBits, width : encBits, path : encBits,
  carry : encBool, bit : encBits

/-- Convert raw numeric words to the canonical query's natural-number fields. -/
@[expose] def RawInput.normalize (q : RawInput) : Input :=
  ⟨q.context, ofBits q.count, ofBits q.width, q.path, q.carry, ofBits q.bit⟩

/-- Counter normalization is charged native polynomial-time computation. -/
theorem computableInPolyTime_normalize :
    ComputableInPolyTime RawInput.normalize encRawInput encInput := by
  have hn : ComputableInPolyTime ofBits encBits encNat :=
    .of_tidy ComputableTidilyInPolyTime.bitsToNat
  unfold RawInput.normalize
  apply encInput_mk_polyTime <;> fun_prop

/-- Read an unnormalized physical query and evaluate its counting-leaf bit. -/
@[expose] def runRaw (predicate : List Bool × ℕ → Bool) (q : RawInput) : Bool :=
  run predicate q.normalize

/-- The complete raw-query evaluator includes all three binary normalizations. -/
theorem computableInPolyTime_runRaw (predicate : List Bool × ℕ → Bool)
    (hp : ComputableInPolyTime predicate (encPair encBits encNat) encBool) :
    ComputableInPolyTime (runRaw predicate) encRawInput encBool :=
  (computableInPolyTime_run predicate hp).comp computableInPolyTime_normalize

/-- Exact framing layout for the physical serializer. -/
theorem encRawInput_eq (q : RawInput) :
    encRawInput q = frame q.context ++ frame q.count ++ frame q.width ++ frame q.path ++
      frame [q.carry] ++ q.bit := by
  simp [encRawInput_apply, encPair_apply, List.append_assoc]

/-- Copying raw counters has linear encoding size, without a canonicality premise. -/
theorem length_encRawInput (q : RawInput) :
    (encRawInput q).length =
      2 * (q.context.length + q.count.length + q.width.length + q.path.length) +
        q.bit.length + 7 := by
  simp only [encRawInput_apply, length_encPair, encBits_apply, encBool_apply,
    List.length_singleton]
  omega

/-- One traversal-size budget bounds every leaf serialization, independently of its path
and decremented bit-index contents. The three fixed context words are charged separately. -/
theorem length_encRawInput_le (q : RawInput) (sizeBudget : ℕ)
    (h : q.path.length + q.bit.length ≤ sizeBudget) :
    (encRawInput q).length ≤
      2 * (q.context.length + q.count.length + q.width.length + sizeBudget) + 7 := by
  rw [length_encRawInput]
  omega

/-- The native raw-query result agrees with the existing zero-layer semantics. -/
theorem runRaw_eq_value (predicate : List Bool × ℕ → Bool) (q : RawInput) :
    runRaw predicate q = Circuits.Boolean.CarrySaveQuery.value
      (fun path => Circuits.Boolean.CarrySaveQuery.Counting.leafPair
        (ofBits q.count) (ofBits q.width)
        (fun j => predicate (q.context, j)) (BitString.binaryValue path))
      ⟨q.path, 0, q.carry, ofBits q.bit⟩ :=
  run_eq_value predicate q.normalize

end Cslib.CountingLeaf
