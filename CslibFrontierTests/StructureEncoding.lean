/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists

/-! Tests of `enc_structure`. -/

namespace CslibFrontierTests.StructureEncoding

open Turing.MultiTapeTM

/-- A structure with fields of different encodings. -/
structure Point where
  /-- A binary number. -/
  x : ℕ
  /-- A bit string. -/
  y : List Bool
  /-- A list of unary numbers. -/
  z : List ℕ

/-- Points, as their fields. -/
enc_structure ePoint : Point where x : encNat, y : encBits, z : (encList encUnary)

/-! The encoding unfolds to the tuple, and the encoding is injective by construction. -/

example (p : Point) : ePoint p = ePointFields (p.x, p.y, p.z) := ePoint_apply p
example {p q : Point} (h : ePoint p = ePoint q) : p = q := ePoint.injective h

/-! The field and constructor rules assemble programs over the structure. -/

example : ComputableInDegree (fun p : Point => Point.mk p.x p.y p.z) ePoint ePoint 1 1 := by
  fun_prop (disch := lia)

/-- Reading a generated field retains the caller's budget, including for unary list elements. -/
example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → Point}
    (hf : ComputableInSpace f enc ePoint S) :
    ComputableInSpace (fun a => (f a).z) enc (encList encUnary) S :=
  ePoint_z_budget hf

-- Reading fields and rebuilding the structure, with the bounds checked once.
example : ComputableInO (fun p : Point => Point.mk p.x p.y p.z.tail) ePoint ePoint
    (fun p => 8 * ((ePoint p).length + 1)) fun p => 8 * ((ePoint p).length + 1) := by
  refine .mono (by fun_prop) 16 (fun p => ?_) fun p => ?_ <;>
  · simp only [ePoint_apply, length_encPair]
    have := ((List.tail_sublist p.z).flatMap (frame ∘ encUnary)).length_le
    omega

/-! The command resolves the structure through `open`, and a parent structure is the single field
`toParent`, as in the constructor. -/

namespace Inner

/-- A structure declared in a namespace. -/
structure Pair where
  /-- The first component. -/
  fst : ℕ
  /-- The second component. -/
  snd : Bool

end Inner

/-- A structure extending another, with fields `toPair` and `w`. -/
structure Triple extends Inner.Pair where
  /-- The new field. -/
  w : ℕ

open Inner in
/-- Pairs, through `open`. -/
enc_structure ePair : Pair where fst : encNat, snd : encBool

/-- Triples, as the encoded parent and the new field. -/
enc_structure eTriple : Triple where toPair : ePair, w : encUnary

example (t : Triple) : eTriple t = eTripleFields (t.toPair, t.w) := eTriple_apply t

/-! The command checks the field list before declaring anything. Each error names the field. -/

/--
error: enc_structure: `n` is not a field of `Point`; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
#guard_msgs in
enc_structure eUnknown : Point where x : encNat, n : encBits, z : (encList encUnary)

/-- error: enc_structure: field `y` is listed twice -/
#guard_msgs in
enc_structure eTwice : Point where x : encNat, y : encBits, y : encBits, z : (encList encUnary)

/--
error: enc_structure: field `x` must come before `y`; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
#guard_msgs in
enc_structure eOrder : Point where y : encBits, x : encNat, z : (encList encUnary)

/--
error: enc_structure: missing field `z` of `Point`; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
#guard_msgs in
enc_structure eMissing : Point where x : encNat, y : encBits

/--
error: enc_structure: missing fields `x`, `z` of `Point`; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
#guard_msgs in
enc_structure eMissingTwo : Point where y : encBits

-- Inherited fields are not fields of the extending structure.
/--
error: enc_structure: `fst` is not a field of `Triple`; the fields of `Triple` in declaration order are `toPair`, `w`
-/
#guard_msgs in
enc_structure eFlat : Triple where fst : encNat, snd : encBool, w : encUnary

/-- error: enc_structure: `Nat` is not a structure -/
#guard_msgs in
enc_structure eNat : Nat where succ : encNat

/-! A failed check declares nothing. -/

/-- error: Unknown identifier `eOrder` -/
#guard_msgs in
#check eOrder

end CslibFrontierTests.StructureEncoding
