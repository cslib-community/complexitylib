/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import CslibFrontier.Tactic.PolyTime

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

-- Direct and composed polynomial-time field projections and structure construction.
example : ComputableInPolyTime Point.x ePoint encNat := by
  fun_prop

example {α : Type} {enc : α ↪ List Bool} {f : α → Point}
    (hf : ComputableInPolyTime f enc ePoint) :
    ComputableInPolyTime (fun a => Point.mk (f a).x (f a).y (f a).z) enc ePoint := by
  fun_prop

/-- A single-field structure, where `eSFields` is the field encoding itself rather than a pair. -/
structure Single where
  /-- Binary payload list. -/
  items : List ℕ

/-- Single-field records, encoded directly by their field encoding. -/
enc_structure eSingle : Single where items : (encList encNat)

example : ComputableInPolyTime Single.items eSingle (encList encNat) := by
  fun_prop

example {α : Type} {enc : α ↪ List Bool} {xs : α → List ℕ}
    (hxs : ComputableInPolyTime xs enc (encList encNat)) :
    ComputableInPolyTime (fun a => Single.mk (xs a)) enc eSingle := by
  fun_prop

/-- A multi-field problem instance encoded with `enc_structure` for `polytime` clients. -/
structure HittingSetInstance where
  /-- Finite ground set of elements, encoded in binary. -/
  ground : List ℕ
  /-- Subsets that must each be hit. -/
  sets : List (List ℕ)
  /-- Target cardinality, encoded in binary. -/
  k : ℕ

/-- Ground set, framed, followed by framed subsets, framed, followed by binary target `k`. -/
enc_structure encHittingSet : HittingSetInstance where
  ground : (encList encNat), sets : (encList (encList encNat)), k : encNat

/-- Transform a problem instance using named fields without unfolding `encHittingSet`. -/
def prependZeroToSets (I : HittingSetInstance) : HittingSetInstance where
  ground := 0 :: I.ground
  sets := I.sets.map fun S => 0 :: S
  k := I.k

example : ComputableInPolyTime prependZeroToSets encHittingSet encHittingSet := by
  polytime [prependZeroToSets]

/-! The command resolves the structure through `open`, a parent structure is the single field
`toParent`, as in the constructor, and the constructor need not be called `mk`. The projections
are those of the checked structure, even where another declaration shares their name. -/

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

/-- Not the projection `Inner.Pair.fst`: under `open Inner`, `Pair.fst` could name either. -/
def Pair.fst (p : Inner.Pair) : ℕ := p.fst + 1

open Inner in
/-- Pairs, through `open`. -/
enc_structure ePair : Pair where fst : encNat, snd : encBool

-- The field rule is about the projection, not the decoy `Pair.fst` above.
example : ComputableInDegree Inner.Pair.fst ePair encNat 1 1 := ePair_fst_deg

/-- Triples, as the encoded parent and the new field. -/
enc_structure eTriple : Triple where toPair : ePair, w : encUnary

example (t : Triple) : eTriple t = eTripleFields (t.toPair, t.w) := eTriple_apply t

/-- A structure whose constructor is not called `mk`. -/
structure Renamed where mkRenamed ::
  /-- A number. -/
  n : ℕ
  /-- A bit. -/
  b : Bool

/-- Renamed records, as their fields. -/
enc_structure eRenamed : Renamed where n : encNat, b : encBool

example :
    ComputableInDegree (fun r : Renamed => Renamed.mkRenamed r.n r.b) eRenamed eRenamed 1 1 := by
  fun_prop (disch := lia)

example :
    ComputableInPolyTime (fun r : Renamed => Renamed.mkRenamed r.n r.b) eRenamed eRenamed := by
  fun_prop

/-! The command checks the field list before declaring anything. Each error names the field. -/

/--
error: enc_structure: `n` is not a field of `Point`; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
#guard_msgs in
enc_structure eUnknown : Point where x : encNat, n : encBits, z : (encList encUnary)

/--
error: enc_structure: field `y` is listed twice; the fields of `Point` in declaration order are `x`, `y`, `z`
-/
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

-- A field inherited from a parent is listed through its parent field.
/--
error: enc_structure: `fst` is inherited through the parent field `toPair`, so list `toPair` instead; the fields of `Triple` in declaration order are `toPair`, `w`
-/
#guard_msgs in
enc_structure eFlat : Triple where fst : encNat, snd : encBool, w : encUnary

/-- error: enc_structure: `Nat` is not a structure -/
#guard_msgs in
enc_structure eNat : Nat where succ : encNat

/-- A class, whose field takes the instance as an instance argument. -/
class Klass where
  /-- The field. -/
  k : ℕ

/--
error: enc_structure: `Klass` is a class; only structures, whose fields are explicit, can be encoded
-/
#guard_msgs in
enc_structure eKlass : Klass where k : encNat

/-! A failed check declares nothing. -/

/-- error: Unknown identifier `eOrder` -/
#guard_msgs in
#check eOrder

end CslibFrontierTests.StructureEncoding
