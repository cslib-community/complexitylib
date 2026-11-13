/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (structure-encoding regression tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
public import CslibFrontier.Tactic.PolyTime

/-! Tests of `enc_structure`. -/

public section

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

/-- A record with an implicit description type, as used by encoded security challenges. -/
structure DescribedPair {Desc : Type} where
  /-- The arbitrary description. -/
  description : Desc
  /-- The first word. -/
  left : List Bool
  /-- The second word. -/
  right : List Bool

/-- Explicit command parameters determine the record type and its field encodings. -/
enc_structure eDescribedPair (Desc : Type) (encDesc : Desc ↪ List Bool) :
    DescribedPair (Desc := Desc) where
  description : encDesc, left : encBits, right : encBits

example (Desc : Type) (encDesc : Desc ↪ List Bool) (d : Desc) (u v : List Bool) :
    eDescribedPair Desc encDesc ⟨d, u, v⟩ = encPair encDesc (encPair encBits encBits) (d, u, v) :=
  rfl

-- Swapping the two words exercises both generated field projections and the constructor rule.
example (Desc : Type) (encDesc : Desc ↪ List Bool) :
    ComputableInPolyTime
      (fun p : DescribedPair (Desc := Desc) =>
        { description := p.description, left := p.right, right := p.left })
      (eDescribedPair Desc encDesc) (eDescribedPair Desc encDesc) := by
  fun_prop

example (Desc : Type) (encDesc : Desc ↪ List Bool) {α : Type} {enc : α ↪ List Bool}
    {S : α → ℕ} {f : α → DescribedPair (Desc := Desc)}
    (hf : ComputableInSpace f enc (eDescribedPair Desc encDesc) S) :
    ComputableInSpace (fun a => (f a).description) enc encDesc S :=
  eDescribedPair_description_budget Desc encDesc hf

/-- User parameters may share names with the command's generated proof variables. -/
enc_structure eDescribedPairCollision (γ : Type) (encIn : γ ↪ List Bool) :
    DescribedPair (Desc := γ) where
  description : encIn, left : encBits, right : encBits

example (γ : Type) (encIn : γ ↪ List Bool) :
    ComputableInPolyTime
      (fun p : DescribedPair (Desc := γ) =>
        { description := p.description, left := p.right, right := p.left })
      (eDescribedPairCollision γ encIn) (eDescribedPairCollision γ encIn) := by
  fun_prop

-- The constructor must retain the chosen description encoding when the caller has a different
-- input type and encoding. A same-domain identity test would not detect parameter capture.
example (γ : Type) (encIn : γ ↪ List Bool) {α : Type} {enc : α ↪ List Bool}
    {description : α → γ} {left right : α → List Bool}
    (hd : ComputableInPolyTime description enc encIn)
    (hl : ComputableInPolyTime left enc encBits)
    (hr : ComputableInPolyTime right enc encBits) :
    ComputableInPolyTime
      (fun a => { description := description a, left := left a, right := right a })
      enc (eDescribedPairCollision γ encIn) :=
  eDescribedPairCollision_mk_polyTime γ encIn hd hl hr

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

/-- A fixed-size family with a tag whose type does not mention the size parameter. -/
structure TaggedTable (n : ℕ) where
  /-- A flag outside the table. -/
  tag : Bool
  /-- Binary values indexed by the fixed table size. -/
  entries : Fin n → ℕ

noncomputable section

variable {n : ℕ}

/-- The framed tag followed by the existing finite-table encoding. -/
enc_structure eTaggedTable : TaggedTable n where
  tag : encBool, entries : (encPi (Index := Fin n) encNat)

example (t : TaggedTable n) :
    eTaggedTable t = encPair encBool (encPi encNat) (t.tag, t.entries) := rfl

-- A parameter-independent field still fixes the encoded input type, including at size zero.
example : ComputableInDegree (TaggedTable.tag (n := 0)) eTaggedTable encBool 1 1 := by
  fun_prop

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → TaggedTable n}
    (hf : ComputableInSpace f enc eTaggedTable S) :
    ComputableInSpace (fun a => (f a).entries) enc (encPi encNat) S := by
  fun_prop

example {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {tag : α → Bool} {entries : α → Fin n → ℕ}
    (ht : ComputableInSpace tag enc encBool S)
    (he : ComputableInSpace entries enc (encPi encNat) S) :
    ComputableInSpace (fun a => TaggedTable.mk (tag a) (entries a)) enc eTaggedTable S := by
  fun_prop

end

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
@[expose]
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
@[expose]
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

/-! Listing the fields of a parent instead of the parent field flattens them into the tuple. -/

/-- Triples, as the flat tuple of their three fields. -/
enc_structure eFlat : Triple where fst : encNat, snd : encBool, w : encUnary

example (t : Triple) : eFlat t = encPair encNat (encPair encBool encUnary) (t.fst, t.snd, t.w) :=
  rfl

-- The constructor rule on tuples nests the constructor of the parent.
example : ComputableInDegree (fun p : ℕ × Bool × ℕ => Triple.mk ⟨p.1, p.2.1⟩ p.2.2)
    eFlatFields eFlat 1 1 :=
  eFlat_mk_deg

-- The flattened field rules read through the parent projection.
example {α : Type} {enc : α ↪ List Bool} {f : α → Triple} (hf : ComputableInPolyTime f enc eFlat) :
    ComputableInPolyTime (fun a => Triple.mk ⟨(f a).fst, (f a).snd⟩ (f a).w) enc eFlat := by
  fun_prop

/-! A field whose type depends on an earlier field is encoded by an injective word function of the
earlier fields. -/

/-- A family of types indexed by descriptions, with injective encodings of their elements. -/
structure Family where
  /-- The descriptions. -/
  Desc : Type
  /-- The encoding of descriptions. -/
  encDesc : Desc ↪ List Bool
  /-- The type described by each description. -/
  Carrier : Desc → Type
  /-- The encoding of the elements of each type. -/
  encode : ∀ d, Carrier d → List Bool
  /-- Element encodings are injective. -/
  encode_injective : ∀ d, Function.Injective (encode d)

/-- A description and an element of the type it describes. -/
structure Element (F : Family) where
  /-- A unary size. -/
  size : ℕ
  /-- The description. -/
  desc : F.Desc
  /-- The element. -/
  elt : F.Carrier desc

/-- Elements, as their size, description and the word of the element. -/
enc_structure eElement (F : Family) : Element F where
  size : encUnary, desc : F.encDesc, elt : (F.encode desc) using (F.encode_injective desc)

example (F : Family) (x : Element F) :
    eElement F x =
      encPair encUnary (encPair F.encDesc encBits) (x.size, x.desc, F.encode x.desc x.elt) :=
  rfl

example (F : Family) {x y : Element F} (h : eElement F x = eElement F y) : x = y :=
  (eElement F).injective h

example (F : Family) {α : Type} {enc : α ↪ List Bool} {f : α → Element F}
    (hf : ComputableInPolyTime f enc (eElement F)) :
    ComputableInPolyTime (fun a => F.encode (f a).desc (f a).elt) enc encBits := by
  fun_prop

/-- An element with a second element of the same type, through a flattened parent. -/
structure ElementPair (F : Family) extends Element F where
  /-- The second element. -/
  other : F.Carrier desc

/-- Element pairs, flattening the parent: byte-compatible with a hand-written five-word tuple. -/
enc_structure eElementPair (F : Family) : ElementPair F where
  size : encUnary, desc : F.encDesc, elt : (F.encode desc) using (F.encode_injective desc),
  other : (F.encode desc) using (F.encode_injective desc)

example (F : Family) (x : ElementPair F) :
    eElementPair F x = encPair encUnary (encPair F.encDesc (encPair encBits encBits))
      (x.size, x.desc, F.encode x.desc x.elt, F.encode x.desc x.other) :=
  rfl

-- Swapping the two elements uses the dependent field rules and the dependent constructor rule.
example (F : Family) :
    ComputableInPolyTime
      (fun x : ElementPair F => (⟨⟨x.size, x.desc, x.other⟩, x.elt⟩ : ElementPair F))
      (eElementPair F) (eElementPair F) := by
  fun_prop

example (F : Family) {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {f : α → ElementPair F}
    (hf : ComputableInSpace f enc (eElementPair F) S) :
    ComputableInSpace (fun a => F.encode (f a).desc (f a).other) enc encBits S :=
  eElementPair_other_budget F hf

-- The parent projection follows from the parent's constructor rule and the flattened field rules.
example (F : Family) {α : Type} {enc : α ↪ List Bool} {f : α → ElementPair F}
    (hf : ComputableInPolyTime f enc (eElementPair F)) :
    ComputableInPolyTime (fun a => (f a).toElement) enc (eElement F) :=
  eElement_mk_polyTime F (eElementPair_size_polyTime F hf) (eElementPair_desc_polyTime F hf)
    (eElementPair_elt_polyTime F hf)

/-- An element with a second element of the same type, keeping the parent as one field. -/
structure ElementTagged (F : Family) extends Element F where
  /-- The second element. -/
  other : F.Carrier desc

/-- A dependent word may read a listed parent field through a dotted name. -/
enc_structure eElementTagged (F : Family) : ElementTagged F where
  toElement : (eElement F),
  other : (F.encode toElement.desc) using (F.encode_injective toElement.desc)

example (F : Family) (x : ElementTagged F) :
    eElementTagged F x = encPair (eElement F) encBits (x.toElement, F.encode x.desc x.other) :=
  rfl

/-- The injectivity proof may be a lambda: the command supplies its expected type. -/
enc_structure eElementLambda (F : Family) : Element F where
  size : encUnary, desc : F.encDesc,
  elt : (F.encode desc) using (fun ⦃_ _⦄ h => F.encode_injective desc h)

example (F : Family) (x : Element F) : eElementLambda F x = eElement F x := rfl

-- A parameter named like a field that a dependent word reads would be captured by the field.
/--
error: enc_structure: the parameter `desc` has the name of a field that the word of `elt` reads; rename the parameter
-/
#guard_msgs in
enc_structure eClash (F : Family) (desc : F.Desc) : Element F where
  size : encUnary, desc : F.encDesc, elt : (F.encode desc) using (F.encode_injective desc)

/-! Generated binders keep plain names, so callers may pass them by name. -/

example (p : Point) : ePoint p = ePointFields (p.x, p.y, p.z) := ePoint_apply (a := p)

-- Only the binders that collide with the parameters `γ` and `encIn` are renamed.
example (γ : Type) (encIn : γ ↪ List Bool) {α : Type} {enc : α ↪ List Bool}
    {description : α → γ} {left right : α → List Bool}
    (hd : ComputableInPolyTime description enc encIn)
    (hl : ComputableInPolyTime left enc encBits)
    (hr : ComputableInPolyTime right enc encBits) :
    ComputableInPolyTime
      (fun a => { description := description a, left := left a, right := right a })
      enc (eDescribedPairCollision γ encIn) :=
  eDescribedPairCollision_mk_polyTime γ encIn (x0 := description) (h0 := hd) (h1 := hl) (h2 := hr)

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

-- A parent is listed either as its field or as its fields, not both.
/--
error: enc_structure: the parent field `toPair` and its field `fst` are both listed; list either the parent field or its fields; the fields of `Triple` in declaration order are `fst`, `snd`, `w`
-/
#guard_msgs in
enc_structure eBoth : Triple where toPair : ePair, fst : encNat, w : encUnary

/--
error: enc_structure: missing field `snd` of `Triple`; the fields of `Triple` in declaration order are `fst`, `snd`, `w`
-/
#guard_msgs in
enc_structure eFlatMissing : Triple where fst : encNat, w : encUnary

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
