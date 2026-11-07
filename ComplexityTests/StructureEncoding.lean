/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Tests of `enc_structure`. -/

namespace ComplexityTests.StructureEncoding

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

/-! The rules assemble programs over the fields, at each level of the calculus. -/

example : ComputableInDegree (fun p : Point => Point.mk p.x p.y p.z) ePoint ePoint 1 1 := by
  fun_prop (disch := lia)

-- Reading fields and rebuilding the structure, with the bounds checked once.
example : ComputableInO (fun p : Point => Point.mk p.x p.y p.z) ePoint ePoint
    (fun p => 8 * ((ePoint p).length + 1)) fun p => 8 * ((ePoint p).length + 1) := by
  refine .mono (by fun_prop) 16 (fun p => ?_) fun p => ?_ <;>
  · simp only [ePoint_apply, length_encPair]
    omega

example {α : Type} {input : α ↪ List Bool} {p : α → Point}
    (hp : ComputableInPolyTime p input ePoint) :
    ComputableInPolyTime (fun a => Point.mk (p a).x (p a).y (p a).z) input ePoint := by
  fun_prop

/-- A parametric structure. -/
structure Tagged (C : Type) where
  /-- A unary tag. -/
  tag : ℕ
  /-- The payload. -/
  payload : C

namespace Tagged

/-! An explicit binder stays an explicit argument of the encoding. -/

/-- Tagged values, with the encoding of the payload as a parameter. -/
enc_structure encoding {C : Type} (enc : C ↪ List Bool) : Tagged C where
  tag : encUnary, payload : enc

end Tagged

example {C : Type} (enc : C ↪ List Bool) (t : Tagged C) :
    Tagged.encoding enc t = Tagged.encodingFields enc (t.tag, t.payload) := rfl

section

open scoped Tagged

-- The rules are available outside the namespace after `open scoped`.
example {α C : Type} {input : α ↪ List Bool} {enc : C ↪ List Bool} {t : α → Tagged C}
    (ht : ComputableInPolyTime t input (Tagged.encoding enc)) :
    ComputableInPolyTime (fun a => (t a).payload) input enc := by
  fun_prop

end

/-- A structure in a public API. -/
structure Labelled where
  /-- A unary label. -/
  label : ℕ

/-- Labelled values, with rules available everywhere. -/
global enc_structure encLabelled : Labelled where label : encUnary

end ComplexityTests.StructureEncoding

namespace ComplexityTests

-- Outside the namespace, without `open scoped`.
example {α : Type} {input : α ↪ List Bool} {l : α → StructureEncoding.Labelled}
    (hl : Turing.MultiTapeTM.ComputableInPolyTime l input StructureEncoding.encLabelled) :
    Turing.MultiTapeTM.ComputableInPolyTime (fun a => StructureEncoding.Labelled.mk (l a).label)
      input StructureEncoding.encLabelled := by
  fun_prop

end ComplexityTests

namespace ComplexityTests.StructureEncoding

open Turing.MultiTapeTM

/-! An encoding built from noncomputable parts is declared as such. -/

/-- A pair of a finite value and a number. -/
structure FinitePart (α : Type) where
  /-- The finite value. -/
  value : α
  /-- The number. -/
  count : ℕ

/-- Finite parts, with the value by its rank. -/
noncomputable enc_structure encFinitePart {α : Type} [Finite α] : FinitePart α where
  value : (encFinite α), count : encUnary

end ComplexityTests.StructureEncoding
