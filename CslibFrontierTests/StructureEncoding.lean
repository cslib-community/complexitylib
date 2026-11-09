/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

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

end CslibFrontierTests.StructureEncoding
