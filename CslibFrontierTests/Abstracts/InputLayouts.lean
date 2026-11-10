/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract regression tests)

import CslibFrontierAbstracts.FormulaBoundsAbstract
import CslibFrontierAbstracts.USTCONAbstract

/-! # Input layout checks for the Andreev and undirected-connectivity abstracts -/

namespace CslibFrontierTests.Abstracts.InputLayouts

open FormulaBoundsAbstract

-- Coordinate zero is the least significant address bit.
example : tableIndex 3 ![true, true, false] = 3 := by decide

-- The first bit of the second block follows the four table bits and the first block.
example (x : Fin 10 → Bool) : blockInput (b := 2) (m := 3) x 1 0 = x 7 :=
  blockInput_eq (b := 2) (m := 3) x 1 0 7 rfl

-- Block parities are (true, false), so the answer is table entry one.
example : andreev 2 2 ![false, true, false, false, true, false, true, true] = true := by
  decide

-- Empty addresses and empty blocks both select the first table entry.
example (x : Fin 1 → Bool) : andreev 0 3 x = x 0 := rfl

example (x : Fin 4 → Bool) : andreev 2 0 x = x 0 := rfl

private def singleton : USTCONAbstract.Instance :=
  ⟨1, ⟨⟨fun _ _ => false, by simp⟩, 0, 0⟩⟩

private def edgeWithIsolatedVertex : USTCONAbstract.Instance :=
  ⟨3, ⟨⟨fun a b => decide (a.val + b.val = 1), by decide⟩, 0, 2⟩⟩

-- The smallest valid instance has a one-bit matrix and coincident endpoints.
example : USTCONAbstract.encode singleton = [true, false, false, false, false] := by decide

example : singleton ∈ USTCONAbstract.USTCON := SimpleGraph.Reachable.refl _

-- Vertices zero and one are adjacent; vertex two is isolated. Headers name endpoints zero and two.
example : USTCONAbstract.encode edgeWithIsolatedVertex =
    [true, true, true, false, false, true, true, false,
      false, true, false, true, false, false, false, false, false] := by decide

-- An endpoint rules out a zero-vertex instance.
example (I : USTCONAbstract.Instance) : 0 < I.vertexCount := Fin.pos I.source

end CslibFrontierTests.Abstracts.InputLayouts
