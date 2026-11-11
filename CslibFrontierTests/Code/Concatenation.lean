/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.Code.Concatenation
import CslibFrontier.Foundations.Data.Code.ReedSolomon
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests: concatenated codes

The Reed–Solomon code of dimension two over `ZMod 5`, of minimum distance four, concatenated with
an inner binary code of length four that encodes the five letters as words of even weight, at
pairwise distance two: a binary code of length twenty and minimum distance at least eight. The
distance of two concatenated words is the sum over their blocks.
-/

namespace CslibFrontierTests.Code.Concatenation

open Cslib Cslib.Code

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The five points of `ZMod 5`. -/
private def points5 : Fin 5 → ZMod 5 := fun i => (i : ℕ)

private theorem minDist_rs : minDist (reedSolomon points5 2 : Set (Fin 5 → ZMod 5)) = 4 :=
  minDist_reedSolomon (by decide) (by norm_num) (by simp)

/-- The inner code: the five letters as binary words of length four and even weight. -/
private def inner : ZMod 5 → Fin 4 → Bool :=
  ![![false, false, false, false], ![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false]]

private theorem inner_dist : ∀ a b, a ≠ b → 2 ≤ hammingDist (inner a) (inner b) := by
  decide

example : Function.Injective (concat (ι := Fin 5) inner) :=
  concat_injective fun a b h => by_contra fun hab => by
    have := inner_dist a b hab
    rw [h, hammingDist_self] at this
    omega

/-- **Concatenation multiplies distances**: `4 * 2 = 8`. -/
example : (8 : ℕ∞) ≤
    minDist (concat inner '' (reedSolomon points5 2 : Set (Fin 5 → ZMod 5))) :=
  le_minDist_image_concat (dOut := 4) minDist_rs.ge inner_dist

/-- The distance of concatenated words is the sum over the blocks. -/
example (c c' : Fin 5 → ZMod 5) :
    hammingDist (concat inner c) (concat inner c') =
      ∑ i, hammingDist (inner (c i)) (inner (c' i)) :=
  hammingDist_concat inner c c'

end CslibFrontierTests.Code.Concatenation
