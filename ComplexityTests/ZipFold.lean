/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (tests of `zipFold`)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold

/-! Tests of `zipFold`: what it computes, and that its cost theorem applies to a concrete walk. -/

namespace ComplexityTests.ZipFold

open Turing.MultiTapeTM

/-! `zipFold` pads or truncates, as its function decides at a missing partner. -/

-- Keeping an element without a partner pads with the rest of the first list.
example : zipFold (fun (_ : Unit) (a : ℕ) (b : Option ℕ) => some (a + b.getD 0)) ()
    [1, 2, 3] [10] = [11, 2, 3] := by decide

-- Dropping it truncates to the shorter list, as `List.zipWith` does.
example : zipFold (fun (_ : Unit) (a : ℕ) (b : Option ℕ) => b.map (a + ·)) ()
    [1, 2, 3] [10] = [11] := by decide

-- A walk that keeps every element reads the second list by index.
example : zipFold (fun (_ : Unit) (a : ℕ) (b : Option ℕ) => some (a + b.getD 0)) () [1, 2] [10] =
    [1, 2].mapIdx fun i a => a + ([10][i]?).getD 0 :=
  zipFold_some (fun _ a b => a + b.getD 0) () _ _

/-! The linear cost theorem applies: copying the first list while walking along the second. -/

private theorem zipFold_keep (p : Bool) (l r : List Bool) :
    zipFold (fun (_ : Bool) (a : Bool) (_ : Option Bool) => some a) p l r = l := by
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => simp [zipFold, ih]

example : ComputableInO
    (fun q : Bool × List Bool × List Bool =>
      zipFold (fun (_ : Bool) (a : Bool) (_ : Option Bool) => some a) q.1 q.2.1 q.2.2)
    (encPair encBool (encPair (encList encBool) (encList encBool))) (encList encBool)
    (fun q => (q.2.1.length + 1) *
      ((encPair encBool (encPair (encList encBool) (encList encBool)) q).length + 1))
    fun q => (encPair encBool (encPair (encList encBool) (encList encBool)) q).length := by
  refine ComputableInO.zipFold ?_ 1 fun q i => ?_
  · exact ((ComputableInDegree.optionSome (enc₁ := encBool)
      (enc := encOption encBool)).inO_one.comp_linear
        (ComputableInO.snd encBool (encPair encBool (encOption encBool))).fst').mono 8
      (fun q => by simp only [length_encPair]; omega) fun q => by
        simp only [length_encPair]; omega
  · have := length_encList_take_le encBool q.2.1 i
    rw [zipFold_keep]
    simp only [length_encPair]
    omega

end ComplexityTests.ZipFold
