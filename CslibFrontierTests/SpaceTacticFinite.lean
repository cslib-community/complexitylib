/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Tactic.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite

/-! Finite values, decidable conditions and Boolean connectives under `space`. -/

open Turing.MultiTapeTM ComputableInSpace

namespace SpaceTacticFinite

inductive Dir where
  | left
  | stay
  | right
  deriving DecidableEq

instance : FinEnum Dir :=
  FinEnum.ofList [.left, .stay, .right] fun x => by cases x <;> decide

/-- The opposite direction. -/
def Dir.opp : Dir → Dir
  | .left => .right
  | .stay => .stay
  | .right => .left

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ} {a b : α → ℕ} {r : α → Dir}
  (ha : ComputableInSpace a enc encNat S) (hb : ComputableInSpace b enc encNat S)
  (hr : ComputableInSpace r enc (encFinEnum Dir) S) (hin : (fun x => (enc x).length) ≼ S)
include ha hb hin

-- Comparisons combined by Boolean connectives.
example : ComputableInSpace (fun x => decide (a x < b x) && !decide (a x = 0) || decide (b x = 1))
    enc encBool S := by
  space

-- A conditional on a decidable proposition, as `simp only` leaves it.
example : ComputableInSpace (fun x => if a x < b x then b x - a x else 0) enc encNat S := by
  space

-- Negated conditions.
example : ComputableInSpace (fun x => if a x ≠ b x then a x else b x) enc encNat S := by
  space

example : ComputableInSpace (fun x => if ¬a x < b x then a x else b x) enc encNat S := by
  space

include hr

-- Equality on a finite type selects a branch.
example : ComputableInSpace
    (fun x => if r x = .left then a x - 1 else if r x = .right then a x + 1 else b x)
    enc encNat S := by
  space

example : ComputableInSpace (fun x => if r x ≠ .left then a x else b x) enc encNat S := by
  space

-- The value of a finite function feeding an equality: its encoding is stated first.
example : ComputableInSpace (fun x => if (r x).opp = .left then a x else b x) enc encNat S := by
  have := budget_finite (encC := encFinEnum Dir) Dir.opp hr
  space

-- Without that statement, the intermediate encoding of `budget_finite` is undetermined.
/--
Failed to infer `(?encB✝ : Dir ↪ List Bool)` when applying theorem
`Turing.MultiTapeTM.ComputableInSpace.budget_finite`.
-/
#guard_msgs (substring := true) in
example : ComputableInSpace (fun x => if (r x).opp = .left then a x else b x) enc encNat S := by
  space

end SpaceTacticFinite
