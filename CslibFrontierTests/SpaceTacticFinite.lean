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

/-- A finite function of a pair of finite values. -/
def g2 : Dir × Bool → Bool
  | (.left, b) => b
  | _ => false

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

-- `≤`, `∧` and `∨` in a condition.
example : ComputableInSpace (fun x => if a x ≤ b x ∧ b x ≠ 0 then b x - a x else 0)
    enc encNat S := by
  space

example : ComputableInSpace (fun x => if a x = 0 ∨ b x ≤ a x then a x else b x) enc encNat S := by
  space

include hr

-- Equality on a finite type selects a branch.
example : ComputableInSpace
    (fun x => if r x = .left then a x - 1 else if r x = .right then a x + 1 else b x)
    enc encNat S := by
  space

example : ComputableInSpace (fun x => if r x ≠ .left then a x else b x) enc encNat S := by
  space

-- The value of a finite function feeding an equality passes through the canonical encoding.
example : ComputableInSpace (fun x => if (r x).opp = .left then a x else b x) enc encNat S := by
  space

-- A finite function of a finite value, as a component of the argument of another finite function:
-- the encoding of `(r x).opp` is undetermined.
/--
Failed to infer `(?encB✝ : Dir ↪ List Bool)` when applying theorem
`Turing.MultiTapeTM.ComputableInSpace.budget_finite`.
-/
#guard_msgs (substring := true) in
example : ComputableInSpace (fun x => g2 ((r x).opp, decide (a x = 0))) enc encBool S := by
  space

-- Stating the encoding of that component first closes the goal.
example : ComputableInSpace (fun x => g2 ((r x).opp, decide (a x = 0))) enc encBool S := by
  have := budget_finite (encC := encFinEnum Dir) Dir.opp hr
  space

omit ha hb hin hr

-- A component of a value encoded as one finite value. `space` keeps `encFinEnum` folded, so the
-- pair rule fails at once instead of enumerating `Bool × Fin 64` to the recursion limit.
example {f : α → Bool × Fin 64} (hf : ComputableInSpace f enc (encFinEnum (Bool × Fin 64)) S) :
    ComputableInSpace (fun x => !(f x).1) enc encBool S := by
  space

example {f : α → Bool × Fin 64} (hf : ComputableInSpace f enc (encFinEnum (Bool × Fin 64)) S) :
    ComputableInSpace (fun x => (f x).2) enc (encFinEnum (Fin 64)) S := by
  space

-- A test on a component of the head of a list of finite pairs.
example {l : α → List (Dir × Bool)}
    (hl : ComputableInSpace l enc (encList (encFinEnum (Dir × Bool))) S) :
    ComputableInSpace (fun x => decide (((l x).headD (.stay, false)).1 = .left) ||
      ((l x).headD (.stay, false)).2) enc encBool S := by
  space

end SpaceTacticFinite
