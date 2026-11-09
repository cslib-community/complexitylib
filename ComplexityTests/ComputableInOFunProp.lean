/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp

/-!
# `fun_prop` for bounds up to constants

`fun_prop` assembles `Turing.MultiTapeTM.ComputableInO` certificates with composite bounds: the
projections of nested pairs, a case distinction on `Option.isSome`, and `Option.getD`. One `mono`
step then compares the assembled bounds with the intended ones.
-/

@[expose] public section

open Turing.MultiTapeTM

namespace ComplexityTests.ComputableInOFunProp

variable {enc : ℕ ↪ List Bool}

/-- The encoding of the test inputs. -/
abbrev eIn : (ℕ × Option ℕ) × ℕ ↪ List Bool := encPair (encPair enc (encOption enc)) enc

-- Projections of nested pairs keep the bounds of the projected pair.
example : ComputableInO (fun p : (ℕ × Option ℕ) × ℕ => (p.2, p.1.1)) (eIn (enc := enc))
    (encPair enc enc) (fun p => (eIn (enc := enc) p).length + (eIn (enc := enc) p).length)
    fun p => (eIn (enc := enc) p).length + (eIn (enc := enc) p).length := by
  fun_prop

-- A default for a projected option keeps the bounds of the projection.
example (d : ℕ) : ComputableInO (fun p : (ℕ × Option ℕ) × ℕ => p.1.2.getD d) (eIn (enc := enc))
    enc (fun p => (eIn (enc := enc) p).length) fun p => (eIn (enc := enc) p).length := by
  fun_prop

-- A case distinction adds the bounds of the test and of the branch taken.
example (d : ℕ) : ComputableInO
    (fun p : (ℕ × Option ℕ) × ℕ => if p.1.2.isSome then (p.1.2.getD d, p.2) else (p.2, d))
    (eIn (enc := enc)) (encPair enc enc)
    (fun p => (eIn (enc := enc) p).length + if p.1.2.isSome then
      (eIn (enc := enc) p).length + (eIn (enc := enc) p).length
      else (eIn (enc := enc) p).length + (eIn (enc := enc) p).length)
    fun p => (eIn (enc := enc) p).length + if p.1.2.isSome then
      (eIn (enc := enc) p).length + (eIn (enc := enc) p).length
      else (eIn (enc := enc) p).length + (eIn (enc := enc) p).length := by
  fun_prop

-- With unknown bounds, `fun_prop` assembles them, and one `mono` step reaches linear bounds.
example (d : ℕ) : ComputableInO
    (fun p : (ℕ × Option ℕ) × ℕ => if p.1.2.isSome then (p.1.2.getD d, p.2) else (p.2, d))
    (eIn (enc := enc)) (encPair enc enc) (fun p => (eIn (enc := enc) p).length)
    fun p => (eIn (enc := enc) p).length := by
  refine .mono (by fun_prop) 3 (fun p => ?_) fun p => ?_ <;> split_ifs <;> omega

/-- A certificate with a nonlinear bound, used through composition. -/
theorem square_inO {g : ℕ → ℕ} (h : ComputableInO g enc enc
    (fun n => (enc n).length * (enc n).length) fun n => (enc n).length) :
    ComputableInO (fun p : (ℕ × Option ℕ) × ℕ => (g p.1.1, p.2)) (eIn (enc := enc))
      (encPair enc enc) (fun p => ((eIn (enc := enc) p).length + 1) ^ 2)
      fun p => (eIn (enc := enc) p).length := by
  refine .mono (by fun_prop) 4 (fun p => ?_) fun p => ?_
  all_goals
    have h₁ : (enc p.1.1).length ≤ (eIn (enc := enc) p).length := by
      simp only [eIn, length_encPair]; omega
  · have := Nat.mul_le_mul h₁ h₁
    nlinarith
  · omega

end ComplexityTests.ComputableInOFunProp
