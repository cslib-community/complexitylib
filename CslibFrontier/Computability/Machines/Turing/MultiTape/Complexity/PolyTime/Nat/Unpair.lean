/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Unary integer square root and unpairing in polynomial time

On unary naturals (`Turing.MultiTapeTM.encUnary`), the integer floor square root `Nat.sqrt` is
found by searching `0, …, m` for the least `s` with `m < (s + 1) * (s + 1)`, and Mathlib's inverse
pairing function `Nat.unpair : ℕ → ℕ × ℕ` follows by unfolding its definition in terms of
`Nat.sqrt`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.unary_sqrt`: `Nat.sqrt` on unary naturals.
* `Turing.MultiTapeTM.ComputableInPolyTime.unary_unpair`, `.unary_unpair'`: `Nat.unpair` on unary
  naturals.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

private def unarySqrtSearch (m : ℕ) : ℕ :=
  ((List.range (m + 1)).find? fun s => decide (m < (s + 1) * (s + 1))).getD 0

private theorem unarySqrtSearch_eq (m : ℕ) : unarySqrtSearch m = m.sqrt := by
  have hfind : ((List.range (m + 1)).find? fun s => decide (m < (s + 1) * (s + 1))) =
      some m.sqrt := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simp only [decide_eq_true_eq]; exact Nat.lt_succ_sqrt m, m.sqrt,
      by simp only [List.length_range]; exact Nat.lt_succ_of_le (Nat.sqrt_le_self m),
      List.getElem_range _, fun j hj => ?_⟩
    rw [List.getElem_range]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
    exact (Nat.mul_le_mul hj hj).trans (Nat.sqrt_le m)
  simp only [unarySqrtSearch, hfind, Option.getD_some]

/-- Integer floor square root `Nat.sqrt`, with input and output in unary. -/
@[fun_prop]
theorem unary_sqrt : ComputableInPolyTime Nat.sqrt encUnary encUnary := by
  have h : ComputableInPolyTime unarySqrtSearch encUnary encUnary := by
    unfold unarySqrtSearch
    fun_prop
  simpa only [funext unarySqrtSearch_eq] using h

/-- Mathlib's inverse pairing function `Nat.unpair`, with input and both components in unary. -/
@[fun_prop]
theorem unary_unpair :
    ComputableInPolyTime Nat.unpair encUnary (encPair encUnary encUnary) := by
  unfold Nat.unpair
  fun_prop

/-- Apply `Nat.unpair` to a computed unary value. -/
@[fun_prop]
theorem unary_unpair' {α : Type} {input : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f input encUnary) :
    ComputableInPolyTime (fun a => (f a).unpair) input (encPair encUnary encUnary) :=
  unary_unpair.comp hf

end Turing.MultiTapeTM.ComputableInPolyTime
