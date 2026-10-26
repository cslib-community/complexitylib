/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Pure binary-counted iteration states

The existing counter transition, iteration law and arithmetic bound are moved unchanged from the
legacy binary calculus. They store a binary counter with the current state, not a unary list.
-/

public section
namespace Turing.MultiTapeTM.Internal.BinaryCounter

variable {β : Type} [Inhabited β]

/-- A round of the counted iteration: stop at zero, otherwise count down and apply `step`. -/
@[expose] public def countStep (step : β → β) : Option (ℕ × β) → Option (ℕ × β)
  | some (i + 1, b) => some (i, step b)
  | _ => none

lemma countStep_eq (step : β → β) (o : Option (ℕ × β)) : countStep step o =
    if o.isSome && !decide ((o.getD default).1 = 0) then
      some ((o.getD default).1 - 1, step (o.getD default).2) else none := by
  rcases o with _ | ⟨_ | i, b⟩ <;> rfl

omit [Inhabited β] in
lemma iterate_countStep (step : β → β) (t : ℕ) (b : β) {k : ℕ} (hk : k ≤ t) :
    (countStep step)^[k] (some (t, b)) = some (t - k, step^[k] b) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (by omega), show t - k = t - (k + 1) + 1 by omega,
      countStep, Function.iterate_succ_apply']

lemma sum_le {c₀ c₁ k k' A M X Y : ℕ} (hX : X ≤ k * (M + 1)) (hY : Y ≤ c₀ * (A + 1)) :
    c₀ * (A + 1) + X + c₁ * (Y + 1) ≤ (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) := by
  have h₁ : c₁ * (Y + 1) ≤ c₁ * (c₀ + 1) * (A + M + 1) :=
    calc c₁ * (Y + 1) ≤ c₁ * (c₀ * (A + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ c₁ * ((c₀ + 1) * (A + M + 1)) := Nat.mul_le_mul_left _ (by nlinarith)
      _ = _ := by ring
  have h₂ : X ≤ k * (A + M + 1) := hX.trans (Nat.mul_le_mul_left _ (by omega))
  have h₃ : c₀ * (A + 1) ≤ c₀ * (A + M + 1) := Nat.mul_le_mul_left _ (by omega)
  have : (c₀ + c₁ * (c₀ + 1) + k + k') * (A + M + 1) = c₀ * (A + M + 1) +
      c₁ * (c₀ + 1) * (A + M + 1) + k * (A + M + 1) + k' * (A + M + 1) := by ring
  omega


theorem iterate_sub_one (k n : ℕ) : (· - 1)^[k] n = n - k := Nat.pred_iterate n k

end Turing.MultiTapeTM.Internal.BinaryCounter
