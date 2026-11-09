/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.MassProduction.Basic
import Mathlib.Tactic.Ring

/-!
# Padding circuit mass-production bounds

Adding unused inputs preserves the mass complexity of a function with a nonempty input block.
A fixed amount of padding changes the integer Shannon scale by only a constant factor.
Consequently an eventual rational-rate bound extends to every positive input length.

## Main results

* `Cslib.Circuits.Boolean.MassProduction.massComplexity_comp_castLE`: padding preserves cost.
* `Cslib.Circuits.Boolean.MassProduction.shannonScale_le_of_le_add`: the floor-stable scale bound.
* `Cslib.Circuits.Boolean.MassProduction.MassProducesAt.allLengths`: an eventual bound holds at
  every positive input length, with one larger constant.

## References

* Adapted from MassProduction/InputSplit.lean, MassProduction/Growth.lean and
  MassProduction/Padding.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.MassProduction

/-- Padding a nonempty block by ignored tail coordinates preserves minimum weighted cost. -/
theorem massComplexity_comp_castLE {n p : ℕ} (hn : 0 < n) (hle : n ≤ p)
    (f : (Fin n → Bool) → Bool) (k : ℕ) :
    massComplexity (fun x => f (x ∘ Fin.castLE hle)) k = massComplexity f k := by
  refine le_antisymm (massComplexity_comp_wiring_le _ _) ?_
  let retract : Fin p → Fin n := fun i =>
    if h : i.val < n then ⟨i.val, h⟩ else ⟨0, hn⟩
  have h := massComplexity_comp_wiring_le (f := fun x => f (x ∘ Fin.castLE hle)) retract k
  have heq : (fun x => f ((x ∘ retract) ∘ Fin.castLE hle)) = f := by
    funext x
    apply congrArg f
    funext i
    simp [retract]
  simpa only [heq] using h

/-- Moving a coefficient outside natural division loses at most a factor two when the quotient
is nonzero. This is the rounding step in the padding argument. -/
private theorem mul_div_le {c a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    c * a / b ≤ 2 * c * (a / b) := by
  have hq : 1 ≤ a / b := (Nat.le_div_iff_mul_le hb).mpr (by simpa using hba)
  have ha : a ≤ b * (2 * (a / b)) :=
    (Nat.lt_mul_div_succ a hb).le.trans (Nat.mul_le_mul_left b (by lia))
  calc
    c * a / b ≤ c * (b * (2 * (a / b))) / b := Nat.div_le_div_right (Nat.mul_le_mul_left c ha)
    _ = 2 * c * (a / b) := by
      rw [show c * (b * (2 * (a / b))) = (2 * c * (a / b)) * b by ring,
        Nat.mul_div_cancel _ hb]

/-- Adding at most `padding` inputs changes the integer Shannon scale by a fixed factor. -/
theorem shannonScale_le_of_le_add {n p padding : ℕ} (hn : 0 < n)
    (hle : n ≤ p) (hp : p ≤ n + padding) :
    2 ^ p / p ≤ (2 * 2 ^ padding) * (2 ^ n / n) := by
  have hpow : 2 ^ p ≤ 2 ^ padding * 2 ^ n := by
    simpa only [Nat.pow_add, Nat.mul_comm] using Nat.pow_le_pow_right two_pos hp
  have hn' : n ≤ 2 ^ n :=
    (show n ≤ 2 * n by lia).trans (Nat.mul_le_pow (by decide : 2 ≠ 1) n)
  exact ((Nat.div_le_div_left hle hn).trans (Nat.div_le_div_right hpow)).trans (mul_div_le hn hn')

/-- Padding by the fixed cutoff turns an eventual bound into an all-positive-length bound. -/
theorem MassProducesAt.allLengths {numerator denominator : ℕ}
    (h : MassProducesAt numerator denominator) :
    MassProducesAtAllLengths numerator denominator := by
  obtain ⟨constant, cutoff, h⟩ := h
  refine ⟨(2 * 2 ^ cutoff) * constant, fun n hn f copies hc hb => ?_⟩
  have hle : n ≤ n + cutoff := Nat.le_add_right _ _
  have hbound := h (n + cutoff) (hn.trans_le hle) (Nat.le_add_left _ _)
    (fun x => f (x ∘ Fin.castLE hle)) copies hc
    (hb.trans (rationalCopyBudget_mono_inputs hle))
  rw [massComplexity_comp_castLE hn hle] at hbound
  refine hbound.trans ?_
  have hscale := shannonScale_le_of_le_add hn hle (le_rfl : n + cutoff ≤ n + cutoff)
  exact_mod_cast (Nat.mul_le_mul_left constant hscale).trans_eq (by ring)

end Cslib.Circuits.Boolean.MassProduction
