/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.EXP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Plain

/-! Timed deterministic reductions use the time-class API without importing padding.
The exponential-time client uses the diagonal language, which is outside `P`. -/

namespace ComplexityTests.TimeReductions

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

example {α : Type} {enc : α ↪ List Bool} {t : ℕ → ℕ} {A : Set α}
    (hA : A ∈ DTIME enc t) :
    ComputableTidilyInO (indicator A) enc encBool (fun a => t (enc a).length)
      fun a => t (enc a).length :=
  (computableInO_indicator_of_mem_DTIME hA).tidy

example {α : Type} {enc : α ↪ List Bool} {t : ℕ → ℕ} :
    DTIME enc (fun n => 2 * t n + 2) ⊆ DTIME enc t :=
  DTIME_mono_of_le_mul_add (fun _ => le_rfl)

/-- **`DTIME` under timed reductions**, for a problem outside `P`: the diagonal problem pulled back
along the linear-time map from unary numbers to words of ones stays in exponential time. -/
example : (fun n : ℕ => List.replicate n true) ⁻¹' {x | diagonal x = true} ∈ EXP encUnary := by
  obtain ⟨k, hk⟩ := mem_EXP_iff.mp setOf_diagonal_mem_EXP
  refine mem_EXP_iff.mpr ⟨k + 1, preimage_mem_DTIME (C := 2) hk
    (.of_tidy (ComputableTidilyInO.of_linear (.of_eq fun _ => rfl))) fun n => ?_⟩
  simp only [encUnary_apply, encBits_apply, List.length_replicate]
  have h₁ : n < 2 ^ n ^ (k + 1) := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_self_pow (by omega) n))
  have h₂ : 2 ^ n ^ k ≤ 2 ^ n ^ (k + 1) + 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases k with _ | k <;> simp
    · exact (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right hn (Nat.le_succ k))).trans
        (Nat.le_add_right _ _)
  omega

/--
info: 'Cslib.Complexity.preimage_mem_DTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Complexity.preimage_mem_DTIME

end ComplexityTests.TimeReductions
