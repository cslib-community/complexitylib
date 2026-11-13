/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.HardSet
import Mathlib.Tactic

/-! Lemma 6.3 of submission 865 on the first bit and on a deep function. -/

namespace CslibFrontierTests.CircuitHardSet
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Formula

/-- Lemma 6.3 at `t = 0` for the first bit: the input formula agrees everywhere, so the assumption
holds and the lemma bounds the formula depth. -/
example : formulaDepth (fun x : BitString 2 => x 0) ≤
    0 + 4 * Nat.clog 2 2 + Nat.clog 2 (4 * 2 + 4) + 32 :=
  formulaDepth_le_add_of_forall_exists_agree _ 0 fun S _ => ⟨.input 0, by simp, by
    simp only [eval_input, Finset.filter_true_of_mem fun _ _ => trivial]
    omega⟩

private theorem pow_lt_two_mul_two_pow {a b c : ℕ} (ha : a ≤ 2 ^ 9) (hbc : 9 * b ≤ c) :
    a ^ b < 2 * 2 ^ c := by
  have h₁ : a ^ b ≤ 2 ^ c :=
    (Nat.pow_le_pow_left ha b).trans ((pow_mul 2 9 b).symm.le.trans
      (Nat.pow_le_pow_right two_pos hbc))
  have h₂ : 0 < 2 ^ c := pow_pos two_pos c
  omega

/-- **A nonvacuous consequence.** Some function on `80` bits has a nonempty set `S` on which no
formula of depth `0` (a literal or a constant, up to free negations) agrees with it on `2|S|/3`
points. The function has formula depth above `69 = 0 + 4 ⌈log₂ 80⌉ + ⌈log₂ 324⌉ + 32` by
counting, so the contrapositive of Lemma 6.3 applies. -/
example : ∃ g : BooleanFunction 80, ∃ S : Finset (BitString 80), S.Nonempty ∧
    ∀ F : Formula signature 80, F.depthWith binaryCost ≤ 0 →
      3 * (S.filter fun x => F.eval interpretation x = g x).card < 2 * S.card := by
  obtain ⟨g, hg⟩ := exists_lt_formulaDepth (n := 80) (t := 69)
    (pow_lt_two_mul_two_pow (by norm_num) (by norm_num))
  refine ⟨g, ?_⟩
  by_contra hno
  push Not at hno
  have h := formulaDepth_le_add_of_forall_exists_agree g 0 fun S hS => by
    obtain ⟨F, hF, hagree⟩ := hno S hS
    exact ⟨F, hF, hagree⟩
  have h80 : Nat.clog 2 80 = 7 := by decide
  have h324 : Nat.clog 2 (4 * 80 + 4) = 9 := by decide
  omega

end CslibFrontierTests.CircuitHardSet
