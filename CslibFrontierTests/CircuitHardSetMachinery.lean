/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.DepthFunctions
import CslibFrontier.Computability.Circuit.Boolean.MajorityFormula
import CslibFrontier.Computability.Circuit.Boolean.Memorize
import Mathlib.Tactic

/-! Machinery toward Lemma 6.3 of submission 865: formula majority, memorization, counting. -/

namespace CslibFrontierTests.CircuitHardSetMachinery
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Formula

/-- The majority of three input formulas computes the majority of three bits. -/
example (x : BitString 3) :
    (maj3Of (.input 0) (.input 1) (.input 2) : Formula signature 3).eval interpretation x =
      Cslib.maj3 (x 0) (x 1) (x 2) := by
  simp

/-- A majority tree of depth one over the three inputs has depth at most three. -/
example : (majTreeFormula 1 fun i : Fin (3 ^ 1) => (Formula.input (Fin.cast (by simp) i) :
    Formula signature 3)).depthWith binaryCost ≤ 0 + 3 * 1 :=
  depthWith_majTreeFormula_le 1 _ fun _ => by simp

/-- Lemma 3.7 for formulas: three equally weighted copies of the parity-free formula `x₀`, each
always correct for `f x = x 0`, give a correct formula on all of `BitString 1`. -/
example : ∃ G : Formula signature 1, (∀ x ∈ (Finset.univ : Finset (BitString 1)),
    G.eval interpretation x = x 0) ∧ G.depthWith binaryCost ≤ 0 + 3 * (5 + 1) + 3 * 1 := by
  refine exists_eq_of_forall_sum_ne_le (Ω := Fin 1) (w := fun _ => 1) (fun _ => zero_le_one)
    (by simp) (H := fun _ => .input 0) (d := 0) (fun _ => by simp) Finset.univ (fun x => x 0)
    (ε := 1 / 2) (by norm_num) (fun x _ => by simp) (m₁ := 5) (m₂ := 1) (by norm_num) (by simp)

/-- Memorizing the first bit on the single point `(true, true)`, with default `false`. -/
example : ∃ F : Formula signature 2,
    (∀ x ∈ ({fun _ => true} : Finset (BitString 2)), F.eval interpretation x = x 0) ∧
    (∀ x ∉ ({fun _ => true} : Finset (BitString 2)), F.eval interpretation x = false) ∧
    F.depthWith binaryCost ≤ Nat.clog 2 2 + Nat.clog 2 1 := by
  simpa using exists_memorize (fun x : BitString 2 => x 0) {fun _ => true} false

/-- Depth-zero formulas over one bit compute at most two functions times two, here `x₀`, `¬x₀`
and the two constants: `2 · 4 ≤ (4 · 1 + 4)^1`. -/
example : 2 * (depthFunctions 1 0).card ≤ (4 * 1 + 4) ^ 2 ^ 0 :=
  two_mul_card_depthFunctions_le 0

/-- The function of a concrete depth-one formula is a candidate of depth one. -/
example : ((Formula.input 0).and (.input 1) : Formula signature 2).eval interpretation ∈
    depthFunctions 2 1 :=
  (eval_mem_depthFunctions _ (by simp)).1

end CslibFrontierTests.CircuitHardSetMachinery
