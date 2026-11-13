/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.NaturalProperty

/-!
# Tests: learners yield natural properties

A toy learner on `n` bits that makes no queries and outputs the constant `false`. It learns the
class `{fun _ => false}` exactly, with one seed. Its low-agreement property at threshold `1`
excludes the constant, holds for at least half of all functions, and is decided from truth tables
by a small circuit. Asymptotically it is `P/poly`-natural and useful against every class of
languages whose slices are eventually constant `false`.
-/

namespace CslibFrontierTests.LearningNaturalProperty

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.NaturalProof
  Cslib.MachineLearning.UniformLearning Filter

variable {n : ℕ}

/-- Make no queries and output the constant `false`. -/
private noncomputable def zeroLearner : QueryLearner (Fin n) Unit :=
  QueryLearner.ofNonadaptive (fun _ => []) fun _ _ _ => false

private theorem eval_zeroLearner (f : BooleanFunction n) :
    (zeroLearner ()).eval f = fun _ => false :=
  QueryLearner.eval_ofNonadaptive (fun _ _ _ _ => rfl) f ()

/-- The toy learner has no queries and a circuit with one gate: a constant. -/
private theorem hasCircuit_zeroLearner : (zeroLearner (n := n)).HasCircuit 0 1 :=
  QueryLearner.hasCircuit_ofNonadaptive (fun _ _ _ _ => rfl)
    fun _ => ⟨Fin.elim0, fun _ => false, (Synthesis.const false).complexity_le, fun _ _ => rfl⟩

/-- The toy learner learns the constant exactly, with probability one. -/
private theorem learns_zeroLearner :
    (zeroLearner (n := n)).Learns (Cslib.Probability.PMF.uniformOfFintype Unit)
      {fun _ => false} 0 0 := by
  rw [QueryLearner.learns_iff]
  rintro f rfl
  simp [eval_zeroLearner]

private theorem queriesAtMost_zeroLearner : (zeroLearner (n := n)).QueriesAtMost 0 :=
  fun ω => QueryLearner.depth_ofNonadaptive_le _ _ ω

/-- **Usefulness.** The constant is not in the property. -/
example : (fun _ => false) ∉ (zeroLearner (n := n)).lowAgreement ((1 - 0) * (1 - 0)) :=
  QueryLearner.notMem_lowAgreement learns_zeroLearner zero_le_one le_rfl rfl

/-- **Largeness.** At least `1 - (1 / 2 + 0 / 2 ^ (n + 1)) = 1 / 2` of all functions are in the
property. -/
example [DecidablePred (· ∈ (zeroLearner (n := n)).lowAgreement 1)] :
    (1 / 2 : ℝ) ≤ (Finset.dens {g | g ∈ (zeroLearner (n := n)).lowAgreement 1} : ℝ) := by
  have h := QueryLearner.sub_le_dens_lowAgreement (A := zeroLearner (n := n))
    queriesAtMost_zeroLearner le_rfl
  norm_num at h
  convert h using 1

/-- **Asymptotically natural and useful.** -/
example {Λ : Set (Language Bool)} (hΛ : ∀ L ∈ Λ, ∀ᶠ n in atTop, L.slice n = fun _ => false) :
    IsNatural PPoly (fun n => (zeroLearner (n := n)).lowAgreement ((1 - 0) * (1 - 0))) ∧
      IsUseful Λ fun n => (zeroLearner (n := n)).lowAgreement ((1 - 0) * (1 - 0)) := by
  refine ⟨isNatural_PPoly_lowAgreement (q := fun _ => 0) (t := fun _ => 1 + 7) (c := 3)
    (fun n => ?_) (fun n => ?_) (fun n => hasCircuit_zeroLearner.hasCircuitTests)
    (fun _ => ⟨le_rfl, zero_le_one⟩) (fun _ => le_rfl) ?_,
    isUseful_lowAgreement (Eventually.of_forall fun n => learns_zeroLearner)
      (fun _ => zero_le_one) (fun _ => le_rfl) hΛ⟩
  · simp only [Fintype.card_unit]
    exact Nat.one_le_two_pow
  · calc 1 + 7 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * (n + 1)) := Nat.pow_le_pow_right two_pos (by omega)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h : (2 : ℝ) ≤ 2 ^ (3 * n) := by
      calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ (3 * n) := pow_le_pow_right₀ one_le_two (by omega)
    have h' : ((2 : ℝ) ^ (3 * n))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    norm_num
    linarith

end CslibFrontierTests.LearningNaturalProperty
