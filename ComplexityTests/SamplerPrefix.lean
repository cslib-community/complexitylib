/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (sampler prefix regressions)

public import Complexity.Foundations.Probability.SamplerPrefix
import Mathlib.Tactic.FinCases

/-!
# Correlated finite sampler prefixes

Two nonconstant groups use the same seed with weights one and two. Their actual prefix noise
has fourth moment 81, while the derived finite-prefix budget is 1296. No independence or
final-output error hypothesis is supplied. A second client uses a concrete conditional
component walk on a nonconstant free-bit sample.
-/

public section

namespace ComplexityTests.SamplerPrefix

open Cslib Cslib.RowCompression Cslib.RotationMap Cslib.Probability Finset
open scoped BigOperators

/-- One nonconstant raw channel and one zero channel on a single endpoint. -/
def sample (_ : Unit) (ν : Fin 2) (σ : Bool) : ℝ :=
  if ν = 0 then (if σ then 1 else -1) else 0

/-- The nonconstant, fully correlated prefix has exact positive fourth moment. -/
theorem shared_prefix_moment :
    (𝔼 σ : Bool, rowNoiseEnvelope univ (fun y ν => 3 * sample y ν σ) 0 ^ 4) = 81 := by
  simp_rw [rowNoiseEnvelope_pow_four]
  norm_num [sample, Fin.sum_univ_succ, Finset.expect_eq_sum_div_card,
    Fintype.sum_bool]

/-- Actual walk prefixes obtain a budget from centered input moments, with correlated groups. -/
theorem shared_prefix_budget :
    (𝔼 σ : Bool, rowNoiseEnvelope univ (fun y ν => 3 * sample y ν σ) 0 ^ 4) ≤ 1296 := by
  let G : RotationMap Bool Unit := ofInvolutive id (fun _ => rfl)
  have h := expect_rowNoiseEnvelope_prefix_le (univ : Finset (Fin 2)) (univ : Finset Unit)
    (fun _ => G) (fun _ => 0) (fun _ => sample)
    (fun i => if i = 0 then 1 else 2) (fun _ => 2)
    (fun i _ => by fin_cases i <;> norm_num) (by norm_num)
    (fun i _ => by
      norm_num [sample, Fin.sum_univ_succ, Finset.expect_eq_sum_div_card, Fintype.sum_bool])
  norm_num [Fin.sum_univ_succ, sample, Finset.expect_eq_sum_div_card,
    Fintype.sum_bool] at h ⊢
  exact h

/-- The mean/noise envelope covers the actual unit clipped error on a negative sampled row. -/
theorem negative_sample_clipped :
    clippedError 0 0 (sample () · false) ≤
      clippedError 0 0 (fun _ => 0) + rowNoiseEnvelope univ (sample · · false) 0 :=
  clippedError_le_mean_add_rowNoiseEnvelope univ (sample · · false) 0
    (d := 0) (v := 0) (mem_univ ()) (by norm_num)

/-- The no-channel component slice with three free bits. -/
abbrev Slice :=
  (∀ _j : Fin 0, RetentionSlice 2 3 1 1 (0 : ZMod 2)) × (Fin 3 → ZMod 2)

/-- A nonconstant free-bit sample in the actual component environment. -/
def componentSample (_ : Unit) (ν : Fin 2) (A : Slice) : ℝ :=
  if ν = 0 ∧ A.2 0 ≠ 0 then 1 else 0

/-- The sample really changes on two concrete component environments. -/
theorem componentSample_nonconstant :
    componentSample () 0 (fun j => Fin.elim0 j, fun _ => 0) ≠
      componentSample () 0 (fun j => Fin.elim0 j, fun _ => 1) := by
  norm_num [componentSample]

/-- The positive-length conditional component walk controls the actual row noise. -/
theorem component_noise_budget :
    (𝔼 A, rowNoiseEnvelope (univ : Finset Unit)
      (fun z ν => ((((ofPerms (componentMove 3 2 (fun _ : Fin 0 => 2)
        (fun _ => 1))).lazy.reindex
        (componentEquiv 2 (fun _ => by decide) (fun _ => 0)).symm).walk ^ 2)
          (componentSample z ν) A))
      (fun z ν => 𝔼 B, componentSample z ν B) ^ 4) ≤
        2 * (1 - 1 / 12607488) ^ 2 *
          ∑ z : Unit, ∑ ν : Fin 2, 𝔼 A,
            (componentSample z ν A - 𝔼 B, componentSample z ν B) ^ 4 := by
  have h := expect_rowNoiseEnvelope_componentMove_le (P := fun _ : Fin 0 => 2)
    (L := fun _ => 1) (M := 2) (by decide : 3 ≤ 3) (fun _ => by decide)
    (fun _ => 0) (univ : Finset Unit) componentSample 1
  norm_num at h ⊢
  exact h

end ComplexityTests.SamplerPrefix
