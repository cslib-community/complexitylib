/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of separate-source correction sampling)

import Complexity.Foundations.Probability.HierarchySourceSampling
import all ComplexityTests.HierarchyCorrectionMean

/-! Unequal nonconstant sampling/stage/usage slices, a free spectator,
and positive actual output. -/
set_option linter.privateModule false
namespace SourceRegression
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
  Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

def request : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
  ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 2 [1],
    gridChannel 2 1 [2,3], gridChannel 2 3 [2,3]⟩

lemma admissible : Admissible (request HP) :=
  ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩

def horizon : Horizon 5 := ⟨2, 4, by decide, by decide⟩

/-- Source, true stage and usage have different nominal rates and different nontrivial
actual densities. Role 1 remains a free spectator in the environment. -/
theorem rates_and_densities :
    (request HP).source.rate < (request HP).terminal.rate ∧
    (request HP).usage.rate < (request HP).source.rate ∧
    (dens {σ : Environment 5 3 | (request HP).source.retains (channels 1) σ
      (SingleRegression.identifier ())} : ℝ) = 16/625 ∧
    (dens {σ : Environment 5 3 | (request HP).terminal.retains (channels 1) σ
      (SingleRegression.identifier ())} : ℝ) = 81/625 ∧
    (dens {σ : Environment 5 3 | (request HP).usage.retains (channels 1) σ
      (SingleRegression.identifier ())} : ℝ) = 1/625 := by
  rw [channel_density 1 (request HP).source 2 rfl,
    channel_density 1 (request HP).terminal 1 rfl,
    channel_density 1 (request HP).usage 3 rfl]
  norm_num [request, gridChannel, rate, side, Nat.ceilDiv_eq_add_pred_div]

/-- The true source keeps the stage marginal 81/625, rather than adopting the actual
source's 16/625 marginal. This checks the channel used by the recurrence itself. -/
theorem stage_source_density :
    (dens {a | stageSource 1 SingleRegression.identifier (request HP) (admissible HP)
      a ()} : ℝ) = 81/625 := by
  have hh := stage_channels 1 SingleRegression.identifier (request HP) (admissible HP)
    (by norm_num) SingleRegression.identifier_injective horizon (k := 1) (by decide) rfl
  have hd := hh.1.dens_X ()
  convert hd using 1
  norm_num [side, Nat.ceilDiv_eq_add_pred_div]

/-- The target uses the genuine final pilot at the stage rate. Its maximum is zero
because the actual detector rank exceeds the singleton vertex domain. -/
theorem positive_target :
    0 < HP.toHierarchyParams.correctionIter
      (stageSource 1 SingleRegression.identifier (request HP) (admissible HP))
      (splitTerminal 1 SingleRegression.identifier (request HP))
      (request HP).terminal.rate (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 1 () () := by
  erw [HP.toHierarchyParams.correctionIter_succ_apply (i := 0)]
  have hmax := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (stageSource 1 SingleRegression.identifier (request HP) (admissible HP))
    (splitTerminal 1 SingleRegression.identifier (request HP))
    (request HP).terminal.rate (fun _ _ => rate 1)
    (by simpa using SingleRegression.one_lt_J HP) HP.k
  erw [PilotTask.value_maximum_last] at hmax
  erw [hmax]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  have hraw : HP.toHierarchyParams.correctionInput
      (stageSource 1 SingleRegression.identifier (request HP) (admissible HP))
      (splitTerminal 1 SingleRegression.identifier (request HP))
      (request HP).terminal.rate (fun _ _ => rate 1) 0 () () = rate 1 := by
    change rate 1 + ∑ _ : Unit, (0:ℝ) * rate 1 = rate 1
    simp
  rw [hraw]
  change 0 < rate 1 * HP.Q (rate 1 / rate 1)
  rw [div_self (ne_of_gt (rate_pos 1))]
  exact mul_pos (rate_pos 1) (CutoffRegression.Q_one_pos HP)

/-- Positive complete actual output averaged on the actual narrower source slice,
with genuine stage raw and pilot children and actual-source preparation. -/
theorem positive_actual_mean :
    0 < (𝔼 σ ∈ ({σ : Environment 5 3 |
      (request HP).source.retains (channels 1) σ (SingleRegression.identifier ())} : Finset _),
      ((request HP).terminal.rate / (dens {σ : Environment 5 3 |
        (request HP).usage.retains (channels 1) σ (SingleRegression.identifier ())} : ℝ)) *
      correctionRequest 1 SingleRegression.identifier (request HP) (polynomialAuxCutoff4 HP.θ)
        HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊
        (fun _ => stageRaw HP 1 SingleRegression.identifier (request HP) (admissible HP)
          (fun _ _ => rate 1) 0)
        (sourcePreparation HP 1 SingleRegression.identifier (request HP) (admissible HP)
          (fun _ _ => rate 1) 0)
        (fun _ => stageMaximum HP 1 SingleRegression.identifier (request HP) (admissible HP)
          (fun _ _ => rate 1)) σ () ()) := by
  rw [source_request_mean HP 1 SingleRegression.identifier (request HP) (admissible HP)
    (by norm_num) SingleRegression.identifier_injective horizon
    (k := 1) (s := 2) (u := 3) (by decide) (by decide)
    rfl rfl rfl (fun _ _ => rate 1) (by intros; norm_num [rate])
    (by intro x; norm_num [Matrix.mulVec, dotProduct, rate])
    (by intros; rfl) HP.k_pos]
  exact positive_target HP

/-- A genuine hierarchy witness inhabits all premises of the unequal-rate positive example. -/
example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
    (request HP).source.rate < (request HP).terminal.rate ∧
      0 < HP.toHierarchyParams.correctionIter
        (stageSource 1 SingleRegression.identifier (request HP) (admissible HP))
        (splitTerminal 1 SingleRegression.identifier (request HP))
        (request HP).terminal.rate (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 1 () () := by
  let HP : FourthRootHierarchyParams 16 1 16 32 8 :=
    Classical.choice (FourthRootHierarchyParams.nonempty (by norm_num) (by norm_num))
  exact ⟨HP, (rates_and_densities HP).1, positive_target HP⟩

end
end SourceRegression
