/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual shared-midpoint means)
import Complexity.Foundations.Probability.HierarchySharedMidpoint
import all ComplexityTests.HierarchySourceSampling

/-! Nonconstant shared-midpoint product on four actual roles: narrower old source,
midpoint, terminal with narrower usage, and a free spectator. All suffixes are nonempty.
The correction and dense children are the actual evaluators with genuine preparation. -/
set_option linter.privateModule false
namespace SharedMidpointRegression
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
  Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

def left : HierarchyTask.Request HP.k (Fin 4) (ZMod 5) :=
  ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 2 [1],
    gridChannel 1 1 [2,3], gridChannel 1 1 [2,3]⟩

def right : HierarchyTask.Request HP.k (Fin 4) (ZMod 5) :=
  ⟨.baseNormalized 0 0, gridChannel 1 1 [2,3],
    gridChannel 2 1 [4], gridChannel 2 2 [4]⟩

lemma left_admissible : Admissible (left HP) := ⟨by change (0 : Fin 4) ≠ 1; decide, rfl, rfl⟩
lemma right_admissible : Admissible (right HP) := ⟨by change (1 : Fin 4) ≠ 2; decide, rfl, rfl⟩

def endpoint (A : FrameChannel 5 4 1) : Prop :=
  coordinate 1 (gridChannel (2 : Fin 4) 2 [4]) A 0

/-- Actual source, midpoint, terminal-usage densities are nontrivial and unequal. -/
example :
    (dens {σ : Environment 5 4 | (left HP).source.retains (channels 1) σ 0} : ℝ) = 16/625 ∧
    (dens {σ : Environment 5 4 | (left HP).terminal.retains (channels 1) σ 0} : ℝ) = 81/625 ∧
    (dens {σ : Environment 5 4 | (right HP).usage.retains (channels 1) σ 0} : ℝ) = 16/625 := by
  rw [channel_density 1 (left HP).source 2 rfl,
    channel_density 1 (left HP).terminal 1 rfl, channel_density 1 (right HP).usage 2 rfl]
  norm_num [side, Nat.ceilDiv_eq_add_pred_div]

/-- The canonical genuine first correction is evaluated, including the final pilot. -/
lemma correction_one :
    HP.toHierarchyParams.correctionIter (canonicalChannel SingleRegression.identifier (rate 1))
      (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1)
      (fun _ _ => rate 1 : Matrix Unit Unit ℝ) 1 () () = rate 1 * HP.Q 1 := by
  erw [HP.toHierarchyParams.correctionIter_succ_apply (i := 0)]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel SingleRegression.identifier (rate 1))
    (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1)
    (fun _ _ => rate 1 : Matrix Unit Unit ℝ)
    (by simpa using SingleRegression.one_lt_J HP) HP.k
  erw [PilotTask.value_maximum_last] at hm
  erw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  change rate 1 * HP.Q ((rate 1 + ∑ _ : Unit, (0:ℝ) * rate 1) / rate 1) = _
  simp [div_self (ne_of_gt (rate_pos 1))]

/-- Complete actual product mean, with literal midpoint divisor 81/625 and unit
endpoint importance, at distinct source/midpoint/terminal roles and one free spectator. -/
theorem actual_product_mean :
    (𝔼 σ ∈ ({σ : Environment 5 4 |
      (left HP).source.retains (channels 1) σ 0 ∧ endpoint (σ 2)} : Finset _),
      (625/1296 : ℝ) *
        sourceChild HP 1 SingleRegression.identifier (left HP) (left_admissible HP)
          (fun _ _ => rate 1) 0 σ () () * (1/16) *
        denseChild 1 SingleRegression.identifier (right HP) cutoff (fun _ => 1) gate 66
          (fun _ _ => rate 1) σ () ()) = HP.Q 1 / 256 := by
  have hh := sourceChild_mul_denseChild_mean HP 1 SingleRegression.identifier
    (left HP) (left_admissible HP) (right HP) (right_admissible HP)
    rfl rfl (by change (0 : Fin 4) ≠ 2; decide)
    (by change (1 : Fin 4) ≠ 2; decide) (by norm_num) SingleRegression.identifier_injective
    SourceRegression.horizon (k := 1) (s := 2) (b := 1) (u := 2)
    (by decide) (by decide) rfl rfl (by decide) rfl rfl
    (fun _ _ => rate 1) (by intros; exact (rate_pos 1).le)
    (by intro x; norm_num [Matrix.mulVec, dotProduct, rate]) (by intros; rfl)
    HP.k_pos cutoff (fun _ => 1) gate 66 endpoint () () () (fun _ h => h)
    (fun _ _ => rfl) gate_nonneg gate_le_one (η := 1) (by norm_num)
    (fun _ h => gate_one h) (by norm_num)
  simp only [show (left HP).terminal.rate = rate 1 from rfl, zero_add] at hh
  rw [correction_one HP] at hh
  have hu : (dens {A | splitUsage 1 SingleRegression.identifier (right HP) A ()} : ℝ) =
      16/625 := by
    rw [split_usage_density 1 SingleRegression.identifier (right HP) (u := 2) rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  have heq : endpoint = fun A => splitUsage 1 SingleRegression.identifier (right HP) A () := rfl
  have hd : (dens {A | endpoint A} : ℝ) = 16/625 := by rw [heq]; exact hu
  rw [channel_density 1 (left HP).terminal 1 rfl,
    channel_density 1 (right HP).usage 2 rfl] at hh
  rw [dens_filter_pi_eval (right HP).terminal.role endpoint] at hh
  have hcut : cutoff (rate 1 / rate 1) = 1 := by
    rw [div_self (rate_pos 1).ne']
    exact polynomialSwitch4_of_ge (by norm_num) le_rfl
  simp only [show (right HP).terminal.rate = rate 1 from rfl, hcut, mul_one] at hh
  norm_num [side, Nat.ceilDiv_eq_add_pred_div, hd, rate, SingleRegression.identifier] at hh ⊢
  convert hh using 1
  · apply expect_congr
    · ext σ
      rfl
    · intro σ _
      ring
  · ring

example : 0 < HP.Q 1 / 256 := div_pos (CutoffRegression.Q_one_pos HP) (by norm_num)

/-- The actual right request has reset the whole tuple, including its copy suffix. -/
example : (right HP).source = (left HP).terminal ∧
    (right HP).source.suffix ≠ (left HP).source.suffix := by
  exact ⟨rfl, by change ([2,3] : List (ZMod 5)) ≠ [1]; decide⟩

/-- A free spectator and the reset midpoint can vary while the dense value is fixed. -/
example (σ τ : Environment 5 4) (ht : σ 2 = τ 2) :
    denseChild 1 SingleRegression.identifier (right HP) cutoff (fun _ => 1) gate 66
      (fun _ _ => rate 1) σ () () =
    denseChild 1 SingleRegression.identifier (right HP) cutoff (fun _ => 1) gate 66
      (fun _ _ => rate 1) τ () () := by
  apply denseChild_terminal 1 SingleRegression.identifier (right HP) (right_admissible HP)
    cutoff (fun _ => 1) gate 66 (fun _ _ => rate 1) σ τ ht
  exact source_nonempty 1 SingleRegression.identifier (right HP) (right_admissible HP)
    (by norm_num) SingleRegression.identifier_injective SourceRegression.horizon
    (s := 1) (by decide) rfl ()

/-- Zero dense cutoff gives a zero actual product, even with the positive genuine left
correction and the same nonempty source/terminal events. -/
example (σ : Environment 5 4) :
    sourceChild HP 1 SingleRegression.identifier (left HP) (left_admissible HP)
      (fun _ _ => rate 1) 0 σ () () *
    denseChild 1 SingleRegression.identifier (right HP) (fun _ => 0) (fun _ => 1) gate 66
      (fun _ _ => rate 1) σ () () = 0 := by
  have hz := source_nonempty 1 SingleRegression.identifier (right HP) (right_admissible HP)
    (by norm_num) SingleRegression.identifier_injective SourceRegression.horizon
    (s := 1) (by decide) rfl ()
  rw [denseChild_eq 1 SingleRegression.identifier (right HP) (right_admissible HP)
    (fun _ => 0) (fun _ => 1) gate 66 (fun _ _ => rate 1) σ () () hz]
  simp [denseAtom]

/-- The genuine full-Ω product is nonconstant: a missing midpoint kills it, while
its complete conditional mean above is strictly positive. No second seed is introduced. -/
example : ¬ ∃ c : ℝ, ∀ σ : Environment 5 4,
    (625/1296 : ℝ) *
      sourceChild HP 1 SingleRegression.identifier (left HP) (left_admissible HP)
        (fun _ _ => rate 1) 0 σ () () * (1/16) *
      denseChild 1 SingleRegression.identifier (right HP) cutoff (fun _ => 1) gate 66
        (fun _ _ => rate 1) σ () () = c := by
  have hd : (dens {σ : Environment 5 4 |
      (left HP).terminal.retains (channels 1) σ 0} : ℝ) = 81/625 := by
    rw [channel_density 1 (left HP).terminal 1 rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  have hmiss : ∃ σ : Environment 5 4,
      ¬ (left HP).terminal.retains (channels 1) σ 0 := by
    by_contra hn
    have hall : ∀ σ : Environment 5 4,
        (left HP).terminal.retains (channels 1) σ 0 := by simpa using hn
    have he : ({σ : Environment 5 4 |
        (left HP).terminal.retains (channels 1) σ 0} : Finset _) = univ := by
      ext σ
      simp [hall σ]
    rw [he] at hd
    norm_num at hd
  obtain ⟨σ, hσ⟩ := hmiss
  have hz : sourceChild HP 1 SingleRegression.identifier (left HP) (left_admissible HP)
      (fun _ _ => rate 1) 0 σ () () = 0 := by
    unfold sourceChild
    unfold correctionRequest
    rw [dite_eq_left (left_admissible HP)]
    dsimp only
    unfold CorrectionRowRecipe.normalized
    apply ite_eq_right
    change ¬ coordinate 1 (left HP).usage (σ (left HP).terminal.role)
      (SingleRegression.identifier ())
    exact hσ
  rintro ⟨c, hc⟩
  have hc0 : c = 0 := by simpa only [hz, mul_zero, zero_mul] using (hc σ).symm
  have hm := actual_product_mean HP
  simp_rw [hc, hc0] at hm
  have hp := div_pos (CutoffRegression.Q_one_pos HP) (by norm_num : (0 : ℝ) < 256)
  simp only [expect_const_zero] at hm
  linarith

/-- Empty terminal conditioning remains the zero finite expectation. -/
example : (𝔼 σ ∈ ({_σ : Environment 5 4 | False} : Finset _),
    sourceChild HP 1 SingleRegression.identifier (left HP) (left_admissible HP)
      (fun _ _ => rate 1) 0 σ () () *
    denseChild 1 SingleRegression.identifier (right HP) cutoff (fun _ => 1) gate 66
      (fun _ _ => rate 1) σ () ()) = 0 := by simp
end
end SharedMidpointRegression
