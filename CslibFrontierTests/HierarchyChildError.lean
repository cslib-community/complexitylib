/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual estimated-child mean errors)
import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.FirstMeanError
import all CslibFrontierTests.HierarchySignedMean

/-! Reuse the actual nonconstant four-role/spectator/suffix fixture without weakening its
exact checks. Additional nonzero coupled perturbations, once-negative accounting and
actual bounded incoming-child clients exercise the absolute propagation API. -/
set_option linter.privateModule false
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
  Matrix.HierarchyParams.H4RankEnvironment
  Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

-- Shared noise need not make either child constant or independent of the other.
example (σ : Bool) :
    let a : ℝ := if σ then 2 else 1
    |a * (3 * a) - (a + 1) * (3 * a - 1)| ≤
      2 * |3 * a - (3 * a - 1)| + |a - (a + 1)| * 5 := by
  dsimp only
  simpa only [sum_singleton] using
    abs_sum_mul_sub_mul_le ({()} : Finset Unit)
      (fun _ => if σ then 2 else 1) (fun _ => (if σ then 2 else 1) + 1)
      (fun _ => 3 * (if σ then 2 else 1)) (fun _ => 3 * (if σ then 2 else 1) - 1)
      (CA := 2) (CB := 5) (by intro _ _; cases σ <;> norm_num)
      (by intro _ _; cases σ <;> norm_num)

-- A genuinely nonzero product error: neither perturbed factor is zero.
example : |(2 : ℝ) * 6 - 3 * 5| = 3 := by norm_num

-- Fine normalized input may exceed the TOP cap; it must still remain unchanged.
example : boundedRoutedBinCutoff (fun v => v) (fun i => (16 : ℝ)⁻¹ ^ i)
      1 1 (fun _ => 1) ((1 : ℝ) / 16⁻¹) =
    routedBinCutoff (fun v => v) (fun i => (16 : ℝ)⁻¹ ^ i)
      1 (fun _ => 1) ((1 : ℝ) / 16⁻¹) := by
  simpa only [pow_zero, pow_one, mul_one] using boundedRoutedBinCutoff_div_eq
    (χ := fun v => v) (route := fun _ => 1) (cap := 1) (w := 1)
    (b := fun i => (16 : ℝ)⁻¹ ^ i) (by intro i; positivity) (by norm_num) (by norm_num) 1

namespace NumericCalls
private lemma final_task : HierarchyTask.correctionAtomTask (k := 1) 0 false 1 =
    .row 0 (.normalized 0) := HierarchyTask.correctionAtomTask_last_succ 0 0
private def src : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨0, 1, [()]⟩
private def mid : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨1, 1, [(), ()]⟩
private def dst : CorrectionRowTask.Channel (Fin 3) (List Unit) := ⟨2, 1, [()]⟩
private def mask (_ : Fin 3) (_ : ℝ) (_ : List Unit) (_ : Unit) (_ : Unit) : Prop := True
private def estimate (r : HierarchyTask.Request 1 (Fin 3) Unit) : Matrix Unit Unit ℝ :=
  match r.task with | .baseNormalized _ _ => fun _ _ => 2 | _ => fun _ _ => 3
private def truth (_ : HierarchyTask.Request 1 (Fin 3) Unit) : Matrix Unit Unit ℝ := fun _ _ => 1

-- Literal positive calls are 8 each. The negative 3 is subtracted once, not twice.
example : (∑ i ∈ range 2, HierarchyTask.rawPositiveSample mask 0 i .residual
    src mid dst 1 estimate () ()) -
    HierarchyTask.rawNegativeSample mask 0 0 .residual src mid dst 1 estimate () () = 13 := by
  norm_num [HierarchyTask.rawPositiveSample, HierarchyTask.rawNegativeSample,
    HierarchyTask.rawRequests, final_task, HierarchyTask.usageRatio,
    CorrectionRowTask.Channel.retains, src, mid, dst, mask, estimate]

example : (∑ i ∈ range 2, HierarchyTask.positiveChildError mask 0 i .residual
    src mid dst 1 3 1 estimate truth () ()) +
    HierarchyTask.negativeChildError mask 0 0 .residual src mid dst 1 estimate truth () () = 14
      := by
  norm_num [HierarchyTask.positiveChildError, HierarchyTask.negativeChildError,
    HierarchyTask.rawRequests, final_task, HierarchyTask.usageRatio,
    CorrectionRowTask.Channel.retains, src, mid, dst, mask, estimate, truth]

-- The canonical error is exactly zero, not merely bounded by a positive reserve.
example (CA CB : ℝ) : HierarchyTask.positiveChildError mask 0 0 .residual
    src mid dst 1 CA CB truth truth () () = 0 ∧
    HierarchyTask.negativeChildError mask 0 0 .residual src mid dst 1 truth truth () () = 0 := by
  simp [HierarchyTask.positiveChildError, HierarchyTask.negativeChildError,
    HierarchyTask.rawRequests]

-- Base task has no negative request; empty joint event contributes exactly zero.
example : HierarchyTask.negativeChildError mask 0 0 (.input 0)
    src mid dst 1 estimate truth () () = 0 := rfl
example : (𝔼 _σ ∈ (∅ : Finset Unit), HierarchyTask.rawSample mask 0 0 .residual
    src mid dst 1 estimate () ()) = 0 := by simp
end NumericCalls

namespace SignedMeanRegression
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
-- Actual bounded incoming children at two bins on the inherited nonconstant environment.
-- Top cap=1 is a genuine C/rate bound and adjacent ratios are exactly 16.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (raw prep : ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → Matrix Unit Unit ℝ)
    (maximum : ℕ → HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
      Environment 5 4 → Unit → ℝ) :
    let cutoff := fun i => routedBinCutoff (polynomialSwitch4 (1 / 2) 1) (fun i => rate ((fun i
      => i + 1) i)) i (fun _ => 1)
    let bounded := fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) (fun i => rate
      ((fun i => i + 1) i)) 1 i (fun _ => 1)
    let source := gridChannel roles.source 2 [1]
    let mid := gridChannel roles.midpoint 1 [2, 3]
    let terminal := gridChannel roles.terminal 2 [4]
    let estimated := fun i σ r => incomingChildren HP 1 SingleRegression.identifier 3 (bounded i)
      (raw i) (prep i) (maximum i) r σ
    let canonical := fun i σ r => canonicalRequestChild HP 1 SingleRegression.identifier base
      (cutoff i) ((fun _ _ => 1) i) gate 66 r σ
    let channelsV := fun role b suffix σ v => channels 1 role b suffix σ
      (SingleRegression.identifier v)
    let S := ({σ : Environment 5 4 | source.retains (channels 1) σ (SingleRegression.identifier
      ()) ∧
      terminal.retains (channels 1) σ (SingleRegression.identifier ())} : Finset _)
    |(𝔼 σ ∈ S, ((∑ i ∈ range (1 + 1), HierarchyTask.rawPositiveSample channelsV
      0 i .residual source mid terminal (rate ((fun i => i + 1) i)) (estimated i σ) () ()) -
      HierarchyTask.rawNegativeSample channelsV 0 0 .residual source mid terminal
        (rate ((fun i => i + 1) 0)) (estimated 0 σ) () ())) -
      HP.toHierarchyParams.residual (canonicalChannel SingleRegression.identifier (rate 1))
        (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1) base () ()| ≤
    𝔼 σ ∈ S, ((∑ i ∈ range (1 + 1), HierarchyTask.positiveChildError channelsV
      0 i .residual source mid terminal (rate ((fun i => i + 1) i))
      (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * max 1 16)
      (estimated i σ) (canonical i σ) () ()) +
      HierarchyTask.negativeChildError channelsV 0 0 .residual source mid terminal
        (rate ((fun i => i + 1) 0)) (estimated 0 σ) (canonical 0 σ) () ()) := by
  exact estimated_residual_bins_mean_error HP 1 SingleRegression.identifier (by norm_num)
    SingleRegression.identifier_injective SourceRegression.horizon roles
    0 2 1 2 1 (by decide) (by decide) [1] [2, 3] [4] (fun i => i + 1)
    (by intro i hi; simp only [mem_range] at hi; change i + 1 ≤ 2; omega)
    base (by intros; exact (rate_pos 1).le)
    (by intro x; norm_num [base, Matrix.mulVec, dotProduct, rate]) (by intros; rfl)
    (polynomialSwitch4 (1 / 2) 1) (fun _ hv => polynomialSwitch4_of_ge (by norm_num) hv)
    (fun _ _ => 1) gate 66 (by intros; rfl) gate_nonneg gate_le_one
    (η := 1) (by norm_num) (fun _ hh => gate_one hh) (by norm_num)
    (monotone_polynomialSwitch4 (by norm_num))
    (fun _ hh => polynomialSwitch4_of_le (by norm_num) hh)
    (fun _ => ⟨polynomialSwitch4_nonneg _ _ _, polynomialSwitch4_le_one _ _ _⟩)
    (fun _ _ hh => rate_antitone (Nat.add_le_add_right hh 1))
    (fun i => (adjacent_rate_ratio (i + 1)).le) (cap := 1) (by norm_num)
    (by intros; simp only [base, one_mul]; rfl) 3 raw prep maximum () ()
    (by intro z; right; norm_num [base, rate])
end SignedMeanRegression

namespace SignedMeanRegression
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def perturbed (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (r : HierarchyTask.Request HP.k (Fin 4) (ZMod 5)) (σ : Environment 5 4) :
    Matrix Unit Unit ℝ :=
  match r.task with
  | .baseNormalized _ _ => fun x y => 2 * child HP r σ x y
  | _ => child HP r σ

-- Nonzero perturbations of the actual canonical dense children on the same environment.
-- The two correction requests retain their distinct source/terminal/usage tuples.
private lemma perturbation_eq_positive (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (σ : Environment 5 4) :
    HierarchyTask.rawSample
      (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
      0 0 .residual (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
      (gridChannel roles.terminal 2 [4]) (rate 1) (fun r => perturbed HP r σ) () () -
      sample HP σ () () =
    HierarchyTask.rawPositiveSample
      (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
      0 0 .residual (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
      (gridChannel roles.terminal 2 [4]) (rate 1) (fun r => child HP r σ) () () := by
  simp only [sample, HierarchyTask.rawSample, HierarchyTask.rawPositiveSample,
    HierarchyTask.rawNegativeSample, HierarchyTask.rawRequests,
    HierarchyTask.correctionAtomTask_last HP.k_pos, perturbed, Fintype.sum_unique]
  ring

-- The perturbed conditional mean differs by the positive genuine direct+product mean.
set_option backward.isDefEq.respectTransparency false in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    (𝔼 σ ∈ ({σ : Environment 5 4 | src σ () ∧ dst σ ()} : Finset _),
      (HierarchyTask.rawSample
        (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
        0 0 .residual (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
        (gridChannel roles.terminal 2 [4]) (rate 1) (fun r => perturbed HP r σ) () () -
        sample HP σ () ())) = (1 + E HP) / 16 ∧ 0 < (1 + E HP) / 16 := by
  have hm := canonical_rawPositiveSample_mean HP 1 SingleRegression.identifier (by norm_num)
    SingleRegression.identifier_injective SourceRegression.horizon roles
    0 0 2 1 2 1 (by decide) (by decide) (by decide) [1] [2, 3] [4]
    base (by intros; exact (rate_pos 1).le)
    (by intro x; norm_num [base, Matrix.mulVec, dotProduct, rate]) (by intros; rfl)
    cutoff (fun _ => 1) gate 66 (fun _ _ => rfl) gate_nonneg gate_le_one
    (η := 1) (by norm_num) (fun _ h => gate_one h) (by norm_num) () ()
  have hcut : cutoff (rate 1 / rate 1) = 1 := by
    rw [div_self (rate_pos 1).ne']
    exact polynomialSwitch4_of_ge (by norm_num) le_rfl
  dsimp only at hm
  simp only [base, hcut, mul_one, Fintype.sum_unique] at hm
  constructor
  · apply Eq.trans (expect_congr rfl (fun σ _ => perturbation_eq_positive HP σ))
    convert hm using 1
    · simp only [child, src, dst, retainedMask, gridChannel, CorrectionRowTask.Channel.retains,
        channels, semanticSide_grid, SingleRegression.identifier]
    · dsimp only [E, base]
      norm_num only [rate, pow_one, pow_zero, inv_pow, one_pow, one_div]
      ring
  · exact div_pos (by linarith [E_pos HP]) (by norm_num)
end SignedMeanRegression
