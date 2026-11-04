/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of actual signed canonical means)

import Complexity.Foundations.Probability.HierarchySignedMean
import Complexity.Foundations.Probability.NormalizedAtomRows.FirstSignal
import all ComplexityTests.HierarchySharedMidpoint

/-! Fixed HP.k, final dispatched corrections, literal signed rawSample and two statistical
walk precisions on one four-role environment. Nonempty suffixes, unequal source/rank/usage
rates, the full midpoint reset and a free spectator survive. -/
set_option linter.privateModule false
namespace SignedMeanRegression
open Finset Cslib Cslib.Probability Cslib.RowCompression Matrix Matrix.HierarchyParams
  Matrix.HierarchyParams.H4RankEnvironment
  Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private abbrev roles : RoleProfile 4 := ⟨0, 1, 2, by decide, by decide, by decide⟩
private def base : Matrix Unit Unit ℝ := fun _ _ => rate 1
private def E : ℝ := HP.toHierarchyParams.correctionIter
  (canonicalChannel SingleRegression.identifier (rate 1))
  (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1) base HP.k () ()

private def requests : HierarchyTask.RawRequests HP.k (Fin 4) (ZMod 5) :=
  HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
  (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
  (gridChannel roles.terminal 2 [4]) (rate 1)
private lemma left_admissible : Admissible (requests HP).left :=
  ⟨by change (0 : Fin 4) ≠ 1; decide, rfl, rfl⟩
private def child : HierarchyTask.Request HP.k (Fin 4) (ZMod 5) →
    Environment 5 4 → Matrix Unit Unit ℝ :=
  canonicalRequestChild HP 1 SingleRegression.identifier base
  cutoff (fun _ => 1) gate 66
private def sample (σ : Environment 5 4) : Matrix Unit Unit ℝ :=
  HierarchyTask.rawSample (k := HP.k)
    (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
    0 0 .residual (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
    (gridChannel roles.terminal 2 [4]) (rate 1) (fun r => child HP r σ)

-- Exact structural final dispatch; the normalized index supplies k-1, not precision 1 or 3.
example (h : ℕ) (_hk : HP.k = h + 1) :
    HierarchyTask.correctionAtomTask 0 false (Fin.last (h + 1)) =
      HierarchyTask.row 0 (.normalized (Fin.last h)) := by
  exact HierarchyTask.correctionAtomTask_last_succ h 0

example (σ : Environment 5 4) : child HP (requests HP).left σ =
    sourceChild HP 1 SingleRegression.identifier (requests HP).left (left_admissible HP)
      base (HP.k - 1) σ :=
  canonicalRequestChild_final HP 1 SingleRegression.identifier (requests HP).left
    (left_admissible HP) HP.k_pos base cutoff (fun _ => 1) gate 66 0 rfl σ

private abbrev src (σ : Environment 5 4) (_ : Unit) : Prop :=
  retainedMask roles.source (side 5 2) 1 [1] σ 0
private abbrev dst (σ : Environment 5 4) (_ : Unit) : Prop :=
  retainedMask roles.terminal (side 5 2) 1 [4] σ 0

set_option backward.isDefEq.respectTransparency false in
private theorem actual_mean :
    rowSliceMean src dst (sample HP) () () =
        1 / 16 - (15 / 16) * E HP := by
  have hm := canonical_rawSample_mean HP 1 SingleRegression.identifier (by norm_num)
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
  simp only [rowSliceMean, sample, child, src, dst, retainedMask,
    gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid,
    SingleRegression.identifier] at hm ⊢
  convert hm using 1
  dsimp only [E, base]
  norm_num only [rate, pow_one, pow_zero, inv_pow, one_pow, one_div]
  ring

-- The genuine final correction is positive; the signed negative and product are present.
private theorem E_pos : 0 < E HP := by
  have hk := HP.k_pos
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  unfold E
  rw [hj, HP.toHierarchyParams.correctionIter_succ_apply]
  have hm := PilotTask.value_maximum_eq_zero HP.toHierarchyParams
    (canonicalChannel SingleRegression.identifier (rate 1))
    (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1) base
    (by simpa using SingleRegression.one_lt_J HP) HP.k
  erw [PilotTask.value_maximum_last] at hm
  rw [hm]
  simp only [Pi.zero_apply, HP.γ_one 0 (by norm_num), mul_one]
  have hn := (HP.toHierarchyParams.isCorrectionSeq_correctionIter (X :=
    canonicalChannel SingleRegression.identifier (rate 1)) (Y :=
    canonicalChannel SingleRegression.identifier (rate 1)) (rate_pos 1)
    (fun _ _ => (rate_pos 1).le)).nonneg j () ()
  have hi : 1 ≤ HP.toHierarchyParams.correctionInput
      (canonicalChannel SingleRegression.identifier (rate 1))
      (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1) base j () () / rate 1 := by
    rw [one_le_div (rate_pos 1)]
    change rate 1 ≤ rate 1 + ∑ _ : Unit, _ * rate 1
    simp only [Fintype.sum_unique, le_add_iff_nonneg_right]
    exact mul_nonneg hn (rate_pos 1).le
  exact mul_pos (rate_pos 1) ((CutoffRegression.Q_one_pos HP).trans_le (HP.Q_mono hi))

private def walk (precision : ℕ) :=
  conditionalWalk src dst
    (graph roles.source roles.terminal roles.source_terminal (side 5 2) (side 5 2)
      (side_le 5 2) (side_le 5 2) (fun (_ : Unit) => CopyPadding.identifier 1 [1] 0)
      (fun (_ : Unit) => CopyPadding.identifier 1 [4] 0)) (fun _ _ => precision + 2) (sample HP)

-- Precisions 1 and 3 have different walk lengths (3 and 5), on the same Request HP.k.
set_option backward.isDefEq.respectTransparency false in
example :
    rowSliceMean src dst (walk HP 1) () () =
        1 / 16 - (15 / 16) * E HP ∧
    rowSliceMean src dst (walk HP 3) () () =
        1 / 16 - (15 / 16) * E HP := by
  constructor <;> rw [walk, rowSliceMean_conditionalWalk] <;> exact actual_mean HP

example : 0 < E HP * (1 / 16) ∧ 0 < E HP :=
  ⟨mul_pos (E_pos HP) (by norm_num), E_pos HP⟩

private def product (σ : Environment 5 4) : ℝ :=
  (625 / 1296 : ℝ) * child HP (requests HP).left σ () () *
    (1 / 16) * child HP (requests HP).right σ () ()

set_option backward.isDefEq.respectTransparency false in
private theorem product_mean : (𝔼 σ ∈ ({σ : Environment 5 4 |
    src σ () ∧ dst σ ()} : Finset _), product HP σ) = E HP / 16 := by
  have hr : Admissible (requests HP).right := ⟨by change (1 : Fin 4) ≠ 2; decide, rfl, rfl⟩
  have hp := sourceChild_mul_denseChild_mean (i := HP.k - 1) HP 1 SingleRegression.identifier
    (requests HP).left (left_admissible HP) (requests HP).right hr rfl rfl
    (by change (0 : Fin 4) ≠ 2; decide) (by change (1 : Fin 4) ≠ 2; decide)
    (by norm_num) SingleRegression.identifier_injective SourceRegression.horizon
    (k := 1) (s := 2) (b := 1) (u := 2) (by decide) (by decide) rfl rfl
    (by decide) rfl (rate_min 2 1) base (by intros; exact (rate_pos 1).le)
    (by intro x; norm_num [base, Matrix.mulVec, dotProduct, rate]) (by intros; rfl)
    (Nat.sub_lt HP.k_pos (by decide)) cutoff (fun _ => 1) gate 66
    (fun A => coordinate 1 (gridChannel (2 : Fin 4) 2 [4]) A 0) () () ()
    (coordinate_min_grid 1 (2 : Fin 4) [4] 2 1 · 0)
    (fun _ _ => rfl) gate_nonneg gate_le_one (η := 1) (by norm_num)
    (fun _ h => gate_one h) (by norm_num)
  have heq : HP.k - 1 + 1 = HP.k := by have := HP.k_pos; omega
  rw [heq, channel_density 1 (requests HP).left.terminal 1 rfl,
    channel_density 1 (requests HP).right.usage 2 (rate_min 2 1),
    dens_filter_pi_eval (requests HP).right.terminal.role
      (fun A => coordinate 1 (gridChannel (2 : Fin 4) 2 [4]) A 0)] at hp
  have hd : (dens {A : FrameChannel 5 4 1 | coordinate 1 (gridChannel (2 : Fin 4) 2 [4]) A 0} : ℝ) =
      16 / 625 := by
    have hh := split_usage_density 1 SingleRegression.identifier
      (SharedMidpointRegression.right HP) (u := 2) rfl ()
    norm_num [side, Nat.ceilDiv_eq_add_pred_div] at hh
    exact hh
  rw [hd] at hp
  have hcut : cutoff (rate 1 / rate 1) = 1 := by
    rw [div_self (rate_pos 1).ne']
    exact polynomialSwitch4_of_ge (by norm_num) le_rfl
  have hl := canonicalRequestChild_final HP 1 SingleRegression.identifier
    (requests HP).left (left_admissible HP) HP.k_pos base cutoff (fun _ => 1) gate 66 0 rfl
  simp only [product, child, hl]
  have hright (σ : Environment 5 4) :
      canonicalRequestChild HP 1 SingleRegression.identifier base cutoff (fun _ => 1) gate
        66 (requests HP).right σ =
      denseChild 1 SingleRegression.identifier (requests HP).right cutoff (fun _ => 1)
        gate 66 base σ := rfl
  simp_rw [hright]
  simp only [show (requests HP).left.terminal.rate = rate 1 from rfl,
    show (requests HP).right.terminal.rate = rate 1 from rfl, base, hcut,
    mul_one] at hp
  norm_num [side, Nat.ceilDiv_eq_add_pred_div, rate] at hp
  convert hp using 1
  · apply expect_congr
    · ext σ
      simp only [mem_filter, mem_univ, true_and, src, dst, retainedMask, requests,
        HierarchyTask.rawRequests, gridChannel, CorrectionRowTask.Channel.retains,
        channels, coordinate, semanticSide_grid, SingleRegression.identifier]
    · intro σ _
      ac_rfl
  · dsimp only [E, base]
    norm_num only [rate, pow_one]
    ring

-- A missed midpoint kills the genuine final product; its conditional mean is positive.
example : ¬ ∃ c, ∀ σ : Environment 5 4, product HP σ = c := by
  have hd : (dens {σ : Environment 5 4 |
      (requests HP).left.usage.retains (channels 1) σ 0} : ℝ) = 81 / 625 := by
    rw [channel_density 1 (requests HP).left.usage 1 rfl]
    norm_num [side, Nat.ceilDiv_eq_add_pred_div]
  have hmiss : ∃ σ : Environment 5 4,
      ¬ (requests HP).left.usage.retains (channels 1) σ 0 := by
    by_contra hn
    have hall : ∀ σ : Environment 5 4,
        (requests HP).left.usage.retains (channels 1) σ 0 := by simpa using hn
    have he : ({σ : Environment 5 4 |
        (requests HP).left.usage.retains (channels 1) σ 0} : Finset _) = univ := by
      ext σ
      simp [hall σ]
    rw [he] at hd
    norm_num at hd
  obtain ⟨σ, hσ⟩ := hmiss
  have hz : child HP (requests HP).left σ () () = 0 := by
    rw [child, canonicalRequestChild_final HP 1 SingleRegression.identifier
      (requests HP).left (left_admissible HP) HP.k_pos base cutoff (fun _ => 1) gate 66 0 rfl]
    exact sourceChild_zero_off_usage HP 1 SingleRegression.identifier
      (requests HP).left (left_admissible HP) base (HP.k - 1) σ () () hσ
  rintro ⟨c, hc⟩
  have hc0 : c = 0 := by
    have hh := (hc σ).symm
    simp only [product, hz, mul_zero, zero_mul] at hh
    exact hh
  have hm := product_mean HP
  simp_rw [hc, hc0] at hm
  simp only [expect_const_zero] at hm
  linarith [E_pos HP]

-- Two positive bins plus one special negative request, with finite coverage and horizon.
-- The fine bin is zero at this entry: subtracting the negative once per bin would fail.
set_option backward.isDefEq.respectTransparency false in
example :
    let cut := fun i => routedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      (fun i => rate (i + 1)) i (fun _ => 1)
    (𝔼 σ ∈ ({σ : Environment 5 4 | src σ () ∧ dst σ ()} : Finset _),
      ((∑ i ∈ range 2, HierarchyTask.rawPositiveSample (k := HP.k)
        (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
        0 i .residual (gridChannel roles.source 2 [1])
        (gridChannel roles.midpoint 1 [2, 3]) (gridChannel roles.terminal 2 [4]) (rate (i + 1))
        (fun r => canonicalRequestChild HP 1 SingleRegression.identifier base (cut i)
          (fun _ => 1) gate 66 r σ) () ()) -
      HierarchyTask.rawNegativeSample (k := HP.k)
        (fun role b suffix σ v => channels 1 role b suffix σ (SingleRegression.identifier v))
        0 0 .residual (gridChannel roles.source 2 [1]) (gridChannel roles.midpoint 1 [2, 3])
        (gridChannel roles.terminal 2 [4]) (rate 1)
        (fun r => canonicalRequestChild HP 1 SingleRegression.identifier base (cut 0)
          (fun _ => 1) gate 66 r σ) () ())) =
      HP.toHierarchyParams.residual (canonicalChannel SingleRegression.identifier (rate 1))
        (canonicalChannel SingleRegression.identifier (rate 1)) (rate 1) base () () := by
  dsimp only
  have hm := canonical_residual_bins_mean HP 1 SingleRegression.identifier (by norm_num)
    SingleRegression.identifier_injective SourceRegression.horizon roles
    0 2 1 2 1 (by decide) (by decide) [1] [2, 3] [4] (fun i => i + 1)
    (by intro i hi; simp only [mem_range] at hi; change i + 1 ≤ 2; omega)
    base (by intros; exact (rate_pos 1).le)
    (by intro x; norm_num [base, Matrix.mulVec, dotProduct, rate]) (by intros; rfl)
    (polynomialSwitch4 (1 / 2) 1) (fun _ hv => polynomialSwitch4_of_ge (by norm_num) hv)
    (fun _ _ => 1) gate 66 (by intros; rfl) gate_nonneg gate_le_one
    (η := 1) (by norm_num) (fun _ hh => gate_one hh) (by norm_num) () ()
    (by intro z; right; norm_num [base, rate])
  dsimp only at hm
  apply Eq.trans ?_ hm
  apply expect_congr
  · ext σ
    simp only [mem_filter, mem_univ, true_and, src, dst, retainedMask, gridChannel,
      CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, SingleRegression.identifier]
  · intro σ _
    rfl

-- Literal zero correction dispatch stays separate from the final positive case.
example : HierarchyTask.correctionAtomTask (k := 0) 7 false (Fin.last 0) =
    .row 7 (.correction 0) := rfl

-- The full environment's free spectator is integrated, rather than frozen.
example (σ τ : Environment 5 4)
    (hs : σ 0 = τ 0) (hm : σ 1 = τ 1) :
    sourceChild HP 1 SingleRegression.identifier (requests HP).left (left_admissible HP)
      base (HP.k - 1) σ () () =
    sourceChild HP 1 SingleRegression.identifier (requests HP).left (left_admissible HP)
      base (HP.k - 1) τ () () :=
  sourceChild_roles HP 1 SingleRegression.identifier (requests HP).left
    (left_admissible HP) base (HP.k - 1) σ τ hs hm () ()

example : (𝔼 σ ∈ ({_σ : Environment 5 4 | False} : Finset _), sample HP σ () ()) = 0 := by
  simp

end
end SignedMeanRegression
