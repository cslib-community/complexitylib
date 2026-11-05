/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPrefixNoise
public import Complexity.Foundations.Probability.HierarchyInitialFeasibility
public import Complexity.Foundations.Probability.NormalizedAtomRows.ScheduleAllocation
public import Complexity.Foundations.Probability.HierarchyInitialIntegrated
import Complexity.Foundations.Data.Nat.Power

/-!
# Joint horizon and precision allocation for RAW prefixes

The retained prefix cube is paid by a growing precision margin. This is an explicit
additional allocation guard on the actual grid request budget, not a consequence of
positive precision alone. All endpoint calls and gates remain separate obligations.
No rarity is applied to centered noise. The guard is sufficient, not necessary for
actual noise. Joint recursive availability and compatibility with every other reserve
remain open. These are original finite bounds; reserve-allocation proof patterns are
adapted from Samuel Schlesinger.

## Main definitions

* `residualFirstNoisePayment`: the unconditional four-component noise contribution.

## Main results

* `requestPrecision_prefix_margin`: actual grid budget implies a growing precision margin.
* `combinedNoiseEnvelope_allocated`: the margin pays the retained prefix cube.
* `exists_prefix_budget_family`: unbounded budgets satisfying that allocation guard.
* `exists_residualFirstNoise_reserve_charge`: charge before all fields and requests.
* `combinedNoiseEnvelope_not_uniform`: fixed precision cannot pay this envelope uniformly.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression Cslib.Probability
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

/-- The budget covers the literal grid penalties and an additional horizon margin.
The natural charge `A` is fixed before the request and its budget. -/
theorem requestPrecision_prefix_margin
    {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (A : ℕ) (B : BudgetData HP P) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hbudget : 16 * (B.slack : ℝ) *
      (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M) :
    (A : ℝ) + (Nat.log2 M + 1 : ℕ) + 3 ≤ B.requestPrecision M r := by
  rw [B.requestPrecision_grid M ks ka r hs ht]
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hh := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
    (show (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
      A + (Nat.log2 M + 1 : ℕ) + 3) * (16 * B.slack) ≤ M by
        nlinarith only [hbudget])
  linarith only [hh]

/-- Spare precision pays the prefix cube, including an explicit constant salary. -/
theorem combinedNoiseEnvelope_allocated (A m j : ℕ) (hm : 0 < m)
    (hj : j ≤ m) (p : ℝ) (hp : (A : ℝ) + m + 3 ≤ p) :
    16 * ((j : ℝ) ^ 3 * ∑ i ∈ range j,
      64 * ((2 : ℝ) ^ (-p) * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8) ≤
    ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-p) *
      (1 / 4 : ℝ) ^ dyadicSlack m (j - 1)) ^ 4 := by
  let ε := (2 : ℝ) ^ (-p)
  let δ := (1 / 2 : ℝ) ^ A
  let d := dyadicSlack m (j - 1)
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hδ : 0 ≤ δ := by dsimp only [δ]; positivity
  have hεbound : ε ≤ δ / (8 * (2 : ℝ) ^ m) := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -p ≤ -(A : ℝ) + -(m : ℝ) + -3 by linarith only [hp])
    convert hh using 1
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_neg (by norm_num),
      Real.rpow_neg (by norm_num), Real.rpow_natCast, Real.rpow_natCast]
    norm_num [δ, div_pow, ε]
    ring
  have hm2 : (m : ℝ) ≤ (2 : ℝ) ^ m := by
    exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
  have hεm : ε * (m : ℝ) ≤ δ / 8 := by
    calc
      _ ≤ ε * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left hm2 hε
      _ ≤ δ / 8 := by
        have hh := mul_le_mul_of_nonneg_right hεbound
          (show 0 ≤ (2 : ℝ) ^ m by positivity)
        field_simp at hh ⊢
        nlinarith only [hh]
  have hc : 1024 / (1 - ((64 : ℝ)⁻¹) ^ 8) ≤ 4096 := by norm_num
  have hcube : (j : ℝ) ^ 3 ≤ (m : ℝ) ^ 4 := by
    calc
      _ ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ hj0 hjm 3
      _ ≤ _ := pow_le_pow_right₀ hm1 (by decide : 3 ≤ 4)
  have hpaid : (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) * ε ^ 4 * (j : ℝ) ^ 3 ≤ δ ^ 4 := by
    calc
      _ ≤ 4096 * ε ^ 4 * (m : ℝ) ^ 4 := by
        exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hcube
          (by positivity) (by positivity)
      _ = 4096 * (ε * (m : ℝ)) ^ 4 := by ring
      _ ≤ 4096 * (δ / 8) ^ 4 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hεm 4) (by norm_num)
      _ = _ := by ring
  have hdecay : ((64 : ℝ)⁻¹ ^ d) ^ 8 ≤ ((1 / 4 : ℝ) ^ d) ^ 4 := by
    have hpow (q : ℝ) (n : ℕ) : (q ^ d) ^ n = (q ^ n) ^ d := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    rw [hpow, hpow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) d
  apply (combinedNoiseEnvelope_prefix_le _ m j hj).trans
  change (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) * ε ^ 8 * (j : ℝ) ^ 3 *
    ((64 : ℝ)⁻¹ ^ d) ^ 8 ≤ (δ * ε * (1 / 4 : ℝ) ^ d) ^ 4
  calc
    _ = ((1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) * ε ^ 4 * (j : ℝ) ^ 3) *
        ε ^ 4 * ((64 : ℝ)⁻¹ ^ d) ^ 8 := by ring
    _ ≤ δ ^ 4 * ε ^ 4 * ((1 / 4 : ℝ) ^ d) ^ 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpaid (by positivity)) hdecay
        (by positivity) (by positivity)
    _ = _ := by ring

/-- A nonvacuous growing family for every fixed evaluator, charge and request.
The budget is `2^N`; source/rank penalties are fixed before increasing `N`.
This establishes the allocation guard, not recursive execution availability. -/
theorem exists_prefix_budget_family
    {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}
    (A : ℕ) (B : BudgetData HP P) (ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      16 * (B.slack : ℝ) *
        (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
          A + (Nat.log2 (2 ^ N) + 1 : ℕ) + 3) ≤ (2 ^ N : ℕ) := by
  let L := 2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank + A + 4
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (max (max (32 * (B.slack : ℝ)) L) 4)
  refine ⟨N₀, ?_⟩
  intro N hN
  have hNN : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
  have hN4 : 4 ≤ N := by
    have hh := (le_max_right (max (32 * (B.slack : ℝ)) L) 4).trans hN₀.le
    exact_mod_cast hh.trans hNN
  have hNs : 32 * (B.slack : ℝ) ≤ N :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hN₀.le.trans hNN)
  have hNL : L ≤ N :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hN₀.le.trans hNN)
  have hsq : (N : ℝ) ^ 2 ≤ (2 : ℝ) ^ N := by
    exact_mod_cast (Nat.sq_le_two_pow hN4)
  have hs0 : (0 : ℝ) ≤ B.slack := Nat.cast_nonneg _
  rw [Nat.log2_two_pow]
  push_cast
  have hh : 16 * (B.slack : ℝ) * (L + N) ≤ (N : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg hs0 (sub_nonneg.mpr hNL),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) N) (sub_nonneg.mpr hNs)]
  dsimp only [L] at hh
  nlinarith only [hh.trans hsq]

/-- The unconditional centered-noise contribution with the literal four weights.
The raw branch retains the outer factor 64 used by the separated reserve. -/
@[expose] def residualFirstNoisePayment (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre E : ℝ) : ℝ :=
  initialSeparatedReserve HP C Cpre (floor * E / 511) (E / 4)
    (E * (458752 / 57))
    (64 * (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
      ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63)

-- The conservative dilation 1000000 exceeds 63 * (458752 / 57). Comparing
-- with the existing allocator enlarges the tail payment; it grants no noise rarity.
private theorem residualFirstNoisePayment_le_transport
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre E : ℝ) (hf : 0 < floor) (hE : 0 ≤ E) :
    residualFirstNoisePayment HP floor cap C Cpre E ≤
      initialFirstTransportPayment HP floor cap C Cpre (1000000 * E) := by
  have h8 : (1 : ℝ) ≤ 8 ^ (4⁻¹ : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
  have hq : (1 : ℝ) ≤ (2 + 256 / floor) ^ (4⁻¹ : ℝ) :=
    Real.one_le_rpow (by have hh := div_nonneg (by norm_num : (0 : ℝ) ≤ 256) hf.le
                         linarith) (by norm_num)
  have hscale : E ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * E := by nlinarith only [h8, hE]
  have hscale' : E ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * E *
      (2 + 256 / floor) ^ (4⁻¹ : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ (8 : ℝ) ^ (4⁻¹ : ℝ) * E by positivity)
    nlinarith only [hscale, hh]
  unfold residualFirstNoisePayment initialFirstTransportPayment
  apply initialSeparatedReserve_mono HP C Cpre
  · positivity
  · positivity
  · positivity
  · nlinarith [mul_le_mul_of_nonneg_right hscale hf.le]
  · nlinarith only [hscale, hE]
  · nlinarith only [hscale', hE]
  · have hW : 0 ≤ 64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((HP.K + 1) * floor ^ 4) := by positivity
    nlinarith [mul_nonneg hW (pow_nonneg hE 4)]

/-- One charge, above any requested lower bound, pays this unconditional noise
contribution at every larger charge and every precision. HP, cap, decoder and floor
are fixed first. Later requests must still satisfy the joint budget guard. -/
theorem exists_residualFirstNoise_reserve_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre : ℝ) (hf : 0 < floor) (lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ ∀ A ≥ A₀, ∀ p : ℝ,
      residualFirstNoisePayment HP floor cap C Cpre
        ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-p)) ≤ ((2 : ℝ) ^ (-p)) ^ 4 := by
  obtain ⟨A₁, halloc⟩ := initialFirstTransportPayment_exists_charge
    HP floor cap C Cpre 1000000
  refine ⟨max lower A₁, le_max_left _ _, ?_⟩
  intro A hA p
  have ha : A₁ ≤ A := (le_max_right _ _).trans hA
  have hsmall : (1 / 2 : ℝ) ^ A ≤ (2 : ℝ) ^ (-(A₁ : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    rw [one_div_pow, one_div]
    apply (inv_le_inv₀ (by positivity : (0 : ℝ) < 2 ^ A)
      (by positivity : (0 : ℝ) < 2 ^ A₁)).mpr
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ha
  apply (residualFirstNoisePayment_le_transport HP floor cap C Cpre _ hf
    (by positivity)).trans
  apply le_trans _ (halloc ((2 : ℝ) ^ (-p)))
  apply initialFirstTransportPayment_mono HP floor cap C Cpre hf.le (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ (2 : ℝ) ^ (-p) by positivity)]

/-- At fixed positive precision the conservative envelope cannot be bounded by
one horizon-independent scalar. This is not a lower bound on actual noise. -/
theorem combinedNoiseEnvelope_not_uniform (ε T : ℝ) (hε : 0 < ε) :
    ¬ ∀ m : ℕ, 0 < m →
      16 * ((m : ℝ) ^ 3 * ∑ i ∈ range m,
        64 * (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8) ≤ T := by
  let c := 1024 * ε ^ 8 * ((64 : ℝ)⁻¹) ^ 8
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨n, hn⟩ := exists_nat_gt (max (T / c) 1)
  intro h
  have hn1 : (1 : ℝ) < n := (le_max_right _ _).trans_lt hn
  have hn0 : 0 < n := by exact_mod_cast (by linarith only [hn1] : (0 : ℝ) < n)
  have hnc : T < c * n := by
    have hh := (le_max_left _ _).trans_lt hn
    exact (div_lt_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  have hl := combinedNoiseEnvelope_final_lower ε (n - 1)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hl
  have hp : (n : ℝ) ≤ (n : ℝ) ^ 3 := le_self_pow₀ hn1.le (by decide : 3 ≠ 0)
  have hh := mul_le_mul_of_nonneg_left hp hc.le
  have hh' := h n hn0
  dsimp only [c] at hh hnc
  nlinarith only [hl, hh, hh', hnc]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
