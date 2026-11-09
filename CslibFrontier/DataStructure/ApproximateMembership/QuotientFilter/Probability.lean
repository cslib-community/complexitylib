/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.ApproximateMembership.QuotientFilter.Basic
public import CslibFrontier.Probability.KWiseIndependent.Reduced
public import CslibFrontier.DataStructure.HashFamily.WordRAM.KWise
public import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Probabilistic Analysis of the Two-Stage Quotient Filter

This file establishes the probabilistic guarantees of the canonical quotient filter when
instantiated with:
1. a two-stage $5$-wise independent reduced polynomial hash `quotHash U w₀ n` mapping keys in
   `Fin U` (`U ≤ 2 ^ w₀`) to `b = tableLog (min n (2 ^ w₀))`-bit quotients (`2 ^ b ≥ 8 * n_eff`,
   where `n_eff = min n (2 ^ w₀)`), and
2. an independent multiply-shift hash `remHash U w₀ k` mapping keys in `Fin U` to
   `remBits w₀ k = min w₀ (k + 1)`-bit remainders.

## Main results

* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.card_quotHash_eq_le`: pairwise
  collision bound for the two-stage quotient hash (`≤ 2 / 2 ^ b`).
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.toOuterMeasure_falsePositive_le`:
  for any set `S : Finset (Fin U)` with `#S ≤ n` and any absent key `u ∉ S`, the false-positive
  probability under `filterSeedLaw w₀ n` is at most `(1 / 2 : ℝ≥0∞) ^ k`.
* `Cslib.DataStructure.ApproximateMembership.QuotientFilter.sum_clusterLen_le`,
  `Cslib.DataStructure.ApproximateMembership.QuotientFilter.tsum_clusterLen_le`: for any set
  `S : Finset (Fin U)` with `#S ≤ n` and any key `u : Fin U`, the expected cluster length around
  `quotHash θ u` is at most `290` (`289` on injective top-level seeds plus at most `1` from the
  non-injective top-level event of probability `≤ (n_eff + 1) * n_eff / 2 ^ (3 * b)`).

## References

* [A. Pagh, R. Pagh and S. S. Rao, *An optimal Bloom filter replacement*][PaghPaghRao2005]
* [M. A. Bender, M. Farach-Colton, R. Johnson, R. Kraner, B. C. Kuszmaul, D. Medjedovic, P. Montes,
  P. Shetty, R. P. Spillane and E. Zadok, *Don't thrash: how to cache your hash on
  flash*][BenderEtAl2012]
* [A. Pagh, R. Pagh and M. Ružić, *Linear Probing with Constant Independence*][PaghPaghRuzic2009]
-/

public section

namespace Cslib.DataStructure.ApproximateMembership.QuotientFilter

open Finset
open Cslib.Probability
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.LinearProbing
open scoped BigOperators ENNReal NNReal

/-! ## Section 1: Two-stage quotient and remainder hash parameters -/

/-- Effective capacity `min n (2 ^ w₀)`: since `#S ≤ U ≤ 2 ^ w₀` for every `S : Finset (Fin U)`,
any valid state of capacity `n` has `#S ≤ effCap w₀ n`. -/
@[expose] def effCap (w₀ n : ℕ) : ℕ :=
  min n (2 ^ w₀)

/-- Quotient bit-width `b = tableLog (effCap w₀ n) = ⌈log₂ max(8 · effCap w₀ n, 8)⌉`. -/
@[expose] def quotBits (w₀ n : ℕ) : ℕ :=
  tableLog (effCap w₀ n)

/-- Remainder bit-width `f = min w₀ (k + 1)`. -/
@[expose] def remBits (w₀ k : ℕ) : ℕ :=
  min w₀ (k + 1)

theorem three_le_quotBits (w₀ n : ℕ) : 3 ≤ quotBits w₀ n :=
  three_le_tableLog (effCap w₀ n)

theorem eight_le_two_pow_quotBits (w₀ n : ℕ) : 8 ≤ 2 ^ quotBits w₀ n :=
  eight_le_tableSize (effCap w₀ n)

theorem eight_mul_effCap_le_two_pow_quotBits (w₀ n : ℕ) :
    8 * effCap w₀ n ≤ 2 ^ quotBits w₀ n :=
  eight_mul_le_tableSize (effCap w₀ n)

theorem effCap_lt_two_pow_quotBits (w₀ n : ℕ) :
    effCap w₀ n < 2 ^ quotBits w₀ n :=
  n_max_lt_tableSize (effCap w₀ n)

theorem card_le_effCap {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀) {S : Finset (Fin U)} (hS : #S ≤ n) :
    #S ≤ effCap w₀ n := by
  have hcardU : #S ≤ U := by
    calc #S ≤ Fintype.card (Fin U) := Finset.card_le_univ S
      _ = U := Fintype.card_fin U
  exact le_min hS (hcardU.trans hU)

theorem card_lt_two_pow_quotBits {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀) {S : Finset (Fin U)}
    (hS : #S ≤ n) :
    #S < 2 ^ quotBits w₀ n :=
  lt_of_le_of_lt (card_le_effCap hU hS) (effCap_lt_two_pow_quotBits w₀ n)

/-- Seed type for the two-stage $5$-wise independent quotient hash. -/
abbrev QuotSeed (w₀ n : ℕ) : Type :=
  ReducedPolySeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5

/-- Seed type for the independent multiply-shift remainder hash. -/
abbrev RemSeed (w₀ : ℕ) : Type :=
  Fin (2 ^ (w₀ - 1))

/-- Combined seed type `QuotSeed w₀ n × RemSeed w₀` for the quotient filter. -/
abbrev FilterSeed (w₀ n : ℕ) : Type :=
  QuotSeed w₀ n × RemSeed w₀

/-- Uniform distribution over `FilterSeed w₀ n`. -/
@[expose] noncomputable def filterSeedLaw (w₀ n : ℕ) : PMF (FilterSeed w₀ n) :=
  PMF.uniformOfFintype (FilterSeed w₀ n)

/-- Two-stage $5$-wise independent quotient hash mapping `Fin U` to `Fin (2 ^ quotBits w₀ n)`. -/
@[expose] noncomputable def quotHash (U w₀ n : ℕ) (θ : QuotSeed w₀ n) (u : Fin U) :
    Fin (2 ^ quotBits w₀ n) :=
  reducedPolyHash U w₀ (quotBits w₀ n) (quotBits w₀ n) 5 θ u

/-- Multiply-shift remainder hash mapping `Fin U` to `Fin (2 ^ remBits w₀ k)`. -/
@[expose] def remHash (U w₀ k : ℕ) (γ : RemSeed w₀) (u : Fin U) :
    Fin (2 ^ remBits w₀ k) :=
  multiplyShiftReduced U w₀ (k + 1) γ u

/-! ## Section 2: Pairwise collision and false-positive probability bounds -/

/-- For any distinct `x, y : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of remainder seeds
`γ : RemSeed w₀` on which `remHash U w₀ k γ x = remHash U w₀ k γ y` satisfies
`#{γ | remHash U w₀ k γ x = remHash U w₀ k γ y} * 2 ^ k ≤ Fintype.card (RemSeed w₀)`. -/
theorem card_remHash_eq_le {U w₀ k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {x y : Fin U} (hxy : x ≠ y) :
    #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ y} * 2 ^ k ≤
      Fintype.card (RemSeed w₀) := by
  have h1 := card_multiplyShiftReduced_eq_le (R := k + 1) hw₀ hU hxy
  have hpow_k : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
  have hpow_w : 2 ^ w₀ = 2 * 2 ^ (w₀ - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hw₀, pow_succ']
  simp only [remHash, Fintype.card_fin]
  have h2 :
      2 * (#{γ : RemSeed w₀ |
        multiplyShiftReduced U w₀ (k + 1) γ x = multiplyShiftReduced U w₀ (k + 1) γ y} * 2 ^ k) ≤
        2 * 2 ^ (w₀ - 1) := by
    calc 2 * (#{γ : RemSeed w₀ |
          multiplyShiftReduced U w₀ (k + 1) γ x = multiplyShiftReduced U w₀ (k + 1) γ y} * 2 ^ k)
        = #{γ : RemSeed w₀ |
            multiplyShiftReduced U w₀ (k + 1) γ x = multiplyShiftReduced U w₀ (k + 1) γ y} *
            2 ^ (k + 1) := by rw [hpow_k]; ring
      _ ≤ 2 ^ w₀ := h1
      _ = 2 * 2 ^ (w₀ - 1) := hpow_w
  exact Nat.le_of_mul_le_mul_left h2 (by decide)

/-- For any distinct `x, y : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of quotient seeds
`θ : QuotSeed w₀ n` on which `quotHash U w₀ n θ x = quotHash U w₀ n θ y` satisfies
`#{θ | quotHash U w₀ n θ x = quotHash U w₀ n θ y} * 2 ^ quotBits w₀ n ≤
2 * Fintype.card (QuotSeed w₀ n)`. -/
theorem card_quotHash_eq_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {x y : Fin U} (hxy : x ≠ y) :
    #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ y} * 2 ^ quotBits w₀ n ≤
      2 * Fintype.card (QuotSeed w₀ n) := by
  classical
  set b := quotBits w₀ n
  set t := reducedTrinomialStep w₀ b b
  set Top := ReducedTopSeed w₀
  set Bot := ReducedBotSeed w₀ b b 5
  have hbi :
      #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ y} =
        ∑ α : Top, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} := by
    rw [← Finset.card_sigma]
    refine Finset.card_bij (fun θ _ => ⟨θ.1, θ.2⟩) ?_ ?_ ?_
    · intro θ hθ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma] at hθ ⊢
      exact hθ
    · rintro ⟨α₁, β₁⟩ _ ⟨α₂, β₂⟩ _ h
      cases h
      rfl
    · rintro ⟨α, β⟩ h
      simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at h
      exact ⟨(α, β), by simp [h], rfl⟩
  rw [hbi, Finset.sum_mul]
  set Bad : Finset Top :=
    Finset.univ.filter fun α : Top =>
      multiplyShiftReduced U w₀ (3 * b) α x = multiplyShiftReduced U w₀ (3 * b) α y
  set Good : Finset Top := Finset.univ \ Bad
  have hsplit :
      (∑ α : Top, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) =
        (∑ α ∈ Good, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) +
        (∑ α ∈ Bad, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) := by
    rw [← Finset.sum_union Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset (Finset.subset_univ _)]
  rw [hsplit]
  have hgood_bound :
      ∀ α ∈ Good,
        #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b ≤
          Fintype.card Bot := by
    intro α hα
    have hne_red :
        multiplyShiftReduced U w₀ (3 * b) α x ≠ multiplyShiftReduced U w₀ (3 * b) α y := by
      simp only [Good, Bad, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hα
      exact hα
    set x' := multiplyShiftReduced U w₀ (3 * b) α x
    set y' := multiplyShiftReduced U w₀ (3 * b) α y
    set H := trinomialPolyHash t 5 (2 ^ min w₀ (3 * b)) b
    have hk : IsKWiseIndependentHash 5 H :=
      isKWiseIndependentHash_trinomialPolyHash
        (two_pow_min_le_two_pow_reducedTrinomialDeg w₀ b b)
        (le_reducedTrinomialDeg w₀ b b)
    set P : Finset (Fin (2 ^ min w₀ (3 * b))) := {x', y'}
    have hP_card : #P = 2 := Finset.card_pair hne_red
    have hP_le : #P ≤ 5 := by omega
    have hsub :
        (Finset.univ.filter fun β : Bot =>
          quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y) ⊆
        Finset.univ.biUnion fun v : Fin (2 ^ b) =>
          Finset.univ.filter fun β : Bot => P.restrict (H β) = fun _ => v := by
      intro β hβ
      have hβ' : quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y :=
        (Finset.mem_filter.mp hβ).2
      change H β x' = H β y' at hβ'
      rw [Finset.mem_biUnion]
      refine ⟨H β x', Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      funext ⟨z, hz⟩
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · rfl
      · exact hβ'.symm
    have hmul_sq :
        (2 ^ b) ^ 2 * #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} ≤
          2 ^ b * Fintype.card Bot := by
      calc (2 ^ b) ^ 2 * #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y}
          ≤ (2 ^ b) ^ 2 * ∑ v : Fin (2 ^ b),
              #{β : Bot | P.restrict (H β) = fun _ => v} := by
            refine Nat.mul_le_mul_left _ ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
        _ = ∑ v : Fin (2 ^ b),
              Fintype.card (Fin (2 ^ b)) ^ #P * #{β : Bot | P.restrict (H β) = fun _ => v} := by
            rw [Finset.mul_sum, hP_card, Fintype.card_fin]
        _ = ∑ _v : Fin (2 ^ b), Fintype.card Bot := by
            refine Finset.sum_congr rfl fun v _ => hk.card_filter_restrict_eq hP_le (fun _ => v)
        _ = 2 ^ b * Fintype.card Bot := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have hmul_re :
        2 ^ b * (#{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) ≤
          2 ^ b * Fintype.card Bot := by
      calc 2 ^ b * (#{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b)
          = (2 ^ b) ^ 2 * #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} := by
            ring
        _ ≤ 2 ^ b * Fintype.card Bot := hmul_sq
    exact Nat.le_of_mul_le_mul_left hmul_re (by positivity)
  have hsum_good :
      (∑ α ∈ Good, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) ≤
        Fintype.card Top * Fintype.card Bot := by
    calc (∑ α ∈ Good, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b)
        ≤ ∑ _α ∈ Good, Fintype.card Bot := Finset.sum_le_sum hgood_bound
      _ = #Good * Fintype.card Bot := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card Top * Fintype.card Bot :=
          Nat.mul_le_mul_right _ (Finset.card_le_univ Good)
  have hbad_card : #Bad * 2 ^ b ≤ Fintype.card Top := by
    have h1 := card_multiplyShiftReduced_eq_le (R := 3 * b) hw₀ hU hxy
    have hb3 : 3 ≤ b := three_le_quotBits w₀ n
    have hpow_3b : 2 * 2 ^ b ≤ 2 ^ (3 * b) := by
      have : b + 1 ≤ 3 * b := by omega
      calc 2 * 2 ^ b = 2 ^ (b + 1) := (pow_succ' 2 b).symm
        _ ≤ 2 ^ (3 * b) := Nat.pow_le_pow_right (by decide) this
    have hpow_w : 2 ^ w₀ = 2 * Fintype.card Top := by
      dsimp only [Top, ReducedTopSeed]
      rw [Fintype.card_fin]
      conv_lhs => rw [← Nat.sub_add_cancel hw₀, pow_succ']
    have h2 : 2 * (#Bad * 2 ^ b) ≤ 2 * Fintype.card Top := by
      calc 2 * (#Bad * 2 ^ b) = #Bad * (2 * 2 ^ b) := by ring
        _ ≤ #Bad * 2 ^ (3 * b) := Nat.mul_le_mul_left _ hpow_3b
        _ ≤ 2 ^ w₀ := h1
        _ = 2 * Fintype.card Top := hpow_w
    exact Nat.le_of_mul_le_mul_left h2 (by decide)
  have hsum_bad :
      (∑ α ∈ Bad, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b) ≤
        Fintype.card Top * Fintype.card Bot := by
    calc (∑ α ∈ Bad, #{β : Bot | quotHash U w₀ n (α, β) x = quotHash U w₀ n (α, β) y} * 2 ^ b)
        ≤ ∑ _α ∈ Bad, Fintype.card Bot * 2 ^ b := by
          refine Finset.sum_le_sum fun α _ =>
            Nat.mul_le_mul_right _ (Finset.card_le_univ _)
      _ = (#Bad * 2 ^ b) * Fintype.card Bot := by
          rw [Finset.sum_const, smul_eq_mul]
          ring
      _ ≤ Fintype.card Top * Fintype.card Bot := by gcongr
  have hcard_prod : Fintype.card (QuotSeed w₀ n) = Fintype.card Top * Fintype.card Bot :=
    Fintype.card_prod Top Bot
  omega

/-- Counting false-positive bound over `FilterSeed w₀ n`: for any `S : Finset (Fin U)` with
`#S ≤ n` and any `u ∉ S` (`0 < w₀`, `U ≤ 2 ^ w₀`), the number of seeds `p : FilterSeed w₀ n` for
which `∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
remHash U w₀ k p.2 x = remHash U w₀ k p.2 u` satisfies
`#{p | ...} * 2 ^ k ≤ Fintype.card (FilterSeed w₀ n)`. -/
theorem card_falsePositive_mul_le {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) {u : Fin U} (hu : u ∉ S) :
    #{p : FilterSeed w₀ n |
      ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} * 2 ^ k ≤
      Fintype.card (FilterSeed w₀ n) := by
  classical
  have hS_eff : #S ≤ effCap w₀ n := card_le_effCap hU hS
  by_cases hS0 : #S = 0
  · have hSe : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hSe
    simp
  · have hne_pos : 1 ≤ effCap w₀ n := by omega
    set FP : Finset (FilterSeed w₀ n) :=
      Finset.univ.filter fun p : FilterSeed w₀ n =>
        ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
          remHash U w₀ k p.2 x = remHash U w₀ k p.2 u
    have hsub :
        FP ⊆ S.biUnion fun x =>
          (Finset.univ.filter fun θ : QuotSeed w₀ n =>
            quotHash U w₀ n θ x = quotHash U w₀ n θ u) ×ˢ
          (Finset.univ.filter fun γ : RemSeed w₀ =>
            remHash U w₀ k γ x = remHash U w₀ k γ u) := by
      intro p hp
      simp only [FP, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_product] at hp ⊢
      exact hp
    have hpair_bound :
        ∀ x ∈ S,
          (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
            #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u}) *
            (effCap w₀ n * 2 ^ k) ≤
            Fintype.card (FilterSeed w₀ n) := by
      intro x hx
      have hxu : x ≠ u := fun h => hu (h ▸ hx)
      have hq := card_quotHash_eq_le (n := n) hw₀ hU hxu
      have hr := card_remHash_eq_le (k := k) hw₀ hU hxu
      have h8 : 8 * effCap w₀ n ≤ 2 ^ quotBits w₀ n := eight_mul_effCap_le_two_pow_quotBits w₀ n
      have hq' :
          #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} * effCap w₀ n ≤
            Fintype.card (QuotSeed w₀ n) := by
        have hmul :
            2 * (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} * effCap w₀ n) ≤
              #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
                2 ^ quotBits w₀ n := by
          have : 2 * effCap w₀ n ≤ 2 ^ quotBits w₀ n := by omega
          calc 2 * (#{θ : QuotSeed w₀ n |
                quotHash U w₀ n θ x = quotHash U w₀ n θ u} * effCap w₀ n)
              = #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
                  (2 * effCap w₀ n) := by ring
            _ ≤ #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
                  2 ^ quotBits w₀ n := Nat.mul_le_mul_left _ this
        omega
      calc (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
            #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u}) *
            (effCap w₀ n * 2 ^ k)
          = (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} * effCap w₀ n) *
              (#{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u} * 2 ^ k) := by ring
        _ ≤ Fintype.card (QuotSeed w₀ n) * Fintype.card (RemSeed w₀) := by gcongr
        _ = Fintype.card (FilterSeed w₀ n) := (Fintype.card_prod _ _).symm
    have hsum :
        #FP * (effCap w₀ n * 2 ^ k) ≤ effCap w₀ n * Fintype.card (FilterSeed w₀ n) := by
      calc #FP * (effCap w₀ n * 2 ^ k)
          ≤ (#(S.biUnion fun x =>
              (Finset.univ.filter fun θ : QuotSeed w₀ n =>
                quotHash U w₀ n θ x = quotHash U w₀ n θ u) ×ˢ
              (Finset.univ.filter fun γ : RemSeed w₀ =>
                remHash U w₀ k γ x = remHash U w₀ k γ u))) *
              (effCap w₀ n * 2 ^ k) := Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
        _ ≤ (∑ x ∈ S,
              #{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
              #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u}) *
              (effCap w₀ n * 2 ^ k) := by
            refine Nat.mul_le_mul_right _ (Finset.card_biUnion_le.trans ?_)
            refine Finset.sum_le_sum fun x _ => ?_
            rw [Finset.card_product]
        _ = ∑ x ∈ S,
              (#{θ : QuotSeed w₀ n | quotHash U w₀ n θ x = quotHash U w₀ n θ u} *
                #{γ : RemSeed w₀ | remHash U w₀ k γ x = remHash U w₀ k γ u}) *
                (effCap w₀ n * 2 ^ k) := Finset.sum_mul _ _ _
        _ ≤ ∑ _x ∈ S, Fintype.card (FilterSeed w₀ n) := Finset.sum_le_sum hpair_bound
        _ = #S * Fintype.card (FilterSeed w₀ n) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ effCap w₀ n * Fintype.card (FilterSeed w₀ n) := Nat.mul_le_mul_right _ hS_eff
    have hmul_comm : #FP * (effCap w₀ n * 2 ^ k) = effCap w₀ n * (#FP * 2 ^ k) := by ring
    rw [hmul_comm] at hsum
    exact Nat.le_of_mul_le_mul_left hsum hne_pos

/-- **Per-query false-positive probability bound**: for any `S : Finset (Fin U)` with `#S ≤ n` and
any absent key `u ∉ S` (`0 < w₀`, `U ≤ 2 ^ w₀`), the probability under `filterSeedLaw w₀ n` that
`u` collides in both quotient and remainder with some key in `S` is at most `(1 / 2 : ℝ≥0∞) ^ k`. -/
theorem toOuterMeasure_falsePositive_le {U w₀ n k : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) {u : Fin U} (hu : u ∉ S) :
    (filterSeedLaw w₀ n).toOuterMeasure
      {p : FilterSeed w₀ n |
        ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
          remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} ≤
      (1 / 2 : ℝ≥0∞) ^ k := by
  classical
  set FP : Finset (FilterSeed w₀ n) :=
    Finset.univ.filter fun p : FilterSeed w₀ n =>
      ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
        remHash U w₀ k p.2 x = remHash U w₀ k p.2 u
  have hset :
      {p : FilterSeed w₀ n |
        ∃ x ∈ S, quotHash U w₀ n p.1 x = quotHash U w₀ n p.1 u ∧
          remHash U w₀ k p.2 x = remHash U w₀ k p.2 u} =
        (FP : Set (FilterSeed w₀ n)) := by
    ext p
    simp [FP]
  rw [hset, filterSeedLaw, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, ← div_eq_mul_inv]
  have hcard := card_falsePositive_mul_le (k := k) hw₀ hU hS hu
  have hcast : (#FP : ℝ≥0∞) * (2 ^ k : ℝ≥0∞) ≤ (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞) := by
    exact_mod_cast hcard
  have hcard_ne_zero : (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard_ne_top : (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  have hpow_ne_zero : (2 ^ k : ℝ≥0∞) ≠ 0 := by positivity
  have hpow_ne_top : (2 ^ k : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  rw [ENNReal.div_le_iff_le_mul (Or.inl hcard_ne_zero) (Or.inl hcard_ne_top)]
  have hhalf : (1 / 2 : ℝ≥0∞) ^ k = (2 ^ k : ℝ≥0∞)⁻¹ := by
    rw [one_div, ENNReal.inv_pow]
  rw [hhalf]
  calc (#FP : ℝ≥0∞)
      = (#FP : ℝ≥0∞) * (2 ^ k : ℝ≥0∞) * (2 ^ k : ℝ≥0∞)⁻¹ :=
        (ENNReal.mul_inv_cancel_right hpow_ne_zero hpow_ne_top).symm
    _ ≤ (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞) * (2 ^ k : ℝ≥0∞)⁻¹ := by gcongr
    _ = (2 ^ k : ℝ≥0∞)⁻¹ * (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞) := mul_comm _ _

/-- Minimum exponent `k = max 1 ⌈log₂(1 / ε)⌉` such that `(1 / 2 : ℝ≥0∞) ^ k ≤ ε` for any
`ε : ℝ≥0∞` with `ε ≠ 0`. -/
@[expose] noncomputable def epsLog (ε : ℝ≥0∞) : ℕ :=
  max 1 (Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊)

theorem one_le_epsLog (ε : ℝ≥0∞) : 1 ≤ epsLog ε :=
  le_max_left 1 _

theorem two_pow_neg_epsLog_le {ε : ℝ≥0∞} (hε0 : ε ≠ 0) :
    (1 / 2 : ℝ≥0∞) ^ epsLog ε ≤ ε := by
  have hinv_top : ε⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hε0
  have hcoe : ((ε⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) = ε⁻¹ := ENNReal.coe_toNNReal hinv_top
  have h1 : ε⁻¹.toNNReal ≤ (⌈ε⁻¹.toNNReal⌉₊ : ℝ≥0) := Nat.le_ceil _
  have h2 : ⌈ε⁻¹.toNNReal⌉₊ ≤ 2 ^ Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊ :=
    Nat.le_pow_clog (by decide) _
  have h3 : 2 ^ Nat.clog 2 ⌈ε⁻¹.toNNReal⌉₊ ≤ 2 ^ epsLog ε :=
    Nat.pow_le_pow_right (by decide) (le_max_right 1 _)
  have hle_inv : ε⁻¹ ≤ (2 ^ epsLog ε : ℝ≥0∞) := by
    calc ε⁻¹ = ((ε⁻¹.toNNReal : ℝ≥0) : ℝ≥0∞) := hcoe.symm
      _ ≤ ((⌈ε⁻¹.toNNReal⌉₊ : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr h1
      _ = (⌈ε⁻¹.toNNReal⌉₊ : ℝ≥0∞) := rfl
      _ ≤ ((2 ^ epsLog ε : ℕ) : ℝ≥0∞) := Nat.cast_le.mpr (h2.trans h3)
      _ = (2 ^ epsLog ε : ℝ≥0∞) := by push_cast; rfl
  calc (1 / 2 : ℝ≥0∞) ^ epsLog ε
      = (2 ^ epsLog ε : ℝ≥0∞)⁻¹ := by rw [one_div, ENNReal.inv_pow]
    _ ≤ (ε⁻¹)⁻¹ := ENNReal.inv_le_inv.mpr hle_inv
    _ = ε := inv_inv ε

/-! ## Section 3: Expected cluster length bound across the two-stage seed distribution -/

private theorem sum_Icc_two_pow_mul_div_sq_le (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2)) ≤ 288 := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsum_eq :
        (∑ j ∈ Finset.Icc 1 (M + 1), (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2)) =
          288 - 288 / (2 ^ (M + 1) : ℝ) := by
      clear ih
      induction M with
      | zero =>
        simp
        ring
      | succ K ihK =>
        rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 (K + 1)), ihK, pow_succ']
        have hpow : (2 ^ (K + 1) : ℝ) ≠ 0 := by positivity
        field_simp [hpow]
        ring
    rw [hsum_eq]
    have : (0 : ℝ) ≤ 288 / (2 ^ (M + 1) : ℝ) := by positivity
    linarith

/-- Seed-only upper bound on the cluster length around `quotHash U w₀ n θ u` for any state
representing `S` (`#S ≤ n`). -/
@[expose] noncomputable def seedClusterBound (U w₀ n : ℕ) (S : Finset (Fin U)) (u : Fin U)
    (θ : QuotSeed w₀ n) : ℕ :=
  let b := quotBits w₀ n
  let T : Finset (Fin U) := insert u (S.erase u)
  if θ.1 ∈ reducedGoodTop U w₀ (3 * b) T then
    1 + ∑ j ∈ Finset.Icc 1 b,
      if scaleOverload b (fun β' x => quotHash U w₀ n (θ.1, β') x) (S.erase u) u j θ.2
      then 2 ^ j else 0
  else
    2 ^ b

/-- Pointwise bound of `hinv.clusterLen hS_lt (quotHash U w₀ n θ u)` by the state-independent
quantity `seedClusterBound U w₀ n S u θ`. -/
theorem FilterInv.clusterLen_le_seedClusterBound {U w₀ n f : ℕ}
    {S : Finset (Fin U)} {θ : QuotSeed w₀ n} {rem : Fin U → Fin (2 ^ f)}
    {st : FilterState (quotBits w₀ n) f}
    (hinv : FilterInv n S (quotHash U w₀ n θ) rem st)
    (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U) :
    hinv.clusterLen hS_lt (quotHash U w₀ n θ u) ≤ seedClusterBound U w₀ n S u θ := by
  dsimp only [seedClusterBound]
  split_ifs with hgood
  · have h1 := hinv.clusterLen_sub_one_le_sum_scaleOverload
      (fun β' x => quotHash U w₀ n (θ.1, β') x) θ.2 hS_lt u
    have hsum_eq :
        (∑ j ∈ Finset.Icc 1 (quotBits w₀ n),
          (2 ^ j : ℝ) *
            (if scaleOverload (quotBits w₀ n) (fun β' x => quotHash U w₀ n (θ.1, β') x)
              (S.erase u) u j θ.2 then (1 : ℝ) else 0)) =
        ((∑ j ∈ Finset.Icc 1 (quotBits w₀ n),
          if scaleOverload (quotBits w₀ n) (fun β' x => quotHash U w₀ n (θ.1, β') x)
            (S.erase u) u j θ.2 then 2 ^ j else 0 : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    rw [hsum_eq] at h1
    have h1_nat :
        hinv.clusterLen hS_lt (quotHash U w₀ n θ u) - 1 ≤
          ∑ j ∈ Finset.Icc 1 (quotBits w₀ n),
            if scaleOverload (quotBits w₀ n) (fun β' x => quotHash U w₀ n (θ.1, β') x)
              (S.erase u) u j θ.2 then 2 ^ j else 0 := by
      exact_mod_cast h1
    omega
  · exact (hinv.clusterLen_le_card hS_lt _).trans hS_lt.le

/-- For any top-level seed `α ∈ reducedGoodTop U w₀ (3 * quotBits w₀ n) (insert u (S.erase u))`
that is injective on `insert u (S.erase u)`, summing `seedClusterBound - 1` over all bottom
polynomial seeds `β : ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5` is bounded by
`288 * Fintype.card Bot`. -/
theorem sum_seedClusterBound_sub_one_goodTop_le {U w₀ n : ℕ} (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U)
    {α : ReducedTopSeed w₀}
    (hα : α ∈ reducedGoodTop U w₀ (3 * quotBits w₀ n) (insert u (S.erase u))) :
    (∑ β : ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5,
      (seedClusterBound U w₀ n S u (α, β) - 1)) ≤
      288 * Fintype.card (ReducedBotSeed w₀ (quotBits w₀ n) (quotBits w₀ n) 5) := by
  classical
  set b := quotBits w₀ n
  set Bot := ReducedBotSeed w₀ b b 5
  set T : Finset (Fin U) := insert u (S.erase u)
  have huT : u ∈ T := Finset.mem_insert_self u (S.erase u)
  set u' : T := ⟨u, huT⟩
  set S' : Finset T := T.attach.erase u'
  have hu'_notMem : u' ∉ S' := Finset.notMem_erase u' T.attach
  have hS'_card : #S' ≤ effCap w₀ n := by
    have h1 : #S' = #T.attach - 1 := Finset.card_erase_of_mem (Finset.mem_attach T u')
    have h2 : #T.attach = #T := Finset.card_attach
    have h3 : #T = #(S.erase u) + 1 := Finset.card_insert_of_notMem (Finset.notMem_erase u S)
    have h4 : #(S.erase u) ≤ effCap w₀ n := (Finset.card_erase_le).trans (card_le_effCap hU hS)
    omega
  have h8 : 8 * effCap w₀ n ≤ 2 ^ b := eight_mul_effCap_le_two_pow_quotBits w₀ n
  set hT : Bot → T → Fin (2 ^ b) := fun β x => quotHash U w₀ n (α, β) x.val
  have hkT : IsKWiseIndependentHash 5 hT :=
    isKWiseIndependentHash_reducedPolyHash_of_injOn (mem_reducedGoodTop.mp hα)
  have hov_iff :
      ∀ (j : ℕ) (β : Bot),
        scaleOverload b (fun β' x => quotHash U w₀ n (α, β') x) (S.erase u) u j β ↔
          scaleOverload b hT S' u' j β := by
    intro j β
    dsimp only [scaleOverload, hT, u']
    have hcard_filter :
        #((S.erase u).filter fun x =>
          quotHash U w₀ n (α, β) x ∈ scaleWindow b (quotHash U w₀ n (α, β) u) j) =
        #(S'.filter fun x : T =>
          quotHash U w₀ n (α, β) x.val ∈ scaleWindow b (quotHash U w₀ n (α, β) u) j) := by
      refine Finset.card_bij (fun x hx => ⟨x, Finset.mem_insert_of_mem (Finset.mem_filter.mp hx).1⟩)
        ?_ ?_ ?_
      · intro x hx
        have hx' := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ?_, hx'.2⟩
        exact ⟨fun h => (Finset.mem_erase.mp hx'.1).1 (congrArg Subtype.val h),
          Finset.mem_attach _ _⟩
      · intro x₁ _ x₂ _ h
        exact congrArg Subtype.val h
      · intro y hy
        have hy' := Finset.mem_filter.mp hy
        have hy_er := Finset.mem_erase.mp hy'.1
        have hy_erase : y.val ∈ S.erase u := by
          rcases Finset.mem_insert.mp y.property with h | h
          · exact False.elim (hy_er.1 (Subtype.ext h))
          · exact h
        exact ⟨y.val, Finset.mem_filter.mpr ⟨hy_erase, hy'.2⟩, rfl⟩
    rw [hcard_filter]
  have hpt (β : Bot) :
      ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ) ≤
        ∑ j ∈ Finset.Icc 1 b,
          (2 ^ j : ℝ) * (if scaleOverload b hT S' u' j β then (1 : ℝ) else 0) := by
    dsimp only [seedClusterBound]
    rw [ite_eq_left hα, Nat.add_sub_cancel_left, Nat.cast_sum]
    refine le_of_eq (Finset.sum_congr rfl fun j _ => ?_)
    rw [if_congr (hov_iff j β) rfl rfl]
    split_ifs <;> simp
  have hexp :
      (𝔼 β : Bot, ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ)) ≤ 288 := by
    calc (𝔼 β : Bot, ((seedClusterBound U w₀ n S u (α, β) - 1 : ℕ) : ℝ))
        ≤ 𝔼 β : Bot, ∑ j ∈ Finset.Icc 1 b,
            (2 ^ j : ℝ) * (if scaleOverload b hT S' u' j β then (1 : ℝ) else 0) :=
          Finset.expect_le_expect fun β _ => hpt β
      _ = ∑ j ∈ Finset.Icc 1 b,
            𝔼 β : Bot, (2 ^ j : ℝ) * (if scaleOverload b hT S' u' j β then (1 : ℝ) else 0) :=
          Finset.expect_sum_comm _ _ _
      _ ≤ ∑ j ∈ Finset.Icc 1 b, (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2) := by
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_Icc] at hj
          rw [Fintype.expect_eq_sum_div_card, ← Finset.mul_sum, mul_div_assoc,
            ← Fintype.expect_eq_sum_div_card]
          exact mul_le_mul_of_nonneg_left
            (expect_scaleOverload_le hkT S' hu'_notMem hS'_card h8 hj.1) (by positivity)
      _ ≤ 288 := sum_Icc_two_pow_mul_div_sq_le b
  rw [Fintype.expect_eq_sum_div_card] at hexp
  have hcard_pos : (0 : ℝ) < (Fintype.card Bot : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hcard_pos] at hexp
  exact_mod_cast hexp

/-- **Unconditional sum bound on `seedClusterBound` over `QuotSeed w₀ n`**:
for any `S : Finset (Fin U)` with `#S ≤ n` and any `u : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`),
the sum of `seedClusterBound` over all quotient seeds `θ : QuotSeed w₀ n` is at most
`290 * Fintype.card (QuotSeed w₀ n)`. -/
theorem sum_seedClusterBound_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑ θ : QuotSeed w₀ n, seedClusterBound U w₀ n S u θ) ≤
      290 * Fintype.card (QuotSeed w₀ n) := by
  classical
  set b := quotBits w₀ n
  set Top := ReducedTopSeed w₀
  set Bot := ReducedBotSeed w₀ b b 5
  set T : Finset (Fin U) := insert u (S.erase u)
  set Good : Finset Top := reducedGoodTop U w₀ (3 * b) T
  set Bad : Finset Top := Finset.univ \ Good
  have hprod_sum :
      (∑ θ : QuotSeed w₀ n, seedClusterBound U w₀ n S u θ) =
        ∑ α : Top, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β) :=
    Fintype.sum_prod_type _
  have hsplit :
      (∑ α : Top, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) =
        (∑ α ∈ Good, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) +
        (∑ α ∈ Bad, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) := by
    rw [← Finset.sum_union Finset.sdiff_disjoint.symm,
      Finset.union_sdiff_of_subset (Finset.subset_univ _)]
  have hgood_each :
      ∀ α ∈ Good,
        (∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
          289 * Fintype.card Bot := by
    intro α hα
    have hsub :
        (∑ β : Bot, (seedClusterBound U w₀ n S u (α, β) - 1)) ≤
          288 * Fintype.card Bot :=
      sum_seedClusterBound_sub_one_goodTop_le hU hS u hα
    have hle_add :
        (∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
          (∑ β : Bot, (seedClusterBound U w₀ n S u (α, β) - 1)) +
            Fintype.card Bot := by
      have h1 : (Fintype.card Bot : ℕ) = ∑ _β : Bot, 1 := by simp
      rw [h1, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun β _ => ?_
      omega
    omega
  have hsum_good :
      (∑ α ∈ Good, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
        289 * Fintype.card (QuotSeed w₀ n) := by
    calc (∑ α ∈ Good, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β))
        ≤ ∑ _α ∈ Good, 289 * Fintype.card Bot := Finset.sum_le_sum hgood_each
      _ = #Good * (289 * Fintype.card Bot) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ Fintype.card Top * (289 * Fintype.card Bot) :=
          Nat.mul_le_mul_right _ (Finset.card_le_univ Good)
      _ = 289 * (Fintype.card Top * Fintype.card Bot) := by ring
      _ = 289 * Fintype.card (QuotSeed w₀ n) := by rw [Fintype.card_prod]
  have hbad_card : #Bad * 2 ^ b ≤ Fintype.card Top := by
    have h1 := card_not_injOn_multiplyShiftReduced_le (R := 3 * b) hw₀ hU T
    have hT_le : #T ≤ 2 ^ b := by
      have hS_le : #(S.erase u) ≤ effCap w₀ n :=
        (Finset.card_erase_le).trans (card_le_effCap hU hS)
      have h8 : 8 * effCap w₀ n ≤ 2 ^ b := eight_mul_effCap_le_two_pow_quotBits w₀ n
      have h8' : 8 ≤ 2 ^ b := eight_le_two_pow_quotBits w₀ n
      have hT_card : #T ≤ #(S.erase u) + 1 := Finset.card_insert_le u (S.erase u)
      omega
    have hT_prod : #T * (#T - 1) ≤ 2 ^ (2 * b) := by
      calc #T * (#T - 1) ≤ #T * #T := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ ≤ 2 ^ b * 2 ^ b := Nat.mul_le_mul hT_le hT_le
        _ = 2 ^ (2 * b) := by rw [← pow_add, two_mul]
    have hpow_3b : 2 ^ (3 * b) = 2 ^ b * 2 ^ (2 * b) := by
      rw [← pow_add]
      congr 1
      omega
    have htop_card : Fintype.card Top = 2 ^ (w₀ - 1) := Fintype.card_fin _
    have h2 : (#Bad * 2 ^ b) * 2 ^ (2 * b) ≤ Fintype.card Top * 2 ^ (2 * b) := by
      calc (#Bad * 2 ^ b) * 2 ^ (2 * b)
          = #Bad * 2 ^ (3 * b) := by rw [hpow_3b]; ring
        _ ≤ (#T * (#T - 1)) * 2 ^ (w₀ - 1) := h1
        _ ≤ 2 ^ (2 * b) * 2 ^ (w₀ - 1) := Nat.mul_le_mul_right _ hT_prod
        _ = Fintype.card Top * 2 ^ (2 * b) := by rw [htop_card, mul_comm]
    exact Nat.le_of_mul_le_mul_right h2 (by positivity)
  have hsum_bad :
      (∑ α ∈ Bad, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β)) ≤
        Fintype.card (QuotSeed w₀ n) := by
    calc (∑ α ∈ Bad, ∑ β : Bot, seedClusterBound U w₀ n S u (α, β))
        ≤ ∑ _α ∈ Bad, ∑ _β : Bot, 2 ^ b := by
          refine Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun β _ => ?_
          have hnot : α ∉ Good := (Finset.mem_sdiff.mp hα).2
          dsimp only [seedClusterBound]
          rw [ite_eq_right hnot]
      _ = (#Bad * 2 ^ b) * Fintype.card Bot := by
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
          ring
      _ ≤ Fintype.card Top * Fintype.card Bot := by gcongr
      _ = Fintype.card (QuotSeed w₀ n) := (Fintype.card_prod Top Bot).symm
  rw [hprod_sum, hsplit]
  omega

/-- **`ℝ≥0∞` expectation bound on `seedClusterBound` under `filterSeedLaw w₀ n`**:
`∑' p : FilterSeed w₀ n, filterSeedLaw w₀ n p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞) ≤ 290`. -/
theorem tsum_seedClusterBound_le {U w₀ n : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (u : Fin U) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞)) ≤ 290 := by
  classical
  have hsum_all :
      (∑ p : FilterSeed w₀ n, seedClusterBound U w₀ n S u p.1) ≤
        290 * Fintype.card (FilterSeed w₀ n) := by
    rw [Fintype.sum_prod_type_right]
    calc (∑ _γ : RemSeed w₀, ∑ θ : QuotSeed w₀ n, seedClusterBound U w₀ n S u θ)
        ≤ ∑ _γ : RemSeed w₀, 290 * Fintype.card (QuotSeed w₀ n) := by
          refine Finset.sum_le_sum fun _ _ => sum_seedClusterBound_le hw₀ hU hS u
      _ = Fintype.card (RemSeed w₀) * (290 * Fintype.card (QuotSeed w₀ n)) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = 290 * (Fintype.card (QuotSeed w₀ n) * Fintype.card (RemSeed w₀)) := by ring
      _ = 290 * Fintype.card (FilterSeed w₀ n) := by
          rw [← Fintype.card_prod (QuotSeed w₀ n) (RemSeed w₀)]
  calc (∑' p : FilterSeed w₀ n,
        (filterSeedLaw w₀ n) p * (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞))
      = ∑ p : FilterSeed w₀ n,
          (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞)⁻¹ *
            (seedClusterBound U w₀ n S u p.1 : ℝ≥0∞) := by
        rw [tsum_fintype]
        simp [filterSeedLaw, PMF.uniformOfFintype_apply]
    _ = (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞)⁻¹ *
          ((∑ p : FilterSeed w₀ n, seedClusterBound U w₀ n S u p.1 : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum, Nat.cast_sum]
    _ ≤ (Fintype.card (FilterSeed w₀ n) : ℝ≥0∞)⁻¹ *
          ((290 * Fintype.card (FilterSeed w₀ n) : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = 290 := by
        push_cast
        rw [mul_comm (290 : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
        · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        · exact ENNReal.natCast_ne_top _

/-- **Unconditional sum bound on `clusterLen` over `QuotSeed w₀ n`**:
for any `S : Finset (Fin U)` with `#S ≤ n` and any `u : Fin U` (`0 < w₀`, `U ≤ 2 ^ w₀`),
the sum of `clusterLen` over all quotient seeds `θ : QuotSeed w₀ n` is at most
`290 * Fintype.card (QuotSeed w₀ n)`. -/
theorem sum_clusterLen_le {U w₀ n f : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U)
    {rem : Fin U → Fin (2 ^ f)}
    {st : QuotSeed w₀ n → FilterState (quotBits w₀ n) f}
    (hinv : ∀ θ : QuotSeed w₀ n, FilterInv n S (quotHash U w₀ n θ) rem (st θ)) :
    (∑ θ : QuotSeed w₀ n, (hinv θ).clusterLen hS_lt (quotHash U w₀ n θ u)) ≤
      290 * Fintype.card (QuotSeed w₀ n) :=
  (Finset.sum_le_sum fun θ _ => (hinv θ).clusterLen_le_seedClusterBound hS_lt u).trans
    (sum_seedClusterBound_le hw₀ hU hS u)

/-- **`ℝ≥0∞` expectation bound on `clusterLen` under `filterSeedLaw w₀ n`**:
`∑' p : FilterSeed w₀ n, filterSeedLaw w₀ n p * (clusterLen p.1 : ℝ≥0∞) ≤ 290`. -/
theorem tsum_clusterLen_le {U w₀ n f : ℕ} (hw₀ : 0 < w₀) (hU : U ≤ 2 ^ w₀)
    {S : Finset (Fin U)} (hS : #S ≤ n) (hS_lt : #S < 2 ^ quotBits w₀ n) (u : Fin U)
    {rem : RemSeed w₀ → Fin U → Fin (2 ^ f)}
    {st : FilterSeed w₀ n → FilterState (quotBits w₀ n) f}
    (hinv : ∀ p : FilterSeed w₀ n, FilterInv n S (quotHash U w₀ n p.1) (rem p.2) (st p)) :
    (∑' p : FilterSeed w₀ n,
      (filterSeedLaw w₀ n) p *
        ((hinv p).clusterLen hS_lt (quotHash U w₀ n p.1 u) : ℝ≥0∞)) ≤ 290 := by
  refine le_trans ?_ (tsum_seedClusterBound_le hw₀ hU hS u)
  gcongr with p
  exact Nat.cast_le.mpr ((hinv p).clusterLen_le_seedClusterBound hS_lt u)

end Cslib.DataStructure.ApproximateMembership.QuotientFilter
