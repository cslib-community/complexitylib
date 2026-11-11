/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.FairDivision.MMSAllocationLoss
public import CslibFrontier.GameTheory.FairDivision.MMSCodes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Uniform asymptotic MMS impossibility

[EzraGarbuz2027], Theorems 1 and 3 (PDF pp. 5–6, proofs pp. 12–14).
The explicit code in `MMSCodes` has distance at least k/32, rather than the
paper's k/4. We adjust the additive loss and constants accordingly. For every
n ≥ 65536 the actual construction has n agents and at most n+640 floor(log₂ n)
items. Exact MMS is proved using all partitions, and the universal loss uses
`universal_goods_loss` and `universal_chores_loss`, with no loss hypothesis.
The proportional share also equals MMS: each type's total value/cost is n times
204k³. The lower population bound, code choice and loss constants are uniform in n.

## Main results

- `population_hardness`: actual positive instances with exact MMS, proportional
  equality, uniform inverse-log-squared loss and a logarithmic excess of items.
- `inverse_polynomial_lt_gap`: every Cn⁻ε is eventually smaller than the loss
  for every real ε>0 and C≥0.
- `no_inverse_polynomial_guarantee`: actual goods and chores counterexamples to
  inverse-polynomial approximation errors for all sufficiently large populations.
-/

public section

open scoped BigOperators

namespace Cslib.FairDivision.MMSAsymptotic

/-- Code length used for a population of n agents. -/
@[expose] def populationLength (n : ℕ) : ℕ := 32 * (Nat.log 2 n + 1) + 32 * (Nat.log 2 n + 1)

/-- Dummy items fill out the population after the two distinguished and 2k Z slots. -/
@[expose] def populationDummies (n : ℕ) : ℕ := n - (2 * populationLength n + 2)

/-- Exactly n actual agents, with no fixed-population restriction. -/
theorem card_population (n : ℕ) (hn : 65536 ≤ n) :
    Fintype.card (HighGood (populationLength n) (populationDummies n)) = n := by
  have hi := MMSCodes.high_items_le_population n hn
  have hc (k d : ℕ) : Fintype.card (HighGood k d) = 2 * k + 2 + d := by
    simp [HighGood]
    omega
  rw [hc]
  dsimp only [populationLength, populationDummies]
  omega

/-- The explicit relative loss retained with the weaker code. Logarithms are
base two; the natural logarithm is used only in the later asymptotic proof. -/
@[expose] noncomputable def populationGap (n : ℕ) : ℝ := 1 / (4000000000 * (Nat.log 2 n : ℝ) ^ 2)

private theorem gap_le_loss (n : ℕ) (hn : 65536 ≤ n) :
    populationGap n * (204 * (populationLength n : ℝ) ^ 3) ≤ ((Nat.log 2 n + 1) / 4 : ℕ) := by
  let r := Nat.log 2 n
  have hr : 16 ≤ r := Nat.le_log_of_pow_le (by decide) (by norm_num; exact hn)
  have hr' : (16 : ℝ) ≤ r := by exact_mod_cast hr
  have hk : (populationLength n : ℝ) ≤ 128 * r := by
    dsimp only [populationLength]
    push_cast
    change 32 * ((r : ℝ) + 1) + 32 * (r + 1) ≤ _
    linarith
  have hl : (r : ℝ) ≤ 8 * ((r + 1) / 4 : ℕ) := by
    have hd := Nat.mod_lt (r + 1) (by decide : 0<4)
    have he := Nat.mod_add_div (r + 1) 4
    have hh : r ≤ 8 * ((r + 1) / 4) := by omega
    exact_mod_cast hh
  have hcube : (populationLength n : ℝ) ^ 3 ≤ (128 * (r : ℝ)) ^ 3 := by gcongr
  have hmul := mul_le_mul_of_nonneg_left hl (show 0 ≤ 500000000 * (r : ℝ) ^ 2 by positivity)
  have hbound : 204 * (populationLength n : ℝ) ^ 3 ≤
      4000000000 * (r : ℝ) ^ 2 * ((r + 1) / 4 : ℕ) := by
    nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) ^ 2 by positivity) (show 0 ≤ (r : ℝ) by positivity)]
  dsimp only [populationGap]
  change 1 / (4000000000 * (r : ℝ) ^ 2) * _ ≤ _
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)

/-- Theorems 1 and 3, with explicit constants for the constructed code. The same
positive integer items witness goods and chores hardness, each type has exact
MMS 204k³, and the number of agents is exactly n (`card_population`). -/
theorem population_hardness (n : ℕ) (hn : 65536 ≤ n) :
    let k := populationLength n
    let d := populationDummies n
    ∃ S : HighGood k d → Finset (Fin (2 * k)),
      (∀ i g, 0 < goodsValue k d (S i) g ∧ 0 < choreCost k d (S i) g) ∧
      (∀ i t, (Guarantees k d (S i) t ↔ t ≤ 204 * (k : ℤ) ^ 3) ∧
        (Caps k d (S i) t ↔ 204 * (k : ℤ) ^ 3 ≤ t)) ∧
      (∀ a : Allocation k d, ∃ i,
        ((∑ g ∈ bundle k d a i, goodsValue k d (S i) g : ℤ) : ℝ) <
          (1 - populationGap n) * (204 * (k : ℝ) ^ 3)) ∧
      (∀ a : Allocation k d, ∃ i,
        (1 + populationGap n) * (204 * (k : ℝ) ^ 3) <
          ((∑ g ∈ bundle k d a i, choreCost k d (S i) g : ℤ) : ℝ)) ∧
      (∀ i, (∑ g, goodsValue k d (S i) g) = (n : ℤ) * (204 * (k : ℤ) ^ 3) ∧
        (∑ g, choreCost k d (S i) g) = (n : ℤ) * (204 * (k : ℤ) ^ 3)) ∧
      Fintype.card (Good k d) ≤ n + 640 * Nat.log 2 n := by
  classical
  let k := populationLength n
  let d := populationDummies n
  let r := Nat.log 2 n
  have hk : 0 < k := by dsimp [k, populationLength]; omega
  have heven : 2 ∣ k := by dsimp [k, populationLength]; omega
  let e : HighGood k d ≃ Fin n := Fintype.equivFinOfCardEq (card_population n hn)
  obtain ⟨c, _, hc, hd⟩ := MMSCodes.exists_population_code n
  let S : HighGood k d → Finset (Fin (2 * k)) := fun i => labelSet (c (e i))
  have hS (i) : (S i).card = k := card_labelSet _
  have hbal (i) : (Finset.univ.filter fun h => c (e i) h).card = k / 2 := by
    have hh := hc (e i)
    dsimp only [k, populationLength]
    omega
  have hU (i) : (∑ j ∈ S i, k * (6 * k + j.val)) = 7 * k * k * k - k * k / 2 :=
    labelSet_x_weight _ heven (hbal i)
  let l : ℤ := ((r + 1) / 4 : ℕ)
  have hl : l < k := by dsimp [l, k, populationLength, r]; omega
  have hdist (i j) (hij : i ≠ j) : 5 * l < ((S i \ S j).card : ℤ) := by
    have hh := hd (e i) (e j) (e.injective.ne hij)
    have hid : (S i \ S j).card = hammingDist (c (e i)) (c (e j)) :=
      labelSet_sdiff_card (c (e i)) (c (e j))
    rw [hid]
    dsimp only [l, r]
    omega
  refine ⟨S, fun i g => ⟨goodsValue_pos k d hk _ g, choreCost_pos k d hk _ g⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    have hg := guarantees_iff k d (S i) (hS i) (hU i) t
    have hch := caps_iff k d (S i) (hS i) (hU i) t
    have he : 204 * (k : ℤ) * k * k = 204 * (k : ℤ) ^ 3 := by ring
    rw [he] at hg hch
    exact ⟨hg, hch⟩
  · intro a
    obtain ⟨i, hi⟩ := universal_goods_loss hk S hS hU l hl hdist a
    refine ⟨i, ?_⟩
    have hgap := gap_le_loss n hn
    have hc : ((∑ g ∈ bundle k d a i, goodsValue k d (S i) g : ℤ) : ℝ) <
        204 * (k : ℝ) ^ 3 - (l : ℝ) := by exact_mod_cast hi
    change populationGap n * (204 * (k : ℝ) ^ 3) ≤ (l : ℝ) at hgap
    nlinarith
  · intro a
    obtain ⟨i, hi⟩ := universal_chores_loss hk S hS hU l hl hdist a
    refine ⟨i, ?_⟩
    have hgap := gap_le_loss n hn
    have hc : 204 * (k : ℝ) ^ 3 + (l : ℝ) <
        ((∑ g ∈ bundle k d a i, choreCost k d (S i) g : ℤ) : ℝ) := by exact_mod_cast hi
    change populationGap n * (204 * (k : ℝ) ^ 3) ≤ (l : ℝ) at hgap
    nlinarith
  · intro i
    have hpop : (2 * (k : ℤ) + 2 + d) = n := by
      have hn' : 2 * k + 2 + d = n := by
        have hi := MMSCodes.high_items_le_population n hn
        dsimp only [k, d, populationDummies, populationLength]
        omega
      exact_mod_cast hn'
    constructor
    · rw [goodsValue_total k d (S i) (hS i), hpop]
      ring
    · rw [choreCost_total k d (S i) (hS i), hpop]
      ring
  · exact (MMSCodes.population_item_count n hn).2

/-- Every inverse-polynomial error is eventually smaller than the constructed
inverse-log-squared loss, for every real exponent ε>0 and every constant C≥0. -/
theorem inverse_polynomial_lt_gap (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, C * (n : ℝ) ^ (-ε) < populationGap n := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a : ℝ := (Real.log 2) ^ 2 / (8000000000 * (C + 1))
  have ha : 0 < a := by dsimp only [a]; positivity
  have hh := (isLittleO_log_rpow_rpow_atTop 2 hε).bound ha
  have hn : ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n : ℝ)) ^ 2 ≤ a * (n : ℝ) ^ ε := by
    have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hh
    filter_upwards [ht] with n hn
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) ε)] using hn
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hn
  refine ⟨max N 65536, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hr : 0 < Nat.log 2 n := by
    have hh : 16 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by norm_num; omega)
    omega
  have hr' : (0 : ℝ) < Nat.log 2 n := by exact_mod_cast hr
  have hl := Real.natLog_le_logb n 2
  simp only [Nat.cast_ofNat, Real.logb] at hl
  have hl' : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log n := (le_div_iff₀ hlog).mp hl
  have hlogn : 0 ≤ Real.log (n : ℝ) := le_trans (by positivity) hl'
  have hs : (Nat.log 2 n : ℝ) ^ 2 * (Real.log 2) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_self_le_mul_self (show 0 ≤ (Nat.log 2 n : ℝ) * Real.log 2 by positivity) hl'
    nlinarith only [hm]
  have hb := hN n (by omega)
  dsimp only [a] at hb
  rw [div_mul_eq_mul_div] at hb
  have hb' := (le_div_iff₀ (show 0 < 8000000000 * (C + 1) by positivity)).mp hb
  have hs' : (Nat.log 2 n : ℝ) ^ 2 ≤ (n : ℝ) ^ ε / (8000000000 * (C + 1)) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 8000000000 * (C + 1) by positivity)
    nlinarith [sq_pos_of_pos hlog]
  have hp := Real.rpow_pos_of_pos hn0 ε
  have hm := mul_le_mul_of_nonneg_left hs' (show 0 ≤ 4000000000 * C by positivity)
  have hprod : 4000000000 * (Nat.log 2 n : ℝ) ^ 2 * C < (n : ℝ) ^ ε := by
    have ht : 4000000000 * C * ((n : ℝ) ^ ε / (8000000000 * (C + 1))) < (n : ℝ) ^ ε := by
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith
    nlinarith
  rw [Real.rpow_neg hn0.le, ← div_eq_mul_inv]
  dsimp only [populationGap]
  exact (div_lt_div_iff₀ hp (by positivity)).mpr (by nlinarith)

/-- The inverse-polynomial guarantees excluded by Theorems 1 and 3: uniformly
for every sufficiently large population there is an actual instance defeating
both 1-Cn⁻ε goods and 1+Cn⁻ε chores guarantees. -/
theorem no_inverse_polynomial_guarantee (ε C : ℝ) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N,
      let k := populationLength n
      let d := populationDummies n
      ∃ S : HighGood k d → Finset (Fin (2 * k)),
        (∀ i t, (Guarantees k d (S i) t ↔ t ≤ 204 * (k : ℤ) ^ 3) ∧
          (Caps k d (S i) t ↔ 204 * (k : ℤ) ^ 3 ≤ t)) ∧
        (∀ a : Allocation k d, ∃ i,
          ((∑ g ∈ bundle k d a i, goodsValue k d (S i) g : ℤ) : ℝ) <
            (1 - C * (n : ℝ) ^ (-ε)) * (204 * (k : ℝ) ^ 3)) ∧
        (∀ a : Allocation k d, ∃ i,
          (1 + C * (n : ℝ) ^ (-ε)) * (204 * (k : ℝ) ^ 3) <
            ((∑ g ∈ bundle k d a i, choreCost k d (S i) g : ℤ) : ℝ)) ∧
        Fintype.card (Good k d) ≤ n + 640 * Nat.log 2 n := by
  obtain ⟨N, hN⟩ := inverse_polynomial_lt_gap ε C hε hC
  refine ⟨max N 65536, fun n hn => ?_⟩
  obtain ⟨S, _, hM, hg, hc, _, hitems⟩ := population_hardness n (by omega)
  refine ⟨S, hM, ?_, ?_, hitems⟩
  · intro a
    obtain ⟨i, hi⟩ := hg a
    refine ⟨i, ?_⟩
    have hh := hN n (by omega)
    have hp : 0 < (204 * (populationLength n : ℝ) ^ 3) := by
      have : 0 < populationLength n := by dsimp [populationLength]; omega
      positivity
    nlinarith
  · intro a
    obtain ⟨i, hi⟩ := hc a
    refine ⟨i, ?_⟩
    have hh := hN n (by omega)
    have hp : 0 < (204 * (populationLength n : ℝ) ^ 3) := by
      have : 0 < populationLength n := by dsimp [populationLength]; omega
      positivity
    nlinarith

end Cslib.FairDivision.MMSAsymptotic
