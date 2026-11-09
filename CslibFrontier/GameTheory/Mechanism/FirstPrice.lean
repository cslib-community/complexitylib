/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Bayesian
public import CslibFrontier.GameTheory.Mechanism.Vickrey
import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The first-price auction

A single item is sold to the highest bidder, ties being broken in favour of the smallest index as
in `SingleParameter.Vickrey.allocation`; the winner pays its own bid and losers pay nothing
(winner-pays-bid, [Hartline2021], Chapter 2, §2.3 and equation (2.7.1)). Unlike the second-price
auction, the first-price auction is not DSIC, and bidders shade their bids below their values.

For `n` bidders with independent valuations uniform on `[0, 1]`, bidding `β(v) = (n − 1) v / n`
is a Bayes–Nash equilibrium (`FirstPrice.isBayesNash_uniformBid`), with expected revenue
`(n − 1) / (n + 1)` (`FirstPrice.integral_sum_payment_uniformBid`), the same as the second-price
auction's. For two bidders this is [Hartline2021], §2.3 and Example 2.8.1, where each bidder bids
half its value, and the revenue comparison `1/3 = 1/3` of §2.7. The `n`-bidder statement is the
standard generalization of that example. We derive it with Hartline's method of revenue
equivalence (§2.8) and do not quote it from a source.

The proof of the equilibrium goes through the characterization `Mechanism.isBayesNash_iff` of
`CslibFrontier.GameTheory.Mechanism.Bayesian`. Under `β` a bid `z` wins with probability
`min(z / c, 1)^(n − 1)` where `c = (n − 1) / n` (`FirstPrice.interimAllocation_uniformBid`), so the
interim allocation of the type `v` is `v^(n − 1)`: monotone, and its payment `β(v) v^(n − 1)` is the
payment identity's `v^n − ∫₀^v z^(n − 1) dz`. Bids above `c` are dominated by the bid `c`, which
also wins for sure (Example 2.8.1 (v)(b) for `n = 2`).

## Main definitions

* `SingleParameter.FirstPrice.mechanism`: the first-price auction.
* `SingleParameter.FirstPrice.uniformBid n`: the bidding strategy `v ↦ (n − 1) v / n`.

## Main results

* `SingleParameter.FirstPrice.isBayesNash_uniformBid`: for `n` bidders with values uniform on
  `[0, 1]`, all bidding `uniformBid n` is a Bayes–Nash equilibrium.
* `SingleParameter.FirstPrice.not_isBayesNash_id`: with at least two bidders, truthful bidding is
  not a Bayes–Nash equilibrium of the first-price auction.
* `SingleParameter.FirstPrice.integral_sum_payment_uniformBid`: its expected revenue is
  `(n − 1) / (n + 1)`.
* `SingleParameter.FirstPrice.integral_sum_payment_uniformBid_eq_vickrey`: **revenue equivalence
  of the first- and second-price auctions** for uniform values ([Hartline2021], Corollary 2.7.2,
  for the uniform distribution), proved from the Bayes–Nash revenue formula
  `Mechanism.IsBayesNash.integral_sum_payment_eq` for the first-price auction and the DSIC revenue
  formula for the truthful second-price auction.
* `SingleParameter.FirstPrice.integral_sum_payment_vickrey`: the expected revenue of the
  second-price auction for `n` uniform bidders is `(n − 1) / (n + 1)`, the expected second-highest
  value (`1/3` for two bidders, [Hartline2021], §2.7).

Uniqueness of the equilibrium ([Hartline2021], §2.9) and equilibria for other value distributions
are not formalized.

## References

* [J. D. Hartline, *Mechanism Design and Approximation*][Hartline2021]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter.FirstPrice

open Vickrey

variable {ι : Type*} [LinearOrder ι]

/-- The **first-price auction**: the highest bidder wins, ties going to the smallest index, and pays
its bid; losers pay nothing ([Hartline2021], §2.3). -/
@[expose] noncomputable def mechanism : Mechanism ι where
  allocation := Vickrey.allocation
  payment b i := b i * Vickrey.allocation b i

/-- The bidding strategy `v ↦ (n − 1) v / n`, the symmetric Bayes–Nash equilibrium of the
first-price auction with `n` bidders whose values are uniform on `[0, 1]`. -/
@[expose] noncomputable def uniformBid (n : ℕ) (v : ℝ) : ℝ := (n - 1) / n * v

theorem measurable_uniformBid (n : ℕ) : Measurable (uniformBid n) :=
  measurable_const.mul measurable_id

/-- With two bidders each bids half its value ([Hartline2021], §2.3). -/
theorem uniformBid_two (v : ℝ) : uniformBid 2 v = v / 2 := by
  rw [uniformBid]
  push_cast
  ring

private theorem unif_isProb : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

private theorem unif_Iic {a : ℝ} (ha : 0 ≤ a) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (Iic a) = min a 1 := by
  have hset : Iic a ∩ Icc (0 : ℝ) 1 = Icc 0 (min a 1) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Icc, le_min_iff]
    tauto
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal (le_min ha zero_le_one)]

private theorem unif_Iio {a : ℝ} (ha : 0 ≤ a) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (Iio a) = min a 1 := by
  rw [measureReal_congr Iio_ae_eq_Iic, unif_Iic ha]

private theorem coeff_pos {n : ℕ} (hn : 2 ≤ n) : 0 < ((n : ℝ) - 1) / n := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact div_pos (by linarith) (by linarith)

private theorem coeff_nonneg (n : ℕ) : 0 ≤ ((n : ℝ) - 1) / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    exact div_nonneg (by linarith) (Nat.cast_nonneg n)

private theorem coeff_le_one (n : ℕ) : ((n : ℝ) - 1) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    linarith

theorem uniformBid_nonneg (n : ℕ) {v : ℝ} (hv : 0 ≤ v) : 0 ≤ uniformBid n v :=
  mul_nonneg (coeff_nonneg n) hv

variable [Fintype ι]

omit [Fintype ι] in
theorem mechanism_allocation : (mechanism (ι := ι)).allocation = Vickrey.allocation := rfl

/-- **Winner pays bid** ([Hartline2021], equation (2.7.1)): the interim payment at bid `z` is `z`
times the interim allocation at `z`. -/
theorem interimPayment_eq (μ : ι → Measure ℝ) (β : ι → ℝ → ℝ) (i : ι) (z : ℝ) :
    mechanism.interimPayment μ β i z = z * mechanism.interimAllocation μ β i z := by
  simp only [Mechanism.interimPayment, Mechanism.interimAllocation, mechanism,
    Function.update_self]
  exact integral_const_mul z _

/-- Interim allocation of the first-price auction when the other bidders, with values uniform on
`[0, 1]`, bid the linear strategy `v ↦ c v`. -/
private theorem interimAllocation_mul (c : ℝ) (hc : 1 < Fintype.card ι → 0 < c) (i : ι) {z : ℝ}
    (hz : 0 ≤ z) :
    mechanism.interimAllocation (fun _ => volume.restrict (Icc (0 : ℝ) 1)) (fun _ v => c * v) i z =
      min (z / c) 1 ^ (Fintype.card ι - 1) := by
  have := unif_isProb
  set n := Fintype.card ι
  have hmc : Measurable fun v : ℝ => c * v := measurable_const.mul measurable_id
  set s : ι → Set ℝ := fun j => if j = i then univ else
    if j < i then {t | c * t < z} else {t | c * t ≤ z} with hs
  have hwin : ∀ v : ι → ℝ, Wins (Function.update (fun j => c * v j) i z) i ↔
      v ∈ univ.pi s := by
    intro v
    simp only [Wins, mem_univ_pi, hs]
    refine forall_congr' fun j => ?_
    rcases eq_or_ne j i with rfl | hj
    · simp only [ne_eq, not_true_eq_false, IsEmpty.forall_iff, ite_true, mem_univ]
    · rw [Function.update_self, Function.update_of_ne hj, ite_eq_right hj]
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · rw [ite_eq_left hlt]
        simp only [mem_ofPred_eq, ne_eq, hj, not_false_eq_true, hlt, forall_const]
        exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
      · rw [ite_eq_right (not_lt.2 hgt.le)]
        simp only [mem_ofPred_eq, ne_eq, hj, not_false_eq_true, forall_const]
        exact ⟨fun h => h.1, fun h => ⟨h, fun hlt => absurd hlt (not_lt.2 hgt.le)⟩⟩
  have hind : (fun v : ι → ℝ => mechanism.allocation
      (Function.update (fun j => c * v j) i z) i) = (univ.pi s).indicator 1 := by
    funext v
    by_cases h : v ∈ univ.pi s
    · rw [indicator_of_mem h, mechanism_allocation, allocation_eq_one_iff.2 ((hwin v).2 h)]
      rfl
    · rw [indicator_of_notMem h, mechanism_allocation,
        allocation_eq_zero_iff.2 (mt (hwin v).1 h)]
  have hsm : ∀ j, MeasurableSet (s j) := by
    intro j
    simp only [hs]
    split_ifs
    · exact MeasurableSet.univ
    · exact measurableSet_lt hmc measurable_const
    · exact measurableSet_le hmc measurable_const
  have hsj : ∀ j, j ≠ i → (volume.restrict (Icc (0 : ℝ) 1)).real (s j) = min (z / c) 1 := by
    intro j hj
    have hcpos : 0 < c := hc (Fintype.one_lt_card_iff.2 ⟨j, i, hj⟩)
    have hzc : 0 ≤ z / c := div_nonneg hz hcpos.le
    have hlo : Iio (z / c) ⊆ s j := by
      intro t ht
      simp only [hs, ite_eq_right hj]
      have : c * t < z := by
        rw [mem_Iio, lt_div_iff₀ hcpos] at ht
        linarith
      split_ifs
      · exact this
      · exact this.le
    have hhi : s j ⊆ Iic (z / c) := by
      intro t ht
      simp only [hs, ite_eq_right hj] at ht
      have : c * t ≤ z := by
        split_ifs at ht
        · exact (show c * t < z from ht).le
        · exact ht
      rw [mem_Iic, le_div_iff₀ hcpos]
      linarith
    refine le_antisymm ?_ ?_
    · rw [← unif_Iic hzc]
      exact measureReal_mono hhi
    · rw [← unif_Iio hzc]
      exact measureReal_mono hlo
  simp only [Mechanism.interimAllocation]
  rw [hind, integral_indicator_one (MeasurableSet.univ_pi hsm), measureReal_def, Measure.pi_pi,
    ENNReal.toReal_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  have hsi : s i = univ := by simp only [hs, ↓reduceIte]
  rw [hsi, measure_univ, ENNReal.toReal_one, one_mul,
    Finset.prod_congr rfl fun j hj => (measureReal_def _ _).symm.trans
      (hsj j (Finset.ne_of_mem_erase hj)), Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]

/-- **Interim allocation** of the first-price auction under `uniformBid`: against `n − 1` bidders
with values uniform on `[0, 1]` bidding `c v`, `c = (n − 1) / n`, a bid `z ≥ 0` wins with
probability `min(z / c, 1)^(n − 1)`. -/
theorem interimAllocation_uniformBid (i : ι) {z : ℝ} (hz : 0 ≤ z) :
    mechanism.interimAllocation (fun _ => volume.restrict (Icc (0 : ℝ) 1))
        (fun _ => uniformBid (Fintype.card ι)) i z =
      min (z / ((Fintype.card ι - 1) / Fintype.card ι)) 1 ^ (Fintype.card ι - 1) :=
  interimAllocation_mul (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) (fun h => coeff_pos h) i hz

/-- At a valuation `v ∈ [0, 1]`, the interim allocation under `uniformBid` is `v^(n−1)`, the
probability that `v` is the highest of `n` uniform values. -/
theorem interimAllocation_uniformBid_uniformBid (i : ι) {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    mechanism.interimAllocation (fun _ => volume.restrict (Icc (0 : ℝ) 1))
        (fun _ => uniformBid (Fintype.card ι)) i (uniformBid (Fintype.card ι) v) =
      v ^ (Fintype.card ι - 1) := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
  rw [interimAllocation_uniformBid i (uniformBid_nonneg _ hv.1)]
  rcases (show Fintype.card ι = 1 ∨ 2 ≤ Fintype.card ι by omega) with h1 | h2
  · rw [h1, Nat.sub_self, pow_zero, pow_zero]
  · rw [uniformBid, mul_div_cancel_left₀ _ (coeff_pos h2).ne', min_eq_left hv.2]

/-- A bid of at least `(n − 1) / n` wins for sure against `uniformBid`. -/
theorem interimAllocation_uniformBid_of_le (i : ι) {z : ℝ}
    (hz : ((Fintype.card ι : ℝ) - 1) / Fintype.card ι ≤ z) :
    mechanism.interimAllocation (fun _ => volume.restrict (Icc (0 : ℝ) 1))
        (fun _ => uniformBid (Fintype.card ι)) i z = 1 := by
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
  rw [interimAllocation_uniformBid i ((coeff_nonneg _).trans hz)]
  rcases (show Fintype.card ι = 1 ∨ 2 ≤ Fintype.card ι by omega) with h1 | h2
  · rw [h1, Nat.sub_self, pow_zero]
  · rw [min_eq_right ((one_le_div (coeff_pos h2)).2 hz), one_pow]

/-- **The first-price equilibrium for uniform values** ([Hartline2021], §2.3 and Example 2.8.1 for
two bidders). With `n` bidders whose values are independent and uniform on `[0, 1]`, every bidder
bidding `(n − 1) v / n` is a Bayes–Nash equilibrium of the first-price auction. -/
theorem isBayesNash_uniformBid :
    mechanism.IsBayesNash (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) (fun _ => 1)
      (fun _ => uniformBid (Fintype.card ι)) := by
  rw [Mechanism.isBayesNash_iff]
  intro i
  have hn : 0 < Fintype.card ι := Fintype.card_pos_iff.2 ⟨i⟩
  have hX := fun v (hv : v ∈ Icc (0 : ℝ) 1) => interimAllocation_uniformBid_uniformBid i hv
  refine ⟨fun v hv => uniformBid_nonneg _ hv.1, ?_, ?_, ?_⟩
  · intro w hw v hv hwv
    simp only [hX v hv, hX w hw]
    exact pow_le_pow_left₀ hw.1 hwv _
  · intro v hv
    rw [interimPayment_eq, interimPayment_eq, hX v hv]
    have hint : ∫ z in (0 : ℝ)..v, mechanism.interimAllocation
        (fun _ => volume.restrict (Icc (0 : ℝ) 1)) (fun _ => uniformBid (Fintype.card ι)) i
          (uniformBid (Fintype.card ι) z) = ∫ z in (0 : ℝ)..v, z ^ (Fintype.card ι - 1) := by
      refine intervalIntegral.integral_congr fun z hz => ?_
      rw [uIcc_of_le hv.1] at hz
      exact hX z ⟨hz.1, hz.2.trans hv.2⟩
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card ι = k + 1 := ⟨Fintype.card ι - 1, by omega⟩
    have hk' : (Fintype.card ι : ℝ) = k + 1 := by rw [hk]; push_cast; ring
    rw [hint, integral_pow, uniformBid, uniformBid, mul_zero, zero_mul, zero_add,
      show Fintype.card ι - 1 = k by omega, hk', zero_pow (Nat.succ_ne_zero k), sub_zero]
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  · intro v hv z hz
    rcases lt_or_ge z (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) with hzc | hzc
    · have hcpos : 0 < ((Fintype.card ι : ℝ) - 1) / Fintype.card ι := hz.trans_lt hzc
      refine ⟨z / (((Fintype.card ι : ℝ) - 1) / Fintype.card ι),
        ⟨div_nonneg hz hcpos.le, (div_le_one hcpos).2 hzc.le⟩, ?_⟩
      rw [uniformBid, mul_div_cancel₀ _ hcpos.ne']
    · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
      have h1 : uniformBid (Fintype.card ι) 1 = ((Fintype.card ι : ℝ) - 1) / Fintype.card ι := by
        rw [uniformBid, mul_one]
      rw [interimPayment_eq, interimPayment_eq, interimAllocation_uniformBid_of_le i hzc,
        interimAllocation_uniformBid_of_le i h1.ge, h1]
      linarith

/-- **Bid shading.** With at least two bidders whose values are uniform on `[0, 1]`, truthful
bidding is not a Bayes–Nash equilibrium of the first-price auction: by bidding `1/2` instead of
its value, which leaves it nothing, the type `1` wins with probability `2^(1 − n)` and gains
utility `(1 − 1/2) · 2^(1 − n) = 2^(−n) > 0`. -/
theorem not_isBayesNash_id (hn : 1 < Fintype.card ι) :
    ¬ mechanism.IsBayesNash (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) (fun _ => 1)
      (fun _ v => v) := by
  intro hM
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  have hX : ∀ z, 0 ≤ z → mechanism.interimAllocation (fun _ => volume.restrict (Icc (0 : ℝ) 1))
      (fun _ v => v) i z = min z 1 ^ (Fintype.card ι - 1) := fun z hz => by
    have := interimAllocation_mul (ι := ι) 1 (fun _ => one_pos) i hz
    simp only [one_mul, div_one] at this
    exact this
  have h := (hM i 1 ⟨zero_le_one, le_rfl⟩).2 (1 / 2) (by norm_num)
  rw [interimPayment_eq, interimPayment_eq, hX _ (by norm_num), hX _ zero_le_one,
    min_eq_left (by norm_num), min_self, one_pow] at h
  have : 0 < ((1 : ℝ) / 2) ^ (Fintype.card ι - 1) := by positivity
  linarith

theorem integrable_payment_uniformBid (i : ι) :
    Integrable (fun v : ι → ℝ => mechanism.payment (fun j => uniformBid (Fintype.card ι) (v j)) i)
      (Measure.pi fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) := by
  have := unif_isProb
  have hm : Measurable fun v : ι → ℝ => Vickrey.allocation
      (fun j => uniformBid (Fintype.card ι) (v j)) i :=
    (measurable_allocation i).comp
      (measurable_pi_iff.2 fun j => (measurable_uniformBid _).comp (measurable_pi_apply j))
  refine Integrable.of_bound
    (((measurable_uniformBid _).comp (measurable_pi_apply i)).mul hm).aestronglyMeasurable 1 ?_
  filter_upwards [ae_mem_box fun _ : ι => hasValueDensity_uniform] with v hv
  have h2 : |Vickrey.allocation (fun j => uniformBid (Fintype.card ι) (v j)) i| ≤ 1 := by
    rcases allocation_binary (fun j => uniformBid (Fintype.card ι) (v j)) i with h | h <;>
      rw [h] <;> norm_num
  have h1 : |uniformBid (Fintype.card ι) (v i)| ≤ 1 := by
    rw [abs_of_nonneg (uniformBid_nonneg _ (hv i).1)]
    exact (mul_le_of_le_one_left (hv i).1 (coeff_le_one _)).trans (hv i).2
  change ‖uniformBid (Fintype.card ι) (v i) *
    Vickrey.allocation (fun j => uniformBid (Fintype.card ι) (v j)) i‖ ≤ 1
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) h1).trans h2

/-- **Expected revenue of the first-price auction** for `n` uniform bidders in the equilibrium
`uniformBid n`: `(n − 1) / (n + 1)`. Each bidder pays
`E[β(v) v^(n − 1)] = (n − 1) / (n (n + 1))`. -/
theorem integral_sum_payment_uniformBid [Nonempty ι] :
    ∫ v, ∑ i, mechanism.payment (fun j => uniformBid (Fintype.card ι) (v j)) i
        ∂Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) =
      ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι + 1) := by
  have := unif_isProb
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  rw [integral_finsetSum _ fun i _ => integrable_payment_uniformBid i]
  have hi : ∀ i, ∫ v, mechanism.payment (fun j => uniformBid (Fintype.card ι) (v j)) i
      ∂Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) =
        ((Fintype.card ι : ℝ) - 1) / Fintype.card ι / (Fintype.card ι + 1) := by
    intro i
    rw [Mechanism.integral_payment_eq_integral_interimPayment _ _ i
      (integrable_payment_uniformBid i)]
    have hae : ∀ᵐ z ∂(volume.restrict (Icc (0 : ℝ) 1)),
        mechanism.interimPayment (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))
          (fun _ => uniformBid (Fintype.card ι)) i (uniformBid (Fintype.card ι) z) =
        ((Fintype.card ι : ℝ) - 1) / Fintype.card ι * z ^ Fintype.card ι := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      rw [interimPayment_eq, interimAllocation_uniformBid_uniformBid i hz, uniformBid, mul_assoc,
        ← pow_succ', Nat.sub_add_cancel hn]
    rw [integral_congr_ae hae, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le zero_le_one, integral_pow, one_pow,
      zero_pow (Nat.succ_ne_zero _), sub_zero]
    ring
  rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- **Revenue equivalence of the first- and second-price auctions** for values uniform on
`[0, 1]` ([Hartline2021], Corollary 2.7.2, for the uniform distribution): the first-price auction
in the equilibrium `uniformBid n` and the second-price auction with truthful bids have the same
expected revenue. The proof is the method of revenue equivalence: both equilibria allocate to the
highest-valued bidder and the zero type pays nothing in both, so both revenues equal the expected
virtual welfare of the highest-value allocation (`Mechanism.IsBayesNash.integral_sum_payment_eq`
and `Mechanism.IsDSIC.integral_sum_payment_eq`). -/
theorem integral_sum_payment_uniformBid_eq_vickrey :
    ∫ v, ∑ i, mechanism.payment (fun j => uniformBid (Fintype.card ι) (v j)) i
        ∂Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) =
      ∫ v, ∑ i, Vickrey.mechanism.payment v i
        ∂Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) := by
  have := unif_isProb
  have hB : ∀ b : ι → ℝ, 0 ≤ b → ∀ i, |Vickrey.allocation b i| ≤ 1 := fun b _ i => by
    rcases allocation_binary b i with h | h <;> rw [h] <;> norm_num
  have hm : ∀ i, Measurable fun v : ι → ℝ => Vickrey.allocation
      (fun j => uniformBid (Fintype.card ι) (v j)) i := fun i =>
    (measurable_allocation i).comp
      (measurable_pi_iff.2 fun j => (measurable_uniformBid _).comp (measurable_pi_apply j))
  rw [isBayesNash_uniformBid.integral_sum_payment_eq (fun _ => hasValueDensity_uniform)
      integrable_payment_uniformBid hm hB,
    Vickrey.mechanism_isDSIC.integral_sum_payment_eq Vickrey.mechanism_isNormalized
      (fun _ => hasValueDensity_uniform) (fun i => measurable_allocation i) hB]
  have h0 : ∀ i, mechanism.interimPayment (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1))
      (fun _ => uniformBid (Fintype.card ι)) i (uniformBid (Fintype.card ι) 0) = 0 := fun i => by
    rw [interimPayment_eq, uniformBid, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => h0 i, Finset.sum_const_zero, zero_add]
  congr 1
  funext v
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  change Vickrey.allocation _ i = Vickrey.allocation v i
  rcases (show Fintype.card ι ≤ 1 ∨ 2 ≤ Fintype.card ι by omega) with h1 | h2
  · have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 h1
    rw [allocation_eq_one_iff.2 (wins_of_subsingleton _ i),
      allocation_eq_one_iff.2 (wins_of_subsingleton _ i)]
  · exact allocation_comp (φ := uniformBid (Fintype.card ι))
      (strictMono_mul_left_of_pos (coeff_pos h2)) v i

/-- **Expected revenue of the second-price auction** for `n` bidders with values uniform on
`[0, 1]` and truthful bids: `(n − 1) / (n + 1)`, the expected second-highest value (`1/3` for two
bidders, [Hartline2021], §2.7). -/
theorem integral_sum_payment_vickrey [Nonempty ι] :
    ∫ v, ∑ i, Vickrey.mechanism.payment v i
        ∂Measure.pi (fun _ : ι => volume.restrict (Icc (0 : ℝ) 1)) =
      ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι + 1) := by
  rw [← integral_sum_payment_uniformBid_eq_vickrey, integral_sum_payment_uniformBid]

end Cslib.GameTheory.SingleParameter.FirstPrice
