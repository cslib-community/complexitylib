/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.SmallBias
public import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Foundations.Combinatorics.Subsets.Geometric
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic.Linarith

/-!
# Pointwise bounds from parity biases

Fourier inversion bounds the relative error of each atom by the sum of the absolute nonempty
parity biases. Unlike a statistical-distance estimate, this implies that every string is in
the support when that sum is less than one. This is the pointwise version of Vazirani's lemma
used in low-discrepancy lifting [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, Lemma 2.5]
[ChattopadhyayFilmusKorothMeirPitassi2021], including its cardinality-dependent bias hypothesis.
Controlling only high-order parities gives the min-entropy variant, Lemma 2.6 of the same source.

## Main results

* `Cslib.BitString.bias_bind_map_eq`: bias of an independent two-source output law.
* `Cslib.BitString.abs_mul_mass_sub_one_le_of_bias_le`: pointwise multiplicative error.
* `Cslib.BitString.le_minEntropy_of_high_order_bias_le`: the min-entropy variant.
* `Cslib.BitString.mem_support_of_sum_abs_bias_lt_one`: full support from a bias-sum bound.
-/

public section

namespace Cslib.BitString

open Finset Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The parity bias of a two-source output law is the corresponding signed expectation under
the independent input sources. -/
theorem bias_bind_map_eq {X Y : Type*} [Fintype X] [Fintype Y]
    (p : PMF X) (q : PMF Y) (F : X → Y → ι → Bool) (S : Finset ι) :
    bias (p.bind fun x => q.map (F x)) S =
      ∑ x, ∑ y, (p x).toReal * (q y).toReal * signVal (parityOn S (F x y)) := by
  unfold bias
  rw [PMF.sum_bind_mul]
  simp_rw [PMF.sum_map_mul, chi_eq_signVal_parityOn]
  simp only [mul_sum, mul_assoc]

/-- Fourier inversion expressed using the unnormalised parity biases of a probability mass
function. -/
theorem sum_bias_mul_chi (p : PMF (ι → Bool)) (z : ι → Bool) :
    ∑ S, bias p S * chi ℝ S z = 2 ^ Fintype.card ι * (p z).toReal := by
  have h := sum_fourierCoeff_mul_chi (fun x => (p x).toReal) z
  simp only [fourierCoeff_eq_sum, div_mul_eq_mul_div, ← sum_div] at h
  change (∑ S, bias p S * chi ℝ S z) / 2 ^ Fintype.card ι = (p z).toReal at h
  exact (div_eq_iff (by positivity)).mp h |>.trans (mul_comm _ _)

/-- The relative error at any atom is bounded by the total absolute nonempty parity bias. -/
theorem abs_mul_mass_sub_one_le_sum_abs_bias (p : PMF (ι → Bool)) (z : ι → Bool) :
    |2 ^ Fintype.card ι * (p z).toReal - 1| ≤
      ∑ S with S.Nonempty, |bias p S| := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Finset ι))
    Finset.Nonempty (fun S => bias p S * chi ℝ S z)
  have hempty : (∑ S with ¬ S.Nonempty, bias p S * chi ℝ S z) = 1 := by
    rw [sum_eq_single_of_mem ∅ (by simp)]
    · simp
    · intro S hS hne
      exact False.elim (hne (not_nonempty_iff_eq_empty.mp (mem_filter.mp hS).2))
  rw [hempty, sum_bias_mul_chi] at hsplit
  have heq : 2 ^ Fintype.card ι * (p z).toReal - 1 =
      ∑ S with S.Nonempty, bias p S * chi ℝ S z := by linarith
  rw [heq]
  calc
    _ ≤ ∑ S with S.Nonempty, |bias p S * chi ℝ S z| := abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_chi, mul_one]

/-- A normalized atom is at most the sum of all absolute parity biases. -/
theorem mul_mass_le_sum_abs_bias (p : PMF (ι → Bool)) (z : ι → Bool) :
    2 ^ Fintype.card ι * (p z).toReal ≤ ∑ S, |bias p S| := by
  rw [← sum_bias_mul_chi]
  apply sum_le_sum
  intro S _
  calc
    bias p S * chi ℝ S z ≤ |bias p S * chi ℝ S z| := le_abs_self _
    _ = |bias p S| := by rw [abs_mul, abs_chi, mul_one]

/-- Controlling only the higher-order parity biases bounds the atom mass by the number of
uncontrolled low-order parities plus the total controlled bias. -/
theorem mul_mass_le_card_add_sum_abs_bias (p : PMF (ι → Bool)) (t : ℕ)
    (z : ι → Bool) :
    2 ^ Fintype.card ι * (p z).toReal ≤
      #{S : Finset ι | S.card < t} + ∑ S with t ≤ S.card, |bias p S| := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Finset ι))
    (fun S => S.card < t) (fun S => |bias p S|)
  have hlow : (∑ S : Finset ι with S.card < t, |bias p S|) ≤
      #{S : Finset ι | S.card < t} := by
    calc
      _ ≤ ∑ S : Finset ι with S.card < t, (1 : ℝ) :=
        sum_le_sum fun S _ => abs_bias_le_one p S
      _ = _ := by simp
  simp only [not_lt] at hsplit
  have h := mul_mass_le_sum_abs_bias p z
  rw [← hsplit] at h
  linarith

omit [DecidableEq ι] in
/-- An explicit normalized atom cap gives a min-entropy lower bound. -/
private theorem le_minEntropy_of_mul_mass_le (p : PMF (ι → Bool)) {K : ℝ} (hK : 0 < K)
    (h : ∀ z, 2 ^ Fintype.card ι * (p z).toReal ≤ K) :
    Fintype.card ι - Real.logb 2 K ≤ Cslib.Probability.PMF.minEntropy p := by
  rw [Cslib.Probability.PMF.le_minEntropy_iff]
  intro z
  have heq : (2 : ℝ) ^ (-(Fintype.card ι - Real.logb 2 K)) =
      K / 2 ^ Fintype.card ι := by
    rw [neg_sub, Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hK,
      Real.rpow_natCast]
  rw [heq]
  exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h z)

/-- A parity-bias sum below one forces full support. -/
theorem mem_support_of_sum_abs_bias_lt_one (p : PMF (ι → Bool))
    (h : (∑ S with S.Nonempty, |bias p S|) < 1) (z : ι → Bool) : z ∈ p.support := by
  have hz := abs_mul_mass_sub_one_le_sum_abs_bias p z
  by_contra hn
  rw [(p.apply_eq_zero_iff z).mpr hn, ENNReal.toReal_zero, mul_zero] at hz
  norm_num at hz
  linarith

/-- Geometrically decaying parity biases imply multiplicative, pointwise closeness to uniform.
The decay parameter `q` is explicit so the result also applies to restricted coordinate sets. -/
theorem abs_mul_mass_sub_one_le_of_bias_le_geometric (p : PMF (ι → Bool))
    {ε q : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hnq : Fintype.card ι * q ≤ 1 / 2)
    (hbias : ∀ S : Finset ι, S.Nonempty → |bias p S| ≤ ε * q ^ S.card)
    (z : ι → Bool) : |2 ^ Fintype.card ι * (p z).toReal - 1| ≤ ε := by
  have hs : (∑ S : Finset ι with S.Nonempty, q ^ S.card) ≤ 1 := by
    simpa only [powerset_univ] using
      sum_nonempty_powerset_pow_card_le_one (univ : Finset ι) hq hq1
        (by simpa only [card_univ] using hnq)
  have hb : (∑ S : Finset ι with S.Nonempty, |bias p S|) ≤
      ε * ∑ S : Finset ι with S.Nonempty, q ^ S.card := by
    rw [mul_sum]
    exact sum_le_sum fun S hS => hbias S (mem_filter.mp hS).2
  exact (abs_mul_mass_sub_one_le_sum_abs_bias p z).trans
    (hb.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs hε))

/-- **Pointwise Vazirani lemma** [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, Lemma 2.5]
[ChattopadhyayFilmusKorothMeirPitassi2021]. The absolute deviation is expressed after
multiplication by `2^n`, equivalently each atom lies between `(1-ε)/2^n` and `(1+ε)/2^n`.
The zero-coordinate cube is included. -/
theorem abs_mul_mass_sub_one_le_of_bias_le (p : PMF (ι → Bool)) {ε : ℝ} (hε : 0 ≤ ε)
    (hbias : ∀ S : Finset ι, S.Nonempty →
      |bias p S| ≤ ε * (1 / (2 * Fintype.card ι) : ℝ) ^ S.card)
    (z : ι → Bool) : |2 ^ Fintype.card ι * (p z).toReal - 1| ≤ ε := by
  apply abs_mul_mass_sub_one_le_of_bias_le_geometric p hε (by positivity) _ _ hbias z
  · by_cases hn : Fintype.card ι = 0
    · simp [hn]
    · have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      apply (div_le_one (by positivity)).mpr
      linarith
  · by_cases hn : Fintype.card ι = 0
    · simp [hn]
    · have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Nat.pos_of_ne_zero hn
      apply le_of_eq
      field_simp

/-- High-order geometric bias bounds charge the low-order parities by their exact number.
This estimate also includes cubes with zero or one coordinate. -/
theorem mul_mass_le_card_add_one_of_high_order_bias_le (p : PMF (ι → Bool))
    {q : ℝ} {t : ℕ} (ht : 1 ≤ t)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hnq : Fintype.card ι * q ≤ 1 / 2)
    (hbias : ∀ S : Finset ι, t ≤ S.card → |bias p S| ≤ q ^ S.card)
    (z : ι → Bool) :
    2 ^ Fintype.card ι * (p z).toReal ≤ (#{S : Finset ι | S.card < t} + 1 : ℝ) := by
  have hgeom : (∑ S : Finset ι with S.Nonempty, q ^ S.card) ≤ 1 := by
    simpa only [powerset_univ] using
      sum_nonempty_powerset_pow_card_le_one (univ : Finset ι) hq hq1
        (by simpa only [card_univ] using hnq)
  have hhigh : (∑ S : Finset ι with t ≤ S.card, |bias p S|) ≤ 1 := by
    calc
      _ ≤ ∑ S : Finset ι with t ≤ S.card, q ^ S.card :=
        sum_le_sum fun S hS => hbias S (mem_filter.mp hS).2
      _ ≤ ∑ S : Finset ι with S.Nonempty, q ^ S.card := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro S hS
          have hcard := (mem_filter.mp hS).2
          exact mem_filter.mpr ⟨mem_univ _, card_pos.mp (by omega)⟩
        · intro S _ _
          positivity
      _ ≤ 1 := hgeom
  have hmass := mul_mass_le_card_add_sum_abs_bias p t z
  linarith

/-- High-order geometric bias bounds control the largest atom. Low-order parities are charged
only their number, without assuming any bound better than one on their biases. -/
theorem mul_mass_le_pow_of_high_order_bias_le (p : PMF (ι → Bool))
    {q : ℝ} {t : ℕ} (hn : 2 ≤ Fintype.card ι) (ht : 1 ≤ t)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hnq : Fintype.card ι * q ≤ 1 / 2)
    (hbias : ∀ S : Finset ι, t ≤ S.card → |bias p S| ≤ q ^ S.card)
    (z : ι → Bool) : 2 ^ Fintype.card ι * (p z).toReal ≤ (Fintype.card ι : ℝ) ^ t := by
  have hcount : (#{S : Finset ι | S.card < t} : ℝ) + 1 ≤ (Fintype.card ι : ℝ) ^ t := by
    exact_mod_cast card_filter_card_lt_add_one_le_pow (α := ι) hn t
  exact (mul_mass_le_card_add_one_of_high_order_bias_le p ht hq hq1 hnq hbias z).trans hcount

/-- **Min-entropy Vazirani lemma** [Chattopadhyay, Filmus, Koroth, Meir and Pitassi, Lemma 2.6]
[ChattopadhyayFilmusKorothMeirPitassi2021]. Bias bounds are required only for sets
of at least `t` coordinates. The source's one-bit slack also covers a one-coordinate cube. -/
theorem le_minEntropy_of_high_order_bias_le (p : PMF (ι → Bool)) {t : ℕ}
    (hn : 1 ≤ Fintype.card ι) (ht : 1 ≤ t)
    (hbias : ∀ S : Finset ι, t ≤ S.card →
      |bias p S| ≤ (1 / (2 * Fintype.card ι) : ℝ) ^ S.card) :
    Fintype.card ι - t * Real.logb 2 (Fintype.card ι) - 1 ≤
      Cslib.Probability.PMF.minEntropy p := by
  by_cases hn1 : Fintype.card ι = 1
  · simpa only [hn1, Nat.cast_one, Real.logb_one, mul_zero, sub_zero, sub_self]
      using Cslib.Probability.PMF.minEntropy_nonneg p
  · have hn2 : 2 ≤ Fintype.card ι := by omega
    have hn0 : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (by omega : 0 < Fintype.card ι)
    have hq1 : (1 / (2 * Fintype.card ι) : ℝ) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn2
      linarith
    have hnq : (Fintype.card ι : ℝ) * (1 / (2 * Fintype.card ι)) ≤ 1 / 2 := by
      apply le_of_eq
      field_simp
    have hmass := mul_mass_le_pow_of_high_order_bias_le p hn2 ht
      (by positivity) hq1 hnq hbias
    have h := le_minEntropy_of_mul_mass_le p (pow_pos hn0 t) hmass
    rw [Real.logb_pow] at h
    linarith

end Cslib.BitString
