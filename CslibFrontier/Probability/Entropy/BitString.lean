/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Shannon Entropy Lemmas for BitString Distributions

This module collects reusable Shannon-entropy and statistical-distance bounds on `BitString n`
distributions:

* `Cslib.Probability.PMF.entropy_ge_of_dist_uniform`: general statistical-distance-to-entropy lower
  bound $H(p) \ge (n - 1)(1 - 2 \cdot \mathsf{SD}(p, U_n))$.
* `Cslib.Probability.PMF.entropy_ge_of_dist_uniform_le`: if $\mathsf{SD}(p, U_n) \le 1 / n^2$, then
  $H(p) \ge n - 2$ ([Liu and Pass, Lemma 2.2, §2.5, p. 9 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Probability.PMF.sum_filter_mass_le_ge_of_entropy_ge`: if $H(p) \ge B \ge 3$ on
  `BitString m` ($m \ge 1$), then outcomes with point mass at most $2^{-(B - 3)}$ have total
  probability at least $1 / m$
  ([Liu and Pass, Proof of Theorem 5.2, Claim 2, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Probability.PMF.entropy_ofList_take_ge`: truncating an `m`-bit distribution to its first
  `k ≤ m` bits decreases Shannon entropy by at most `m - k` bits.
* `Cslib.Probability.PMF.entropy_append_uniform`: appending `k` independent uniform bits to an
  `m`-bit distribution increases Shannon entropy by `k` bits.

## References

* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Sections 2.5 and 5.2).
-/

public section

namespace Cslib.Probability.PMF

open Cslib
open scoped BigOperators ENNReal

/-- Auxiliary bound: for any $q \in (0, 1]$, $-q \log_2 q \le 2$. -/
private theorem mul_neg_logb_two_le_two {q : ℝ} (hq0 : 0 < q) :
    q * (-Real.logb 2 q) ≤ 2 := by
  have hlog_half := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [one_div, Real.log_inv] at hlog_half
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith
  have hlog_inv : Real.log (1 / q) ≤ 1 / q - 1 :=
    Real.log_le_sub_one_of_pos (one_div_pos.mpr hq0)
  have hq_log : q * (-Real.log q) ≤ 1 - q := by
    have h1 : -Real.log q = Real.log (1 / q) := by
      rw [one_div, Real.log_inv]
    rw [h1]
    have hmul := mul_le_mul_of_nonneg_left hlog_inv hq0.le
    rwa [mul_sub, mul_one_div_cancel hq0.ne', mul_one] at hmul
  rw [Real.logb, ← neg_div, ← mul_div_assoc]
  have hnum : q * -Real.log q ≤ 1 := by linarith
  calc
    (q * -Real.log q) / Real.log 2 ≤ 1 / Real.log 2 :=
      div_le_div_of_nonneg_right hnum (by linarith)
    _ ≤ 1 / (1 / 2) := one_div_le_one_div_of_le (by norm_num) hlog2
    _ = 2 := by norm_num

/-- **General statistical-distance-to-entropy lower bound.**
For any distribution $p$ on `BitString n`, the mass of outcomes with probability strictly above
$2^{-(n - 1)}$ is at most $2 \cdot \mathsf{SD}(p, U_n)$, so
$H(p) \ge (n - 1)(1 - 2 \cdot \mathsf{SD}(p, U_n))$. -/
theorem entropy_ge_of_dist_uniform {n : ℕ} (hn : 1 ≤ n) (p : PMF (BitString n)) :
    ((n : ℝ) - 1) * (1 - 2 * dist p (PMF.uniformOfFintype (BitString n))) ≤ entropy p := by
  classical
  let U := PMF.uniformOfFintype (BitString n)
  have hU_apply (x : BitString n) : (U x).toReal = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    simp [U, uniformOfFintype_apply]
  let S₁ : Finset (BitString n) :=
    Finset.univ.filter fun x => (p x).toReal ≤ (2 : ℝ) ^ (-((n : ℝ) - 1))
  let S₂ : Finset (BitString n) :=
    Finset.univ.filter fun x => (2 : ℝ) ^ (-((n : ℝ) - 1)) < (p x).toReal
  have htwo_pow : (2 : ℝ) ^ (-((n : ℝ) - 1)) = 2 * (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [show -((n : ℝ) - 1) = 1 + -(n : ℝ) by ring, Real.rpow_add (by norm_num), Real.rpow_one]
  have hS₂_sub : S₂ ⊆ Finset.univ.filter fun x => (U x).toReal < (p x).toReal := by
    intro x hx
    simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    rw [hU_apply]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    linarith [htwo_pow]
  have hS₂_mass : ∑ x ∈ S₂, (p x).toReal ≤ 2 * dist p U := by
    rw [dist_eq_sum_filter_lt p U, Finset.mul_sum]
    calc
      ∑ x ∈ S₂, (p x).toReal ≤ ∑ x ∈ S₂, 2 * ((p x).toReal - (U x).toReal) := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hU_apply]
        linarith [htwo_pow]
      _ ≤ ∑ x ∈ Finset.univ.filter (fun x => (U x).toReal < (p x).toReal),
            2 * ((p x).toReal - (U x).toReal) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hS₂_sub fun x hx _ => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        linarith
  have hpart : (∑ x ∈ S₁, (p x).toReal) + ∑ x ∈ S₂, (p x).toReal = 1 := by
    have hcompl : S₂ = S₁ᶜ := by
      ext x
      simp [S₁, S₂, not_le]
    rw [hcompl, Finset.sum_add_sum_compl, sum_toReal]
  have hS₁_mass : 1 - 2 * dist p U ≤ ∑ x ∈ S₁, (p x).toReal := by linarith
  have hsurp (x : BitString n) (hx : x ∈ S₁) :
      (p x).toReal * ((n : ℝ) - 1) ≤ (p x).toReal * surprisal p x := by
    by_cases hp0 : (p x).toReal = 0
    · simp [hp0]
    · have hpos : 0 < (p x).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hp0)
      apply mul_le_mul_of_nonneg_left _ hpos.le
      simp only [S₁, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [surprisal, le_neg]
      exact (Real.logb_le_iff_le_rpow (by norm_num) hpos).mpr hx
  have hn_real : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  rw [entropy_eq_sum_surprisal]
  calc
    ((n : ℝ) - 1) * (1 - 2 * dist p U)
      ≤ ((n : ℝ) - 1) * ∑ x ∈ S₁, (p x).toReal :=
        mul_le_mul_of_nonneg_left hS₁_mass (by linarith)
    _ = ∑ x ∈ S₁, (p x).toReal * ((n : ℝ) - 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    _ ≤ ∑ x ∈ S₁, (p x).toReal * surprisal p x :=
        Finset.sum_le_sum fun x hx => hsurp x hx
    _ ≤ ∑ x, (p x).toReal * surprisal p x :=
        Finset.sum_le_univ_sum_of_nonneg fun x =>
          mul_nonneg ENNReal.toReal_nonneg (surprisal_nonneg p x)

/-- **[Liu and Pass, Lemma 2.2, §2.5, p. 9 of arXiv:2009.11514v1][LiuPass2020]: Statistical
distance to uniform bounds Shannon entropy from below.**
If $\mathsf{SD}(p, U_n) \le 1 / n^2$, then $H(p) \ge n - 2$. -/
theorem entropy_ge_of_dist_uniform_le {n : ℕ} (p : PMF (BitString n))
    (hdist : dist p (PMF.uniformOfFintype (BitString n)) ≤ 1 / (n : ℝ) ^ 2) :
    (n : ℝ) - 2 ≤ entropy p := by
  rcases le_or_gt n 1 with hn1 | hn1
  · have hent : 0 ≤ entropy p := entropy_nonneg p
    have hn_le : (n : ℝ) ≤ 1 := by exact_mod_cast hn1
    linarith
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h1 := entropy_ge_of_dist_uniform hn1.le p
  have hn_ge : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have h2 : ((n : ℝ) - 1) * (1 - 2 * (1 / (n : ℝ) ^ 2)) ≤
      ((n : ℝ) - 1) * (1 - 2 * dist p (PMF.uniformOfFintype (BitString n))) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    linarith
  have h3 : (n : ℝ) - 2 ≤ ((n : ℝ) - 1) * (1 - 2 * (1 / (n : ℝ) ^ 2)) := by
    have hsq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hn_pos
    have hquad : 2 * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hdiv : 2 * ((n : ℝ) - 1) * (1 / (n : ℝ) ^ 2) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one hsq).mpr hquad
    linarith
  linarith

/-- **[Liu and Pass, Proof of Theorem 5.2, Claim 2, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]:
High Shannon entropy implies non-negligible mass on low-probability outcomes.**
For any distribution $p$ on `BitString m` with $m \ge 1$ and $B \ge 3$ such that $H(p) \ge B$,
the set of outcomes $y$ with point mass $p(y) \le 2^{-(B - 3)}$ has total probability at least
$1 / m$. -/
theorem sum_filter_mass_le_ge_of_entropy_ge {m : ℕ} (hm : 1 ≤ m) (p : PMF (BitString m))
    {B : ℝ} (hB : 3 ≤ B) (hent : B ≤ entropy p) :
    1 / (m : ℝ) ≤
      ∑ y ∈ Finset.univ.filter (fun y => (p y).toReal ≤ (2 : ℝ) ^ (-(B - 3))), (p y).toReal := by
  classical
  let S : Finset (BitString m) :=
    Finset.univ.filter fun y => (p y).toReal ≤ (2 : ℝ) ^ (-(B - 3))
  let q : ℝ := ∑ y ∈ S, (p y).toReal
  change 1 / (m : ℝ) ≤ q
  have hm_pos : (0 : ℝ) < m := by exact_mod_cast hm
  -- Bound the contribution outside S: every y ∉ S has surprisal p y ≤ B - 3
  have hout : ∑ y ∈ Sᶜ, (p y).toReal * surprisal p y ≤ B - 3 := by
    have hterm (y : BitString m) (hy : y ∈ Sᶜ) :
        (p y).toReal * surprisal p y ≤ (p y).toReal * (B - 3) := by
      simp only [S, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hy
      exact mul_le_mul_of_nonneg_left (surprisal_le_of_mass_ge p y hy.le) ENNReal.toReal_nonneg
    calc
      ∑ y ∈ Sᶜ, (p y).toReal * surprisal p y
        ≤ ∑ y ∈ Sᶜ, (p y).toReal * (B - 3) := Finset.sum_le_sum hterm
      _ = (∑ y ∈ Sᶜ, (p y).toReal) * (B - 3) := (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (B - 3) := by
        refine mul_le_mul_of_nonneg_right ?_ (by linarith)
        calc
          ∑ y ∈ Sᶜ, (p y).toReal ≤ ∑ y : BitString m, (p y).toReal :=
            Finset.sum_le_univ_sum_of_nonneg fun _ => ENNReal.toReal_nonneg
          _ = 1 := sum_toReal p
      _ = B - 3 := one_mul _
  -- Bound the contribution inside S by q * m + 2
  have hin : ∑ y ∈ S, (p y).toReal * surprisal p y ≤ q * (m : ℝ) + 2 := by
    by_cases hq0 : q = 0
    · have hall0 : ∀ y ∈ S, (p y).toReal = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => ENNReal.toReal_nonneg).mp hq0
      have hsum0 : ∑ y ∈ S, (p y).toReal * surprisal p y = 0 :=
        Finset.sum_eq_zero fun y hy => by simp [hall0 y hy]
      rw [hsum0, hq0]
      linarith
    · have hq_nonneg : 0 ≤ q := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
      have hq_pos : 0 < q := lt_of_le_of_ne hq_nonneg (Ne.symm hq0)
      have hex : ∃ y ∈ (S : Set (BitString m)), y ∈ p.support := by
        by_contra! hno
        have hzero : q = 0 := Finset.sum_eq_zero fun y hy => by
          have := hno y hy
          rw [PMF.mem_support_iff, not_not] at this
          simp [this]
        exact hq0 hzero
      let pS := p.filter (S : Set (BitString m)) hex
      have hmeas : (p.toOuterMeasure (S : Set (BitString m))).toReal = q := by
        rw [toOuterMeasure_apply_toReal]
        simp [q]
      have hent_pS : entropy pS ≤ m := by
        have hcard := entropy_le_log_card pS
        rwa [show Fintype.card (BitString m) = 2 ^ m by simp, Nat.cast_pow, Nat.cast_ofNat,
          Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hcard
      have hident : ∑ y ∈ S, (p y).toReal * surprisal p y =
          q * entropy pS + q * (-Real.logb 2 q) := by
        rw [entropy_eq_sum_surprisal pS, Finset.mul_sum]
        have hcompl0 : ∑ y ∈ Sᶜ, q * ((pS y).toReal * surprisal pS y) = 0 := by
          refine Finset.sum_eq_zero fun y hy => ?_
          simp only [Finset.mem_compl] at hy
          have hpSy : (pS y).toReal = 0 := by
            simp [pS, hy]
          simp [hpSy]
        have hq_sum : q * (-Real.logb 2 q) = ∑ y ∈ S, (p y).toReal * (-Real.logb 2 q) :=
          Finset.sum_mul S (fun y => (p y).toReal) (-Real.logb 2 q)
        rw [← Finset.sum_add_sum_compl S, hcompl0, add_zero, hq_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y hy => ?_
        by_cases hpy0 : (p y).toReal = 0
        · have hpSy : (pS y).toReal = 0 := by
            simp [pS, hy, hpy0]
          simp [hpy0, hpSy]
        · have hpy_pos : 0 < (p y).toReal :=
            lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hpy0)
          have hpSy : (pS y).toReal = (p y).toReal / q := by
            dsimp [pS]
            rw [filter_apply_toReal, ite_eq_left (Finset.mem_coe.mpr hy), hmeas]
          have hq_mul : q * (pS y).toReal = (p y).toReal := by
            rw [hpSy, mul_div_cancel₀ _ hq_pos.ne']
          rw [← mul_assoc, hq_mul]
          simp only [surprisal, hpSy, Real.logb_div hpy_pos.ne' hq_pos.ne']
          ring
      have hq_log := mul_neg_logb_two_le_two hq_pos
      have hq_ent : q * entropy pS ≤ q * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hent_pS hq_pos.le
      linarith
  have htotal : entropy p =
      (∑ y ∈ S, (p y).toReal * surprisal p y) + ∑ y ∈ Sᶜ, (p y).toReal * surprisal p y := by
    rw [entropy_eq_sum_surprisal, ← Finset.sum_add_sum_compl S]
  have h1 : 1 ≤ q * (m : ℝ) := by linarith
  exact (div_le_iff₀ hm_pos).mpr (by linarith)

/-- Truncating an `m`-bit distribution to its first `k ≤ m` bits decreases Shannon entropy by at
most `m - k` bits. -/
theorem entropy_ofList_take_ge {m k : ℕ} (hk : k ≤ m) (p : PMF (BitString m)) :
    entropy p - ((m - k : ℕ) : ℝ) ≤
      entropy (p.map fun x => BitString.ofList k ((List.ofFn x).take k)) := by
  let split (x : BitString m) : BitString k × BitString (m - k) :=
    (BitString.ofList k ((List.ofFn x).take k),
      BitString.ofList (m - k) ((List.ofFn x).drop k))
  have hinj : Function.Injective split := by
    intro x y hxy
    have h1 := congrArg (List.ofFn ∘ Prod.fst) hxy
    have h2 := congrArg (List.ofFn ∘ Prod.snd) hxy
    dsimp only [Function.comp_apply, split] at h1 h2
    rw [BitString.ofFn_ofList (by simp [hk]), BitString.ofFn_ofList (by simp [hk])] at h1
    rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList (by simp)] at h2
    apply List.ofFn_inj.mp
    rw [← List.take_append_drop k (List.ofFn x), ← List.take_append_drop k (List.ofFn y), h1, h2]
  have hjoint : entropy (p.map split) = entropy p := entropy_map_of_injective p hinj
  have hfst : (p.map split).map Prod.fst =
      p.map fun x => BitString.ofList k ((List.ofFn x).take k) := by
    rw [PMF.map_comp]
    rfl
  have hcond := conditionalEntropy_le_log_card (p.map split)
  rw [conditionalEntropy, hjoint, hfst,
    show Fintype.card (BitString (m - k)) = 2 ^ (m - k) by simp,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num),
    mul_one] at hcond
  linarith

/-- Appending `k` independent uniform bits to an `m`-bit distribution increases Shannon entropy
by exactly `k` bits. -/
theorem entropy_append_uniform {m k : ℕ} (p : PMF (BitString m)) :
    entropy (p.bind fun x => (PMF.uniformOfFintype (BitString k)).map fun z =>
      BitString.ofList (m + k) (List.ofFn x ++ List.ofFn z)) =
      entropy p + (k : ℝ) := by
  let join (xz : BitString m × BitString k) : BitString (m + k) :=
    BitString.ofList (m + k) (List.ofFn xz.1 ++ List.ofFn xz.2)
  have hinj : Function.Injective join := by
    rintro ⟨x₁, z₁⟩ ⟨x₂, z₂⟩ hxy
    have h := congrArg List.ofFn hxy
    dsimp only [join] at h
    rw [BitString.ofFn_ofList (by simp), BitString.ofFn_ofList (by simp)] at h
    obtain ⟨hx, hz⟩ := List.append_inj h (by simp)
    exact Prod.ext (List.ofFn_inj.mp hx) (List.ofFn_inj.mp hz)
  have hmap : (p.bind fun x => (PMF.uniformOfFintype (BitString k)).map (x, ·)).map join =
      p.bind fun x => (PMF.uniformOfFintype (BitString k)).map fun z =>
        BitString.ofList (m + k) (List.ofFn x ++ List.ofFn z) := by
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, join]
  rw [← hmap, entropy_map_of_injective _ hinj, entropy_prod, entropy_uniform,
    show Fintype.card (BitString k) = 2 ^ k by simp,
    Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end Cslib.Probability.PMF
