/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Kolmogorov.TimeBounded
public import Complexity.Probability.Entropy.BitString
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Average-case hardness building blocks for time-bounded Kolmogorov complexity (`K^t`)

This module formalizes the $K^t$-specific counting, generator upper-bound, and threshold
distinguisher lemmas from [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov
Complexity*][LiuPass2020]. Generic mild average-case hardness definitions and bridges live in
`Complexity.Computability.Complexity.AverageCase`, and reusable BitString Shannon-entropy bounds
live in `Complexity.Probability.Entropy.BitString`. All section, theorem, lemma, and page locators
follow the full version `arXiv:2009.11514v1` (and ECCC TR20-052).

## Main results

* `Cslib.Kolmogorov.mildlyHardOnAverageENat_timeBounded_iff`,
  `Cslib.Kolmogorov.mildlyHardOnAverageIOENat_timeBounded_iff`:
  equivalence between `ℕ∞`-valued `timeBounded t` hardness and `ℕ`-valued `timeBoundedNat t`
  hardness whenever `∀ n, n + 1 ≤ t n`.
* `Cslib.Kolmogorov.exists_timeBounded_generator_le`: for any length-nondecreasing
  polynomial-time generator $G : \{0, 1\}^* \to \{0, 1\}^*$, there exist a polynomial $p_G$ and a
  constant $c$ such that for all $t \ge p_G$ and all $z$, $K^t(G(z)) \le |z| + c$
  ([Liu and Pass, Proof of Theorem 5.2, Equation (3), §5.2, pp. 11–12 of
  arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Kolmogorov.sum_uniform_timeBoundedNat_lt_le`: counting bound on the fraction of $n$-bit
  strings with $K^t(x) < n - k$
  ([Liu and Pass, Proof of Theorem 5.2, Equation (2), §5.2, p. 11 of
  arXiv:2009.11514v1][LiuPass2020]).
* `Cslib.Kolmogorov.uniformList_threshold_accept_ge`,
  `Cslib.Kolmogorov.generator_threshold_accept_le`:
  acceptance bounds for the Theorem 5.2 threshold distinguisher on $U_m$ and on an
  entropy-preserving generator distribution $p_G$
  ([Liu and Pass, Proof of Theorem 5.2, Claims 1–2, §5.2, p. 12 of
  arXiv:2009.11514v1][LiuPass2020]).

## References

* [Y. Liu, R. Pass, *On One-way Functions and Kolmogorov Complexity*][LiuPass2020],
  full version `arXiv:2009.11514v1` (Section 5.2).
-/

@[expose] public section

namespace Cslib.Kolmogorov

open Filter Cslib.Complexity Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped BigOperators ENNReal

/-! ### Equivalence between `timeBounded` (`ℕ∞`) and `timeBoundedNat` (`ℕ`) hardness -/

/-- Whenever `∀ n, n + 1 ≤ t n`, `MildlyHardOnAverageENat (timeBounded t)` is equivalent to
`MildlyHardOnAverage (timeBoundedNat t)`. -/
theorem mildlyHardOnAverageENat_timeBounded_iff {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) :
    MildlyHardOnAverageENat (timeBounded t) ↔ MildlyHardOnAverage (timeBoundedNat t) := by
  have heq (v : ℕ) (x : List Bool) :
      ((v : ℕ∞) = timeBounded t x) ↔ (v = timeBoundedNat t x) := by
    rw [← natCast_timeBoundedNat (timeBounded_ne_top (ht x.length)), ENat.natCast_inj]
  simp only [MildlyHardOnAverageENat, MildlyHardOnAverage, heq]

/-- Whenever `∀ n, n + 1 ≤ t n`, `MildlyHardOnAverageIOENat (timeBounded t)` is equivalent to
`MildlyHardOnAverageIO (timeBoundedNat t)`. -/
theorem mildlyHardOnAverageIOENat_timeBounded_iff {t : ℕ → ℕ} (ht : ∀ n, n + 1 ≤ t n) :
    MildlyHardOnAverageIOENat (timeBounded t) ↔ MildlyHardOnAverageIO (timeBoundedNat t) := by
  have heq (H : List Bool → ℕ) (x : List Bool) :
      ((H x : ℕ∞) = timeBounded t x) ↔ (H x = timeBoundedNat t x) := by
    rw [← natCast_timeBoundedNat (timeBounded_ne_top (ht x.length)), ENat.natCast_inj]
  simp only [MildlyHardOnAverageIOENat, MildlyHardOnAverageIO, heq]

/-! ### Generator $K^t$ upper bound
([Liu and Pass, Proof of Theorem 5.2, Eq. (3), §5.2, pp. 11–12 of arXiv:2009.11514v1][LiuPass2020])
-/

/-- **[Liu and Pass, Proof of Theorem 5.2, Equation (3), §5.2, pp. 11–12 of
arXiv:2009.11514v1][LiuPass2020]:
Outputs of a polynomial-time generator have $K^t(G(z)) \le |z| + O(1)$.**
For any polynomial-time generator $G : \{0, 1\}^* \to \{0, 1\}^*$ that does not shrink its input
($|z| \le |G(z)|$), there exist a polynomial $p_G$ (with $n + 1 \le p_G(n)$) and a constant $c$
such that for every time bound $t$ dominating $p_G$ and every seed $z \in \{0, 1\}^*$,
$K^t(G(z)) \le |z| + c$. -/
theorem exists_timeBounded_generator_le {G : List Bool → List Bool}
    (hG : ComputableInPolyTime G encBits encBits)
    (hstretch : ∀ z : List Bool, z.length ≤ (G z).length) :
    ∃ (pG : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ pG.eval n) ∧
      Monotone pG.eval ∧
      ∀ {t : ℕ → ℕ}, (∀ m, pG.eval m ≤ t m) → ∀ z : List Bool,
        timeBounded t (G z) ≤ (z.length + c : ℕ) := by
  obtain ⟨tG, sG, htG, _, k, State, hfin, tm, htm⟩ := hG
  obtain ⟨c_tm, d_tm, hle⟩ := polynomiallyBounded_iff_le.mp htG
  obtain ⟨c_sim, hsim⟩ :=
    DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM tm
  let pG : Polynomial ℕ := Polynomial.C (c_tm + 1) * (Polynomial.X + 1) ^ (d_tm + 1)
  have hpG_eval (n : ℕ) : pG.eval n = (c_tm + 1) * (n + 1) ^ (d_tm + 1) := by
    simp [pG]
  have hpG_ge (n : ℕ) : n + 1 ≤ pG.eval n := by
    rw [hpG_eval, pow_succ']
    have hpow : 1 ≤ (n + 1) ^ d_tm := Nat.one_le_pow _ _ (by omega)
    calc
      n + 1 = 1 * ((n + 1) * 1) := by ring
      _ ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hpow)
  have hpG_mono : Monotone pG.eval := by
    intro a b hab
    dsimp only
    rw [hpG_eval, hpG_eval]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have htG_le (n : ℕ) : tG n ≤ pG.eval n := by
    rw [hpG_eval, pow_succ']
    have h1 := hle n
    have hpow : 1 ≤ (n + 1) ^ d_tm := Nat.one_le_pow _ _ (by omega)
    have h2 : c_tm * (n + 1) ^ d_tm ≤ (c_tm + 1) * (n + 1) ^ d_tm :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (c_tm + 1) * (n + 1) ^ d_tm ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) := by
      refine Nat.mul_le_mul_left _ ?_
      exact Nat.le_mul_of_pos_left _ (by omega)
    omega
  refine ⟨pG, c_sim, hpG_ge, hpG_mono, fun {t} ht z => ?_⟩
  have hcomp := htm z
  have hstep : tG z.length ≤ t (G z).length :=
    (htG_le z.length).trans ((hpG_mono (hstretch z)).trans (ht (G z).length))
  have htm_le : (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG z.length) (G z) ≤
      (z.length : ℕ∞) :=
    DescriptionMethod.etimeBoundedComplexity_ofMultiTapeTM_le hcomp.2.1 hcomp.1
  calc
    timeBounded t (G z) = timeBoundedAt (t (G z).length) (G z) := rfl
    _ ≤ timeBoundedAt (tG z.length) (G z) := timeBoundedAt_anti hstep
    _ ≤ (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG z.length) (G z) + c_sim :=
      hsim (tG z.length) (G z)
    _ ≤ (z.length : ℕ∞) + c_sim := add_le_add_left htm_le _
    _ = (z.length + c_sim : ℕ) := by rw [Nat.cast_add]

/-- Natural-number version of `exists_timeBounded_generator_le` for `timeBoundedNat`. -/
theorem timeBoundedNat_generator_le {G : List Bool → List Bool} {pG : Polynomial ℕ} {c : ℕ}
    (hpG : ∀ n, n + 1 ≤ pG.eval n)
    (hbound : ∀ {t : ℕ → ℕ}, (∀ m, pG.eval m ≤ t m) → ∀ z : List Bool,
      timeBounded t (G z) ≤ (z.length + c : ℕ))
    {t : ℕ → ℕ} (ht : ∀ m, pG.eval m ≤ t m) (z : List Bool) :
    timeBoundedNat t (G z) ≤ z.length + c := by
  have hne : timeBounded t (G z) ≠ ⊤ :=
    timeBounded_ne_top ((hpG (G z).length).trans (ht (G z).length))
  exact (timeBoundedNat_le_iff hne).mpr (hbound ht z)

/-- General polynomial-time $K^t$ upper bound for any encoded input type $\alpha$: if
`G : α → List Bool` is computable in polynomial time with respect to `enc : α ↪ List Bool` and
`encBits`, there exist a monotone polynomial `pG` (with `n + 1 ≤ pG.eval n`) and a constant `c`
such that whenever `pG.eval (enc a).length ≤ t (G a).length`, we have
`timeBounded t (G a) ≤ ((enc a).length + c : ℕ)`. -/
theorem exists_timeBounded_of_computableInPolyTime {α : Type*} {enc : α ↪ List Bool}
    {G : α → List Bool} (hG : ComputableInPolyTime G enc encBits) :
    ∃ (pG : Polynomial ℕ) (c : ℕ),
      (∀ n, n + 1 ≤ pG.eval n) ∧
      Monotone pG.eval ∧
      ∀ {t : ℕ → ℕ} (a : α), pG.eval (enc a).length ≤ t (G a).length →
        timeBounded t (G a) ≤ ((enc a).length + c : ℕ) := by
  obtain ⟨tG, sG, htG, _, k, State, hfin, tm, htm⟩ := hG
  obtain ⟨c_tm, d_tm, hle⟩ := polynomiallyBounded_iff_le.mp htG
  obtain ⟨c_sim, hsim⟩ :=
    DescriptionMethod.exists_etimeBoundedComplexity_universalTM_le_ofMultiTapeTM tm
  let pG : Polynomial ℕ := Polynomial.C (c_tm + 1) * (Polynomial.X + 1) ^ (d_tm + 1)
  have hpG_eval (n : ℕ) : pG.eval n = (c_tm + 1) * (n + 1) ^ (d_tm + 1) := by
    simp [pG]
  have hpG_ge (n : ℕ) : n + 1 ≤ pG.eval n := by
    rw [hpG_eval, pow_succ']
    have hpow : 1 ≤ (n + 1) ^ d_tm := Nat.one_le_pow _ _ (by omega)
    calc
      n + 1 = 1 * ((n + 1) * 1) := by ring
      _ ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hpow)
  have hpG_mono : Monotone pG.eval := by
    intro a b hab
    dsimp only
    rw [hpG_eval, hpG_eval]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have htG_le (n : ℕ) : tG n ≤ pG.eval n := by
    rw [hpG_eval, pow_succ']
    have h1 := hle n
    have h2 : c_tm * (n + 1) ^ d_tm ≤ (c_tm + 1) * (n + 1) ^ d_tm :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (c_tm + 1) * (n + 1) ^ d_tm ≤ (c_tm + 1) * ((n + 1) * (n + 1) ^ d_tm) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
    omega
  refine ⟨pG, c_sim, hpG_ge, hpG_mono, fun {t} a hstep' => ?_⟩
  have hcomp := htm a
  have hstep : tG (enc a).length ≤ t (G a).length := (htG_le _).trans hstep'
  have htm_le :
      (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG (enc a).length) (G a) ≤
        ((enc a).length : ℕ∞) :=
    DescriptionMethod.etimeBoundedComplexity_ofMultiTapeTM_le hcomp.2.1 hcomp.1
  calc
    timeBounded t (G a) = timeBoundedAt (t (G a).length) (G a) := rfl
    _ ≤ timeBoundedAt (tG (enc a).length) (G a) := timeBoundedAt_anti hstep
    _ ≤ (DescriptionMethod.ofMultiTapeTM tm).etimeBoundedComplexity (tG (enc a).length) (G a) +
        c_sim := hsim (tG (enc a).length) (G a)
    _ ≤ ((enc a).length : ℕ∞) + c_sim := add_le_add_left htm_le _
    _ = ((enc a).length + c_sim : ℕ) := by rw [Nat.cast_add]

/-- Fewer than `2 ^ r` bitstrings of length `n` have `timeBoundedNat t (List.ofFn x) < r`
whenever `n + 1 ≤ t n`. -/
theorem card_filter_timeBoundedNat_lt {t : ℕ → ℕ} {n : ℕ} (ht : n + 1 ≤ t n) (r : ℕ) :
    ((Finset.univ : Finset (BitString n)).filter fun x =>
      timeBoundedNat t (List.ofFn x) < r).card < 2 ^ r := by
  let S := (Finset.univ : Finset (BitString n)).filter fun x =>
    timeBoundedNat t (List.ofFn x) < r
  have hsub : (List.ofFn '' (S : Set (BitString n))) ⊆
      {y : List Bool | y.length = n ∧ timeBounded t y < (r : ℕ)} := by
    rintro y ⟨x, hx, rfl⟩
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    have hne : timeBounded t (List.ofFn x) ≠ ⊤ :=
      timeBounded_ne_top (t := t) (x := List.ofFn x) (by simpa [List.length_ofFn] using ht)
    refine ⟨List.length_ofFn, ?_⟩
    rw [← natCast_timeBoundedNat hne]
    exact_mod_cast hx
  have hinj : Function.Injective (List.ofFn (α := Bool) (n := n)) := fun _ _ h => List.ofFn_inj.mp h
  have henc := (Set.encard_le_encard hsub).trans_lt (encard_setOf_timeBounded_lt t n r)
  rw [hinj.encard_image, Set.encard_coe_eq_coe_finsetCard] at henc
  exact_mod_cast henc

/-- **[Liu and Pass, Proof of Theorem 5.2, Equation (2), §5.2, p. 11 of
arXiv:2009.11514v1][LiuPass2020]:
Probability that a random $n$-bit string has $K^t(x) < n - k$ is at most $2^{-k}$.** -/
theorem sum_uniform_timeBoundedNat_lt_le {t : ℕ → ℕ} {n : ℕ} (ht : n + 1 ≤ t n) (k : ℕ) :
    (∑ x : BitString n, (PMF.uniformOfFintype (BitString n) x).toReal *
      if timeBoundedNat t (List.ofFn x) < n - k then (1 : ℝ) else 0) ≤
      (2 : ℝ) ^ (-(k : ℝ)) := by
  by_cases hkn : k ≤ n
  · have hcard := (card_filter_timeBoundedNat_lt ht (n - k)).le
    have hsum : (∑ x : BitString n, (PMF.uniformOfFintype (BitString n) x).toReal *
        if timeBoundedNat t (List.ofFn x) < n - k then (1 : ℝ) else 0) =
        (((Finset.univ : Finset (BitString n)).filter fun x =>
          timeBoundedNat t (List.ofFn x) < n - k).card : ℝ) / (2 : ℝ) ^ n := by
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        ← Finset.mul_sum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        div_eq_inv_mul]
    rw [hsum]
    calc
      (((Finset.univ : Finset (BitString n)).filter fun x =>
          timeBoundedNat t (List.ofFn x) < n - k).card : ℝ) / (2 : ℝ) ^ n
        ≤ ((2 ^ (n - k) : ℕ) : ℝ) / (2 : ℝ) ^ n := by
          gcongr
      _ = (2 : ℝ) ^ (-(k : ℝ)) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast, ← Real.rpow_natCast,
            ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Nat.cast_sub hkn]
          ring_nf
  · have hnk : n - k = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp only [hnk, Nat.not_lt_zero, ↓reduceIte, mul_zero, Finset.sum_const_zero]
    positivity

private theorem pmf_bool_true_add_false_toReal (μ : PMF Bool) :
    (μ true).toReal + (μ false).toReal = 1 := by
  have h : μ true + μ false = 1 := by simpa [tsum_bool] using μ.tsum_coe
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), ENNReal.toReal_one] at h'

private theorem pmf_bool_true_toReal_le_one (μ : PMF Bool) :
    (μ true).toReal ≤ 1 := by
  have h := pmf_bool_true_add_false_toReal μ
  have h0 : 0 ≤ (μ false).toReal := ENNReal.toReal_nonneg
  linarith

private theorem pmf_map_true_le_one_sub_of_imp_false {α : Type*} (q : PMF α) (P Q : α → Bool)
    (hdisj : ∀ v, P v = true → Q v = false) :
    ((q.map P) true).toReal ≤ 1 - ((q.map Q) true).toReal := by
  have hle : (q.map P) true ≤ (q.map Q) false := by
    rw [PMF.map_apply, PMF.map_apply]
    refine tsum_le_tsum fun v => ?_
    by_cases hp : P v = true
    · have hq : Q v = false := hdisj v hp
      simp [hp, hq]
    · simp [hp]
  have hle' : ((q.map P) true).toReal ≤ ((q.map Q) false).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _) hle
  have hsum := pmf_bool_true_add_false_toReal (q.map Q)
  linarith

private theorem pmf_map_true_le_of_imp_true {α : Type*} (q : PMF α) (P Q : α → Bool)
    (himp : ∀ v, P v = true → Q v = true) :
    ((q.map P) true).toReal ≤ ((q.map Q) true).toReal := by
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.map_apply, PMF.map_apply]
  refine tsum_le_tsum fun v => ?_
  by_cases hp : P v = true
  · have hq : Q v = true := himp v hp
    simp [hp, hq]
  · simp [hp]

/-- **[Liu and Pass, Proof of Theorem 5.2, Claim 1, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]:
Acceptance probability of the threshold distinguisher on the uniform distribution $U_m$.** -/
theorem uniformList_threshold_accept_ge {t : ℕ → ℕ} {m : ℕ} (ht : m + 1 ≤ t m)
    (k g_err : ℕ) (q : List Bool → PMF ℕ) :
    (((BitString.uniformList m).bind fun y =>
        (q y).map fun v =>
          decide (timeBoundedNat t y - g_err ≤ v ∧ v ≤ timeBoundedNat t y)) true).toReal -
      (2 : ℝ) ^ (-(k : ℝ)) ≤
    (((BitString.uniformList m).bind fun y =>
        (q y).map fun v => decide (m - k - g_err ≤ v)) true).toReal := by
  let approx (y : List Bool) : PMF Bool :=
    (q y).map fun v => decide (timeBoundedNat t y - g_err ≤ v ∧ v ≤ timeBoundedNat t y)
  let accept (y : List Bool) : PMF Bool :=
    (q y).map fun v => decide (m - k - g_err ≤ v)
  have hpoint (x : BitString m) :
      (approx (List.ofFn x) true).toReal ≤
        (accept (List.ofFn x) true).toReal +
          if timeBoundedNat t (List.ofFn x) < m - k then (1 : ℝ) else 0 := by
    by_cases hlt : timeBoundedNat t (List.ofFn x) < m - k
    · simp only [hlt, ↓reduceIte]
      have h1 := pmf_bool_true_toReal_le_one (approx (List.ofFn x))
      have h2 : 0 ≤ (accept (List.ofFn x) true).toReal := ENNReal.toReal_nonneg
      linarith
    · simp only [hlt, ↓reduceIte, add_zero]
      refine pmf_map_true_le_of_imp_true (q (List.ofFn x)) _ _ fun v hv => ?_
      simp only [decide_eq_true_eq] at hv ⊢
      omega
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun x _ =>
    mul_le_mul_of_nonneg_left (hpoint x)
      (ENNReal.toReal_nonneg (a := PMF.uniformOfFintype (BitString m) x))
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have hbind_approx :
      (((BitString.uniformList m).bind approx) true).toReal =
        ∑ x : BitString m, (PMF.uniformOfFintype (BitString m) x).toReal *
          (approx (List.ofFn x) true).toReal := by
    simp only [BitString.uniformList, PMF.bind_map, bind_apply_toReal, Function.comp_apply]
  have hbind_accept :
      (((BitString.uniformList m).bind accept) true).toReal =
        ∑ x : BitString m, (PMF.uniformOfFintype (BitString m) x).toReal *
          (accept (List.ofFn x) true).toReal := by
    simp only [BitString.uniformList, PMF.bind_map, bind_apply_toReal, Function.comp_apply]
  have hcount := sum_uniform_timeBoundedNat_lt_le ht k
  linarith

/-- **[Liu and Pass, Proof of Theorem 5.2, Claim 2, §5.2, p. 12 of arXiv:2009.11514v1][LiuPass2020]:
Acceptance probability of the threshold distinguisher on an entropy-preserving generator
distribution $p_G$.** -/
theorem generator_threshold_accept_le {t : ℕ → ℕ} {m : ℕ} (hm : 1 ≤ m)
    {pG : PMF (BitString m)} {B : ℝ} (hB3 : 3 ≤ B) (hent : B ≤ entropy pG)
    (k g_err : ℕ)
    (hlow : ∀ x ∈ pG.support, timeBoundedNat t (List.ofFn x) < m - k - g_err)
    (q : List Bool → PMF ℕ) :
    ((((pG.map List.ofFn).bind fun y =>
        (q y).map fun v => decide (m - k - g_err ≤ v)) true).toReal) ≤
      1 - 1 / (m : ℝ) + (2 : ℝ) ^ ((m : ℝ) - (B - 3)) *
        (1 - (((BitString.uniformList m).bind fun y =>
          (q y).map fun v =>
            decide (timeBoundedNat t y - g_err ≤ v ∧ v ≤ timeBoundedNat t y)) true).toReal) := by
  let approx (y : List Bool) : PMF Bool :=
    (q y).map fun v => decide (timeBoundedNat t y - g_err ≤ v ∧ v ≤ timeBoundedNat t y)
  let accept (y : List Bool) : PMF Bool :=
    (q y).map fun v => decide (m - k - g_err ≤ v)
  let fail (x : BitString m) : ℝ := 1 - (approx (List.ofFn x) true).toReal
  have hfail_nonneg (x : BitString m) : 0 ≤ fail x := by
    have := pmf_bool_true_toReal_le_one (approx (List.ofFn x))
    dsimp [fail]
    linarith
  have hpoint (x : BitString m) :
      (pG x).toReal * (accept (List.ofFn x) true).toReal ≤ (pG x).toReal * fail x := by
    by_cases hx : x ∈ pG.support
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      refine pmf_map_true_le_one_sub_of_imp_false (q (List.ofFn x)) _ _ fun v hv => ?_
      have hkx := hlow x hx
      simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hv ⊢
      omega
    · have hx0 : pG x = 0 := by simpa only [PMF.mem_support_iff, not_not] using hx
      simp [hx0]
  let S : Finset (BitString m) :=
    Finset.univ.filter fun x => (pG x).toReal ≤ (2 : ℝ) ^ (-(B - 3))
  have hS_mass : 1 / (m : ℝ) ≤ ∑ x ∈ S, (pG x).toReal :=
    sum_filter_mass_le_ge_of_entropy_ge hm pG hB3 hent
  have hS_sum :
      ∑ x ∈ S, (pG x).toReal * (accept (List.ofFn x) true).toReal ≤
        (2 : ℝ) ^ (-(B - 3)) * ∑ x : BitString m, fail x := by
    calc
      ∑ x ∈ S, (pG x).toReal * (accept (List.ofFn x) true).toReal
        ≤ ∑ x ∈ S, (pG x).toReal * fail x := Finset.sum_le_sum fun x _ => hpoint x
      _ ≤ ∑ x ∈ S, (2 : ℝ) ^ (-(B - 3)) * fail x := by
        refine Finset.sum_le_sum fun x hx => ?_
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact mul_le_mul_of_nonneg_right hx (hfail_nonneg x)
      _ ≤ ∑ x : BitString m, (2 : ℝ) ^ (-(B - 3)) * fail x := by
        refine Finset.sum_le_univ_sum_of_nonneg fun x => ?_
        exact mul_nonneg (by positivity) (hfail_nonneg x)
      _ = (2 : ℝ) ^ (-(B - 3)) * ∑ x : BitString m, fail x := by
        rw [← Finset.mul_sum]
  have hSc_sum :
      ∑ x ∈ Sᶜ, (pG x).toReal * (accept (List.ofFn x) true).toReal ≤ 1 - 1 / (m : ℝ) := by
    have hcompl : (∑ x ∈ S, (pG x).toReal) + ∑ x ∈ Sᶜ, (pG x).toReal = 1 := by
      rw [Finset.sum_add_sum_compl, sum_toReal]
    have hle1 : ∑ x ∈ Sᶜ, (pG x).toReal * (accept (List.ofFn x) true).toReal ≤
        ∑ x ∈ Sᶜ, (pG x).toReal * 1 := by
      refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      exact pmf_bool_true_toReal_le_one _
    simp only [mul_one] at hle1
    linarith
  have hfail_sum :
      (2 : ℝ) ^ (-(B - 3)) * ∑ x : BitString m, fail x =
        (2 : ℝ) ^ ((m : ℝ) - (B - 3)) *
          (1 - (((BitString.uniformList m).bind approx) true).toReal) := by
    have hbind_approx :
        1 - (((BitString.uniformList m).bind approx) true).toReal =
          ((2 : ℝ) ^ m)⁻¹ * ∑ x : BitString m, fail x := by
      simp only [BitString.uniformList, PMF.bind_map, bind_apply_toReal, Function.comp_apply,
        PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat,
        ← Finset.mul_sum, fail, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
      field_simp [h2m]
    rw [hbind_approx, ← mul_assoc]
    congr 1
    rw [← Real.rpow_natCast 2 m, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring_nf
  have hbind_pG :
      (((pG.map List.ofFn).bind accept) true).toReal =
        (∑ x ∈ S, (pG x).toReal * (accept (List.ofFn x) true).toReal) +
          ∑ x ∈ Sᶜ, (pG x).toReal * (accept (List.ofFn x) true).toReal := by
    rw [PMF.bind_map, bind_apply_toReal, ← Finset.sum_add_sum_compl S]
    rfl
  linarith

end Cslib.Kolmogorov
