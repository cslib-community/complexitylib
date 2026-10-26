/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Probability.PMF
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Probability.PMF

/-!
# The rewinding lemma

A two-stage experiment runs a first stage with outcome `s`, draws a challenge `t` from
`challenge s`, and lets a second stage answer `t` from `s`; it succeeds when a test `ok s t a`
of the answer `a` passes. *Rewinding* keeps `s` and reruns the second stage on a fresh challenge,
independent conditional on `s`. If every atom of `challenge s` has mass at most `κ` for every
possible first-stage outcome, one-run success `ε` and two-run success with distinct challenges
`δ` satisfy `ε² − κ * ε ≤ δ` (`sq_sub_mul_le_twice`) and `ε ≤ κ + √δ`
(`le_add_sqrt_twice`). The atom bound is conditional on the saved state; a bound on the
unconditional challenge distribution does not suffice.

This is an original extension of Boneh and Shoup's uniform-challenge rewinding lemma
([BonehShoup2023], Lemma 19.2). For a uniform challenge among `N` possibilities, `κ = 1 / N`
recovers `ε² − ε / N ≤ δ` (`sq_sub_le_twice`) and `ε ≤ 1 / N + √δ`
(`le_inv_add_sqrt_twice`).

The second stage may use fresh randomness in each run. This generalizes the book's
deterministic `f(X, Y)`: averaging over the second stage's coins turns the indicator into a
success probability `p(s, t) ∈ [0, 1]`, and the proof needs only `p ^ 2 ≤ p`. The first stage
and the answer may have infinitely many outcomes; the bounds assume a finite challenge type.
These are exact statements about experiment laws, with no efficiency or sampler-realization
claim.

The experiments are written in `do` notation for `PMF`, whose monad lives in a single universe;
since they return a `PMF Bool`, the outcome, challenge and answer types are in `Type`.

## Main definitions

* `Cslib.Probability.Rewinding.once`: one run of the two-stage experiment.
* `Cslib.Probability.Rewinding.twice`: two runs sharing the first stage, with independent
  challenges conditional on that state, and independent second-stage randomness.

## Main results

* `Cslib.Probability.Rewinding.sq_sub_mul_le_twice`: `ε² − κ * ε ≤ δ` for bounded challenge atoms.
* `Cslib.Probability.Rewinding.le_add_sqrt_twice`: `ε ≤ κ + √δ` for bounded challenge atoms.
* `Cslib.Probability.Rewinding.sq_sub_le_twice`: `ε² − ε / N ≤ δ` ([BonehShoup2023], Lemma 19.2).
* `Cslib.Probability.Rewinding.le_inv_add_sqrt_twice`: `ε ≤ 1 / N + √δ`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Lemma 19.2 and the proof of Theorem 19.1.
-/

@[expose] public section

namespace Cslib.Probability.Rewinding

variable {S T A : Type}

/-- The law of one run of a two-stage experiment: the first stage, a challenge from the law
chosen by that state, the second stage's answer, and its acceptance test. -/
noncomputable def once (first : PMF S) (challenge : S → PMF T) (answer : S → T → PMF A)
    (ok : S → T → A → Bool) : PMF Bool := do
  let s ← first
  let t ← challenge s
  let a ← answer s t
  return ok s t a

/-- The law of rewinding: one first stage, then two challenges sampled independently from the
same conditional law, and two answers with independent randomness. It succeeds when both answers
pass their tests and the challenges are distinct. -/
noncomputable def twice [DecidableEq T] (first : PMF S) (challenge : S → PMF T)
    (answer : S → T → PMF A) (ok : S → T → A → Bool) : PMF Bool := do
  let s ← first
  let t ← challenge s
  let t' ← challenge s
  let a ← answer s t
  let a' ← answer s t'
  return (ok s t a && ok s t' a' && t != t')

/-! ### Proof of the rewinding lemma -/

/-- Jensen's inequality `E[g]² ≤ E[g²]` for a function with values in `[0, 1]`. -/
private theorem sq_tsum_le_tsum_sq {α : Type*} (μ : PMF α) {g : α → ℝ} (h0 : ∀ a, 0 ≤ g a)
    (h1 : ∀ a, g a ≤ 1) :
    (∑' a, (μ a).toReal * g a) ^ 2 ≤ ∑' a, (μ a).toReal * g a ^ 2 := by
  have hm : Summable fun a => (μ a).toReal := Probability.PMF.summable_toReal μ
  have hbounded {f : α → ℝ} (f0 : ∀ a, 0 ≤ f a) (f1 : ∀ a, f a ≤ 1) :
      Summable fun a => (μ a).toReal * f a :=
    hm.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (f0 a))
      fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 a)
  have hg := hbounded h0 h1
  have hg2 := hbounded (fun a => sq_nonneg (g a)) fun a => pow_le_one₀ (h0 a) (h1 a)
  set e := ∑' a, (μ a).toReal * g a
  have hexpand : ∑' a, (μ a).toReal * (g a - e) ^ 2 =
      ∑' a, (μ a).toReal * g a ^ 2 - e ^ 2 := by
    have hsplit : (fun a => (μ a).toReal * (g a - e) ^ 2) = fun a =>
        ((μ a).toReal * g a ^ 2 - 2 * e * ((μ a).toReal * g a)) + e ^ 2 * (μ a).toReal := by
      funext a
      ring
    rw [hsplit, (hg2.sub (hg.mul_left (2 * e))).tsum_add (hm.mul_left (e ^ 2)),
      hg2.tsum_sub (hg.mul_left (2 * e)), tsum_mul_left, tsum_mul_left,
      Probability.PMF.tsum_toReal]
    ring
  have hnonneg : 0 ≤ ∑' a, (μ a).toReal * (g a - e) ^ 2 :=
    tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  linarith

/-- Two independent Boolean outcomes are both true, together with a fixed condition, with the
product probability. -/
private theorem bind_bind_and_apply (X Y : PMF A) (f g : A → Bool) (d : Bool) :
    (X.bind fun a => Y.bind fun a' => PMF.pure (f a && g a' && d)) true =
      if d then X.map f true * Y.map g true else 0 := by
  have hmap : (X.bind fun a => Y.bind fun a' => PMF.pure (f a && g a' && d)) =
      (X.map f).bind fun b => (Y.map g).bind fun b' => PMF.pure (b && b' && d) := by
    simp only [PMF.bind_map, Function.comp_def]
  rw [hmap]
  cases d
  · simp only [Bool.and_false, PMF.bind_const, PMF.pure_apply, Bool.true_eq_false,
      Bool.false_eq_true, ite_false]
  · simp only [Bool.and_true, PMF.bind_apply, tsum_bool, PMF.pure_apply, Bool.and_false,
      Bool.true_eq_false, ite_false, ite_true, mul_zero, zero_add, mul_one]

/-- The success probability of the second stage at the challenge `t`. -/
private noncomputable def pass (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    ℝ :=
  ((answer s t).map (ok s t) true).toReal

private theorem pass_nonneg (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    0 ≤ pass answer ok s t := ENNReal.toReal_nonneg

private theorem pass_le_one (answer : S → T → PMF A) (ok : S → T → A → Bool) (s : S) (t : T) :
    pass answer ok s t ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact PMF.coe_le_one _ true)

variable [Fintype T]

/-- An average of values in `[0, 1]` lies in `[0, 1]`. -/
private theorem average_mem_Icc (μ : PMF T) (f : T → ℝ) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ 1) :
    0 ≤ ∑ t, (μ t).toReal * f t ∧ ∑ t, (μ t).toReal * f t ≤ 1 := by
  refine ⟨Finset.sum_nonneg fun t _ => mul_nonneg ENNReal.toReal_nonneg (h0 t), ?_⟩
  calc ∑ t, (μ t).toReal * f t ≤ ∑ t, (μ t).toReal :=
        Finset.sum_le_sum fun t _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (h1 t)
    _ = 1 := Probability.PMF.sum_toReal μ

/-- At one saved state, removing equal-challenge pairs loses at most `κ` times the one-run
success probability when every challenge atom has mass at most `κ`. -/
private theorem sq_sub_le_pairs [DecidableEq T] (μ : PMF T) (p : T → ℝ)
    (h0 : ∀ t, 0 ≤ p t) (h1 : ∀ t, p t ≤ 1) {κ : ℝ}
    (hκ : ∀ t, (μ t).toReal ≤ κ) :
    (∑ t, (μ t).toReal * p t) ^ 2 - κ * (∑ t, (μ t).toReal * p t) ≤
      ∑ t, (μ t).toReal * ∑ t', (μ t').toReal *
        (if t = t' then 0 else p t * p t') := by
  set q : T → ℝ := fun t => (μ t).toReal * p t
  have hq0 (t : T) : 0 ≤ q t := mul_nonneg ENNReal.toReal_nonneg (h0 t)
  have hqκ (t : T) : q t ≤ κ :=
    (mul_le_of_le_one_right ENNReal.toReal_nonneg (h1 t)).trans (hκ t)
  have hdiag : ∑ t, q t * q t ≤ κ * ∑ t, q t := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (hqκ t) (hq0 t)
  have hoff (t : T) : ∑ t', (if t = t' then 0 else q t * q t') =
      q t * ∑ t', q t' - q t * q t := by
    have hite : (fun t' => if t = t' then 0 else q t * q t') = fun t' =>
        q t * q t' - if t = t' then q t * q t' else 0 := by
      funext t'
      split_ifs <;> ring
    rw [hite, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq,
      ite_eq_left (Finset.mem_univ t)]
  have hpair (t t' : T) :
      (μ t).toReal * ((μ t').toReal * (if t = t' then 0 else p t * p t')) =
        if t = t' then 0 else q t * q t' := by
    dsimp only [q]
    split_ifs <;> ring
  calc (∑ t, q t) ^ 2 - κ * (∑ t, q t)
      ≤ (∑ t, q t) ^ 2 - ∑ t, q t * q t := sub_le_sub_left hdiag _
    _ = ∑ t, ∑ t', (if t = t' then 0 else q t * q t') := by
      simp only [hoff, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = _ := by simp only [Finset.mul_sum, hpair]

/-- One-run success averages the conditional second-stage success probabilities. -/
private theorem toReal_once (first : PMF S) (challenge : S → PMF T)
    (answer : S → T → PMF A) (ok : S → T → A → Bool) :
    (once first challenge answer ok true).toReal =
      ∑' s, (first s).toReal * ∑ t, (challenge s t).toReal * pass answer ok s t := by
  simp only [once, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]
  refine tsum_congr fun s => congrArg _ ?_
  rw [Probability.PMF.bind_apply_toReal]
  rfl

/-- Two-run success averages the product probabilities at distinct challenges. -/
private theorem toReal_twice [DecidableEq T] (first : PMF S) (challenge : S → PMF T)
    (answer : S → T → PMF A) (ok : S → T → A → Bool) :
    (twice first challenge answer ok true).toReal =
      ∑' s, (first s).toReal * ∑ t, (challenge s t).toReal *
        ∑ t', (challenge s t').toReal *
          (if t = t' then 0 else pass answer ok s t * pass answer ok s t') := by
  simp only [twice, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
  rw [Probability.PMF.bind_apply_toReal_tsum]
  refine tsum_congr fun s => congrArg _ ?_
  rw [Probability.PMF.bind_apply_toReal]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Probability.PMF.bind_apply_toReal]
  refine congrArg _ (Finset.sum_congr rfl fun t' _ => ?_)
  rw [bind_bind_and_apply]
  by_cases h : t = t' <;> simp [h, pass, ENNReal.toReal_mul]

/-! ### Challenges with bounded atoms -/

variable [DecidableEq T] (first : PMF S) (challenge : S → PMF T)
  (answer : S → T → PMF A) (ok : S → T → A → Bool)

omit [Fintype T] in
/-- **Rewinding with bounded challenge atoms.** If each conditional challenge law has atoms of
mass at most `κ`, one-run success `ε` and two-run success at distinct challenges `δ` satisfy
`ε² − κ * ε ≤ δ`. The bound is needed only on possible first-stage outcomes.

This is an original extension of [BonehShoup2023], Lemma 19.2, to biased challenges depending on
the saved state. It concerns experiment laws, with no efficiency claim. -/
theorem sq_sub_mul_le_twice [Finite T] {κ : ℝ}
    (hκ : ∀ s ∈ first.support, ∀ t, (challenge s t).toReal ≤ κ) :
    (once first challenge answer ok true).toReal ^ 2 -
        κ * (once first challenge answer ok true).toReal ≤
      (twice first challenge answer ok true).toReal := by
  let := Fintype.ofFinite T
  set p := pass answer ok
  set g : S → ℝ := fun s => ∑ t, (challenge s t).toReal * p s t
  set h : S → ℝ := fun s => ∑ t, (challenge s t).toReal *
    ∑ t', (challenge s t').toReal * (if t = t' then 0 else p s t * p s t')
  have hg (s : S) : 0 ≤ g s ∧ g s ≤ 1 :=
    average_mem_Icc (challenge s) _ (pass_nonneg answer ok s) (pass_le_one answer ok s)
  have hpair (s : S) (t t' : T) :
      0 ≤ (if t = t' then 0 else p s t * p s t') ∧ (if t = t' then 0 else p s t * p s t') ≤ 1 := by
    split_ifs
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨mul_nonneg (pass_nonneg _ _ _ _) (pass_nonneg _ _ _ _),
        (mul_le_mul (pass_le_one _ _ _ _) (pass_le_one _ _ _ _) (pass_nonneg _ _ _ _)
          zero_le_one).trans_eq (one_mul 1)⟩
  have hh (s : S) : 0 ≤ h s ∧ h s ≤ 1 := by
    refine average_mem_Icc (challenge s) _
      (fun t => (average_mem_Icc (challenge s) _ (fun t' => (hpair s t t').1)
        fun t' => (hpair s t t').2).1)
      fun t => (average_mem_Icc (challenge s) _ (fun t' => (hpair s t t').1)
        fun t' => (hpair s t t').2).2
  have hm : Summable fun s => (first s).toReal := Probability.PMF.summable_toReal first
  have hsum {f : S → ℝ} (f0 : ∀ s, 0 ≤ f s) (f1 : ∀ s, f s ≤ 1) :
      Summable fun s => (first s).toReal * f s :=
    hm.of_nonneg_of_le (fun s => mul_nonneg ENNReal.toReal_nonneg (f0 s))
      fun s => mul_le_of_le_one_right ENNReal.toReal_nonneg (f1 s)
  have hsumg := hsum (fun s => (hg s).1) fun s => (hg s).2
  have hsumg2 := hsum (fun s => sq_nonneg (g s)) fun s => pow_le_one₀ (hg s).1 (hg s).2
  have hsumh := hsum (fun s => (hh s).1) fun s => (hh s).2
  have hpoint (s : S) :
      (first s).toReal * g s ^ 2 - κ * ((first s).toReal * g s) ≤ (first s).toReal * h s := by
    by_cases hs : s ∈ first.support
    · calc _ = (first s).toReal * (g s ^ 2 - κ * g s) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_left
             (sq_sub_le_pairs (challenge s) (p s) (pass_nonneg answer ok s)
               (pass_le_one answer ok s) (hκ s hs)) ENNReal.toReal_nonneg
    · simp [(PMF.apply_eq_zero_iff first s).mpr hs]
  rw [toReal_once, toReal_twice]
  calc (∑' s, (first s).toReal * g s) ^ 2 - κ * (∑' s, (first s).toReal * g s)
      ≤ ∑' s, (first s).toReal * g s ^ 2 - κ * (∑' s, (first s).toReal * g s) := by
        gcongr
        exact sq_tsum_le_tsum_sq first (fun s => (hg s).1) fun s => (hg s).2
    _ = ∑' s, ((first s).toReal * g s ^ 2 - κ * ((first s).toReal * g s)) := by
        rw [hsumg2.tsum_sub (hsumg.mul_left κ), tsum_mul_left]
    _ ≤ ∑' s, (first s).toReal * h s :=
        (hsumg2.sub (hsumg.mul_left κ)).tsum_le_tsum hpoint hsumh

omit [Fintype T] in
/-- The bounded-atom rewinding inequality solved for one-run success: `ε ≤ κ + √δ`.
The conditional atom hypothesis implies `κ ≥ 0`; no separate sign assumption is needed. -/
theorem le_add_sqrt_twice [Finite T] {κ : ℝ}
    (hκ : ∀ s ∈ first.support, ∀ t, (challenge s t).toReal ≤ κ) :
    (once first challenge answer ok true).toReal ≤
      κ + √(twice first challenge answer ok true).toReal := by
  obtain ⟨s, hs⟩ := first.support_nonempty
  obtain ⟨t, -⟩ := (challenge s).support_nonempty
  have hκ0 : 0 ≤ κ := ENNReal.toReal_nonneg.trans (hκ s hs t)
  set ε := (once first challenge answer ok true).toReal
  have hδ := sq_sub_mul_le_twice first challenge answer ok hκ
  by_cases hε : ε ≤ κ
  · exact hε.trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · have hsq : (ε - κ) ^ 2 ≤ (twice first challenge answer ok true).toReal := by
      nlinarith [mul_nonneg hκ0 (sub_nonneg.mpr (le_of_not_ge hε))]
    have := Real.abs_le_sqrt hsq
    linarith [le_abs_self (ε - κ)]

/-! ### Uniform challenges -/

variable [Nonempty T]

omit [DecidableEq T] in
/-- The real probability of a uniform challenge's outcome. -/
private theorem toReal_uniformOfFintype (t : T) :
    (PMF.uniformOfFintype T t).toReal = (Fintype.card T : ℝ)⁻¹ := by
  simp only [Probability.PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast]

/-- **Rewinding lemma** ([BonehShoup2023], Lemma 19.2): if one run succeeds with probability `ε`,
then two runs sharing the first stage succeed with distinct challenges with probability at least
`ε ^ 2 - ε / N`, where `N` is the number of uniform challenges. -/
theorem sq_sub_le_twice :
    (once first (fun _ => PMF.uniformOfFintype T) answer ok true).toReal ^ 2 -
        (once first (fun _ => PMF.uniformOfFintype T) answer ok true).toReal / Fintype.card T ≤
      (twice first (fun _ => PMF.uniformOfFintype T) answer ok true).toReal := by
  simpa only [div_eq_mul_inv, mul_comm] using
    sq_sub_mul_le_twice first (fun _ => PMF.uniformOfFintype T) answer ok
      (κ := (Fintype.card T : ℝ)⁻¹) (fun _ _ t => (toReal_uniformOfFintype t).le)

/-- The uniform rewinding lemma solved for the one-run probability ([BonehShoup2023], from the
proof of Theorem 19.1): `ε ≤ 1 / N + √δ`. -/
theorem le_inv_add_sqrt_twice :
    (once first (fun _ => PMF.uniformOfFintype T) answer ok true).toReal ≤
      1 / Fintype.card T +
        √(twice first (fun _ => PMF.uniformOfFintype T) answer ok true).toReal := by
  simpa only [one_div] using
    le_add_sqrt_twice first (fun _ => PMF.uniformOfFintype T) answer ok
      (κ := (Fintype.card T : ℝ)⁻¹) (fun _ _ t => (toReal_uniformOfFintype t).le)

end Cslib.Probability.Rewinding
