/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.StatisticalAudit
public import CslibFrontier.Probability.Testing
public import CslibFrontier.Probability.ProductDivergence
import Mathlib.Tactic

/-!
# The binary hard family for adaptivity auditing

[Aldridge2027], Theorem 5.4, PDF p. 5. Contexts are uniform binary variables.
The policy plays the matching action with probability `p`. Only the cost of
action `true` in context `true` has perturbed Bernoulli mean `1/2 + u`.
`hardLaw` is the full observable context/action/binary-loss law; propensities
are known deterministic functions of context and so convey no additional
instance-dependent information. Sample laws are actual independent products.

## Main definitions

* `hardLaw`: the normalized logged-data experiment.
* `hardGap`: its actual policy-minus-marginal expected cost.

## Main results

* `auditing_lower_bound`: the quantitative minimax bound for every permitted divergence.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal
namespace Cslib.Probability.AdaptivePolicy.AuditLowerBound

/-- The complete observable binary context, action and observed loss. -/
abbrev BinaryLog := Bool × Bool × Bool

/-- Behavior policy of the lower-bound family. -/
@[expose] def hardAction (p : ℝ) (x a : Bool) : ℝ := if x = a then p else 1 - p

/-- Conditional mean of the selected Bernoulli loss. -/
@[expose] def hardMean (u : ℝ) (x a : Bool) : ℝ := if x && a then 1 / 2 + u else 1 / 2

/-- Actual probability of each complete log record. -/
@[expose] def hardMass (p u : ℝ) : BinaryLog → ℝ :=
  fun (x, a, y) => 1 / 2 * hardAction p x a *
    (if y then hardMean u x a else 1 - hardMean u x a)

/-- Every outcome has positive probability in the stated parameter regime. -/
theorem hardMass_pos {p u : ℝ} (hp : 0 < p) (hpmax : p ≤ 1 / 4)
    (hu : |u| ≤ 1 / 4) (z : BinaryLog) : 0 < hardMass p u z := by
  obtain ⟨hulo, huhi⟩ := abs_le.mp hu
  obtain ⟨x, a, y⟩ := z
  have hp1 : 0 < 1 - p := by linarith
  have hplus : 0 < 1 / 2 + u := by linarith
  have hminus : 0 < 1 - (1 / 2 + u) := by linarith
  cases x <;> cases a <;> cases y <;>
    norm_num [hardMass, hardAction, hardMean] <;> first | positivity | linarith


/-- The conditional action and loss draws are normalized. -/
theorem hardMass_sum (p u : ℝ) : ∑ z, hardMass p u z = 1 := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, hardMass, hardAction, hardMean]
  norm_num
  ring

/-- The exact logged-data PMF; no moment or statistical bound is assumed. -/
@[expose] def hardLaw (p u : ℝ) (hp : 0 < p) (hpmax : p ≤ 1 / 4)
    (hu : |u| ≤ 1 / 4) : PMF BinaryLog :=
  PMF.ofFintype (fun z => ENNReal.ofReal (hardMass p u z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => (hardMass_pos hp hpmax hu z).le),
      hardMass_sum, ENNReal.ofReal_one])

/-- Real masses of the actual experiment agree with the displayed probability table. -/
theorem hardLaw_toReal (p u : ℝ) (hp : 0 < p) (hpmax : p ≤ 1 / 4)
    (hu : |u| ≤ 1 / 4) (z : BinaryLog) :
    (hardLaw p u hp hpmax hu z).toReal = hardMass p u z :=
  ENNReal.toReal_ofReal (hardMass_pos hp hpmax hu z).le

/-- The hard law has full support, including all loss outcomes. -/
theorem hardLaw_ne_zero (p u : ℝ) (hp : 0 < p) (hpmax : p ≤ 1 / 4)
    (hu : |u| ≤ 1 / 4) (z : BinaryLog) : hardLaw p u hp hpmax hu z ≠ 0 :=
  ENNReal.ofReal_ne_zero_iff.mpr (hardMass_pos hp hpmax hu z)

/-- Expected behavior cost minus expected marginal-policy cost of the actual
contextual instance, whose marginal action frequencies are both one half. -/
@[expose] def hardGap (p u : ℝ) : ℝ :=
  (∑ x : Bool, ∑ a : Bool, 1 / 2 * hardAction p x a * hardMean u x a) -
    ∑ x : Bool, ∑ a : Bool, 1 / 2 * (1 / 2) * hardMean u x a

/-- The target policy is the actual marginal of the behavior policy. -/
theorem hardAction_marginal (p : ℝ) (a : Bool) :
    (∑ x : Bool, 1 / 2 * hardAction p x a) = 1 / 2 := by
  cases a <;> norm_num [hardAction] <;> ring

/-- The expected gap of the hard family, with the paper's cost sign. -/
theorem hardGap_eq (p u : ℝ) : hardGap p u = -u * (1 - 2 * p) / 4 := by
  norm_num [hardGap, hardAction, hardMean]
  ring

/-- The two alternatives with perturbations `±8δ` are separated by `2δ`,
including the endpoint `p = 1/4`. -/
theorem hardGap_separation {p δ : ℝ} (hpmax : p ≤ 1 / 4) (hδ : 0 < δ) :
    2 * δ ≤ |hardGap p (8 * δ) - hardGap p (-(8 * δ))| := by
  rw [hardGap_eq, hardGap_eq]
  have hn : -(8 * δ) * (1 - 2 * p) / 4 - -(-(8 * δ)) * (1 - 2 * p) / 4 ≤ 0 := by
    nlinarith
  rw [abs_of_nonpos hn]
  nlinarith

/-- Every desired divergence parameter at least `1/3` has an admissible
exploration probability. This is an exact quantified family, not sampled parameters. -/
theorem exists_exploration_parameter {Γ : ℝ} (hΓ : 1 / 3 ≤ Γ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 / 4 ∧ 1 / (4 * p * (1 - p)) - 1 = Γ ∧
      3 * (Γ + 1) ≤ 1 / p := by
  let r := Real.sqrt (Γ / (Γ + 1))
  have hΓ0 : 0 < Γ := by linarith
  have hΓ1 : 0 < Γ + 1 := by linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = Γ / (Γ + 1) := Real.sq_sqrt (div_nonneg hΓ0.le hΓ1.le)
  have hratio : Γ / (Γ + 1) < 1 := (div_lt_one hΓ1).mpr (by linarith)
  have hr1 : r < 1 := by nlinarith
  have hratioLower : 1 / 4 ≤ Γ / (Γ + 1) := (le_div_iff₀ hΓ1).mpr (by linarith)
  have hrhalf : 1 / 2 ≤ r := by nlinarith
  let p := (1 - r) / 2
  have hp : 0 < p := by dsimp only [p]; linarith
  have hpmax : p ≤ 1 / 4 := by dsimp only [p]; linarith
  have hprod : 4 * p * (1 - p) * (Γ + 1) = 1 := by
    have heq := (div_eq_iff hΓ1.ne').mp hr2.symm
    dsimp only [p]
    nlinarith
  have hp1 : 0 < 1 - p := by linarith
  have hden : 4 * p * (1 - p) ≠ 0 := by positivity
  refine ⟨p, hp, hpmax, ?_, ?_⟩
  · apply (sub_eq_iff_eq_add).mpr
    apply (div_eq_iff hden).mpr
    nlinarith [hprod]
  · apply (le_div_iff₀ hp).mpr
    nlinarith [hprod]

/-- Exact average chi-squared divergence of the hard policy. -/
theorem hard_averagePearson {p : ℝ} (hp : 0 < p) (hpmax : p ≤ 1 / 4) :
    averagePearson (PMF.uniformOfFintype Bool).toMeasure (hardAction p) (fun _ _ => 1 / 2) =
      ENNReal.ofReal (1 / (4 * p * (1 - p)) - 1) := by
  have hp1 : 0 < 1 - p := by linarith
  have hb (x a : Bool) : 0 < hardAction p x a := by
    unfold hardAction
    split <;> assumption
  have hc (x : Bool) : conditionalPearson (hardAction p) (fun _ _ => 1 / 2) x =
      ENNReal.ofReal (1 / (4 * p * (1 - p)) - 1) := by
    rw [conditionalPearson_eq (fun x a => (hb x a).le) x
      (fun a ha => False.elim ((hb x a).ne' ha))]
    simp_rw [← ENNReal.ofReal_mul (hb _ _).le]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (hb x a).le (sq_nonneg _))]
    congr 1
    cases x <;> norm_num [hardAction] <;> field_simp [hp.ne', hp1.ne'] <;> ring
  unfold averagePearson
  simp only [hc, lintegral_const, measure_univ, mul_one]

/-- Single-log KL is bounded by the rare observation's Bernoulli discrepancy. -/
theorem hardLaw_klDiv_le {p u : ℝ} (hp : 0 < p) (hpmax : p ≤ 1 / 4)
    (hu : |u| ≤ 1 / 4) :
    (klDiv (hardLaw p u hp hpmax hu).toMeasure
      (hardLaw p (-u) hp hpmax (by simpa only [abs_neg] using hu)).toMeasure).toReal ≤
        32 / 3 * p * u ^ 2 := by
  have hneg : |-u| ≤ 1 / 4 := by simpa only [abs_neg] using hu
  have h := Cslib.Probability.PMF.toReal_klDiv_le_pearson
    (hardLaw p u hp hpmax hu) (hardLaw p (-u) hp hpmax hneg)
    (hardLaw_ne_zero p u hp hpmax hu) (hardLaw_ne_zero p (-u) hp hpmax hneg)
  simp only [hardLaw_toReal] at h
  have hsum : (∑ z : BinaryLog,
      (hardMass p u z - hardMass p (-u) z) ^ 2 / hardMass p (-u) z) =
        2 * p * u ^ 2 / (1 / 4 - u ^ 2) := by
    have hulo := (abs_le.mp hu).1
    have huhi := (abs_le.mp hu).2
    have hp1 : 0 < 1 - p := by linarith
    have hp2 : 0 < 1 / 2 + u := by linarith
    have hm2 : 0 < 1 / 2 - u := by linarith
    have hden : 0 < 1 / 4 - u ^ 2 := by nlinarith [sq_abs u, (sq_le_sq₀ (abs_nonneg u)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hu]
    norm_num [Fintype.sum_prod_type, hardMass, hardAction, hardMean]
    field_simp [hp.ne', hp1.ne', hp2.ne', hm2.ne', hden.ne',
      (show 1 - u * 2 ≠ 0 by linarith), (show 1 + u * 2 ≠ 0 by linarith),
      (show 1 - u ^ 2 * 4 ≠ 0 by nlinarith)]
    ring_nf
    field_simp [(show 1 - u * 2 ≠ 0 by linarith), (show 1 + u * 2 ≠ 0 by linarith)]
    ring
  rw [hsum] at h
  have hsq : u ^ 2 ≤ 1 / 16 := by nlinarith [sq_abs u,
    (sq_le_sq₀ (abs_nonneg u) (by norm_num : (0 : ℝ) ≤ 1 / 4)).mpr hu]
  have hden : 0 < 1 / 4 - u ^ 2 := by linarith
  apply h.trans
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_nonneg (mul_nonneg hp.le (sq_nonneg u)) (show 0 ≤ 1 / 16 - u ^ 2 by linarith)]

/-- The hard family enforces the paper's confidence-dependent sample lower
bound against every randomized auditor on the complete independent logs. -/
theorem hardLaw_sample_lower_bound {p Γ δ η : ℝ}
    (hp : 0 < p) (hpmax : p ≤ 1 / 4) (hΓ : 1 / 3 ≤ Γ)
    (hparam : 3 * (Γ + 1) ≤ 1 / p)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 32) (hη : 0 < η) (hηmax : η ≤ 1 / 8)
    (T : ℕ) (auditor : Kernel (Fin T → BinaryLog) ℝ) [IsMarkovKernel auditor]
    (hplus : 1 - η ≤ (auditor ∘ₘ (Cslib.Probability.PMF.pi
      (fun _ : Fin T => hardLaw p (8 * δ) hp hpmax
        (by rw [abs_of_pos (mul_pos (by norm_num) hδ)]; linarith))).toMeasure).real
          {y | |y - hardGap p (8 * δ)| < δ})
    (hminus : 1 - η ≤ (auditor ∘ₘ (Cslib.Probability.PMF.pi
      (fun _ : Fin T => hardLaw p (-(8 * δ)) hp hpmax
        (by rw [abs_neg, abs_of_pos (mul_pos (by norm_num) hδ)]; linarith))).toMeasure).real
          {y | |y - hardGap p (-(8 * δ))| < δ}) :
    9 / 2048 * (Γ + 1) * Real.log (1 / (4 * η)) / δ ^ 2 ≤ T := by
  have hu : |8 * δ| ≤ 1 / 4 := by rw [abs_of_pos (by positivity)]; linarith
  have hnu : |-(8 * δ)| ≤ 1 / 4 := by simpa only [abs_neg] using hu
  let P := hardLaw p (8 * δ) hp hpmax hu
  let Q := hardLaw p (-(8 * δ)) hp hpmax hnu
  let PP := Cslib.Probability.PMF.pi (fun _ : Fin T => P)
  let QQ := Cslib.Probability.PMF.pi (fun _ : Fin T => Q)
  have hp0 : ∀ z, P z ≠ 0 := hardLaw_ne_zero _ _ _ _ _
  have hq0 : ∀ z, Q z ≠ 0 := hardLaw_ne_zero _ _ _ _ _
  have hqt : ∀ z, QQ z ≠ 0 := by
    intro z
    simp only [QQ, Cslib.Probability.PMF.pi_apply, prod_ne_zero_iff]
    exact fun i _ => hq0 (z i)
  have hfinite : klDiv PP.toMeasure QQ.toMeasure ≠ ⊤ :=
    Cslib.Probability.PMF.klDiv_toMeasure_ne_top_iff.mpr
      (fun z _ => (PMF.mem_support_iff QQ z).mpr (hqt z))
  have htest := estimation_separation_le_klDiv PP.toMeasure QQ.toMeasure auditor hη
    (show η ≤ 1 by linarith) (hardGap_separation hpmax hδ) hplus hminus
  have hlog : 0 ≤ Real.log (1 / (4 * η)) :=
    Real.log_nonneg ((le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η)).mpr (by linarith))
  have hlower := ENNReal.toReal_mono hfinite htest
  rw [ENNReal.toReal_ofReal hlog] at hlower
  have hupper : (klDiv PP.toMeasure QQ.toMeasure).toReal ≤
      2048 / 3 * T * p * δ ^ 2 := by
    rw [Cslib.Probability.PMF.toReal_klDiv_pi _ _ (fun _ => hp0) (fun _ => hq0)]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hsingle := hardLaw_klDiv_le hp hpmax hu
    have hmul := mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    dsimp only [P, Q] at *
    nlinarith [hmul]
  have hbound := hlower.trans hupper
  have hΓ1 : 0 < Γ + 1 := by linarith
  have hparam' : 3 * (Γ + 1) * p ≤ 1 := (le_div_iff₀ hp).mp hparam
  have hmul := mul_le_mul_of_nonneg_left hbound (show 0 ≤ 3 * (Γ + 1) by positivity)
  have hmul' := mul_le_mul_of_nonneg_left hparam'
    (show 0 ≤ (2048 : ℝ) * T * δ ^ 2 by positivity)
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).mpr
  nlinarith [hmul, hmul']

/-- Theorem 5.4: for every permitted divergence and accuracy/confidence pair,
there are two actual binary-cost instances enforcing the stated minimax lower
bound. The quantifier covers arbitrary randomized auditors and every integer
sample count, including zero. -/
theorem auditing_lower_bound {Γ δ η : ℝ} (hΓ : 1 / 3 ≤ Γ)
    (hδ : 0 < δ) (hδmax : δ ≤ 1 / 32) (hη : 0 < η) (hηmax : η ≤ 1 / 8) :
    ∃ (p : ℝ) (hp : 0 < p) (hpmax : p ≤ 1 / 4),
      averagePearson (PMF.uniformOfFintype Bool).toMeasure (hardAction p) (fun _ _ => 1 / 2) =
        ENNReal.ofReal Γ ∧
      ∀ (T : ℕ) (auditor : Kernel (Fin T → BinaryLog) ℝ) (_ : IsMarkovKernel auditor),
        1 - η ≤ (auditor ∘ₘ (Cslib.Probability.PMF.pi
          (fun _ : Fin T => hardLaw p (8 * δ) hp hpmax
            (by rw [abs_of_pos (mul_pos (by norm_num) hδ)]; linarith))).toMeasure).real
              {y | |y - hardGap p (8 * δ)| < δ} →
        1 - η ≤ (auditor ∘ₘ (Cslib.Probability.PMF.pi
          (fun _ : Fin T => hardLaw p (-(8 * δ)) hp hpmax
            (by rw [abs_neg, abs_of_pos (mul_pos (by norm_num) hδ)]; linarith))).toMeasure).real
              {y | |y - hardGap p (-(8 * δ))| < δ} →
        9 / 2048 * (Γ + 1) * Real.log (1 / (4 * η)) / δ ^ 2 ≤ T := by
  obtain ⟨p, hp, hpmax, hchi, hparam⟩ := exists_exploration_parameter hΓ
  refine ⟨p, hp, hpmax, ?_, ?_⟩
  · rw [hard_averagePearson hp hpmax, hchi]
  · intro T auditor hMarkov hplus hminus
    exact hardLaw_sample_lower_bound hp hpmax hΓ hparam hδ hδmax hη hηmax T auditor hplus hminus

/-- Probability mass of context and both potential costs, drawn before the
action. The two Bernoulli coordinates are independent conditional on context. -/
@[expose] def hardPotentialMass (u : ℝ) (x yfalse ytrue : Bool) : ℝ :=
  1 / 2 * (if yfalse then (1 / 2 : ℝ) else 1 - 1 / 2) *
    (if ytrue then hardMean u x true else 1 - hardMean u x true)

/-- The observed hard-law table is the marginal of an actual potential-cost
experiment in which action sampling is independent of costs given context. -/
theorem hardMass_observation (p u : ℝ) (x a y : Bool) :
    (∑ yfalse : Bool, ∑ ytrue : Bool,
      hardPotentialMass u x yfalse ytrue * hardAction p x a *
        (if (if a then ytrue else yfalse) = y then 1 else 0)) = hardMass p u (x, a, y) := by
  cases x <;> cases a <;> cases y <;>
    norm_num [hardPotentialMass, hardMass, hardMean, hardAction] <;> ring

end Cslib.Probability.AdaptivePolicy.AuditLowerBound
