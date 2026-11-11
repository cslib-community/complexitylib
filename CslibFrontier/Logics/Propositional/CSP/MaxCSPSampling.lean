/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.MaxCSP
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.PMF
public import CslibFrontier.Probability.PMF.Union
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Uniform constraint subsampling and the `2 δ m` optimality loss for `Max-CSP`

Given an `m`-constraint `Max-CSP` (or `[0, 1]`-weighted `WeightedMaxCSP`) instance `F` on `n`
declared variables over a finite inhabited domain `D`, drawing `s` constraints uniformly and
independently with replacement (`uniformSamplePMF`) produces a sparse `s`-constraint instance
`F.sample ω` whose rescaled score `(m / s) * (F.sample ω).score sem x` concentrates uniformly around
`F.score sem x` across all `|D| ^ n` assignments:

1. **Single-assignment Hoeffding tail (`WeightedMaxCSP.sample_score_abs_sub_ge_le`):**
   for `δ ≥ 0` and each assignment `x`, the rescaled sample score deviates from `F.score sem x` by
   at least `δ * m` with probability at most `2 * exp (-2 * s * δ ^ 2)`.
2. **Uniform union bound (`WeightedMaxCSP.exists_sample_score_abs_sub_ge_le`,
   `WeightedMaxCSP.boolean_exists_sample_score_abs_sub_ge_le`,
   `MaxCSPInstance.boolean_exists_sample_score_abs_sub_ge_le`):**
   for `δ ≥ 0`, uniform deviation `≥ δ * m` at *some* assignment occurs with probability at most
   `|D| ^ n * 2 * exp (-2 * s * δ ^ 2)`, specializing over `Bool` (`|Bool| = 2`) to
   `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`.
3. **Deterministic `2 * δ * m` optimality loss (`WeightedMaxCSP.optimum_sub_score_le_two_mul`,
   `MaxCSPInstance.optimum_sub_score_le_two_mul`):**
   whenever the rescaled sample score approximates `F.score sem` within `δ * m` on every
   assignment, the rescaled sample optimum is within `δ * m` of `F.optimum sem` and *every*
   assignment `xHat` maximizing the sampled instance achieves
   `F.optimum sem - F.score sem xHat ≤ 2 * δ * m` (yielding a `(1 - ε)`-approximation whenever
   `0 < α`, `0 ≤ δ`, `F.optimum sem ≥ α * m`, and `2 * δ ≤ ε * α`).
4. **Probabilistic loss tail and existence (`MaxCSPInstance.boolean_sample_loss_gt_le`,
   `MaxCSPInstance.exists_boolean_sample_approx`):**
   over `Bool` with `δ ≥ 0`, every sampled maximizer achieves loss at most `2 * δ * m` with
   probability at least `1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`, guaranteeing a good `s`-constraint
   subsample whenever `(n + 1) * log 2 < 2 * s * δ ^ 2`.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*][AlonSpencer2016]
* [M. Mitzenmacher, E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

public section

namespace Cslib.Logic.PL

open Cslib.Probability.PMF
open scoped BigOperators

/-! ### Uniform i.i.d. index sampling and sampled instances -/

namespace MaxCSP

/-- Uniform distribution over `s`-tuples of constraint indices in `Fin m` (`0 < m`). -/
@[expose] noncomputable def uniformSamplePMF (m : ℕ) (hm : 0 < m) (s : ℕ) :
    _root_.PMF (Fin s → Fin m) :=
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  uniformOfFintype (Fin s → Fin m)

/-! ### Core Hoeffding + union-bound engine for `[0, 1]` constraint evaluators -/

private theorem uniformSample_abs_sub_ge_le {m : ℕ} (hm : 0 < m) (s : ℕ)
    (val : Fin m → ℝ) (hval : ∀ i, val i ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((uniformSamplePMF m hm s).toOuterMeasure
      {ω : Fin s → Fin m |
        δ * (m : ℝ) ≤ |(m : ℝ) / (s : ℝ) * (∑ j : Fin s, val (ω j)) - ∑ i : Fin m, val i|}).toReal ≤
      2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · refine (toOuterMeasure_toReal_le_one _ _).trans ?_
    simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero, mul_one]
    norm_num
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hpi : uniformSamplePMF m hm s = pi (fun _ : Fin s => uniformOfFintype (Fin m)) :=
    (pi_uniformOfFintype (α := fun _ : Fin s => Fin m)).symm
  set tot : ℝ := ∑ i : Fin m, val i
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsR : (0 : ℝ) < s := Nat.cast_pos.mpr hs
  have hcoord_mean :
      ∑ i : Fin m, ((uniformOfFintype (Fin m)) i).toReal * val i = tot / (m : ℝ) := by
    simp only [uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, inv_mul_eq_div, ← Finset.sum_div, tot]
  have hsum_mean :
      (∑ _ : Fin s, ∑ i : Fin m, ((uniformOfFintype (Fin m)) i).toReal * val i) =
        (s : ℝ) * (tot / (m : ℝ)) := by
    simp only [hcoord_mean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hevent :
      {ω : Fin s → Fin m |
        δ * (m : ℝ) ≤ |(m : ℝ) / (s : ℝ) * (∑ j : Fin s, val (ω j)) - tot|} =
      {ω : Fin s → Fin m |
        (s : ℝ) * δ ≤ |(∑ j : Fin s, val (ω j)) -
          ∑ _ : Fin s, ∑ i : Fin m,
            ((uniformOfFintype (Fin m)) i).toReal * val i|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hsum_mean]
    have hdiv_pos : 0 < (m : ℝ) / (s : ℝ) := div_pos hmR hsR
    have hscale : (m : ℝ) / (s : ℝ) * (∑ j : Fin s, val (ω j)) - tot =
        ((m : ℝ) / (s : ℝ)) * ((∑ j : Fin s, val (ω j)) - (s : ℝ) * (tot / (m : ℝ))) := by
      field_simp
    have hlhs : δ * (m : ℝ) = ((m : ℝ) / (s : ℝ)) * ((s : ℝ) * δ) := by
      field_simp
    rw [hscale, abs_mul, abs_of_pos hdiv_pos, hlhs]
    exact mul_le_mul_iff_right₀ hdiv_pos
  rw [hpi, hevent]
  have hconc := pi_sum_abs_sub_mean_ge (fun _ : Fin s => uniformOfFintype (Fin m))
    (fun _ i => val i) (bound := 1) (ε := (s : ℝ) * δ) zero_le_one (fun _ i _ => hval i)
    (by positivity)
  refine hconc.trans_eq ?_
  congr 2
  rw [Fintype.card_fin]
  field_simp

private theorem uniformSample_exists_abs_sub_ge_le {D : Type*} [Fintype D] {n m : ℕ}
    (hm : 0 < m) (s : ℕ) (evalAt : Fin m → (Fin n → D) → ℝ)
    (heval : ∀ i x, evalAt i x ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((uniformSamplePMF m hm s).toOuterMeasure
      {ω : Fin s → Fin m | ∃ x : Fin n → D,
        δ * (m : ℝ) ≤ |(m : ℝ) / (s : ℝ) * (∑ j : Fin s, evalAt (ω j) x) -
          ∑ i : Fin m, evalAt i x|}).toReal ≤
      (Fintype.card D : ℝ) ^ n * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  let B (x : Fin n → D) : Set (Fin s → Fin m) :=
    {ω | δ * (m : ℝ) ≤ |(m : ℝ) / (s : ℝ) * (∑ j : Fin s, evalAt (ω j) x) -
      ∑ i : Fin m, evalAt i x|}
  have heq : {ω : Fin s → Fin m | ∃ x : Fin n → D, ω ∈ B x} =
      ⋃ x ∈ (Finset.univ : Finset (Fin n → D)), B x := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  change ((uniformSamplePMF m hm s).toOuterMeasure {ω | ∃ x, ω ∈ B x}).toReal ≤ _
  rw [heq]
  calc ((uniformSamplePMF m hm s).toOuterMeasure
        (⋃ x ∈ (Finset.univ : Finset (Fin n → D)), B x)).toReal
      ≤ ∑ x ∈ (Finset.univ : Finset (Fin n → D)),
          ((uniformSamplePMF m hm s).toOuterMeasure (B x)).toReal :=
        toOuterMeasure_toReal_biUnion_finset_le _ _ _
    _ ≤ ∑ _x ∈ (Finset.univ : Finset (Fin n → D)),
          (2 * Real.exp (-2 * (s : ℝ) * δ ^ 2)) :=
        Finset.sum_le_sum fun x _ =>
          uniformSample_abs_sub_ge_le hm s (fun i => evalAt i x) (fun i => heval i x) hδ
    _ = (Fintype.card D : ℝ) ^ n * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_pow]
        ring

private theorem abs_scale_sup_sub_le {α : Type*} {c optS optF ε : ℝ} (hc : 0 ≤ c)
    {sScore fScore : α → ℝ}
    (hStar : ∃ xStar, fScore xStar = optF) (hHat : ∃ xHat, sScore xHat = optS)
    (hf_le : ∀ x, fScore x ≤ optF) (hs_le : ∀ x, sScore x ≤ optS)
    (hunif : ∀ x, |c * sScore x - fScore x| ≤ ε) :
    |c * optS - optF| ≤ ε := by
  obtain ⟨xStar, rfl⟩ := hStar
  obtain ⟨xHat, rfl⟩ := hHat
  have h1 := (abs_le.mp (hunif xHat)).2
  have h2 := (abs_le.mp (hunif xStar)).1
  have hopt_le := hf_le xHat
  have hsamp_le := mul_le_mul_of_nonneg_left (hs_le xStar) hc
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- When `0 < η` and `n * log |D| + log (2 / η) ≤ 2 * s * δ ^ 2`, the union-bound factor
`|D| ^ n * 2 * exp (-2 * s * δ ^ 2)` is at most `η`. -/
theorem card_pow_two_mul_exp_le_eta {D : Type*} [Fintype D] [Nonempty D]
    {n s : ℕ} {δ η : ℝ} (hη : 0 < η)
    (hs : (n : ℝ) * Real.log (Fintype.card D) + Real.log (2 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    (Fintype.card D : ℝ) ^ n * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤ η := by
  have hc : (0 : ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have h2η : 0 < 2 / η := div_pos zero_lt_two hη
  have hpow : (Fintype.card D : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log (Fintype.card D)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hc, mul_comm]
  have hdiv : 2 / η = Real.exp (Real.log (2 / η)) := (Real.exp_log h2η).symm
  have hrew : (Fintype.card D : ℝ) ^ n * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) =
      η * ((Fintype.card D : ℝ) ^ n * (2 / η) * Real.exp (-2 * (s : ℝ) * δ ^ 2)) := by
    field_simp
  rw [hrew, hpow, hdiv, ← Real.exp_add, ← Real.exp_add]
  have hexp : Real.exp ((n : ℝ) * Real.log (Fintype.card D) + Real.log (2 / η) +
      (-2 * (s : ℝ) * δ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

/-- Boolean specialization: when `0 < η` and `(n + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`,
`2 ^ (n + 1) * exp (-2 * s * δ ^ 2) ≤ η`. -/
theorem two_pow_succ_mul_exp_le_eta {n s : ℕ} {δ η : ℝ} (hη : 0 < η)
    (hs : (n + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    2 ^ (n + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤ η := by
  have hlog : (n : ℝ) * Real.log (Fintype.card Bool) + Real.log (2 / η) ≤
      2 * (s : ℝ) * δ ^ 2 := by
    have hmul : (2 : ℝ) / η = 2 * (1 / η) := by ring
    rw [Fintype.card_bool, Nat.cast_ofNat, hmul,
      Real.log_mul two_ne_zero (one_div_pos.mpr hη).ne']
    linarith
  have h := card_pow_two_mul_exp_le_eta (D := Bool) hη hlog
  simpa only [Fintype.card_bool, Nat.cast_ofNat, pow_succ, mul_assoc] using h

end MaxCSP

/-! ### Subsampling and `2 δ m` loss for `WeightedMaxCSP` -/

namespace WeightedMaxCSP

variable {Rel V W D : Type*}

/-- Subsampled `WeightedMaxCSP` obtained by selecting `s` constraints indexed by `ω`. -/
@[expose] def sample (F : WeightedMaxCSP Rel V W) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) : WeightedMaxCSP Rel V W :=
  ⟨F.numVars, List.ofFn fun j => F.constraints[ω j]⟩

/-- Uniform distribution over `s`-constraint subsamples of a nonempty `WeightedMaxCSP`. -/
@[expose] noncomputable def samplePMF (F : WeightedMaxCSP Rel V W)
    (hm : 0 < F.constraints.length) (s : ℕ) : _root_.PMF (Fin s → Fin F.constraints.length) :=
  MaxCSP.uniformSamplePMF F.constraints.length hm s

@[simp]
theorem numVars_sample (F : WeightedMaxCSP Rel V W) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) :
    (F.sample ω).numVars = F.numVars :=
  rfl

@[simp]
theorem length_constraints_sample (F : WeightedMaxCSP Rel V W) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) :
    (F.sample ω).constraints.length = s := by
  simp only [sample, List.length_ofFn]

theorem mem_constraints_sample {F : WeightedMaxCSP Rel V W} {s : ℕ}
    {ω : Fin s → Fin F.constraints.length} {c : WeightedConstraint Rel V W}
    (hc : c ∈ (F.sample ω).constraints) : c ∈ F.constraints := by
  simp only [sample, List.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  exact List.getElem_mem _

theorem score_sample_eq_sum [Inhabited D] [AddCommMonoid W] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ W) {s : ℕ} (ω : Fin s → Fin F.constraints.length)
    (x : Fin F.numVars → D) :
    (F.sample ω).score sem x =
      ∑ j : Fin s, F.constraints[ω j].evalWeight sem (MaxCSP.assignment F.numVars x) := by
  simp only [score, evalScore, sample, List.map_ofFn, Function.comp_def, List.sum_ofFn]

theorem score_eq_sum_fin [Inhabited D] [AddCommMonoid W] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ W) (x : Fin F.numVars → D) :
    F.score sem x =
      ∑ i : Fin F.constraints.length,
        F.constraints[i].evalWeight sem (MaxCSP.assignment F.numVars x) := by
  simp only [score, evalScore, ← List.sum_ofFn]
  congr 1
  exact (List.ofFn_getElem_eq_map F.constraints _).symm

/-- **Rescaled sample optimum approximation.** If the rescaled sample score approximates `F.score`
within `ε` uniformly across all assignments, then `(m / s) * (F.sample ω).optimum sem` is within `ε`
of `F.optimum sem`. -/
theorem abs_rescaled_optimum_sub_le [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) {s : ℕ} (ω : Fin s → Fin F.constraints.length) {ε : ℝ}
    (hunif : ∀ x : Fin F.numVars → D,
      |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x - F.score sem x| ≤ ε) :
    |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).optimum sem - F.optimum sem| ≤ ε :=
  MaxCSP.abs_scale_sup_sub_le (by positivity)
    (F.exists_score_eq_optimum sem) ((F.sample ω).exists_score_eq_optimum sem)
    (F.score_le_optimum sem) ((F.sample ω).score_le_optimum sem) hunif

/-- **The `2 * δ * m` optimality loss bound.** Whenever the rescaled sample score approximates
`F.score` within `δ * m` uniformly across all assignments, any assignment `xHat` maximizing the
sampled score `(F.sample ω).score sem` achieves original score at least
`F.optimum sem - 2 * δ * m`. -/
theorem optimum_sub_score_le_two_mul [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) {s : ℕ} (ω : Fin s → Fin F.constraints.length) {δ : ℝ}
    (hunif : ∀ x : Fin F.numVars → D,
      |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x - F.score sem x| ≤
        δ * (F.constraints.length : ℝ))
    {xHat : Fin F.numVars → D}
    (hmax : ∀ x : Fin F.numVars → D,
      (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) :
    F.optimum sem - F.score sem xHat ≤ 2 * δ * (F.constraints.length : ℝ) := by
  have hscale_nonneg : 0 ≤ (F.constraints.length : ℝ) / (s : ℝ) := by positivity
  obtain ⟨xStar, hxStar⟩ := F.exists_score_eq_optimum sem
  have hHat := (abs_le.mp (hunif xHat)).2
  have hStar := (abs_le.mp (hunif xStar)).1
  have hcmp :
      (F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem xStar ≤
        (F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem xHat :=
    mul_le_mul_of_nonneg_left (hmax xStar) hscale_nonneg
  linarith

/-- Multiplicative `(1 - ε)`-approximation corollary when `0 < α`, `0 ≤ δ`, `F.optimum sem ≥ α * m`,
and `2 * δ ≤ ε * α`. -/
theorem one_sub_mul_optimum_le_score [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) {s : ℕ} (ω : Fin s → Fin F.constraints.length) {δ α ε : ℝ}
    (hα_pos : 0 < α) (hopt : α * (F.constraints.length : ℝ) ≤ F.optimum sem)
    (hδ : 0 ≤ δ) (hεδ : 2 * δ ≤ ε * α)
    (hunif : ∀ x : Fin F.numVars → D,
      |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x - F.score sem x| ≤
        δ * (F.constraints.length : ℝ))
    {xHat : Fin F.numVars → D}
    (hmax : ∀ x : Fin F.numVars → D,
      (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) :
    (1 - ε) * F.optimum sem ≤ F.score sem xHat := by
  have hloss := F.optimum_sub_score_le_two_mul sem ω hunif hmax
  have hm_nonneg : 0 ≤ (F.constraints.length : ℝ) := Nat.cast_nonneg _
  have h1 : 2 * δ * (F.constraints.length : ℝ) ≤ ε * (α * (F.constraints.length : ℝ)) := by
    nlinarith
  have hε_nonneg : 0 ≤ ε := by nlinarith
  have h2 : ε * (α * (F.constraints.length : ℝ)) ≤ ε * F.optimum sem :=
    mul_le_mul_of_nonneg_left hopt hε_nonneg
  linarith

/-- **Single-assignment subsampling tail** for `[0, 1]`-weighted `WeightedMaxCSP`. -/
theorem sample_score_abs_sub_ge_le [Inhabited D] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) (hm : 0 < F.constraints.length) (s : ℕ)
    (hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (x : Fin F.numVars → D) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | δ * (F.constraints.length : ℝ) ≤
        |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x -
          F.score sem x|}).toReal ≤
      2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  have hval (i : Fin F.constraints.length) :
      F.constraints[i].evalWeight sem (MaxCSP.assignment F.numVars x) ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [WeightedConstraint.evalWeight]
    split_ifs
    · exact hw _ (List.getElem_mem _)
    · exact ⟨le_rfl, zero_le_one⟩
  simpa only [samplePMF, score_sample_eq_sum, score_eq_sum_fin] using
    MaxCSP.uniformSample_abs_sub_ge_le hm s
      (fun i => F.constraints[i].evalWeight sem (MaxCSP.assignment F.numVars x)) hval hδ

/-- **Uniform subsampling concentration over a general finite domain `D`** (`|D| ^ n * 2 * exp`). -/
theorem exists_sample_score_abs_sub_ge_le [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) (hm : 0 < F.constraints.length) (s : ℕ)
    (hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → D,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x -
            F.score sem x|}).toReal ≤
      (Fintype.card D : ℝ) ^ F.numVars * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  have heval (i : Fin F.constraints.length) (x : Fin F.numVars → D) :
      F.constraints[i].evalWeight sem (MaxCSP.assignment F.numVars x) ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [WeightedConstraint.evalWeight]
    split_ifs
    · exact hw _ (List.getElem_mem _)
    · exact ⟨le_rfl, zero_le_one⟩
  simpa only [samplePMF, score_sample_eq_sum, score_eq_sum_fin] using
    MaxCSP.uniformSample_exists_abs_sub_ge_le hm s
      (fun i x => F.constraints[i].evalWeight sem (MaxCSP.assignment F.numVars x)) heval hδ

/-- **Boolean uniform subsampling concentration (`2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`).** -/
theorem boolean_exists_sample_score_abs_sub_ge_le (sem : Rel → List Bool → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) (hm : 0 < F.constraints.length) (s : ℕ)
    (hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : BitString F.numVars,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x -
            F.score sem x|}).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  refine (F.exists_sample_score_abs_sub_ge_le sem hm s hw hδ).trans_eq ?_
  rw [Fintype.card_bool, Nat.cast_ofNat, pow_succ]
  ring

/-- **Sample-size bound for failure probability `η` over a finite domain `D`:** when `0 < η` and
`n * log |D| + log (2 / η) ≤ 2 * s * δ ^ 2`, the uniform deviation failure probability is at most
`η`. -/
theorem exists_sample_score_abs_sub_ge_le_of_sample_size [Fintype D] [Inhabited D]
    (sem : Rel → List D → Bool) (F : WeightedMaxCSP Rel ℕ ℝ) (hm : 0 < F.constraints.length)
    {s : ℕ} (hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars : ℝ) * Real.log (Fintype.card D) + Real.log (2 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → D,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x -
            F.score sem x|}).toReal ≤ η :=
  (F.exists_sample_score_abs_sub_ge_le sem hm s hw hδ).trans
    (MaxCSP.card_pow_two_mul_exp_le_eta hη hs)

/-- **Boolean sample-size bound for failure probability `η`:** when `0 < η` and
`(n + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`, the uniform deviation failure probability is at
most `η`. -/
theorem boolean_exists_sample_score_abs_sub_ge_le_of_sample_size (sem : Rel → List Bool → Bool)
    (F : WeightedMaxCSP Rel ℕ ℝ) (hm : 0 < F.constraints.length) {s : ℕ}
    (hw : ∀ c ∈ F.constraints, c.weight ∈ Set.Icc (0 : ℝ) 1) {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : BitString F.numVars,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * (F.sample ω).score sem x -
            F.score sem x|}).toReal ≤ η :=
  (F.boolean_exists_sample_score_abs_sub_ge_le sem hm s hw hδ).trans
    (MaxCSP.two_pow_succ_mul_exp_le_eta hη hs)

end WeightedMaxCSP

/-! ### Unweighted `MaxCSPInstance` subsampling, `2 δ m` loss, and existence corollaries -/

namespace MaxCSPInstance

variable {Rel V D : Type*}

/-- Subsampled unweighted `MaxCSPInstance` obtained by selecting `s` constraints indexed by `ω`. -/
@[expose] def sample (F : MaxCSPInstance Rel V) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) : MaxCSPInstance Rel V :=
  ⟨F.numVars, List.ofFn fun j => F.constraints[ω j]⟩

/-- Uniform distribution over `s`-constraint subsamples of a nonempty `MaxCSPInstance`. -/
@[expose] noncomputable def samplePMF (F : MaxCSPInstance Rel V)
    (hm : 0 < F.constraints.length) (s : ℕ) : _root_.PMF (Fin s → Fin F.constraints.length) :=
  MaxCSP.uniformSamplePMF F.constraints.length hm s

@[simp]
theorem numVars_sample (F : MaxCSPInstance Rel V) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) :
    (F.sample ω).numVars = F.numVars :=
  rfl

@[simp]
theorem length_constraints_sample (F : MaxCSPInstance Rel V) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) :
    (F.sample ω).constraints.length = s := by
  simp only [sample, List.length_ofFn]

theorem mem_constraints_sample {F : MaxCSPInstance Rel V} {s : ℕ}
    {ω : Fin s → Fin F.constraints.length} {c : MaxConstraint Rel V}
    (hc : c ∈ (F.sample ω).constraints) : c ∈ F.constraints := by
  simp only [sample, List.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  exact List.getElem_mem _

theorem workSize_sample_le_of_width {k : ℕ} {F : MaxCSPInstance Rel V}
    (hk : ∀ c ∈ F.constraints, c.scope.length ≤ k) {s : ℕ}
    (ω : Fin s → Fin F.constraints.length) :
    (F.sample ω).workSize ≤ (k + 1) * s := by
  have hvars : (F.sample ω).vars.length ≤ k * s := by
    calc (F.sample ω).vars.length
        = ((F.sample ω).constraints.map fun c => c.scope.length).sum := by
          simp only [vars, List.length_flatMap]
      _ ≤ ((F.sample ω).constraints.map fun _ => k).sum :=
          List.sum_le_sum fun c hc => hk c (mem_constraints_sample hc)
      _ = k * s := by
          simp only [List.map_const', List.sum_replicate, length_constraints_sample, smul_eq_mul,
            Nat.mul_comm]
  simp only [workSize, length_constraints_sample]
  nlinarith

private theorem countP_eq_sum_map_boole {α : Type*} (l : List α) (p : α → Bool) :
    (l.countP p : ℝ) = (l.map fun a => if p a then (1 : ℝ) else 0).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]
    cases p a <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_one, Nat.cast_zero] <;> ring

theorem score_sample_eq_sum_boole [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) {s : ℕ} (ω : Fin s → Fin F.constraints.length)
    (x : Fin F.numVars → D) :
    ((F.sample ω).score sem x : ℝ) =
      ∑ j : Fin s,
        if F.constraints[ω j].eval sem (MaxCSP.assignment F.numVars x) then 1 else 0 := by
  simp only [score, evalCount, sample, countP_eq_sum_map_boole, List.map_ofFn, Function.comp_def,
    List.sum_ofFn]

theorem score_eq_sum_boole [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (x : Fin F.numVars → D) :
    (F.score sem x : ℝ) =
      ∑ i : Fin F.constraints.length,
        if F.constraints[i].eval sem (MaxCSP.assignment F.numVars x) then 1 else 0 := by
  rw [score, evalCount, countP_eq_sum_map_boole, ← List.sum_ofFn]
  congr 1
  exact (List.ofFn_getElem_eq_map F.constraints _).symm

/-- **Deterministic rescaled sample optimum bound** for unweighted `MaxCSPInstance`. -/
theorem abs_rescaled_optimum_sub_le [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) {s : ℕ} (ω : Fin s → Fin F.constraints.length) {ε : ℝ}
    (hunif : ∀ x : Fin F.numVars → D,
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
        (F.score sem x : ℝ)| ≤ ε) :
    |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
      (F.optimum sem : ℝ)| ≤ ε := by
  obtain ⟨xStar, hxStar⟩ := F.exists_score_eq_optimum sem
  obtain ⟨xHat, hxHat⟩ := (F.sample ω).exists_score_eq_optimum sem
  exact MaxCSP.abs_scale_sup_sub_le (by positivity)
    ⟨xStar, congrArg Nat.cast hxStar⟩ ⟨xHat, congrArg Nat.cast hxHat⟩
    (fun x => Nat.cast_le.mpr (F.score_le_optimum sem x))
    (fun x => Nat.cast_le.mpr ((F.sample ω).score_le_optimum sem x)) hunif

/-- **The `2 * δ * m` optimality loss bound** for unweighted `MaxCSPInstance`: if the rescaled
sample score approximates `F.score` within `δ * m` on every assignment, then every assignment `xHat`
maximizing `(F.sample ω).score sem` achieves score at least `F.optimum sem - 2 * δ * m`. -/
theorem optimum_sub_score_le_two_mul [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) {s : ℕ} (ω : Fin s → Fin F.constraints.length) {δ : ℝ}
    (hunif : ∀ x : Fin F.numVars → D,
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
        (F.score sem x : ℝ)| ≤ δ * (F.constraints.length : ℝ))
    {xHat : Fin F.numVars → D}
    (hmax : ∀ x : Fin F.numVars → D,
      (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) :
    (F.optimum sem : ℝ) - (F.score sem xHat : ℝ) ≤ 2 * δ * (F.constraints.length : ℝ) := by
  have hscale_nonneg : 0 ≤ (F.constraints.length : ℝ) / (s : ℝ) := by positivity
  obtain ⟨xStar, hxStar⟩ := F.exists_score_eq_optimum sem
  have hHat := (abs_le.mp (hunif xHat)).2
  have hStar := (abs_le.mp (hunif xStar)).1
  have hcmp :
      (F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem xStar : ℝ) ≤
        (F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem xHat : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hmax xStar)) hscale_nonneg
  rw [← hxStar]
  linarith

/-- **Uniform subsampling concentration** for unweighted `MaxCSPInstance` over `D`. -/
theorem exists_sample_score_abs_sub_ge_le [Fintype D] [Inhabited D] (sem : Rel → List D → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → D,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
            (F.score sem x : ℝ)|}).toReal ≤
      (Fintype.card D : ℝ) ^ F.numVars * 2 * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  have heval (i : Fin F.constraints.length) (x : Fin F.numVars → D) :
      (if F.constraints[i].eval sem (MaxCSP.assignment F.numVars x) then (1 : ℝ) else 0) ∈
        Set.Icc (0 : ℝ) 1 := by
    split_ifs <;> simp only [Set.mem_Icc, zero_le_one, le_refl, and_self]
  simpa only [samplePMF, score_sample_eq_sum_boole, score_eq_sum_boole] using
    MaxCSP.uniformSample_exists_abs_sub_ge_le hm s
      (fun i x => if F.constraints[i].eval sem (MaxCSP.assignment F.numVars x) then 1 else 0)
      heval hδ

/-- **Boolean uniform subsampling concentration (`2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`).** -/
theorem boolean_exists_sample_score_abs_sub_ge_le (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : BitString F.numVars,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
            (F.score sem x : ℝ)|}).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  refine (F.exists_sample_score_abs_sub_ge_le sem hm s hδ).trans_eq ?_
  rw [Fintype.card_bool, Nat.cast_ofNat, pow_succ]
  ring

/-- **Boolean subsampling `2 * δ * m` loss tail:** the probability that *some* maximizer `xHat` of
`F.sample ω` loses strictly more than `2 * δ * m` (or that the rescaled sample optimum errs by
strictly more than `δ * m`) is at most `2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`. -/
theorem boolean_sample_loss_gt_le (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | (∃ xHat : BitString F.numVars,
          (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) ∧
            2 * δ * (F.constraints.length : ℝ) < (F.optimum sem : ℝ) - (F.score sem xHat : ℝ)) ∨
        δ * (F.constraints.length : ℝ) <
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
            (F.optimum sem : ℝ)|}).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
  refine (toOuterMeasure_toReal_mono (F.samplePMF hm s) fun ω hω => ?_).trans
    (F.boolean_exists_sample_score_abs_sub_ge_le sem hm s hδ)
  by_contra hgood
  simp only [Set.mem_ofPred_eq, not_exists, not_le] at hgood
  have hunif : ∀ x : BitString F.numVars,
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
        (F.score sem x : ℝ)| ≤ δ * (F.constraints.length : ℝ) :=
    fun x => (hgood x).le
  rcases hω with ⟨xHat, hmax, hgt⟩ | hopt_gt
  · linarith [F.optimum_sub_score_le_two_mul sem ω hunif hmax]
  · linarith [F.abs_rescaled_optimum_sub_le sem ω hunif]

/-- **Complementary success probability (`≥ 1 - 2 ^ (n + 1) * exp (-2 * s * δ ^ 2)`):** with at
least this probability, the rescaled sample optimum is within `δ * m` of `F.optimum sem` and *every*
maximizer of `F.sample ω` achieves score within `2 * δ * m` of `F.optimum sem`. -/
theorem one_sub_le_boolean_sample_good (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) (s : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    1 - 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) →
              (F.optimum sem : ℝ) - (F.score sem xHat : ℝ) ≤ 2 * δ * (F.constraints.length : ℝ)) ∧
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
            (F.optimum sem : ℝ)| ≤ δ * (F.constraints.length : ℝ)}).toReal := by
  set good : Set (Fin s → Fin F.constraints.length) :=
    {ω | (∀ xHat : BitString F.numVars,
        (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) →
          (F.optimum sem : ℝ) - (F.score sem xHat : ℝ) ≤ 2 * δ * (F.constraints.length : ℝ)) ∧
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
        (F.optimum sem : ℝ)| ≤ δ * (F.constraints.length : ℝ)}
  have hsum := toOuterMeasure_toReal_add_compl (F.samplePMF hm s) good
  have hcompl_le : ((F.samplePMF hm s).toOuterMeasure goodᶜ).toReal ≤
      2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) := by
    refine (toOuterMeasure_toReal_mono (F.samplePMF hm s) fun ω hω => ?_).trans
      (F.boolean_sample_loss_gt_le sem hm s hδ)
    simp only [good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hω
    rcases hω with ⟨xHat, hmax, hgt⟩ | hopt
    · exact Or.inl ⟨xHat, hmax, hgt⟩
    · exact Or.inr hopt
  linarith

/-- **Unweighted sample-size bound for failure probability `η` over a finite domain `D`.** -/
theorem exists_sample_score_abs_sub_ge_le_of_sample_size [Fintype D] [Inhabited D]
    (sem : Rel → List D → Bool) (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length)
    {s : ℕ} {δ η : ℝ} (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars : ℝ) * Real.log (Fintype.card D) + Real.log (2 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | ∃ x : Fin F.numVars → D,
        δ * (F.constraints.length : ℝ) ≤
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
            (F.score sem x : ℝ)|}).toReal ≤ η :=
  (F.exists_sample_score_abs_sub_ge_le sem hm s hδ).trans
    (MaxCSP.card_pow_two_mul_exp_le_eta hη hs)

/-- **Boolean `2 * δ * m` loss failure bound `≤ η` under `(n + 1) * log 2 + log (1 / η) ≤ 2 s δ²`.**
-/
theorem boolean_sample_loss_gt_le_of_sample_size (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) {s : ℕ} {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    ((F.samplePMF hm s).toOuterMeasure
      {ω | (∃ xHat : BitString F.numVars,
          (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) ∧
            2 * δ * (F.constraints.length : ℝ) <
              (F.optimum sem : ℝ) - (F.score sem xHat : ℝ)) ∨
        δ * (F.constraints.length : ℝ) <
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
            (F.optimum sem : ℝ)|}).toReal ≤ η :=
  (F.boolean_sample_loss_gt_le sem hm s hδ).trans (MaxCSP.two_pow_succ_mul_exp_le_eta hη hs)

/-- **Boolean `1 - η` success bound under `(n + 1) * log 2 + log (1 / η) ≤ 2 * s * δ ^ 2`.** -/
theorem one_sub_le_boolean_sample_good_of_sample_size (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) {s : ℕ} {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 + Real.log (1 / η) ≤ 2 * (s : ℝ) * δ ^ 2) :
    1 - η ≤
      ((F.samplePMF hm s).toOuterMeasure
        {ω | (∀ xHat : BitString F.numVars,
            (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) →
              (F.optimum sem : ℝ) - (F.score sem xHat : ℝ) ≤
                2 * δ * (F.constraints.length : ℝ)) ∧
          |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
            (F.optimum sem : ℝ)| ≤ δ * (F.constraints.length : ℝ)}).toReal := by
  have h1 := MaxCSP.two_pow_succ_mul_exp_le_eta hη hs
  have h2 := F.one_sub_le_boolean_sample_good sem hm s hδ
  linarith

/-- **Existence of an `s`-constraint uniform approximator** whenever
`(F.numVars + 1) * log 2 < 2 * s * δ ^ 2`
(for example `s = ⌈(n + 1) * log 2 / (2 * δ ^ 2)⌉₊ + 1`). -/
theorem exists_boolean_sample_approx (sem : Rel → List Bool → Bool)
    (F : MaxCSPInstance Rel ℕ) (hm : 0 < F.constraints.length) {s : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hs : (F.numVars + 1 : ℝ) * Real.log 2 < 2 * (s : ℝ) * δ ^ 2) :
    ∃ ω : Fin s → Fin F.constraints.length,
      (∀ x : BitString F.numVars,
        |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
          (F.score sem x : ℝ)| < δ * (F.constraints.length : ℝ)) ∧
      (∀ xHat : BitString F.numVars,
        (∀ x, (F.sample ω).score sem x ≤ (F.sample ω).score sem xHat) →
          (F.optimum sem : ℝ) - (F.score sem xHat : ℝ) ≤ 2 * δ * (F.constraints.length : ℝ)) ∧
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).optimum sem : ℝ) -
        (F.optimum sem : ℝ)| ≤ δ * (F.constraints.length : ℝ) := by
  set bad : Set (Fin s → Fin F.constraints.length) :=
    {ω | ∃ x : BitString F.numVars,
      δ * (F.constraints.length : ℝ) ≤
        |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
          (F.score sem x : ℝ)|}
  have htwo_pow : (2 : ℝ) ^ (F.numVars + 1) = Real.exp ((F.numVars + 1 : ℝ) * Real.log 2) := by
    have hcast : ((F.numVars + 1 : ℕ) : ℝ) = (F.numVars + 1 : ℝ) := by push_cast; rfl
    rw [← hcast, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlt_one : 2 ^ (F.numVars + 1) * Real.exp (-2 * (s : ℝ) * δ ^ 2) < 1 := by
    rw [htwo_pow, ← Real.exp_add, Real.exp_lt_one_iff]
    linarith
  have hbad_le := F.boolean_exists_sample_score_abs_sub_ge_le sem hm s hδ
  have hsum := toOuterMeasure_toReal_add_compl (F.samplePMF hm s) bad
  have hpos : 0 < ((F.samplePMF hm s).toOuterMeasure badᶜ).toReal := by linarith
  obtain ⟨ω, hω, -⟩ := (toOuterMeasure_toReal_pos_iff (F.samplePMF hm s) badᶜ).mp hpos
  simp only [bad, Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, not_le] at hω
  have hunif : ∀ x : BitString F.numVars,
      |(F.constraints.length : ℝ) / (s : ℝ) * ((F.sample ω).score sem x : ℝ) -
        (F.score sem x : ℝ)| ≤ δ * (F.constraints.length : ℝ) :=
    fun x => (hω x).le
  exact ⟨ω, hω, fun xHat hmax => F.optimum_sub_score_le_two_mul sem ω hunif hmax,
    F.abs_rescaled_optimum_sub_le sem ω hunif⟩

end MaxCSPInstance

end Cslib.Logic.PL
