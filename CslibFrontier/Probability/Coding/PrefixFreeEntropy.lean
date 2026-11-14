/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.Entropy
public import Mathlib.InformationTheory.Coding.PrefixFree
import CslibFrontier.Probability.Divergence
import CslibFrontier.Probability.MinEntropy
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Map
import Mathlib.InformationTheory.Coding.Kraft

/-!
# Kraft–Gibbs Compression Bounds for Shannon Entropy

This module connects Mathlib's `InformationTheory.IsPrefixFree` and Kraft inequality
(`Mathlib/InformationTheory/Coding/Kraft.lean`) to finite-distribution Shannon entropy and
conditional entropy (`CslibFrontier/Probability/Entropy.lean`,
`CslibFrontier/Probability/Divergence.lean`). Deterministic prefix-free concatenation combinators
and
basic binary codes (`finIdxBits`, `eliasGamma`) live in
`CslibFrontier/Foundations/Data/BitString/List/PrefixFree.lean`.

## Main results

* `Cslib.Probability.Coding.entropy_le_expected_length_of_isPrefixFree`: for any finite `p : PMF α`
  and prefix-free encoding `enc` injective on `p.support`, `entropy p` is at most the expected
  codeword length under `p` ([CoverThomas2006], Theorem 5.3.1).
* `Cslib.Probability.Coding.conditionalEntropy_le_expected_length_of_isPrefixFree`: fiberwise
  Kraft–Gibbs lower bound for `conditionalEntropy joint`.
* `Cslib.Probability.Coding.conditionalEntropy_map_le_expected_length_of_isPrefixFree`: transcript
  compression form bounding `H(target(ω) | obs(ω))` by expected message length `E[|msg(ω)|]`.
* `Cslib.Probability.Coding.logb_prob_add_logb_card_le_conditionalEntropy`: lower bound on
  conditional entropy `H(target | obs)` conditioned on an event `W` when the unconditioned joint
  distribution on `(obs, target)` has point masses bounded by `1 / |ObsT × TgtT|`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], Section 5.2 and
  Theorem 5.3.1.
* [L. G. Kraft, *A Device for Quantizing, Grouping, and Coding Amplitude-Modulated
  Pulses*][Kraft1949].
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.Probability.Coding

open InformationTheory Cslib.Probability.PMF

/-- **Kraft–Gibbs source coding lower bound** ([CoverThomas2006], Theorem 5.3.1): if `enc` is
injective on `p.support` and its image on `p.support` is prefix-free, then `entropy p` is at most
the expected codeword length under `p`. -/
theorem entropy_le_expected_length_of_isPrefixFree {α : Type*} [Fintype α]
    (p : PMF α) (enc : α → List Bool)
    (hinj : Set.InjOn enc p.support)
    (hpf : IsPrefixFree (enc '' p.support)) :
    entropy p ≤ ∑ a, (p a).toReal * ((enc a).length : ℝ) := by
  classical
  let s : Finset α := Finset.univ.filter fun a => a ∈ p.support
  have hs_mem (a : α) : a ∈ s ↔ a ∈ p.support := by simp [s]
  have hs_coe : (s : Set α) = p.support := Set.ext hs_mem
  obtain ⟨a₀, ha₀⟩ := p.support_nonempty
  have hs_ne : s.Nonempty := ⟨a₀, (hs_mem a₀).mpr ha₀⟩
  let S : Finset (List Bool) := s.image enc
  have hS_pf : IsPrefixFree (S : Set (List Bool)) := by
    simpa only [S, Finset.coe_image, hs_coe] using hpf
  have hkraft_img := hS_pf.finsetSum_one_div_card_pow_length_le_one
  simp only [Fintype.card_bool, Nat.cast_ofNat, one_div] at hkraft_img
  have hinj_s : Set.InjOn enc (s : Set α) := hs_coe.symm ▸ hinj
  have hsum_eq : ∑ w ∈ S, (2⁻¹ : ℝ) ^ w.length = ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length :=
    Finset.sum_image hinj_s
  set Z : ℝ := ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length
  have hZ_le : Z ≤ 1 := hsum_eq ▸ hkraft_img
  have hZ_pos : 0 < Z :=
    Finset.sum_pos (fun a _ => by positivity) hs_ne
  let f : α → ℝ≥0∞ := fun a =>
    if a ∈ s then ENNReal.ofReal ((2⁻¹ : ℝ) ^ (enc a).length / Z) else 0
  have hf_sum : ∑ a, f a = 1 := by
    have hsum_real : ∑ a ∈ s, (2⁻¹ : ℝ) ^ (enc a).length / Z = 1 := by
      rw [← Finset.sum_div, div_self hZ_pos.ne']
    simp only [f, Finset.sum_ite_mem, Finset.univ_inter]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity), hsum_real, ENNReal.ofReal_one]
  let q : PMF α := PMF.ofFintype f hf_sum
  have hq_toReal (a : α) (ha : a ∈ p.support) :
      (q a).toReal = (2⁻¹ : ℝ) ^ (enc a).length / Z := by
    have has : a ∈ s := (hs_mem a).mpr ha
    change (f a).toReal = _
    simp only [f, ite_eq_left has]
    exact ENNReal.toReal_ofReal (by positivity)
  have hmass_ge (a : α) (ha : a ∈ p.support) :
      (2 : ℝ) ^ (-((enc a).length : ℝ)) ≤ (q a).toReal := by
    rw [hq_toReal a ha, Real.rpow_neg (by norm_num), Real.rpow_natCast, ← inv_pow]
    exact le_div_self (by positivity) hZ_pos hZ_le
  have hsupp : p.support ⊆ q.support := by
    intro a ha
    have hpos : 0 < (q a).toReal :=
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).trans_le (hmass_ge a ha)
    exact (PMF.mem_support_iff q a).mpr fun h0 => by simp [h0] at hpos
  refine (entropy_le_sum_mul_surprisal hsupp).trans ?_
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a ∈ p.support
  · exact mul_le_mul_of_nonneg_left (surprisal_le_of_mass_ge q a (hmass_ge a ha))
      ENNReal.toReal_nonneg
  · have hp0 : (p a).toReal = 0 := by simp [(PMF.apply_eq_zero_iff p a).mpr ha]
    simp [hp0]

/-- **Conditional Kraft–Gibbs compression bound**: if for each observable `obs`, `enc obs` is
injective on `(conditionalSnd joint obs).support` with prefix-free image, then
`conditionalEntropy joint` is at most the expected codeword length under `joint`. -/
theorem conditionalEntropy_le_expected_length_of_isPrefixFree {Obs α : Type*}
    [Fintype Obs] [Fintype α]
    (joint : PMF (Obs × α)) (enc : Obs → α → List Bool)
    (hinj : ∀ obs ∈ (joint.map Prod.fst).support,
      Set.InjOn (enc obs) (conditionalSnd joint obs).support)
    (hpf : ∀ obs ∈ (joint.map Prod.fst).support,
      IsPrefixFree (enc obs '' (conditionalSnd joint obs).support)) :
    conditionalEntropy joint ≤ ∑ oa, (joint oa).toReal * ((enc oa.1 oa.2).length : ℝ) := by
  rw [conditionalEntropy_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_le_sum fun obs _ => ?_
  by_cases hobs : obs ∈ (joint.map Prod.fst).support
  · have hbound := entropy_le_expected_length_of_isPrefixFree (conditionalSnd joint obs)
      (enc obs) (hinj obs hobs) (hpf obs hobs)
    calc ((joint.map Prod.fst) obs).toReal * entropy (conditionalSnd joint obs)
        ≤ ((joint.map Prod.fst) obs).toReal *
            ∑ a, (conditionalSnd joint obs a).toReal * ((enc obs a).length : ℝ) :=
          mul_le_mul_of_nonneg_left hbound ENNReal.toReal_nonneg
      _ = ∑ a, (joint (obs, a)).toReal * ((enc obs a).length : ℝ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← mul_assoc, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
  · have hm0 : (joint.map Prod.fst) obs = 0 := (PMF.apply_eq_zero_iff _ _).mpr hobs
    have hj0 : ∀ a, joint (obs, a) = 0 := fun a =>
      le_antisymm (hm0 ▸ apply_le_map_fst joint obs a) bot_le
    simp [hm0, hj0]

/-- **Communication transcript compression bound**: if a message `msg ω` sent over an outcome space
`p : PMF Ω` is prefix-free on each observation fiber `{ω ∈ p.support | obs ω = o}` and uniquely
determines `target ω` given `obs ω` on `p.support`, then `H(target(ω) | obs(ω)) ≤ E[|msg(ω)|]`. -/
theorem conditionalEntropy_map_le_expected_length_of_isPrefixFree {Ω Obs α : Type*}
    [Fintype Ω] [Finite Obs] [Finite α]
    (p : PMF Ω) (obs : Ω → Obs) (target : Ω → α) (msg : Ω → List Bool)
    (hpf : ∀ o : Obs, IsPrefixFree (msg '' {ω ∈ p.support | obs ω = o}))
    (hdec : ∀ ω₁ ∈ p.support, ∀ ω₂ ∈ p.support,
      obs ω₁ = obs ω₂ → msg ω₁ = msg ω₂ → target ω₁ = target ω₂) :
    conditionalEntropy (p.map fun ω => (obs ω, target ω)) ≤
      ∑ ω, (p ω).toReal * ((msg ω).length : ℝ) := by
  classical
  let := Fintype.ofFinite Obs
  let := Fintype.ofFinite α
  let W : Finset (List Bool) := Finset.univ.image msg
  let cw : Ω → {w // w ∈ W} := fun ω => ⟨msg ω, Finset.mem_image_of_mem msg (Finset.mem_univ ω)⟩
  let joint_cw : PMF (Obs × {w // w ∈ W}) := p.map fun ω => (obs ω, cw ω)
  let joint_tgt : PMF (Obs × α) := p.map fun ω => (obs ω, target ω)
  obtain ⟨ω_def, _⟩ := p.support_nonempty
  let dec : Obs × {w // w ∈ W} → Obs × α := fun oc =>
    if h : ∃ ω ∈ p.support, obs ω = oc.1 ∧ cw ω = oc.2 then
      (oc.1, target (Classical.choose h))
    else
      (oc.1, target ω_def)
  have hmap_dec : joint_cw.map dec = joint_tgt := by
    rw [PMF.map_comp]
    refine Cslib.Probability.PMF.map_congr_on_support p _ _ fun ω hω => ?_
    have hex : ∃ ω' ∈ p.support, obs ω' = obs ω ∧ cw ω' = cw ω := ⟨ω, hω, rfl, rfl⟩
    obtain ⟨hω', hobs', hcw'⟩ := Classical.choose_spec hex
    have hmsg' : msg (Classical.choose hex) = msg ω := congrArg Subtype.val hcw'
    simp only [Function.comp_apply, dec, dite_eq_left hex]
    exact Prod.ext rfl (hdec (Classical.choose hex) hω' ω hω hobs' hmsg')
  have hent_le : conditionalEntropy joint_tgt ≤ conditionalEntropy joint_cw := by
    have hm_fst : joint_tgt.map Prod.fst = joint_cw.map Prod.fst := by
      simp only [joint_tgt, joint_cw, PMF.map_comp, Function.comp_def]
    rw [conditionalEntropy, conditionalEntropy, hm_fst, ← hmap_dec]
    exact sub_le_sub_right (entropy_map_le joint_cw dec) _
  have hcw_pf : ∀ o ∈ (joint_cw.map Prod.fst).support,
      IsPrefixFree (Subtype.val '' (conditionalSnd joint_cw o).support) := by
    intro o ho
    refine (hpf o).anti ?_
    rintro _ ⟨c, hc, rfl⟩
    have hoc : (o, c) ∈ joint_cw.support :=
      (mem_support_conditionalSnd_iff joint_cw o ho c).mp hc
    obtain ⟨ω, hω, hpair⟩ := (PMF.mem_support_map_iff _ _ _).mp hoc
    rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
    exact ⟨ω, ⟨hω, rfl⟩, rfl⟩
  have hcw_bound := conditionalEntropy_le_expected_length_of_isPrefixFree joint_cw
    (fun _ c => c.val) (fun _ _ => Subtype.val_injective.injOn) hcw_pf
  have hexp_eq : ∑ oc, (joint_cw oc).toReal * ((oc.2.val).length : ℝ) =
      ∑ ω, (p ω).toReal * ((msg ω).length : ℝ) :=
    sum_map_mul p (fun ω => (obs ω, cw ω)) (fun oc => ((oc.2.val).length : ℝ))
  exact hent_le.trans (hcw_bound.trans_eq hexp_eq)

open Classical in
/-- Lower bound on conditional entropy under an event `W` of conditional probability
`(μ.map W) true`, when the prior joint distribution on `(obs, target)` has point masses
bounded by `1 / |ObsT × TgtT|`. -/
theorem logb_prob_add_logb_card_le_conditionalEntropy {Ω ObsT TgtT : Type*}
    [Finite Ω] [Fintype ObsT] [Fintype TgtT] [Nonempty ObsT] [Nonempty TgtT]
    (μ : PMF Ω) (W : Ω → Bool) (obs : Ω → ObsT) (target : Ω → TgtT) (hW0 : (μ.map W) true ≠ 0)
    (hmass : ∀ ot : ObsT × TgtT,
      ((μ.map fun ω => (obs ω, target ω)) ot).toReal ≤ (Fintype.card (ObsT × TgtT) : ℝ)⁻¹) :
    let p := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
    Real.logb 2 (((μ.map W) true).toReal) + Real.logb 2 (Fintype.card TgtT) ≤
      PMF.conditionalEntropy (p.map fun ω => (obs ω, target ω)) := by
  let _ := Fintype.ofFinite Ω
  dsimp only
  have hW_mem : true ∈ ((μ.map fun ω => (W ω, ω)).map Prod.fst).support := by
    rw [_root_.PMF.map_comp]; exact (_root_.PMF.mem_support_iff _ _).mpr hW0
  set p : PMF Ω := PMF.conditionalSnd (μ.map fun ω => (W ω, ω)) true
  set joint_ot : PMF (ObsT × TgtT) := p.map fun ω => (obs ω, target ω)
  set q : PMF (ObsT × TgtT) := μ.map fun ω => (obs ω, target ω)
  set pW_real : ℝ := ((μ.map W) true).toReal
  have hpW_pos : 0 < pW_real := ENNReal.toReal_pos hW0 (PMF.apply_ne_top (μ.map W) true)
  have hp_le (ω : Ω) : (p ω).toReal ≤ pW_real⁻¹ * (μ ω).toReal := by
    have hle_enn : p ω ≤ ((μ.map W) true)⁻¹ * μ ω := by
      rw [PMF.conditionalSnd_apply _ _ hW_mem]
      have hmap_le : (μ.map fun ω' => (W ω', ω')) (true, ω) ≤ μ ω := by
        rw [_root_.PMF.map_apply, tsum_fintype]
        refine (Finset.sum_le_sum (g := fun x => if x = ω then μ x else 0) fun x _ => ?_).trans_eq
          (by simp)
        split_ifs with h₁ h₂
        · rfl
        · exact (h₂ (Prod.mk.inj h₁).2.symm).elim
        · exact zero_le
        · rfl
      have hfst : (μ.map fun ω' => (W ω', ω')).map Prod.fst = μ.map W := by
        rw [_root_.PMF.map_comp]; rfl
      rw [hfst, div_eq_mul_inv, mul_comm]; exact mul_le_mul_right hmap_le _
    have htop : ((μ.map W) true)⁻¹ * μ ω ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hW0) (PMF.apply_ne_top μ ω)
    exact (ENNReal.toReal_mono htop hle_enn).trans_eq
      (by rw [ENNReal.toReal_mul, ENNReal.toReal_inv])
  have hj_le (ot : ObsT × TgtT) : (joint_ot ot).toReal ≤ pW_real⁻¹ * (q ot).toReal := by
    dsimp only [joint_ot, q]; rw [PMF.map_apply_toReal p, PMF.map_apply_toReal μ, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => by split_ifs <;> [exact hp_le ω; simp]
  have hcObs : (0 : ℝ) < (Fintype.card ObsT : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcTgt : (0 : ℝ) < (Fintype.card TgtT : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hcard_ot : (Fintype.card ObsT : ℝ) * (Fintype.card TgtT : ℝ) =
      (Fintype.card (ObsT × TgtT) : ℝ) := by exact_mod_cast (Fintype.card_prod ObsT TgtT).symm
  have hmin : Real.logb 2 (pW_real * (Fintype.card ObsT : ℝ) * (Fintype.card TgtT : ℝ)) ≤
      PMF.entropy joint_ot := by
    refine le_trans ?_ (PMF.minEntropy_le_entropy joint_ot)
    rw [PMF.le_minEntropy_iff joint_ot]; intro ot
    rw [Real.rpow_neg (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity),
      mul_assoc pW_real, hcard_ot, mul_inv]
    exact (hj_le ot).trans (mul_le_mul_of_nonneg_left (hmass ot) (inv_nonneg.mpr hpW_pos.le))
  have hfst_le : PMF.entropy (joint_ot.map Prod.fst) ≤ Real.logb 2 (Fintype.card ObsT) :=
    PMF.entropy_le_log_card _
  rw [Real.logb_mul (mul_pos hpW_pos hcObs).ne' hcTgt.ne',
    Real.logb_mul hpW_pos.ne' hcObs.ne'] at hmin
  rw [PMF.conditionalEntropy]; linarith

end Cslib.Probability.Coding
