/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Conditioning
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
import Complexity.Probability.PMF.ToReal
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite Shannon entropy

Entropy is measured in bits. Conditional entropy is the joint entropy minus the entropy of the
observed first component. For a joint distribution presented as a marginal and a conditional
kernel, this is exactly the average entropy of the kernel. Both descriptions use ordinary PMFs.

The deterministic chain rule accounts for all the entropy of a source after exposing a function
and then a predicate. This is the entropy accounting used in the OWF-to-PRG construction; an
entropy identity alone makes no claim about computational indistinguishability.

## Main definitions

* `Cslib.Probability.PMF.surprisal`: information content of a supported outcome in bits.
* `Cslib.Probability.PMF.entropy`: finite Shannon entropy.
* `Cslib.Probability.PMF.conditionalEntropy`: remaining entropy after an observation.

## Main results

* `Cslib.Probability.PMF.entropy_bind_pair`, `.entropy_bind_sigma`: joint entropy decompositions.
* `Cslib.Probability.PMF.conditionalEntropy_eq_sum`: average of conditional entropies.
* `Cslib.Probability.PMF.conditionalEntropy_map_fst_ge`: forgetting observations increases entropy.
* `Cslib.Probability.PMF.entropy_chain_rule_deterministic`: deterministic chain rule.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Sections 3.3 and 5.
  Section 5 uses `H(g(W)) + H(P(W) | g(W)) + H(W | g(W), P(W)) = H(W)` to count output bits.

Adapted from Probability/Entropy.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared PMF and conditioning APIs.
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β γ : Type*}

/-- Information content of an outcome, in bits. For finite entropy sums we assign zero at null
outcomes, which are never sampled. Identities requiring positive mass explicitly require support
membership. -/
noncomputable def surprisal (p : PMF α) (a : α) : ℝ := -Real.logb 2 (p a).toReal

/-- Information content is nonnegative, including the chosen value at null outcomes. -/
theorem surprisal_nonneg (p : PMF α) (a : α) : 0 ≤ surprisal p a := by
  apply neg_nonneg.mpr
  exact Real.logb_nonpos (by norm_num) ENNReal.toReal_nonneg (toReal_apply_le_one p a)

/-- A lower bound on the outcome's probability bounds its information content. -/
theorem surprisal_le_of_mass_ge (p : PMF α) (a : α) {bound : ℝ}
    (hmass : (2 : ℝ) ^ (-bound) ≤ (p a).toReal) : surprisal p a ≤ bound := by
  have hpos : 0 < (p a).toReal :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).trans_le hmass
  have hlog : -bound ≤ Real.logb 2 (p a).toReal :=
    (Real.le_logb_iff_rpow_le (by norm_num) hpos).mpr hmass
  simpa only [surprisal, neg_neg] using neg_le_neg hlog

/-- On the support, an upper information bound is exactly a lower probability bound. -/
theorem surprisal_le_iff_mass_ge (p : PMF α) (a : α) (ha : a ∈ p.support) {bound : ℝ} :
    surprisal p a ≤ bound ↔ (2 : ℝ) ^ (-bound) ≤ (p a).toReal := by
  rw [surprisal, neg_le, Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2)
    (ENNReal.toReal_pos ha (PMF.apply_ne_top _ _))]

/-- Shannon entropy of a finite distribution, in bits. Zero masses contribute zero. -/
noncomputable def entropy [Finite α] (p : PMF α) : ℝ :=
  let := Fintype.ofFinite α
  (∑ a, Real.negMulLog (p a).toReal) / Real.log 2

/-- The finite sum formula does not depend on the choice of enumeration. -/
theorem entropy_eq_sum [Fintype α] (p : PMF α) :
    entropy p = (∑ a, Real.negMulLog (p a).toReal) / Real.log 2 := by
  rw [entropy, Subsingleton.elim (Fintype.ofFinite α) ‹Fintype α›]

/-- Entropy is the expected information content `-log₂ p(a)`. -/
theorem entropy_eq_sum_surprisal [Fintype α] (p : PMF α) :
    entropy p = ∑ a, (p a).toReal * surprisal p a := by
  simp only [entropy_eq_sum, Finset.sum_div, Real.negMulLog, surprisal, Real.logb,
    neg_div, neg_mul, mul_neg, mul_div_assoc]

/-- Finite entropy is nonnegative. -/
theorem entropy_nonneg [Finite α] (p : PMF α) : 0 ≤ entropy p := by
  let := Fintype.ofFinite α
  rw [entropy_eq_sum_surprisal]
  exact Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (surprisal_nonneg p a)

/-- A deterministic value carries no entropy. -/
@[simp] theorem entropy_pure [Finite α] (a : α) : entropy (PMF.pure a) = 0 := by
  classical
  simp [entropy, PMF.pure_apply, apply_ite]

/-- A distribution supported on at most one value carries no entropy. -/
theorem entropy_eq_zero_of_subsingleton_support [Finite α] (p : PMF α)
    (h : p.support.Subsingleton) : entropy p = 0 := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hp : p = PMF.pure a := by
    calc
      p = p.bind PMF.pure := (PMF.bind_pure p).symm
      _ = p.bind (fun _ => PMF.pure a) :=
        bind_congr_on_support _ _ _ (fun b hb => congrArg PMF.pure (h hb ha))
      _ = PMF.pure a := PMF.bind_const p _
  simp [hp]

/-- A uniform sample has the logarithm of its cardinality as entropy. -/
@[simp] theorem entropy_uniform [Fintype α] [Nonempty α] :
    entropy (PMF.uniformOfFintype α) = Real.logb 2 (Fintype.card α) := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [entropy_eq_sum, PMF.uniformOfFintype_apply, Real.negMulLog, Real.log_inv,
    Real.logb, hcard]

/-- Uniform sampling maximizes entropy on a fixed finite type. -/
theorem entropy_le_log_card [Fintype α] (p : PMF α) :
    entropy p ≤ Real.logb 2 (Fintype.card α) := by
  let : Nonempty α := ⟨p.support_nonempty.choose⟩
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := fun a => (p a).toReal)
    (fun _ _ => by positivity) (by simp [hcard]) (fun _ _ => ENNReal.toReal_nonneg)
  simp only [smul_eq_mul, ← Finset.mul_sum, sum_toReal, mul_one] at h
  have hsum := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (Fintype.card α))
  simp only [Real.negMulLog, Real.log_inv, mul_neg, neg_mul, neg_neg] at hsum
  simp only [← mul_assoc, mul_inv_cancel₀ hcard, one_mul] at hsum
  simpa only [entropy_eq_sum, Real.negMulLog, neg_mul, Real.logb] using
    div_le_div_of_nonneg_right hsum (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

/-- Entropy of a deterministic observation, averaged over its original source. -/
theorem entropy_map_eq_sum [Fintype α] [Finite β] (p : PMF α) (f : α → β) :
    entropy (p.map f) = ∑ a, (p a).toReal * surprisal (p.map f) (f a) := by
  let := Fintype.ofFinite β
  rw [entropy_eq_sum_surprisal, sum_map_mul]

/-- A deterministic observation cannot increase entropy. -/
theorem entropy_map_le [Finite α] [Finite β] (p : PMF α) (f : α → β) :
    entropy (p.map f) ≤ entropy p := by
  classical
  let := Fintype.ofFinite α
  rw [entropy_map_eq_sum, entropy_eq_sum_surprisal]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : (p a).toReal = 0
  · simp [ha]
  have hmass := ENNReal.toReal_mono (PMF.apply_ne_top _ _) (le_map_apply p f a)
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact neg_le_neg (Real.logb_le_logb_of_le (by norm_num)
    (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm ha)) hmass)

/-- Re-encoding preserves entropy when distinct supported outcomes remain distinct. -/
theorem entropy_map_of_injOn [Finite α] [Finite β] (p : PMF α) {f : α → β}
    (hf : Set.InjOn f p.support) : entropy (p.map f) = entropy p := by
  classical
  let : Nonempty α := ⟨p.support_nonempty.choose⟩
  have hmap : (p.map f).map (Function.invFunOn f p.support) = p := by
    rw [PMF.map_comp]
    exact (map_congr_on_support p _ id (fun a ha => hf.leftInvOn_invFunOn ha)).trans
      (PMF.map_id p)
  exact le_antisymm (entropy_map_le p f)
    (by simpa only [hmap] using entropy_map_le (p.map f) (Function.invFunOn f p.support))

/-- Injective re-encoding preserves entropy. -/
theorem entropy_map_of_injective [Finite α] [Finite β] (p : PMF α) {f : α → β}
    (hf : Function.Injective f) : entropy (p.map f) = entropy p :=
  entropy_map_of_injOn p hf.injOn

/-- Mixing finite distributions cannot lower their average entropy. -/
theorem sum_mul_entropy_le_entropy_bind [Fintype α] [Finite β]
    (p : PMF α) (kernel : α → PMF β) :
    (∑ a, (p a).toReal * entropy (kernel a)) ≤ entropy (p.bind kernel) := by
  let := Fintype.ofFinite β
  simp only [entropy_eq_sum, ← mul_div_assoc, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _
  have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun a => (p a).toReal) (p := fun a => (kernel a b).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) (sum_toReal p) (fun _ _ => ENNReal.toReal_nonneg)
  simpa only [smul_eq_mul, bind_apply_toReal] using h

/-- The joint entropy is the marginal entropy plus the average conditional entropy. -/
theorem entropy_bind_pair [Fintype α] [Finite β] (p : PMF α) (kernel : α → PMF β) :
    entropy (p.bind (fun a => (kernel a).map (a, ·))) =
      entropy p + ∑ a, (p a).toReal * entropy (kernel a) := by
  let := Fintype.ofFinite β
  simp only [entropy_eq_sum, Fintype.sum_prod_type, bind_map_prodMk_apply,
    ENNReal.toReal_mul, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_toReal, one_mul, add_div, Finset.sum_div,
    mul_div_assoc]

/-- Entropy also decomposes when the second sample's alphabet depends on the first. -/
theorem entropy_bind_sigma {β : α → Type*} [Fintype α] [∀ a, Finite (β a)]
    (p : PMF α) (kernel : (a : α) → PMF (β a)) :
    entropy (p.bind (fun a => (kernel a).map (Sigma.mk a))) =
      entropy p + ∑ a, (p a).toReal * entropy (kernel a) := by
  let (a : α) := Fintype.ofFinite (β a)
  simp only [entropy_eq_sum, Fintype.sum_sigma, bind_sigma_apply,
    ENNReal.toReal_mul, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, sum_toReal, one_mul, add_div, Finset.sum_div,
    mul_div_assoc]

/-- Independent sources add their entropies. -/
theorem entropy_prod [Finite α] [Finite β] (p : PMF α) (q : PMF β) :
    entropy (p.bind (fun a => q.map (a, ·))) = entropy p + entropy q := by
  let := Fintype.ofFinite α
  rw [entropy_bind_pair, ← Finset.sum_mul, sum_toReal, one_mul]

/-- Entropy of the second component given the first, in bits. -/
noncomputable def conditionalEntropy [Finite α] [Finite β] (joint : PMF (α × β)) : ℝ :=
  entropy joint - entropy (joint.map Prod.fst)

/-- Conditioning leaves nonnegative entropy. -/
theorem conditionalEntropy_nonneg [Finite α] [Finite β] (joint : PMF (α × β)) :
    0 ≤ conditionalEntropy joint := sub_nonneg.mpr (entropy_map_le joint Prod.fst)

/-- A constant observation reveals nothing about the sampled value. -/
@[simp] theorem conditionalEntropy_map_const [Finite α] [Finite β] (p : PMF β) (a : α) :
    conditionalEntropy (p.map (a, ·)) = entropy p := by
  rw [conditionalEntropy, entropy_map_of_injective p (Prod.mk_right_injective a), PMF.map_comp]
  change entropy p - entropy (p.map (Function.const β a)) = entropy p
  rw [PMF.map_const, entropy_pure, sub_zero]

/-- The difference-of-entropies definition equals the usual average of conditional entropies. -/
theorem conditionalEntropy_bind_pair [Fintype α] [Finite β]
    (p : PMF α) (kernel : α → PMF β) :
    conditionalEntropy (p.bind (fun a => (kernel a).map (a, ·))) =
      ∑ a, (p a).toReal * entropy (kernel a) := by
  simp [conditionalEntropy, entropy_bind_pair]

/-- When a branch index is public, its remaining conditional entropy is the average over
branches. The observed alphabet may depend on the index, as with variable-length hashes. -/
theorem conditionalEntropy_bind_sigma {β : α → Type*}
    [Fintype α] [∀ a, Finite (β a)] [Finite γ]
    (p : PMF α) (kernel : (a : α) → PMF (β a × γ)) :
    conditionalEntropy (p.bind (fun a => (kernel a).map
      (fun pair => ((⟨a, pair.1⟩ : Sigma β), pair.2)))) =
        ∑ a, (p a).toReal * conditionalEntropy (kernel a) := by
  let joint := p.bind (fun a => (kernel a).map (Sigma.mk a))
  have h := entropy_map_of_injective joint (Equiv.sigmaProdDistrib β γ).symm.injective
  simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def,
    Equiv.sigmaProdDistrib_symm_apply, entropy_bind_sigma] at h
  simp only [conditionalEntropy, PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [h]
  have hmarginal := entropy_bind_sigma p (fun a => (kernel a).map Prod.fst)
  simp only [PMF.map_comp, Function.comp_def] at hmarginal
  rw [hmarginal]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- For any joint law, conditional entropy averages the normalized conditional distributions. -/
theorem conditionalEntropy_eq_sum [Fintype α] [Finite β] (joint : PMF (α × β)) :
    conditionalEntropy joint =
      ∑ a, ((joint.map Prod.fst) a).toReal * entropy (conditionalSnd joint a) := by
  simpa only [bind_conditionalSnd] using
    conditionalEntropy_bind_pair (joint.map Prod.fst) (conditionalSnd joint)

/-- Observing a function of the input leaves at least the average entropy of the output kernel.
The observation may merge inputs, including inputs whose conditional laws differ. -/
theorem conditionalEntropy_observe_ge [Fintype α] [Finite β] [Finite γ]
    (p : PMF α) (kernel : α → PMF β) (observe : α → γ) :
    (∑ a, (p a).toReal * entropy (kernel a)) ≤
      conditionalEntropy (p.bind (fun a => (kernel a).map (observe a, ·))) := by
  let := Fintype.ofFinite γ
  let conditional := conditionalSnd (p.map (fun a => (observe a, a)))
  have hreplay : (p.map observe).bind (fun c => ((conditional c).bind kernel).map (c, ·)) =
      p.bind (fun a => (kernel a).map (observe a, ·)) := by
    have h := congrArg (fun joint : PMF (γ × α) =>
      joint.bind (fun pair => (kernel pair.2).map (pair.1, ·)))
        (bind_conditionalSnd (p.map (fun a => (observe a, a))))
    simpa only [PMF.map_comp, Function.comp_def, PMF.map_bind, PMF.bind_bind, PMF.bind_map]
      using h
  calc
    _ = ∑ c, ((p.map observe) c).toReal *
        ∑ a, (conditional c a).toReal * entropy (kernel a) := by
      rw [sum_map_mul]
      exact (sum_conditionalSnd_map p observe (fun _ a => entropy (kernel a))).symm
    _ ≤ ∑ c, ((p.map observe) c).toReal * entropy ((conditional c).bind kernel) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left
        (sum_mul_entropy_le_entropy_bind (conditional c) kernel) ENNReal.toReal_nonneg)
    _ = _ := by rw [← hreplay, conditionalEntropy_bind_pair]

/-- Replacing the observation by a function of it can only increase conditional entropy. -/
theorem conditionalEntropy_map_fst_ge [Finite α] [Finite β] [Finite γ]
    (joint : PMF (α × β)) (observe : α → γ) :
    conditionalEntropy joint ≤
      conditionalEntropy (joint.map (fun pair => (observe pair.1, pair.2))) := by
  let := Fintype.ofFinite α
  have h := conditionalEntropy_observe_ge (joint.map Prod.fst) (conditionalSnd joint) observe
  have hlaw := congrArg (PMF.map (fun pair : α × β => (observe pair.1, pair.2)))
    (bind_conditionalSnd joint)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at hlaw
  simpa only [hlaw, ← conditionalEntropy_eq_sum] using h

/-- Conditional entropy is the expected information content of the hidden value after its
observation. Null observations are automatically weighted by zero. -/
theorem conditionalEntropy_eq_sum_surprisal [Fintype α] [Fintype β]
    (joint : PMF (α × β)) :
    conditionalEntropy joint =
      ∑ pair, (joint pair).toReal * surprisal (conditionalSnd joint pair.1) pair.2 := by
  rw [conditionalEntropy_eq_sum, Fintype.sum_prod_type]
  simp only [entropy_eq_sum_surprisal, Finset.mul_sum, ← mul_assoc,
    ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]

/-- Side information leaves at most the logarithm of the unobserved alphabet's size. -/
theorem conditionalEntropy_le_log_card [Finite α] [Fintype β] (joint : PMF (α × β)) :
    conditionalEntropy joint ≤ Real.logb 2 (Fintype.card β) := by
  let := Fintype.ofFinite α
  rw [conditionalEntropy_eq_sum]
  exact sum_mul_le _ _ _ (fun _ => entropy_le_log_card _)

/-- A bit has at most one bit of conditional entropy. -/
theorem conditionalEntropy_bool_le_one [Finite α] (joint : PMF (α × Bool)) :
    conditionalEntropy joint ≤ 1 := by
  simpa using conditionalEntropy_le_log_card joint

/-- If an observation determines a value except on bad observations, its remaining entropy is
at most the bad probability times the logarithm of the value's alphabet size. -/
theorem conditionalEntropy_map_le_of_determined [Fintype α] [Finite β] [Fintype γ]
    (p : PMF α) (observe : α → β) (value : α → γ) (bad : β → Prop) [DecidablePred bad]
    (hdetermined : ∀ x y, ¬bad (observe x) → observe x = observe y → value x = value y) :
    conditionalEntropy (p.map (fun x => (observe x, value x))) ≤
      ∑ x, (p x).toReal * (if bad (observe x) then Real.logb 2 (Fintype.card γ) else 0) := by
  classical
  let := Fintype.ofFinite β
  rw [← sum_map_mul p observe (fun b => if bad b then Real.logb 2 (Fintype.card γ) else 0),
    conditionalEntropy_eq_sum]
  apply Finset.sum_le_sum
  intro b _
  let joint := p.map (fun x => (observe x, value x))
  have hmarginal : joint.map Prod.fst = p.map observe := by
    simp only [joint, PMF.map_comp, Function.comp_def]
  change ((joint.map Prod.fst) b).toReal * entropy (conditionalSnd joint b) ≤ _
  rw [← hmarginal]
  by_cases hb : b ∈ (joint.map Prod.fst).support
  · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    by_cases hbad : bad b
    · simpa [hbad] using entropy_le_log_card (conditionalSnd joint b)
    · suffices hzero : entropy (conditionalSnd joint b) = 0 by simp [hbad, hzero]
      apply entropy_eq_zero_of_subsingleton_support
      intro z hz w hw
      obtain ⟨x, _, hx⟩ := (PMF.mem_support_map_iff _ _ _).mp
        ((mem_support_conditionalSnd_iff joint b hb z).mp hz)
      obtain ⟨y, _, hy⟩ := (PMF.mem_support_map_iff _ _ _).mp
        ((mem_support_conditionalSnd_iff joint b hb w).mp hw)
      rcases Prod.mk.inj hx with ⟨hxb, hxz⟩
      rcases Prod.mk.inj hy with ⟨hyb, hyw⟩
      exact hxz.symm.trans ((hdetermined x y (hxb ▸ hbad) (hxb.trans hyb.symm)).trans hyw)
  · have hz := (PMF.apply_eq_zero_iff _ _).mpr hb
    simp [hz]

open Classical in
/-- Entropy can remain only when the observation has more than one possible preimage. -/
theorem conditionalEntropy_map_le_collision [Fintype α] [Finite β] [Fintype γ]
    (p : PMF α) (observe : α → β) (value : α → γ) :
    conditionalEntropy (p.map (fun x => (observe x, value x))) ≤
      ∑ x, (p x).toReal *
        (if ∃ y, y ≠ x ∧ observe y = observe x then Real.logb 2 (Fintype.card γ) else 0) := by
  let bad (b : β) := ¬Set.Subsingleton {x | observe x = b}
  have hbad (x : α) : bad (observe x) ↔ ∃ y, y ≠ x ∧ observe y = observe x := by
    simpa only [bad, Set.not_subsingleton_iff, Set.mem_ofPred_eq, and_comm] using
      Set.nontrivial_iff_exists_ne (show x ∈ {y | observe y = observe x} from rfl)
  have h := conditionalEntropy_map_le_of_determined p observe value bad
    (fun x y hgood hxy => congrArg value ((not_not.mp hgood) rfl hxy.symm))
  simpa only [hbad] using h

/-- Exposing a function, then another observation, accounts for all the source entropy. -/
theorem entropy_chain_rule_deterministic [Finite α] [Finite β] [Finite γ]
    (p : PMF α) (f : α → β) (g : α → γ) :
    entropy (p.map f) + conditionalEntropy (p.map (fun a => (f a, g a))) +
      conditionalEntropy (p.map (fun a => ((f a, g a), a))) = entropy p := by
  have h := entropy_map_of_injective p (f := fun a => ((f a, g a), a))
    (fun a b hab => congrArg Prod.snd hab)
  simp only [conditionalEntropy, PMF.map_comp, Function.comp_def, h]
  ring

end Cslib.Probability.PMF
