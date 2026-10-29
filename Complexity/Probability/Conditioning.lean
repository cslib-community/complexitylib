/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map

/-!
# Conditioning discrete joint distributions

`conditionalSnd joint a` uses the upstream posterior distribution to recover the second component
after observing `a` in the first. At a zero-probability observation it defaults to the second
marginal. The joint law and all weighted averages are independent of this choice. No finiteness
assumption is needed
for the conditional distribution or its reconstruction law.

## Main definitions

* `Cslib.Probability.PMF.conditionalSnd`: the second component after observing the first.

## Main results

* `Cslib.Probability.PMF.bind_conditionalSnd`: reconstruct the complete joint distribution.
* `Cslib.Probability.PMF.conditionalSnd_bind_pair`: recover a supported conditional kernel.
* `Cslib.Probability.PMF.conditionalSnd_uniform_map`: uniformity on the observed fiber.

## References

Adapted from Probability/Conditioning.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing the upstream PMF operations.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- The first marginal is the sum of the corresponding joint slice. -/
theorem map_fst_apply (joint : PMF (α × β)) (a : α) :
    (joint.map Prod.fst) a = ∑' b, joint (a, b) := by
  classical
  rw [PMF.map_apply, tsum_prod']
  rw [tsum_eq_single a]
  · simp
  · intro x hx
    simp [Ne.symm hx]

/-- Each joint mass is at most the corresponding marginal mass. -/
theorem apply_le_map_fst (joint : PMF (α × β)) (a : α) (b : β) :
    joint (a, b) ≤ (joint.map Prod.fst) a :=
  le_map_apply joint Prod.fst (a, b)

open Classical in
/-- The second component conditioned on the first, defaulting to its marginal at null events. -/
noncomputable def conditionalSnd (joint : PMF (α × β)) (a : α) : PMF β :=
  if ha : a ∈ (joint.bind (fun pair => PMF.pure pair.1)).support then
    (posteriorDist joint (fun pair => PMF.pure pair.1) a ha).map Prod.snd
  else joint.map Prod.snd

/-- At a positive-probability observation, conditional probabilities are normalized joint masses. -/
theorem conditionalSnd_apply (joint : PMF (α × β)) (a : α)
    (ha : a ∈ (joint.map Prod.fst).support) (b : β) :
    conditionalSnd joint a b = joint (a, b) / (joint.map Prod.fst) a := by
  classical
  have hpost : a ∈ (joint.bind (fun pair => PMF.pure pair.1)).support := ha
  simp only [conditionalSnd, hpost, dite_true, PMF.map_apply, tsum_prod',
    posteriorDist_apply, bind_pair_apply, PMF.pure_apply]
  simp [tsum_prod', div_eq_mul_inv]

/-- Multiplying by the marginal recovers the joint mass, also at zero-probability observations. -/
theorem marginal_mul_conditionalSnd (joint : PMF (α × β)) (a : α) (b : β) :
    (joint.map Prod.fst) a * conditionalSnd joint a b = joint (a, b) := by
  by_cases ha : (joint.map Prod.fst) a = 0
  · have hz : joint (a, b) = 0 := le_antisymm (ha ▸ apply_le_map_fst joint a b) bot_le
    simp [ha, hz]
  · rw [conditionalSnd_apply joint a ((PMF.mem_support_iff _ _).mpr ha)]
    rw [mul_comm, ENNReal.div_mul_cancel ha (PMF.apply_ne_top _ _)]

/-- Removing the probability of the observation can only increase the joint outcome's mass. -/
theorem apply_le_conditionalSnd (joint : PMF (α × β)) (a : α) (b : β) :
    joint (a, b) ≤ conditionalSnd joint a b := by
  calc
    joint (a, b) = (joint.map Prod.fst) a * conditionalSnd joint a b :=
      (marginal_mul_conditionalSnd joint a b).symm
    _ ≤ 1 * conditionalSnd joint a b := mul_le_mul' ((joint.map Prod.fst).coe_le_one a) le_rfl
    _ = conditionalSnd joint a b := one_mul _

/-- At an observable first component, the conditional support is exactly the joint slice. -/
theorem mem_support_conditionalSnd_iff (joint : PMF (α × β)) (a : α)
    (ha : a ∈ (joint.map Prod.fst).support) (b : β) :
    b ∈ (conditionalSnd joint a).support ↔ (a, b) ∈ joint.support := by
  have ha0 : (joint.map Prod.fst) a ≠ 0 := ha
  rw [PMF.mem_support_iff, PMF.mem_support_iff, ← marginal_mul_conditionalSnd, mul_ne_zero_iff]
  exact ⟨fun h => ⟨ha0, h⟩, And.right⟩

/-- Sampling the marginal and then the conditional distribution reconstructs the joint law. -/
theorem bind_conditionalSnd (joint : PMF (α × β)) :
    (joint.map Prod.fst).bind (fun a => (conditionalSnd joint a).map (a, ·)) = joint := by
  ext ⟨a, b⟩
  rw [bind_map_prodMk_apply, marginal_mul_conditionalSnd]

/-- Conditioning a joint sampler on a possible first component recovers its conditional kernel. -/
theorem conditionalSnd_bind_pair (p : PMF α) (kernel : α → PMF β)
    (a : α) (ha : a ∈ p.support) :
    conditionalSnd (p.bind (fun a => (kernel a).map (a, ·))) a = kernel a := by
  ext b
  rw [conditionalSnd_apply _ a (by simpa using ha), map_fst_bind_pair, bind_map_prodMk_apply,
    mul_comm, mul_div_assoc, ENNReal.div_self ha (PMF.apply_ne_top _ _), mul_one]

/-- A score can be averaged by first revealing a deterministic observation and then resampling
the input conditionally. The score may depend on both the observation and the hidden input. -/
theorem sum_conditionalSnd_map [Fintype α] [Finite β] (p : PMF α) (f : α → β)
    (score : β → α → ℝ) :
    (∑ x, (p x).toReal * ∑ y,
      (conditionalSnd (p.map (fun a => (f a, a))) (f x) y).toReal * score (f x) y) =
      ∑ x, (p x).toReal * score (f x) x := by
  let := Fintype.ofFinite β
  have h := congrArg (fun joint : PMF (β × α) =>
    ∑ pair, (joint pair).toReal * score pair.1 pair.2)
      (bind_conditionalSnd (p.map (fun a => (f a, a))))
  simpa only [sum_bind_mul, sum_map_mul, PMF.map_comp, Function.comp_def] using h

open Classical in
/-- Conditioning a uniform input on its image gives the uniform distribution on that fiber.
The nonempty assumption restricts this statement to observable images. -/
theorem conditionalSnd_uniform_map [Fintype α] [Nonempty α] (f : α → β) (b : β)
    [Nonempty {a // f a = b}] :
    conditionalSnd ((PMF.uniformOfFintype α).map (fun a => (f a, a))) b =
      (PMF.uniformOfFintype {a // f a = b}).map Subtype.val := by
  classical
  let fiber := {a // f a = b}
  have hsupport : b ∈ (((PMF.uniformOfFintype α).map (fun a => (f a, a))).map
      Prod.fst).support := by
    obtain ⟨a, ha⟩ := ‹Nonempty {a // f a = b}›
    simp only [PMF.map_comp, Function.comp_def]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨a, (by simp [PMF.mem_support_iff]), ha⟩
  have hjoint (a : α) :
      ((PMF.uniformOfFintype α).map (fun x => (f x, x))) (b, a) =
        if f a = b then (Fintype.card α : ℝ≥0∞)⁻¹ else 0 := by
    simp [PMF.map_apply, PMF.uniformOfFintype_apply, and_comm, ite_and, eq_comm]
  have hfiber (a : α) : ((PMF.uniformOfFintype fiber).map Subtype.val) a =
      if f a = b then (Fintype.card fiber : ℝ≥0∞)⁻¹ else 0 := by
    simp only [fiber, PMF.map_apply, PMF.uniformOfFintype_apply]
    erw [tsum_subtype {x | f x = b}
      (fun x => if a = x then (Fintype.card fiber : ℝ≥0∞)⁻¹ else 0)]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, ← ite_and, and_comm]
    simp [fiber, ite_and]
  ext a
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [conditionalSnd_apply _ b hsupport, hjoint]
  change _ = (((PMF.uniformOfFintype fiber).map Subtype.val) a).toReal
  rw [hfiber]
  simp only [PMF.map_comp, Function.comp_def, uniformOfFintype_map_apply,
    Nat.card_eq_fintype_card, ENNReal.toReal_div, ENNReal.toReal_natCast]
  by_cases ha : f a = b
  · have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have hfcard : (Fintype.card fiber : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [ha, ite_true, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    change (Fintype.card α : ℝ)⁻¹ / (Fintype.card fiber / Fintype.card α) = _
    field_simp
  · simp [ha]

end Cslib.Probability.PMF
