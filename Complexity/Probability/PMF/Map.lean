/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind

/-!
# Relabeling discrete distributions

## Main results

* `Cslib.Probability.PMF.map_equiv_apply`: point masses after an equivalence.
* `Cslib.Probability.PMF.map_congr_on_support`: only supported inputs need equal outputs.
* `Cslib.Probability.PMF.map_apply_toReal`: finite fiber sums.
* `Cslib.Probability.PMF.uniformOfFintype_map_apply`: uniform image masses from fiber sizes.
* `Cslib.Probability.PMF.bind_map_prodMk_apply`: point masses of a pairing bind.
* `Cslib.Probability.PMF.map_injective`: injective encodings preserve equality of distributions.

## References

Adapted from Probability/PMF.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, reusing Mathlib's support-sensitive bind congruence.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- A deterministic map preserves at least the mass of each individual preimage. -/
theorem le_map_apply (p : PMF α) (f : α → β) (a : α) : p a ≤ (p.map f) (f a) := by
  classical
  rw [PMF.map_apply]
  simpa using le_tsum (f := fun x => if f a = f x then p x else 0) a

/-- Relabeling a distribution by an equivalence preserves each corresponding point mass. -/
theorem map_equiv_apply (p : PMF α) (e : α ≃ β) (b : β) :
    p.map e b = p (e.symm b) := by
  classical
  simp only [PMF.map_apply, ← e.symm_apply_eq, tsum_ite_eq']

/-- Re-encoding only needs to agree on outcomes which the distribution can produce. -/
theorem map_congr_on_support (p : PMF α) (f g : α → β)
    (h : ∀ a ∈ p.support, f a = g a) : p.map f = p.map g :=
  PMF.bind_congr_on_support p _ _ (fun a ha => congrArg PMF.pure (h a ha))

/-- The mass of a deterministic image is the sum of the masses in its fiber. -/
theorem map_apply_toReal [Fintype α] [DecidableEq β] (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal = ∑ a, if b = f a then (p a).toReal else 0 := by
  change (p.bind (fun a => PMF.pure (f a)) b).toReal = _
  rw [bind_apply_toReal]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : b = f a <;> simp [PMF.pure_apply, h]

/-- The mass of an image of a uniform input is its fiber size divided by the input size. -/
theorem uniformOfFintype_map_apply [Fintype α] [Nonempty α] (f : α → β) (b : β) :
    ((uniformOfFintype α).map f) b =
      (Nat.card {a // f a = b} : ℝ≥0∞) / Fintype.card α := by
  classical
  simp only [PMF.map_apply, uniformOfFintype_apply, tsum_fintype,
    ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
    Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

/-- Evaluating the pairing bind `p.bind fun a => (f a).map (a, ·)` at `pair` gives
`p pair.1 * f pair.1 pair.2`. -/
theorem bind_map_prodMk_apply (p : PMF α) (f : α → PMF β) (pair : α × β) :
    (p.bind (fun a => (f a).map (a, ·))) pair = p pair.1 * f pair.1 pair.2 := by
  simp only [PMF.map, Function.comp_def]
  exact bind_pair_apply p f pair.1 pair.2

/-- Marginalizing over a freshly sampled second component recovers the first distribution. -/
@[simp] theorem map_fst_bind_pair (p : PMF α) (f : α → PMF β) :
    (p.bind (fun a => (f a).map (a, ·))).map Prod.fst = p := by
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  change p.bind (fun a => (f a).map (Function.const β a)) = p
  simp only [PMF.map_const, PMF.bind_pure]

/-- An injective representation of outcomes also embeds their complete probability laws. -/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (PMF.map f) := by
  classical
  intro p q h
  ext a
  simpa only [PMF.map_apply, hf.eq_iff, tsum_ite_eq'] using congrArg (fun law => law (f a)) h

end Cslib.Probability.PMF
