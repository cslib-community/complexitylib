/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF

/-!
# Comparing two-stage experiments at one outcome

These lemmas compare the probabilities that two-stage experiments `μ.bind f` give one outcome `b`,
using facts about the continuations alone. Pointwise sum identities between continuations carry
over to the experiments: a constant offset with `bind_apply_add_of_forall`, and an exchange of two
pairs on the support with `bind_apply_add_eq_on_support`. Continuations that agree up to `ε` away
from one exceptional first-stage result differ by at most `ε` plus that result's probability
(`bind_apply_le_add_of_ne`). Stateful experiments whose first stages agree on good states, and
whose continuations agree on good states and keep bad states bad, give good outcomes equal
probability (`bind_apply_eq_of_good`).

The one-sided bounds, where the continuations need only be compared on the support, are in
`CslibFrontier.Probability.PMF.Bind`.

## Main results

* `Cslib.Probability.PMF.bind_apply_add_of_forall`,
  `Cslib.Probability.PMF.bind_apply_add_eq_on_support`: sum identities between continuations
  carry over to the experiments.
* `Cslib.Probability.PMF.bind_apply_le_add_of_ne`: continuations close away from one first-stage
  result.
* `Cslib.Probability.PMF.bind_apply_eq_of_good`: stateful experiments that agree until a bad
  state.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

-- Moved from `CslibFrontier/Crypto/Primitives/PRG/NextBit.lean`, where it was private.
/-- If every second stage satisfies `f x b + g x b = h x b + c`, so does the whole experiment. -/
theorem bind_apply_add_of_forall {α β : Type*} (μ : PMF α) {f g h : α → PMF β} {b : β}
    {c : ℝ≥0∞} (hfg : ∀ x, f x b + g x b = h x b + c) :
    μ.bind f b + μ.bind g b = μ.bind h b + c := by
  simp only [PMF.bind_apply]
  rw [← tsum_add]
  simp_rw [← mul_add, hfg, mul_add]
  rw [tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

-- Moved from `CslibFrontier/Crypto/Computational/Encryption/CCA.lean`, where it was
-- `Cslib.Crypto.Encryption.bind_apply_add_eq_of_support`.
/-- If two pairs of continuations satisfy `f₁ a b + g₂ a b = f₂ a b + g₁ a b` on the support of
`p`, then `(p.bind f₁) b + (p.bind g₂) b = (p.bind f₂) b + (p.bind g₁) b`. -/
theorem bind_apply_add_eq_on_support {α β : Type*} {p : PMF α}
    {f₁ f₂ g₁ g₂ : α → PMF β} {b : β}
    (h : ∀ a ∈ p.support, f₁ a b + g₂ a b = f₂ a b + g₁ a b) :
    p.bind f₁ b + p.bind g₂ b = p.bind f₂ b + p.bind g₁ b := by
  simp only [PMF.bind_apply, ← tsum_add]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ p.support
  · rw [← mul_add, ← mul_add, h a ha]
  · simp [(PMF.apply_eq_zero_iff p a).mpr ha]

-- Moved from `CslibFrontier/Crypto/Computational/WeakPRF.lean` (Karn Seth), where it was private.
/-- Pointwise bounds away from one exceptional first-stage result bound a two-stage experiment,
up to the probability of that result. -/
theorem bind_apply_le_add_of_ne {T β : Type*} (μ : PMF T) (F G : T → PMF β) (b : β)
    (bad : T) {ε : ℝ≥0∞} (h : ∀ t, t ≠ bad → F t b ≤ G t b + ε) :
    μ.bind F b ≤ μ.bind G b + ε + μ bad := by
  classical
  have hpoint (t : T) :
      μ t * F t b ≤ μ t * G t b + μ t * ε + if t = bad then μ bad else 0 := by
    by_cases ht : t = bad
    · subst ht
      rw [ite_eq_left_of_eq_true _ _ (eq_self t)]
      exact le_add_of_le_right (mul_le_of_le_one_right zero_le (PMF.coe_le_one _ _))
    · simp only [ht, ↓reduceIte, add_zero]
      rw [← mul_add]
      exact mul_le_mul_right (h t ht) _
  simp only [PMF.bind_apply]
  calc ∑' t, μ t * F t b
      ≤ ∑' t, (μ t * G t b + μ t * ε + if t = bad then μ bad else 0) :=
        tsum_le_tsum hpoint
    _ = ∑' t, μ t * G t b + ε + μ bad := by
        rw [tsum_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          tsum_ite_eq]

-- Moved from `CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NotBot/Challenge.lean`, where it
-- was private.
/-- Binds whose first stages agree on good states, and whose continuations agree on good inputs
and outputs and keep bad states bad, agree on good outputs. -/
theorem bind_apply_eq_of_good {α β σ : Type*} {bad : σ → Prop} {p₁ p₂ : PMF (α × σ)}
    {f₁ f₂ : α × σ → PMF (β × σ)} (hp : ∀ x, ¬bad x.2 → p₁ x = p₂ x)
    (hf : ∀ x, ¬bad x.2 → ∀ y, ¬bad y.2 → f₁ x y = f₂ x y)
    (h₁ : ∀ x, bad x.2 → ∀ y ∈ (f₁ x).support, bad y.2)
    (h₂ : ∀ x, bad x.2 → ∀ y ∈ (f₂ x).support, bad y.2) (y : β × σ) (hy : ¬bad y.2) :
    (p₁.bind f₁) y = (p₂.bind f₂) y := by
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : bad x.2
  · rw [(PMF.apply_eq_zero_iff _ _).mpr fun hm => hy (h₁ x hx y hm),
      (PMF.apply_eq_zero_iff _ _).mpr fun hm => hy (h₂ x hx y hm), mul_zero, mul_zero]
  · rw [hp x hx, hf x hx y hy]

end Cslib.Probability.PMF
