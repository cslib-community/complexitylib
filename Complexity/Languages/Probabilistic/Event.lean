/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Semantics
import Complexity.Probability.PMF.Event

/-!
# Sequential success bounds for probabilistic programs

A first program can establish success, and a second program can recover when the first fails.
If each branch succeeds with probability at least `1 / s` on the inputs that need it, and later
execution retains every first-branch success, the sequence succeeds with probability at least
`2 / (s + 1)`. The second program may depend on the first result. Hypotheses apply only to
possible outcomes, and no independence or finite output-type hypothesis is needed.

These are bounds on the distributions denoted by terminating `ProbComp` programs. Runtime and
oracle-query costs require separate certificates.

## Main results

* `Cslib.ProbComp.two_branch_hit_prob_ge`: retained first-branch success and conditional recovery
  give the two-branch success bound.

## References

The generic success rule is from Renfei Zhou's Karger–Stein development.
-/

@[expose] public section

namespace Cslib.ProbComp

open scoped ENNReal
open Cslib.Probability.PMF

/-- Elementary recurrence `2 / (s + 1) ≤ 1 - (1 - 1 / s) ^ 2` in `ℝ≥0∞` for `1 ≤ s`, derived from
`(2 * s - 1) * (s + 1) = 2 * s ^ 2 + s - 1 ≥ 2 * s ^ 2`. -/
private theorem one_sub_sq_one_sub_inv_ge {s : ℕ} (hs : 1 ≤ s) :
    (2 : ℝ≥0∞) / ((s + 1 : ℕ) : ℝ≥0∞) ≤ 1 - (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by
  have hs0 : (s : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hst : (s : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top s
  have hsub : (1 : ℝ≥0∞) - 1 / (s : ℝ≥0∞) =
      ((s - 1 : ℕ) : ℝ≥0∞) / (s : ℝ≥0∞) := by
    rw [ENNReal.natCast_sub, Nat.cast_one, ENNReal.sub_div (fun _ _ => hs0),
      ENNReal.div_self hs0 hst]
  rw [hsub]
  have hs20 : ((s * s : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.mul_pos hs hs).ne'
  have hs2t : ((s * s : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsp10 : ((s + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hsp1t : ((s + 1 : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsq_eq : (((s - 1 : ℕ) : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 =
      (((s - 1) * (s - 1) : ℕ) : ℝ≥0∞) / ((s * s : ℕ) : ℝ≥0∞) := by
    simp only [sq, div_eq_mul_inv, Nat.cast_mul, ENNReal.mul_inv (Or.inl hs0) (Or.inl hst)]
    ring
  rw [hsq_eq]
  have hsub_eq : (1 : ℝ≥0∞) - (((s - 1) * (s - 1) : ℕ) : ℝ≥0∞) / ((s * s : ℕ) : ℝ≥0∞) =
      ((2 * s - 1 : ℕ) : ℝ≥0∞) / ((s * s : ℕ) : ℝ≥0∞) := by
    refine ENNReal.sub_eq_of_eq_add
      (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hs20) ?_
    rw [div_eq_mul_inv, div_eq_mul_inv, ← add_mul]
    have hsum : (2 * s - 1) + (s - 1) * (s - 1) = s * s := by
      obtain ⟨d, rfl⟩ : ∃ d, s = d + 1 := ⟨s - 1, by omega⟩
      have h1 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
      have h2 : d + 1 - 1 = d := by omega
      rw [h1, h2]
      ring
    have hcast : ((2 * s - 1 : ℕ) : ℝ≥0∞) + (((s - 1) * (s - 1) : ℕ) : ℝ≥0∞) =
        ((s * s : ℕ) : ℝ≥0∞) := by exact_mod_cast hsum
    rw [hcast, ← div_eq_mul_inv, ENNReal.div_self hs20 hs2t]
  rw [hsub_eq]
  rw [ENNReal.div_le_iff_le_mul (Or.inl hsp10) (Or.inl hsp1t)]
  rw [← ENNReal.mul_div_right_comm]
  rw [ENNReal.le_div_iff_mul_le (Or.inl hs20) (Or.inl hs2t)]
  have hnat : 2 * (s * s) ≤ (2 * s - 1) * (s + 1) := by
    obtain ⟨d, rfl⟩ : ∃ d, s = d + 1 := ⟨s - 1, by omega⟩
    have h1 : 2 * (d + 1) - 1 = 2 * d + 1 := by omega
    rw [h1]
    nlinarith
  exact_mod_cast hnat

/-- Sequential two-branch success probability recurrence on `ProbComp`: if Branch 1 hits `hit₁`
with probability `≥ 1 / s`, any outcome in `hit₁` guarantees `f a b ∈ hit` on every supported `b`,
and conditioned on any outcome outside `hit₁` Branch 2 achieves `f a b ∈ hit` with probability
`≥ 1 / s`, then the combined computation hits `hit` with probability `≥ 2 / (s + 1)`. -/
theorem two_branch_hit_prob_ge {α β γ : Type} (m₁ : ProbComp α) (m₂ : α → ProbComp β)
    (f : α → β → γ) (hit₁ : Set α) (hit : Set γ) {s : ℕ} (hs : 1 ≤ s)
    (hb₁ : (1 : ℝ≥0∞) / (s : ℝ≥0∞) ≤ m₁.eval.toOuterMeasure hit₁)
    (hprop₁ : ∀ a ∈ m₁.support, a ∈ hit₁ → ∀ b ∈ (m₂ a).support, f a b ∈ hit)
    (hb₂ : ∀ a ∈ m₁.support, a ∉ hit₁ →
      (1 : ℝ≥0∞) / (s : ℝ≥0∞) ≤ ((m₂ a).eval.map (f a)).toOuterMeasure hit) :
    (2 : ℝ≥0∞) / ((s + 1 : ℕ) : ℝ≥0∞) ≤
      (do let a ← m₁; let b ← m₂ a; pure (f a b)).eval.toOuterMeasure hit := by
  let p := (do let a ← m₁; let b ← m₂ a; pure (f a b)).eval
  have hp_eq : p = m₁.eval.bind (fun a => (m₂ a).eval.map (f a)) := by
    dsimp only [p]
    rw [ProbComp.eval_bind]
    refine congrArg (m₁.eval.bind ·) (funext fun a => ?_)
    rw [bind_pure_comp, ProbComp.eval_map]
  have hcompl_le : p.toOuterMeasure hitᶜ ≤ (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by
    rw [hp_eq, sq]
    refine toOuterMeasure_bind_le_mul_ennreal m₁.eval (fun a => (m₂ a).eval.map (f a))
      hit₁ᶜ hitᶜ (toOuterMeasure_compl_le_one_sub m₁.eval hit₁ hb₁) ?_ ?_
    · intro a ha_eval ha_miss
      have ha : a ∈ m₁.support := (ProbComp.support_eval m₁) ▸ ha_eval
      exact toOuterMeasure_compl_le_one_sub _ hit (hb₂ a ha ha_miss)
    · intro a ha_eval ha_not_miss
      have ha : a ∈ m₁.support := (ProbComp.support_eval m₁) ▸ ha_eval
      have ha_hit : a ∈ hit₁ := not_not.mp ha_not_miss
      rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
      refine tsum_eq_zero_iff.mpr fun b => ?_
      by_cases hb_eval : b ∈ (m₂ a).eval.support
      · have hb : b ∈ (m₂ a).support := (ProbComp.support_eval (m₂ a)) ▸ hb_eval
        have hmem : f a b ∈ hit := hprop₁ a ha ha_hit b hb
        have hnot : b ∉ (f a ⁻¹' hitᶜ) := fun hc => hc hmem
        exact Set.indicator_of_notMem hnot _
      · have hp0 : (m₂ a).eval b = 0 := by simpa only [PMF.mem_support_iff, not_not] using hb_eval
        simp [hp0]
  have hsum := toOuterMeasure_add_compl_ennreal p hit
  have hhit_ge : 1 - (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 ≤ p.toOuterMeasure hit := by
    refine tsub_le_iff_right.mpr ?_
    calc
      (1 : ℝ≥0∞) = p.toOuterMeasure hit + p.toOuterMeasure hitᶜ := hsum.symm
      _ ≤ p.toOuterMeasure hit + (1 - (1 : ℝ≥0∞) / (s : ℝ≥0∞)) ^ 2 := by gcongr
  exact (one_sub_sq_one_sub_inv_ge hs).trans hhit_ge

end Cslib.ProbComp
