/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import Mathlib.Tactic

/-!
# Discrete hidden-state disintegration

Condition an arbitrary PMF using pinned cslib's `PMF.posteriorDist`.
Null observations use the prior. Neither the private state nor its observation
alphabet must be finite; PMF semantics still describes discrete laws.

## Main results

* `posterior_factor`: the conditional joint mass is the original fiber mass.
* `posterior_bind`: every continuation has the original joint law after disintegration.
-/

public section
noncomputable section
namespace Cslib.Probability.PMF
variable {S H B : Type*}

open scoped Classical in
/-- Private-state posterior on an observed atom. Null observations use the prior,
which leaves every joint law unchanged. -/
@[expose] def posterior (p : PMF S) (observe : S → H) (h : H) : PMF S :=
  if hp : h ∈ (p.bind fun s => PMF.pure (observe s)).support then
    posteriorDist p (fun s => PMF.pure (observe s)) h hp
  else p

open scoped Classical in
/-- Exact fiber factorization, including null observations. -/
theorem posterior_factor (p : PMF S) (observe : S → H) (h : H) (s : S) :
    p.map observe h * posterior p observe h s = if observe s = h then p s else 0 := by
  classical
  by_cases hp : h ∈ (p.bind fun s => PMF.pure (observe s)).support
  · have hn : p.map observe h ≠ 0 := hp
    have he : posterior p observe h s =
        (if observe s = h then p s else 0) * (p.map observe h)⁻¹ := by
      rw [posterior, dite_eq_left hp, posteriorDist_apply, bind_pair_apply, div_eq_mul_inv,
        PMF.pure_apply]
      by_cases hs : observe s = h
      · simp [hs]
      · simp [hs, Ne.symm hs]
    rw [he]
    by_cases hs : observe s = h
    · rw [ite_eq_left hs]
      calc
        _ = p s * (p.map observe h * (p.map observe h)⁻¹) := by ac_rfl
        _ = p s := by rw [ENNReal.mul_inv_cancel hn ((p.map observe).apply_ne_top h), mul_one]
    · simp [hs]
  · have hz : p.map observe h = 0 := (PMF.apply_eq_zero_iff _ _).mpr hp
    rw [hz, zero_mul]
    split_ifs with hs
    · have hz' : p s = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro ht
        exact hp ((PMF.mem_support_map_iff _ _ _).mpr ⟨s, ht, hs⟩)
      exact hz'.symm
    · rfl

/-- Disintegrating hidden state before any observation-dependent continuation
preserves the entire resulting law, with no supplied conditional-law identity. -/
theorem posterior_bind (p : PMF S) (observe : S → H) (next : S → H → PMF B) :
    (p.map observe).bind (fun h => (posterior p observe h).bind (fun s => next s h)) =
      p.bind (fun s => next s (observe s)) := by
  classical
  ext b
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_left, ← mul_assoc, posterior_factor]
  rw [tsum_comm]
  apply tsum_congr
  intro s
  rw [tsum_eq_single (observe s)]
  · simp
  · intro h hh
    simp [Ne.symm hh]

end Cslib.Probability.PMF
