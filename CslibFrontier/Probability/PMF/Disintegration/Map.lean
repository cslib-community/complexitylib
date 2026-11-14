/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Disintegration
import CslibFrontier.Probability.PMF.Map

/-!
# Deterministic observations of discrete posteriors

Pushing a private-state law forward before conditioning agrees with pushing its
posterior forward afterward, provided the observation factors through that map.
The equality includes null observations because both sides then use their prior
completion. No injectivity, finite state alphabet or supported-observation premise
is needed.

## Main results

* `posterior_map`: deterministic pushforward commutes with conditioning.
* `posterior_bind_pair`: conditioning the first component preserves its attached kernel.
-/

public section
namespace Cslib.Probability.PMF
variable {S T H : Type*}

/-- A posterior can be computed before or after any deterministic state projection
through which the observed value factors, including at null observations. -/
theorem posterior_map (p : PMF S) (f : S → T) (observe : T → H) (h : H) :
    (posterior p (observe ∘ f) h).map f = posterior (p.map f) observe h := by
  classical
  by_cases hh : h ∈ (p.map (observe ∘ f)).support
  · ext t
    apply (ENNReal.mul_right_inj hh ((p.map (observe ∘ f)).apply_ne_top h)).mp
    have hp := posterior_map_factor p (observe ∘ f) f h t
    have hq := posterior_map_factor (p.map f) observe id h t
    simp only [PMF.map_comp, PMF.map_id, Function.comp_def, id_eq] at hp hq ⊢
    exact hp.trans hq.symm
  · have hp : h ∉ (p.bind fun s => PMF.pure ((observe ∘ f) s)).support := hh
    have hq : h ∉ ((p.map f).bind fun t => PMF.pure (observe t)).support := by
      change h ∉ ((p.map f).map observe).support
      simpa only [PMF.map_comp] using hh
    simp only [posterior, dite_eq_right hp, dite_eq_right hq]

/-- Conditioning a retained first component leaves its conditional second-component
sampler unchanged, including at null observations of that first component. -/
theorem posterior_bind_pair (p : PMF S) (kernel : S → PMF T) (observe : S → H) (h : H) :
    posterior (p.bind fun s => (kernel s).map (s, ·)) (observe ∘ Prod.fst) h =
      (posterior p observe h).bind fun s => (kernel s).map (s, ·) := by
  classical
  let joint := p.bind fun s => (kernel s).map (s, ·)
  change posterior joint (observe ∘ Prod.fst) h = _
  have hm : joint.map (observe ∘ Prod.fst) = p.map observe := by
    rw [← PMF.map_comp]
    dsimp only [joint]
    rw [map_fst_bind_pair]
  by_cases hh : h ∈ (p.map observe).support
  · ext ⟨s, t⟩
    apply (ENNReal.mul_right_inj hh ((p.map observe).apply_ne_top h)).mp
    have hj := posterior_factor joint (observe ∘ Prod.fst) h (s, t)
    rw [hm] at hj
    have hp : joint (s, t) = p s * kernel s t := bind_map_prodMk_apply p kernel (s, t)
    rw [hp] at hj
    rw [bind_map_prodMk_apply, ← mul_assoc, posterior_factor]
    by_cases hs : observe s = h <;> simpa [Function.comp_def, hs] using hj
  · have hp : h ∉ (p.bind fun s => PMF.pure (observe s)).support := hh
    have hq : h ∉ (joint.bind fun pair => PMF.pure ((observe ∘ Prod.fst) pair)).support := by
      change h ∉ (joint.map (observe ∘ Prod.fst)).support
      rw [hm]
      exact hh
    simp only [posterior, dite_eq_right hp, dite_eq_right hq]
    rfl

end Cslib.Probability.PMF
