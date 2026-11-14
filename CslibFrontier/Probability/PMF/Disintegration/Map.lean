/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.Disintegration

/-!
# Deterministic observations of discrete posteriors

Pushing a private-state law forward before conditioning agrees with pushing its
posterior forward afterward, provided the observation factors through that map.
The equality includes null observations because both sides then use their prior
completion. No injectivity, finite state alphabet or supported-observation premise
is needed.

## Main results

* `posterior_map`: deterministic pushforward commutes with conditioning.
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

end Cslib.Probability.PMF
