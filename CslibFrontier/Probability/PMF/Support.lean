/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map

/-!
# Support-conditioned facts about `PMF.map`, `PMF.bind` and `StateT.lift`

A distribution's pushforward or two-stage experiment is deterministic when it is so on the
support: `p.map f = PMF.pure b` exactly when `f` is constantly `b` on `p.support`
(`map_eq_pure_iff`), and `p.bind f = PMF.pure b` when every possible continuation is
(`bind_eq_pure_of_forall_mem_support`). Pushforwards to different point masses distinguish their
inputs (`ne_of_map_eq_pure`).

Pairing with a constant second coordinate pins that coordinate on the support
(`snd_eq_of_mem_support_map_pair`). Lifting a state-free `PMF` into `StateT` is such a pairing,
so it keeps the state on its support (`snd_eq_of_mem_support_lift`) and cannot reach a bad state
from a good one (`toOuterMeasure_lift_eq_zero`).

## Main results

* `Cslib.Probability.PMF.map_eq_pure_iff`, `Cslib.Probability.PMF.ne_of_map_eq_pure`:
  deterministic pushforwards.
* `Cslib.Probability.PMF.bind_eq_pure_of_forall_mem_support`: deterministic two-stage experiments.
* `Cslib.Probability.PMF.snd_eq_of_mem_support_map_pair`,
  `Cslib.Probability.PMF.snd_eq_of_mem_support_lift`,
  `Cslib.Probability.PMF.toOuterMeasure_lift_eq_zero`: state-free steps keep their state.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β σ : Type*}

/-- A pushforward is the point mass at `b` exactly when the map sends every possible outcome
to `b`. -/
theorem map_eq_pure_iff {p : PMF α} {f : α → β} {b : β} :
    p.map f = PMF.pure b ↔ ∀ a ∈ p.support, f a = b := by
  refine ⟨fun h a ha => ?_, fun h => ?_⟩
  · have hmem : f a ∈ (p.map f).support := (PMF.mem_support_map_iff _ _ _).2 ⟨a, ha, rfl⟩
    rwa [h, PMF.mem_support_pure_iff] at hmem
  · rw [map_congr_on_support p f (fun _ => b) h]
    exact PMF.map_const p b

/-- Distributions whose pushforwards along one map are different point masses are
different. -/
theorem ne_of_map_eq_pure {p q : PMF α} {f : α → β} {b c : β} (hp : p.map f = PMF.pure b)
    (hq : q.map f = PMF.pure c) (hbc : b ≠ c) : p ≠ q := by
  rintro rfl
  have hsupp := congrArg PMF.support (hp.symm.trans hq)
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupp
  exact hbc hsupp

/-- A two-stage experiment is the point mass at `b` when every possible continuation is. -/
theorem bind_eq_pure_of_forall_mem_support {p : PMF α} {f : α → PMF β} {b : β}
    (h : ∀ a ∈ p.support, f a = PMF.pure b) : p.bind f = PMF.pure b :=
  (bind_congr_on_support p f _ h).trans (PMF.bind_const p _)

/-- Pairing every outcome with a fixed second coordinate pins that coordinate on the
support. -/
theorem snd_eq_of_mem_support_map_pair {μ : PMF α} {t : σ} {x : α × σ}
    (hx : x ∈ (μ.map (·, t)).support) : x.2 = t := by
  obtain ⟨a, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
  rfl

/-- Lifting a state-free `PMF` into `StateT` preserves the state on the entire support. -/
theorem snd_eq_of_mem_support_lift {α σ : Type _} {p : PMF α} {s : σ} {z : α × σ}
    (hz : z ∈ ((StateT.lift p : StateT σ PMF α) s).support) : z.2 = s :=
  snd_eq_of_mem_support_map_pair hz

/-- Lifting a state-free `PMF` from a good state reaches a bad state with probability zero. -/
theorem toOuterMeasure_lift_eq_zero {α σ : Type _} {bad : σ → Prop} (p : PMF α) (s : σ)
    (hs : ¬bad s) : ((StateT.lift p : StateT σ PMF α) s).toOuterMeasure {x | bad x.2} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro x hx hbad
  exact hs ((snd_eq_of_mem_support_lift hx) ▸ hbad)

end Cslib.Probability.PMF
