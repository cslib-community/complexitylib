/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import Mathlib.Probability.Independence.Basic
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Product

/-!
# Independent observables of a PMF

Two observables `X` and `Y` of `ν : PMF Ω` are independent exactly when the law of `(X, Y)` is
the law of `X` paired with an independent draw from the law of `Y`. For countable codomains, this
factorization is equivalent to Mathlib's `IndepFun X Y ν.toMeasure`.

`IndepUniform ν X Y` is the special case in which the law of `Y` is uniform. Security statements
use it for a value that is uniform and independent of an adversary's view.

## Main definitions

* `Cslib.Probability.PMF.IndepUniform`: `Y` is uniform and independent of `X` under `ν`.

## Main results

* `Cslib.Probability.PMF.indepFun_iff_map_pair_eq_bind`: factorization of the joint PMF is
  Mathlib's measure-theoretic independence.
* `Cslib.Probability.PMF.IndepUniform.map_snd`: the second observable is uniform.
* `Cslib.Probability.PMF.indepUniform_iff`: `IndepUniform` is independence together with a uniform
  law for `Y`.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory ProbabilityTheory

variable {Ω α β : Type*}

/-- A factorization of the joint PMF is Mathlib's measure-theoretic independence. -/
theorem indepFun_iff_map_pair_eq_bind
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    [Countable α] [Countable β]
    (p : PMF Ω) {f : Ω → α} {g : Ω → β} (hf : Measurable f) (hg : Measurable g) :
    IndepFun f g p.toMeasure ↔
      p.map (fun ω => (f ω, g ω)) = (p.map f).bind (fun a => (p.map g).map (fun b => (a, b))) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,
    PMF.toMeasure_map _ _ (hf.prodMk hg), PMF.toMeasure_map _ _ hf, PMF.toMeasure_map _ _ hg,
    ← toMeasure_bind_pair, PMF.toMeasure_inj]

/-- `Y` is uniform and independent of `X` under `ν`: drawing `ω ← ν` and reporting `(X ω, Y ω)`
is the same as drawing `X ω` and then an independent uniform `Y`. -/
structure IndepUniform [Fintype β] [Nonempty β] (ν : PMF Ω) (X : Ω → α) (Y : Ω → β) : Prop where
  /-- The joint law of `(X, Y)` is the law of `X` paired with an independent uniform draw. -/
  map_pair_eq : ν.map (fun ω => (X ω, Y ω)) =
    (ν.map X).bind fun x => (PMF.uniformOfFintype β).map (x, ·)

namespace IndepUniform

variable [Fintype β] [Nonempty β] {ν : PMF Ω} {X : Ω → α} {Y : Ω → β}

/-- The second observable of `IndepUniform ν X Y` is uniform. -/
theorem map_snd (h : IndepUniform ν X Y) : ν.map Y = PMF.uniformOfFintype β := by
  have hY : ν.map Y = (ν.map fun ω => (X ω, Y ω)).map Prod.snd := by
    rw [PMF.map_comp]
    rfl
  rw [hY, h.map_pair_eq, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  exact (congrArg (ν.map X).bind (funext fun _ => PMF.map_id _)).trans (PMF.bind_const _ _)

end IndepUniform

/-- `IndepUniform ν X Y` is Mathlib's independence of `X` and `Y` together with a uniform law for
`Y`. -/
theorem indepUniform_iff [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Fintype β]
    [Nonempty β] {ν : PMF Ω} {X : Ω → α} {Y : Ω → β} (hX : Measurable X) (hY : Measurable Y) :
    IndepUniform ν X Y ↔ IndepFun X Y ν.toMeasure ∧ ν.map Y = PMF.uniformOfFintype β := by
  rw [indepFun_iff_map_pair_eq_bind ν hX hY]
  refine ⟨fun h => ⟨?_, h.map_snd⟩, fun ⟨h, hU⟩ => ⟨?_⟩⟩
  · rw [h.map_snd]
    exact h.map_pair_eq
  · rw [h, hU]

end Cslib.Probability.PMF
