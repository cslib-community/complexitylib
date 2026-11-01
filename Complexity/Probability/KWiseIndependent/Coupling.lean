/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.StatisticalDistance.Coupling
public import Mathlib.Data.Fintype.Pi
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Complexity.Probability.Uniform

/-!
# Uniform Restriction and Two-Level Coupling Laws for $k$-Wise Independent Hash Families

Under a uniform finite seed `θ ← PMF.uniformOfFintype Seed`, restricting a `k`-wise independent hash
family `eval : Seed → Fin U → Fin m` to any subset `T : Finset (Fin U)` of size `#T ≤ k` yields the
exact uniform distribution `PMF.uniformOfFintype (T → Fin m)`
(`Cslib.Probability.uniformOfFintype_map_restrict_eq`).

For a two-level hash family `eval : TopSeed → BotSeed → Fin U → Fin m` whose inner family `eval α`
is `k`-wise independent for every good top seed `α ∈ GoodTop`, the restricted distribution on `T`
with `#T ≤ k` is coupled within `(#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed` of
`PMF.uniformOfFintype (T → Fin m)`
(`Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`).

## Main results

* `Cslib.Probability.uniformOfFintype_map_restrict_eq`: restricting a `k`-wise independent hash
  family to `T` (`#T ≤ k`) under a uniform seed produces `PMF.uniformOfFintype (T → Fin m)`.
* `Cslib.Probability.coupledWithin_uniformOfFintype_prod_restrict`: two-level coupling bound for
  restricting a hash family whose top seed is `k`-wise independent on `GoodTop`.
-/

public section

open scoped ENNReal Cslib.Probability.PMF
open Cslib.Probability.PMF

namespace Cslib.Probability

universe u v w

/-- If `eval : Seed → Fin U → Fin m` is `k`-wise independent, then restricting `eval θ` under
`θ ← PMF.uniformOfFintype Seed` to any subset `T : Finset (Fin U)` of size `#T ≤ k` produces the
exact uniform distribution `PMF.uniformOfFintype (T → Fin m)`. -/
theorem uniformOfFintype_map_restrict_eq {Seed : Type u} {U m : ℕ}
    [Fintype Seed] [Nonempty Seed] [NeZero m] {k : ℕ} {eval : Seed → Fin U → Fin m}
    (hk : IsKWiseIndependentHash k eval)
    {T : Finset (Fin U)} (hT : T.card ≤ k) :
    (PMF.uniformOfFintype Seed).map (fun θ => T.restrict (eval θ)) =
      PMF.uniformOfFintype (T → Fin m) := by
  classical
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [toReal_uniformOfFintype_map_apply, hk.dens_filter_restrict_eq hT y]
  simp [Fintype.card_pi]

private theorem uniformOfFintype_prod_map {α : Type u} {β : Type v} {γ : Type w}
    [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] (f : α → β → γ) :
    (PMF.uniformOfFintype (α × β)).map (fun p => f p.1 p.2) =
      (PMF.uniformOfFintype α).bind (fun a => (PMF.uniformOfFintype β).map (f a)) := by
  rw [← PMF.uniformOfFintype_prod, PMF.map_bind]
  refine congrArg ((PMF.uniformOfFintype α).bind ·) (funext fun a => ?_)
  simp [PMF.map_comp, Function.comp_def]

private theorem toOuterMeasure_uniformOfFintype_compl_finset {α : Type u}
    [Fintype α] [Nonempty α] [DecidableEq α] (s : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure (s : Set α)ᶜ =
      ((Finset.univ \ s).card : ℝ≥0∞) / Fintype.card α := by
  have hcompl : ((s : Set α)ᶜ : Set α) = ((Finset.univ \ s : Finset α) : Set α) := by
    ext a
    simp
  rw [hcompl, PMF.toOuterMeasure_apply_finset]
  simp [PMF.uniformOfFintype_apply, div_eq_mul_inv]

/-- Single-epoch coupling for a two-level hash family: if every `α ∈ GoodTop` induces a `k`-wise
independent family `eval α : BotSeed → Fin U → Fin m`, then restricting `eval p.1 p.2` under
`p ← PMF.uniformOfFintype (TopSeed × BotSeed)` to a set `T` of size `#T ≤ k` is coupled within
`(#(Finset.univ \ GoodTop) : ℝ≥0∞) / Fintype.card TopSeed` of `PMF.uniformOfFintype (T → Fin m)`. -/
theorem coupledWithin_uniformOfFintype_prod_restrict {TopSeed : Type u} {BotSeed : Type v}
    {U m : ℕ} [Fintype TopSeed] [Nonempty TopSeed] [DecidableEq TopSeed]
    [Fintype BotSeed] [Nonempty BotSeed]
    [NeZero m] {k : ℕ} (eval : TopSeed → BotSeed → Fin U → Fin m)
    (GoodTop : Finset TopSeed)
    (hgood : ∀ α ∈ GoodTop, IsKWiseIndependentHash k (eval α))
    {T : Finset (Fin U)} (hT : T.card ≤ k) :
    CoupledWithin
      ((PMF.uniformOfFintype (TopSeed × BotSeed)).map (fun p => T.restrict (eval p.1 p.2)))
      (PMF.uniformOfFintype (T → Fin m))
      (((Finset.univ \ GoodTop).card : ℝ≥0∞) / Fintype.card TopSeed) := by
  rw [uniformOfFintype_prod_map (fun α β => T.restrict (eval α β)),
    ← toOuterMeasure_uniformOfFintype_compl_finset GoodTop]
  refine CoupledWithin.bind_of_eq_on (GoodTop : Set TopSeed) fun α _ hα => ?_
  exact uniformOfFintype_map_restrict_eq (hgood α hα) hT

end Cslib.Probability
