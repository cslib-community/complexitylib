/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.EquivFin

/-!
# Selfish routing: nonatomic congestion games

In a **nonatomic congestion game** a continuum of infinitesimal players routes traffic. There is a
finite set `P` of paths. Each path `p` belongs to a commodity `commodity p` and uses the finite set
of resources `resources p` (the edges of a path in a network). A commodity `k` has traffic rate
`rate k`. A flow `f : P → ℝ` is **feasible** if it is nonnegative and routes exactly `rate k` units
of traffic on the paths of each commodity `k`. The flow on resource `e` is the total flow on the
paths through `e`, a path's latency is the sum of the latencies of its resources at their flows,
and the cost of `f` is the total latency `∑ p, f p * pathLatency f p`.

This is the model of Roughgarden and Tardos [RoughgardenTardos2002], Section 2.1, with a network's
`s_i`–`t_i` paths abstracted to finite sets of resources. A feasible flow is a **Wardrop
equilibrium** (a flow at Nash equilibrium, [RoughgardenTardos2002], Definition 2.1) when every path
carrying flow is a shortest path of its commodity; for continuous nondecreasing latencies this is
the characterization of [RoughgardenTardos2002], Lemma 2.2, which we take as the definition.

The variational inequality proved here is the first step of every price-of-anarchy bound. The
bounds themselves are in `Complexity.GameTheory.Congestion.PigouBound`: the Pigou bound for an
arbitrary class of latencies, its value for polynomials of bounded degree, and the `4/3` theorem
for affine latencies ([RoughgardenTardos2002], Theorem 4.5).

## Main definitions

* `Cslib.GameTheory.NonatomicCongestionGame`: a nonatomic congestion game.
* `Cslib.GameTheory.NonatomicCongestionGame.IsFeasible`, `edgeFlow`, `pathLatency`, `cost`:
  feasible flows, resource flows, path latencies and total cost.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop`: Wardrop equilibria.
* `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies`: nonnegative affine latencies.

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.cost_eq_sum_edgeFlow`: the cost is
  `∑ e, edgeFlow f e * latency e (edgeFlow f e)`.
* `Cslib.GameTheory.NonatomicCongestionGame.cost_nonneg`: nonnegative flows and latencies have
  nonnegative cost.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_sum_mul_pathLatency`: the
  variational inequality `cost f ≤ ∑ p, g p * pathLatency f p` for a Wardrop equilibrium `f` and a
  feasible flow `g`.

## References

* [RoughgardenTardos2002]
-/

public section

namespace Cslib.GameTheory

/-- A **nonatomic congestion game**: each path `p` belongs to the commodity `commodity p` and uses
the resources `resources p`; commodity `k` has traffic rate `rate k`; and `latency e x` is the
latency of resource `e` when it carries flow `x`. -/
structure NonatomicCongestionGame (K P E : Type*) where
  /-- The commodity whose traffic may use the path `p`. -/
  commodity : P → K
  /-- The resources used by the path `p`. -/
  resources : P → Finset E
  /-- The amount of traffic of commodity `k`. -/
  rate : K → ℝ
  /-- The latency of resource `e` when it carries flow `x`. -/
  latency : E → ℝ → ℝ

namespace NonatomicCongestionGame

variable {K P E : Type*} [Fintype P] [DecidableEq E] (G : NonatomicCongestionGame K P E)

/-- A flow `f` on the paths is **feasible** if it is nonnegative and routes exactly `rate k` units
of traffic on the paths of each commodity `k`. -/
@[expose] def IsFeasible [DecidableEq K] (f : P → ℝ) : Prop :=
  (∀ p, 0 ≤ f p) ∧ ∀ k, ∑ p with G.commodity p = k, f p = G.rate k

/-- The flow on the resource `e`: the total flow on the paths that use `e`. -/
@[expose] def edgeFlow (f : P → ℝ) (e : E) : ℝ :=
  ∑ p with e ∈ G.resources p, f p

/-- The latency of the path `p` under the flow `f`: the sum of the latencies of its resources. -/
@[expose] def pathLatency (f : P → ℝ) (p : P) : ℝ :=
  ∑ e ∈ G.resources p, G.latency e (G.edgeFlow f e)

/-- The **cost** (total latency) of the flow `f`: `∑ p, f p * pathLatency f p`. -/
@[expose] def cost (f : P → ℝ) : ℝ :=
  ∑ p, f p * G.pathLatency f p

/-- A **Wardrop equilibrium**: a feasible flow under which every path carrying positive flow has
latency at most that of every path of the same commodity ([RoughgardenTardos2002], Lemma 2.2). -/
@[expose] def IsWardrop [DecidableEq K] (f : P → ℝ) : Prop :=
  G.IsFeasible f ∧ ∀ p q, G.commodity p = G.commodity q → 0 < f p →
    G.pathLatency f p ≤ G.pathLatency f q

/-- `G` has **affine latencies**: there are `a e, b e ≥ 0` with `latency e x = a e * x + b e` for
every resource `e` and flow `x` ([RoughgardenTardos2002], Section 4). -/
@[expose] def HasAffineLatencies : Prop :=
  ∃ a b : E → ℝ, (∀ e, 0 ≤ a e) ∧ (∀ e, 0 ≤ b e) ∧ ∀ e x, G.latency e x = a e * x + b e

/-- Exchanging the sums over paths and resources: weighting each path's resource sum by `w p`
weights each resource `e` by the flow `edgeFlow w e`. -/
theorem sum_mul_sum_resources [Fintype E] (w : P → ℝ) (h : E → ℝ) :
    ∑ p, w p * ∑ e ∈ G.resources p, h e = ∑ e, G.edgeFlow w e * h e := by
  simp only [edgeFlow, Finset.mul_sum, Finset.sum_mul, Finset.sum_filter, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The cost of a flow is the sum over resources of flow times latency. -/
theorem cost_eq_sum_edgeFlow [Fintype E] (f : P → ℝ) :
    G.cost f = ∑ e, G.edgeFlow f e * G.latency e (G.edgeFlow f e) :=
  G.sum_mul_sum_resources f _

/-- A nonnegative flow has nonnegative cost when the latencies are nonnegative on `[0, ∞)`. -/
theorem cost_nonneg (hl : ∀ e x, 0 ≤ x → 0 ≤ G.latency e x) {f : P → ℝ} (hf : ∀ p, 0 ≤ f p) :
    0 ≤ G.cost f :=
  Finset.sum_nonneg fun p _ => mul_nonneg (hf p) <| Finset.sum_nonneg fun e _ =>
    hl e _ <| Finset.sum_nonneg fun q _ => hf q

variable {G}

/-- **The variational inequality** for Wardrop equilibria: if `f` is a Wardrop equilibrium and
`g` is feasible, then `cost f ≤ ∑ p, g p * pathLatency f p`, that is, rerouting the traffic as in
`g` while keeping the latencies of `f` does not lower the total latency. -/
theorem IsWardrop.cost_le_sum_mul_pathLatency [DecidableEq K] {f g : P → ℝ}
    (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ ∑ p, g p * G.pathLatency f p := by
  unfold cost
  have hmaps : ∀ p ∈ (Finset.univ : Finset P), G.commodity p ∈ Finset.univ.image G.commodity :=
    fun p _ => Finset.mem_image_of_mem _ (Finset.mem_univ p)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h : ∃ p₀, G.commodity p₀ = k ∧ 0 < f p₀
  · obtain ⟨p₀, hp₀, hpos⟩ := h
    have hL : ∀ p ∈ Finset.univ.filter (G.commodity · = k),
        f p * G.pathLatency f p = f p * G.pathLatency f p₀ := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases (hf.1.1 p).lt_or_eq with hfp | hfp
      · rw [le_antisymm (hf.2 p p₀ (hp.trans hp₀.symm) hfp) (hf.2 p₀ p (hp₀.trans hp.symm) hpos)]
      · rw [← hfp, zero_mul, zero_mul]
    have hge : ∀ p ∈ Finset.univ.filter (G.commodity · = k),
        g p * G.pathLatency f p₀ ≤ g p * G.pathLatency f p := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact mul_le_mul_of_nonneg_left (hf.2 p₀ p (hp₀.trans hp.symm) hpos) (hg.1 p)
    rw [Finset.sum_congr rfl hL, ← Finset.sum_mul, hf.1.2 k, ← hg.2 k, Finset.sum_mul]
    exact Finset.sum_le_sum hge
  · push Not at h
    have hf0 : ∀ p ∈ Finset.univ.filter (G.commodity · = k), f p = 0 := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact le_antisymm (h p hp) (hf.1.1 p)
    have hg0 : ∀ p ∈ Finset.univ.filter (G.commodity · = k), g p = 0 := by
      have hsum : ∑ p with G.commodity p = k, g p = 0 := by
        rw [hg.2 k, ← hf.1.2 k]
        exact Finset.sum_eq_zero hf0
      exact (Finset.sum_eq_zero_iff_of_nonneg fun p _ => hg.1 p).1 hsum
    rw [Finset.sum_eq_zero fun p hp => by rw [hf0 p hp, zero_mul],
      Finset.sum_eq_zero fun p hp => by rw [hg0 p hp, zero_mul]]

end NonatomicCongestionGame

end Cslib.GameTheory
