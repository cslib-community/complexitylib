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
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Selfish routing: nonatomic congestion games with affine latencies

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

The main result is the theorem of Roughgarden and Tardos ([RoughgardenTardos2002], Theorem 4.5):
with affine latencies `latency e x = a e * x + b e`, `a e, b e ≥ 0`, the cost of a Wardrop
equilibrium is at most `4/3` times the cost of every feasible flow. Pigou's example
([RoughgardenTardos2002], Figure 3) shows that `4/3` cannot be improved
(`exists_cost_eq_four_thirds_mul`).

## Main definitions

* `Cslib.GameTheory.NonatomicCongestionGame`: a nonatomic congestion game.
* `Cslib.GameTheory.NonatomicCongestionGame.IsFeasible`, `edgeFlow`, `pathLatency`, `cost`:
  feasible flows, resource flows, path latencies and total cost.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop`: Wardrop equilibria.
* `Cslib.GameTheory.NonatomicCongestionGame.HasAffineLatencies`: nonnegative affine latencies.

## Main results

* `Cslib.GameTheory.NonatomicCongestionGame.cost_eq_sum_edgeFlow`: the cost is
  `∑ e, edgeFlow f e * latency e (edgeFlow f e)`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le_sum_mul_pathLatency`: the
  variational inequality `cost f ≤ ∑ p, g p * pathLatency f p` for a Wardrop equilibrium `f` and a
  feasible flow `g`.
* `Cslib.GameTheory.NonatomicCongestionGame.IsWardrop.cost_le` ([RoughgardenTardos2002],
  Theorem 4.5): the price of anarchy of selfish routing with affine latencies is at most `4/3`.
* `Cslib.GameTheory.NonatomicCongestionGame.exists_cost_eq_four_thirds_mul`
  ([RoughgardenTardos2002], Figure 3): Pigou's example attains `4/3`.

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

/-- **The price of anarchy of selfish routing with affine latencies is at most `4/3`**
([RoughgardenTardos2002], Theorem 4.5): if the latencies are affine with nonnegative coefficients,
`f` is a Wardrop equilibrium and `g` is a feasible flow, then `cost f ≤ 4/3 * cost g`. -/
theorem IsWardrop.cost_le [DecidableEq K] [Finite E] (hG : G.HasAffineLatencies)
    {f g : P → ℝ} (hf : G.IsWardrop f) (hg : G.IsFeasible g) :
    G.cost f ≤ 4 / 3 * G.cost g := by
  have := Fintype.ofFinite E
  obtain ⟨a, b, ha, hb, hl⟩ := hG
  have hvi := hf.cost_le_sum_mul_pathLatency hg
  simp only [pathLatency] at hvi
  rw [G.sum_mul_sum_resources g, G.cost_eq_sum_edgeFlow] at hvi
  rw [G.cost_eq_sum_edgeFlow, G.cost_eq_sum_edgeFlow]
  have hfe : ∀ e, 0 ≤ G.edgeFlow f e := fun e => Finset.sum_nonneg fun p _ => hf.1.1 p
  have key : ∀ e, G.edgeFlow g e * G.latency e (G.edgeFlow f e)
      ≤ G.edgeFlow g e * G.latency e (G.edgeFlow g e)
        + 1 / 4 * (G.edgeFlow f e * G.latency e (G.edgeFlow f e)) := by
    intro e
    rw [hl, hl]
    nlinarith [mul_nonneg (ha e) (sq_nonneg (G.edgeFlow g e - G.edgeFlow f e / 2)),
      mul_nonneg (hb e) (hfe e)]
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) => key e
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  linarith

/-- **Pigou's example** ([RoughgardenTardos2002], Figure 3): one unit of traffic on two parallel
links, with latency `x` on link `0` and constant latency `1` on link `1`. -/
private def pigou : NonatomicCongestionGame Unit (Fin 2) (Fin 2) where
  commodity _ := ()
  resources p := {p}
  rate _ := 1
  latency e x := if e = 0 then x else 1

private theorem pigou_edgeFlow (f : Fin 2 → ℝ) (e : Fin 2) : pigou.edgeFlow f e = f e := by
  simp [edgeFlow, pigou, Finset.filter_eq]

private theorem pigou_pathLatency (f : Fin 2 → ℝ) (p : Fin 2) :
    pigou.pathLatency f p = if p = 0 then f 0 else 1 := by
  simp only [pathLatency, pigou_edgeFlow]
  fin_cases p <;> simp [pigou]

private theorem pigou_cost (f : Fin 2 → ℝ) : pigou.cost f = f 0 * f 0 + f 1 := by
  simp only [cost, pigou_pathLatency]
  simp [Fin.sum_univ_two]

/-- **The bound `4/3` is attained** by Pigou's example ([RoughgardenTardos2002], Figure 3): there
is a nonatomic congestion game with affine latencies, a Wardrop equilibrium `f` and a feasible flow
`g` with `cost f = 4/3 * cost g > 0`. So the constant in `IsWardrop.cost_le` cannot be improved. -/
theorem exists_cost_eq_four_thirds_mul :
    ∃ (G : NonatomicCongestionGame Unit (Fin 2) (Fin 2)) (f g : Fin 2 → ℝ),
      G.HasAffineLatencies ∧ G.IsWardrop f ∧ G.IsFeasible g ∧ 0 < G.cost g ∧
        G.cost f = 4 / 3 * G.cost g := by
  refine ⟨pigou, ![1, 0], ![1 / 2, 1 / 2], ⟨![1, 0], ![0, 1], ?_, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩,
    ⟨?_, ?_⟩, ?_, ?_⟩
  · intro e; fin_cases e <;> norm_num
  · intro e; fin_cases e <;> norm_num
  · intro e x; fin_cases e <;> simp [pigou]
  · intro p; fin_cases p <;> norm_num
  · intro k; simp [pigou, Fin.sum_univ_two]
  · intro p q _ hp
    fin_cases p <;> fin_cases q <;> simp_all [pigou_pathLatency]
  · intro p; fin_cases p <;> norm_num
  · intro k; norm_num [pigou, Fin.sum_univ_two]
  · rw [pigou_cost]; norm_num
  · rw [pigou_cost, pigou_cost]; norm_num

end NonatomicCongestionGame

end Cslib.GameTheory
