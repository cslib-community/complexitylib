/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.KCenter.Basic
public import Complexity.Foundations.Combinatorics.SimpleGraph.DominatingSet
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.NormNum

/-!
# Dominating sets and the hardness gap for k-center

The hardness of approximating k-center within a factor below `2` comes from the dominating set
problem ([WilliamsonShmoys2011], Section 2.2 and Theorem 2.4, attributed there to
[HsuNemhauser1979]). Give a graph `G` the distance `domDist G`: `1` between adjacent vertices, `2`
between distinct nonadjacent vertices and `0` from a vertex to itself. This is a metric, and a
set of centers has radius at most `1` exactly when it dominates `G`; otherwise its radius is `2`.
So `G` has a dominating set of at most `k` vertices exactly when the optimal k-center radius is
at most `1`, and otherwise the optimum is `2`. A set of centers whose radius is within a factor
`ρ < 2` of the optimum has radius less than `2` when the optimum is `1`, so it is dominating: a
polynomial-time `ρ`-approximation algorithm with `ρ < 2` would decide the NP-complete dominating
set problem.

## Model

Graphs are Mathlib simple graphs on a finite nonempty vertex type with decidable equality and
adjacency; dominating sets are `SimpleGraph.IsDominatingSet`. Distances take values in a linearly
ordered strict semiring `α` such as `ℕ` or `ℝ`. A `ρ`-approximate set of centers is stated as
"radius at most `ρ * r` for every bound `r` on the optimum", which avoids multiplication in
`WithTop α` and agrees with `radius ≤ ρ * optimum` whenever the optimum is finite.

## Limitations

This module proves the combinatorial reduction and the gap only, on Mathlib simple graphs. The
NP-hardness statement of Theorem 2.4 on encoded instances, with the polynomial-time map from
encoded graphs to distance matrices, is `Cslib.Complexity.P_eq_NP_of_kCenter_approx`
(`Complexity.Computability.PCP.Approximation.KCenter`).

## Main definitions

* `Cslib.Algorithms.Lean.KCenter.domDist`: the `{1, 2}` distance of a graph.

## Main results

* `domDist_symm`, `domDist_triangle`: `domDist G` is symmetric and satisfies the triangle
  inequality.
* `radius_domDist_le_one_iff`, `radius_domDist_lt_two_iff`: a set of centers has radius at most
  `1`, equivalently less than `2`, exactly when it is dominating.
* `optRadius_domDist_le_one_iff`: a dominating set of at most `k` vertices exists exactly when the
  optimal radius is at most `1`.
* `optRadius_domDist_eq_two`: otherwise, for `k ≥ 1`, the optimal radius is `2`.
* `isDominatingSet_of_radius_le_mul`: **the gap**: when a dominating set of at most `k` vertices
  exists, every `ρ`-approximate set of centers with `ρ < 2` is dominating.
* `exists_isDominatingSet_iff_of_radius_le_mul`: so a `ρ`-approximate set of at most `k` centers
  with `ρ < 2` is dominating exactly when some dominating set of at most `k` vertices exists.

## References

* [W.-L. Hsu and G. L. Nemhauser, *Easy and hard bottleneck location
  problems*][HsuNemhauser1979]
* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.2.
-/

public section

namespace Cslib.Algorithms.Lean.KCenter

variable {V α : Type*} (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]

section Semiring

variable [Semiring α]

/-- The `{1, 2}` **distance of a graph** ([WilliamsonShmoys2011], Section 2.2): `0` from a vertex
to itself, `1` between adjacent vertices and `2` between distinct nonadjacent vertices. -/
@[expose] def domDist (u v : V) : α :=
  if u = v then 0 else if G.Adj u v then 1 else 2

variable {G}

theorem domDist_symm (u v : V) : domDist (α := α) G u v = domDist G v u := by
  unfold domDist
  by_cases h : u = v
  · simp only [h]
  · simp only [h, Ne.symm h, ↓reduceIte, G.adj_comm]

end Semiring

variable {G} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]

theorem domDist_triangle (u v w : V) :
    domDist (α := α) G u w ≤ domDist G u v + domDist G v w := by
  unfold domDist
  split_ifs <;> first | (subst_vars; simp_all) | norm_num

theorem domDist_le_one_iff {u v : V} : domDist (α := α) G u v ≤ 1 ↔ u = v ∨ G.Adj u v := by
  unfold domDist
  split_ifs <;> simp_all

theorem domDist_lt_two_iff {u v : V} : domDist (α := α) G u v < 2 ↔ u = v ∨ G.Adj u v := by
  unfold domDist
  split_ifs <;> simp_all

theorem domDist_le_two (u v : V) : domDist (α := α) G u v ≤ 2 := by
  unfold domDist
  split_ifs <;> norm_num

variable [Fintype V] [Nonempty V] {S : Finset V}

/-- A set of centers has radius at most `1` in the `{1, 2}` distance exactly when it dominates
the graph. -/
theorem radius_domDist_le_one_iff :
    radius (domDist (α := α) G) S ≤ (1 : α) ↔ G.IsDominatingSet S := by
  rw [radius_le_coe_iff, SimpleGraph.isDominatingSet_iff]
  refine forall_congr' fun v => ?_
  simp only [domDist_le_one_iff, Finset.mem_coe]
  constructor
  · rintro ⟨c, hc, rfl | h⟩
    · exact Or.inl hc
    · exact Or.inr ⟨c, hc, h⟩
  · rintro (h | ⟨c, hc, h⟩)
    · exact ⟨v, h, Or.inl rfl⟩
    · exact ⟨c, hc, Or.inr h⟩

/-- Distances in the `{1, 2}` distance are integers, so radius less than `2` means radius at most
`1`: domination again. -/
theorem radius_domDist_lt_two_iff :
    radius (domDist (α := α) G) S < (2 : α) ↔ G.IsDominatingSet S := by
  rw [← radius_domDist_le_one_iff (α := α), radius_le_iff, radius_lt_iff]
  refine forall_congr' fun v => ?_
  simp only [centerDist_lt_coe_iff, centerDist_le_coe_iff, domDist_lt_two_iff,
    domDist_le_one_iff]

/-- A nonempty set of centers has radius at most `2` in the `{1, 2}` distance. -/
theorem radius_domDist_le_two (hS : S.Nonempty) : radius (domDist (α := α) G) S ≤ (2 : α) := by
  obtain ⟨c, hc⟩ := hS
  exact radius_le_coe_iff.2 fun v => ⟨c, hc, domDist_le_two v c⟩

/-- **Dominating sets are k-center solutions of radius `1`** ([WilliamsonShmoys2011], Section 2.2):
a graph has a dominating set of at most `k` vertices exactly when the optimal k-center radius of
its `{1, 2}` distance is at most `1`. -/
theorem optRadius_domDist_le_one_iff {k : ℕ} :
    optRadius (domDist (α := α) G) k ≤ (1 : α) ↔
      ∃ S : Finset V, S.card ≤ k ∧ G.IsDominatingSet S := by
  simp only [optRadius_le_iff, radius_domDist_le_one_iff]

/-- Without a dominating set of at most `k ≥ 1` vertices, the optimal k-center radius of the
`{1, 2}` distance is exactly `2`. -/
theorem optRadius_domDist_eq_two {k : ℕ} (hk : 0 < k)
    (h : ¬ ∃ S : Finset V, S.card ≤ k ∧ G.IsDominatingSet S) :
    optRadius (domDist (α := α) G) k = (2 : α) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨c⟩ := ‹Nonempty V›
    refine optRadius_le_iff.2 ⟨{c}, ?_, radius_domDist_le_two (Finset.singleton_nonempty c)⟩
    rw [Finset.card_singleton]
    exact hk
  · rw [le_optRadius_iff]
    intro S hS
    by_contra hlt
    exact h ⟨S, hS, radius_domDist_lt_two_iff.1 (not_le.1 hlt)⟩

/-- **The gap behind the hardness of k-center** ([WilliamsonShmoys2011], Theorem 2.4;
[HsuNemhauser1979]): if a graph has a dominating set of at most `k` vertices, then every set `S`
of centers that is `ρ`-approximate for the `{1, 2}` distance with `ρ < 2` is dominating. So a
`ρ`-approximation algorithm for k-center with `ρ < 2` decides whether a dominating set of at most
`k` vertices exists: check whether its output dominates the graph and has at most `k` vertices.
This is the combinatorial core of Theorem 2.4; the NP-hardness statement is
`Cslib.Complexity.P_eq_NP_of_kCenter_approx`. -/
theorem isDominatingSet_of_radius_le_mul {k : ℕ} {ρ : α} (hρ : ρ < 2)
    (happrox : ∀ r : α, optRadius (domDist G) k ≤ (r : WithTop α) →
      radius (domDist G) S ≤ ((ρ * r : α) : WithTop α))
    (hdom : ∃ S : Finset V, S.card ≤ k ∧ G.IsDominatingSet S) : G.IsDominatingSet S := by
  have h1 := happrox 1 (optRadius_domDist_le_one_iff.2 hdom)
  rw [mul_one] at h1
  exact radius_domDist_lt_two_iff.1 (h1.trans_lt (WithTop.coe_lt_coe.2 hρ))

/-- **A `ρ`-approximation with `ρ < 2` decides dominating set** ([WilliamsonShmoys2011],
Theorem 2.4): if `S` has at most `k` vertices and is `ρ`-approximate for the `{1, 2}` distance
with `ρ < 2`, then the graph has a dominating set of at most `k` vertices exactly when `S` is
dominating. -/
theorem exists_isDominatingSet_iff_of_radius_le_mul {k : ℕ} {ρ : α} (hρ : ρ < 2)
    (hS : S.card ≤ k)
    (happrox : ∀ r : α, optRadius (domDist G) k ≤ (r : WithTop α) →
      radius (domDist G) S ≤ ((ρ * r : α) : WithTop α)) :
    (∃ T : Finset V, T.card ≤ k ∧ G.IsDominatingSet T) ↔ G.IsDominatingSet S :=
  ⟨isDominatingSet_of_radius_le_mul hρ happrox, fun h => ⟨S, hS, h⟩⟩

end Cslib.Algorithms.Lean.KCenter
