/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Hom
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Edge multiplicities and harmonic functions on regular multigraphs

Facts about the edge multiplicities `G.edgeCount x y` of a regular multigraph `G : RotationMap V D`
that random-walk arguments need, and the **maximum principle**: on a connected graph, a function
whose value at every vertex is the average of its values along the edges there is constant
(`eq_of_forall_sum_edgeCount_mul_eq`, `eq_of_walk_eq_self`). Equivalently, the only fixed points
of the walk operator are the constants.

## Main results

* `Cslib.RotationMap.sum_comp_neighbor`: a sum over the labels at `x` is a sum over vertices
  weighted by edge multiplicities.
* `Cslib.RotationMap.edgeCount_ne_zero_iff`, `Cslib.RotationMap.reachable_of_edgeCount_ne_zero`,
  `Cslib.RotationMap.edgeCount_ne_zero_of_adj`: edges, adjacency and reachability.
* `Cslib.RotationMap.eq_of_forall_sum_edgeCount_mul_eq`, `Cslib.RotationMap.eq_of_walk_eq_self`:
  the maximum principle.
-/

public section

namespace Cslib.RotationMap

open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] (G : RotationMap V D)

/-- A sum over the labels at `x` of a function of the neighbor is a sum over the vertices weighted
by edge multiplicities. -/
theorem sum_comp_neighbor [Fintype V] {M : Type*} [AddCommMonoid M] (x : V) (f : V → M) :
    ∑ i, f (G.neighbor x i) = ∑ y, G.edgeCount x y • f y := by
  rw [← sum_fiberwise univ (G.neighbor x) (fun i => f (G.neighbor x i))]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_congr rfl fun i hi => by rw [(mem_filter.1 hi).2], sum_const, edgeCount_eq_card_filter]

variable {G}

/-- Some edge joins `x` to `y` exactly when `y` is a neighbor of `x`. -/
theorem edgeCount_ne_zero_iff {x y : V} : G.edgeCount x y ≠ 0 ↔ ∃ i, G.neighbor x i = y := by
  rw [edgeCount_eq_card_filter, ← pos_iff_ne_zero, card_pos]
  simp [Finset.Nonempty]

/-- The ends of an edge are in the same connected component. -/
theorem reachable_of_edgeCount_ne_zero {x y : V} (h : G.edgeCount x y ≠ 0) :
    G.toSimpleGraph.Reachable x y := by
  obtain ⟨i, rfl⟩ := edgeCount_ne_zero_iff.1 h
  exact G.reachable_neighbor x i

/-- Adjacent vertices of the simple graph are joined by an edge. -/
theorem edgeCount_ne_zero_of_adj {x y : V} (h : G.toSimpleGraph.Adj x y) : G.edgeCount x y ≠ 0 :=
  edgeCount_ne_zero_iff.2 h.2

variable [Fintype V]

/-- **Maximum principle.** On a connected regular multigraph, a function equal at every vertex to
the average of its values over the edges there is constant. -/
theorem eq_of_forall_sum_edgeCount_mul_eq (hG : G.toSimpleGraph.Preconnected) {f : V → ℝ}
    (hf : ∀ y, ∑ x, (G.edgeCount y x : ℝ) * f x = Fintype.card D * f y) (x y : V) :
    f x = f y := by
  have : Nonempty V := ⟨x⟩
  obtain ⟨m, hm⟩ := Finite.exists_max f
  set S : Set V := {v | f v = f m}
  have hS : ∀ v ∈ S, ∀ i, G.neighbor v i ∈ S := by
    intro v hv i
    have hsum : ∑ z, (G.edgeCount v z : ℝ) * (f m - f z) = 0 := by
      simp_rw [mul_sub, sum_sub_distrib, hf v, ← sum_mul]
      have hc : ∑ z, (G.edgeCount v z : ℝ) = Fintype.card D := by
        exact_mod_cast G.sum_edgeCount v
      rw [hc, (hv : f v = f m), sub_self]
    have hz := (sum_eq_zero_iff_of_nonneg fun z _ =>
      mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hm z))).1 hsum (G.neighbor v i) (mem_univ _)
    have hc : (G.edgeCount v (G.neighbor v i) : ℝ) ≠ 0 := by
      exact_mod_cast (edgeCount_ne_zero_iff (G := G)).2 ⟨i, rfl⟩
    exact (sub_eq_zero.1 ((mul_eq_zero.1 hz).resolve_left hc)).symm
  have hall : ∀ v, v ∈ S := fun v => G.mem_of_reachable hS (show m ∈ S from rfl) (hG m v)
  exact (hall x).trans (hall y).symm

omit [DecidableEq V] [Fintype V] in
/-- **Maximum principle.** On a connected regular multigraph of positive degree, a function fixed
by the walk operator is constant. -/
theorem eq_of_walk_eq_self [Finite V] [Nonempty D] (hG : G.toSimpleGraph.Preconnected) {f : V → ℝ}
    (hf : G.walk f = f) (x y : V) : f x = f y := by
  classical
  have : Fintype V := Fintype.ofFinite V
  refine eq_of_forall_sum_edgeCount_mul_eq hG (fun y => ?_) x y
  have h := congrFun hf y
  rw [walk_apply, Fintype.expect_eq_sum_div_card, G.sum_comp_neighbor y f] at h
  have hd : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [nsmul_eq_mul] at h
  rw [div_eq_iff hd] at h
  rw [h, mul_comm]

end Cslib.RotationMap
