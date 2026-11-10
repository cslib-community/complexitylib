/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Cheeger
public import CslibFrontier.Foundations.Combinatorics.Expander.Loops
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# The lazy graph

The **lazy graph** `G.lazy` of a `D`-regular multigraph `G` adds a self-loop at every vertex for
each of its edges there: its random walk stays put with probability `1 / 2` and otherwise takes a
step of the walk on `G`, so its walk operator is `(1 + G.walk) / 2` (`walk_lazy_apply`). This
operator is positive semidefinite, so Cheeger's inequality
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006] bounds the spectral expansion
of the lazy graph by the edge expansion of `G`: `λ(G.lazy) ≤ 1 - h(G)² / (4 |D|²)`
(`spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div`). This turns edge expanders into
spectral expanders, even those, such as bipartite ones, whose walk operators have the
eigenvalue `-1`.

## Main definitions

* `Cslib.RotationMap.lazy`: the lazy graph, with a self-loop for every edge at each vertex.

## Main results

* `Cslib.RotationMap.walk_lazy_apply`: the lazy walk is `(f + G.walk f) / 2`.
* `Cslib.RotationMap.spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two`:
  `λ(G.lazy) ≤ (1 + λ₂(G)) / 2`.
* `Cslib.RotationMap.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div`,
  `Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`: edge
  expansion bounds the spectral expansion of the lazy graph.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*}

/-- The **lazy graph** of `G`: `G` with a self-loop added at every vertex for each of its edges
there. Its random walk stays put with probability `1 / 2` and otherwise takes a step of the
random walk on `G`. -/
def lazy (G : RotationMap V D) : RotationMap V (D ⊕ D) :=
  G.addLoops D

variable (G : RotationMap V D)

/-- The rotation map of `G.lazy` on an original edge of `G`. -/
@[simp]
theorem rot_lazy_inl (v : V) (i : D) :
    G.lazy.rot (v, .inl i) = Prod.map id Sum.inl (G.rot (v, i)) :=
  rfl

/-- The rotation map of `G.lazy` on a lazy self-loop. -/
@[simp]
theorem rot_lazy_inr (v : V) (i : D) :
    G.lazy.rot (v, .inr i) = (v, .inr i) :=
  rfl

/-- The neighbors in `G.lazy` along the original edges of `G`. -/
@[simp]
theorem neighbor_lazy_inl (v : V) (i : D) :
    G.lazy.neighbor v (.inl i) = G.neighbor v i :=
  rfl

/-- The lazy edges of `G.lazy` are self-loops. -/
@[simp]
theorem neighbor_lazy_inr (v : V) (i : D) :
    G.lazy.neighbor v (.inr i) = v :=
  rfl

variable [Fintype D]

/-- The walk operator of the lazy graph is `(1 + G.walk) / 2`. -/
theorem walk_lazy_apply [Nonempty D] (f : V → ℝ) (v : V) :
    G.lazy.walk f v = (f v + G.walk f v) / 2 := by
  rw [lazy, walk_addLoops_apply]
  have : (0 : ℝ) < Fintype.card D := Nat.cast_pos.2 Fintype.card_pos
  field_simp
  ring

variable [Fintype V]

/-- **The spectral expansion of the lazy graph** is at most `(1 + λ₂(G)) / 2`: its walk operator
is positive semidefinite, so its spectral expansion is its second eigenvalue. -/
theorem spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two :
    G.lazy.spectralExpansion ≤ (1 + G.secondEigenvalue) / 2 := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have : G.lazy.spectralExpansion ≤ 0 :=
      spectralExpansion_le le_rfl fun f _ ↦ by simp [walk_apply]
    linarith [G.neg_one_le_secondEigenvalue]
  have hQ (f : V → ℝ) :
      𝔼 v, f v * G.lazy.walk f v = (𝔼 v, f v ^ 2 + 𝔼 v, f v * G.walk f v) / 2 := by
    rw [← expect_add_distrib, expect_div]
    exact expect_congr rfl fun v _ ↦ by rw [G.walk_lazy_apply]; ring
  rw [G.lazy.spectralExpansion_eq_secondEigenvalue_of_nonneg fun f ↦ ?_]
  · rcases subsingleton_or_nontrivial V with hV | hV
    · rw [G.lazy.secondEigenvalue_eq_zero_of_subsingleton,
        G.secondEigenvalue_eq_zero_of_subsingleton]
      norm_num
    refine G.lazy.secondEigenvalue_le_iff.2 fun f hf ↦ ?_
    rw [hQ]
    have := G.expect_mul_walk_le_secondEigenvalue_mul hf
    linarith
  · rw [hQ]
    have := neg_abs_le (𝔼 v, f v * G.walk f v)
    have := G.abs_expect_mul_walk_le_expect_sq f
    linarith

/-- **Edge expansion bounds the spectral expansion of the lazy graph**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]:
`λ(G.lazy) ≤ 1 - h(G)² / (4 |D|²)`. -/
theorem spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div [DecidableEq V] :
    G.lazy.spectralExpansion ≤ 1 - G.edgeExpansion ^ 2 / (4 * Fintype.card D ^ 2) := by
  refine G.spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two.trans ?_
  have h := G.secondEigenvalue_le_one_sub_edgeExpansion_sq_div
  have h4 : G.edgeExpansion ^ 2 / (4 * Fintype.card D ^ 2) =
      G.edgeExpansion ^ 2 / (2 * Fintype.card D ^ 2) / 2 := by
    rw [div_div]
    ring
  linarith

/-- **Edge expansion bounds the spectral expansion of the lazy graph**
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006]: on at least two vertices, if
`c ≥ 0` and at least `c |S|` edges leave every set `S` of at most half of the vertices, then
`λ(G.lazy) ≤ 1 - c² / (4 |D|²)`. -/
theorem spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl [DecidableEq V]
    [Nontrivial V] {c : ℝ} (hc₀ : 0 ≤ c)
    (hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ #(G.interedges S Sᶜ)) :
    G.lazy.spectralExpansion ≤ 1 - c ^ 2 / (4 * Fintype.card D ^ 2) := by
  refine G.spectralExpansion_lazy_le_one_sub_edgeExpansion_sq_div.trans ?_
  have := G.le_edgeExpansion_iff.2 hc
  gcongr

end Cslib.RotationMap
