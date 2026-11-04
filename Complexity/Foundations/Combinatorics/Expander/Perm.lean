/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cheeger

/-!
# Regular multigraphs of permutations

A family `σ : K → Equiv.Perm V` of permutations of the vertices gives a regular multigraph of degree
`2 |K|` (`ofPerms`): at every vertex `v`, each permutation `σ k` contributes an edge to `σ k v` and,
as the other end of the edge from `(σ k)⁻¹ v`, an edge to `(σ k)⁻¹ v`. Following an edge forwards
along `σ k` and then backwards along `(σ k)⁻¹` returns to its start, so the rotation map is an
involution. When the permutations are the actions of the generators of a group, this is the Schreier
graph of the action with respect to the generators and their inverses
[Hoory, Linial and Wigderson, Section 11.1.2][HooryLinialWigderson2006].

The edges leaving a set `S` of vertices are counted exactly by how many points of `S` each
permutation moves out of `S`: `σ k` moves as many points of `S` out of `S` as its inverse does, and
each such point is the start of an edge leaving `S` (`card_interedges_compl_ofPerms`). So if every
set of at most half of the vertices has a constant fraction of its points moved out of it by the
permutations, the multigraph is an edge expander (`le_edgeExpansion_ofPerms`). Random permutations
have this property (`Cslib.exists_perms_card_le_mul_card_filter_notMem`): their multigraph is the
permutation model of random regular graphs
[Hoory, Linial and Wigderson, Section 7.2.1][HooryLinialWigderson2006], and random regular graphs
are expanders [Hoory, Linial and Wigderson, Theorem 4.16][HooryLinialWigderson2006]
[Arora and Barak, Chapter 21][AroraBarak09].

## Main definitions

* `Cslib.RotationMap.ofPerms`: the regular multigraph of a family of permutations.

## Main results

* `Cslib.RotationMap.card_interedges_compl_ofPerms`: the edges leaving a set count the points the
  permutations move out of it, twice.
* `Cslib.RotationMap.le_edgeExpansion_ofPerms`: a lower bound on these counts for every set of at
  most half of the vertices bounds the edge expansion.
* `Cslib.RotationMap.expect_mul_walk_ofPerms`: the Dirichlet form of the walk is the total squared
  change of a function along the permutations.
* `Cslib.RotationMap.secondEigenvalue_ofPerms_le`: a Poincaré inequality for the permutations
  bounds the second eigenvalue.

## References

* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V K : Type*}

/-- The regular multigraph of a family `σ : K → Equiv.Perm V` of permutations, of degree `2 |K|`, as
in the permutation model of random regular graphs
[Hoory, Linial and Wigderson, Section 7.2.1][HooryLinialWigderson2006]: the edge `(k, false)` at `v`
leads to `σ k v`, where it is the edge `(k, true)`, which leads back along the inverse permutation.
-/
def ofPerms (σ : K → Equiv.Perm V) : RotationMap V (K × Bool) where
  rot p := bif p.2.2 then ((σ p.2.1).symm p.1, (p.2.1, false)) else (σ p.2.1 p.1, (p.2.1, true))
  rot_involutive := by
    rintro ⟨v, k, _ | _⟩ <;> simp

variable (σ : K → Equiv.Perm V)

/-- The rotation map of `ofPerms σ` on a forward edge. -/
@[simp]
theorem rot_ofPerms_false (v : V) (k : K) :
    (ofPerms σ).rot (v, (k, false)) = (σ k v, (k, true)) :=
  rfl

/-- The rotation map of `ofPerms σ` on a backward edge. -/
@[simp]
theorem rot_ofPerms_true (v : V) (k : K) :
    (ofPerms σ).rot (v, (k, true)) = ((σ k).symm v, (k, false)) :=
  rfl

/-- The forward edge labelled `k` at `v` leads to `σ k v`. -/
@[simp]
theorem neighbor_ofPerms_false (v : V) (k : K) : (ofPerms σ).neighbor v (k, false) = σ k v :=
  rfl

/-- The backward edge labelled `k` at `v` leads to `(σ k)⁻¹ v`. -/
@[simp]
theorem neighbor_ofPerms_true (v : V) (k : K) :
    (ofPerms σ).neighbor v (k, true) = (σ k).symm v :=
  rfl

/-- A permutation moves as many points of a finite set out of the set as its inverse does. -/
private theorem card_filter_symm_apply_notMem [DecidableEq V] (τ : Equiv.Perm V)
    (S : Finset V) : #{v ∈ S | τ.symm v ∉ S} = #{v ∈ S | τ v ∉ S} := by
  have h : #{v ∈ S | τ.symm v ∈ S} = #{v ∈ S | τ v ∈ S} := by
    refine card_nbij' τ.symm τ (fun v hv ↦ ?_) (fun v hv ↦ ?_) (fun v _ ↦ by simp)
      (fun v _ ↦ by simp) <;>
    · simp only [coe_filter] at hv ⊢
      simpa using hv.symm
  have h₁ := card_filter_add_card_filter_not (s := S) fun v ↦ τ.symm v ∈ S
  have h₂ := card_filter_add_card_filter_not (s := S) fun v ↦ τ v ∈ S
  omega

variable [Fintype V] [DecidableEq V] [Fintype K]

/-- **The edges leaving a set** in the multigraph of `σ`: each permutation `σ k` contributes twice
the number of points of `S` it moves out of `S`, once along `σ k` and once along its inverse. -/
theorem card_interedges_compl_ofPerms (S : Finset V) :
    #((ofPerms σ).interedges S Sᶜ) = 2 * ∑ k, #{v ∈ S | σ k v ∉ S} := by
  rw [interedges, card_filter, sum_product, mul_sum]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, neighbor_ofPerms_false,
    neighbor_ofPerms_true, mem_compl]
  rw [sum_comm]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [sum_add_distrib, two_mul]
  nth_rw 1 [← card_filter_symm_apply_notMem (σ k) S]
  rw [card_filter, card_filter]
  rfl

/-- **Edge expansion from moved points**: on at least two vertices, if the permutations together
move at least `c |S|` points of every set `S` of at most half of the vertices out of `S`, then the
edge expansion of their multigraph is at least `2 c`. -/
theorem le_edgeExpansion_ofPerms [Nontrivial V] {c : ℝ}
    (h : ∀ S : Finset V, 2 * #S ≤ Fintype.card V → c * #S ≤ ∑ k, #{v ∈ S | σ k v ∉ S}) :
    2 * c ≤ (ofPerms σ).edgeExpansion := by
  refine (ofPerms σ).le_edgeExpansion_iff.2 fun S hS ↦ ?_
  rw [card_interedges_compl_ofPerms]
  have := h S hS
  push_cast at this ⊢
  linarith

omit [DecidableEq V] in
/-- **The Dirichlet form of a permutation multigraph**: the correlation of `f` with its walk is
`𝔼 f²` minus `1 / (2 |K|)` times the total squared change `∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2` of `f`
along the permutations. -/
theorem expect_mul_walk_ofPerms [Nonempty K] (f : V → ℝ) :
    𝔼 v, f v * (ofPerms σ).walk f v =
      (𝔼 v, f v ^ 2) - (∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2) / (2 * Fintype.card K) := by
  have hK : (0 : ℝ) < Fintype.card K := Nat.cast_pos.2 Fintype.card_pos
  have hwalk (v : V) : (ofPerms σ).walk f v =
      (∑ k, (f (σ k v) + f ((σ k).symm v))) / (2 * Fintype.card K) := by
    rw [walk_apply, Fintype.expect_eq_sum_div_card, Fintype.sum_prod_type, Fintype.card_prod,
      Fintype.card_bool]
    simp only [Fintype.sum_bool, neighbor_ofPerms_true, neighbor_ofPerms_false,
      add_comm (f ((σ _).symm v))]
    push_cast
    ring
  have hsymm (k : K) : ∑ v, f v * f ((σ k).symm v) = ∑ v, f v * f (σ k v) := by
    rw [← Equiv.sum_comp (σ k)]
    simp [mul_comm]
  have hcross (k : K) : ∑ v, (f (σ k v) - f v) ^ 2 =
      2 * ∑ v, f v ^ 2 - 2 * ∑ v, f v * f (σ k v) := by
    simp only [sub_sq, sum_add_distrib, sum_sub_distrib, Equiv.sum_comp (σ k) (fun v ↦ f v ^ 2),
      mul_sum]
    ring_nf
    simp only [← sum_mul, mul_comm (f _) (f _)]
  calc 𝔼 v, f v * (ofPerms σ).walk f v
      = (∑ v, f v * ∑ k, (f (σ k v) + f ((σ k).symm v))) / (2 * Fintype.card K) /
          Fintype.card V := by
        simp only [hwalk, Fintype.expect_eq_sum_div_card, ← mul_div_assoc, ← sum_div]
    _ = (2 * ∑ k, ∑ v, f v * f (σ k v)) / (2 * Fintype.card K) / Fintype.card V := by
        congr 2
        simp only [mul_sum, mul_add, sum_add_distrib]
        rw [sum_comm, sum_comm (f := fun v k ↦ f v * f ((σ k).symm v))]
        simp only [hsymm, ← two_mul, mul_sum]
    _ = _ := by
        simp only [Fintype.expect_eq_sum_div_card, ← sum_div, hcross, sum_sub_distrib, sum_const,
          card_univ, nsmul_eq_mul, ← mul_sum]
        field_simp
        ring

omit [DecidableEq V] in
/-- **A Poincaré inequality bounds the second eigenvalue** of a permutation multigraph on at least
two vertices: if `c 𝔼 f² ≤ ∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2` for every `f` of expectation zero, then
`λ₂ ≤ 1 - c / (2 |K|)`. -/
theorem secondEigenvalue_ofPerms_le [Nonempty K] [Nontrivial V] {c : ℝ}
    (h : ∀ f : V → ℝ, 𝔼 v, f v = 0 → c * (𝔼 v, f v ^ 2) ≤ ∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2) :
    (ofPerms σ).secondEigenvalue ≤ 1 - c / (2 * Fintype.card K) := by
  refine (ofPerms σ).secondEigenvalue_le_iff.2 fun f hf ↦ ?_
  have hK : (0 : ℝ) < 2 * Fintype.card K := by
    have := Fintype.card_pos (α := K)
    positivity
  calc 𝔼 v, f v * (ofPerms σ).walk f v
      = (𝔼 v, f v ^ 2) - (∑ k, 𝔼 v, (f (σ k v) - f v) ^ 2) / (2 * Fintype.card K) :=
        expect_mul_walk_ofPerms σ f
    _ ≤ (𝔼 v, f v ^ 2) - c * (𝔼 v, f v ^ 2) / (2 * Fintype.card K) := by
        have := div_le_div_of_nonneg_right (h f hf) hK.le
        linarith
    _ = (1 - c / (2 * Fintype.card K)) * 𝔼 v, f v ^ 2 := by ring

end Cslib.RotationMap
