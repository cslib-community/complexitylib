/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.AugmentingPath
public import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted Bipartite Matching: Potentials and Linear-Programming Duality

Costs, perfect matchings and vertex potentials on the edge-indicator representation
`G : L × R → Bool` of `CslibFrontier.Algorithms.Lean.MaxFlow.BipartiteMatching`, with weak duality
and
complementary slackness for the minimum-cost (perfect) matching problem ([Schrijver2003], Ch. 17;
[Kuhn1955]). The executable Hungarian method and Egerváry's strong duality theorem for the
assignment problem are in `CslibFrontier.Algorithms.Lean.MaxFlow.Hungarian`.

## Conventions

Costs take values in an ordered additive commutative monoid or group `α` and are **minimized**.
Potentials `y : L → α` and `z : R → α` are *feasible* when every reduced cost
`c (u, v) - y u - z v` of an edge is nonnegative, i.e. `y u + z v ≤ c (u, v)`; an edge is *tight*
when equality holds. This is the reduced-cost convention of primal-dual algorithms for
minimum-cost flow, so the lemmas below are stated for arbitrary matchings and graphs, not only for
the complete bipartite graph of the assignment problem. Maximum-weight problems are obtained by
negating costs.

## Main definitions

* `IsPerfectMatching G M`: `M` is a matching of `G` covering every left and every right vertex.
* `matchingCost c M`: the total cost `∑ e ∈ M, c e`.
* `IsFeasiblePotential G c y z`: `y u + z v ≤ c (u, v)` for every edge of `G`.
* `IsMinCostPerfectMatching G c M`: `M` is a perfect matching of minimum cost.
* `permMatching σ`: the perfect matching `{(u, σ u)}` of a permutation `σ` of `V`.

## Main results

* `IsMatching.sum_potential_eq`: `∑ e ∈ M, (y e.1 + z e.2)` splits into the potentials of the
  matched left and right vertices.
* `IsMatching.sum_matched_potential_le_cost` (**weak duality**, any matching): the potentials of
  the matched vertices sum to at most the cost; `IsMatching.sum_matched_potential_eq_cost_iff`
  (**complementary slackness**): equality holds iff every edge of `M` is tight.
* `IsPerfectMatching.potential_le_cost`, `IsPerfectMatching.potential_eq_cost_iff`: the same for
  perfect matchings, with all potentials summed.
* `IsPerfectMatching.isMinCostPerfectMatching_of_tight`: a perfect matching that is tight for
  feasible potentials has minimum cost.
* `isPerfectMatching_permMatching`, `exists_eq_permMatching`, `matchingCost_permMatching`:
  perfect matchings of `V × V` are exactly the permutation matchings, with cost
  `∑ u, c (u, σ u)`.

## References

* [A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*][Schrijver2003]
* [H. W. Kuhn, *The Hungarian Method for the Assignment Problem*][Kuhn1955]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

open Finset

section Defs

variable {L R α : Type*}

/-- `M` is a perfect matching of `G`: a matching covering every left and every right vertex. -/
@[expose] def IsPerfectMatching [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]
    (G : L × R → Bool) (M : Finset (L × R)) : Prop :=
  IsMatching G M ∧ matchedLeft M = univ ∧ matchedRight M = univ

/-- Total cost of the edges of `M`. -/
@[expose] def matchingCost [AddCommMonoid α] (c : L × R → α) (M : Finset (L × R)) : α :=
  ∑ e ∈ M, c e

/-- Potentials `y`, `z` are feasible for the cost `c` on `G` if every edge has nonnegative reduced
cost: `y u + z v ≤ c (u, v)`. -/
@[expose] def IsFeasiblePotential [Add α] [LE α] (G : L × R → Bool) (c : L × R → α) (y : L → α)
    (z : R → α) : Prop :=
  ∀ u v, G (u, v) = true → y u + z v ≤ c (u, v)

/-- `M` is a minimum-cost perfect matching of `G` for the cost `c`. -/
@[expose] def IsMinCostPerfectMatching [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]
    [AddCommMonoid α] [LE α] (G : L × R → Bool) (c : L × R → α) (M : Finset (L × R)) : Prop :=
  IsPerfectMatching G M ∧ ∀ M', IsPerfectMatching G M' → matchingCost c M ≤ matchingCost c M'

end Defs

section Sums

variable {L R α : Type*} [DecidableEq L] [DecidableEq R] [AddCommMonoid α]
variable {G : L × R → Bool} {M : Finset (L × R)}

omit [DecidableEq R] in
theorem IsMatching.sum_fst_eq (hM : IsMatching G M) (f : L → α) :
    ∑ e ∈ M, f e.1 = ∑ u ∈ matchedLeft M, f u := by
  rw [matchedLeft, sum_image]
  rintro ⟨a, b⟩ ha ⟨a', b'⟩ hb (h : a = a')
  subst h
  rw [hM.2.1 a b b' ha hb]

omit [DecidableEq L] in
theorem IsMatching.sum_snd_eq (hM : IsMatching G M) (f : R → α) :
    ∑ e ∈ M, f e.2 = ∑ v ∈ matchedRight M, f v := by
  rw [matchedRight, sum_image]
  rintro ⟨a, b⟩ ha ⟨a', b'⟩ hb (h : b = b')
  subst h
  rw [hM.2.2 a a' b ha hb]

/-- The potential of a matching splits over its matched left and right vertices. -/
theorem IsMatching.sum_potential_eq (hM : IsMatching G M) (y : L → α) (z : R → α) :
    ∑ e ∈ M, (y e.1 + z e.2) = ∑ u ∈ matchedLeft M, y u + ∑ v ∈ matchedRight M, z v := by
  rw [sum_add_distrib, hM.sum_fst_eq, hM.sum_snd_eq]

theorem IsPerfectMatching.sum_potential_eq [Fintype L] [Fintype R] (hM : IsPerfectMatching G M)
    (y : L → α) (z : R → α) :
    ∑ e ∈ M, (y e.1 + z e.2) = ∑ u, y u + ∑ v, z v := by
  rw [hM.1.sum_potential_eq, hM.2.1, hM.2.2]

end Sums

section Duality

variable {L R α : Type*} [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)} {c : L × R → α} {y : L → α} {z : R → α}

/-- **Weak duality** for an arbitrary matching: the potentials of the matched vertices sum to at
most the cost. -/
theorem IsMatching.sum_matched_potential_le_cost [AddCommMonoid α] [PartialOrder α]
    [IsOrderedAddMonoid α] (hM : IsMatching G M) (hf : IsFeasiblePotential G c y z) :
    ∑ u ∈ matchedLeft M, y u + ∑ v ∈ matchedRight M, z v ≤ matchingCost c M := by
  rw [← hM.sum_potential_eq]
  exact sum_le_sum fun e he => hf e.1 e.2 (hM.1 e he)

/-- **Complementary slackness** for an arbitrary matching: weak duality is an equality iff every
edge of the matching is tight. -/
theorem IsMatching.sum_matched_potential_eq_cost_iff [AddCommMonoid α] [PartialOrder α]
    [IsOrderedCancelAddMonoid α] (hM : IsMatching G M) (hf : IsFeasiblePotential G c y z) :
    ∑ u ∈ matchedLeft M, y u + ∑ v ∈ matchedRight M, z v = matchingCost c M ↔
      ∀ e ∈ M, y e.1 + z e.2 = c e := by
  rw [← hM.sum_potential_eq, matchingCost]
  exact sum_eq_sum_iff_of_le fun e he => hf e.1 e.2 (hM.1 e he)

variable [Fintype L] [Fintype R]

/-- **Weak duality** for perfect matchings: `∑ y + ∑ z ≤ cost M`. -/
theorem IsPerfectMatching.potential_le_cost [AddCommMonoid α] [PartialOrder α]
    [IsOrderedAddMonoid α] (hM : IsPerfectMatching G M) (hf : IsFeasiblePotential G c y z) :
    ∑ u, y u + ∑ v, z v ≤ matchingCost c M := by
  have h := hM.1.sum_matched_potential_le_cost hf
  rwa [hM.2.1, hM.2.2] at h

/-- **Complementary slackness** for perfect matchings. -/
theorem IsPerfectMatching.potential_eq_cost_iff [AddCommMonoid α] [PartialOrder α]
    [IsOrderedCancelAddMonoid α] (hM : IsPerfectMatching G M) (hf : IsFeasiblePotential G c y z) :
    ∑ u, y u + ∑ v, z v = matchingCost c M ↔ ∀ e ∈ M, y e.1 + z e.2 = c e := by
  have h := hM.1.sum_matched_potential_eq_cost_iff hf
  rwa [hM.2.1, hM.2.2] at h

/-- A perfect matching all of whose edges are tight for feasible potentials has minimum cost, and
its cost equals the total potential. -/
theorem IsPerfectMatching.isMinCostPerfectMatching_of_tight [AddCommMonoid α] [PartialOrder α]
    [IsOrderedCancelAddMonoid α] (hM : IsPerfectMatching G M) (hf : IsFeasiblePotential G c y z)
    (ht : ∀ e ∈ M, y e.1 + z e.2 = c e) : IsMinCostPerfectMatching G c M := by
  refine ⟨hM, fun M' hM' => ?_⟩
  rw [← (hM.potential_eq_cost_iff hf).mpr ht]
  exact hM'.potential_le_cost hf

end Duality

section Permutation

variable {V α : Type*} [DecidableEq V] [Fintype V]

/-- The perfect matching `{(u, σ u)}` of a permutation `σ`. -/
@[expose] def permMatching (σ : Equiv.Perm V) : Finset (V × V) :=
  univ.image fun u => (u, σ u)

theorem mem_permMatching {σ : Equiv.Perm V} {e : V × V} : e ∈ permMatching σ ↔ σ e.1 = e.2 := by
  obtain ⟨u, v⟩ := e
  simp only [permMatching, mem_image, mem_univ, true_and, Prod.mk.injEq]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    rfl
  · rintro h
    exact ⟨u, rfl, h⟩

theorem isPerfectMatching_permMatching (σ : Equiv.Perm V) :
    IsPerfectMatching (fun _ => true) (permMatching σ) := by
  refine ⟨⟨fun _ _ => rfl, fun u v₁ v₂ h₁ h₂ => ?_, fun u₁ u₂ v h₁ h₂ => ?_⟩, ?_, ?_⟩
  · exact (mem_permMatching.mp h₁).symm.trans (mem_permMatching.mp h₂)
  · exact σ.injective ((mem_permMatching.mp h₁).trans (mem_permMatching.mp h₂).symm)
  · refine eq_univ_of_forall fun u => mem_matchedLeft.mpr ⟨σ u, mem_permMatching.mpr rfl⟩
  · refine eq_univ_of_forall fun v => mem_matchedRight.mpr ⟨σ.symm v, mem_permMatching.mpr ?_⟩
    simp

theorem matchingCost_permMatching [AddCommMonoid α] (c : V × V → α) (σ : Equiv.Perm V) :
    matchingCost c (permMatching σ) = ∑ u, c (u, σ u) := by
  rw [matchingCost, permMatching, sum_image]
  intro a _ b _ h
  exact (Prod.mk.inj h).1

/-- Every perfect matching of `V × V` is the matching of a permutation. -/
theorem exists_eq_permMatching {G : V × V → Bool} {M : Finset (V × V)}
    (hM : IsPerfectMatching G M) : ∃ σ : Equiv.Perm V, M = permMatching σ := by
  have hex : ∀ u, ∃ v, (u, v) ∈ M := fun u => mem_matchedLeft.mp (hM.2.1 ▸ mem_univ u)
  choose f hf using hex
  have hinj : Function.Injective f := fun a b h =>
    hM.1.2.2 a b (f a) (hf a) (h ▸ hf b)
  let σ : Equiv.Perm V := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ext fun e => ?_⟩
  obtain ⟨u, v⟩ := e
  rw [mem_permMatching]
  change (u, v) ∈ M ↔ f u = v
  constructor
  · intro h
    exact hM.1.2.1 u (f u) v (hf u) h
  · rintro rfl
    exact hf u

end Permutation

end Cslib.Algorithms.Lean.MaxFlow
