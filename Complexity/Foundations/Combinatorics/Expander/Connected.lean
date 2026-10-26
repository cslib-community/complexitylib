/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Cheeger
public import Complexity.Foundations.Combinatorics.Expander.Hom
public import Complexity.Foundations.Combinatorics.Expander.Mixing

/-!
# Connectivity and spectral expansion

Two facts connect the spectral expansion `λ(G)` of a regular multigraph with its connectivity,
and they are the two ends of Reingold's algorithm for undirected connectivity
[Reingold][Reingold2008] [Arora and Barak, Section 21.4][AroraBarak09].

**A connected graph has a spectral gap.** If `G` is connected, a set `S` of at most half of the
vertices has an edge leaving it, so the edge expansion of `G` is at least `1 / |V|`, and Cheeger's
inequality bounds the second eigenvalue of the walk operator by `1 - 1 / (2 |V|² |D|²)`. When at
least half of the edges at every vertex are self-loops, the walk operator is positive semidefinite
(`expect_mul_walk_nonneg`), so this also bounds `λ(G)`
(`spectralExpansion_le_of_preconnected`). Reingold uses the sharper bound `1 - 1 / (D N²)` for
connected nonbipartite graphs, due to Alon and Sudakov [Reingold, Lemma 2.5][Reingold2008]; any
inverse polynomial gap suffices for his algorithm. Self-loops are often added for this purpose by
passing to the lazy graph (`Cslib.RotationMap.lazy`), whose spectral expansion edge expansion
bounds in the same way
(`Cslib.RotationMap.spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`); the bound
here applies to any graph that already has enough self-loops, without relabelling.

**In a good expander, short walks reach every vertex.** If `λ(G) ^ t (|V| - 1) < 1`, then for any
two vertices `u` and `v` some walk of length exactly `t` leads from `u` to `v`
(`exists_neighbor_pow_eq`): by the mixing lemma, a random walk of length `t` from `u` ends at `v`
with probability at least `(1 - λ(G) ^ t (|V| - 1)) / |V| > 0`. So an expander with `λ(G) ≤ c < 1`
has diameter `O(log |V|)`; Reingold derives this from vertex expansion instead
[Reingold, Proposition 2.2][Reingold2008].

## Main results

* `Cslib.RotationMap.interedges_compl_nonempty`: in a connected graph, an edge leaves every
  nonempty proper set of vertices.
* `Cslib.RotationMap.expect_mul_walk_nonneg`: if at least half of the edges at every vertex are
  self-loops, the walk operator is positive semidefinite.
* `Cslib.RotationMap.spectralExpansion_le_of_preconnected`: a connected graph with at least half
  self-loops at every vertex has `λ(G) ≤ 1 - 1 / (2 |V|² |D|²)`.
* `Cslib.RotationMap.exists_neighbor_pow_eq`: if `λ(G) ^ t (|V| - 1) < 1`, every vertex is
  reachable from every other by a walk of length exactly `t`.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D)

section Gap

variable [Fintype V] [DecidableEq V] [Fintype D]

/-- In a connected graph, some edge leaves every nonempty proper set of vertices. -/
theorem interedges_compl_nonempty (hG : G.toSimpleGraph.Preconnected) {S : Finset V}
    (hS : S.Nonempty) (hS' : S ≠ univ) : (G.interedges S Sᶜ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl : ∀ v ∈ (S : Set V), ∀ i, G.neighbor v i ∈ (S : Set V) := by
    intro v hv i
    by_contra hvi
    have : (v, i) ∈ G.interedges S Sᶜ := mem_interedges.2 ⟨hv, mem_compl.2 hvi⟩
    rw [h] at this
    exact notMem_empty _ this
  obtain ⟨x, hx⟩ := hS
  exact hS' (eq_univ_of_forall fun y ↦ G.mem_of_reachable hcl hx (hG x y))

omit [Fintype V] in
/-- If at least half of the edges at `v` are self-loops, the average over `i : D` of `c` on
self-loops and `-c` on non-loop edges is nonnegative for `c ≥ 0`. -/
private theorem expect_ite_neighbor_eq_nonneg {v : V}
    (hv : Fintype.card D ≤ 2 * G.edgeCount v v) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ 𝔼 i, (if G.neighbor v i = v then c else -c) := by
  rw [Fintype.expect_eq_sum_div_card]
  refine div_nonneg ?_ (Nat.cast_nonneg _)
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcard := card_filter_add_card_filter_not (s := (univ : Finset D))
    (fun i ↦ G.neighbor v i = v)
  rw [card_univ] at hcard
  have hle : (#{i | ¬G.neighbor v i = v} : ℝ) ≤ #{i | G.neighbor v i = v} := by
    rw [edgeCount] at hv
    exact_mod_cast (by omega : #{i | ¬G.neighbor v i = v} ≤ #{i | G.neighbor v i = v})
  nlinarith

/-- If at least half of the edges at every vertex are self-loops, the walk operator is positive
semidefinite: `0 ≤ 𝔼 v, f v * G.walk f v` for every `f`. -/
theorem expect_mul_walk_nonneg (hG : ∀ v, Fintype.card D ≤ 2 * G.edgeCount v v)
    (f : V → ℝ) : 0 ≤ 𝔼 v, f v * G.walk f v := by
  -- a self-loop contributes `f v ^ 2`, any other edge at least `-(f v ^ 2 + f w ^ 2) / 2`
  set g : V → V → ℝ := fun v w ↦ if w = v then f v ^ 2 else -(f v ^ 2 + f w ^ 2) / 2 with hg
  have hfg (v w : V) : g v w ≤ f v * f w := by
    simp only [hg]
    split_ifs with h
    · rw [h, sq]
    · nlinarith [sq_nonneg (f v + f w)]
  -- the far ends of the edges other than self-loops are the near ends of such edges
  have hsymm : 𝔼 v, 𝔼 i, (if G.neighbor v i = v then 0 else -f (G.neighbor v i) ^ 2 / 2) =
      𝔼 v, 𝔼 i, (if G.neighbor v i = v then 0 else -f v ^ 2 / 2 : ℝ) := by
    rw [G.expect_expect_neighbor_comm fun v w ↦ (if w = v then 0 else -f w ^ 2 / 2 : ℝ)]
    simp only [eq_comm]
  have h (v : V) (i : D) : g v (G.neighbor v i) =
      (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2 / 2) +
        if G.neighbor v i = v then 0 else -f (G.neighbor v i) ^ 2 / 2 := by
    simp only [hg]
    split_ifs <;> ring
  have hsplit : 𝔼 v, 𝔼 i, g v (G.neighbor v i) =
      𝔼 v, 𝔼 i, (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2) := by
    simp only [h, expect_add_distrib]
    rw [hsymm, ← expect_add_distrib]
    refine expect_congr rfl fun v _ ↦ ?_
    rw [← expect_add_distrib]
    refine expect_congr rfl fun i _ ↦ ?_
    split_ifs <;> ring
  calc (0 : ℝ) ≤ 𝔼 v, 𝔼 i, (if G.neighbor v i = v then f v ^ 2 else -f v ^ 2) :=
        expect_nonneg fun v _ ↦ G.expect_ite_neighbor_eq_nonneg (hG v) (sq_nonneg _)
    _ = 𝔼 v, 𝔼 i, g v (G.neighbor v i) := hsplit.symm
    _ ≤ 𝔼 v, 𝔼 i, f v * f (G.neighbor v i) :=
        expect_le_expect fun v _ ↦ expect_le_expect fun i _ ↦ hfg v _
    _ = 𝔼 v, f v * G.walk f v := by simp only [walk_apply, mul_expect]

/-- **A connected graph has a spectral gap.** If `G` is connected and at least half of the edges at
every vertex are self-loops, then `λ(G) ≤ 1 - 1 / (2 |V|² |D|²)`: an edge leaves every set of at
most half of the vertices, which bounds the second eigenvalue by Cheeger's inequality
[Hoory, Linial and Wigderson, Theorem 2.4][HooryLinialWigderson2006], and the self-loops make the
walk operator positive semidefinite, so that the second eigenvalue is `λ(G)`. Compare the lazy
graph, whose walk is positive semidefinite by construction
(`spectralExpansion_lazy_le_of_mul_card_le_card_interedges_compl`). -/
theorem spectralExpansion_le_of_preconnected
    (hloop : ∀ v, Fintype.card D ≤ 2 * G.edgeCount v v)
    (hconn : G.toSimpleGraph.Preconnected) :
    G.spectralExpansion ≤ 1 - 1 / (2 * Fintype.card V ^ 2 * Fintype.card D ^ 2) := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [G.spectralExpansion_eq_zero_of_subsingleton, sub_nonneg]
    rcases Nat.eq_zero_or_pos (2 * Fintype.card V ^ 2 * Fintype.card D ^ 2) with h | h
    · rw [← Nat.cast_ofNat, ← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_mul, h,
        Nat.cast_zero, div_zero]
      exact zero_le_one
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast h
  have hN : (0 : ℝ) < Fintype.card V := Nat.cast_pos.2 Fintype.card_pos
  rw [G.spectralExpansion_eq_secondEigenvalue_of_nonneg (G.expect_mul_walk_nonneg hloop),
    secondEigenvalue_le_iff]
  intro f hf
  have hc : ∀ S : Finset V, 2 * #S ≤ Fintype.card V →
      1 / (Fintype.card V : ℝ) * #S ≤ #(G.interedges S Sᶜ) := by
    intro S hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    have hlt : #S < Fintype.card V := by
      have := hne.card_pos
      omega
    have hne' : S ≠ univ := fun h ↦ by rw [h, card_univ] at hlt; exact lt_irrefl _ hlt
    have h1 : (1 : ℝ) ≤ #(G.interedges S Sᶜ) :=
      Nat.one_le_cast.2 (G.interedges_compl_nonempty hconn hne hne').card_pos
    have h2 : 1 / (Fintype.card V : ℝ) * #S ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one hN]
      exact_mod_cast hlt.le
    exact h2.trans h1
  refine (G.expect_mul_walk_le_of_mul_card_le_card_interedges_compl (by positivity) hc hf).trans ?_
  apply le_of_eq
  congr 1
  rw [div_pow, one_pow, div_div]
  ring

end Gap

section Walks

variable [Fintype V] [Fintype D] [Nonempty D]

/-- **Short walks in an expander reach every vertex.** If `λ(G) ^ t (|V| - 1) < 1`, then from every
vertex `u` some walk of length exactly `t` leads to any given vertex `v`: by the mixing lemma, a
uniformly random walk of length `t` from `u` ends at `v` with probability at least
`(1 - λ(G) ^ t (|V| - 1)) / |V|`. -/
theorem exists_neighbor_pow_eq {t : ℕ} (h : G.spectralExpansion ^ t * (Fintype.card V - 1) < 1)
    (u v : V) : ∃ k : Fin t → D, (G.pow t).neighbor u k = v := by
  classical
  by_contra hk
  simp only [not_exists] at hk
  set N : ℝ := (Fintype.card V : ℝ) with hN
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  set f : V → ℝ := fun w ↦ if w = u then 1 else 0 with hf
  set g : V → ℝ := fun w ↦ if w = v then 1 else 0 with hg
  have hexp (x : V) : 𝔼 w, (if w = x then 1 else 0 : ℝ) = 1 / N := by
    rw [Fintype.expect_eq_sum_div_card, sum_ite_eq', ite_eq_left (mem_univ _)]
  have hexp2 (x : V) : 𝔼 w, (if w = x then 1 else 0 : ℝ) ^ 2 = 1 / N := by
    rw [← hexp x]
    exact expect_congr rfl fun w _ ↦ by split_ifs <;> norm_num
  -- no walk of length `t` from `u` ends at `v`
  have hW : (G.walk ^ t) g u = 0 := by
    rw [← walk_pow, walk_apply]
    exact Finset.expect_eq_zero fun k _ ↦ ite_eq_right (hk k)
  have hcorr : 𝔼 w, f w * (G.walk ^ t) g w = 0 := by
    refine Finset.expect_eq_zero fun w _ ↦ ?_
    simp only [hf]
    split_ifs with hw
    · rw [hw, hW, mul_zero]
    · rw [zero_mul]
  have hmix := G.sq_expect_mul_walk_pow_sub_le t f g
  rw [hcorr, hexp u, hexp v, hexp2 u, hexp2 v] at hmix
  -- so `1 ≤ (λ(G) ^ t (N - 1)) ^ 2`, against the hypothesis
  have e₁ : (0 - 1 / N * (1 / N)) ^ 2 = 1 / N ^ 4 := by
    field_simp
    ring
  have e₂ : G.spectralExpansion ^ (2 * t) * (1 / N - (1 / N) ^ 2) * (1 / N - (1 / N) ^ 2) =
      (G.spectralExpansion ^ t * (N - 1)) ^ 2 / N ^ 4 := by
    rw [pow_mul']
    field_simp
  rw [e₁, e₂, div_le_div_iff_of_pos_right (by positivity)] at hmix
  have hx : 0 ≤ G.spectralExpansion ^ t * (N - 1) := by
    refine mul_nonneg (pow_nonneg G.spectralExpansion_nonneg t) ?_
    rw [sub_nonneg, hN]
    exact Nat.one_le_cast.2 (Fintype.card_pos_iff.2 ⟨u⟩)
  nlinarith

end Walks

end Cslib.RotationMap
