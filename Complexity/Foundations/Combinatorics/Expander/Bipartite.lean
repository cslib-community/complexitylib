/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Vertex expansion of bipartite graphs

A bipartite graph between left vertices `ι` and right vertices `κ` is a decidable relation
`G : ι → κ → Prop`, with the neighbourhoods `Finset.bipartiteAbove` / `Finset.bipartiteBelow` and
the double-counting lemmas of Mathlib. A set `S` of left vertices has *neighbours* `N(S)`
(`Cslib.Bipartite.neighbors`) and *unique neighbours* `U(S)`
(`Cslib.Bipartite.uniqueNeighbors`), the right vertices adjacent to exactly one vertex of `S`
[GuruswamiRudraSudan2025, Definitions 11.2.1 and 11.3.3]. The graph is a *vertex expander* for
sets of size at most `k` with factor `α` (`Cslib.Bipartite.IsVertexExpander`) when every such `S`
has `α |S| ≤ |N(S)|`; this is the `(n, m, c, γ, α)` bipartite expander of
[GuruswamiRudraSudan2025, Definition 11.2.2] with `k = γ n`, except that we only require left
degrees *at most* `c` (`Cslib.Bipartite.IsLeftBounded`) rather than exactly `c`.

The *unique-neighbour lemma* (`Cslib.Bipartite.IsVertexExpander.le_card_uniqueNeighbors`): if left
degrees are at most `c`, then `(2 α - c) |S| ≤ |U(S)|` for `|S| ≤ k`. For a lossless expander
`α = c (1 - ε)` this is `|U(S)| ≥ c (1 - 2 ε) |S|` [GuruswamiRudraSudan2025, Lemma 11.3.4]
[GuruswamiSharma2010, Lemma 3]. It drives the distance and decoding analysis of expander codes
[SipserSpielman1996] in `Complexity.Foundations.Data.Code.ExpanderCode`.

## Main definitions

* `Cslib.Bipartite.neighbors`, `Cslib.Bipartite.uniqueNeighbors`: neighbours and unique neighbours.
* `Cslib.Bipartite.IsLeftBounded`, `Cslib.Bipartite.IsBiregular`: degree conditions.
* `Cslib.Bipartite.IsVertexExpander`: vertex expansion of small left sets.

## Main results

* `Cslib.Bipartite.two_mul_card_neighbors_le`: `2 |N(S)| ≤ |U(S)| + c |S|`.
* `Cslib.Bipartite.IsVertexExpander.le_card_uniqueNeighbors`: the unique-neighbour lemma.
* `Cslib.Bipartite.IsBiregular.card_mul_eq`: `n c = m d` for a `(c, d)`-biregular graph.

## References

* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2025], §11.2–11.3
* [V. Guruswami, A. Sharma, *Expander codes and their decoding*][GuruswamiSharma2010]
* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996]
-/

@[expose] public section

namespace Cslib.Bipartite

open Finset

variable {ι κ : Type*} [Fintype κ] (G : ι → κ → Prop) [∀ i j, Decidable (G i j)]

/-- The neighbours `N(S)` of a set `S` of left vertices: the right vertices adjacent to some vertex
of `S`. -/
def neighbors (S : Finset ι) : Finset κ :=
  {j | ∃ i ∈ S, G i j}

/-- The unique neighbours `U(S)` of a set `S` of left vertices: the right vertices adjacent to
exactly one vertex of `S` [GuruswamiRudraSudan2025, Definition 11.3.3]. -/
def uniqueNeighbors (S : Finset ι) : Finset κ :=
  {j | #(S.bipartiteBelow G j) = 1}

/-- Every left vertex has at most `c` neighbours. -/
def IsLeftBounded (c : ℕ) : Prop :=
  ∀ i, #(univ.bipartiteAbove G i) ≤ c

/-- The graph is `(c, d)`-biregular: every left vertex has exactly `c` neighbours and every right
vertex exactly `d`. -/
def IsBiregular [Fintype ι] (c d : ℕ) : Prop :=
  (∀ i, #(univ.bipartiteAbove G i) = c) ∧ ∀ j, #(univ.bipartiteBelow G j) = d

/-- **Vertex expansion** [GuruswamiRudraSudan2025, Definition 11.2.2]: every set `S` of at most `k`
left vertices has at least `α |S|` neighbours. -/
def IsVertexExpander (k : ℕ) (α : ℝ) : Prop :=
  ∀ S : Finset ι, #S ≤ k → α * #S ≤ #(neighbors G S)

variable {G}

@[simp] theorem mem_neighbors {S : Finset ι} {j : κ} : j ∈ neighbors G S ↔ ∃ i ∈ S, G i j := by
  simp [neighbors]

theorem mem_uniqueNeighbors {S : Finset ι} {j : κ} :
    j ∈ uniqueNeighbors G S ↔ #(S.bipartiteBelow G j) = 1 := by
  simp [uniqueNeighbors]

/-- Unique neighbours are neighbours. -/
theorem uniqueNeighbors_subset_neighbors (S : Finset ι) : uniqueNeighbors G S ⊆ neighbors G S := by
  intro j hj
  obtain ⟨i, hi⟩ := card_eq_one.1 (mem_uniqueNeighbors.1 hj)
  have : i ∈ S.bipartiteBelow G j := hi ▸ mem_singleton_self i
  rw [mem_bipartiteBelow] at this
  exact mem_neighbors.2 ⟨i, this⟩

/-- A `(c, d)`-biregular graph has left degrees at most `c`. -/
theorem IsBiregular.isLeftBounded [Fintype ι] {c d : ℕ} (hG : IsBiregular G c d) :
    IsLeftBounded G c :=
  fun i => (hG.1 i).le

/-- If left degrees are at most `c`, a set `S` has at most `c |S|` neighbours. -/
theorem card_neighbors_le {c : ℕ} (hG : IsLeftBounded G c) (S : Finset ι) :
    #(neighbors G S) ≤ c * #S := by
  classical
  have : neighbors G S ⊆ S.biUnion fun i => univ.bipartiteAbove G i := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := mem_neighbors.1 hj
    exact mem_biUnion.2 ⟨i, hi, (mem_bipartiteAbove G).2 ⟨mem_univ _, hij⟩⟩
  refine (card_le_card this).trans (card_biUnion_le.trans ?_)
  rw [mul_comm, ← smul_eq_mul]
  exact sum_le_card_nsmul _ _ _ fun i _ => hG i

/-- The edges leaving `S`, counted at their right endpoints in `N(S)`: at most `c |S|`. -/
theorem sum_card_bipartiteBelow_neighbors_le {c : ℕ} (hG : IsLeftBounded G c) (S : Finset ι) :
    ∑ j ∈ neighbors G S, #(S.bipartiteBelow G j) ≤ c * #S := by
  rw [← sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow, mul_comm, ← smul_eq_mul]
  refine sum_le_card_nsmul _ _ _ fun i hi => (card_le_card fun j hj => ?_).trans (hG i)
  rw [mem_bipartiteAbove] at hj ⊢
  exact ⟨mem_univ _, hj.2⟩

/-- Double counting the edges between `S` and `N(S)`: a neighbour that is not unique receives at
least two edges, so `2 |N(S)| ≤ |U(S)| + c |S|`. -/
theorem two_mul_card_neighbors_le {c : ℕ} (hG : IsLeftBounded G c) (S : Finset ι) :
    2 * #(neighbors G S) ≤ #(uniqueNeighbors G S) + c * #S := by
  have hU : #(uniqueNeighbors G S) =
      ∑ j ∈ neighbors G S, if #(S.bipartiteBelow G j) = 1 then 1 else 0 := by
    rw [sum_boole, Nat.cast_id]
    congr 1
    ext j
    rw [mem_filter, mem_uniqueNeighbors]
    exact ⟨fun h => ⟨uniqueNeighbors_subset_neighbors (G := G) S (mem_uniqueNeighbors.2 h), h⟩,
      fun h => h.2⟩
  have hle : ∀ j ∈ neighbors G S,
      2 ≤ #(S.bipartiteBelow G j) + if #(S.bipartiteBelow G j) = 1 then 1 else 0 := by
    intro j hj
    obtain ⟨i, hi, hij⟩ := mem_neighbors.1 hj
    have hpos : 0 < #(S.bipartiteBelow G j) :=
      card_pos.2 ⟨i, (mem_bipartiteBelow G).2 ⟨hi, hij⟩⟩
    split_ifs with hu <;> omega
  calc 2 * #(neighbors G S) = ∑ j ∈ neighbors G S, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ j ∈ neighbors G S,
        (#(S.bipartiteBelow G j) + if #(S.bipartiteBelow G j) = 1 then 1 else 0) :=
      sum_le_sum hle
    _ = ∑ j ∈ neighbors G S, #(S.bipartiteBelow G j) + #(uniqueNeighbors G S) := by
      rw [sum_add_distrib, hU]
    _ ≤ #(uniqueNeighbors G S) + c * #S := by
      have := sum_card_bipartiteBelow_neighbors_le hG S
      omega

/-- **The unique-neighbour lemma** [GuruswamiRudraSudan2025, Lemma 11.3.4]
[GuruswamiSharma2010, Lemma 3]. If left degrees are at most `c` and sets of at most `k` left
vertices expand by `α`, then every such set `S` has at least `(2 α - c) |S|` unique neighbours.
With `α = c (1 - ε)` this is the source's `|U(S)| ≥ c (1 - 2 ε) |S|`; the source assumes
`c`-left-regularity, which we weaken to left degrees at most `c`. -/
theorem IsVertexExpander.le_card_uniqueNeighbors {c k : ℕ} {α : ℝ} (hG : IsLeftBounded G c)
    (hE : IsVertexExpander G k α) {S : Finset ι} (hS : #S ≤ k) :
    (2 * α - c) * #S ≤ #(uniqueNeighbors G S) := by
  have h1 := hE S hS
  have h2 : (2 * #(neighbors G S) : ℝ) ≤ #(uniqueNeighbors G S) + c * #S := by
    exact_mod_cast two_mul_card_neighbors_le hG S
  nlinarith

/-- A `(c, d)`-biregular graph with `n` left and `m` right vertices has `n c = m d` edges. -/
theorem IsBiregular.card_mul_eq [Fintype ι] {c d : ℕ} (hG : IsBiregular G c d) :
    Fintype.card ι * c = Fintype.card κ * d :=
  card_mul_eq_card_mul G (fun i _ => hG.1 i) fun j _ => hG.2 j

end Cslib.Bipartite
