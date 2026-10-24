/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Union
import Mathlib.Combinatorics.Hall.Finite

/-!
# Bipartite perfect matching

A bipartite graph with `n` left and `n` right vertices is a subgraph of the complete bipartite
graph `K_{n,n}`, given by the indicator of its edges, one bit for each pair `(i, j)` of a left
vertex `i` and a right vertex `j` (`Cslib.Circuits.BipartiteMatching.graph`, numbering the pairs by
`finProdFinEquiv`). It has a *perfect matching* when some bijection `σ` from the left to the right
vertices uses only edges, `(i, σ i)` for every `i` (`BipartiteMatching.HasPerfectMatching`). The
bipartite perfect matching function `Cslib.Circuits.bipartitePerfectMatching n` of the `n * n`
possible edges says whether the graph has a perfect matching. It is monotone
(`monotone_bipartitePerfectMatching`): adding edges keeps a perfect matching.

Relabelling the left and the right vertices along bijections preserves perfect matchings
(`BipartiteMatching.hasPerfectMatching_comp_iff`). A graph has no perfect matching when a set of
left vertices has fewer neighbours (`BipartiteMatching.not_hasPerfectMatching_of_card_lt`), the easy
direction of Hall's theorem; Hall's theorem itself, from Mathlib's
`Finset.all_card_le_biUnion_card_iff_existsInjective'`, says that a perfect matching exists exactly
when every set of left vertices has at least as many neighbours
(`BipartiteMatching.hasPerfectMatching_iff_forall_card_le`).

## Main definitions

* `Cslib.Circuits.BipartiteMatching.HasPerfectMatching`: a bipartite graph on `V × V` has a
  perfect matching.
* `Cslib.Circuits.BipartiteMatching.graph`: the bipartite graph of an input.
* `Cslib.Circuits.bipartitePerfectMatching`: the bipartite perfect matching function.

## Main results

* `Cslib.Circuits.monotone_bipartitePerfectMatching`: the function is monotone.
* `Cslib.Circuits.BipartiteMatching.hasPerfectMatching_comp_iff`: relabelling vertices.
* `Cslib.Circuits.BipartiteMatching.hasPerfectMatching_iff_forall_card_le`: Hall's theorem.

## References

* [R. Raz and A. Wigderson, *Monotone circuits for matching require linear
  depth*][RazWigderson1992]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

namespace BipartiteMatching

variable {V W : Type*}

/-- A bipartite graph whose left and right vertices are both indexed by `V`, given by the indicator
of its edges `(left, right)`, has a *perfect matching*: a bijection `σ` from the left to the right
vertices with `(v, σ v)` an edge for every `v`. -/
def HasPerfectMatching (G : V × V → Bool) : Prop :=
  ∃ σ : Equiv.Perm V, ∀ v, G (v, σ v) = true

/-- Whether a bipartite graph on a finite vertex type has a perfect matching is decidable. -/
instance [Fintype V] [DecidableEq V] (G : V × V → Bool) : Decidable (HasPerfectMatching G) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm V, ∀ v, G (v, σ v) = true))

/-- Relabelling the left vertices along `hL` and the right vertices along `hR` preserves perfect
matchings. -/
theorem hasPerfectMatching_comp_iff (hL hR : W ≃ V) (G : V × V → Bool) :
    HasPerfectMatching (fun e : W × W => G (hL e.1, hR e.2)) ↔ HasPerfectMatching G := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨hL.symm.trans (σ.trans hR), fun v => ?_⟩
    simpa using hσ (hL.symm v)
  · rintro ⟨σ, hσ⟩
    refine ⟨hL.trans (σ.trans hR.symm), fun w => ?_⟩
    simpa using hσ (hL w)

/-- **Hall's condition is necessary**: if the edges from a set `S` of left vertices all end in a
set `T` of fewer right vertices, the graph has no perfect matching. -/
theorem not_hasPerfectMatching_of_card_lt {G : V × V → Bool} {S T : Finset V}
    (hST : ∀ v ∈ S, ∀ w, G (v, w) = true → w ∈ T) (hcard : T.card < S.card) :
    ¬HasPerfectMatching G := by
  rintro ⟨σ, hσ⟩
  exact absurd (Finset.card_le_card_of_injOn σ (fun v hv => hST v hv _ (hσ v))
    σ.injective.injOn) (not_le.mpr hcard)

/-- **Hall's theorem** for bipartite graphs on `V × V`: a perfect matching exists exactly when
every set of left vertices has at least as many neighbours. -/
theorem hasPerfectMatching_iff_forall_card_le [Fintype V] [DecidableEq V] (G : V × V → Bool) :
    HasPerfectMatching G ↔ ∀ S : Finset V,
      S.card ≤ (S.biUnion fun v => Finset.univ.filter fun w => G (v, w) = true).card := by
  rw [Finset.all_card_le_biUnion_card_iff_existsInjective']
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, σ.injective, fun v => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hσ v⟩⟩
  · rintro ⟨f, hf, hfG⟩
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf),
      fun v => (Finset.mem_filter.mp (hfG v)).2⟩

/-- Adding edges keeps a perfect matching. -/
theorem HasPerfectMatching.mono {G H : V × V → Bool} (hG : HasPerfectMatching G) (h : G ≤ H) :
    HasPerfectMatching H := by
  obtain ⟨σ, hσ⟩ := hG
  exact ⟨σ, fun v => Bool.eq_true_of_true_le (hσ v ▸ h (v, σ v))⟩

variable {n : ℕ}

/-- The bipartite graph of an input: the left vertex `i` and the right vertex `j` are adjacent when
the bit numbered `finProdFinEquiv (i, j)` is one. -/
def graph (x : BitString (n * n)) : Fin n × Fin n → Bool :=
  fun e => x (finProdFinEquiv e)

end BipartiteMatching

open BipartiteMatching

/-- The bipartite perfect matching function of the `n * n` possible edges of the complete
bipartite graph `K_{n,n}`: whether the graph of the input (`BipartiteMatching.graph`) has a perfect
matching. -/
def bipartitePerfectMatching (n : ℕ) : BooleanFunction (n * n) :=
  fun x => decide (HasPerfectMatching (graph x))

variable {n : ℕ}

/-- The bipartite perfect matching function is true exactly on graphs with a perfect matching. -/
theorem bipartitePerfectMatching_eq_true_iff {x : BitString (n * n)} :
    bipartitePerfectMatching n x = true ↔ HasPerfectMatching (graph x) :=
  decide_eq_true_iff

/-- The bipartite perfect matching function is monotone: adding edges keeps a perfect matching. -/
theorem monotone_bipartitePerfectMatching : Monotone (bipartitePerfectMatching n) := by
  intro x y hxy
  by_cases h : bipartitePerfectMatching n x = true
  · rw [h, bipartitePerfectMatching_eq_true_iff.mpr
      ((bipartitePerfectMatching_eq_true_iff.mp h).mono fun e => hxy (finProdFinEquiv e))]
  · rw [Bool.not_eq_true] at h
    rw [h]
    exact Bool.false_le _

end Cslib.Circuits
