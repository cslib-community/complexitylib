/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Sym.Card

/-!
# The clique function

A Boolean function of the possible edges of a graph on `n` vertices, the unordered pairs of distinct
vertices (`Cslib.Circuits.Clique.Edge`), reads its input as a graph (`Cslib.Circuits.Clique.graph`).
The `k`-clique function `Cslib.Circuits.clique n k` says whether that graph has a clique of `k`
vertices.

Two families of inputs are used to prove lower bounds for it: the complete graph on a set of `k`
vertices (`Cslib.Circuits.Clique.ofFinset`), which has a `k`-clique, and the complete multipartite
graph of a colouring with fewer than `k` colours (`Cslib.Circuits.Clique.ofColoring`), which has
none.

## Main definitions

* `Cslib.Circuits.Clique.Edge`, `Cslib.Circuits.Clique.edgeCount`: the possible edges.
* `Cslib.Circuits.Clique.graph`: the graph of an input.
* `Cslib.Circuits.Clique.Contains`: the input contains all edges inside a set of vertices.
* `Cslib.Circuits.clique`: the `k`-clique function.
* `Cslib.Circuits.Clique.ofFinset`, `Cslib.Circuits.Clique.ofColoring`: test inputs.

## Main results

* `Cslib.Circuits.Clique.edgeCount_eq_choose`: there are `n.choose 2` possible edges.
* `Cslib.Circuits.clique_eq_true_iff`: the clique function in terms of `SimpleGraph.IsNClique`.
* `Cslib.Circuits.clique_ofFinset`, `Cslib.Circuits.clique_ofColoring`: the test inputs.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Clique

variable {n r : ℕ}

/-- The possible edges of a graph on `n` vertices: unordered pairs of distinct vertices. -/
abbrev Edge (n : ℕ) : Type := {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- The number of possible edges of a graph on `n` vertices. -/
abbrev edgeCount (n : ℕ) : ℕ := Fintype.card (Edge n)

theorem edgeCount_eq_choose (n : ℕ) : edgeCount n = n.choose 2 := by
  rw [edgeCount, Sym2.card_subtype_not_diag, Fintype.card_fin]

/-- A numbering of the possible edges by the inputs of a circuit. -/
noncomputable def edgeEquiv (n : ℕ) : Edge n ≃ Fin (edgeCount n) := Fintype.equivFin _

/-- The graph of an input: its edges are the possible edges set to `true`. -/
def graph (x : Fin (edgeCount n) → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬e.IsDiag, x (edgeEquiv n ⟨e, h⟩) = true}

/-- The input `x` contains all edges between the vertices of `s`. -/
def Contains (x : Fin (edgeCount n) → Bool) (s : Finset (Fin n)) : Prop :=
  ∀ e : Edge n, e.1.toFinset ⊆ s → x (edgeEquiv n e) = true

noncomputable instance (x : Fin (edgeCount n) → Bool) (s : Finset (Fin n)) :
    Decidable (Contains x s) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The edge between two distinct vertices. -/
def edge {u v : Fin n} (h : u ≠ v) : Edge n := ⟨s(u, v), by simpa using h⟩

@[simp] theorem toFinset_edge {u v : Fin n} (h : u ≠ v) : (edge h).1.toFinset = {u, v} :=
  Sym2.toFinset_mk_eq

theorem Contains.mono {x : Fin (edgeCount n) → Bool} {s t : Finset (Fin n)} (hst : s ⊆ t)
    (h : Contains x t) : Contains x s :=
  fun e he => h e (he.trans hst)

/-- Containing all edges inside `s` is being a clique of the graph. -/
theorem contains_iff_isClique {x : Fin (edgeCount n) → Bool} {s : Finset (Fin n)} :
    Contains x s ↔ (graph x).IsClique (s : Set (Fin n)) := by
  constructor
  · intro h u hu v hv huv
    rw [graph, SimpleGraph.fromEdgeSet_adj]
    exact ⟨⟨_, h (edge huv) (by
      simp only [toFinset_edge, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv⟩)⟩, huv⟩
  · rintro h ⟨z, hz⟩ hzs
    induction z using Sym2.ind with
    | h u v =>
      have huv : u ≠ v := by simpa using hz
      have hadj := h (hzs (by simp)) (hzs (by simp)) huv
      rw [graph, SimpleGraph.fromEdgeSet_adj] at hadj
      exact hadj.1.2

/-- The complete graph on `s`, as an input. -/
noncomputable def ofFinset (s : Finset (Fin n)) : Fin (edgeCount n) → Bool :=
  fun i => decide (((edgeEquiv n).symm i).1.toFinset ⊆ s)

@[simp] theorem ofFinset_edgeEquiv (s : Finset (Fin n)) (e : Edge n) :
    ofFinset s (edgeEquiv n e) = decide (e.1.toFinset ⊆ s) := by
  simp [ofFinset]

theorem contains_ofFinset (s : Finset (Fin n)) : Contains (ofFinset s) s :=
  fun e he => by simpa using he

/-- In the complete graph on `s`, the sets of at least two vertices with all edges inside are the
subsets of `s`. -/
theorem subset_of_contains_ofFinset {s t : Finset (Fin n)} (ht : 2 ≤ t.card)
    (h : Contains (ofFinset s) t) : t ⊆ s := by
  intro v hv
  obtain ⟨u, hu, huv⟩ := t.exists_mem_ne (by omega) v
  have := h (edge (Ne.symm huv)) (by simp [Finset.insert_subset_iff, hu, hv])
  rw [ofFinset_edgeEquiv, decide_eq_true_iff, toFinset_edge] at this
  exact this (Finset.mem_insert_self v {u})

/-- The complete multipartite graph of a colouring, as an input: two vertices are adjacent when
they have different colours. -/
noncomputable def ofColoring (c : Fin n → Fin r) : Fin (edgeCount n) → Bool :=
  fun i => decide (∀ u ∈ ((edgeEquiv n).symm i).1.toFinset,
    ∀ v ∈ ((edgeEquiv n).symm i).1.toFinset, c u = c v → u = v)

/-- In the graph of a colouring, the sets with all edges inside are those coloured injectively. -/
theorem contains_ofColoring_iff {c : Fin n → Fin r} {s : Finset (Fin n)} :
    Contains (ofColoring c) s ↔ Set.InjOn c s := by
  constructor
  · intro h u hu v hv hc
    by_contra huv
    have := h (edge huv) (by
      simp only [toFinset_edge, Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv⟩)
    simp only [ofColoring, Equiv.symm_apply_apply, toFinset_edge, decide_eq_true_iff] at this
    exact huv (this u (by simp) v (by simp) hc)
  · intro h e he
    simp only [ofColoring, Equiv.symm_apply_apply, decide_eq_true_iff]
    exact fun u hu v hv => h (he hu) (he hv)

/-- A set with all edges inside in the graph of a colouring with `r` colours has at most `r`
vertices. -/
private theorem card_le_of_contains_ofColoring {c : Fin n → Fin r} {s : Finset (Fin n)}
    (h : Contains (ofColoring c) s) : s.card ≤ r := by
  simpa using Finset.card_le_card_of_injOn c (fun _ _ => Finset.mem_univ _)
    (contains_ofColoring_iff.1 h)

/-- The sets of `k` vertices. -/
abbrev CliqueSet (n k : ℕ) : Type := ↥((Finset.univ : Finset (Fin n)).powersetCard k)

/-- The colourings of `n` vertices with `r` colours. -/
abbrev Coloring (n r : ℕ) : Type := Fin n → Fin r

end Clique

open Clique

/-- The `k`-clique function on graphs with `n` vertices: whether the graph of the input has a
clique of `k` vertices. -/
noncomputable def clique (n k : ℕ) : BooleanFunction (edgeCount n) :=
  fun x => decide (∃ s : Finset (Fin n), s.card = k ∧ Contains x s)

variable {n k r : ℕ}

theorem clique_eq_true_iff {x : Fin (edgeCount n) → Bool} :
    clique n k x = true ↔ ∃ s : Finset (Fin n), (graph x).IsNClique k s := by
  simp only [clique, decide_eq_true_iff, contains_iff_isClique, SimpleGraph.isNClique_iff]
  exact exists_congr fun s => and_comm

/-- The complete graph on `k` vertices has a `k`-clique. -/
theorem clique_ofFinset {s : Finset (Fin n)} (hs : s.card = k) : clique n k (ofFinset s) = true :=
  decide_eq_true ⟨s, hs, contains_ofFinset s⟩

/-- The complete multipartite graph of a colouring with fewer than `k` colours has no
`k`-clique. -/
theorem clique_ofColoring (hr : r < k) (c : Fin n → Fin r) : clique n k (ofColoring c) = false :=
  decide_eq_false fun ⟨_, hs, h⟩ => absurd (card_le_of_contains_ofColoring h) (by omega)

/-- The clique function is monotone. -/
theorem clique_le_clique {x y : Fin (edgeCount n) → Bool} (h : ∀ i, x i ≤ y i) :
    clique n k x ≤ clique n k y := by
  by_cases hx : clique n k x = true
  · obtain ⟨s, hs, hxs⟩ := of_decide_eq_true hx
    rw [show clique n k y = true from decide_eq_true ⟨s, hs, fun e he => by
      have := h (edgeEquiv n e)
      rw [hxs e he] at this
      exact Bool.eq_true_of_true_le this⟩]
    exact Bool.le_true _
  · rw [Bool.eq_false_iff.2 hx]
    exact Bool.false_le _

end Cslib.Circuits
