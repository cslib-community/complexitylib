/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/OddCycleTransversal.lean`)

public import Complexity.Foundations.Combinatorics.SimpleGraph.Separator
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Finset.Card
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Odd cycle transversals and the compression lemma

An *odd cycle transversal* of a simple graph `G` is a set `S` of vertices whose deletion leaves a
bipartite graph (`SimpleGraph.IsOddCycleTransversal`): the subgraph induced on `Sᶜ` is
`IsBipartite`, that is, `2`-colourable. Equivalently, some Boolean colouring of `G` is proper on
the edges outside `S` (`SimpleGraph.isOddCycleTransversal_iff_exists_bool`), or every closed walk of
odd length visits `S` (`SimpleGraph.isOddCycleTransversal_iff_forall_odd_walk`). The last form
explains the name: a closed walk of odd length contains an odd cycle on its vertices.

## The compression lemma

Iterative compression for odd cycle transversal [ReedSmithVetta2004] [CyganEtAl2015, Section 4.4]
starts from an odd cycle transversal `W` with a colouring `c₀` that is proper off `W`, and asks for
an odd cycle transversal of at most `k` vertices. Guess the part `D ⊆ W` of the new solution inside
`W` and a colouring `σ` of `W` that is proper off `D`. A vertex `v ∉ W` adjacent to `w ∈ W \ D`
must, if it survives, receive the colour `!σ w`. Relative to `c₀`, it keeps its colour when
`σ w ≠ c₀ v` (`SimpleGraph.OddCycleTransversal.keepTerminals`), and flips it when `σ w = c₀ v`
(`SimpleGraph.OddCycleTransversal.flipTerminals`). The edges of `G - W` join vertices of opposite
`c₀`-colours, so along a walk of `G - W` a vertex keeps its colour exactly when its neighbour does.

The guess extends to a solution `D ∪ X` with `X ∩ W = ∅` exactly when `X` separates the keep
terminals from the flip terminals in `G - W`, that is, when `W ∪ X` separates them in `G`
(`SimpleGraph.isOddCycleTransversal_card_le_iff`):

* given a solution `S`, take `D = S ∩ W`, `σ` its colouring and `X = S \ W`
  (`SimpleGraph.OddCycleTransversal.isSeparator_of_proper`);
* given a separator `X`, every vertex outside `W` keeps or flips its colour according to a side
  labelling that is constant along the edges of `G - W - X`, true on the keep terminals and false
  on the flip terminals (`SimpleGraph.OddCycleTransversal.proper_of_side`).

There are `3 ^ |W|` guesses: each vertex of `W` is deleted or receives one of two colours. The
minimum separator of each guess is a minimum vertex cut, computed in
`Cslib.Algorithms.Lean.IterativeCompression.OddCycleTransversal`. The statement here is
combinatorial; `W` is any odd cycle transversal, and `|W| = k + 1` only matters for the running
time.

## Main definitions

* `SimpleGraph.IsOddCycleTransversal`: deleting `S` leaves a bipartite graph.
* `SimpleGraph.OddCycleTransversal.keepTerminals`, `SimpleGraph.OddCycleTransversal.flipTerminals`:
  the vertices outside `W` whose colour a guess `(D, σ)` forces to be kept or flipped.

## Main results

* `SimpleGraph.isOddCycleTransversal_iff_exists_bool`: a colouring proper off `S`.
* `SimpleGraph.isOddCycleTransversal_iff_forall_odd_walk`: every odd closed walk visits `S`.
* `SimpleGraph.isOddCycleTransversal_empty_iff`: `∅` is an odd cycle transversal exactly when `G`
  is bipartite.
* `SimpleGraph.OddCycleTransversal.isSeparator_of_proper`,
  `SimpleGraph.OddCycleTransversal.proper_of_side`: the two directions of the compression lemma.
* `SimpleGraph.isOddCycleTransversal_card_le_iff`: the compression lemma.

## References

* [B. Reed, K. Smith, A. Vetta, *Finding odd cycle transversals*][ReedSmithVetta2004]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `S` is an *odd cycle transversal* of `G`: the subgraph induced on the complement of `S` is
bipartite. -/
def IsOddCycleTransversal (S : Set V) : Prop :=
  (G.induce Sᶜ).IsBipartite

variable {G} {S T : Set V}

/-- A graph is bipartite exactly when it has a proper Boolean colouring. -/
private theorem isBipartite_iff_exists_bool {W : Type*} {H : SimpleGraph W} :
    H.IsBipartite ↔ ∃ c : W → Bool, ∀ ⦃u v⦄, H.Adj u v → c u ≠ c v := by
  constructor
  · rintro ⟨C⟩
    exact ⟨finTwoEquiv ∘ C, fun u v h => finTwoEquiv.injective.ne (C.valid h)⟩
  · rintro ⟨c, hc⟩
    simpa using (Coloring.mk c fun h => hc h).colorable

/-- `S` is an odd cycle transversal exactly when some Boolean colouring of `G` is proper on the
edges with both endpoints outside `S`. -/
theorem isOddCycleTransversal_iff_exists_bool :
    G.IsOddCycleTransversal S ↔
      ∃ c : V → Bool, ∀ ⦃u v⦄, G.Adj u v → u ∉ S → v ∉ S → c u ≠ c v := by
  rw [IsOddCycleTransversal, isBipartite_iff_exists_bool]
  constructor
  · rintro ⟨c, hc⟩
    classical
    refine ⟨fun v => if h : v ∈ S then false else c ⟨v, h⟩, fun u v huv hu hv => ?_⟩
    simp only [hu, hv, ↓reduceDIte]
    exact hc (u := ⟨u, hu⟩) (v := ⟨v, hv⟩) huv
  · rintro ⟨c, hc⟩
    exact ⟨fun v => c v, fun u v huv => hc huv u.2 v.2⟩

/-- `S` is an odd cycle transversal exactly when every closed walk of odd length visits `S`. -/
theorem isOddCycleTransversal_iff_forall_odd_walk :
    G.IsOddCycleTransversal S ↔
      ∀ (u : V) (p : G.Walk u u), Odd p.length → ∃ x ∈ p.support, x ∈ S := by
  constructor
  · rintro hS u p hodd
    by_contra hp
    push Not at hp
    obtain ⟨C⟩ := hS
    let c : (G.induce Sᶜ).Coloring Bool := recolorOfEquiv _ finTwoEquiv C
    have hlen : (p.induce Sᶜ hp).length = p.length :=
      (Walk.length_map _ _).symm.trans (congrArg Walk.length (Walk.map_induce p hp))
    exact iff_not_self ((c.odd_length_iff_not_congr (p.induce Sᶜ hp)).mp (hlen ▸ hodd)).symm
  · intro h
    rw [IsOddCycleTransversal, IsBipartite, two_colorable_iff_forall_loop_even]
    intro u p
    by_contra hp
    rw [Nat.not_even_iff_odd] at hp
    obtain ⟨x, hx, hxS⟩ := h _ (p.map (Embedding.induce Sᶜ).toHom)
      ((Walk.length_map (Embedding.induce Sᶜ).toHom p) ▸ hp)
    have hx' : x ∈ p.support.map (Embedding.induce Sᶜ).toHom := (Walk.support_map _ p) ▸ hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx'
    exact y.2 hxS

theorem IsOddCycleTransversal.mono (h : G.IsOddCycleTransversal S) (hST : S ⊆ T) :
    G.IsOddCycleTransversal T := by
  rw [isOddCycleTransversal_iff_exists_bool] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun u v huv hu hv => hc huv (fun h => hu (hST h)) fun h => hv (hST h)⟩

theorem IsOddCycleTransversal.anti {H : SimpleGraph V} (h : G.IsOddCycleTransversal S)
    (hHG : H ≤ G) : H.IsOddCycleTransversal S := by
  rw [isOddCycleTransversal_iff_exists_bool] at h ⊢
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun u v huv => hc (hHG huv)⟩

theorem isOddCycleTransversal_univ : G.IsOddCycleTransversal Set.univ :=
  isOddCycleTransversal_iff_exists_bool.mpr ⟨fun _ => false, fun _ _ _ hu => (hu trivial).elim⟩

/-- `∅` is an odd cycle transversal exactly when `G` is bipartite. -/
theorem isOddCycleTransversal_empty_iff : G.IsOddCycleTransversal ∅ ↔ G.IsBipartite := by
  rw [isOddCycleTransversal_iff_exists_bool, isBipartite_iff_exists_bool]
  simp only [Set.mem_empty_iff_false, not_false_eq_true, forall_const]

namespace OddCycleTransversal

variable (G)

/-- The vertices outside `W` that keep their `c₀`-colour under the guess `(D, σ)`: those with a
neighbour `w ∈ W \ D` such that `σ w ≠ c₀ v`. -/
def keepTerminals (W D : Set V) (σ c₀ : V → Bool) : Set V :=
  {v | v ∉ W ∧ ∃ w ∈ W, w ∉ D ∧ G.Adj w v ∧ σ w ≠ c₀ v}

/-- The vertices outside `W` that flip their `c₀`-colour under the guess `(D, σ)`: those with a
neighbour `w ∈ W \ D` such that `σ w = c₀ v`. -/
def flipTerminals (W D : Set V) (σ c₀ : V → Bool) : Set V :=
  {v | v ∉ W ∧ ∃ w ∈ W, w ∉ D ∧ G.Adj w v ∧ σ w = c₀ v}

variable {G}

theorem mem_keepTerminals {W D : Set V} {σ c₀ : V → Bool} {v : V} :
    v ∈ keepTerminals G W D σ c₀ ↔ v ∉ W ∧ ∃ w ∈ W, w ∉ D ∧ G.Adj w v ∧ σ w ≠ c₀ v :=
  Iff.rfl

theorem mem_flipTerminals {W D : Set V} {σ c₀ : V → Bool} {v : V} :
    v ∈ flipTerminals G W D σ c₀ ↔ v ∉ W ∧ ∃ w ∈ W, w ∉ D ∧ G.Adj w v ∧ σ w = c₀ v :=
  Iff.rfl

/-- **Compression lemma, solution to separator.** Let `c₀` be proper off `W` and `c` proper off
`S`. Take `D = S ∩ W` and any `σ` agreeing with `c` on `W \ S`. Then `W ∪ S` separates the keep
terminals from the flip terminals of `(D, σ)`: along a walk of `G - (W ∪ S)` both colourings are
proper, so `c v = c₀ v` holds at one end exactly when it holds at the other. -/
theorem isSeparator_of_proper {W : Set V} {c₀ c σ : V → Bool}
    (hc₀ : ∀ ⦃u v⦄, G.Adj u v → u ∉ W → v ∉ W → c₀ u ≠ c₀ v)
    (hc : ∀ ⦃u v⦄, G.Adj u v → u ∉ S → v ∉ S → c u ≠ c v)
    (hσ : ∀ w ∈ W, w ∉ S → σ w = c w) :
    G.IsSeparator (keepTerminals G W (S ∩ W) σ c₀) (flipTerminals G W (S ∩ W) σ c₀) (W ∪ S) := by
  refine isSeparator_of_forall_adj (fun v => c v == c₀ v) (fun u v huv hu hv => ?_) ?_ ?_
  · simp only [Set.mem_union, not_or] at hu hv
    have h1 := hc huv hu.2 hv.2
    have h2 := hc₀ huv hu.1 hv.1
    revert h1 h2
    cases c u <;> cases c v <;> cases c₀ u <;> cases c₀ v <;> decide
  · rintro a ⟨-, w, hw, hwD, hwa, hne⟩ ha
    simp only [Set.mem_union, not_or] at ha
    have hwS : w ∉ S := fun h => hwD ⟨h, hw⟩
    have h1 := hc hwa hwS ha.2
    rw [hσ w hw hwS] at hne
    revert h1 hne
    cases c w <;> cases c a <;> cases c₀ a <;> decide
  · rintro b ⟨-, w, hw, hwD, hwb, heq⟩ hb
    simp only [Set.mem_union, not_or] at hb
    have hwS : w ∉ S := fun h => hwD ⟨h, hw⟩
    have h1 := hc hwb hwS hb.2
    rw [hσ w hw hwS] at heq
    revert h1 heq
    cases c w <;> cases c b <;> cases c₀ b <;> decide

/-- **Compression lemma, separator to solution.** Let `c₀` be proper off `W`, let `σ` be proper on
`W \ D`, and let `side` be constant along the edges of `G - (W ∪ X)`, true on the keep terminals
outside `X` and false on the flip terminals outside `X`. Then any colouring `c` that follows `σ` on
`W` and keeps (`side v = true`) or flips (`side v = false`) the colour `c₀ v` outside `W` is proper
off `D ∪ X`. -/
theorem proper_of_side {W D X : Set V} {c₀ σ side c : V → Bool}
    (hc₀ : ∀ ⦃u v⦄, G.Adj u v → u ∉ W → v ∉ W → c₀ u ≠ c₀ v)
    (hσ : ∀ ⦃u v⦄, G.Adj u v → u ∈ W → v ∈ W → u ∉ D → v ∉ D → σ u ≠ σ v)
    (hside : ∀ ⦃u v⦄, G.Adj u v → u ∉ W → v ∉ W → u ∉ X → v ∉ X → side u = side v)
    (hkeep : ∀ v ∈ keepTerminals G W D σ c₀, v ∉ X → side v = true)
    (hflip : ∀ v ∈ flipTerminals G W D σ c₀, v ∉ X → side v = false)
    (hcW : ∀ v ∈ W, c v = σ v) (hcW' : ∀ v ∉ W, c v = (c₀ v == side v)) :
    ∀ ⦃u v⦄, G.Adj u v → u ∉ D ∪ X → v ∉ D ∪ X → c u ≠ c v := by
  -- One endpoint in `W`, the other outside.
  have hmixed : ∀ ⦃u v⦄, G.Adj u v → u ∈ W → v ∉ W → u ∉ D → v ∉ X → c u ≠ c v := by
    intro u v huv hu hv huD hvX
    rw [hcW u hu, hcW' v hv]
    by_cases h : σ u = c₀ v
    · rw [hflip v ⟨hv, u, hu, huD, huv, h⟩ hvX, h]
      cases c₀ v <;> decide
    · rw [hkeep v ⟨hv, u, hu, huD, huv, h⟩ hvX]
      revert h
      cases σ u <;> cases c₀ v <;> decide
  intro u v huv hu hv
  simp only [Set.mem_union, not_or] at hu hv
  by_cases huW : u ∈ W <;> by_cases hvW : v ∈ W
  · rw [hcW u huW, hcW v hvW]
    exact hσ huv huW hvW hu.1 hv.1
  · exact hmixed huv huW hvW hu.1 hv.2
  · exact (hmixed huv.symm hvW huW hv.1 hu.2).symm
  · rw [hcW' u huW, hcW' v hvW, hside huv huW hvW hu.2 hv.2]
    have h := hc₀ huv huW hvW
    revert h
    cases c₀ u <;> cases c₀ v <;> cases side v <;> decide

/-- The canonical side labelling of a separator: reachability from the keep terminals in
`G - (W ∪ X)`. -/
private theorem exists_side_of_isSeparator {W D X : Set V} {σ c₀ : V → Bool}
    (hX : G.IsSeparator (keepTerminals G W D σ c₀) (flipTerminals G W D σ c₀) (W ∪ X)) :
    ∃ side : V → Bool,
      (∀ ⦃u v⦄, G.Adj u v → u ∉ W → v ∉ W → u ∉ X → v ∉ X → side u = side v) ∧
      (∀ v ∈ keepTerminals G W D σ c₀, v ∉ X → side v = true) ∧
      (∀ v ∈ flipTerminals G W D σ c₀, v ∉ X → side v = false) := by
  classical
  set R := G.reachAvoiding (keepTerminals G W D σ c₀) (W ∪ X)
  have hR : ∀ ⦃u v⦄, G.Adj u v → v ∉ W → v ∉ X → u ∈ R → v ∈ R := fun u v huv hvW hvX hu =>
    mem_reachAvoiding_of_adj hu huv (by simp only [Set.mem_union, not_or]; exact ⟨hvW, hvX⟩)
  refine ⟨fun v => decide (v ∈ R), fun u v huv huW hvW huX hvX => ?_, fun v hv hvX => ?_,
    fun v hv hvX => ?_⟩
  · exact decide_eq_decide.mpr ⟨hR huv hvW hvX, hR huv.symm huW huX⟩
  · exact decide_eq_true (mem_reachAvoiding_of_mem hv
      (by simp only [Set.mem_union, not_or]; exact ⟨hv.1, hvX⟩))
  · exact decide_eq_false (isSeparator_iff_forall_not_mem_reachAvoiding.mp hX v hv)

/-- **Compression lemma** [ReedSmithVetta2004] [CyganEtAl2015, Section 4.4]. Let `W` be a set with
a colouring `c₀` that is proper off `W`. Then `G` has an odd cycle transversal of at most `k`
vertices exactly when there are `D ⊆ W`, a colouring `σ` proper on `W \ D`, and `X` disjoint from
`W` such that `W ∪ X` separates the keep terminals from the flip terminals of `(D, σ)` and
`|D| + |X| ≤ k`. -/
theorem _root_.SimpleGraph.isOddCycleTransversal_card_le_iff {W : Finset V}
    {c₀ : V → Bool} (hc₀ : ∀ ⦃u v⦄, G.Adj u v → u ∉ W → v ∉ W → c₀ u ≠ c₀ v) (k : ℕ) :
    (∃ S : Finset V, G.IsOddCycleTransversal S ∧ S.card ≤ k) ↔
      ∃ (D X : Finset V) (σ : V → Bool), D ⊆ W ∧ Disjoint X W ∧
        (∀ ⦃u v⦄, G.Adj u v → u ∈ W → v ∈ W → u ∉ D → v ∉ D → σ u ≠ σ v) ∧
        G.IsSeparator (keepTerminals G W D σ c₀) (flipTerminals G W D σ c₀) (↑W ∪ ↑X) ∧
        D.card + X.card ≤ k := by
  classical
  constructor
  · rintro ⟨S, hS, hk⟩
    obtain ⟨c, hc⟩ := isOddCycleTransversal_iff_exists_bool.mp hS
    refine ⟨S ∩ W, S \ W, c, Finset.inter_subset_right, Finset.sdiff_disjoint,
      fun u v huv _ _ hu hv => hc huv (fun h => hu (Finset.mem_inter.mpr ⟨h, ‹_›⟩))
        fun h => hv (Finset.mem_inter.mpr ⟨h, ‹_›⟩), ?_, ?_⟩
    · have hsep := isSeparator_of_proper (S := (S : Set V)) hc₀ hc fun _ _ _ => rfl
      rw [Finset.coe_inter] at *
      rwa [Finset.coe_sdiff, Set.union_sdiff_self]
    · rw [Finset.card_inter_add_card_sdiff]
      exact hk
  · rintro ⟨D, X, σ, -, -, hσ, hX, hk⟩
    obtain ⟨side, hside, hkeep, hflip⟩ := exists_side_of_isSeparator hX
    refine ⟨D ∪ X, ?_, (Finset.card_union_le D X).trans hk⟩
    rw [isOddCycleTransversal_iff_exists_bool, Finset.coe_union]
    exact ⟨fun v => if v ∈ W then σ v else (c₀ v == side v),
      proper_of_side hc₀ hσ (fun u v huv hu hv => hside huv hu hv) hkeep hflip
        (fun v hv => by simp only [Finset.mem_coe.mp hv, ↓reduceIte])
        fun v hv => by simp only [Finset.mem_coe.not.mp hv, ↓reduceIte]⟩

end OddCycleTransversal

end SimpleGraph
