/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Sunflower
public import Mathlib.Data.Fintype.Pi

/-!
# Lower bounds for the sunflower lemma

The sunflower lemma (`containsSunflower_of_forall_card_le`) finds a sunflower with `p` petals in
every family of more than `(p - 1) ^ w * w!` sets of size at most `w`. Erdős and Rado also showed
that the factor `(p - 1) ^ w` cannot be dropped [Erdős and Rado][ErdosRado1960]: the graphs
`{(i, f i) | i : ι}` of all functions `f : ι → β` form a family of `|β| ^ |ι|` sets of size `|ι|`
without a sunflower with `|β| + 1` petals (`not_containsSunflower_graphFamily`). Indeed, among
`|β| + 1` graphs, at each coordinate `i` some pair agrees. Thus every petal is contained in the
core, which is impossible for two distinct petals.
Taking `ι = Fin w` and `β = Fin (p - 1)` gives `(p - 1) ^ w` sets of size `w` without a sunflower
with `p` petals (`exists_card_eq_pow_not_containsSunflower`).

For `w = 1` the two bounds meet: distinct sets of size at most one are pairwise disjoint, so a
family of such sets contains a sunflower with `p` petals exactly when it has at least `p` members
(`containsSunflower_iff_le_card`). For `w = 2` and `p = 3` the product construction is not
optimal: two disjoint triangles are six edges without a sunflower with three petals
(`not_containsSunflower_twoTriangles`), more than the `(3 - 1) ^ 2 = 4` edges of the construction.

## Main definitions

* `Cslib.Sunflower.functionGraph`: the graph of a function on a finite type, as a finite set.
* `Cslib.Sunflower.graphFamily`: the graphs of all functions `ι → β`.
* `Cslib.Sunflower.twoTriangles`: the edges of two disjoint triangles.

## Main results

* `Cslib.Sunflower.not_containsSunflower_graphFamily`: the graph family has no sunflower with
  `|β| + 1` petals.
* `Cslib.exists_card_eq_pow_not_containsSunflower`: `(p - 1) ^ w` sets of size `w` without a
  sunflower with `p` petals.
* `Cslib.containsSunflower_iff_le_card`: for sets of size at most one, a sunflower with `p` petals
  exists exactly when there are at least `p` sets.
* `Cslib.Sunflower.not_containsSunflower_twoTriangles`: six sets of size two without a sunflower
  with three petals.

## References

* [P. Erdős, R. Rado, *Intersection theorems for systems of sets*][ErdosRado1960]
-/

@[expose] public section

namespace Cslib

open Finset

/-! ### Graphs of functions -/

namespace Sunflower

variable {ι β : Type*} [Fintype ι]

/-- The graph `{(i, f i) | i : ι}` of a function on a finite type, as a finite set. -/
def functionGraph (f : ι → β) : Finset (ι × β) :=
  univ.map ⟨fun i => (i, f i), fun _ _ h => (Prod.mk.inj h).1⟩

/-- A pair lies in the graph of `f` exactly when its second component is the value of `f` at its
first. -/
@[simp]
theorem mem_functionGraph {f : ι → β} {x : ι × β} : x ∈ functionGraph f ↔ f x.1 = x.2 := by
  constructor
  · intro hx
    obtain ⟨i, -, rfl⟩ := mem_map.1 hx
    rfl
  · intro h
    exact mem_map.2 ⟨x.1, mem_univ _, Prod.ext rfl h⟩

/-- The graph of a function on `ι` has `|ι|` elements. -/
@[simp]
theorem card_functionGraph (f : ι → β) : #(functionGraph f) = Fintype.card ι := by
  rw [functionGraph, card_map, card_univ]

/-- A function is determined by its graph. -/
theorem functionGraph_injective : Function.Injective (functionGraph : (ι → β) → _) :=
  fun f g h => funext fun i =>
    (mem_functionGraph.1 (h ▸ mem_functionGraph.2 rfl : (i, f i) ∈ functionGraph g)).symm

variable [DecidableEq ι] [Fintype β]

/-- The graphs of all functions `ι → β`. -/
def graphFamily (ι β : Type*) [Fintype ι] [DecidableEq ι] [Fintype β] : Finset (Finset (ι × β)) :=
  univ.map ⟨functionGraph, functionGraph_injective⟩

/-- The members of the graph family are the graphs of functions. -/
theorem mem_graphFamily {s : Finset (ι × β)} : s ∈ graphFamily ι β ↔ ∃ f, functionGraph f = s := by
  simp [graphFamily]

/-- There are `|β| ^ |ι|` graphs of functions `ι → β`. -/
theorem card_graphFamily : #(graphFamily ι β) = Fintype.card β ^ Fintype.card ι := by
  rw [graphFamily, card_map, card_univ, Fintype.card_fun]

/-- Every graph of a function on `ι` has `|ι|` elements. -/
theorem card_of_mem_graphFamily {s : Finset (ι × β)} (hs : s ∈ graphFamily ι β) :
    #s = Fintype.card ι := by
  obtain ⟨f, rfl⟩ := mem_graphFamily.1 hs
  exact card_functionGraph f

variable [DecidableEq β]

/-- **Erdős–Rado lower bound.** The graphs of all functions `ι → β`, for nonempty `β`, contain no
sunflower with `|β| + 1` petals: at each coordinate some pair of petals agrees, so every petal is
contained in the core. -/
theorem not_containsSunflower_graphFamily [Nonempty β] :
    ¬ ContainsSunflower (Fintype.card β + 1) (graphFamily ι β) := by
  rintro ⟨S, hSF, hS, K, hK⟩
  have h2 : 2 ≤ #S := by have := Fintype.card_pos (α := β); omega
  have hKsub : ∀ s ∈ S, K ⊆ s := fun s hs => hK.subset_of_mem h2 hs
  -- every set of `S` is the graph of `φ s`
  set φ : Finset (ι × β) → ι → β := Function.invFun functionGraph
  have hmem {s} (hs : s ∈ S) {y : ι × β} : y ∈ s ↔ φ s y.1 = y.2 := by
    have h := mem_functionGraph (f := φ s) (x := y)
    rwa [Function.invFun_eq (mem_graphFamily.1 (hSF hs))] at h
  -- every petal is contained in the core
  have hsub : ∀ s ∈ S, s ⊆ K := by
    intro s hs x hx
    obtain ⟨u, hu, u', hu', hne, huu'⟩ := exists_ne_map_eq_of_card_lt_of_maps_to
      (t := (univ : Finset β)) (f := fun u => φ u x.1)
      (by rw [card_univ, hS]; omega) fun _ _ => mem_coe.2 (mem_univ _)
    have hK' : (x.1, φ u x.1) ∈ K := by
      rw [← hK hu hu' hne]
      exact mem_inter.2 ⟨(hmem hu).2 rfl, (hmem hu').2 huu'.symm⟩
    have hval : φ s x.1 = φ u x.1 := (hmem hs).1 (hKsub s hs hK')
    rwa [show x = (x.1, φ u x.1) from Prod.ext rfl (((hmem hs).1 hx).symm.trans hval)]
  obtain ⟨s, hs, t, ht, hst⟩ := one_lt_card.1 (show 1 < #S by omega)
  exact hst ((hsub s hs).trans (hKsub t ht) |>.antisymm ((hsub t ht).trans (hKsub s hs)))

end Sunflower

open Sunflower

/-- **Erdős–Rado lower bound.** For `p ≥ 2` there are `(p - 1) ^ w` sets of size `w` without a
sunflower with `p` petals: the graphs of all functions `Fin w → Fin (p - 1)`. -/
theorem exists_card_eq_pow_not_containsSunflower (p w : ℕ) (hp : 2 ≤ p) :
    ∃ F : Finset (Finset (Fin w × Fin (p - 1))),
      #F = (p - 1) ^ w ∧ (∀ s ∈ F, #s = w) ∧ ¬ ContainsSunflower p F := by
  have : Nonempty (Fin (p - 1)) := ⟨⟨0, by omega⟩⟩
  refine ⟨graphFamily (Fin w) (Fin (p - 1)), ?_, fun s hs => ?_, ?_⟩
  · rw [card_graphFamily, Fintype.card_fin, Fintype.card_fin]
  · rw [card_of_mem_graphFamily hs, Fintype.card_fin]
  · have h := not_containsSunflower_graphFamily (ι := Fin w) (β := Fin (p - 1))
    rwa [Fintype.card_fin, Nat.sub_add_cancel (by omega)] at h

/-! ### Sets of size at most one -/

/-- For a family of sets of size at most one, which are pairwise disjoint when distinct, a
sunflower with `p` petals exists exactly when the family has at least `p` sets. With the sunflower
lemma for `w = 1` this shows that its bound `p - 1` is exact. -/
theorem containsSunflower_iff_le_card {α : Type*} [DecidableEq α] {F : Finset (Finset α)}
    (hF : ∀ s ∈ F, #s ≤ 1) (p : ℕ) : ContainsSunflower p F ↔ p ≤ #F := by
  refine ⟨fun ⟨S, hSF, hS, _⟩ => hS ▸ card_le_card hSF, fun h => ?_⟩
  obtain ⟨S, hSF, hS⟩ := exists_subset_card_eq h
  refine ⟨S, hSF, hS, ∅, fun s hs t ht hst => eq_empty_of_forall_notMem fun x hx => hst ?_⟩
  obtain ⟨hxs, hxt⟩ := mem_inter.1 hx
  ext y
  exact ⟨fun hy => card_le_one.1 (hF s (hSF hs)) y hy x hxs ▸ hxt,
    fun hy => card_le_one.1 (hF t (hSF ht)) y hy x hxt ▸ hxs⟩

/-! ### Two disjoint triangles -/

namespace Sunflower

/-- The six edges of two disjoint triangles on `Fin 6`. -/
def twoTriangles : Finset (Finset (Fin 6)) :=
  {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}

/-- The two triangles have six edges. -/
theorem card_twoTriangles : #twoTriangles = 6 := by decide

/-- Every edge of the two triangles has two vertices. -/
theorem card_of_mem_twoTriangles : ∀ s ∈ twoTriangles, #s = 2 := by decide

private theorem twoTriangles_triples : ∀ s ∈ twoTriangles, ∀ t ∈ twoTriangles,
    ∀ u ∈ twoTriangles, s ≠ t → s ≠ u → t ≠ u → ¬ (s ∩ t = s ∩ u ∧ s ∩ t = t ∩ u) := by
  decide

/-- Two disjoint triangles contain no sunflower with three petals: such a sunflower of edges
consists of three edges through a common vertex or of three pairwise disjoint edges, but every
vertex has degree two and every three edges include two of the same triangle. So the product
construction, with `(3 - 1) ^ 2 = 4` sets, is not optimal for `w = 2` and `p = 3`. The proof checks
all triples of edges by `decide`. -/
theorem not_containsSunflower_twoTriangles : ¬ ContainsSunflower 3 twoTriangles := by
  rintro ⟨S, hSF, hS, K, hK⟩
  obtain ⟨s, t, u, hst, hsu, htu, rfl⟩ := card_eq_three.1 hS
  have hs : s ∈ ({s, t, u} : Finset (Finset (Fin 6))) := by simp
  have ht : t ∈ ({s, t, u} : Finset (Finset (Fin 6))) := by simp
  have hu : u ∈ ({s, t, u} : Finset (Finset (Fin 6))) := by simp
  exact twoTriangles_triples s (hSF hs) t (hSF ht) u (hSF hu) hst hsu htu
    ⟨(hK hs ht hst).trans (hK hs hu hsu).symm, (hK hs ht hst).trans (hK ht hu htu).symm⟩

end Sunflower

end Cslib
