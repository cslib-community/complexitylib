/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Coloring/Vertex.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.GreedyColoring

/-!
# Proper colorings as functions

Sampling and counting arguments for colorings ([LevinPeres2017], Sections 3.3.1 and 14.3–14.4)
work with arbitrary maps `x : V → Fin q`, proper or not, rather than with the bundled
`SimpleGraph.Coloring`. This file provides the predicate `SimpleGraph.IsProperColoring`, the finset
`SimpleGraph.properColorings` of proper `q`-colorings, and the colors allowed at a vertex,
`SimpleGraph.allowedColors`: those absent from its neighbors. At most `Δ` colors are excluded
(`SimpleGraph.sub_maxDegree_le_card_allowedColors`), and recoloring a vertex of a proper coloring
with an allowed color keeps it proper (`SimpleGraph.IsProperColoring.update_of_mem`). The proper
colorings agreeing with a fixed coloring `b` off a vertex set `U`, `SimpleGraph.frozenColorings`,
are the state spaces of the approximate counting algorithm of [LevinPeres2017], Section 14.4.2.

## Main definitions

* `SimpleGraph.IsProperColoring`: adjacent vertices have different colors.
* `SimpleGraph.allowedColors`: the colors absent from the neighbors of a vertex.
* `SimpleGraph.properColorings`: the finset of proper `q`-colorings.
* `SimpleGraph.frozenColorings`: the proper colorings agreeing with `b` off `U`.

## Main results

* `SimpleGraph.isProperColoring_iff_exists_coloring`: proper colorings are the
  `SimpleGraph.Coloring`s.
* `SimpleGraph.sub_maxDegree_le_card_allowedColors`: at least `q - Δ` colors are allowed.
* `SimpleGraph.properColorings_nonempty`: proper colorings exist when `Δ < q`.
* `SimpleGraph.IsProperColoring.update_of_mem`: recoloring with an allowed color.
* `SimpleGraph.frozenColorings_univ`, `SimpleGraph.frozenColorings_empty`,
  `SimpleGraph.frozenColorings_erase`: nothing frozen, everything frozen, and freezing one more
  vertex.

## References

* [LevinPeres2017], Sections 3.1, 3.3.1 and 14.4.2.
-/

public section

namespace SimpleGraph

variable {V : Type*} {q : ℕ}

section Proper

variable (G : SimpleGraph V)

/-- `x` is a proper coloring of `G`: adjacent vertices have different colors. -/
def IsProperColoring (x : V → Fin q) : Prop :=
  ∀ u v, G.Adj u v → x u ≠ x v

theorem isProperColoring_iff {x : V → Fin q} :
    G.IsProperColoring x ↔ ∀ u v, G.Adj u v → x u ≠ x v :=
  Iff.rfl

/-- Proper colorings are the colorings of `G` in the sense of `SimpleGraph.Coloring`. -/
theorem isProperColoring_iff_exists_coloring {x : V → Fin q} :
    G.IsProperColoring x ↔ ∃ C : G.Coloring (Fin q), ⇑C = x :=
  ⟨fun h => ⟨Coloring.mk x fun {u v} huv => h u v huv, rfl⟩,
    fun ⟨C, hC⟩ _ _ huv => hC ▸ C.valid huv⟩

end Proper

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The colors absent from the neighbors of `w` under the coloring `x` ([LevinPeres2017],
Section 3.3.1). -/
def allowedColors (x : V → Fin q) (w : V) : Finset (Fin q) :=
  Finset.univ \ (G.neighborFinset w).image x

theorem mem_allowedColors {x : V → Fin q} {w : V} {c : Fin q} :
    c ∈ G.allowedColors x w ↔ ∀ u, G.Adj w u → x u ≠ c := by
  simp [allowedColors]

/-- At most `Δ` colors are excluded. -/
theorem sub_maxDegree_le_card_allowedColors (x : V → Fin q) (w : V) :
    q - G.maxDegree ≤ (G.allowedColors x w).card := by
  have h1 : ((G.neighborFinset w).image x).card ≤ G.maxDegree :=
    Finset.card_image_le.trans (G.degree_le_maxDegree w)
  have h2 := Finset.le_card_sdiff ((G.neighborFinset w).image x) Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at h2
  rw [allowedColors]
  omega

theorem allowedColors_nonempty (hq : G.maxDegree < q) (x : V → Fin q) (w : V) :
    (G.allowedColors x w).Nonempty := by
  rw [← Finset.card_pos]
  have := G.sub_maxDegree_le_card_allowedColors x w
  omega

/-- The allowed colors at `w` depend only on the colors of the neighbors of `w`. -/
theorem allowedColors_congr {x y : V → Fin q} {w : V} (h : ∀ u, G.Adj w u → x u = y u) :
    G.allowedColors x w = G.allowedColors y w := by
  ext c
  simp only [mem_allowedColors]
  exact forall_congr' fun u => imp_congr_right fun hu => by rw [h u hu]

instance (x : V → Fin q) : Decidable (G.IsProperColoring x) :=
  decidable_of_iff _ (isProperColoring_iff G).symm

variable {G} in
theorem IsProperColoring.mem_allowedColors {x : V → Fin q} (hx : G.IsProperColoring x) (w : V) :
    x w ∈ G.allowedColors x w :=
  (SimpleGraph.mem_allowedColors G).2 fun u hu => (hx w u hu).symm

variable [DecidableEq V]

/-- The proper `q`-colorings of `G`. -/
def properColorings (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ) : Finset (V → Fin q) :=
  Finset.univ.filter fun x => G.IsProperColoring x

theorem mem_properColorings {x : V → Fin q} : x ∈ G.properColorings q ↔ G.IsProperColoring x := by
  simp [properColorings]

/-- **Greedy coloring**: if `Δ < q`, proper `q`-colorings exist. -/
theorem properColorings_nonempty (hq : G.maxDegree < q) : (G.properColorings q).Nonempty := by
  obtain ⟨C⟩ := G.colorable_of_maxDegree_lt hq
  exact ⟨C, (mem_properColorings G).2 fun u v huv => C.valid huv⟩

/-- The proper colorings agreeing with `b` off `U`, the state space `X_k` of [LevinPeres2017],
Section 14.4.2, when `U` is the set of the first `k` vertices. -/
def frozenColorings (q : ℕ) (U : Finset V) (b : V → Fin q) : Finset (V → Fin q) :=
  Finset.univ.filter fun x => G.IsProperColoring x ∧ ∀ u ∉ U, x u = b u

variable {G}

theorem mem_frozenColorings {U : Finset V} {b x : V → Fin q} :
    x ∈ frozenColorings G q U b ↔ G.IsProperColoring x ∧ ∀ u ∉ U, x u = b u := by
  simp [frozenColorings]

theorem mem_frozenColorings_self {U : Finset V} {b : V → Fin q} (hb : G.IsProperColoring b) :
    b ∈ frozenColorings G q U b :=
  mem_frozenColorings.2 ⟨hb, fun _ _ => rfl⟩

theorem frozenColorings_univ (b : V → Fin q) :
    frozenColorings G q Finset.univ b = G.properColorings q := by
  ext x
  simp [mem_frozenColorings, mem_properColorings]

/-- With every vertex frozen, only `b` itself remains. -/
theorem frozenColorings_empty {b : V → Fin q} (hb : G.IsProperColoring b) :
    frozenColorings G q ∅ b = {b} := by
  ext x
  simp only [mem_frozenColorings, Finset.notMem_empty, not_false_eq_true, forall_const,
    Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    exact funext h
  · rintro rfl
    exact ⟨hb, fun _ => rfl⟩

/-- Freezing one more vertex `v` at its color in `b` keeps the colorings with `x v = b v`. -/
theorem frozenColorings_erase (U : Finset V) (b : V → Fin q) (v : V) :
    frozenColorings G q (U.erase v) b = (frozenColorings G q U b).filter fun x => x v = b v := by
  ext x
  simp only [Finset.mem_filter, mem_frozenColorings, Finset.mem_erase, not_and_or, not_not,
    ne_eq]
  constructor
  · rintro ⟨hx, hb⟩
    exact ⟨⟨hx, fun u hu => hb u (Or.inr hu)⟩, hb v (Or.inl rfl)⟩
  · rintro ⟨⟨hx, hb⟩, hv⟩
    refine ⟨hx, fun u hu => ?_⟩
    rcases hu with rfl | hu
    · exact hv
    · exact hb u hu

/-- Recoloring a vertex of a proper coloring with an allowed color gives a proper coloring. -/
theorem IsProperColoring.update_of_mem {x : V → Fin q} (hx : G.IsProperColoring x) {w : V}
    {c : Fin q} (hc : c ∈ G.allowedColors x w) : G.IsProperColoring (Function.update x w c) := by
  rw [SimpleGraph.mem_allowedColors] at hc
  intro u v huv
  by_cases hu : u = w
  · subst hu
    rw [Function.update_self, Function.update_of_ne (G.ne_of_adj huv).symm]
    exact (hc v huv).symm
  · by_cases hv : v = w
    · subst hv
      rw [Function.update_self, Function.update_of_ne hu]
      exact hc u huv.symm
    · rw [Function.update_of_ne hu, Function.update_of_ne hv]
      exact hx u v huv

end SimpleGraph
