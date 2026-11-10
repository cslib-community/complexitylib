/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Matroid.Intersection
public import Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching
public import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Combinatorics.Matroid.Constructions

/-!
# Bipartite matching as matroid intersection

A matching of a bipartite graph `G : L × R → Bool` is a set of edges that is independent in two
unit-capacity partition matroids on `L × R`: the one whose blocks are the fibres of `Prod.fst`
and the one whose blocks are the fibres of `Prod.snd` ([Schrijver2017], Example 10.5a). This module
proves that correspondence and shows that a separator `U` from Edmonds' matroid intersection
theorem gives a vertex cover of size `M₁.eRk U + M₂.eRk (E \ U)`. Edmonds' theorem then yields a
maximum matching together with a vertex cover of the same size. This is König's theorem
([Koenig1931]), derived by the matroid route of [Schrijver2017], Exercise 10.22.

The library's primary statement of König's theorem is the flow-based
`Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`. This module gives a second,
flow-independent derivation via matroid intersection, with an explicit separator cover. It is
stated with the existing `Cslib.Algorithms.Lean.MaxFlow.IsMatching`, `VertexCover` and
`IsVertexCover` API, and shares with the flow proof only the matching/cover weak duality
`Cslib.Algorithms.Lean.MaxFlow.card_le_size_of_matching_vertexCover`, used to conclude minimality
of the cover.

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.unitPartitionMatroid`: the unit-capacity partition matroid of a
  map `f : α → β`, in which a set is independent when `f` is injective on it.
* `Cslib.Algorithms.Lean.Matroid.bipartiteEdges`: the edge set of `G : L × R → Bool` as a `Finset`.
* `Cslib.Algorithms.Lean.Matroid.separatorCover`: the vertex cover `(fst '' U, snd '' (E \ U))`
  read off from a separator `U`.

## Main results

* `Cslib.Algorithms.Lean.Matroid.unitPartitionMatroid_indep_iff`,
  `Cslib.Algorithms.Lean.Matroid.unitPartitionMatroid_eRk`: independence and rank in the
  unit-capacity partition matroid.
* `Cslib.Algorithms.Lean.Matroid.isMatching_iff_isCommonIndep`: matchings of `G` are exactly the
  common independent subsets of `bipartiteEdges G` for the two partition matroids.
* `Cslib.Algorithms.Lean.Matroid.isVertexCover_separatorCover`,
  `Cslib.Algorithms.Lean.Matroid.size_separatorCover`: every separator gives a vertex cover whose
  size is the corresponding rank sum.
* `Cslib.Algorithms.Lean.Matroid.exists_maxMatching_separatorCover`: Edmonds' theorem gives a
  maximum matching and a minimum vertex cover of the form `separatorCover` with equal sizes.

## References

* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 10.5
* [D. König, *Gráfok és mátrixok*][Koenig1931]
-/

public section

namespace Cslib.Algorithms.Lean.Matroid

open Cslib.Algorithms.Lean.MaxFlow

/-! ### Unit-capacity partition matroids -/

section PartitionMatroid

variable {α β : Type*}

/-- The unit-capacity partition matroid of `f : α → β`: its ground set is all of `α`, and a set `I`
is independent exactly when `f` is injective on `I`, so each fibre of `f` is a block of capacity
one. It is the free matroid on `β` pulled back along `f`. -/
def unitPartitionMatroid (f : α → β) : Matroid α :=
  (Matroid.freeOn Set.univ).comap f

theorem unitPartitionMatroid_indep_iff {f : α → β} {I : Set α} :
    (unitPartitionMatroid f).Indep I ↔ Set.InjOn f I := by
  simp [unitPartitionMatroid]

/-- The rank of `X` in the unit-capacity partition matroid of `f` is the number of blocks that
`X` meets. -/
theorem unitPartitionMatroid_eRk (f : α → β) (X : Set α) :
    (unitPartitionMatroid f).eRk X = (f '' X).encard := by
  rw [unitPartitionMatroid, Matroid.eRk_comap, Matroid.eRk_freeOn (Set.subset_univ _)]

end PartitionMatroid

/-! ### Matchings, separators and vertex covers -/

section Bipartite

variable {L R : Type*}

/-- The edge set `{e | G e = true}` of a bipartite graph `G : L × R → Bool` on finite vertex
types. -/
@[expose] def bipartiteEdges [Fintype L] [Fintype R] (G : L × R → Bool) : Finset (L × R) :=
  Finset.univ.filter fun e => G e = true

theorem mem_bipartiteEdges [Fintype L] [Fintype R] {G : L × R → Bool} {e : L × R} :
    e ∈ bipartiteEdges G ↔ G e = true := by
  simp [bipartiteEdges]

/-- **Bipartite matchings are common independent sets** ([Schrijver2017], Example 10.5a): `M` is a
matching of `G` exactly when `M ⊆ bipartiteEdges G` and `M` is independent in both unit-capacity
partition matroids `unitPartitionMatroid Prod.fst` and `unitPartitionMatroid Prod.snd`. -/
theorem isMatching_iff_isCommonIndep [Fintype L] [Fintype R] {G : L × R → Bool}
    {M : Finset (L × R)} :
    IsMatching G M ↔ M ⊆ bipartiteEdges G ∧
      IsCommonIndep (unitPartitionMatroid Prod.fst) (unitPartitionMatroid Prod.snd) M := by
  simp only [IsMatching, IsCommonIndep, unitPartitionMatroid_indep_iff]
  constructor
  · rintro ⟨hE, hL, hR⟩
    refine ⟨fun e he => mem_bipartiteEdges.mpr (hE e he), ?_, ?_⟩
    · rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
      subst hu
      rw [hL u₁ v₁ v₂ h₁ h₂]
    · rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hv : v₁ = v₂)
      subst hv
      rw [hR u₁ u₂ v₁ h₁ h₂]
  · rintro ⟨hE, hL, hR⟩
    refine ⟨fun e he => mem_bipartiteEdges.mp (hE he), ?_, ?_⟩
    · intro u v₁ v₂ h₁ h₂
      exact congrArg Prod.snd (hL (Finset.mem_coe.mpr h₁) (Finset.mem_coe.mpr h₂) rfl)
    · intro u₁ u₂ v h₁ h₂
      exact congrArg Prod.fst (hR (Finset.mem_coe.mpr h₁) (Finset.mem_coe.mpr h₂) rfl)

variable [DecidableEq L] [DecidableEq R]

/-- The vertex cover read off from a separator `U ⊆ E`: the left endpoints of edges in `U` and the
right endpoints of edges in `E \ U`. -/
@[expose] def separatorCover (E U : Finset (L × R)) : VertexCover L R where
  left := U.image Prod.fst
  right := (E \ U).image Prod.snd

/-- For every `U`, `separatorCover (bipartiteEdges G) U` covers every edge of `G`: an edge in `U`
is covered by its left endpoint, and an edge outside `U` by its right endpoint. -/
theorem isVertexCover_separatorCover [Fintype L] [Fintype R] (G : L × R → Bool)
    (U : Finset (L × R)) : IsVertexCover G (separatorCover (bipartiteEdges G) U) := by
  intro u v huv
  by_cases hU : (u, v) ∈ U
  · exact .inl (Finset.mem_image.mpr ⟨(u, v), hU, rfl⟩)
  · exact .inr (Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_sdiff.mpr ⟨mem_bipartiteEdges.mpr huv, hU⟩, rfl⟩)

/-- The size of `separatorCover E U` is the rank sum
`(unitPartitionMatroid Prod.fst).eRk U + (unitPartitionMatroid Prod.snd).eRk (E \ U)` from
Edmonds' theorem. -/
theorem size_separatorCover (E U : Finset (L × R)) :
    ((separatorCover E U).size : ℕ∞) =
      (unitPartitionMatroid Prod.fst).eRk (U : Set (L × R)) +
        (unitPartitionMatroid Prod.snd).eRk ((E \ U : Finset (L × R)) : Set (L × R)) := by
  rw [unitPartitionMatroid_eRk, unitPartitionMatroid_eRk, ← Finset.coe_image, ← Finset.coe_image,
    Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard, VertexCover.size,
    Nat.cast_add]
  rfl

/-- **König's theorem by matroid intersection** ([Schrijver2017], Example 10.5a and
Exercise 10.22; [Koenig1931]): for a bipartite graph `G` on finite vertex types, Edmonds' theorem
for the two unit-capacity partition matroids on `bipartiteEdges G` gives a maximum matching `M` and
a separator `U ⊆ bipartiteEdges G` whose `separatorCover` is a minimum vertex cover of size
`M.card`. The flow-based proof of the same equality is
`Cslib.Algorithms.Lean.MaxFlow.exists_maxMatching_eq_minVertexCover`. -/
theorem exists_maxMatching_separatorCover [Fintype L] [Fintype R] (G : L × R → Bool) :
    ∃ (M U : Finset (L × R)), U ⊆ bipartiteEdges G ∧ IsMaxMatching G M ∧
      IsMinVertexCover G (separatorCover (bipartiteEdges G) U) ∧
      M.card = (separatorCover (bipartiteEdges G) U).size := by
  obtain ⟨M, U, hUE, hmax, heq⟩ := exists_commonIndep_card_eq_eRk_add_eRk
    (unitPartitionMatroid Prod.fst) (unitPartitionMatroid Prod.snd) (bipartiteEdges G)
  have hM : IsMatching G M := isMatching_iff_isCommonIndep.mpr ⟨hmax.1, hmax.2.1⟩
  have hsize : M.card = (separatorCover (bipartiteEdges G) U).size := by
    have h := heq
    rw [← size_separatorCover] at h
    exact_mod_cast h
  have hC := isVertexCover_separatorCover G U
  refine ⟨M, U, hUE, ⟨hM, fun M' hM' => ?_⟩, ⟨hC, fun C' hC' => ?_⟩, hsize⟩
  · obtain ⟨hM'E, hM'⟩ := isMatching_iff_isCommonIndep.mp hM'
    exact hmax.2.2 M' hM'E hM'
  · rw [← hsize]
    exact card_le_size_of_matching_vertexCover hM hC'

end Bipartite

end Cslib.Algorithms.Lean.Matroid
