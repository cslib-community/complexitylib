/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching

/-!
# Augmenting Paths, Berge's Theorem, and the Hopcroft–Karp Phase Bound

Combinatorial core of the Hopcroft–Karp maximum bipartite matching algorithm
([HopcroftKarp1973]; [CLRS2009], Problem 26-6), on the edge-indicator representation
`G : L × R → Bool` and `Finset (L × R)` matchings of
`Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching`.

## Main definitions

* `altLeft`, `altRight`, `IsLayer`: `altLeft G M j` is the set of left vertices reachable from a
  free left vertex by an `M`-alternating path with at most `j` matching edges, `altRight G M j` its
  `G`-neighbourhood, and `IsLayer G M u j` says `u` first appears in layer `j`. This is the
  breadth-first layering of one Hopcroft–Karp phase. `NoShortAug G M k` says no layer `j < k`
  reaches a free right vertex, i.e. every augmenting path has at least `k + 1` non-matching edges.
* `IsAugmentingPath`, `augment`: an augmenting path `u₀ v₀ u₁ v₁ … u_ℓ v_ℓ` is recorded by its
  non-matching edges `(uᵢ, vᵢ)`, with `(uᵢ₊₁, vᵢ) ∈ M`, distinct vertices and free ends.
  `augment M N` replaces the `M`-edges at left vertices covered by `N` with `N`; for a path this is
  the symmetric difference `M ⊕ p`.
* `IsMaximalLayeredAugmentation`, `IsLayeredFamily`: the edge set `N` found by one phase follows
  the layers of `M` to a free right vertex in layer `k`, replaces `M`-edges at both ends, and admits
  no further layered path avoiding it. `IsLayeredFamily` is the list-level description produced by
  depth-first search (concatenated vertex-disjoint shortest augmenting paths), and
  `IsLayeredFamily.isMaximalLayeredAugmentation` packages it.
* `IsPhaseRun G M n`: `n` Hopcroft–Karp phases from `M`, each using the exact shortest
  augmenting path parameter and a maximal layered augmentation.
* `layerCover G M j`: unreached left vertices together with reached right vertices.

## Main results

* `card_mul_le_of_noShortAug` (**layered counting lemma**): `k * |M'| ≤ (k + 1) * |M|` for every
  matching `M'` when `NoShortAug G M k`, obtained from weak duality against the vertex covers
  `layerCover G M j`.
* `isMaxMatching_iff_forall_not_isAugmentingPath` (**Berge's theorem**): the bipartite case of
  [Berge1957], Theorem 1. The proof is not the textbook decomposition of `M ⊕ M*` into alternating
  paths and cycles: it uses the layered counting lemma.
* `IsMaximalLayeredAugmentation.noShortAug_augment` (**phase lemma**): after augmenting along a
  maximal set of vertex-disjoint shortest augmenting paths, the shortest augmenting path is strictly
  longer ([HopcroftKarp1973], consequence of Theorem 2; [CLRS2009], Problem 26-6).
* `IsPhaseRun.add_card_le_and_add_le_two_mul_sqrt`, `IsPhaseRun.le_two_mul_sqrt` (**phase
  count**): the counting lemma gives the deficit bound `t * (ν - |M|) ≤ |M|` after `t` phases, hence
  at most `2 ⌊√ν⌋` augmenting phases from the empty matching, `ν` the maximum matching size. This
  is slightly sharper than the `2 ⌊√s⌋ + 2` bound on distinct shortest-path lengths of
  [HopcroftKarp1973], Theorem 3, because only phases that augment are counted.
* `isMaxMatching_isMinVertexCover_of_stable` (**König certificate**): when the layers stop growing
  without reaching a free right vertex, the layer cover is a minimum vertex cover of size `|M|`.

## Limitations

* The decomposition of `M ⊕ M*` into at least `|M*| - |M|` vertex-disjoint augmenting paths is not
  formalized; the counting lemma replaces it in both Berge's theorem and the phase bound.
* Only bipartite graphs are treated (no blossoms).

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [C. Berge, *Two Theorems in Graph Theory*][Berge1957]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

section Matched

variable {L R : Type*} [DecidableEq L] [DecidableEq R]

/-- Left endpoints of the edges of `M`. -/
@[expose] def matchedLeft (M : Finset (L × R)) : Finset L := M.image Prod.fst

/-- Right endpoints of the edges of `M`. -/
@[expose] def matchedRight (M : Finset (L × R)) : Finset R := M.image Prod.snd

omit [DecidableEq R] in
@[simp] theorem mem_matchedLeft {M : Finset (L × R)} {u : L} :
    u ∈ matchedLeft M ↔ ∃ v, (u, v) ∈ M := by
  simp [matchedLeft]

omit [DecidableEq L] in
@[simp] theorem mem_matchedRight {M : Finset (L × R)} {v : R} :
    v ∈ matchedRight M ↔ ∃ u, (u, v) ∈ M := by
  simp [matchedRight]

variable {G : L × R → Bool} {M : Finset (L × R)}

omit [DecidableEq R] in
theorem card_matchedLeft (hM : IsMatching G M) : (matchedLeft M).card = M.card := by
  refine Finset.card_image_of_injOn ?_
  rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
  subst hu
  rw [hM.2.1 u₁ v₁ v₂ h₁ h₂]

omit [DecidableEq L] in
theorem card_matchedRight (hM : IsMatching G M) : (matchedRight M).card = M.card := by
  refine Finset.card_image_of_injOn ?_
  rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hv : v₁ = v₂)
  subst hv
  rw [hM.2.2 u₁ u₂ v₁ h₁ h₂]

end Matched

section Layers

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

variable (G : L × R → Bool) (M : Finset (L × R))

/-- Right vertices adjacent in `G` to some vertex of `S`. -/
@[expose] def rightNbrs (S : Finset L) : Finset R :=
  Finset.univ.filter fun v => ∃ u ∈ S, G (u, v) = true

/-- Left vertices reachable from free left vertices by an `M`-alternating path with at most `j`
matched edges. -/
@[expose] def altLeft : ℕ → Finset L
  | 0 => Finset.univ \ matchedLeft M
  | j + 1 => altLeft j ∪ (M.filter fun e => e.2 ∈ rightNbrs G (altLeft j)).image Prod.fst

/-- Right vertices adjacent to `altLeft G M j`. -/
@[expose] def altRight (j : ℕ) : Finset R := rightNbrs G (altLeft G M j)

/-- `u` first appears in alternating layer `j`. -/
@[expose] def IsLayer (u : L) (j : ℕ) : Prop := u ∈ altLeft G M j ∧ ∀ i < j, u ∉ altLeft G M i

/-- No alternating path with at most `k - 1` matched edges from a free left vertex ends at a free
right vertex: every vertex of `altRight G M j`, `j < k`, is matched. -/
@[expose] def NoShortAug (k : ℕ) : Prop := ∀ j < k, altRight G M j ⊆ matchedRight M

variable {G M}

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
@[simp] theorem mem_rightNbrs {S : Finset L} {v : R} :
    v ∈ rightNbrs G S ↔ ∃ u ∈ S, G (u, v) = true := by
  simp [rightNbrs]

theorem mem_altLeft_zero {u : L} : u ∈ altLeft G M 0 ↔ u ∉ matchedLeft M := by
  simp [altLeft]

theorem mem_altLeft_succ {u : L} {j : ℕ} :
    u ∈ altLeft G M (j + 1) ↔ u ∈ altLeft G M j ∨ ∃ v, (u, v) ∈ M ∧ v ∈ altRight G M j := by
  simp [altLeft, altRight]

theorem mem_altRight {v : R} {j : ℕ} :
    v ∈ altRight G M j ↔ ∃ u ∈ altLeft G M j, G (u, v) = true := by
  simp [altRight]

theorem altLeft_mono {i j : ℕ} (h : i ≤ j) : altLeft G M i ⊆ altLeft G M j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem altRight_mono {i j : ℕ} (h : i ≤ j) : altRight G M i ⊆ altRight G M j := by
  intro v hv
  obtain ⟨u, hu, hG⟩ := mem_altRight.mp hv
  exact mem_altRight.mpr ⟨u, altLeft_mono h hu, hG⟩

theorem IsLayer.unique {u : L} {i j : ℕ} (hi : IsLayer G M u i) (hj : IsLayer G M u j) :
    i = j := by
  rcases lt_trichotomy i j with h | h | h
  · exact absurd hi.1 (hj.2 i h)
  · exact h
  · exact absurd hj.1 (hi.2 j h)

theorem exists_isLayer {u : L} {j : ℕ} (h : u ∈ altLeft G M j) :
    ∃ i ≤ j, IsLayer G M u i := by
  classical
  have hex : ∃ i, u ∈ altLeft G M i := ⟨j, h⟩
  exact ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩

theorem isLayer_zero {u : L} : IsLayer G M u 0 ↔ u ∉ matchedLeft M := by
  simp [IsLayer, mem_altLeft_zero]

theorem NoShortAug.mono {k k' : ℕ} (h : NoShortAug G M k) (hk : k' ≤ k) :
    NoShortAug G M k' :=
  fun j hj => h j (lt_of_lt_of_le hj hk)

theorem IsLayer.le_of_mem {u : L} {i j : ℕ} (hu : IsLayer G M u i) (h : u ∈ altLeft G M j) :
    i ≤ j := by
  by_contra hlt
  exact hu.2 j (by omega) h

theorem mem_altLeft_succ_of_mem {u : L} {v : R} {j : ℕ} (huv : (u, v) ∈ M)
    (hv : v ∈ altRight G M j) : u ∈ altLeft G M (j + 1) :=
  mem_altLeft_succ.mpr (.inr ⟨v, huv, hv⟩)

omit [Fintype L] [DecidableEq L] [DecidableEq R] in
theorem rightNbrs_mono {S T : Finset L} (h : S ⊆ T) : rightNbrs G S ⊆ rightNbrs G T := by
  intro v hv
  obtain ⟨u, hu, hG⟩ := mem_rightNbrs.mp hv
  exact mem_rightNbrs.mpr ⟨u, h hu, hG⟩

theorem mem_altRight_of_isLayer {u : L} {v : R} {i j : ℕ} (hu : IsLayer G M u i) (hij : i ≤ j)
    (hG : G (u, v) = true) : v ∈ altRight G M j :=
  mem_altRight.mpr ⟨u, altLeft_mono hij hu.1, hG⟩

end Layers

section Counting

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)}

/-- Vertex cover built from alternating layer `j`: unreached left vertices and reached right
vertices. -/
@[expose] def layerCover (G : L × R → Bool) (M : Finset (L × R)) (j : ℕ) : VertexCover L R :=
  ⟨Finset.univ \ altLeft G M j, altRight G M j⟩

theorem isVertexCover_layerCover (j : ℕ) : IsVertexCover G (layerCover G M j) := by
  intro u v hG
  by_cases hu : u ∈ altLeft G M j
  · exact .inr (mem_altRight.mpr ⟨u, hu, hG⟩)
  · exact .inl (by simp [layerCover, hu])

private theorem altLeft_succ_eq (j : ℕ) :
    altLeft G M (j + 1) = (Finset.univ \ matchedLeft M) ∪
      (M.filter fun e => e.2 ∈ altRight G M j).image Prod.fst := by
  induction j with
  | zero =>
    ext u
    simp only [mem_altLeft_succ, mem_altLeft_zero, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_filter, Prod.exists,
      exists_and_right, exists_eq_right]
  | succ j ih =>
    ext u
    rw [mem_altLeft_succ, ih]
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_filter, Prod.exists, exists_and_right, exists_eq_right]
    constructor
    · rintro ((h | ⟨v, hv, hr⟩) | ⟨v, hv, hr⟩)
      · exact .inl h
      · exact .inr ⟨v, hv, altRight_mono (Nat.le_succ j) hr⟩
      · exact .inr ⟨v, hv, hr⟩
    · rintro (h | ⟨v, hv, hr⟩)
      · exact .inl (.inl h)
      · exact .inr ⟨v, hv, hr⟩

private theorem card_altLeft_succ (hM : IsMatching G M) (j : ℕ) :
    (altLeft G M (j + 1)).card + M.card =
      Fintype.card L + (altRight G M j ∩ matchedRight M).card := by
  rw [altLeft_succ_eq, Finset.card_union_of_disjoint]
  · have h1 : (Finset.univ \ matchedLeft M).card + M.card = Fintype.card L := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        card_matchedLeft hM]
      have := card_matchedLeft hM ▸ Finset.card_le_univ (matchedLeft M)
      omega
    have hinjL : Set.InjOn Prod.fst (M.filter fun e => e.2 ∈ altRight G M j : Set (L × R)) := by
      rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
      subst hu
      rw [hM.2.1 u₁ v₁ v₂ (Finset.mem_filter.mp h₁).1 (Finset.mem_filter.mp h₂).1]
    have hinjR : Set.InjOn Prod.snd (M.filter fun e => e.2 ∈ altRight G M j : Set (L × R)) := by
      rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hv : v₁ = v₂)
      subst hv
      rw [hM.2.2 u₁ u₂ v₁ (Finset.mem_filter.mp h₁).1 (Finset.mem_filter.mp h₂).1]
    have himg : (M.filter fun e => e.2 ∈ altRight G M j).image Prod.snd =
        altRight G M j ∩ matchedRight M := by
      ext v
      rw [Finset.mem_inter, mem_matchedRight, Finset.mem_image]
      constructor
      · rintro ⟨⟨u, w⟩, he, rfl⟩
        obtain ⟨hM', hw⟩ := Finset.mem_filter.mp he
        exact ⟨hw, u, hM'⟩
      · rintro ⟨hv, u, hu⟩
        exact ⟨(u, v), Finset.mem_filter.mpr ⟨hu, hv⟩, rfl⟩
    rw [Finset.card_image_of_injOn hinjL, ← Finset.card_image_of_injOn hinjR, himg]
    omega
  · rw [Finset.disjoint_left]
    intro u hu himg
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp himg
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image_of_mem _ (Finset.mem_filter.mp he).1)

private theorem size_layerCover_zero (hM : IsMatching G M) :
    (layerCover G M 0).size = M.card + (altRight G M 0).card := by
  have h : Finset.univ \ altLeft G M 0 = matchedLeft M := by
    ext u
    simp [mem_altLeft_zero]
  simp only [VertexCover.size, layerCover, h, card_matchedLeft hM]

private theorem size_layerCover_succ (hM : IsMatching G M) (j : ℕ) :
    (layerCover G M (j + 1)).size + (altRight G M j ∩ matchedRight M).card =
      M.card + (altRight G M (j + 1)).card := by
  have h := card_altLeft_succ hM j
  have hc : (Finset.univ \ altLeft G M (j + 1)).card + (altLeft G M (j + 1)).card =
      Fintype.card L := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have := Finset.card_le_univ (altLeft G M (j + 1))
    omega
  simp only [VertexCover.size, layerCover]
  omega

/-- **Layered counting lemma.** If no alternating path with fewer than `k` matched edges leads from
a free left vertex to a free right vertex, then every matching `M'` satisfies
`k * |M'| ≤ (k + 1) * |M|`. -/
theorem card_mul_le_of_noShortAug (hM : IsMatching G M) {M' : Finset (L × R)}
    (hM' : IsMatching G M') {k : ℕ} (hk : NoShortAug G M k) :
    k * M'.card ≤ (k + 1) * M.card := by
  have aux : ∀ j < k, (j + 1) * M'.card ≤ (j + 1) * M.card + (altRight G M j).card := by
    intro j
    induction j with
    | zero =>
      intro _
      have h := card_le_size_of_matching_vertexCover hM' (isVertexCover_layerCover (M := M) 0)
      rw [size_layerCover_zero hM] at h
      omega
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have h := card_le_size_of_matching_vertexCover hM'
        (isVertexCover_layerCover (M := M) (j + 1))
      have hs := size_layerCover_succ hM j
      have hinter : altRight G M j ∩ matchedRight M = altRight G M j :=
        Finset.inter_eq_left.mpr (hk j (by omega))
      rw [hinter] at hs
      rw [Nat.add_mul (j + 1) 1, Nat.add_mul (j + 1) 1]
      omega
  cases k with
  | zero => simp
  | succ k =>
    have h := aux k (Nat.lt_succ_self k)
    have hle : (altRight G M k).card ≤ M.card :=
      card_matchedRight hM ▸ Finset.card_le_card (hk k (Nat.lt_succ_self k))
    rw [Nat.add_mul (k + 1) 1]
    omega

end Counting

section Augment

variable {L R : Type*} [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M N : Finset (L × R)}

/-- Replace the edges of `M` at left vertices covered by `N` with the edges of `N`. -/
@[expose] def augment (M N : Finset (L × R)) : Finset (L × R) :=
  N ∪ M.filter fun e => e.1 ∉ matchedLeft N

theorem mem_augment {e : L × R} :
    e ∈ augment M N ↔ e ∈ N ∨ (e ∈ M ∧ e.1 ∉ matchedLeft N) := by
  simp [augment]

/-- Augmenting a matching `M` by a matching `N` gives a matching provided every edge of `M` whose
right end is covered by `N` also has its left end covered by `N`. -/
theorem isMatching_augment (hM : IsMatching G M) (hN : IsMatching G N)
    (hcompat : ∀ u v, (u, v) ∈ M → v ∈ matchedRight N → u ∈ matchedLeft N) :
    IsMatching G (augment M N) := by
  refine ⟨fun e he => ?_, fun u v₁ v₂ h₁ h₂ => ?_, fun u₁ u₂ v h₁ h₂ => ?_⟩
  · rcases mem_augment.mp he with h | ⟨h, _⟩
    · exact hN.1 e h
    · exact hM.1 e h
  · rcases mem_augment.mp h₁ with h₁ | ⟨h₁, n₁⟩ <;> rcases mem_augment.mp h₂ with h₂ | ⟨h₂, n₂⟩
    · exact hN.2.1 u v₁ v₂ h₁ h₂
    · exact absurd (mem_matchedLeft.mpr ⟨v₁, h₁⟩) n₂
    · exact absurd (mem_matchedLeft.mpr ⟨v₂, h₂⟩) n₁
    · exact hM.2.1 u v₁ v₂ h₁ h₂
  · rcases mem_augment.mp h₁ with h₁ | ⟨h₁, n₁⟩ <;> rcases mem_augment.mp h₂ with h₂ | ⟨h₂, n₂⟩
    · exact hN.2.2 u₁ u₂ v h₁ h₂
    · exact absurd (hcompat u₂ v h₂ (mem_matchedRight.mpr ⟨u₁, h₁⟩)) n₂
    · exact absurd (hcompat u₁ v h₁ (mem_matchedRight.mpr ⟨u₂, h₂⟩)) n₁
    · exact hM.2.2 u₁ u₂ v h₁ h₂

/-- Exact size of an augmentation: each newly covered left vertex adds one edge. -/
theorem card_augment (hM : IsMatching G M) (hN : IsMatching G N) :
    (augment M N).card = M.card + (matchedLeft N \ matchedLeft M).card := by
  have hdisj : Disjoint N (M.filter fun e => e.1 ∉ matchedLeft N) := by
    rw [Finset.disjoint_left]
    intro e heN heM
    exact (Finset.mem_filter.mp heM).2 (Finset.mem_image_of_mem _ heN)
  have hsplit := Finset.card_filter_add_card_filter_not (s := M) (fun e => e.1 ∈ matchedLeft N)
  have hinj : Set.InjOn Prod.fst (M.filter fun e => e.1 ∈ matchedLeft N : Set (L × R)) := by
    rintro ⟨u₁, v₁⟩ h₁ ⟨u₂, v₂⟩ h₂ (hu : u₁ = u₂)
    subst hu
    rw [hM.2.1 u₁ v₁ v₂ (Finset.mem_filter.mp h₁).1 (Finset.mem_filter.mp h₂).1]
  have himg : (M.filter fun e => e.1 ∈ matchedLeft N).image Prod.fst =
      matchedLeft N ∩ matchedLeft M := by
    ext u
    rw [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨u', w⟩, he, rfl⟩
      obtain ⟨hMe, hNe⟩ := Finset.mem_filter.mp he
      exact ⟨hNe, mem_matchedLeft.mpr ⟨w, hMe⟩⟩
    · rintro ⟨hN', hM'⟩
      obtain ⟨w, hw⟩ := mem_matchedLeft.mp hM'
      exact ⟨(u, w), Finset.mem_filter.mpr ⟨hw, hN'⟩, rfl⟩
  have hcardIn : (M.filter fun e => e.1 ∈ matchedLeft N).card =
      (matchedLeft N ∩ matchedLeft M).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  have hNsplit := Finset.card_sdiff_add_card_inter (matchedLeft N) (matchedLeft M)
  rw [augment, Finset.card_union_of_disjoint hdisj, ← card_matchedLeft hN]
  omega

/-- The left vertices covered by an augmentation are those covered by `N` or by `M`. -/
theorem matchedLeft_augment : matchedLeft (augment M N) = matchedLeft N ∪ matchedLeft M := by
  ext u
  simp only [Finset.mem_union, mem_matchedLeft, mem_augment]
  constructor
  · rintro ⟨v, h | ⟨h, _⟩⟩
    · exact .inl ⟨v, h⟩
    · exact .inr ⟨v, h⟩
  · rintro (⟨v, h⟩ | ⟨v, h⟩)
    · exact ⟨v, .inl h⟩
    · by_cases hN : ∃ w, (u, w) ∈ N
      · obtain ⟨w, hw⟩ := hN
        exact ⟨w, .inl hw⟩
      · exact ⟨v, .inr ⟨h, hN⟩⟩

end Augment

section AugmentingPath

variable {L R : Type*} [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)}

/-- An `M`-augmenting path `u₀ v₀ u₁ v₁ … uₗ vₗ`, recorded by its non-matching edges
`(uᵢ, vᵢ)`: consecutive ones are joined by matching edges `(uᵢ₊₁, vᵢ) ∈ M`, all vertices are
distinct, and both ends `u₀`, `vₗ` are free. -/
structure IsAugmentingPath (G : L × R → Bool) (M : Finset (L × R)) (p : List (L × R)) :
    Prop where
  ne_nil : p ≠ []
  edge : ∀ e ∈ p, G e = true
  nodup_left : (p.map Prod.fst).Nodup
  nodup_right : (p.map Prod.snd).Nodup
  head_free : ∀ e ∈ p.head?, e.1 ∉ matchedLeft M
  last_free : ∀ e ∈ p.getLast?, e.2 ∉ matchedRight M
  chain : p.IsChain fun a b => (b.1, a.2) ∈ M

omit [DecidableEq L] [DecidableEq R] in
private theorem isChain_mem_compat {p : List (L × R)} (hc : p.IsChain fun a b => (b.1, a.2) ∈ M)
    (hM : IsMatching G M) {u : L} {v : R} (huv : (u, v) ∈ M) {e : L × R} (he : e ∈ p)
    (hv : e.2 = v) : (∃ e' ∈ p.getLast?, e'.2 = v) ∨ u ∈ p.map Prod.fst := by
  induction hc with
  | nil => simp at he
  | singleton a =>
    rw [List.mem_singleton] at he
    subst he
    exact .inl ⟨e, rfl, hv⟩
  | @cons_cons a b l hab _ ih =>
    rcases List.mem_cons.mp he with rfl | he'
    · have hb : b.1 = u := hM.2.2 _ _ _ (hv ▸ hab) huv
      exact .inr (List.mem_map.mpr ⟨b, List.mem_cons_of_mem _ List.mem_cons_self, hb⟩)
    · rcases ih he' with ⟨e', he', hv'⟩ | hu
      · exact .inl ⟨e', by rwa [List.getLast?_cons_cons], hv'⟩
      · exact .inr (List.mem_cons_of_mem _ hu)

theorem IsAugmentingPath.isMatching_toFinset {p : List (L × R)} (hp : IsAugmentingPath G M p) :
    IsMatching G p.toFinset := by
  refine ⟨fun e he => hp.edge e (List.mem_toFinset.mp he), fun u v₁ v₂ h₁ h₂ => ?_,
    fun u₁ u₂ v h₁ h₂ => ?_⟩
  · have h := List.inj_on_of_nodup_map hp.nodup_left (List.mem_toFinset.mp h₁)
      (List.mem_toFinset.mp h₂) rfl
    exact congrArg Prod.snd h
  · have h := List.inj_on_of_nodup_map hp.nodup_right (List.mem_toFinset.mp h₁)
      (List.mem_toFinset.mp h₂) rfl
    exact congrArg Prod.fst h

theorem IsAugmentingPath.compat {p : List (L × R)} (hp : IsAugmentingPath G M p)
    (hM : IsMatching G M) :
    ∀ u v, (u, v) ∈ M → v ∈ matchedRight p.toFinset → u ∈ matchedLeft p.toFinset := by
  intro u v huv hv
  obtain ⟨u', hu'⟩ := mem_matchedRight.mp hv
  rcases isChain_mem_compat hp.chain hM huv (List.mem_toFinset.mp hu') rfl with
    ⟨e', he', hv'⟩ | hu
  · exact absurd (mem_matchedRight.mpr ⟨u, hv' ▸ huv⟩) (hp.last_free e' he')
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
    exact mem_matchedLeft.mpr ⟨e.2, List.mem_toFinset.mpr he⟩

omit [DecidableEq L] [DecidableEq R] in
private theorem isChain_fst_mem {p : List (L × R)} (hc : p.IsChain fun a b => (b.1, a.2) ∈ M)
    {e : L × R} (he : e ∈ p) : (∃ h ∈ p.head?, h = e) ∨ ∃ a ∈ p, (e.1, a.2) ∈ M := by
  induction hc with
  | nil => simp at he
  | singleton a =>
    rw [List.mem_singleton] at he
    exact .inl ⟨a, rfl, he.symm⟩
  | @cons_cons a b l hab _ ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl ⟨e, rfl, rfl⟩
    · rcases ih he with ⟨h, hh, rfl⟩ | ⟨a', ha', hM'⟩
      · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hh
        subst hh
        exact .inr ⟨a, List.mem_cons_self, hab⟩
      · exact .inr ⟨a', List.mem_cons_of_mem _ ha', hM'⟩

/-- Every left vertex of an augmenting path other than its first is already matched. -/
theorem IsAugmentingPath.matchedLeft_toFinset_subset {p : List (L × R)}
    (hp : IsAugmentingPath G M p) :
    ∀ u ∈ matchedLeft p.toFinset, (∃ h ∈ p.head?, h.1 = u) ∨ u ∈ matchedLeft M := by
  intro u hu
  obtain ⟨v, hv⟩ := mem_matchedLeft.mp hu
  rcases isChain_fst_mem hp.chain (List.mem_toFinset.mp hv) with ⟨h, hh, rfl⟩ | ⟨a, _, hM'⟩
  · exact .inl ⟨_, hh, rfl⟩
  · exact .inr (mem_matchedLeft.mpr ⟨a.2, hM'⟩)

/-- An augmenting path covers a matched left vertex iff it covers its mate. -/
theorem IsAugmentingPath.compat_iff {p : List (L × R)} (hp : IsAugmentingPath G M p)
    (hM : IsMatching G M) :
    ∀ u v, (u, v) ∈ M → (u ∈ matchedLeft p.toFinset ↔ v ∈ matchedRight p.toFinset) := by
  intro u v huv
  refine ⟨fun hu => ?_, hp.compat hM u v huv⟩
  obtain ⟨v', hv'⟩ := mem_matchedLeft.mp hu
  rcases isChain_fst_mem hp.chain (List.mem_toFinset.mp hv') with ⟨h, hh, hhe⟩ | ⟨a, ha, hM'⟩
  · subst hhe
    exact absurd (mem_matchedLeft.mpr ⟨v, huv⟩) (hp.head_free _ hh)
  · rw [hM.2.1 u v a.2 huv hM']
    exact mem_matchedRight.mpr ⟨a.1, List.mem_toFinset.mpr ha⟩

/-- Augmenting along an augmenting path gives a matching. -/
theorem IsAugmentingPath.isMatching_augment {p : List (L × R)} (hp : IsAugmentingPath G M p)
    (hM : IsMatching G M) : IsMatching G (augment M p.toFinset) :=
  MaxFlow.isMatching_augment hM hp.isMatching_toFinset (hp.compat hM)

/-- Augmenting along an augmenting path increases the matching size by one. -/
theorem IsAugmentingPath.card_augment {p : List (L × R)} (hp : IsAugmentingPath G M p)
    (hM : IsMatching G M) : M.card < (augment M p.toFinset).card := by
  rw [MaxFlow.card_augment hM hp.isMatching_toFinset]
  obtain ⟨e₀, l, rfl⟩ := List.ne_nil_iff_exists_cons.mp hp.ne_nil
  have hfree := hp.head_free e₀ rfl
  have hmem : e₀.1 ∈ matchedLeft (e₀ :: l).toFinset :=
    mem_matchedLeft.mpr ⟨e₀.2, by simp⟩
  have : 0 < (matchedLeft (e₀ :: l).toFinset \ matchedLeft M).card :=
    Finset.card_pos.mpr ⟨e₀.1, Finset.mem_sdiff.mpr ⟨hmem, hfree⟩⟩
  omega

/-- A maximum matching has no augmenting path (the easy direction of Berge's theorem). -/
theorem IsMaxMatching.not_isAugmentingPath (hM : IsMaxMatching G M) {p : List (L × R)} :
    ¬ IsAugmentingPath G M p := fun hp =>
  absurd (hM.2 _ (hp.isMatching_augment hM.1)) (not_le.mpr (hp.card_augment hM.1))

end AugmentingPath

section Layered

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)}

/-- `IsLayeredPath G M U k u i p`: `p` lists the non-matching edges of an alternating path that
starts at `u` in exact layer `i`, visits exact layers `i, i + 1, …, k`, avoids the right vertices
in `U`, and ends at a free right vertex. -/
inductive IsLayeredPath (G : L × R → Bool) (M : Finset (L × R)) (U : Finset R) (k : ℕ) :
    L → ℕ → List (L × R) → Prop
  | last {u : L} {v : R} : IsLayer G M u k → G (u, v) = true → v ∉ matchedRight M → v ∉ U →
      IsLayeredPath G M U k u k [(u, v)]
  | cons {u u' : L} {v : R} {i : ℕ} {p : List (L × R)} : IsLayer G M u i → G (u, v) = true →
      (u', v) ∈ M → v ∉ U → IsLayeredPath G M U k u' (i + 1) p →
      IsLayeredPath G M U k u i ((u, v) :: p)

/-- `IsLayeredPrefix G M U r u j q`: `q` lists the non-matching edges of an alternating path from
the free vertex `r` to `u` in exact layer `j`, avoiding `U`. -/
inductive IsLayeredPrefix (G : L × R → Bool) (M : Finset (L × R)) (U : Finset R) (r : L) :
    L → ℕ → List (L × R) → Prop
  | root : IsLayer G M r 0 → IsLayeredPrefix G M U r r 0 []
  | snoc {w u : L} {v : R} {j : ℕ} {q : List (L × R)} : IsLayeredPrefix G M U r w j q →
      G (w, v) = true → (u, v) ∈ M → v ∉ U → IsLayer G M u (j + 1) →
      IsLayeredPrefix G M U r u (j + 1) (q ++ [(w, v)])

theorem IsLayeredPath.isLayer {U : Finset R} {k i : ℕ} {u : L} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : IsLayer G M u i := by
  cases h with
  | last hu _ _ _ => exact hu
  | cons hu _ _ _ _ => exact hu

theorem IsLayeredPath.le {U : Finset R} {k i : ℕ} {u : L} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : i ≤ k := by
  induction h with
  | last => exact le_rfl
  | cons _ _ _ _ _ ih => omega

theorem IsLayeredPath.mono {U U' : Finset R} (hU : U' ⊆ U) {k i : ℕ} {u : L}
    {p : List (L × R)} (h : IsLayeredPath G M U k u i p) : IsLayeredPath G M U' k u i p := by
  induction h with
  | last hu hG hv hU' => exact .last hu hG hv fun h => hU' (hU h)
  | cons hu hG hM hU' _ ih => exact .cons hu hG hM (fun h => hU' (hU h)) ih

theorem IsLayeredPrefix.isLayer {U : Finset R} {r u : L} {j : ℕ} {q : List (L × R)}
    (h : IsLayeredPrefix G M U r u j q) : IsLayer G M u j := by
  cases h with
  | root hr => exact hr
  | snoc _ _ _ _ hu => exact hu

theorem IsLayeredPrefix.append {U : Finset R} {k : ℕ} {r u : L} {j : ℕ} {q : List (L × R)}
    (hq : IsLayeredPrefix G M U r u j q) {p : List (L × R)} (hp : IsLayeredPath G M U k u j p) :
    IsLayeredPath G M U k r 0 (q ++ p) := by
  induction hq generalizing p with
  | root _ => exact hp
  | snoc hq' hG hM hv _ ih =>
    rw [List.append_assoc, List.singleton_append]
    exact ih (.cons hq'.isLayer hG hM hv hp)

theorem exists_isLayeredPrefix {u : L} {j : ℕ} (hu : IsLayer G M u j) :
    ∃ r q, IsLayeredPrefix G M ∅ r u j q := by
  induction j generalizing u with
  | zero => exact ⟨u, [], .root hu⟩
  | succ j ih =>
    rcases mem_altLeft_succ.mp hu.1 with h | ⟨v, huv, hv⟩
    · exact absurd h (hu.2 j (Nat.lt_succ_self j))
    obtain ⟨w, hw, hG⟩ := mem_altRight.mp hv
    obtain ⟨i, hij, hwi⟩ := exists_isLayer hw
    rcases Nat.lt_or_eq_of_le hij with hlt | rfl
    · have : u ∈ altLeft G M (i + 1) :=
        mem_altLeft_succ.mpr (.inr ⟨v, huv, mem_altRight.mpr ⟨w, hwi.1, hG⟩⟩)
      exact absurd this (hu.2 (i + 1) (by omega))
    · obtain ⟨r, q, hq⟩ := ih hwi
      exact ⟨r, q ++ [(w, v)], .snoc hq hG huv (Finset.notMem_empty v) hu⟩

end Layered


section LayeredFacts

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)} {U : Finset R} {k : ℕ}

theorem IsLayeredPath.head {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : ∃ v l, p = (u, v) :: l := by
  cases h with
  | @last _ v _ _ _ _ => exact ⟨v, [], rfl⟩
  | @cons _ _ v _ l _ _ _ _ _ => exact ⟨v, l, rfl⟩

theorem IsLayeredPath.edge {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : ∀ e ∈ p, G e = true := by
  induction h with
  | last _ hG _ _ => simpa using hG
  | cons _ hG _ _ _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hG
    · exact ih e he

theorem IsLayeredPath.notMem {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : ∀ e ∈ p, e.2 ∉ U := by
  induction h with
  | last _ _ _ hU => simpa using hU
  | cons _ _ _ hU _ ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact hU
    · exact ih e he

theorem IsLayeredPath.mem_layers {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) :
    ∀ e ∈ p, ∃ j, i ≤ j ∧ IsLayer G M e.1 j ∧
      ((e.2 ∉ matchedRight M ∧ j = k) ∨ ∃ w, (w, e.2) ∈ M ∧ IsLayer G M w (j + 1)) := by
  induction h with
  | last hu _ hv _ =>
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact ⟨_, le_rfl, hu, .inl ⟨hv, rfl⟩⟩
  | @cons u u' v i p hu _ huv _ hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨i, le_rfl, hu, .inr ⟨u', huv, hp.isLayer⟩⟩
    · obtain ⟨j, hj, h⟩ := ih e he
      exact ⟨j, by omega, h⟩

theorem IsLayeredPath.nodup_left {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : (p.map Prod.fst).Nodup := by
  induction h with
  | last => simp
  | @cons u u' v i p hu _ _ _ hp ih =>
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hfst⟩ := List.mem_map.mp hmem
    obtain ⟨j, hj, hl, _⟩ := hp.mem_layers e he
    rw [hfst] at hl
    have := hu.unique hl
    omega

theorem IsLayeredPath.nodup_right (hM : IsMatching G M) {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : (p.map Prod.snd).Nodup := by
  induction h with
  | last => simp
  | @cons u u' v i p hu _ huv _ hp ih =>
    refine List.nodup_cons.mpr ⟨fun hmem => ?_, ih⟩
    obtain ⟨e, he, hsnd⟩ := List.mem_map.mp hmem
    obtain ⟨j, hj, _, hr⟩ := hp.mem_layers e he
    rw [hsnd] at hr
    rcases hr with ⟨hfree, _⟩ | ⟨w, hw, hwl⟩
    · exact hfree (mem_matchedRight.mpr ⟨u', huv⟩)
    · have hwu : w = u' := hM.2.2 _ _ _ hw huv
      subst hwu
      have := hp.isLayer.unique hwl
      omega

theorem IsLayeredPath.chain {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : p.IsChain fun a b => (b.1, a.2) ∈ M := by
  induction h with
  | last => exact .singleton _
  | @cons u u' v i p _ _ huv _ hp ih =>
    obtain ⟨v', l, rfl⟩ := hp.head
    exact .cons_cons huv ih

theorem IsLayeredPath.last_free {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) : ∀ e ∈ p.getLast?, e.2 ∉ matchedRight M := by
  induction h with
  | last _ _ hv _ =>
    intro e he
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at he
    subst he
    exact hv
  | @cons u u' v i p _ _ _ _ hp ih =>
    obtain ⟨v', l, rfl⟩ := hp.head
    intro e he
    rw [List.getLast?_cons_cons] at he
    exact ih e he

/-- A layered path starting in layer `0` is an augmenting path. -/
theorem IsLayeredPath.isAugmentingPath (hM : IsMatching G M) {u : L} {p : List (L × R)}
    (h : IsLayeredPath G M U k u 0 p) : IsAugmentingPath G M p := by
  obtain ⟨v, l, rfl⟩ := h.head
  refine ⟨List.cons_ne_nil _ _, h.edge, h.nodup_left, h.nodup_right hM, ?_, h.last_free,
    h.chain⟩
  intro e he
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
  subst he
  exact isLayer_zero.mp h.isLayer

/-- If `M` has no augmenting path, then no alternating layer reaches a free right vertex. -/
theorem noShortAug_of_forall_not_isAugmentingPath (hM : IsMatching G M)
    (h : ∀ p, ¬ IsAugmentingPath G M p) (k : ℕ) : NoShortAug G M k := by
  intro j _ v hv
  by_contra hfree
  obtain ⟨w, hw, hG⟩ := mem_altRight.mp hv
  obtain ⟨i, _, hwi⟩ := exists_isLayer hw
  obtain ⟨r, q, hq⟩ := exists_isLayeredPrefix hwi
  have hp : IsLayeredPath G M ∅ i w i [(w, v)] :=
    .last hwi hG hfree (Finset.notMem_empty v)
  exact h _ ((hq.append hp).isAugmentingPath hM)

omit [Fintype L] [Fintype R] in
/-- **Berge's theorem** (bipartite case): a matching is maximum iff it has no augmenting path. -/
theorem isMaxMatching_iff_forall_not_isAugmentingPath [Finite L] [Finite R] :
    IsMaxMatching G M ↔ IsMatching G M ∧ ∀ p, ¬ IsAugmentingPath G M p := by
  have := Fintype.ofFinite L
  have := Fintype.ofFinite R
  refine ⟨fun h => ⟨h.1, fun _ => h.not_isAugmentingPath⟩, fun ⟨hM, h⟩ => ⟨hM, fun M' hM' => ?_⟩⟩
  have hk := card_mul_le_of_noShortAug hM hM'
    (noShortAug_of_forall_not_isAugmentingPath hM h (M.card + 1))
  by_contra hlt
  have h2 : (M.card + 1) * (M.card + 1) ≤ (M.card + 1) * M'.card :=
    Nat.mul_le_mul_left _ (Nat.lt_of_not_le hlt)
  have h3 := le_trans h2 hk
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at h3
  omega

theorem IsLayeredPath.mem_left {u : L} {i : ℕ} {p : List (L × R)}
    (h : IsLayeredPath G M U k u i p) :
    ∀ e ∈ p, e.1 = u ∨ ∃ e' ∈ p, (e.1, e'.2) ∈ M := by
  induction h with
  | last =>
    intro e he
    rw [List.mem_singleton] at he
    exact .inl (by rw [he])
  | @cons u u' v i p _ _ huv _ hp ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact .inl rfl
    · rcases ih e he with h | ⟨e', he', h⟩
      · exact .inr ⟨(u, v), List.mem_cons_self, by rw [h]; exact huv⟩
      · exact .inr ⟨e', List.mem_cons_of_mem _ he', h⟩

end LayeredFacts

section Family

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)} {k : ℕ}

/-- `IsLayeredFamily G M k l`: `l` is the concatenation of layered paths of length `k` starting
at distinct free left vertices, each avoiding the right vertices used by the later ones. This is
what one depth-first phase of Hopcroft–Karp produces. -/
inductive IsLayeredFamily (G : L × R → Bool) (M : Finset (L × R)) (k : ℕ) :
    List (L × R) → Prop
  | nil : IsLayeredFamily G M k []
  | cons {r : L} {p l : List (L × R)} : IsLayeredFamily G M k l → r ∉ l.map Prod.fst →
      IsLayeredPath G M (matchedRight l.toFinset) k r 0 p → IsLayeredFamily G M k (p ++ l)

theorem IsLayeredFamily.layered {l : List (L × R)} (h : IsLayeredFamily G M k l) :
    ∀ u v, (u, v) ∈ l.toFinset → ∃ i, IsLayer G M u i ∧
      ((v ∉ matchedRight M ∧ i = k) ∨ ∃ w, (w, v) ∈ M ∧ IsLayer G M w (i + 1)) := by
  induction h with
  | nil => simp
  | cons _ _ hp ih =>
    intro u v he
    rw [List.toFinset_append, Finset.mem_union] at he
    rcases he with he | he
    · obtain ⟨j, _, hl, hr⟩ := hp.mem_layers (u, v) (List.mem_toFinset.mp he)
      exact ⟨j, hl, hr⟩
    · exact ih u v he

omit [Fintype L] [Fintype R] in
private theorem mem_matchedLeft_append {p l : List (L × R)} {u : L} :
    u ∈ matchedLeft (p ++ l).toFinset ↔
      u ∈ matchedLeft p.toFinset ∨ u ∈ matchedLeft l.toFinset := by
  simp only [mem_matchedLeft, List.toFinset_append, Finset.mem_union, exists_or]

omit [Fintype L] [Fintype R] in
private theorem mem_matchedRight_append {p l : List (L × R)} {v : R} :
    v ∈ matchedRight (p ++ l).toFinset ↔
      v ∈ matchedRight p.toFinset ∨ v ∈ matchedRight l.toFinset := by
  simp only [mem_matchedRight, List.toFinset_append, Finset.mem_union, exists_or]

theorem IsLayeredFamily.compat (hM : IsMatching G M) {l : List (L × R)}
    (h : IsLayeredFamily G M k l) :
    ∀ u v, (u, v) ∈ M → (u ∈ matchedLeft l.toFinset ↔ v ∈ matchedRight l.toFinset) := by
  induction h with
  | nil => simp
  | @cons r p l _ _ hp ih =>
    intro u v huv
    rw [mem_matchedLeft_append, mem_matchedRight_append]
    constructor
    · rintro (hu | hu)
      · obtain ⟨v', hv'⟩ := mem_matchedLeft.mp hu
        rcases hp.mem_left (u, v') (List.mem_toFinset.mp hv') with hur | ⟨e', he', hM'⟩
        · have hr := isLayer_zero.mp hp.isLayer
          rw [← hur] at hr
          exact absurd (mem_matchedLeft.mpr ⟨v, huv⟩) hr
        · have : e'.2 = v := hM.2.1 _ _ _ hM' huv
          exact .inl (mem_matchedRight.mpr ⟨e'.1, List.mem_toFinset.mpr (this ▸ he')⟩)
      · exact .inr ((ih u v huv).mp hu)
    · rintro (hv | hv)
      · exact .inl ((hp.isAugmentingPath hM).compat hM u v huv hv)
      · exact .inr ((ih u v huv).mpr hv)

theorem IsLayeredFamily.isMatching (hM : IsMatching G M) {l : List (L × R)}
    (h : IsLayeredFamily G M k l) : IsMatching G l.toFinset := by
  induction h with
  | nil => exact ⟨by simp, by simp, by simp⟩
  | @cons r p l hl hr hp ih =>
    have hP := (hp.isAugmentingPath hM).isMatching_toFinset
    have hc := hl.compat hM
    have hU := hp.notMem
    rw [List.toFinset_append]
    refine ⟨fun e he => ?_, fun u v₁ v₂ h₁ h₂ => ?_, fun u₁ u₂ v h₁ h₂ => ?_⟩
    · rcases Finset.mem_union.mp he with he | he
      · exact hP.1 e he
      · exact ih.1 e he
    · -- a left vertex of `p` is not a left vertex of `l`
      have key : ∀ v v', (u, v) ∈ p.toFinset → (u, v') ∈ l.toFinset → False := by
        intro v v' hp' hl'
        rcases hp.mem_left (u, v) (List.mem_toFinset.mp hp') with hur | ⟨e', he', hM'⟩
        · exact hr (List.mem_map.mpr ⟨(u, v'), List.mem_toFinset.mp hl', hur⟩)
        · have := (hc u e'.2 hM').mp (mem_matchedLeft.mpr ⟨v', hl'⟩)
          exact hU e' he' this
      rcases Finset.mem_union.mp h₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp h₂ with h₂ | h₂
      · exact hP.2.1 u v₁ v₂ h₁ h₂
      · exact (key _ _ h₁ h₂).elim
      · exact (key _ _ h₂ h₁).elim
      · exact ih.2.1 u v₁ v₂ h₁ h₂
    · have key : ∀ u u', (u, v) ∈ p.toFinset → (u', v) ∈ l.toFinset → False := fun u u' hp' hl' =>
        hU (u, v) (List.mem_toFinset.mp hp') (mem_matchedRight.mpr ⟨u', hl'⟩)
      rcases Finset.mem_union.mp h₁ with h₁ | h₁ <;> rcases Finset.mem_union.mp h₂ with h₂ | h₂
      · exact hP.2.2 u₁ u₂ v h₁ h₂
      · exact (key _ _ h₁ h₂).elim
      · exact (key _ _ h₂ h₁).elim
      · exact ih.2.2 u₁ u₂ v h₁ h₂

/-- A nonempty layered family starts at a free left vertex. -/
theorem IsLayeredFamily.exists_free {l : List (L × R)} (h : IsLayeredFamily G M k l)
    (hne : l ≠ []) : ∃ u ∈ matchedLeft l.toFinset, u ∉ matchedLeft M := by
  cases h with
  | nil => exact absurd rfl hne
  | @cons r p l _ _ hp =>
    obtain ⟨v, l', rfl⟩ := hp.head
    exact ⟨r, mem_matchedLeft.mpr ⟨v, by simp⟩, isLayer_zero.mp hp.isLayer⟩

theorem IsLayeredFamily.nodup_right (hM : IsMatching G M) {l : List (L × R)}
    (h : IsLayeredFamily G M k l) : (l.map Prod.snd).Nodup := by
  induction h with
  | nil => exact List.nodup_nil
  | @cons r p l _ _ hp ih =>
    rw [List.map_append]
    refine List.nodup_append.mpr ⟨hp.nodup_right hM, ih, ?_⟩
    intro a ha b hb hab
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hb
    exact hp.notMem e he (hab ▸ mem_matchedRight.mpr ⟨e'.1, List.mem_toFinset.mpr he'⟩)

end Family

section Phase

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M N : Finset (L × R)} {k : ℕ}

/-- `N` is the edge set found by one Hopcroft–Karp phase for `M` with shortest augmenting path
parameter `k`: a matching whose edges follow the alternating layers of `M`, ending in layer `k` at
free right vertices, such that each `M`-edge is either kept or replaced at both ends, and no
layered path with `k + 1` non-matching edges from a free left vertex avoids the vertices of `N`. -/
structure IsMaximalLayeredAugmentation (G : L × R → Bool) (M N : Finset (L × R)) (k : ℕ) :
    Prop where
  isMatching : IsMatching G N
  compat : ∀ u v, (u, v) ∈ M → (u ∈ matchedLeft N ↔ v ∈ matchedRight N)
  layered : ∀ u v, (u, v) ∈ N → ∃ i, IsLayer G M u i ∧
    ((v ∉ matchedRight M ∧ i = k) ∨ ∃ w, (w, v) ∈ M ∧ IsLayer G M w (i + 1))
  maximal : ∀ r, r ∉ matchedLeft N → ∀ p, ¬ IsLayeredPath G M (matchedRight N) k r 0 p

/-- A layered family that cannot be extended by a further layered path is a maximal layered
augmentation. -/
theorem IsLayeredFamily.isMaximalLayeredAugmentation (hM : IsMatching G M) {l : List (L × R)}
    (h : IsLayeredFamily G M k l)
    (hmax : ∀ r, r ∉ matchedLeft l.toFinset →
      ∀ p, ¬ IsLayeredPath G M (matchedRight l.toFinset) k r 0 p) :
    IsMaximalLayeredAugmentation G M l.toFinset k :=
  ⟨h.isMatching hM, h.compat hM, h.layered, hmax⟩

namespace IsMaximalLayeredAugmentation

theorem isMatching_augment (hM : IsMatching G M) (hN : IsMaximalLayeredAugmentation G M N k) :
    IsMatching G (augment M N) :=
  MaxFlow.isMatching_augment hM hN.isMatching fun u v huv hv => (hN.compat u v huv).mpr hv

private theorem free_left (_hN : IsMaximalLayeredAugmentation G M N k) {u : L}
    (hu : u ∉ matchedLeft (augment M N)) : u ∉ matchedLeft M ∧ u ∉ matchedLeft N := by
  have hN' : u ∉ matchedLeft N := fun h => by
    obtain ⟨v, hv⟩ := mem_matchedLeft.mp h
    exact hu (mem_matchedLeft.mpr ⟨v, mem_augment.mpr (.inl hv)⟩)
  refine ⟨fun h => ?_, hN'⟩
  obtain ⟨v, hv⟩ := mem_matchedLeft.mp h
  exact hu (mem_matchedLeft.mpr ⟨v, mem_augment.mpr (.inr ⟨hv, hN'⟩)⟩)

private theorem free_right (hN : IsMaximalLayeredAugmentation G M N k) {v : R}
    (hv : v ∉ matchedRight (augment M N)) : v ∉ matchedRight M ∧ v ∉ matchedRight N := by
  have hN' : v ∉ matchedRight N := fun h => by
    obtain ⟨u, hu⟩ := mem_matchedRight.mp h
    exact hv (mem_matchedRight.mpr ⟨u, mem_augment.mpr (.inl hu)⟩)
  refine ⟨fun h => ?_, hN'⟩
  obtain ⟨u, hu⟩ := mem_matchedRight.mp h
  exact hv (mem_matchedRight.mpr ⟨u, mem_augment.mpr
    (.inr ⟨hu, fun hl => hN' ((hN.compat u v hu).mp hl)⟩)⟩)

/-- Alternating layers do not grow after a phase: `altLeft (augment M N) j ⊆ altLeft M j` for
`j ≤ k`. -/
theorem altLeft_augment_subset (hk : NoShortAug G M k) (hN : IsMaximalLayeredAugmentation G M N k)
    {j : ℕ} (hj : j ≤ k) : altLeft G (augment M N) j ⊆ altLeft G M j := by
  induction j with
  | zero =>
    intro u hu
    exact mem_altLeft_zero.mpr (hN.free_left (mem_altLeft_zero.mp hu)).1
  | succ j ih =>
    have ih := ih (by omega)
    intro u hu
    rcases mem_altLeft_succ.mp hu with hu | ⟨v, huv, hv⟩
    · exact altLeft_mono (Nat.le_succ j) (ih hu)
    have hv : v ∈ altRight G M j := rightNbrs_mono ih hv
    rcases mem_augment.mp huv with huv | ⟨huv, _⟩
    · obtain ⟨i, hi, hr⟩ := hN.layered u v huv
      rcases hr with ⟨hfree, _⟩ | ⟨w, hw, hwi⟩
      · exact absurd (hk j (by omega) hv) hfree
      · have := hwi.le_of_mem (mem_altLeft_succ_of_mem hw hv)
        exact altLeft_mono (by omega) hi.1
    · exact mem_altLeft_succ_of_mem huv hv

/-- Vertices in the same exact layer before and after a phase are reached by a layered prefix
from a vertex not covered by `N`, avoiding the right vertices of `N`. -/
private theorem exists_prefix (hk : NoShortAug G M k) (hN : IsMaximalLayeredAugmentation G M N k)
    {j : ℕ} (hj : j ≤ k) {u : L} (hu' : IsLayer G (augment M N) u j) (hu : IsLayer G M u j) :
    ∃ r, r ∉ matchedLeft N ∧ ∃ q, IsLayeredPrefix G M (matchedRight N) r u j q := by
  induction j generalizing u with
  | zero => exact ⟨u, (hN.free_left (isLayer_zero.mp hu')).2, [], .root hu⟩
  | succ j ih =>
    rcases mem_altLeft_succ.mp hu'.1 with h | ⟨v, huv, hv⟩
    · exact absurd h (hu'.2 j (Nat.lt_succ_self j))
    obtain ⟨w, hw, hG⟩ := mem_altRight.mp hv
    obtain ⟨i, hij, hwi'⟩ := exists_isLayer hw
    have hi : i = j := by
      have := hu'.le_of_mem (mem_altLeft_succ_of_mem huv (mem_altRight_of_isLayer hwi' le_rfl hG))
      omega
    rw [hi] at hwi'
    have hvM : v ∈ altRight G M j := rightNbrs_mono (hN.altLeft_augment_subset hk (by omega)) hv
    rcases mem_augment.mp huv with huvN | ⟨huvM, huN⟩
    · obtain ⟨i₂, hi₂, hr⟩ := hN.layered u v huvN
      have h₂ : i₂ = j + 1 := hi₂.unique hu
      rcases hr with ⟨hfree, _⟩ | ⟨w', hw', hw'l⟩
      · exact absurd (hk j (by omega) hvM) hfree
      · have := hw'l.le_of_mem (mem_altLeft_succ_of_mem hw' hvM)
        omega
    · have hvN : v ∉ matchedRight N := fun h => huN ((hN.compat u v huvM).mpr h)
      have hwM : IsLayer G M w j := by
        obtain ⟨i₁, hi₁j, hwi₁⟩ := exists_isLayer (hN.altLeft_augment_subset hk (by omega) hwi'.1)
        rcases Nat.lt_or_eq_of_le hi₁j with hlt | heq
        · have := hu.le_of_mem
            (mem_altLeft_succ_of_mem huvM (mem_altRight_of_isLayer hwi₁ le_rfl hG))
          omega
        · exact heq ▸ hwi₁
      obtain ⟨r, hr, q, hq⟩ := ih (by omega) hwi' hwM
      exact ⟨r, hr, q ++ [(w, v)], .snoc hq hG huvM hvN hu⟩

/-- **Phase lemma** (Hopcroft–Karp). Augmenting `M` along a maximal layered augmentation for the
shortest augmenting path parameter `k` leaves no alternating path with at most `k` matched edges
between free vertices: the shortest augmenting path length strictly increases. -/
theorem noShortAug_augment (hk : NoShortAug G M k) (hN : IsMaximalLayeredAugmentation G M N k) :
    NoShortAug G (augment M N) (k + 1) := by
  intro j hj t ht
  by_contra hfree
  obtain ⟨hfM, hfN⟩ := hN.free_right hfree
  obtain ⟨w, hw, hG⟩ := mem_altRight.mp ht
  obtain ⟨i, hij, hwi'⟩ := exists_isLayer hw
  obtain ⟨i₀, hi₀, hwi₀⟩ := exists_isLayer (hN.altLeft_augment_subset hk (by omega) hwi'.1)
  have hi₀k : k ≤ i₀ := by
    by_contra hlt
    exact hfM (hk i₀ (by omega) (mem_altRight_of_isLayer hwi₀ le_rfl hG))
  have hi : i = k := by omega
  have hi₀' : i₀ = k := by omega
  rw [hi] at hwi'
  rw [hi₀'] at hwi₀
  obtain ⟨r, hr, q, hq⟩ := hN.exists_prefix hk le_rfl hwi' hwi₀
  exact hN.maximal r hr _ (hq.append (.last hwi₀ hG hfM hfN))

/-- A phase covering some free left vertex strictly enlarges the matching. -/
theorem card_lt_card_augment (hM : IsMatching G M) (hN : IsMaximalLayeredAugmentation G M N k)
    {u : L} (hu : u ∈ matchedLeft N) (hfree : u ∉ matchedLeft M) :
    M.card < (augment M N).card := by
  rw [MaxFlow.card_augment hM hN.isMatching]
  have : 0 < (matchedLeft N \ matchedLeft M).card :=
    Finset.card_pos.mpr ⟨u, Finset.mem_sdiff.mpr ⟨hu, hfree⟩⟩
  omega

/-- **Progress.** A nonempty maximal layered augmentation covers a left vertex that was free. -/
theorem exists_free_of_mem (hM : IsMatching G M) (hN : IsMaximalLayeredAugmentation G M N k)
    {e : L × R} (he : e ∈ N) : ∃ u ∈ matchedLeft N, u ∉ matchedLeft M := by
  by_contra hall
  have hall : ∀ u ∈ matchedLeft N, u ∈ matchedLeft M := fun u hu => by
    by_contra h
    exact hall ⟨u, hu, h⟩
  have key : ∀ i u v, IsLayer G M u i → (u, v) ∉ N := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro u v hui huv
      obtain ⟨vM, hvM⟩ := mem_matchedLeft.mp (hall u (mem_matchedLeft.mpr ⟨v, huv⟩))
      obtain ⟨u', hu'⟩ := mem_matchedRight.mp ((hN.compat u vM hvM).mp
        (mem_matchedLeft.mpr ⟨v, huv⟩))
      obtain ⟨i', hi', hr⟩ := hN.layered u' vM hu'
      rcases hr with ⟨hfree, _⟩ | ⟨w, hw, hwl⟩
      · exact hfree (mem_matchedRight.mpr ⟨u, hvM⟩)
      · have hwu : w = u := hM.2.2 _ _ _ hw hvM
        rw [hwu] at hwl
        exact ih i' (by have := hwl.unique hui; omega) u' vM hi' hu'
  obtain ⟨i, hi, _⟩ := hN.layered e.1 e.2 he
  exact key i e.1 e.2 hi he

/-- If a free right vertex is adjacent to layer `k`, a maximal layered augmentation for `k` is
nonempty. -/
theorem exists_mem (hk : NoShortAug G M k) (hN : IsMaximalLayeredAugmentation G M N k) {t : R}
    (ht : t ∈ altRight G M k) (hfree : t ∉ matchedRight M) : ∃ e, e ∈ N := by
  by_contra h0
  have h0 : N = ∅ := Finset.eq_empty_of_forall_notMem fun e he => h0 ⟨e, he⟩
  obtain ⟨w, hw, hG⟩ := mem_altRight.mp ht
  obtain ⟨i, hik, hwi⟩ := exists_isLayer hw
  have hi : i = k := by
    by_contra hne
    exact hfree (hk i (by omega) (mem_altRight_of_isLayer hwi le_rfl hG))
  rw [hi] at hwi
  obtain ⟨r, q, hq⟩ := exists_isLayeredPrefix hwi
  have hp := hq.append (.last hwi hG hfree (Finset.notMem_empty t))
  have hmr : matchedRight N = ∅ := by simp [h0, matchedRight]
  have hml : r ∉ matchedLeft N := by simp [h0, matchedLeft]
  exact hN.maximal r hml (q ++ [(w, t)]) (hmr ▸ hp)

/-- A phase run after a BFS that found a free right vertex in layer `k` strictly enlarges the
matching. -/
theorem card_lt_card_augment_of_mem_altRight (hM : IsMatching G M) (hk : NoShortAug G M k)
    (hN : IsMaximalLayeredAugmentation G M N k) {t : R} (ht : t ∈ altRight G M k)
    (hfree : t ∉ matchedRight M) : M.card < (augment M N).card := by
  obtain ⟨e, he⟩ := hN.exists_mem hk ht hfree
  obtain ⟨u, hu, hu'⟩ := hN.exists_free_of_mem hM he
  exact hN.card_lt_card_augment hM hu hu'

end IsMaximalLayeredAugmentation

end Phase

section PhaseCount

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable {G : L × R → Bool} {M : Finset (L × R)}

/-- Deficit bound: if no augmenting path has fewer than `t` matched edges, then `M` is within
`|M| / t` of every matching. -/
theorem mul_card_sub_le_of_noShortAug (hM : IsMatching G M) {M' : Finset (L × R)}
    (hM' : IsMatching G M') {t : ℕ} (ht : NoShortAug G M t) :
    t * (M'.card - M.card) ≤ M.card := by
  have h := card_mul_le_of_noShortAug hM hM' ht
  rcases Nat.lt_or_ge M.card M'.card with hlt | hle
  · obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_lt hlt
    rw [hg] at h ⊢
    rw [show M.card + g + 1 - M.card = g + 1 by omega]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one] at h ⊢
    omega
  · rw [Nat.sub_eq_zero_of_le hle, Nat.mul_zero]
    exact Nat.zero_le _

/-- `IsPhaseRun G M n`: starting from `M`, `n` Hopcroft–Karp phases are performed. Each phase
follows a breadth-first search that found the shortest augmenting path parameter `k` (no free
right vertex in layers `< k`, one in layer `k`) and augments along a maximal layered
augmentation. -/
inductive IsPhaseRun (G : L × R → Bool) : Finset (L × R) → ℕ → Prop
  | done {M : Finset (L × R)} : IsPhaseRun G M 0
  | step {M N : Finset (L × R)} {k n : ℕ} {t : R} : NoShortAug G M k → t ∈ altRight G M k →
      t ∉ matchedRight M → IsMaximalLayeredAugmentation G M N k →
      IsPhaseRun G (augment M N) n → IsPhaseRun G M (n + 1)

/-- **Hopcroft–Karp phase bound.** A run of `n` phases from a matching `M` with no augmenting path
shorter than `t` satisfies `n + |M| ≤ ν` and, when `t ≤ ⌊√ν⌋`, `t + n ≤ 2⌊√ν⌋`, where `ν` is the
maximum matching size. In particular, from the empty matching at most `2⌊√ν⌋` phases occur. -/
theorem IsPhaseRun.add_card_le_and_add_le_two_mul_sqrt (hM : IsMatching G M) {n : ℕ}
    (hrun : IsPhaseRun G M n) {t : ℕ} (ht : NoShortAug G M t) {M' : Finset (L × R)}
    (hM' : IsMaxMatching G M') :
    n + M.card ≤ M'.card ∧ (t ≤ Nat.sqrt M'.card → t + n ≤ 2 * Nat.sqrt M'.card) := by
  induction hrun generalizing t with
  | done =>
    exact ⟨by simpa using hM'.2 _ hM, fun h => by omega⟩
  | @step M N k n x hk hx hfree hN _ ih =>
    have htk : t ≤ k := by
      by_contra hlt
      exact hfree (ht k (by omega) hx)
    have hM₁ := hN.isMatching_augment hM
    have hlt := hN.card_lt_card_augment_of_mem_altRight hM hk hx hfree
    have hk₁ : NoShortAug G (augment M N) (t + 1) :=
      (hN.noShortAug_augment hk).mono (by omega)
    obtain ⟨ih₁, ih₂⟩ := ih hM₁ hk₁
    refine ⟨by omega, fun hts => ?_⟩
    rcases Nat.lt_or_eq_of_le hts with hts | hts
    · have := ih₂ (by omega)
      omega
    · -- `t = ⌊√ν⌋`: the deficit of `M` is below `t + 1`.
      have hdef := mul_card_sub_le_of_noShortAug hM hM'.1 ht
      have hsq : M'.card < (t + 1) * (t + 1) := by
        have := Nat.lt_succ_sqrt M'.card
        rw [← hts] at this
        exact this
      have h2 : M.card ≤ M'.card := hM'.2 _ hM
      have hg : (t + 1) * (M'.card - M.card) < (t + 1) * (t + 1) := by
        have : (t + 1) * (M'.card - M.card) = t * (M'.card - M.card) + (M'.card - M.card) := by
          rw [Nat.add_mul, Nat.one_mul]
        omega
      have := Nat.lt_of_mul_lt_mul_left hg
      omega

/-- From the empty matching, Hopcroft–Karp performs at most `2⌊√ν⌋` augmenting phases. -/
theorem IsPhaseRun.le_two_mul_sqrt {n : ℕ} (hrun : IsPhaseRun G ∅ n) {M' : Finset (L × R)}
    (hM' : IsMaxMatching G M') : n ≤ 2 * Nat.sqrt M'.card := by
  have h0 : IsMatching G (∅ : Finset (L × R)) := ⟨by simp, by simp, by simp⟩
  simpa using (hrun.add_card_le_and_add_le_two_mul_sqrt h0 (t := 0)
    (fun _ h => absurd h (Nat.not_lt_zero _)) hM').2 (Nat.zero_le _)

/-- If the alternating layers of `M` stop growing at `j` and reach no free right vertex, then the
layer cover at `j` has size `|M|`. -/
theorem size_layerCover_of_stable (hM : IsMatching G M) {j : ℕ}
    (hstable : altLeft G M (j + 1) = altLeft G M j) (hj : altRight G M j ⊆ matchedRight M) :
    (layerCover G M j).size = M.card := by
  have h := size_layerCover_succ hM j
  have hR : altRight G M (j + 1) = altRight G M j := by
    simp only [altRight, hstable]
  have hC : layerCover G M (j + 1) = layerCover G M j := by
    simp only [layerCover, hstable, hR]
  rw [hC, hR, Finset.inter_eq_left.mpr hj] at h
  omega

/-- **König certificate from a closed BFS.** When the alternating layers stop growing without
reaching a free right vertex, `M` is a maximum matching and the layer cover is a minimum vertex
cover of the same size. -/
theorem isMaxMatching_isMinVertexCover_of_stable (hM : IsMatching G M) {j : ℕ}
    (hstable : altLeft G M (j + 1) = altLeft G M j) (hj : altRight G M j ⊆ matchedRight M) :
    IsMaxMatching G M ∧ IsMinVertexCover G (layerCover G M j) := by
  have hsize := size_layerCover_of_stable hM hstable hj
  refine ⟨⟨hM, fun M' hM' => ?_⟩, isVertexCover_layerCover j, fun C hC => ?_⟩
  · have := card_le_size_of_matching_vertexCover hM' (isVertexCover_layerCover (M := M) j)
    omega
  · have := card_le_size_of_matching_vertexCover hM hC
    omega

/-- Under stability, the right vertices reached by the layers are exactly the mates of reached
left vertices. -/
theorem mem_altRight_iff_of_stable (hM : IsMatching G M) {j : ℕ}
    (hstable : altLeft G M (j + 1) = altLeft G M j) (hj : altRight G M j ⊆ matchedRight M)
    {v : R} : v ∈ altRight G M j ↔ ∃ w, (w, v) ∈ M ∧ w ∈ altLeft G M j := by
  constructor
  · intro hv
    obtain ⟨w, hw⟩ := mem_matchedRight.mp (hj hv)
    exact ⟨w, hw, hstable ▸ mem_altLeft_succ_of_mem hw hv⟩
  · rintro ⟨w, hw, hwj⟩
    obtain ⟨i, hij, hwi⟩ := exists_isLayer hwj
    cases i with
    | zero => exact absurd (mem_matchedLeft.mpr ⟨v, hw⟩) (isLayer_zero.mp hwi)
    | succ i =>
      rcases mem_altLeft_succ.mp hwi.1 with h | ⟨v', hv', hv'i⟩
      · exact absurd h (hwi.2 i (Nat.lt_succ_self i))
      · rw [hM.2.1 _ _ _ hw hv']
        exact altRight_mono (by omega) hv'i

end PhaseCount

end Cslib.Algorithms.Lean.MaxFlow
