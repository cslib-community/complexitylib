/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Crown.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Set.Card

/-!
# Crown decompositions and the linear kernel for vertex cover

A *crown* of a graph `G` [ChorFellowsJuedes2004] [AbuKhzamFellowsLangstonSuters2007]
[CyganEtAl2015, Section 2.3] is a pair `(C, H)` of finite vertex sets such that `C` is
independent, `H` is the neighbourhood of `C`, and `H` matches into `C`
(`SimpleGraph.IsCrown`); the remaining vertices `R = (C ∪ H)ᶜ` have no neighbour in `C`. The
cited definitions require `C` to be nonempty; `SimpleGraph.IsCrown` allows `C = ∅` (then `H = ∅`)
so that crowns compose (`SimpleGraph.IsCrown.union_map`), and results that need a nonempty crown
say so. A matching of `A` into `B` is recorded by the partner map `m`
(`SimpleGraph.IsMatchingInto`); `SimpleGraph.IsMatchingInto.exists_isMatching` converts it to a
Mathlib `SimpleGraph.Subgraph.IsMatching`.

*Reduction rule.* Some minimum vertex cover contains `H` and avoids `C`, so
`τ(G) = τ(G[R]) + |H|` (`SimpleGraph.IsCrown.vertexCoverNum_eq`): `G` has a vertex cover of at
most `k` vertices exactly when `|H| ≤ k` and `G[R]` has one of at most `k - |H|` vertices
(`SimpleGraph.IsCrown.vertexCoverNum_le_iff`).

*Crown lemma.* If `G` has more than `3k` vertices, then `G` has a matching of more than `k`
edges, or a crown with `C` nonempty (`SimpleGraph.exists_isMatchingInto_or_exists_isCrown`); if
`G` has no isolated vertices, then also `H` is nonempty
(`SimpleGraph.exists_isMatchingInto_or_exists_isCrown_of_forall_exists_adj`). The proof takes a
maximum matching `M`, of at most `k` edges. The unmatched vertices form an independent set `I`
of more than `k` vertices. By Hall's theorem, either `I` matches into its neighbourhood, a
matching of more than `k` edges, or some `S ⊆ I` has fewer neighbours than vertices; a subset
of `I` of maximum surplus `|Y| - |N(Y)|` is then a crown (`SimpleGraph.exists_isCrown_of_card_lt`).
Hall's theorem takes the place of Kőnig's theorem in the usual textbook argument.

*Kernel.* A crown with the largest `C ∪ H` leaves a residual graph without nonempty crowns
(`SimpleGraph.exists_isCrown_forall_isCrown_eq_empty`). Applying the crown lemma to that residual
gives the `3k` kernel (`SimpleGraph.exists_isMatchingInto_or_exists_isCrown_card_compl_le`): a
matching of more than `k` edges, or a crown with `|H| ≤ k` whose residual has at most
`3 (k - |H|)` vertices. By the reduction rule, `(G - (C ∪ H), k - |H|)` is then an equivalent
instance with at most `3 (k - |H|)` vertices.

A graph without nonempty crowns has at most `2 |S|` vertices for every vertex cover `S`
(`SimpleGraph.card_le_two_mul_card_of_forall_isCrown_eq_empty`), since the complement of `S` is an
independent set at least as large as its neighbourhood. Hence a single crown leaves a residual
of at most `2 (k - |H|)` vertices for every `k ≥ τ(G)`
(`SimpleGraph.exists_isCrown_forall_card_compl_le`). This matches the `2k` size of the LP-based
(Nemhauser–Trotter) kernel, whose relation to crowns is studied in
[AbuKhzamFellowsLangstonSuters2007].

These are combinatorial existence statements about `SimpleGraph`s. They do not construct crowns
algorithmically and do not give a polynomial-time kernelization
(`Cslib.Complexity.IsKernelization`) of the encoded problem `Cslib.Complexity.VertexCover`; that
needs a polynomial-time maximum matching or Kőnig cover in the machine model.

## Main definitions

* `SimpleGraph.IsMatchingInto`: `m` matches `A` into `B`.
* `SimpleGraph.IsCrown`: `(C, H)` is a crown.

## Main results

* `SimpleGraph.IsMatchingInto.card_le_vertexCoverNum`: a matching bounds the vertex cover number.
* `SimpleGraph.isCrown_iff_forall_card_le`: Hall's criterion for crowns.
* `SimpleGraph.IsCrown.vertexCoverNum_eq`, `SimpleGraph.IsCrown.vertexCoverNum_le_iff`: the crown
  reduction rule.
* `SimpleGraph.exists_isMatchingInto_or_exists_isCrown`,
  `SimpleGraph.exists_isMatchingInto_or_exists_isCrown_of_forall_exists_adj`: the crown lemma.
* `SimpleGraph.exists_isMatchingInto_or_exists_isCrown_card_compl_le`: the `3k` kernel.
* `SimpleGraph.card_le_two_mul_card_of_forall_isCrown_eq_empty`,
  `SimpleGraph.exists_isCrown_forall_card_compl_le`: the `2k` bound for crown-free residuals.

## References

* [B. Chor, M. Fellows, D. Juedes, *Linear kernels in linear time, or how to save `k` colors in
  `O(n²)` steps*][ChorFellowsJuedes2004]
* [F. N. Abu-Khzam, M. R. Fellows, M. A. Langston, W. H. Suters, *Crown structures for vertex
  cover kernelization*][AbuKhzamFellowsLangstonSuters2007]
* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- `m` matches `A` into `B` in `G`: it sends the vertices of `A` to distinct neighbours in `B`.
When `A` and `B` are disjoint, as in every result below that counts edges, the edges `{a, m a}` for
`a ∈ A` form a matching of `|A|` edges (`SimpleGraph.IsMatchingInto.exists_isMatching`); without
disjointness two of them may coincide. -/
structure IsMatchingInto (G : SimpleGraph V) (A B : Finset V) (m : V → V) : Prop where
  /-- Every vertex of `A` is matched into `B`. -/
  mapsTo : ∀ a ∈ A, m a ∈ B
  /-- Every vertex of `A` is matched to a neighbour. -/
  adj : ∀ a ∈ A, G.Adj a (m a)
  /-- Distinct vertices of `A` have distinct partners. -/
  injOn : Set.InjOn m A

/-- `(C, H)` is a *crown* of `G` [CyganEtAl2015, Section 2.3]: `C` is an independent set, `H` is
its neighbourhood, and `H` matches into `C`. Unlike the cited definition, `C` may be empty. -/
structure IsCrown (G : SimpleGraph V) (C H : Finset V) : Prop where
  /-- The crown `C` is an independent set. -/
  isIndepSet : G.IsIndepSet C
  /-- The head `H` is the neighbourhood of `C`. -/
  mem_head_iff : ∀ v, v ∈ H ↔ ∃ c ∈ C, G.Adj c v
  /-- The head `H` matches into `C`. -/
  exists_isMatchingInto : ∃ m, G.IsMatchingInto H C m

namespace IsMatchingInto

variable {A B : Finset V} {m : V → V}

/-- A vertex cover `S` contains at least `|A|` vertices of `A ∪ B`: one endpoint of each matching
edge. -/
theorem card_le_encard_inter (hm : G.IsMatchingInto A B m) (hAB : Disjoint A B) {S : Set V}
    (hS : G.IsVertexCover S) : (A.card : ℕ∞) ≤ (S ∩ (↑A ∪ ↑B)).encard := by
  classical
  let g : V → V := fun a => if a ∈ S then a else m a
  have hg : Set.MapsTo g A (S ∩ (↑A ∪ ↑B)) := fun a ha => by
    have ha : a ∈ A := ha
    by_cases haS : a ∈ S
    · simp only [g, haS, ↓reduceIte]
      exact ⟨haS, Or.inl ha⟩
    · simp only [g, haS, ↓reduceIte]
      exact ⟨(hS (hm.adj a ha)).resolve_left haS, Or.inr (hm.mapsTo a ha)⟩
  have hgi : Set.InjOn g A := by
    intro a ha b hb hab
    have ha : a ∈ A := ha
    have hb : b ∈ A := hb
    by_cases haS : a ∈ S <;> by_cases hbS : b ∈ S <;>
      simp only [g, haS, hbS, ↓reduceIte] at hab
    · exact hab
    · exact absurd (hab ▸ hm.mapsTo b hb) (Finset.disjoint_left.1 hAB ha)
    · exact absurd (hab ▸ hm.mapsTo a ha) (Finset.disjoint_left.1 hAB hb)
    · exact hm.injOn ha hb hab
  rw [← Set.encard_coe_eq_coe_finsetCard, ← hgi.encard_image]
  exact Set.encard_le_encard (Set.image_subset_iff.2 hg)

/-- **Matchings bound vertex covers**: a matching of `A` into a disjoint `B` has `|A|` edges, so
every vertex cover has at least `|A|` vertices. -/
theorem card_le_vertexCoverNum (hm : G.IsMatchingInto A B m) (hAB : Disjoint A B) :
    (A.card : ℕ∞) ≤ G.vertexCoverNum := by
  obtain ⟨S, hcard, hS⟩ := G.vertexCoverNum_exists
  rw [← hcard]
  exact (hm.card_le_encard_inter hAB hS).trans (Set.encard_le_encard Set.inter_subset_left)

/-- A matching of `A` into a disjoint `B` is a Mathlib matching on `A ∪ m '' A`. -/
theorem exists_isMatching (hm : G.IsMatchingInto A B m) (hAB : Disjoint A B) :
    ∃ M : G.Subgraph, M.verts = ↑A ∪ m '' ↑A ∧ M.IsMatching := by
  have hdisj : Disjoint (A : Set V) (m '' ↑A) := by
    refine Set.disjoint_left.2 fun a ha ⟨b, hb, hba⟩ => ?_
    have hb : b ∈ A := hb
    have : m b ∈ B := hm.mapsTo b hb
    rw [hba] at this
    exact Finset.disjoint_left.1 hAB ha this
  exact Subgraph.IsMatching.exists_of_disjoint_sets_of_equiv hdisj
    (hm.injOn.bijOn_image.equiv m) fun a => hm.adj a a.2

end IsMatchingInto

namespace IsCrown

variable {C H : Finset V}

/-- The head and the crown are disjoint. -/
theorem disjoint (h : G.IsCrown C H) : Disjoint H C := by
  refine Finset.disjoint_left.2 fun v hvH hvC => ?_
  obtain ⟨c, hc, hcv⟩ := (h.mem_head_iff v).1 hvH
  exact h.isIndepSet hc hvC hcv.ne hcv

/-- **Crown reduction**: removing a crown `(C, H)` decreases the vertex cover number by `|H|`.
Some minimum vertex cover contains `H` and avoids `C`. -/
theorem vertexCoverNum_eq (h : G.IsCrown C H) :
    G.vertexCoverNum = (G.induce (↑C ∪ ↑H : Set V)ᶜ).vertexCoverNum + H.card := by
  classical
  set R : Set V := (↑C ∪ ↑H : Set V)ᶜ
  obtain ⟨m, hm⟩ := h.exists_isMatchingInto
  apply le_antisymm
  · obtain ⟨S', hcard, hS'⟩ := (G.induce R).vertexCoverNum_exists
    have hcov : G.IsVertexCover (((↑) : R → V) '' S' ∪ ↑H) := by
      intro u v huv
      by_cases huH : u ∈ H
      · exact Or.inl (Or.inr huH)
      by_cases hvH : v ∈ H
      · exact Or.inr (Or.inr hvH)
      by_cases huC : u ∈ C
      · exact absurd ((h.mem_head_iff v).2 ⟨u, huC, huv⟩) hvH
      by_cases hvC : v ∈ C
      · exact absurd ((h.mem_head_iff u).2 ⟨v, hvC, huv.symm⟩) huH
      have hu : u ∈ R := by simp [R, huC, huH]
      have hv : v ∈ R := by simp [R, hvC, hvH]
      rcases hS' (show (G.induce R).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv) with h' | h'
      · exact Or.inl (Or.inl ⟨_, h', rfl⟩)
      · exact Or.inr (Or.inl ⟨_, h', rfl⟩)
    calc G.vertexCoverNum ≤ (((↑) : R → V) '' S' ∪ ↑H).encard := hcov.vertexCoverNum_le
      _ ≤ (((↑) : R → V) '' S').encard + (↑H : Set V).encard := Set.encard_union_le _ _
      _ = _ := by
        rw [Subtype.val_injective.encard_image, hcard, Set.encard_coe_eq_coe_finsetCard]
  · obtain ⟨S, hcard, hS⟩ := G.vertexCoverNum_exists
    have hS' : (G.induce R).IsVertexCover (((↑) : R → V) ⁻¹' S) := fun u v huv => hS huv
    have h₁ : (G.induce R).vertexCoverNum ≤ (S ∩ R).encard := by
      have := hS'.vertexCoverNum_le
      rwa [← Subtype.val_injective.encard_image, Subtype.image_preimage_coe, Set.inter_comm] at this
    have h₂ : (H.card : ℕ∞) ≤ (S ∩ (↑H ∪ ↑C)).encard := hm.card_le_encard_inter h.disjoint hS
    have hdisj : Disjoint (S ∩ R) (S ∩ (↑H ∪ ↑C)) := by
      refine Set.disjoint_left.2 fun v hv hv' => hv.2 ?_
      rcases hv'.2 with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
    rw [← hcard]
    calc (G.induce R).vertexCoverNum + H.card ≤ (S ∩ R).encard + (S ∩ (↑H ∪ ↑C)).encard := by gcongr
      _ = (S ∩ R ∪ S ∩ (↑H ∪ ↑C)).encard := (Set.encard_union_eq hdisj).symm
      _ ≤ S.encard := Set.encard_le_encard (Set.union_subset Set.inter_subset_left
          Set.inter_subset_left)

/-- **The crown reduction rule** [CyganEtAl2015, Section 2.3]: `G` has a vertex cover of at most
`k` vertices exactly when `|H| ≤ k` and the residual graph `G - (C ∪ H)` has one of at most
`k - |H|` vertices. -/
theorem vertexCoverNum_le_iff (h : G.IsCrown C H) {k : ℕ} :
    G.vertexCoverNum ≤ k ↔
      H.card ≤ k ∧ (G.induce (↑C ∪ ↑H : Set V)ᶜ).vertexCoverNum ≤ (k - H.card : ℕ) := by
  rw [h.vertexCoverNum_eq]
  generalize (G.induce (↑C ∪ ↑H : Set V)ᶜ).vertexCoverNum = x
  induction x using ENat.recTopCoe with
  | top => simp
  | coe x => norm_cast; omega

/-- A nonempty crown whose vertices are not isolated has a nonempty head. -/
theorem head_nonempty (h : G.IsCrown C H) (hC : C.Nonempty) (hadj : ∀ c ∈ C, ∃ v, G.Adj c v) :
    H.Nonempty := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨v, hcv⟩ := hadj c hc
  exact ⟨v, (h.mem_head_iff v).2 ⟨c, hc, hcv⟩⟩

end IsCrown

/-- The empty crown. -/
theorem isCrown_empty : G.IsCrown ∅ ∅ :=
  ⟨by simp, by simp, ⟨id, by simp, by simp, by simp⟩⟩

/-- Matchings into disjoint sets combine. -/
theorem IsMatchingInto.union [DecidableEq V] {A B A' B' : Finset V} {m m' : V → V}
    (hm : G.IsMatchingInto A B m) (hm' : G.IsMatchingInto A' B' m') (hBB' : Disjoint B B') :
    ∃ m'', G.IsMatchingInto (A ∪ A') (B ∪ B') m'' := by
  classical
  refine ⟨fun v => if v ∈ A then m v else m' v, fun a ha => ?_, fun a ha => ?_,
    fun a ha b hb hab => ?_⟩
  · by_cases haA : a ∈ A
    · simp only [haA, ↓reduceIte]
      exact Finset.mem_union_left _ (hm.mapsTo a haA)
    · simp only [haA, ↓reduceIte]
      exact Finset.mem_union_right _
        (hm'.mapsTo a ((Finset.mem_union.1 ha).resolve_left haA))
  · by_cases haA : a ∈ A
    · simp only [haA, ↓reduceIte]
      exact hm.adj a haA
    · simp only [haA, ↓reduceIte]
      exact hm'.adj a ((Finset.mem_union.1 ha).resolve_left haA)
  · have ha : a ∈ A ∪ A' := ha
    have hb : b ∈ A ∪ A' := hb
    by_cases haA : a ∈ A <;> by_cases hbA : b ∈ A <;> simp only [haA, hbA, ↓reduceIte] at hab
    · exact hm.injOn haA hbA hab
    · exact absurd (hm'.mapsTo b ((Finset.mem_union.1 hb).resolve_left hbA))
        (Finset.disjoint_left.1 hBB' (hab ▸ hm.mapsTo a haA))
    · exact absurd (hm'.mapsTo a ((Finset.mem_union.1 ha).resolve_left haA))
        (Finset.disjoint_left.1 hBB' (hab.symm ▸ hm.mapsTo b hbA))
    · exact hm'.injOn ((Finset.mem_union.1 ha).resolve_left haA)
        ((Finset.mem_union.1 hb).resolve_left hbA) hab

/-- A matching in an induced subgraph is a matching in the graph. -/
theorem IsMatchingInto.map_subtype {R : Set V} {A B : Finset R} {m : R → R}
    (hm : (G.induce R).IsMatchingInto A B m) :
    ∃ m', G.IsMatchingInto (A.map (Function.Embedding.subtype _))
      (B.map (Function.Embedding.subtype _)) m' := by
  classical
  refine ⟨fun v => if h : v ∈ R then (m ⟨v, h⟩ : V) else v, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 ha
    simp only [Function.Embedding.coe_subtype, Subtype.coe_prop, ↓reduceDIte]
    exact Finset.mem_map_of_mem _ (hm.mapsTo a haA)
  · intro a ha
    obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 ha
    simp only [Function.Embedding.coe_subtype, Subtype.coe_prop, ↓reduceDIte]
    exact hm.adj a haA
  · intro a ha b hb hab
    obtain ⟨a, haA, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 ha)
    obtain ⟨b, hbA, rfl⟩ := Finset.mem_map.1 (Finset.mem_coe.1 hb)
    simp only [Function.Embedding.coe_subtype, Subtype.coe_prop, ↓reduceDIte] at hab
    exact congrArg Subtype.val (hm.injOn haA hbA (Subtype.ext hab))


/-! ### Hall's theorem and crowns -/

section Hall

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **Hall's dichotomy**: either `A` matches into `B`, or some `S ⊆ A` has fewer neighbours in
`B` than vertices. -/
theorem exists_isMatchingInto_or_exists_card_lt (A B : Finset V) :
    (∃ m, G.IsMatchingInto A B m) ∨
      ∃ S ⊆ A, ((S.biUnion (fun v => G.neighborFinset v)) ∩ B).card < S.card := by
  by_cases hHall : ∀ S ⊆ A, S.card ≤ ((S.biUnion (fun v => G.neighborFinset v)) ∩ B).card
  · left
    obtain ⟨f, hfi, hf⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun a : A => G.neighborFinset a ∩ B)).1 fun s => by
        have := hHall (s.map (Function.Embedding.subtype _)) (by
          intro x hx
          obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hx
          exact y.2)
        rw [Finset.card_map] at this
        refine this.trans (Finset.card_le_card fun v hv => ?_)
        simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_map,
          Function.Embedding.coe_subtype] at hv ⊢
        obtain ⟨⟨_, ⟨a, ha, rfl⟩, hv⟩, hvB⟩ := hv
        exact ⟨a, ha, hv, hvB⟩
    refine ⟨fun v => if h : v ∈ A then f ⟨v, h⟩ else v, fun a ha => ?_, fun a ha => ?_,
      fun a ha b hb hab => ?_⟩
    · simp only [ha, ↓reduceDIte]
      exact (Finset.mem_inter.1 (hf ⟨a, ha⟩)).2
    · simp only [ha, ↓reduceDIte]
      exact (G.mem_neighborFinset _ _).1 (Finset.mem_inter.1 (hf ⟨a, ha⟩)).1
    · have ha : a ∈ A := ha
      have hb : b ∈ A := hb
      simp only [ha, hb, ↓reduceDIte] at hab
      exact congrArg Subtype.val (hfi hab)
  · right
    push Not at hHall
    exact hHall

variable {I : Finset V}

/-- An independent set with fewer neighbours than vertices contains a nonempty crown: a subset of
maximum surplus `|Y| - |N(Y)|`. -/
theorem exists_isCrown_of_card_lt (hI : G.IsIndepSet I)
    (hlt : (I.biUnion (fun v => G.neighborFinset v)).card < I.card) :
    ∃ C H, C ⊆ I ∧ C.Nonempty ∧ G.IsCrown C H := by
  obtain ⟨Y, hYI, hYmax⟩ := I.powerset.exists_max_image
    (fun Y => (Y.card : ℤ) - (Y.biUnion (fun v => G.neighborFinset v)).card)
    ⟨∅, Finset.empty_mem_powerset _⟩
  rw [Finset.mem_powerset] at hYI
  have hYmax : ∀ Y' ⊆ I, (Y'.card : ℤ) - (Y'.biUnion (fun v => G.neighborFinset v)).card ≤
      Y.card - (Y.biUnion (fun v => G.neighborFinset v)).card := fun Y' hY' =>
    hYmax Y' (Finset.mem_powerset.2 hY')
  have hpos := hYmax I le_rfl
  have hYne : Y.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp only [Finset.card_empty, Finset.biUnion_empty, Nat.cast_zero, sub_zero] at hpos
    omega
  set N := Y.biUnion (fun v => G.neighborFinset v) with hN
  have hmemN : ∀ v, v ∈ N ↔ ∃ c ∈ Y, G.Adj c v := fun v => by
    simp only [hN, Finset.mem_biUnion, mem_neighborFinset]
  refine ⟨Y, N, hYI, hYne, ⟨hI.mono hYI, hmemN, ?_⟩⟩
  rcases G.exists_isMatchingInto_or_exists_card_lt N Y with h | ⟨T, hTN, hT⟩
  · exact h
  exfalso
  set Z := (T.biUnion (fun v => G.neighborFinset v)) ∩ Y
  have hZY : Z ⊆ Y := Finset.inter_subset_right
  have hsub : (Y \ Z).biUnion (fun v => G.neighborFinset v) ⊆ N \ T := by
    intro v hv
    simp only [Finset.mem_biUnion, mem_neighborFinset, Finset.mem_sdiff] at hv
    obtain ⟨y, ⟨hyY, hyZ⟩, hyv⟩ := hv
    refine Finset.mem_sdiff.2 ⟨(hmemN v).2 ⟨y, hyY, hyv⟩, fun hvT => hyZ ?_⟩
    exact Finset.mem_inter.2 ⟨Finset.mem_biUnion.2 ⟨v, hvT, (G.mem_neighborFinset _ _).2
      hyv.symm⟩, hyY⟩
  have h₁ := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hTN] at h₁
  have h₂ := Finset.card_sdiff_of_subset hZY
  have h₃ := Finset.card_le_card hTN
  have h₄ := Finset.card_le_card hZY
  have := hYmax (Y \ Z) ((Finset.sdiff_subset).trans hYI)
  rw [h₂] at this
  push_cast [h₄] at this
  omega

/-- **Hall's criterion for crowns**: `(C, H)` is a crown exactly when `C` is independent, `H` is
its neighbourhood, and every `S ⊆ H` has at least `|S|` neighbours in `C`. -/
theorem isCrown_iff_forall_card_le {C H : Finset V} :
    G.IsCrown C H ↔ G.IsIndepSet C ∧ (∀ v, v ∈ H ↔ ∃ c ∈ C, G.Adj c v) ∧
      ∀ S ⊆ H, S.card ≤ ((S.biUnion fun v => G.neighborFinset v) ∩ C).card := by
  refine ⟨fun h => ⟨h.isIndepSet, h.mem_head_iff, fun S hS => ?_⟩, fun ⟨hC, hH, hS⟩ =>
    ⟨hC, hH, ?_⟩⟩
  · obtain ⟨m, hm⟩ := h.exists_isMatchingInto
    rw [← Finset.card_image_of_injOn (hm.injOn.mono hS)]
    refine Finset.card_le_card fun v hv => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_inter.2 ⟨Finset.mem_biUnion.2 ⟨a, ha, (G.mem_neighborFinset _ _).2
      (hm.adj a (hS ha))⟩, hm.mapsTo a (hS ha)⟩
  · rcases G.exists_isMatchingInto_or_exists_card_lt H C with h | ⟨S, hSH, hlt⟩
    · exact h
    · exact absurd (hS S hSH) (not_le.2 hlt)

instance {C H : Finset V} : Decidable (G.IsCrown C H) :=
  decidable_of_iff' _ isCrown_iff_forall_card_le

end Hall

/-- Crowns compose. -/
theorem IsCrown.union_map [DecidableEq V] {C H : Finset V} (h : G.IsCrown C H)
    {C' H' : Finset ↥((↑C ∪ ↑H : Set V)ᶜ)}
    (h' : (G.induce (↑C ∪ ↑H : Set V)ᶜ).IsCrown C' H') :
    G.IsCrown (C ∪ C'.map (Function.Embedding.subtype _))
      (H ∪ H'.map (Function.Embedding.subtype _)) := by
  set R : Set V := (↑C ∪ ↑H : Set V)ᶜ
  have hR : ∀ {X : Finset R} {v : V}, v ∈ X.map (Function.Embedding.subtype _) →
      ∃ hv : v ∈ R, (⟨v, hv⟩ : R) ∈ X := fun hv => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hv
    exact ⟨x.2, hx⟩
  have hnotR : ∀ {v : V}, v ∈ R → v ∉ C ∧ v ∉ H := fun hv => by
    simpa [R, not_or] using hv
  -- every neighbour of `C` lies in `H`
  have hCnbr : ∀ {c v : V}, c ∈ C → G.Adj c v → v ∈ H := fun hc hcv =>
    (h.mem_head_iff _).2 ⟨_, hc, hcv⟩
  obtain ⟨m, hm⟩ := h.exists_isMatchingInto
  obtain ⟨m', hm'⟩ := h'.exists_isMatchingInto
  obtain ⟨m'', hm''⟩ := hm'.map_subtype
  refine ⟨?_, fun v => ?_, ?_⟩
  · intro u hu v hv huv hadj
    rcases Finset.mem_union.1 hu with hu | hu <;> rcases Finset.mem_union.1 hv with hv | hv
    · exact h.isIndepSet hu hv huv hadj
    · obtain ⟨hvR, -⟩ := hR hv
      exact (hnotR hvR).2 (hCnbr hu hadj)
    · obtain ⟨huR, -⟩ := hR hu
      exact (hnotR huR).2 (hCnbr hv hadj.symm)
    · obtain ⟨huR, hu⟩ := hR hu
      obtain ⟨hvR, hv⟩ := hR hv
      exact h'.isIndepSet hu hv (fun e => huv (congrArg Subtype.val e)) hadj
  · constructor
    · intro hv
      rcases Finset.mem_union.1 hv with hv | hv
      · obtain ⟨c, hc, hcv⟩ := (h.mem_head_iff v).1 hv
        exact ⟨c, Finset.mem_union_left _ hc, hcv⟩
      · obtain ⟨hvR, hv⟩ := hR hv
        obtain ⟨c, hc, hcv⟩ := (h'.mem_head_iff _).1 hv
        exact ⟨c, Finset.mem_union_right _ (Finset.mem_map_of_mem _ hc), hcv⟩
    · rintro ⟨c, hc, hcv⟩
      rcases Finset.mem_union.1 hc with hc | hc
      · exact Finset.mem_union_left _ (hCnbr hc hcv)
      · obtain ⟨hcR, hc⟩ := hR hc
        by_cases hvH : v ∈ H
        · exact Finset.mem_union_left _ hvH
        by_cases hvC : v ∈ C
        · exact absurd (hCnbr hvC hcv.symm) (hnotR hcR).2
        have hvR : v ∈ R := by simp [R, hvC, hvH]
        exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨v, hvR⟩,
          (h'.mem_head_iff _).2 ⟨_, hc, hcv⟩, rfl⟩)
  · refine hm.union hm'' (Finset.disjoint_left.2 fun v hv hv' => ?_)
    obtain ⟨hvR, -⟩ := hR hv'
    exact (hnotR hvR).1 hv

section Kernel

variable [Fintype V]

omit [Fintype V] in
/-- A crown with the largest `C ∪ H` leaves a residual graph `G - (C ∪ H)` whose crowns are all
empty. -/
theorem exists_isCrown_forall_isCrown_eq_empty [Finite V] :
    ∃ C H, G.IsCrown C H ∧ ∀ C' H', (G.induce (↑C ∪ ↑H : Set V)ᶜ).IsCrown C' H' →
      C' = ∅ := by
  classical
  cases nonempty_fintype V
  obtain ⟨⟨C, H⟩, hCH, hmax⟩ :=
    (Finset.univ.filter fun p : Finset V × Finset V => G.IsCrown p.1 p.2).exists_max_image
      (fun p => (p.1 ∪ p.2).card) ⟨(∅, ∅), Finset.mem_filter.2 ⟨Finset.mem_univ _, isCrown_empty⟩⟩
  have hCH : G.IsCrown C H := (Finset.mem_filter.1 hCH).2
  refine ⟨C, H, hCH, fun C' H' h' => ?_⟩
  by_contra hne
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have h'' := hCH.union_map h'
  have hle := hmax (C ∪ C'.map (Function.Embedding.subtype _),
    H ∪ H'.map (Function.Embedding.subtype _)) (Finset.mem_filter.2 ⟨Finset.mem_univ _, h''⟩)
  have hc' : (c : V) ∉ C ∪ H := by
    have := c.2
    simpa [not_or] using this
  have hsub : C ∪ H ⊂ C ∪ C'.map (Function.Embedding.subtype _) ∪
      (H ∪ H'.map (Function.Embedding.subtype _)) := by
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨c, ?_, hc'⟩
    · exact Finset.union_subset_union Finset.subset_union_left Finset.subset_union_left
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_map_of_mem _ hc))
  exact absurd hle (not_le.2 (Finset.card_lt_card hsub))

/-- A graph whose crowns are all empty has at most `2 |S|` vertices for every vertex cover `S`:
otherwise the independent set `Sᶜ` has fewer neighbours than vertices. -/
theorem card_le_two_mul_card_of_forall_isCrown_eq_empty (hfree : ∀ C H, G.IsCrown C H → C = ∅)
    {S : Finset V} (hS : G.IsVertexCover S) : Fintype.card V ≤ 2 * S.card := by
  classical
  have hind : G.IsIndepSet (Sᶜ : Finset V) := by
    rw [Finset.coe_compl]
    exact isIndepSet_compl_iff_isVertexCover.2 hS
  have hN : (Sᶜ.biUnion fun v => G.neighborFinset v) ⊆ S := by
    intro v hv
    simp only [Finset.mem_biUnion, mem_neighborFinset, Finset.mem_compl] at hv
    obtain ⟨u, hu, huv⟩ := hv
    exact (hS huv).resolve_left hu
  have hcompl := Finset.card_compl_add_card S
  by_contra hlt
  obtain ⟨C, H, -, hC, hCH⟩ := G.exists_isCrown_of_card_lt hind
    ((Finset.card_le_card hN).trans_lt (by omega))
  exact hC.ne_empty (hfree C H hCH)

private theorem card_compl_union_eq [DecidableEq V] (C H : Finset V)
    [Fintype ↥((↑C ∪ ↑H : Set V)ᶜ)] :
    Fintype.card ↥((↑C ∪ ↑H : Set V)ᶜ) = (C ∪ H)ᶜ.card := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ← Finset.coe_union, ← Finset.coe_compl,
    Set.ncard_coe_finset]

/-- **Crown lemma**, existence form of a variant of [CyganEtAl2015, Section 2.3]: a graph with
more than `3k` vertices has a matching of more than `k` edges or a crown with `C` nonempty.
Isolated vertices are allowed, and `H` may be empty. -/
theorem exists_isMatchingInto_or_exists_isCrown {k : ℕ} (hk : 3 * k < Fintype.card V) :
    (∃ A B m, Disjoint A B ∧ G.IsMatchingInto A B m ∧ k < A.card) ∨
      ∃ C H, C.Nonempty ∧ G.IsCrown C H := by
  classical
  obtain ⟨A, hA, hmax⟩ := (Finset.univ.filter fun A : Finset V =>
      ∃ B m, Disjoint A B ∧ G.IsMatchingInto A B m).exists_max_image Finset.card
    ⟨∅, Finset.mem_filter.2 ⟨Finset.mem_univ _, ∅, id, by simp, by simp, by simp, by simp⟩⟩
  obtain ⟨B, m, hAB, hm⟩ := (Finset.mem_filter.1 hA).2
  have hmax : ∀ A' B' m', Disjoint A' B' → G.IsMatchingInto A' B' m' → A'.card ≤ A.card :=
    fun A' B' m' hd hm' => hmax A' (Finset.mem_filter.2 ⟨Finset.mem_univ _, B', m', hd, hm'⟩)
  by_cases hkA : k < A.card
  · exact Or.inl ⟨A, B, m, hAB, hm, hkA⟩
  push Not at hkA
  set I : Finset V := (A ∪ A.image m)ᶜ with hIdef
  have hmemI : ∀ {v}, v ∈ I ↔ v ∉ A ∧ v ∉ A.image m := fun {v} => by
    simp only [hIdef, Finset.mem_compl, Finset.mem_union, not_or]
  have hIcard : k < I.card := by
    have h₁ := Finset.card_compl_add_card (A ∪ A.image m)
    have h₂ := Finset.card_union_le A (A.image m)
    have h₃ := Finset.card_image_le (s := A) (f := m)
    rw [← hIdef] at h₁
    omega
  have hIind : G.IsIndepSet I := by
    intro u hu v hv huv hadj
    have hu := hmemI.1 hu
    have hv := hmemI.1 hv
    have hupd : ∀ a ∈ A, Function.update m u v a = m a := fun a ha =>
      Function.update_of_ne (by rintro rfl; exact hu.1 ha) _ _
    have := hmax (insert u A) (insert v (A.image m)) (Function.update m u v) ?_ ?_
    · rw [Finset.card_insert_of_notMem hu.1] at this
      omega
    · refine Finset.disjoint_left.2 fun x hx hx' => ?_
      rcases Finset.mem_insert.1 hx with hxu | hx <;>
        rcases Finset.mem_insert.1 hx' with hxv | hx'
      · exact huv (hxu.symm.trans hxv)
      · exact hu.2 (hxu ▸ hx')
      · exact hv.1 (hxv ▸ hx)
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx'
        exact Finset.disjoint_left.1 hAB hx (hm.mapsTo a ha)
    · refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha b hb hab => ?_⟩
      · rcases Finset.mem_insert.1 ha with rfl | ha
        · rw [Function.update_self]
          exact Finset.mem_insert_self _ _
        · rw [hupd a ha]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha)
      · rcases Finset.mem_insert.1 ha with rfl | ha
        · rw [Function.update_self]
          exact hadj
        · rw [hupd a ha]
          exact hm.adj a ha
      · have ha' : a ∈ insert u A := ha
        have hb' : b ∈ insert u A := hb
        clear ha hb
        rcases Finset.mem_insert.1 ha' with hau | ha <;>
          rcases Finset.mem_insert.1 hb' with hbu | hb
        · exact hau.trans hbu.symm
        · rw [hau, Function.update_self, hupd b hb] at hab
          exact (hv.2 (by rw [hab]; exact Finset.mem_image_of_mem m hb)).elim
        · rw [hbu, Function.update_self, hupd a ha] at hab
          exact (hv.2 (by rw [← hab]; exact Finset.mem_image_of_mem m ha)).elim
        · rw [hupd a ha, hupd b hb] at hab
          exact hm.injOn ha hb hab
  rcases G.exists_isMatchingInto_or_exists_card_lt I (I.biUnion fun v => G.neighborFinset v) with
    ⟨m', hm'⟩ | ⟨S, hSI, hS⟩
  · refine Or.inl ⟨I, _, m', Finset.disjoint_left.2 fun v hvI hvN => ?_, hm', hIcard⟩
    simp only [Finset.mem_biUnion, mem_neighborFinset] at hvN
    obtain ⟨u, huI, huv⟩ := hvN
    exact hIind huI hvI huv.ne huv
  · refine Or.inr ?_
    have hsub : (S.biUnion fun v => G.neighborFinset v) ⊆ I.biUnion fun v => G.neighborFinset v :=
      Finset.biUnion_subset_biUnion_of_subset_left _ hSI
    rw [Finset.inter_eq_left.2 hsub] at hS
    obtain ⟨C, H, -, hC, hCH⟩ := G.exists_isCrown_of_card_lt (hIind.mono hSI) hS
    exact ⟨C, H, hC, hCH⟩

/-- **Crown lemma** [CyganEtAl2015, Section 2.3], existence form: a graph without isolated
vertices and with more than `3k` vertices has a matching of more than `k` edges or a crown with `C`
and `H` nonempty. The cited lemma also finds one of them in polynomial time; this one does not. -/
theorem exists_isMatchingInto_or_exists_isCrown_of_forall_exists_adj
    (hadj : ∀ v, ∃ w, G.Adj v w) {k : ℕ} (hk : 3 * k < Fintype.card V) :
    (∃ A B m, Disjoint A B ∧ G.IsMatchingInto A B m ∧ k < A.card) ∨
      ∃ C H, C.Nonempty ∧ H.Nonempty ∧ G.IsCrown C H := by
  rcases G.exists_isMatchingInto_or_exists_isCrown hk with h | ⟨C, H, hC, hCH⟩
  · exact Or.inl h
  · exact Or.inr ⟨C, H, hC, hCH.head_nonempty hC fun c _ => hadj c, hCH⟩

/-- **The `3k` kernel for vertex cover** [CyganEtAl2015, Section 2.3], existence form: `G` has a
matching of more than `k` edges, so no vertex cover of at most `k` vertices, or a crown `(C, H)`
with `|H| ≤ k` whose residual graph `G - (C ∪ H)` has at most `3 (k - |H|)` vertices. By
`SimpleGraph.IsCrown.vertexCoverNum_le_iff`, `(G - (C ∪ H), k - |H|)` is then an equivalent
instance. The crown is not constructed in polynomial time. -/
theorem exists_isMatchingInto_or_exists_isCrown_card_compl_le [DecidableEq V] (k : ℕ) :
    (∃ A B m, Disjoint A B ∧ G.IsMatchingInto A B m ∧ k < A.card) ∨
      ∃ C H, G.IsCrown C H ∧ H.card ≤ k ∧ (C ∪ H)ᶜ.card ≤ 3 * (k - H.card) := by
  classical
  obtain ⟨C, H, hCH, hfree⟩ := G.exists_isCrown_forall_isCrown_eq_empty
  obtain ⟨m, hm⟩ := hCH.exists_isMatchingInto
  by_cases hkH : k < H.card
  · exact Or.inl ⟨H, C, m, hCH.disjoint, hm, hkH⟩
  push Not at hkH
  by_cases hR : (C ∪ H)ᶜ.card ≤ 3 * (k - H.card)
  · exact Or.inr ⟨C, H, hCH, hkH, hR⟩
  push Not at hR
  have hRmem : ∀ {X : Finset ↥((↑C ∪ ↑H : Set V)ᶜ)} {v : V},
      v ∈ X.map (Function.Embedding.subtype _) → v ∉ C ∧ v ∉ H := fun hv => by
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hv
    have := x.2
    simpa [not_or] using this
  rcases (G.induce (↑C ∪ ↑H : Set V)ᶜ).exists_isMatchingInto_or_exists_isCrown
      (k := k - H.card) (by rw [card_compl_union_eq]; exact hR) with
    ⟨A', B', m', hAB', hm', hk'⟩ | ⟨C', H', hC', hCH'⟩
  · obtain ⟨m'', hm''⟩ := hm'.map_subtype
    obtain ⟨M, hM⟩ := hm.union hm'' (Finset.disjoint_left.2 fun v hvC hv => (hRmem hv).1 hvC)
    have hHA : Disjoint H (A'.map (Function.Embedding.subtype _)) :=
      Finset.disjoint_left.2 fun v hvH hv => (hRmem hv).2 hvH
    refine Or.inl ⟨_, _, M, ?_, hM, ?_⟩
    · rw [Finset.disjoint_union_left, Finset.disjoint_union_right, Finset.disjoint_union_right]
      exact ⟨⟨hCH.disjoint, Finset.disjoint_left.2 fun v hvH hv => (hRmem hv).2 hvH⟩,
        Finset.disjoint_left.2 fun v hv hvC => (hRmem hv).1 hvC, (Finset.disjoint_map _).2 hAB'⟩
    · rw [Finset.card_union_of_disjoint hHA, Finset.card_map]
      omega
  · exact absurd (hfree C' H' hCH') hC'.ne_empty

/-- **The `2k` bound**: some crown `(C, H)` leaves a residual graph `G - (C ∪ H)` of at most
`2 (k - |H|)` vertices for every `k` with `τ(G) ≤ k`, the size of the Nemhauser–Trotter
kernel. -/
theorem exists_isCrown_forall_card_compl_le [DecidableEq V] :
    ∃ C H, G.IsCrown C H ∧ ∀ k : ℕ, G.vertexCoverNum ≤ k →
      H.card ≤ k ∧ (C ∪ H)ᶜ.card ≤ 2 * (k - H.card) := by
  classical
  obtain ⟨C, H, hCH, hfree⟩ := G.exists_isCrown_forall_isCrown_eq_empty
  refine ⟨C, H, hCH, fun k hk => ?_⟩
  obtain ⟨hHk, hk'⟩ := hCH.vertexCoverNum_le_iff.1 hk
  refine ⟨hHk, ?_⟩
  obtain ⟨S, hS, hScov⟩ := (G.induce (↑C ∪ ↑H : Set V)ᶜ).vertexCoverNum_exists
  have h₂ := (G.induce (↑C ∪ ↑H : Set V)ᶜ).card_le_two_mul_card_of_forall_isCrown_eq_empty hfree
    (S := S.toFinset) (by rwa [Set.coe_toFinset])
  rw [card_compl_union_eq] at h₂
  have hSk : S.toFinset.card ≤ k - H.card := by
    have : (S.toFinset.card : ℕ∞) ≤ (k - H.card : ℕ) := by
      rw [← Set.encard_coe_eq_coe_finsetCard, Set.coe_toFinset, hS]
      exact hk'
    exact_mod_cast this
  omega

end Kernel

end SimpleGraph
