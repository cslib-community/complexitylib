/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Tutte.lean`)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Berge
public import Mathlib.Combinatorics.SimpleGraph.Tutte

/-!
# The Tutte–Berge formula

For a finite simple graph `G = (V, E)` and a vertex set `U`, write `o(G - U)` for the number of
connected components of `G - U` with an odd number of vertices. The **Tutte–Berge formula**
([Berge1958]; [Schrijver2017], Theorem 5.1) states that the maximum size `ν(G)` of a matching is

  `ν(G) = min_U (|V| + |U| - o(G - U)) / 2`.

Here it is stated with vertex counts: a matching `M` covers `2|M|` vertices, so the formula reads
`max_M |V(M)| = min_U (|V| + |U| - o(G - U))`.

* *Weak duality* (`≤`). Every odd component of `G - U` contains a vertex that `M` leaves uncovered
  or matches into `U`. These vertices are distinct, so `o(G - U) ≤ |V \ V(M)| + |U|`.
* *Strong duality* (`≥`). Take `U₀` maximizing the deficiency `o(G - U) - |U|`, with maximum `d`.
  Adjoin `d` new vertices adjacent to every other vertex. A parity argument shows that the
  resulting graph satisfies Tutte's condition, so it has a perfect matching by Mathlib's
  `SimpleGraph.tutte`. Deleting the new vertices leaves a matching of `G` missing at most `d`
  vertices. This is Berge's derivation of the formula from Tutte's theorem ([Berge1958]).
  Schrijver gives a direct inductive proof instead, then derives Tutte's theorem as
  Corollary 5.1a.

## Main results

* `SimpleGraph.Subgraph.IsMatching.ncard_verts_add_ncard_oddComponents_le`: weak duality,
  `|V(M)| + o(G - U) ≤ |V| + |U|` for every matching `M` and vertex set `U`.
* `SimpleGraph.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq`: strong duality, some
  matching and some vertex set attain equality.
* `IsMatching.isMaximumMatching_iff_exists_ncard_verts_add_ncard_oddComponents_eq` (in namespace
  `SimpleGraph.Subgraph`): a matching is maximum iff some `U` attains equality, so `U` certifies
  maximality.
* `SimpleGraph.Subgraph.IsMaximumMatching.isLeast_two_mul_ncard_edgeSet`: **the Tutte–Berge
  formula**. Twice the size of a maximum matching is the least value of `|V| + |U| - o(G - U)`.
* `SimpleGraph.Iso.ncard_oddComponents_eq`: isomorphic graphs have equally many odd components.

## References

* [C. Berge, *Sur le couplage maximum d'un graphe*][Berge1958]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017]
-/

public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Isomorphic graphs have equally many odd components. -/
theorem Iso.ncard_oddComponents_eq {W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (φ : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  refine Set.ncard_congr (fun c _ => φ.connectedComponentEquiv c) (fun c hc => ?_)
    (fun c _ d _ h => φ.connectedComponentEquiv.injective h) (fun d hd => ?_)
  · change Odd _ at hc ⊢
    rwa [← Nat.card_coe_set_eq, ← Nat.card_congr (ConnectedComponent.isoEquivSupp φ c),
      Nat.card_coe_set_eq]
  · refine ⟨φ.connectedComponentEquiv.symm d, ?_, by simp⟩
    change Odd _ at hd ⊢
    rwa [← Nat.card_coe_set_eq, Nat.card_congr (ConnectedComponent.isoEquivSupp φ _),
      Equiv.apply_symm_apply, Nat.card_coe_set_eq]

/-- Deleting `U` from a finite graph leaves `|V| - |U|` vertices. -/
theorem card_verts_deleteVerts_top [Finite V] (U : Set V) :
    Nat.card ((⊤ : G.Subgraph).deleteVerts U).verts = Nat.card V - U.ncard := by
  rw [Nat.card_coe_set_eq, Subgraph.deleteVerts_verts, Subgraph.verts_top,
    ← Set.compl_eq_univ_sdiff]
  have := Set.ncard_add_ncard_compl U
  omega

namespace Subgraph

variable {M : G.Subgraph}

/-! ### Weak duality -/

/-- Every odd component of `G - U` contains a vertex that `M` leaves uncovered or matches into
`U`. This generalizes Mathlib's `ConnectedComponent.odd_matches_node_outside` from perfect
matchings to arbitrary matchings. -/
theorem IsMatching.exists_of_mem_oddComponents [Finite V] (hM : M.IsMatching) {U : Set V}
    (c : ((⊤ : G.Subgraph).deleteVerts U).coe.ConnectedComponent)
    (hc : c ∈ ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents) :
    ∃ x : V, x ∈ M.vertsᶜ ∪ U ∧ ∃ v ∈ c.supp, (v : V) = x ∨ M.Adj v x := by
  by_contra! h
  have hmatch : (M.induce (Subtype.val '' c.supp)).IsMatching := by
    rintro _ ⟨⟨v, hv'⟩, hv, rfl⟩
    have hvM : v ∈ M.verts := by
      by_contra hvM
      exact (h v (Or.inl hvM) ⟨v, hv'⟩ hv).1 rfl
    obtain ⟨w, hw, hwu⟩ := hM hvM
    have hwU : w ∉ U := fun hwU => (h w (Or.inr hwU) ⟨v, hv'⟩ hv).2 hw
    have hw' : w ∈ ((⊤ : G.Subgraph).deleteVerts U).verts := ⟨trivial, hwU⟩
    have hwc : (⟨w, hw'⟩ : ((⊤ : G.Subgraph).deleteVerts U).verts) ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff, ← (ConnectedComponent.mem_supp_iff _ _).mp hv]
      refine (ConnectedComponent.connectedComponentMk_eq_of_adj ?_).symm
      exact Subgraph.Adj.coe (deleteVerts_adj.mpr ⟨trivial, hv'.2, trivial, hwU, M.adj_sub hw⟩)
    refine ⟨w, ⟨⟨⟨v, hv'⟩, hv, rfl⟩, ⟨⟨w, hw'⟩, hwc, rfl⟩, hw⟩, fun y hy => hwu y hy.2.2⟩
  have hodd : Odd c.supp.ncard := hc
  have hcard := hmatch.ncard_verts_eq_two_mul
  rw [induce_verts, Set.ncard_image_of_injective _ Subtype.val_injective] at hcard
  rw [hcard] at hodd
  exact Nat.not_even_iff_odd.mpr hodd (even_two_mul _)

/-- **Tutte–Berge, weak duality** ([Schrijver2017], Theorem 5.1, easy direction): a matching `M`
and a vertex set `U` of a finite graph satisfy `|V(M)| + o(G - U) ≤ |V| + |U|`. -/
theorem IsMatching.ncard_verts_add_ncard_oddComponents_le [Finite V] (hM : M.IsMatching)
    (U : Set V) :
    M.verts.ncard + ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard ≤
      Nat.card V + U.ncard := by
  choose g hgmem v hvc hv using fun c : ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents =>
    hM.exists_of_mem_oddComponents c.1 c.2
  have hnot : ∀ c, (v c : V) = g c → g c ∉ M.verts := fun c hc' => by
    refine (hgmem c).elim id fun h => ?_
    rw [← hc'] at h
    exact absurd h (v c).2.2
  have hinj : Function.Injective fun c => (⟨g c, hgmem c⟩ : (M.vertsᶜ ∪ U : Set V)) := by
    intro c d hcd
    have hcd : g c = g d := congrArg Subtype.val hcd
    have key : v c = v d := by
      rcases hv c with hc' | hc' <;> rcases hv d with hd' | hd'
      · exact Subtype.val_injective (hc'.trans (hcd.trans hd'.symm))
      · exact (hnot c hc' (by rw [hcd]; exact M.edge_vert hd'.symm)).elim
      · exact (hnot d hd' (by rw [← hcd]; exact M.edge_vert hc'.symm)).elim
      · exact Subtype.val_injective (hM.eq_of_adj_right hc' (hcd ▸ hd'))
    exact Subtype.val_injective (ConnectedComponent.eq_of_common_vertex (hvc c) (key ▸ hvc d))
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hle
  have hunion := Set.ncard_union_le M.vertsᶜ U
  have hcompl := Set.ncard_add_ncard_compl M.verts
  omega


end Subgraph

/-! ### Strong duality via universal vertices -/

/-- `G` with `d` new vertices, each adjacent to every other vertex. -/
private def addUniversalVerts (G : SimpleGraph V) (d : ℕ) : SimpleGraph (V ⊕ Fin d) where
  Adj
    | .inl v, .inl w => G.Adj v w
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
    | .inr i, .inr j => i ≠ j
  symm := ⟨fun x y h => by
    rcases x with x | x <;> rcases y with y | y
    · exact G.symm.symm _ _ h
    · trivial
    · trivial
    · exact Ne.symm h⟩
  loopless := ⟨fun x h => by
    rcases x with x | x
    · exact G.loopless.irrefl x h
    · exact h rfl⟩

/-- Deleting a vertex set containing all the new vertices from `G.addUniversalVerts d` gives a copy
of `G` minus the corresponding vertex set. -/
private def deleteVertsAddUniversalVertsIso {d : ℕ} (U' : Set (V ⊕ Fin d))
    (hU' : Set.range Sum.inr ⊆ U') :
    ((⊤ : G.Subgraph).deleteVerts (Sum.inl ⁻¹' U')).coe ≃g
      ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe where
  toFun v := ⟨.inl v.1, trivial, v.2.2⟩
  invFun x := match x with
    | ⟨.inl v, hv⟩ => ⟨v, trivial, hv.2⟩
    | ⟨.inr i, hi⟩ => absurd (hU' ⟨i, rfl⟩) hi.2
  left_inv v := rfl
  right_inv x := by
    rcases x with ⟨x | i, hx⟩
    · rfl
    · exact absurd (hU' ⟨i, rfl⟩) hx.2
  map_rel_iff' {v w} := by
    change (_ ∧ _ ∧ G.Adj _ _) ↔ (_ ∧ _ ∧ G.Adj _ _)
    exact ⟨fun h => ⟨v.2, w.2, h.2.2⟩, fun h => ⟨⟨trivial, v.2.2⟩, ⟨trivial, w.2.2⟩, h.2.2⟩⟩

/-- **Tutte–Berge, strong duality** ([Berge1958]; [Schrijver2017], Theorem 5.1): a finite graph
has a matching `M` and a vertex set `U` with `|V(M)| + o(G - U) = |V| + |U|`. -/
theorem exists_isMatching_ncard_verts_add_ncard_oddComponents_eq [Finite V] (G : SimpleGraph V) :
    ∃ (M : G.Subgraph) (U : Set V), M.IsMatching ∧
      M.verts.ncard + ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard =
        Nat.card V + U.ncard := by
  classical
  have := Fintype.ofFinite V
  -- a vertex set `U₀` maximizing the deficiency `o(G - U) - |U|`
  obtain ⟨U₀, -, hU₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Set V))
    (fun U => ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard + (Nat.card V - U.ncard))
    ⟨∅, Finset.mem_univ _⟩
  have hU₀V := Set.ncard_le_card U₀
  have hmax : ∀ U : Set V, ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard + U₀.ncard ≤
      ((⊤ : G.Subgraph).deleteVerts U₀).coe.oddComponents.ncard + U.ncard := fun U => by
    have := hU₀ U (Finset.mem_univ _)
    have := Set.ncard_le_card U
    omega
  have hle : U₀.ncard ≤ ((⊤ : G.Subgraph).deleteVerts U₀).coe.oddComponents.ncard := by
    have := hmax ∅
    rw [Set.ncard_empty] at this
    omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  -- parity: `|V| + d` is even
  have hpar : Even (Nat.card V + d) := by
    have h := odd_ncard_oddComponents ((⊤ : G.Subgraph).deleteVerts U₀).coe
    rw [hd, card_verts_deleteVerts_top] at h
    rw [← Nat.not_odd_iff_even, Nat.odd_iff]
    rw [Nat.odd_iff, Nat.odd_iff] at h
    omega
  -- `G.addUniversalVerts d` has no Tutte violator
  have htutte : ∀ U' : Set (V ⊕ Fin d), ¬(G.addUniversalVerts d).IsTutteViolator U' := by
    intro U' hU'
    unfold IsTutteViolator at hU'
    by_cases hsub : Set.range Sum.inr ⊆ U'
    · rw [← Iso.ncard_oddComponents_eq (deleteVertsAddUniversalVertsIso U' hsub)] at hU'
      have hU'eq : U' = Sum.inl '' (Sum.inl ⁻¹' U') ∪ Set.range Sum.inr := by
        ext x
        rcases x with x | i
        · simp
        · simpa using hsub ⟨i, rfl⟩
      have hcard : U'.ncard = (Sum.inl ⁻¹' U' : Set V).ncard + d := by
        rw [hU'eq, Set.ncard_union_eq, Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
          Fintype.card_fin, Set.preimage_union, Set.preimage_image_eq _ Sum.inl_injective]
        · simp
        · rw [Set.disjoint_left]
          rintro _ ⟨v, -, rfl⟩ ⟨i, hi⟩
          exact Sum.inr_ne_inl hi
      have := hmax (Sum.inl ⁻¹' U')
      omega
    · obtain ⟨_, ⟨i, rfl⟩, hi⟩ := Set.not_subset.mp hsub
      have hi' : Sum.inr i ∈ ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').verts :=
        ⟨trivial, hi⟩
      have hadj : ∀ x : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').verts,
          x ≠ ⟨_, hi'⟩ →
            ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe.Adj x ⟨_, hi'⟩ :=
        fun x hx => by
          refine Subgraph.Adj.coe (Subgraph.deleteVerts_adj.mpr
            ⟨trivial, x.2.2, trivial, hi, ?_⟩)
          rcases x with ⟨x | j, hx'⟩
          · trivial
          · exact fun h => hx (by subst h; rfl)
      have hpre : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe.Preconnected :=
        fun x y => by
          have hx : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe.Reachable x
              ⟨_, hi'⟩ := by
            by_cases h : x = ⟨_, hi'⟩
            · rw [h]
            · exact (hadj x h).reachable
          have hy : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe.Reachable y
              ⟨_, hi'⟩ := by
            by_cases h : y = ⟨_, hi'⟩
            · rw [h]
            · exact (hadj y h).reachable
          exact hx.trans hy.symm
      have hsing := hpre.subsingleton_connectedComponent
      have hle1 : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts U').coe.oddComponents.ncard
          ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr Set.subsingleton_of_subsingleton
      rcases U'.eq_empty_or_nonempty with rfl | hne
      · have h := odd_ncard_oddComponents
          ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts (∅ : Set (V ⊕ Fin d))).coe
        rw [Set.ncard_empty] at hU'
        have h1 : ((⊤ : (G.addUniversalVerts d).Subgraph).deleteVerts
            (∅ : Set (V ⊕ Fin d))).coe.oddComponents.ncard = 1 := by omega
        rw [h1, card_verts_deleteVerts_top, Set.ncard_empty, Nat.card_sum,
          Nat.card_eq_fintype_card (α := Fin d),
          Fintype.card_fin] at h
        rw [← Nat.not_odd_iff_even] at hpar
        exact hpar (h.mp odd_one)
      · have := (Set.ncard_pos (Set.toFinite _)).mpr hne
        omega
  obtain ⟨M', hM'⟩ := (tutte (G := G.addUniversalVerts d)).mpr htutte
  -- restrict the perfect matching to `G`
  let M : G.Subgraph :=
    { verts := {v | ∃ w, M'.Adj (.inl v) (.inl w)}
      Adj := fun v w => M'.Adj (.inl v) (.inl w)
      adj_sub := fun h => M'.adj_sub h
      edge_vert := fun h => ⟨_, h⟩
      symm := ⟨fun _ _ h => M'.symm.symm _ _ h⟩ }
  have hM : M.IsMatching := by
    rintro v ⟨w, hw⟩
    exact ⟨w, hw, fun y hy => Sum.inl_injective (hM'.1.eq_of_adj_left hy hw)⟩
  -- at most `d` vertices of `G` are uncovered: their partners are distinct new vertices
  choose p hp using fun x => (hM'.1 (hM'.2 x)).exists
  have hunc : M.vertsᶜ.ncard ≤ d := by
    have h := Set.ncard_le_ncard_of_injOn (s := M.vertsᶜ) (t := Set.range (Sum.inr : Fin d → _))
      (fun v => p (.inl v)) (fun v hv => ?_) (fun v _ w _ h => Sum.inl_injective
        (hM'.1.eq_of_adj_right (hp _) (by rw [show p (.inl v) = p (.inl w) from h]; exact hp _)))
      (Set.toFinite _)
    · rwa [Set.ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
        Fintype.card_fin] at h
    · rcases hpv : p (.inl v) with w | i
      · exact absurd ⟨w, hpv ▸ hp (.inl v)⟩ hv
      · exact ⟨i, rfl⟩
  refine ⟨M, U₀, hM, le_antisymm (hM.ncard_verts_add_ncard_oddComponents_le U₀) ?_⟩
  have := Set.ncard_add_ncard_compl M.verts
  omega

namespace Subgraph

variable {M : G.Subgraph}

/-- A maximum matching attains the Tutte–Berge bound: some vertex set `U` has
`|V(M)| + o(G - U) = |V| + |U|`. -/
theorem IsMaximumMatching.exists_ncard_verts_add_ncard_oddComponents_eq [Finite V]
    (hM : M.IsMaximumMatching) :
    ∃ U : Set V, M.verts.ncard + ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard =
      Nat.card V + U.ncard := by
  obtain ⟨M₀, U, hM₀, heq⟩ := G.exists_isMatching_ncard_verts_add_ncard_oddComponents_eq
  have h₀ := (hM.1.isMaximumMatching_iff_ncard_verts.mp hM) M₀ hM₀
  exact ⟨U, le_antisymm (hM.1.ncard_verts_add_ncard_oddComponents_le U) (by omega)⟩

/-- A matching of a finite graph is maximum iff some vertex set `U` attains the Tutte–Berge bound
`|V(M)| + o(G - U) = |V| + |U|`. Such a `U` certifies that `M` is maximum. -/
theorem IsMatching.isMaximumMatching_iff_exists_ncard_verts_add_ncard_oddComponents_eq
    [Finite V] (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ∃ U : Set V,
      M.verts.ncard + ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard =
        Nat.card V + U.ncard := by
  refine ⟨IsMaximumMatching.exists_ncard_verts_add_ncard_oddComponents_eq, fun ⟨U, hU⟩ => ?_⟩
  refine hM.isMaximumMatching_iff_ncard_verts.mpr fun M' hM' => ?_
  have := hM'.ncard_verts_add_ncard_oddComponents_le U
  omega

/-- **The Tutte–Berge formula** ([Berge1958]; [Schrijver2017], Theorem 5.1): twice the size of a
maximum matching `M` of a finite graph is the least value of `|V| + |U| - o(G - U)` over vertex
sets `U`. The subtraction is truncated, but by weak duality it never truncates. -/
theorem IsMaximumMatching.isLeast_two_mul_ncard_edgeSet [Finite V] (hM : M.IsMaximumMatching) :
    IsLeast (Set.range fun U : Set V =>
      Nat.card V + U.ncard - ((⊤ : G.Subgraph).deleteVerts U).coe.oddComponents.ncard)
      (2 * M.edgeSet.ncard) := by
  rw [← hM.1.ncard_verts_eq_two_mul]
  obtain ⟨U, hU⟩ := hM.exists_ncard_verts_add_ncard_oddComponents_eq
  refine ⟨⟨U, by dsimp only; omega⟩, ?_⟩
  rintro _ ⟨U', rfl⟩
  have := hM.1.ncard_verts_add_ncard_oddComponents_le U'
  dsimp only
  omega

end Subgraph

end SimpleGraph
