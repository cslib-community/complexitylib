/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.CorrDigraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FinCases

/-!
# Exponential extension-complexity lower bound for TSP polytopes

This module completes the Fiorini–Massar–Pokutta–Tiwary–de Wolf reduction from the correlation
polytope `corrPolytope K (Fin p)` to the symmetric traveling salesman polytope `tspPolytope K V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11 and Theorem 12], combined with
Kaibel–Weltge's `(3 / 2) ^ p` bound on `corrPolytope` [KaibelWeltge2015, Theorem 1].

For `p ≥ 1`, `SplitV (CorrDigraphV p) v₀ pad` has `3 * |CorrDigraphV p| + pad ≤ 69 * p ^ 2 + pad`
vertices, and intersecting `tspPolytope K W` with the zero-weight non-edge exposed face of
`paddedSplitGraph v₀ pad (corrDigraphAdj p hp)` yields a face whose coordinate projection onto the
distinguished reverse edges `(vOut (chain v 1), vIn (chain v 0))` equals `corrPolytope K (Fin p)`
(`extensionComplexity_corrPolytope_le_tspPolytope_splitV`). Transporting along any bijection
`SplitV (CorrDigraphV p) v₀ pad ≃ V` with `p = ⌊√(|V| / 69)⌋` gives
`3 ^ p ≤ 2 ^ p * extensionComplexity (tspPolytope K V)` and `(3 / 2 : F) ^ ⌊√(|V| / 69)⌋ ≤ r` for
every extended formulation of `tspPolytope K V` with `r` inequalities when `|V| ≥ 69`.

## Main definitions

* `tspHardGraph`: the `m`-vertex undirected 3-split correlation graph on `Fin m` (`m ≥ 69`).

## Main results

* `extensionComplexity_corrPolytope_le_tspPolytope_splitV`:
  `xc (corrPolytope K (Fin p)) ≤ xc (tspPolytope K (SplitV (CorrDigraphV p) v₀ pad))`.
* `extensionComplexity_corrPolytope_le_tspHardGraph_face`:
  `xc (corrPolytope K (Fin ⌊√(m / 69)⌋))` is bounded by the exposed `tspHardGraph m` tour face of
  `tspPolytope K (Fin m)` for `69 ≤ m`.
* `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope`:
  for `69 ≤ |V|` and `p = Nat.sqrt (|V| / 69)`,
  `3 ^ p ≤ 2 ^ p * extensionComplexity (tspPolytope K V)`.
* `ceil_three_div_two_pow_le_extensionComplexity_tspPolytope`:
  `⌈(3 / 2) ^ Nat.sqrt (|V| / 69)⌉ ≤ extensionComplexity (tspPolytope K V)`.
* `HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope`:
  for `69 ≤ |V|`, any extended formulation of `tspPolytope K V` with `r` inequalities satisfies
  `(3 / 2 : F) ^ Nat.sqrt (|V| / 69) ≤ r`.
* `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin`,
  `HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope_fin`: `Fin m` (`69 ≤ m`) forms.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11 and Theorem 12).
* [KaibelWeltge2015], Section 2 (Theorem 1).
-/

public section

section Congruence

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem mapEdgeSet_completeGraph_mem_tourEdgeSet {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂)
    (σ₂ : Fin (Fintype.card V₂) ≃ V₂) (hV₂ : 3 ≤ Fintype.card V₂)
    (x : ↥(⊤ : SimpleGraph V₁).edgeSet) :
    let hcard : Fintype.card V₁ = Fintype.card V₂ := Fintype.card_congr e
    let hV₁ : 3 ≤ Fintype.card V₁ := hcard ▸ hV₂
    let σ₁ : Fin (Fintype.card V₁) ≃ V₁ := (finCongr hcard).trans (σ₂.trans e.symm)
    (SimpleGraph.Iso.completeGraph e).mapEdgeSet x ∈ tourEdgeSet σ₂ hV₂ ↔
      x ∈ tourEdgeSet σ₁ hV₁ := by
  intro hcard hV₁ σ₁
  have hcast_add : ∀ j : Fin (Fintype.card V₁),
      finCongr hcard (j + ⟨1, by omega⟩) = finCongr hcard j + ⟨1, by omega⟩ := fun j =>
    Fin.ext (by
      change (j + ⟨1, by omega⟩).1 = (finCongr hcard j + ⟨1, by omega⟩).1
      simp only [Fin.val_add, hcard]
      rfl)
  obtain ⟨s, hs⟩ := x
  induction s using Sym2.ind with
  | _ u v =>
      change ⟨s(e u, e v), _⟩ ∈ tourEdgeSet σ₂ hV₂ ↔ ⟨s(u, v), hs⟩ ∈ tourEdgeSet σ₁ hV₁
      simp only [tourEdgeSet, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
      constructor
      · rintro ⟨i, hi⟩
        refine ⟨(finCongr hcard).symm i, ?_⟩
        have hstep : finCongr hcard ((finCongr hcard).symm i + ⟨1, by omega⟩) =
            i + ⟨1, by omega⟩ := by
          rw [hcast_add, Equiv.apply_symm_apply]
        have hsym : s(u, v) = Sym2.map e.symm (Sym2.map e s(u, v)) := by
          simp only [Sym2.map_map, Function.comp_def, Equiv.symm_apply_apply, Sym2.map_id', id_eq]
        rw [hsym, Sym2.map_mk, ← hi, Sym2.map_mk]
        simp only [σ₁, Equiv.trans_apply, Equiv.apply_symm_apply, hstep]
      · rintro ⟨j, hj⟩
        refine ⟨finCongr hcard j, ?_⟩
        have hstep := hcast_add j
        have hsym : s(e u, e v) = Sym2.map e s(u, v) := rfl
        rw [hsym, ← hj, Sym2.map_mk]
        simp only [σ₁, Equiv.trans_apply, Equiv.apply_symm_apply, hstep]

omit [IsStrictOrderedRing K] in
private theorem tspPolytope_funLeft_eq {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) :
    LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e).mapEdgeSet '' tspPolytope K V₂ =
      tspPolytope K V₁ := by
  have hcard : Fintype.card V₁ = Fintype.card V₂ := Fintype.card_congr e
  rw [tspPolytope, LinearMap.image_convexHull, tspPolytope]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨F, ⟨hV₂, σ₂, rfl⟩, rfl⟩, rfl⟩
    let hV₁ : 3 ≤ Fintype.card V₁ := hcard ▸ hV₂
    let σ₁ : Fin (Fintype.card V₁) ≃ V₁ := (finCongr hcard).trans (σ₂.trans e.symm)
    refine ⟨tourEdgeSet σ₁ hV₁, ⟨hV₁, σ₁, rfl⟩, ?_⟩
    ext x
    simp only [tspVertex, LinearMap.funLeft_apply,
      mapEdgeSet_completeGraph_mem_tourEdgeSet e σ₂ hV₂ x, σ₁]
  · rintro ⟨F, ⟨hV₁, σ₁, rfl⟩, rfl⟩
    let hV₂ : 3 ≤ Fintype.card V₂ := hcard.symm ▸ hV₁
    let σ₂ : Fin (Fintype.card V₂) ≃ V₂ := (finCongr hcard.symm).trans (σ₁.trans e)
    refine ⟨tspVertex K (tourEdgeSet σ₂ hV₂), ⟨tourEdgeSet σ₂ hV₂, ⟨hV₂, σ₂, rfl⟩, rfl⟩, ?_⟩
    ext x
    simp only [LinearMap.funLeft_apply, tspVertex]
    have heqv := mapEdgeSet_completeGraph_mem_tourEdgeSet e σ₂ hV₂ x
    have hσ : (finCongr hcard).trans (σ₂.trans e.symm) = σ₁ := by
      ext j
      simp only [σ₂, Equiv.trans_apply, Equiv.symm_apply_apply]
      change σ₁ ((finCongr hcard.symm) (finCongr hcard j)) = σ₁ j
      rw [show (finCongr hcard.symm) (finCongr hcard j) = j from Fin.ext rfl]
    have heqv' : (SimpleGraph.Iso.completeGraph e).mapEdgeSet x ∈ tourEdgeSet σ₂ hV₂ ↔
        x ∈ tourEdgeSet σ₁ hV₁ := by
      simpa only [hσ] using heqv
    simp only [heqv']

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_tspPolytope_congr {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) :
    extensionComplexity (tspPolytope K V₁) = extensionComplexity (tspPolytope K V₂) :=
  extensionComplexity_eq_of_linearMaps
    (LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e).mapEdgeSet)
    (LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e.symm).mapEdgeSet)
    (tspPolytope_funLeft_eq e) (tspPolytope_funLeft_eq e.symm)

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_tspPolytope_inter_map_congr
    {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
    (e : V₁ ≃ V₂) (G : SimpleGraph V₁)
    [DecidableRel G.Adj] [DecidableRel (G.map e.toEmbedding).Adj] :
    let c₁ : ↥(⊤ : SimpleGraph V₁).edgeSet → K := fun a => if a.1 ∈ G.edgeSet then 0 else -1
    let c₂ : ↥(⊤ : SimpleGraph V₂).edgeSet → K :=
      fun b => if b.1 ∈ (G.map e.toEmbedding).edgeSet then 0 else -1
    extensionComplexity (tspPolytope K V₁ ∩ {x | c₁ ⬝ᵥ x = 0}) =
      extensionComplexity (tspPolytope K V₂ ∩ {x | c₂ ⬝ᵥ x = 0}) := by
  intro c₁ c₂
  let eEdge := (SimpleGraph.Iso.completeGraph e).mapEdgeSet
  let f : (↥(⊤ : SimpleGraph V₁).edgeSet → K) →ₗ[K] (↥(⊤ : SimpleGraph V₂).edgeSet → K) :=
    LinearMap.funLeft K K ⇑(SimpleGraph.Iso.completeGraph e.symm).mapEdgeSet
  let g : (↥(⊤ : SimpleGraph V₂).edgeSet → K) →ₗ[K] (↥(⊤ : SimpleGraph V₁).edgeSet → K) :=
    LinearMap.funLeft K K ⇑eEdge
  have hc_eq : ∀ a : ↥(⊤ : SimpleGraph V₁).edgeSet, c₂ (eEdge a) = c₁ a := fun ⟨s, _⟩ => by
    induction s using Sym2.ind with
    | _ u v =>
        change (if s(e u, e v) ∈ (G.map e.toEmbedding).edgeSet then (0 : K) else -1) =
          if s(u, v) ∈ G.edgeSet then 0 else -1
        have hmem : s(e u, e v) ∈ (G.map e.toEmbedding).edgeSet ↔ s(u, v) ∈ G.edgeSet := by
          simp only [SimpleGraph.mem_edgeSet, SimpleGraph.map_adj]
          refine ⟨fun ⟨a, b, hab, ha, hb⟩ => ?_, fun h => ⟨u, v, h, rfl, rfl⟩⟩
          exact e.injective ha ▸ e.injective hb ▸ hab
        exact if_congr hmem rfl rfl
  have hgf_inv : ∀ x, g (f x) = x := fun x => by
    ext ⟨s, _⟩
    induction s using Sym2.ind with
    | _ u v =>
        change x ⟨s(e.symm (e u), e.symm (e v)), _⟩ = x ⟨s(u, v), _⟩
        simp only [Equiv.symm_apply_apply]
  have hfg_inv : ∀ y, f (g y) = y := fun y => by
    ext ⟨s, _⟩
    induction s using Sym2.ind with
    | _ u v =>
        change y ⟨s(e (e.symm u), e (e.symm v)), _⟩ = y ⟨s(u, v), _⟩
        simp only [Equiv.apply_symm_apply]
  have hfg_dot : ∀ x, c₂ ⬝ᵥ f x = c₁ ⬝ᵥ x := fun x => by
    have hfun : (fun a => c₂ (eEdge a) * f x (eEdge a)) = fun a => c₁ a * x a := by
      ext ⟨s, _⟩
      induction s using Sym2.ind with
      | _ u v =>
          rw [hc_eq]
          congr 1
          change x ⟨s(e.symm (e u), e.symm (e v)), _⟩ = x ⟨s(u, v), _⟩
          simp only [Equiv.symm_apply_apply]
    rw [dotProduct, dotProduct, ← Equiv.sum_comp eEdge, hfun]
  have himP₂ : f '' tspPolytope K V₁ = tspPolytope K V₂ := tspPolytope_funLeft_eq e.symm
  have himP₁ : g '' tspPolytope K V₂ = tspPolytope K V₁ := tspPolytope_funLeft_eq e
  refine extensionComplexity_eq_of_linearMaps (K := K) g f ?_ ?_
  · ext x
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨hyP, hy0⟩, rfl⟩
      refine ⟨himP₁ ▸ ⟨y, hyP, rfl⟩, ?_⟩
      rw [← hfg_dot (g y), hfg_inv y]
      exact hy0
    · rintro ⟨hxP, hx0⟩
      refine ⟨f x, ⟨himP₂ ▸ ⟨x, hxP, rfl⟩, (hfg_dot x).trans hx0⟩, hgf_inv x⟩
  · ext y
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨hxP, hx0⟩, rfl⟩
      exact ⟨himP₂ ▸ ⟨x, hxP, rfl⟩, (hfg_dot x).trans hx0⟩
    · rintro ⟨hyP, hy0⟩
      refine ⟨g y, ⟨himP₁ ▸ ⟨y, hyP, rfl⟩, ?_⟩, hfg_inv y⟩
      rw [← hfg_dot (g y), hfg_inv y]
      exact hy0

end Congruence

section Reduction

private def corrPairVar {p : ℕ} (i j : Fin p) : CorrVar p :=
  if h1 : i < j then .off ⟨i, j, h1⟩
  else if h2 : j < i then .off ⟨j, i, h2⟩
  else .diag i

private def corrPairEdge {p : ℕ} (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ)
    (i j : Fin p) : ↥(⊤ : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad)).edgeSet :=
  ⟨s(SplitV.vOut (.chain (corrPairVar i j) ⟨1, by
      have := two_le_chainLen hp (corrPairVar i j); omega⟩),
    SplitV.vIn (.chain (corrPairVar i j) ⟨0, by
      have := two_le_chainLen hp (corrPairVar i j); omega⟩)),
    splitV_top_edge_vOut_vIn v₀ pad _ _⟩

private theorem chain_fin_eq {p : ℕ} {v₁ v₂ : CorrVar p} (hv : v₁ = v₂) {k : ℕ}
    (h₁ : k < chainLen p v₁) (h₂ : k < chainLen p v₂) :
    (CorrDigraphV.chain v₁ ⟨k, h₁⟩ : CorrDigraphV p) = .chain v₂ ⟨k, h₂⟩ := by
  subst hv; rfl

private theorem corrPairEdge_mem_iff_tour {p : ℕ} [NeZero p] (hp : 1 ≤ p)
    (v₀ : CorrDigraphV p) (pad : ℕ)
    {τ : Fin (Fintype.card (CorrDigraphV p)) ≃ CorrDigraphV p}
    (b : Finset (Fin p))
    (hdiag : ∀ i : Fin p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain (.diag i) ⟨1, by have := two_le_chainLen hp (.diag i); omega⟩ ∧
        τ (t + 1) = .chain (.diag i) ⟨0, by have := two_le_chainLen hp (.diag i); omega⟩) ↔
        i ∈ b)
    (hoff : ∀ e : CorrPairIdx p,
      (∃ t : Fin (Fintype.card (CorrDigraphV p)),
        τ t = .chain (.off e) ⟨1, by have := two_le_chainLen hp (.off e); omega⟩ ∧
        τ (t + 1) = .chain (.off e) ⟨0, by have := two_le_chainLen hp (.off e); omega⟩) ↔
        e.fst ∈ b ∧ e.snd ∈ b)
    {F : Finset ↥(⊤ : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad)).edgeSet}
    (hinter : ∀ u w : CorrDigraphV p,
      ⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
        ∃ t, τ t = u ∧ τ (t + 1) = w)
    (i j : Fin p) :
    corrPairEdge hp v₀ pad i j ∈ F ↔ i ∈ b ∧ j ∈ b := by
  dsimp only [corrPairEdge]
  rw [hinter]
  by_cases h1 : i < j
  · have hv : corrPairVar i j = .off ⟨i, j, h1⟩ := by
      dsimp only [corrPairVar]; simp only [eq_true h1, ↓reduceDIte]
    rw [chain_fin_eq hv _ (by have := two_le_chainLen hp (.off ⟨i, j, h1⟩); omega),
      chain_fin_eq hv _ (by have := two_le_chainLen hp (.off ⟨i, j, h1⟩); omega)]
    exact hoff ⟨i, j, h1⟩
  · by_cases h2 : j < i
    · have hv : corrPairVar i j = .off ⟨j, i, h2⟩ := by
        dsimp only [corrPairVar]; simp only [eq_false h1, eq_true h2, ↓reduceDIte]
      rw [chain_fin_eq hv _ (by have := two_le_chainLen hp (.off ⟨j, i, h2⟩); omega),
        chain_fin_eq hv _ (by have := two_le_chainLen hp (.off ⟨j, i, h2⟩); omega)]
      exact (hoff ⟨j, i, h2⟩).trans and_comm
    · have hij : i = j := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst hij
      have hv : corrPairVar i i = .diag i := by
        dsimp only [corrPairVar]; simp only [eq_false h1, ↓reduceDIte]
      rw [chain_fin_eq hv _ (by have := two_le_chainLen hp (.diag i); omega),
        chain_fin_eq hv _ (by have := two_le_chainLen hp (.diag i); omega)]
      exact (hdiag i).trans ⟨fun h => ⟨h, h⟩, fun h => h.1⟩

private theorem extensionComplexity_corrPolytope_le_splitV_face
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℕ) (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ)
    [DecidableRel (paddedSplitGraph v₀ pad (corrDigraphAdj p hp)).Adj] :
    let W := SplitV (CorrDigraphV p) v₀ pad
    let c : ↥(⊤ : SimpleGraph W).edgeSet → K :=
      fun e => if e.1 ∈ (paddedSplitGraph v₀ pad (corrDigraphAdj p hp)).edgeSet then 0 else -1
    extensionComplexity (corrPolytope K (Fin p)) ≤
      extensionComplexity (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) := by
  classical
  intro W c
  have : Nonempty (CorrDigraphV p) := ⟨v₀⟩
  have : NeZero p := ⟨by omega⟩
  let G : SimpleGraph W := paddedSplitGraph v₀ pad (corrDigraphAdj p hp)
  let π : (↥(⊤ : SimpleGraph W).edgeSet → K) →ₗ[K] ((Fin p × Fin p) → K) :=
    { toFun := fun x q => x (corrPairEdge hp v₀ pad q.1 q.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hface := tspPolytope_inter_subgraph_eq (K := K) G
  have hproj : π '' (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) = corrPolytope K (Fin p) := by
    rw [hface, LinearMap.image_convexHull, corrPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨F, hF, rfl⟩, rfl⟩
      obtain ⟨τ, _, hinter⟩ :=
        exists_dirTour_of_paddedSplitTour v₀ pad (corrDigraphAdj p hp)
          (two_le_card_corrDigraphV hp) hF
      obtain ⟨b, hdiag, hoff⟩ := exists_assignment_of_dirTour hp ‹_›
      refine ⟨b, ?_⟩
      ext ⟨i, j⟩
      simp only [π, LinearMap.coe_mk, AddHom.coe_mk, tspVertex, corrVertex_apply,
        corrPairEdge_mem_iff_tour hp v₀ pad b hdiag hoff hinter i j]
    · rintro ⟨b, rfl⟩
      obtain ⟨τ, hτ, hdiag, hoff⟩ := exists_dirTour_of_assignment hp b
      obtain ⟨F, hF, hinter⟩ :=
        paddedSplitTour_of_dirTour v₀ pad (corrDigraphAdj p hp)
          (two_le_card_corrDigraphV hp) τ hτ
      refine ⟨tspVertex K F, ⟨F, hF, rfl⟩, ?_⟩
      ext ⟨i, j⟩
      simp only [π, LinearMap.coe_mk, AddHom.coe_mk, tspVertex, corrVertex_apply,
        corrPairEdge_mem_iff_tour hp v₀ pad b hdiag hoff hinter i j]
  calc extensionComplexity (corrPolytope K (Fin p))
      = extensionComplexity (π '' (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0})) := by rw [hproj]
    _ ≤ extensionComplexity (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) :=
      extensionComplexity_image_linearMap_le _ π

/-- `corrPolytope K (Fin p)` is a linear projection of a face of the symmetric TSP polytope on
`SplitV (CorrDigraphV p) v₀ pad` vertices
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11]. -/
theorem extensionComplexity_corrPolytope_le_tspPolytope_splitV
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℕ) (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ) :
    extensionComplexity (corrPolytope K (Fin p)) ≤
      extensionComplexity (tspPolytope K (SplitV (CorrDigraphV p) v₀ pad)) := by
  classical
  exact (extensionComplexity_corrPolytope_le_splitV_face p hp v₀ pad).trans
    (extensionComplexity_inter_dotProduct_eq_le _ _ 0)

end Reduction

section LowerBound

private noncomputable def tspSplitEquiv (V : Type*) [Fintype V]
    {n : ℕ} (hn : 69 ≤ n) (hcard : Fintype.card V = n) :
    let p := Nat.sqrt (n / 69)
    let hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
    let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
    let pad := n - 3 * Fintype.card (CorrDigraphV p)
    SplitV (CorrDigraphV p) v₀ pad ≃ V := by
  intro p hp v₀ pad
  have hsq : p ^ 2 ≤ n / 69 := Nat.sqrt_le' (n / 69)
  have hcardV : Fintype.card (CorrDigraphV p) ≤ 23 * p ^ 2 := card_corrDigraphV_le hp
  have hle : 3 * Fintype.card (CorrDigraphV p) ≤ n := by omega
  exact Fintype.equivOfCardEq (by rw [card_splitV]; omega)

/-- An explicit `m`-vertex graph (`m ≥ 69`) obtained by transporting the 3-split correlation graph
with padding onto `Fin m` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11 and Theorem 12]. -/
noncomputable def tspHardGraph (m : ℕ) : SimpleGraph (Fin m) :=
  if hm : 69 ≤ m then
    let p := Nat.sqrt (m / 69)
    let hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
    let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
    let pad := m - 3 * Fintype.card (CorrDigraphV p)
    let e : SplitV (CorrDigraphV p) v₀ pad ≃ Fin m :=
      tspSplitEquiv (Fin m) hm (Fintype.card_fin m)
    SimpleGraph.map e.toEmbedding (paddedSplitGraph v₀ pad (corrDigraphAdj p hp))
  else ⊥

/-- For `m ≥ 69`, `corrPolytope K (Fin (Nat.sqrt (m / 69)))` has extension complexity at most
that of the Hamiltonian-tour face of `tspPolytope K (Fin m)` supported on `tspHardGraph m`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11]. -/
theorem extensionComplexity_corrPolytope_le_tspHardGraph_face
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (hm : 69 ≤ m) [DecidableRel (tspHardGraph m).Adj] :
    let c : ↥(⊤ : SimpleGraph (Fin m)).edgeSet → K :=
      fun e => if e.1 ∈ (tspHardGraph m).edgeSet then 0 else -1
    extensionComplexity (corrPolytope K (Fin (Nat.sqrt (m / 69)))) ≤
      extensionComplexity (tspPolytope K (Fin m) ∩ {x | c ⬝ᵥ x = 0}) := by
  classical
  intro c
  let p := Nat.sqrt (m / 69)
  have hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
  let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
  let pad := m - 3 * Fintype.card (CorrDigraphV p)
  let e : SplitV (CorrDigraphV p) v₀ pad ≃ Fin m :=
    tspSplitEquiv (Fin m) hm (Fintype.card_fin m)
  let G : SimpleGraph (SplitV (CorrDigraphV p) v₀ pad) :=
    paddedSplitGraph v₀ pad (corrDigraphAdj p hp)
  have hmap : tspHardGraph m = G.map e.toEmbedding := by
    simp only [tspHardGraph, hm, ↓reduceDIte]
    rfl
  have hc_eq : c = fun b => if b.1 ∈ (G.map e.toEmbedding).edgeSet then (0 : K) else -1 :=
    funext fun b => by
      dsimp only [c]
      exact if_congr (by rw [hmap]) rfl rfl
  rw [hc_eq, ← extensionComplexity_tspPolytope_inter_map_congr (K := K) e G]
  exact extensionComplexity_corrPolytope_le_splitV_face p hp v₀ pad

/-- Exponential `2^{Ω(√|V|)}` lower bound for the symmetric TSP polytope `tspPolytope K V` for any
finite vertex type `V` with `|V| ≥ 69` (`p = ⌊√(|V| / 69)⌋`):
`3 ^ p ≤ 2 ^ p * xc (tspPolytope K V)` in `ℕ∞`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 12]; [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_tspPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (V : Type*) [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V) :
    ((3 ^ Nat.sqrt (Fintype.card V / 69) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (Fintype.card V / 69) : ℕ∞) * extensionComplexity (tspPolytope K V) := by
  let p := Nat.sqrt (Fintype.card V / 69)
  have hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
  let v₀ : CorrDigraphV p := .gate (.diag ⟨0, hp⟩)
  let pad := Fintype.card V - 3 * Fintype.card (CorrDigraphV p)
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have h1 := three_pow_le_two_pow_mul_extensionComplexity_corrPolytope (K := K) (α := Fin p)
  rw [Fintype.card_fin] at h1
  have h2 := extensionComplexity_corrPolytope_le_tspPolytope_splitV (K := K) p hp v₀ pad
  rw [extensionComplexity_tspPolytope_congr (tspSplitEquiv V hV rfl)] at h2
  exact h1.trans (mul_le_mul_right h2 _)

/-- Integer-ceiling lower bound for `tspPolytope K V` (`|V| ≥ 69`):
`⌈(3 / 2) ^ Nat.sqrt (|V| / 69)⌉ ≤ xc (tspPolytope K V)`. -/
theorem ceil_three_div_two_pow_le_extensionComplexity_tspPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (V : Type*) [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V) :
    (((3 ^ Nat.sqrt (Fintype.card V / 69) + 2 ^ Nat.sqrt (Fintype.card V / 69) - 1) /
        2 ^ Nat.sqrt (Fintype.card V / 69) : ℕ) : ℕ∞) ≤
      extensionComplexity (tspPolytope K V) :=
  ceil_three_div_two_pow_le_of_mul_le_extensionComplexity
    (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope V hV)

/-- Field-valued `2^{Ω(√|V|)}` lower bound: any extended formulation of `tspPolytope K V`
(`|V| ≥ 69`) with `r` inequalities satisfies `(3 / 2 : F) ^ Nat.sqrt (|V| / 69) ≤ r`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 12]; [KaibelWeltge2015, Theorem 1]. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {V : Type*} [Fintype V] [DecidableEq V] (hV : 69 ≤ Fintype.card V)
    {r : ℕ} (hr : HasExtendedFormulation (tspPolytope K V) r) :
    (3 / 2 : F) ^ Nat.sqrt (Fintype.card V / 69) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope V hV)

/-- Specialization of `three_pow_le_two_pow_mul_extensionComplexity_tspPolytope` to `Fin m`
(`m ≥ 69`), routed through `tspHardGraph m`. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (hm : 69 ≤ m) :
    ((3 ^ Nat.sqrt (m / 69) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (m / 69) : ℕ∞) * extensionComplexity (tspPolytope K (Fin m)) := by
  classical
  let p := Nat.sqrt (m / 69)
  have hp : 1 ≤ p := Nat.sqrt_pos.2 (by omega)
  have : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have h1 := three_pow_le_two_pow_mul_extensionComplexity_corrPolytope (K := K) (α := Fin p)
  rw [Fintype.card_fin] at h1
  have h2 := (extensionComplexity_corrPolytope_le_tspHardGraph_face (K := K) m hm).trans
    (extensionComplexity_inter_dotProduct_eq_le (tspPolytope K (Fin m)) _ 0)
  exact h1.trans (mul_le_mul_right h2 _)

/-- Field-valued `2^{Ω(√m)}` lower bound for `tspPolytope K (Fin m)` (`m ≥ 69`): any extended
formulation with `r` inequalities satisfies `(3 / 2 : F) ^ Nat.sqrt (m / 69) ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope_fin
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {m r : ℕ} (hm : 69 ≤ m) (hr : HasExtendedFormulation (tspPolytope K (Fin m)) r) :
    (3 / 2 : F) ^ Nat.sqrt (m / 69) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le
    (three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin m hm)

end LowerBound
