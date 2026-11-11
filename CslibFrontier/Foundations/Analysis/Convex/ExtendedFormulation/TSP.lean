/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.CorrDigraph
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.FinCases

/-!
# Exponential extension-complexity lower bound for TSP polytopes

This module completes the Fiorini–Massar–Pokutta–Tiwary–de Wolf reduction from the correlation
polytope `corrPolytope K (Fin p)` to the symmetric traveling salesman polytope `tspPolytope K V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11 and Theorem 12], combined with
Kaibel–Weltge's `(3 / 2) ^ p` bound on `corrPolytope` [KaibelWeltge2015, Theorem 1].

For `p ≥ 1`, `SplitV (CorrDigraphV p) v₀ pad` has `3 * |CorrDigraphV p| + pad ≤ 69 * p ^ 2 + pad`
vertices, and intersecting `tspPolytope K W` with the zero-weight facet for non-edges of
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

private def tspEdgeEquiv {V W : Type*} (e : V ≃ W) :
    ↥(⊤ : SimpleGraph V).edgeSet ≃ ↥(⊤ : SimpleGraph W).edgeSet where
  toFun x := ⟨Sym2.map e x.1, by
    obtain ⟨s, hs⟩ := x
    induction s using Sym2.ind with
    | _ u v =>
        simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, Sym2.map_mk, ne_eq,
          EmbeddingLike.apply_eq_iff_eq] using hs⟩
  invFun y := ⟨Sym2.map e.symm y.1, by
    obtain ⟨s, hs⟩ := y
    induction s using Sym2.ind with
    | _ u v =>
        simpa only [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, Sym2.map_mk, ne_eq,
          EmbeddingLike.apply_eq_iff_eq] using hs⟩
  left_inv x := by
    ext
    obtain ⟨s, _⟩ := x
    simp only [Sym2.map_map, Function.comp_def, Equiv.symm_apply_apply, Sym2.map_id', id_eq]
  right_inv y := by
    ext
    obtain ⟨s, _⟩ := y
    simp only [Sym2.map_map, Function.comp_def, Equiv.apply_symm_apply, Sym2.map_id', id_eq]

private theorem tspEdgeEquiv_mem_tourEdgeSet {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂)
    (σ₂ : Fin (Fintype.card V₂) ≃ V₂) (hV₂ : 3 ≤ Fintype.card V₂)
    (x : ↥(⊤ : SimpleGraph V₁).edgeSet) :
    let hcard : Fintype.card V₁ = Fintype.card V₂ := Fintype.card_congr e
    let hV₁ : 3 ≤ Fintype.card V₁ := hcard ▸ hV₂
    let σ₁ : Fin (Fintype.card V₁) ≃ V₁ := (finCongr hcard).trans (σ₂.trans e.symm)
    tspEdgeEquiv e x ∈ tourEdgeSet σ₂ hV₂ ↔ x ∈ tourEdgeSet σ₁ hV₁ := by
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
      simp only [tourEdgeSet, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff,
        tspEdgeEquiv, Equiv.coe_fn_mk, Sym2.map_mk]
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
    LinearMap.funLeft K K ⇑(tspEdgeEquiv e) '' tspPolytope K V₂ = tspPolytope K V₁ := by
  have hcard : Fintype.card V₁ = Fintype.card V₂ := Fintype.card_congr e
  rw [tspPolytope, image_linearMap_convexHull, tspPolytope]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨F, ⟨hV₂, σ₂, rfl⟩, rfl⟩, rfl⟩
    let hV₁ : 3 ≤ Fintype.card V₁ := hcard ▸ hV₂
    let σ₁ : Fin (Fintype.card V₁) ≃ V₁ := (finCongr hcard).trans (σ₂.trans e.symm)
    refine ⟨tourEdgeSet σ₁ hV₁, ⟨hV₁, σ₁, rfl⟩, ?_⟩
    ext x
    simp only [tspVertex, LinearMap.funLeft_apply, tspEdgeEquiv_mem_tourEdgeSet e σ₂ hV₂ x, σ₁]
  · rintro ⟨F, ⟨hV₁, σ₁, rfl⟩, rfl⟩
    let hV₂ : 3 ≤ Fintype.card V₂ := hcard.symm ▸ hV₁
    let σ₂ : Fin (Fintype.card V₂) ≃ V₂ := (finCongr hcard.symm).trans (σ₁.trans e)
    refine ⟨tspVertex K (tourEdgeSet σ₂ hV₂), ⟨tourEdgeSet σ₂ hV₂, ⟨hV₂, σ₂, rfl⟩, rfl⟩, ?_⟩
    ext x
    simp only [LinearMap.funLeft_apply, tspVertex]
    have heqv := tspEdgeEquiv_mem_tourEdgeSet e σ₂ hV₂ x
    have hσ : (finCongr hcard).trans (σ₂.trans e.symm) = σ₁ := by
      ext j
      simp only [σ₂, Equiv.trans_apply, Equiv.symm_apply_apply]
      change σ₁ ((finCongr hcard.symm) (finCongr hcard j)) = σ₁ j
      rw [show (finCongr hcard.symm) (finCongr hcard j) = j from Fin.ext rfl]
    have heqv' : tspEdgeEquiv e x ∈ tourEdgeSet σ₂ hV₂ ↔ x ∈ tourEdgeSet σ₁ hV₁ := by
      simpa only [hσ] using heqv
    simp only [heqv']

omit [IsStrictOrderedRing K] in
private theorem extensionComplexity_tspPolytope_congr {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂]
    [DecidableEq V₁] [DecidableEq V₂] (e : V₁ ≃ V₂) :
    extensionComplexity (tspPolytope K V₁) = extensionComplexity (tspPolytope K V₂) :=
  extensionComplexity_eq_of_linearMaps (LinearMap.funLeft K K ⇑(tspEdgeEquiv e))
    (LinearMap.funLeft K K ⇑(tspEdgeEquiv e.symm)) (tspPolytope_funLeft_eq e)
    (tspPolytope_funLeft_eq e.symm)

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

/-- `corrPolytope K (Fin p)` is a linear projection of a face of the symmetric TSP polytope on
`SplitV (CorrDigraphV p) v₀ pad` vertices
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Lemma 11]. -/
theorem extensionComplexity_corrPolytope_le_tspPolytope_splitV
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℕ) (hp : 1 ≤ p) (v₀ : CorrDigraphV p) (pad : ℕ) :
    extensionComplexity (corrPolytope K (Fin p)) ≤
      extensionComplexity (tspPolytope K (SplitV (CorrDigraphV p) v₀ pad)) := by
  classical
  have : Nonempty (CorrDigraphV p) := ⟨v₀⟩
  have : NeZero p := ⟨by omega⟩
  let W := SplitV (CorrDigraphV p) v₀ pad
  let G : SimpleGraph W := paddedSplitGraph v₀ pad (corrDigraphAdj p hp)
  let c : ↥(⊤ : SimpleGraph W).edgeSet → K := fun e => if ↑e ∈ G.edgeSet then 0 else -1
  let π : (↥(⊤ : SimpleGraph W).edgeSet → K) →ₗ[K] ((Fin p × Fin p) → K) :=
    { toFun := fun x q => x (corrPairEdge hp v₀ pad q.1 q.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hface := tspPolytope_inter_subgraph_eq (K := K) G
  have hproj : π '' (tspPolytope K W ∩ {x | c ⬝ᵥ x = 0}) = corrPolytope K (Fin p) := by
    rw [hface, image_linearMap_convexHull, corrPolytope]
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
    _ ≤ extensionComplexity (tspPolytope K W) :=
      extensionComplexity_inter_dotProduct_eq_le (tspPolytope K W) c 0

end Reduction

section LowerBound

private noncomputable def tspSplitEquiv (V : Type*) [Fintype V] [DecidableEq V]
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
(`m ≥ 69`). -/
theorem three_pow_le_two_pow_mul_extensionComplexity_tspPolytope_fin
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (m : ℕ) (hm : 69 ≤ m) :
    ((3 ^ Nat.sqrt (m / 69) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (m / 69) : ℕ∞) * extensionComplexity (tspPolytope K (Fin m)) := by
  simpa only [Fintype.card_fin] using
    three_pow_le_two_pow_mul_extensionComplexity_tspPolytope (K := K) (Fin m)
      (by simpa only [Fintype.card_fin] using hm)

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
