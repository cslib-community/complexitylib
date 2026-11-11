/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Reduction
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.FinCases

/-!
# TSP polytopes and directed-to-undirected tour splits

This module defines the symmetric traveling salesman polytope `tspPolytope K V` (`TSP(V)`) on the
complete graph over a finite vertex type `V`, and formalizes the directed-to-undirected `3`-split
construction (with edge-subdivision padding on a distinguished vertex `v₀`) used in
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4, Step (iii) of Lemma 11].

Given an irreflexive directed graph `adjD : W → W → Prop` on `|W| ≥ 2` vertices, `paddedSplitGraph`
replaces each `w ≠ v₀` by a `3`-path `vIn w - vMid w 0 - vOut w` and `v₀` by a `(pad + 3)`-path
`vIn v₀ - vMid v₀ 0 - ... - vMid v₀ pad - vOut v₀`, adding `{vOut u, vIn w}` for each directed arc
`adjD u w`. Every undirected Hamiltonian tour of `paddedSplitGraph` comes from a directed
Hamiltonian cycle `τ : Fin |W| ≃ W` of `adjD` (`exists_dirTour_of_paddedSplitTour`), and every
directed Hamiltonian cycle lifts back to an undirected tour (`paddedSplitTour_of_dirTour`).

## Main definitions

* `tourEdgeSet`, `IsTourEdgeSet`: Hamiltonian tour edge sets on the complete graph `K_V`.
* `tspVertex`, `tspPolytope`: the symmetric TSP polytope `TSP(V)`.
* `SplitV`, `paddedSplitGraph`: the `3`-split undirected graph of a digraph with optional padding.
* `IsDirTour`: cyclic permutation `τ : Fin |W| ≃ W` traversing arcs of `adjD`.

## Main results

* `IsTourEdgeSet.card_splitV`: `Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad`.
* `exists_dirTour_of_paddedSplitTour`: every undirected tour of `paddedSplitGraph` induces a
  directed tour of `adjD` with matching inter-gadget edges.
* `paddedSplitTour_of_dirTour`: every directed tour of `adjD` lifts to an undirected tour of
  `paddedSplitGraph`.
* `tspPolytope_inter_subgraph_eq`: intersecting `TSP(V)` with `x_e = 0` for non-edges of `G`
  gives the convex hull of tours of `G`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.4 (Lemma 11, Step (iii)).
-/

public section

section TSPPolytope

/-- Every vertex pair along a bijection `σ : Fin |V| ≃ V` at step `i` and `i + 1` is distinct
when `3 ≤ |V|`. -/
theorem tourEdge_mem_top_edgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V) (i : Fin (Fintype.card V)) :
    s(σ i, σ (i + 1)) ∈ (⊤ : SimpleGraph V).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  intro h
  have h1 : (1 : Fin (Fintype.card V)) = 0 := add_left_eq_self.1 (i.add_comm 1 ▸ h.symm)
  have hval := congrArg Fin.val h1
  have hmod : 1 < Fintype.card V := by omega
  simp only [Fin.val_one' hmod, Fin.val_zero] at hval
  omega

/-- The edge set in `K_V` traced by the cyclic ordering `σ : Fin |V| ≃ V`. -/
def tourEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) :
    Finset ↥(⊤ : SimpleGraph V).edgeSet :=
  Finset.univ.image fun i => ⟨s(σ i, σ (i + 1)), tourEdge_mem_top_edgeSet hV σ i⟩

/-- `F` is the edge set of a Hamiltonian cycle (tour) of `K_V` (`|V| ≥ 3`). -/
@[expose] def IsTourEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : Prop :=
  ∃ (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V), F = tourEdgeSet σ hV

/-- `F` is a Hamiltonian tour contained in the spanning subgraph `G : SimpleGraph V`. -/
@[expose] def IsSubgraphTour {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : Prop :=
  IsTourEdgeSet F ∧ ∀ e ∈ F, e.1 ∈ G.edgeSet

section Polytope

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- Characteristic vector of an edge set `F` in `K_V`. -/
@[expose] def tspVertex {V : Type*} [DecidableEq V]
    (F : Finset ↥(⊤ : SimpleGraph V).edgeSet) : ↥(⊤ : SimpleGraph V).edgeSet → K :=
  fun e => if e ∈ F then 1 else 0

/-- The symmetric **traveling salesman polytope** `TSP(V)`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.4]. -/
@[expose] def tspPolytope (V : Type*) [Fintype V] [DecidableEq V] :
    Set (↥(⊤ : SimpleGraph V).edgeSet → K) :=
  convexHull K (Set.range fun F : {F // IsTourEdgeSet F} => tspVertex K F.1)

end Polytope

/-- Intersecting `TSP(V)` with `{x | c_nonEdge ⬝ᵥ x = 0}` selects the face of tours of `G`. -/
theorem tspPolytope_inter_subgraph_eq
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    let c : ↥(⊤ : SimpleGraph V).edgeSet → K := fun e => if e.1 ∈ G.edgeSet then 0 else -1
    tspPolytope K V ∩ {x | c ⬝ᵥ x = 0} =
      convexHull K (Set.range fun F : {F // IsSubgraphTour G F} => tspVertex K F.1) := by
  classical
  intro c
  have hdot : ∀ F : Finset ↥(⊤ : SimpleGraph V).edgeSet,
      c ⬝ᵥ tspVertex K F = -((F.filter fun e => e.1 ∉ G.edgeSet).card : K) := fun F => by
    simp only [dotProduct, c, tspVertex]
    rw [← Finset.sum_neg_distrib]
    have hterm : ∀ e : ↥(⊤ : SimpleGraph V).edgeSet,
        -((if e.1 ∈ G.edgeSet then (0 : K) else -1) * (if e ∈ F then 1 else 0)) =
          if e ∈ F ∧ e.1 ∉ G.edgeSet then 1 else 0 := fun e => by
      by_cases hg : e.1 ∈ G.edgeSet <;> by_cases hf : e ∈ F <;>
        simp only [hg, hf, not_true_eq_false, not_false_eq_true, and_self, and_true, and_false,
          ↓reduceIte, mul_one, mul_zero, zero_mul, neg_zero, neg_neg]
    simp only [hterm, Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rfl
  have hvalid : ∀ F : {F // IsTourEdgeSet F}, c ⬝ᵥ tspVertex K F.1 ≤ 0 := fun F => by
    rw [hdot]
    exact neg_nonpos.2 (Nat.cast_nonneg _)
  have htight : ∀ F : {F // IsTourEdgeSet F},
      c ⬝ᵥ tspVertex K F.1 = 0 ↔ IsSubgraphTour G F.1 := fun F => by
    rw [hdot, neg_eq_zero, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    refine ⟨fun h => ⟨F.2, fun e he => not_not.1 (h he)⟩, fun ⟨_, h⟩ e he => not_not.2 (h e he)⟩
  rw [tspPolytope, convexHull_inter_dotProduct_eq hvalid]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨_, ⟨F, hF, hFx, rfl⟩, rfl⟩
    rw [htight ⟨F, hF⟩] at hFx
    exact ⟨F, hFx, rfl⟩
  · rintro ⟨F, hFG, rfl⟩
    refine ⟨tspVertex K F, ⟨F, hFG.1, ?_, rfl⟩, rfl⟩
    exact (htight ⟨F, hFG.1⟩).2 hFG

end TSPPolytope

section SplitGraph

/-- Middle chain length of `w` in `SplitV W v₀ pad`: `pad + 1` at `v₀` and `1` elsewhere. -/
@[expose] def splitMidLen {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) : ℕ :=
  if w = v₀ then pad + 1 else 1

/-- Vertices of the `3`-split undirected graph of a digraph on `W`, with `pad` extra middle
nodes inserted at `v₀` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Step (iii)]. -/
inductive SplitV (W : Type*) [DecidableEq W] (v₀ : W) (pad : ℕ) : Type
  | vIn (w : W)
  | vMid (w : W) (k : Fin (splitMidLen v₀ pad w))
  | vOut (w : W)
  deriving DecidableEq

private def splitVEquiv {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    SplitV W v₀ pad ≃ W ⊕ (Σ w : W, Fin (splitMidLen v₀ pad w)) ⊕ W where
  toFun
    | .vIn w => Sum.inl w
    | .vMid w k => Sum.inr (Sum.inl ⟨w, k⟩)
    | .vOut w => Sum.inr (Sum.inr w)
  invFun
    | Sum.inl w => .vIn w
    | Sum.inr (Sum.inl ⟨w, k⟩) => .vMid w k
    | Sum.inr (Sum.inr w) => .vOut w
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with w | ⟨w, k⟩ | w <;> rfl

instance {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype (SplitV W v₀ pad) :=
  Fintype.ofEquiv _ (splitVEquiv v₀ pad).symm

private theorem sum_splitMidLen {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    ∑ w : W, splitMidLen v₀ pad w = Fintype.card W + pad := by
  simp only [splitMidLen]
  have hsplit : (Finset.univ : Finset W).sum (fun w => if w = v₀ then pad + 1 else 1) =
      ∑ w : W, (1 + if w = v₀ then pad else 0) :=
    Finset.sum_congr rfl fun w _ => by by_cases h : w = v₀ <;> simp [h]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- `SplitV W v₀ pad` has `3 * |W| + pad` vertices. -/
theorem card_splitV {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad := by
  rw [Fintype.card_congr (splitVEquiv v₀ pad), Fintype.card_sum, Fintype.card_sum,
    Fintype.card_sigma]
  have hsum : ∑ w : W, Fintype.card (Fin (splitMidLen v₀ pad w)) = Fintype.card W + pad := by
    simpa only [Fintype.card_fin] using sum_splitMidLen v₀ pad
  rw [hsum]
  ring

private def splitAdjRel {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) : SplitV W v₀ pad → SplitV W v₀ pad → Prop
  | .vIn u, .vMid w k => u = w ∧ k.1 = 0
  | .vMid w k, .vIn u => u = w ∧ k.1 = 0
  | .vMid u k₁, .vMid w k₂ => u = w ∧ (k₁.1 + 1 = k₂.1 ∨ k₂.1 + 1 = k₁.1)
  | .vMid w k, .vOut u => u = w ∧ k.1 + 1 = splitMidLen v₀ pad w
  | .vOut u, .vMid w k => u = w ∧ k.1 + 1 = splitMidLen v₀ pad w
  | .vOut u, .vIn w => adjD u w
  | .vIn w, .vOut u => adjD u w
  | _, _ => False

/-- The undirected `3`-split (plus `pad` vertices on `v₀`) of `adjD`. -/
def paddedSplitGraph {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) : SimpleGraph (SplitV W v₀ pad) where
  Adj := splitAdjRel v₀ pad adjD
  symm u v h := by
    cases u <;> cases v <;> simp only [splitAdjRel] at h ⊢ <;> tauto
  loopless u h := by
    cases u <;> simp only [splitAdjRel] at h
    omega

private theorem splitMidLen_pos {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) :
    0 < splitMidLen v₀ pad w := by
  dsimp only [splitMidLen]
  split_ifs <;> omega

/-- Every directed Hamiltonian tour of `(W, adjD)` lifts to a subgraph tour of
`paddedSplitGraph v₀ pad adjD` matching the inter-gadget arcs. -/
theorem paddedSplitTour_of_dirTour {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) (hW : 2 ≤ Fintype.card W)
    (τ : Fin (Fintype.card W) ≃ W) (hτ : IsDirTour adjD τ) :
    ∃ F : Finset ↥(⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet,
      IsSubgraphTour (paddedSplitGraph v₀ pad adjD) F ∧
      ∀ u w : W,
        (⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
          ∃ t : Fin (Fintype.card W), τ t = u ∧ τ (t + 1) = w) := by
  classical
  let m := Fintype.card W
  let t₀ : Fin m := τ.symm v₀
  let τ' : Fin m ≃ W :=
    { toFun := fun t => τ (t₀ + t)
      invFun := fun w => τ.symm w - t₀
      left_inv := fun t => by simp only [Equiv.symm_apply_apply, add_sub_cancel_left]
      right_inv := fun w => by simp only [add_sub_cancel, Equiv.apply_symm_apply] }
  have hτ'_adj : ∀ t : Fin m, adjD (τ' t) (τ' (t + 1)) := fun t => by
    dsimp only [τ', Equiv.coe_fn_mk]
    rw [← add_assoc]
    exact hτ (t₀ + t)
  have hτ'0 : τ' 0 = v₀ := by simp only [τ', t₀, Equiv.coe_fn_mk, add_zero, Equiv.apply_symm_apply]
  have hτ'_symm0 : τ'.symm v₀ = 0 := τ'.symm_apply_eq.2 hτ'0.symm
  have hτ'_ne : ∀ {t : Fin m}, t ≠ 0 → τ' t ≠ v₀ := fun {t} ht h =>
    ht (τ'.injective (h.trans hτ'0.symm))
  have hM_card : Fintype.card (SplitV W v₀ pad) = 3 * m + pad := card_splitV v₀ pad
  have hM3 : 3 ≤ Fintype.card (SplitV W v₀ pad) := by omega
  let splitPos : W → ℕ := fun w => if τ'.symm w = 0 then 0 else 3 * (τ'.symm w).1 + pad
  have hpos_v0 : splitPos v₀ = 0 := by simp only [splitPos, hτ'_symm0, ↓reduceIte]
  let fromSplit : SplitV W v₀ pad → Fin (3 * m + pad) := fun x =>
    match x with
    | .vIn w => ⟨splitPos w, by
        dsimp only [splitPos]; split_ifs with h <;> omega⟩
    | .vMid w k => ⟨splitPos w + 1 + k.1, by
        dsimp only [splitPos]; split_ifs with h
        · have hw : w = v₀ := τ'.symm.injective (h.trans hτ'_symm0.symm)
          have hk := k.2; simp only [splitMidLen, hw, ↓reduceIte] at hk; omega
        · have hw : w ≠ v₀ := fun he => h (he ▸ hτ'_symm0)
          have hk := k.2; simp only [splitMidLen, hw, ↓reduceIte] at hk; omega⟩
    | .vOut w => ⟨splitPos w + 1 + splitMidLen v₀ pad w, by
        dsimp only [splitPos, splitMidLen]; split_ifs with h hw hw <;> omega⟩
  let toSplit : Fin (3 * m + pad) → SplitV W v₀ pad := fun i =>
    if h0 : i.1 = 0 then .vIn v₀
    else if h1 : i.1 < pad + 2 then
      .vMid v₀ ⟨i.1 - 1, by simp only [splitMidLen, ↓reduceIte]; omega⟩
    else if h2 : i.1 = pad + 2 then .vOut v₀
    else
      let j := i.1 - (pad + 3)
      let t : Fin m := ⟨j / 3 + 1, by omega⟩
      if j % 3 = 0 then .vIn (τ' t)
      else if j % 3 = 1 then .vMid (τ' t) ⟨0, splitMidLen_pos v₀ pad _⟩
      else .vOut (τ' t)
  have hleft : ∀ x, toSplit (fromSplit x) = x := fun x => by
    cases x with
    | vIn w =>
        by_cases hw : w = v₀
        · subst hw; simp only [fromSplit, hpos_v0, toSplit, ↓reduceDIte]
        · have ht : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have ht1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
          dsimp only [fromSplit, splitPos, toSplit]
          rw [if_neg ht]
          have hj : 3 * (τ'.symm w).1 + pad - (pad + 3) = 3 * ((τ'.symm w).1 - 1) := by omega
          have h0 : ¬ 3 * (τ'.symm w).1 + pad = 0 := by omega
          have h1 : ¬ 3 * (τ'.symm w).1 + pad < pad + 2 := by omega
          have h2 : ¬ 3 * (τ'.symm w).1 + pad = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte, hj, Nat.mul_div_right _ (by omega : 0 < 3),
            Nat.mul_mod_right, ↓reduceIte]
          congr 1
          rw [← Fin.ext_iff] at *
          have hsub : (τ'.symm w).1 - 1 + 1 = (τ'.symm w).1 := by omega
          simp only [Fin.ext hsub, Equiv.apply_symm_apply]
    | vMid w k =>
        by_cases hw : w = v₀
        · subst hw
          have hk := k.2; simp only [splitMidLen, ↓reduceIte] at hk
          dsimp only [fromSplit, toSplit]
          rw [hpos_v0]
          have h0 : ¬ 0 + 1 + k.1 = 0 := by omega
          have h1 : 0 + 1 + k.1 < pad + 2 := by omega
          simp only [h0, h1, ↓reduceDIte, Nat.add_sub_cancel_left]
          congr 1
          exact Fin.ext (by omega)
        · have ht : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have ht1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
          have hk := k.2; simp only [splitMidLen, hw, ↓reduceIte] at hk
          have hk0 : k.1 = 0 := by omega
          dsimp only [fromSplit, splitPos, toSplit]
          rw [if_neg ht, hk0]
          have hj : 3 * (τ'.symm w).1 + pad + 1 + 0 - (pad + 3) =
              3 * ((τ'.symm w).1 - 1) + 1 := by omega
          have h0 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 0 = 0 := by omega
          have h1 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 0 < pad + 2 := by omega
          have h2 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 0 = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte, hj]
          have hdiv : (3 * ((τ'.symm w).1 - 1) + 1) / 3 = (τ'.symm w).1 - 1 := by omega
          have hmod : (3 * ((τ'.symm w).1 - 1) + 1) % 3 = 1 := by omega
          simp only [hmod, One.one_ne_zero, ↓reduceIte, hdiv]
          have hfin : (⟨(τ'.symm w).1 - 1 + 1, by omega⟩ : Fin m) = τ'.symm w :=
            Fin.ext (by omega)
          rw [hfin, Equiv.apply_symm_apply]
          congr 1
          exact Fin.ext (by simp [hk0])
    | vOut w =>
        by_cases hw : w = v₀
        · subst hw
          dsimp only [fromSplit, toSplit, splitMidLen]
          rw [hpos_v0, if_pos rfl]
          have h0 : ¬ 0 + 1 + (pad + 1) = 0 := by omega
          have h1 : ¬ 0 + 1 + (pad + 1) < pad + 2 := by omega
          have h2 : 0 + 1 + (pad + 1) = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte]
        · have ht : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have ht1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
          dsimp only [fromSplit, splitPos, splitMidLen, toSplit]
          rw [if_neg ht, if_neg hw]
          have hj : 3 * (τ'.symm w).1 + pad + 1 + 1 - (pad + 3) =
              3 * ((τ'.symm w).1 - 1) + 2 := by omega
          have h0 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 = 0 := by omega
          have h1 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 < pad + 2 := by omega
          have h2 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte, hj]
          have hdiv : (3 * ((τ'.symm w).1 - 1) + 2) / 3 = (τ'.symm w).1 - 1 := by omega
          have hmod : (3 * ((τ'.symm w).1 - 1) + 2) % 3 = 2 := by omega
          simp only [hmod, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hdiv]
          have hfin : (⟨(τ'.symm w).1 - 1 + 1, by omega⟩ : Fin m) = τ'.symm w :=
            Fin.ext (by omega)
          rw [hfin, Equiv.apply_symm_apply]
  have hright : ∀ i, fromSplit (toSplit i) = i := fun i => by
    dsimp only [toSplit]
    split_ifs with h0 h1 h2 hmod0 hmod1
    · ext; simp only [fromSplit, hpos_v0]; exact h0.symm
    · ext; simp only [fromSplit, hpos_v0]; omega
    · ext; simp only [fromSplit, hpos_v0, splitMidLen, ↓reduceIte]; omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      ext
      simp only [fromSplit, splitPos, Equiv.symm_apply_apply, ht0, ↓reduceIte]
      omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      ext
      simp only [fromSplit, splitPos, Equiv.symm_apply_apply, ht0, ↓reduceIte]
      omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have hne : τ' ⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ ≠ v₀ := hτ'_ne ht0
      ext
      simp only [fromSplit, splitPos, splitMidLen, Equiv.symm_apply_apply, ht0, hne, ↓reduceIte]
      omega
  let eFin : Fin (Fintype.card (SplitV W v₀ pad)) ≃ Fin (3 * m + pad) := Fin.castOrderIso hM_card
  let eSplit : SplitV W v₀ pad ≃ Fin (3 * m + pad) := ⟨fromSplit, toSplit, hleft, hright⟩
  let σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad :=
    eFin.toEquiv.trans eSplit.symm
  have hσ_succ : ∀ i : Fin (3 * m + pad),
      (paddedSplitGraph v₀ pad adjD).Adj (toSplit i) (toSplit (i + 1)) := fun i => by
    have hmod_succ : (i + 1).1 = if i.1 + 1 = 3 * m + pad then 0 else i.1 + 1 := by
      have hlt : i.1 < 3 * m + pad := i.2
      simp only [Fin.val_add, Fin.val_one' (by omega : 1 < 3 * m + pad)]
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    dsimp only [paddedSplitGraph, toSplit]
    by_cases h0 : i.1 = 0
    · have h1 : ¬ i.1 + 1 = 3 * m + pad := by omega
      have ha : (i + 1).1 = 1 := by rw [hmod_succ, if_neg h1, h0]
      simp only [h0, ↓reduceDIte, ha, One.one_ne_zero, show 1 < pad + 2 by omega, splitAdjRel,
        Nat.sub_self, and_self]
    · by_cases h1 : i.1 < pad + 1
      · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
        have ha : (i + 1).1 = i.1 + 1 := by rw [hmod_succ, if_neg hm1]
        have hlt2 : i.1 < pad + 2 := by omega
        have hlt2' : i.1 + 1 < pad + 2 := by omega
        have ha0 : i.1 + 1 ≠ 0 := by omega
        simp only [h0, hlt2, ↓reduceDIte, ha, ha0, hlt2', splitAdjRel, true_and]
        left; omega
      · by_cases h1' : i.1 = pad + 1
        · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
          have ha : (i + 1).1 = pad + 2 := by rw [hmod_succ, if_neg hm1, h1']
          have hlt2 : i.1 < pad + 2 := by omega
          simp only [h0, hlt2, ↓reduceDIte, ha, show pad + 2 ≠ 0 by omega,
            show ¬ pad + 2 < pad + 2 by omega, splitAdjRel, splitMidLen, h1']
          exact ⟨rfl, rfl⟩
        · by_cases h2 : i.1 = pad + 2
          · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
            have ha : (i + 1).1 = pad + 3 := by rw [hmod_succ, if_neg hm1, h2]
            simp only [h0, h1, h2, ↓reduceDIte, show ¬ pad + 2 < pad + 2 by omega,
              ha, show pad + 3 ≠ 0 by omega, show ¬ pad + 3 < pad + 2 by omega,
              show pad + 3 ≠ pad + 2 by omega, Nat.sub_self, Nat.zero_div, Nat.zero_mod,
              splitAdjRel]
            simpa only [hτ'0] using hτ'_adj 0
          · have hge : pad + 3 ≤ i.1 := by omega
            have hlt1 : ¬ i.1 < pad + 2 := by omega
            by_cases hlast : i.1 + 1 = 3 * m + pad
            · have ha : (i + 1).1 = 0 := by rw [hmod_succ, if_pos hlast]
              have hj : i.1 - (pad + 3) = 3 * (m - 1) - 1 := by omega
              have hmod2 : (i.1 - (pad + 3)) % 3 = 2 := by omega
              have hdiv : (i.1 - (pad + 3)) / 3 + 1 = m - 1 := by omega
              simp only [h0, hlt1, h2, ↓reduceDIte, ha, hmod2,
                show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, splitAdjRel]
              have hm_eq : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) + 1 = 0 := by
                ext; simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), hdiv, Fin.val_zero]
                rw [show m - 1 + 1 = m by omega, Nat.mod_self]
              have hgoal := hτ'_adj ⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩
              rwa [hm_eq, hτ'0] at hgoal
            · have ha : (i + 1).1 = i.1 + 1 := by rw [hmod_succ, if_neg hlast]
              have ha0 : i.1 + 1 ≠ 0 := by omega
              have ha1 : ¬ i.1 + 1 < pad + 2 := by omega
              have ha2 : i.1 + 1 ≠ pad + 2 := by omega
              let j := i.1 - (pad + 3)
              have hj' : i.1 + 1 - (pad + 3) = j + 1 := by omega
              rcases Nat.mod_lt j (by omega : 0 < 3) with hmod
              have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
              rcases hcases with hr | hr | hr
              · have hdiv' : (j + 1) / 3 = j / 3 := by omega
                have hmod' : (j + 1) % 3 = 1 := by omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj', hr, hdiv', hmod',
                  One.one_ne_zero, splitAdjRel, and_self]
              · have hdiv' : (j + 1) / 3 = j / 3 := by omega
                have hmod' : (j + 1) % 3 = 2 := by omega
                have ht0 : (⟨j / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
                  intro h; have := congrArg Fin.val h; simp at this; omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj', hr, hdiv', hmod',
                  One.one_ne_zero, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                  splitAdjRel, splitMidLen, hτ'_ne ht0]
                exact ⟨rfl, rfl⟩
              · have hdiv' : (j + 1) / 3 = j / 3 + 1 := by omega
                have hmod' : (j + 1) % 3 = 0 := by omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj', hr, hdiv', hmod',
                  show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, splitAdjRel]
                have hfin : (⟨j / 3 + 1 + 1, by omega⟩ : Fin m) =
                    ⟨j / 3 + 1, by omega⟩ + 1 := by
                  ext
                  simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
                  exact (Nat.mod_eq_of_lt (by omega)).symm
                rw [hfin]
                exact hτ'_adj ⟨j / 3 + 1, by omega⟩
  have hσ_adj : ∀ k : Fin (Fintype.card (SplitV W v₀ pad)),
      (paddedSplitGraph v₀ pad adjD).Adj (σ k) (σ (k + 1)) := fun k => by
    have hk : eFin (k + 1) = eFin k + 1 := by
      ext
      simp only [eFin, Fin.coe_orderIso_apply, Fin.cast_val_eq_self, Fin.val_add,
        Fin.val_one' (by omega : 1 < Fintype.card (SplitV W v₀ pad)),
        Fin.val_one' (by omega : 1 < 3 * m + pad), hM_card]
    simp only [σ, Equiv.trans_apply, eSplit, Equiv.coe_fn_symm_mk, hk]
    exact hσ_succ (eFin k)
  refine ⟨tourEdgeSet σ hM3, ⟨⟨hM3, σ, rfl⟩, fun e he => ?_⟩, fun u w => ?_⟩
  · rw [tourEdgeSet, Finset.mem_image] at he
    obtain ⟨k, _, rfl⟩ := he
    exact (SimpleGraph.mem_edgeSet _).2 (hσ_adj k)
  · simp only [tourEdgeSet, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
    constructor
    · rintro ⟨k, hk⟩
      have hadj := hσ_adj k
      have hk_eq : (σ k = .vOut u ∧ σ (k + 1) = .vIn w) ∨
          (σ k = .vIn w ∧ σ (k + 1) = .vOut u) := by
        simpa only [Sym2.eq_iff] using hk
      have hnot_rev : ¬ (σ k = .vIn w ∧ σ (k + 1) = .vOut u) := by
        rintro ⟨h1, h2⟩
        have hk1 : eFin (k + 1) = eFin k + 1 := by
          ext; simp only [eFin, Fin.coe_orderIso_apply, Fin.cast_val_eq_self, Fin.val_add,
            Fin.val_one' (by omega : 1 < Fintype.card (SplitV W v₀ pad)),
            Fin.val_one' (by omega : 1 < 3 * m + pad), hM_card]
        simp only [σ, Equiv.trans_apply, eSplit, Equiv.coe_fn_symm_mk, hk1] at h1 h2
        have heq1 := congrArg fromSplit h1
        have heq2 := congrArg fromSplit h2
        rw [hright] at heq1 heq2
        have hpos1 := congrArg Fin.val heq1
        have hpos2 := congrArg Fin.val heq2
        dsimp only [fromSplit, splitPos, splitMidLen] at hpos1 hpos2
        have hstep : (eFin k + 1).1 = if (eFin k).1 + 1 = 3 * m + pad then 0 else (eFin k).1 + 1 := by
          simp only [Fin.val_add, Fin.val_one' (by omega : 1 < 3 * m + pad)]
          split_ifs with h <;> [rw [h, Nat.mod_self]; exact Nat.mod_eq_of_lt (by omega)]
        split_ifs at hpos1 hpos2 hstep <;> omega
      rcases hk_eq with ⟨hu, hw⟩ | hbad
      · have hwrap : ∀ t : Fin m, (⟨splitPos (τ' t) + 1 + splitMidLen v₀ pad (τ' t), by
            dsimp only [splitPos, splitMidLen]; split_ifs <;> omega⟩ : Fin (3 * m + pad)) + 1 =
            ⟨splitPos (τ' (t + 1)), by dsimp only [splitPos]; split_ifs <;> omega⟩ := by
          intro t
          ext
          dsimp only [splitPos, splitMidLen]
          simp only [Fin.val_add, Fin.val_one' (by omega : 1 < 3 * m + pad),
            Fin.val_one' (by omega : 1 < m), Equiv.symm_apply_apply]
          by_cases ht0 : t = 0
          · subst ht0
            have h1 : (0 + 1 : Fin m) ≠ 0 := by
              intro h; have := congrArg Fin.val h
              simp only [zero_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero] at this; omega
            have ht1 : (1 : Fin m).1 = 1 := Fin.val_one' (by omega : 1 < m)
            simp only [↓reduceIte, hτ'0, zero_add, h1, ht1]
            exact Nat.mod_eq_of_lt (by omega)
          · have hne := hτ'_ne ht0
            have ht1 : 1 ≤ t.1 := Nat.pos_of_ne_zero fun h => ht0 (Fin.ext h)
            by_cases hlast : t.1 + 1 = m
            · have ht0' : t + 1 = 0 := Fin.ext (by
                simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero]
                rw [hlast, Nat.mod_self])
              simp only [ht0, hne, ↓reduceIte, ht0']
              rw [show 3 * t.1 + pad + 1 + 1 + 1 = 3 * m + pad by omega, Nat.mod_self]
            · have ht0' : t + 1 ≠ 0 := fun h => by
                have := congrArg Fin.val h
                simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero] at this
                rw [Nat.mod_eq_of_lt (by omega)] at this; omega
              have ht1' : (t + 1).1 = t.1 + 1 := by
                simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
                exact Nat.mod_eq_of_lt (by omega)
              simp only [ht0, hne, ↓reduceIte, ht0', ht1']
              rw [Nat.mod_eq_of_lt (by omega)]
              omega
        have hk' := congrArg eSplit hu
        have hk'' := congrArg eSplit hw
        have hku : eFin k = fromSplit (.vOut u) := by
          simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] using hk'
        have hkw : eFin (k + 1) = fromSplit (.vIn w) := by
          simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply] using hk''
        have hk1 : eFin (k + 1) = eFin k + 1 := by
          ext; simp only [eFin, Fin.coe_orderIso_apply, Fin.cast_val_eq_self, Fin.val_add,
            Fin.val_one' (by omega : 1 < Fintype.card (SplitV W v₀ pad)),
            Fin.val_one' (by omega : 1 < 3 * m + pad), hM_card]
        rw [hk1, hku] at hkw
        let tu := τ'.symm u
        have htu : τ' tu = u := τ'.apply_symm_apply u
        have hwrap_u := hwrap tu
        rw [htu] at hwrap_u
        have heq_in : eSplit.symm (fromSplit (.vIn (τ' (tu + 1)))) =
            eSplit.symm (fromSplit (.vIn w)) := by
          dsimp only [fromSplit] at hwrap_u hkw ⊢
          rw [← hwrap_u, hkw]
        simp only [Equiv.symm_apply_apply, SplitV.vIn.injEq] at heq_in
        refine ⟨t₀ + tu, ?_, ?_⟩
        · exact htu
        · rw [add_assoc]
          exact heq_in
      · exact absurd hbad hnot_rev
    · rintro ⟨t, rfl, rfl⟩
      let t' : Fin m := t - t₀
      have ht'1 : τ' t' = τ t := by simp only [τ', t', Equiv.coe_fn_mk, add_sub_cancel]
      have ht'2 : τ' (t' + 1) = τ (t + 1) := by
        simp only [τ', t', Equiv.coe_fn_mk, show t₀ + (t - t₀ + 1) = t + 1 by abel]
      let k : Fin (Fintype.card (SplitV W v₀ pad)) := eFin.symm (fromSplit (.vOut (τ' t')))
      refine ⟨k, ?_⟩
      have hsk : σ k = .vOut (τ t) := by
        rw [← ht'1]
        simp only [σ, k, Equiv.trans_apply, Equiv.apply_symm_apply, eSplit, Equiv.coe_fn_symm_mk,
          hleft]
      have hk1 : eFin (k + 1) = eFin k + 1 := by
        ext; simp only [eFin, Fin.coe_orderIso_apply, Fin.cast_val_eq_self, Fin.val_add,
          Fin.val_one' (by omega : 1 < Fintype.card (SplitV W v₀ pad)),
          Fin.val_one' (by omega : 1 < 3 * m + pad), hM_card]
      have hstep : eFin k + 1 = fromSplit (.vIn (τ' (t' + 1))) := by
        simp only [k, Equiv.apply_symm_apply]
        ext
        dsimp only [fromSplit, splitPos, splitMidLen]
        simp only [Fin.val_add, Fin.val_one' (by omega : 1 < 3 * m + pad),
          Fin.val_one' (by omega : 1 < m), Equiv.symm_apply_apply]
        by_cases ht0 : t' = 0
        · subst ht0
          have h1 : (0 + 1 : Fin m) ≠ 0 := by
            intro h; have := congrArg Fin.val h
            simp only [zero_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero] at this; omega
          simp only [↓reduceIte, hτ'0, zero_add, h1, Fin.val_one' (by omega : 1 < m)]
          exact Nat.mod_eq_of_lt (by omega)
        · have hne := hτ'_ne ht0
          have ht1 : 1 ≤ t'.1 := Nat.pos_of_ne_zero fun h => ht0 (Fin.ext h)
          by_cases hlast : t'.1 + 1 = m
          · have ht0' : t' + 1 = 0 := Fin.ext (by
              simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero]
              rw [hlast, Nat.mod_self])
            simp only [ht0, hne, ↓reduceIte, ht0']
            rw [show 3 * t'.1 + pad + 1 + 1 + 1 = 3 * m + pad by omega, Nat.mod_self]
          · have ht0' : t' + 1 ≠ 0 := fun h => by
              have := congrArg Fin.val h
              simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero] at this
              rw [Nat.mod_eq_of_lt (by omega)] at this; omega
            have ht1' : (t' + 1).1 = t'.1 + 1 := by
              simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
              exact Nat.mod_eq_of_lt (by omega)
            simp only [ht0, hne, ↓reduceIte, ht0', ht1']
            rw [Nat.mod_eq_of_lt (by omega)]
            omega
      have hsk1 : σ (k + 1) = .vIn (τ (t + 1)) := by
        rw [← ht'2]
        simp only [σ, Equiv.trans_apply, hk1, hstep, eSplit, Equiv.coe_fn_symm_mk, hleft]
      ext
      simp only [hsk, hsk1]

/-- Every undirected tour of `paddedSplitGraph v₀ pad adjD` (`|W| ≥ 2`) induces a directed
Hamiltonian tour of `(W, adjD)` matching the inter-gadget arcs. -/
theorem exists_dirTour_of_paddedSplitTour {W : Type*} [Fintype W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop) (hW : 2 ≤ Fintype.card W)
    {F : Finset ↥(⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet}
    (hF : IsSubgraphTour (paddedSplitGraph v₀ pad adjD) F) :
    ∃ τ : Fin (Fintype.card W) ≃ W, IsDirTour adjD τ ∧
      ∀ u w : W,
        (⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
          ∃ t : Fin (Fintype.card W), τ t = u ∧ τ (t + 1) = w) := by
  classical
  obtain ⟨⟨hM3, σ₀, rfl⟩, hsub⟩ := hF
  let M := Fintype.card (SplitV W v₀ pad)
  have hM_card : M = 3 * Fintype.card W + pad := card_splitV v₀ pad
  have hMpos : 0 < M := by omega
  have hadj0 : ∀ i : Fin M, (paddedSplitGraph v₀ pad adjD).Adj (σ₀ i) (σ₀ (i + 1)) := fun i =>
    (SimpleGraph.mem_edgeSet _).1 (hsub ⟨s(σ₀ i, σ₀ (i + 1)), tourEdge_mem_top_edgeSet hM3 σ₀ i⟩
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
  let mid0 : SplitV W v₀ pad := .vMid v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩
  let k0 : Fin M := σ₀.symm mid0
  have hk0_eq : σ₀ k0 = mid0 := σ₀.apply_symm_apply mid0
  have hnb0_plus : (paddedSplitGraph v₀ pad adjD).Adj mid0 (σ₀ (k0 + 1)) := by
    rw [← hk0_eq]; exact hadj0 k0
  have hnb0_minus : (paddedSplitGraph v₀ pad adjD).Adj mid0 (σ₀ (k0 - 1)) := by
    rw [← hk0_eq]
    have h := (hadj0 (k0 - 1)).symm
    rwa [show k0 - 1 + 1 = k0 by abel] at h
  have hmem_plus := (adj_vMid_iff v₀ pad adjD v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩ _).1 hnb0_plus
  have hmem_minus := (adj_vMid_iff v₀ pad adjD v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩ _).1 hnb0_minus
  have hne0 : σ₀ (k0 - 1) ≠ σ₀ (k0 + 1) :=
    fun h => adj_Fin_add_one_ne_sub_one hM3 k0 (σ₀.injective h)
  have hprev0 : midPrev v₀ pad v₀ ⟨0, splitMidLen_pos v₀ pad v₀⟩ = .vIn v₀ := by
    simp only [midPrev, ↓reduceDIte]
  obtain ⟨σ₁, htour₁, k₁, hk₁_eq, hk₁_prev⟩ :
      ∃ (σ₁ : Fin M ≃ SplitV W v₀ pad), tourEdgeSet σ₁ hM3 = tourEdgeSet σ₀ hM3 ∧
        ∃ k₁ : Fin M, σ₁ k₁ = mid0 ∧ σ₁ (k₁ - 1) = .vIn v₀ := by
    rcases hmem_minus with hm | hm
    · exact ⟨σ₀, rfl, k0, hk0_eq, hm.trans hprev0⟩
    · have hp : σ₀ (k0 + 1) = .vIn v₀ := by
        rcases hmem_plus with hp | hp
        · exact hp.trans hprev0
        · exfalso; exact hne0 (hm.trans hp.symm)
      let σ₁ : Fin M ≃ SplitV W v₀ pad :=
        { toFun := fun i => σ₀ (-i)
          invFun := fun v => -(σ₀.symm v)
          left_inv := fun i => by simp only [Equiv.symm_apply_apply, neg_neg]
          right_inv := fun v => by simp only [neg_neg, Equiv.apply_symm_apply] }
      refine ⟨σ₁, tourEdgeSet_reverse σ₀ hM3, -k0, ?_, ?_⟩
      · simpa only [σ₁, Equiv.coe_fn_mk, neg_neg] using hk0_eq
      · simp only [σ₁, Equiv.coe_fn_mk, show -(-k0 - 1) = k0 + 1 by abel, hp]
  let σ : Fin M ≃ SplitV W v₀ pad :=
    { toFun := fun i => σ₁ ((k₁ - 1) + i)
      invFun := fun v => σ₁.symm v - (k₁ - 1)
      left_inv := fun i => by simp only [Equiv.symm_apply_apply, add_sub_cancel_left]
      right_inv := fun v => by simp only [add_sub_cancel, Equiv.apply_symm_apply] }
  have htour : tourEdgeSet σ hM3 = tourEdgeSet σ₀ hM3 := by
    simpa only [σ] using (tourEdgeSet_shift σ₁ hM3 (k₁ - 1)).trans htour₁
  have hσ0 : σ 0 = .vIn v₀ := by
    simpa only [σ, Equiv.coe_fn_mk, add_zero] using hk₁_prev
  have hσ1 : σ 1 = mid0 := by
    simpa only [σ, Equiv.coe_fn_mk, sub_add_cancel] using hk₁_eq
  have hadj : ∀ i : Fin M, (paddedSplitGraph v₀ pad adjD).Adj (σ i) (σ (i + 1)) := fun i =>
    (SimpleGraph.mem_edgeSet _).1 (hsub ⟨s(σ i, σ (i + 1)), tourEdge_mem_top_edgeSet hM3 σ i⟩
      (htour ▸ Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩))
  let finOf : ℕ → Fin M := fun n => ⟨n % M, Nat.mod_lt _ hMpos⟩
  let stepNat : ℕ → SplitV W v₀ pad := fun n => σ (finOf n)
  have hfin_succ : ∀ n : ℕ, finOf (n + 1) = finOf n + 1 := fun n => by
    ext
    simp only [finOf, Fin.val_add, Fin.val_one' (by omega : 1 < M)]
    exact Nat.add_mod n 1 M
  have hstep_adj : ∀ n : ℕ, (paddedSplitGraph v₀ pad adjD).Adj (stepNat n) (stepNat (n + 1)) :=
    fun n => by
    dsimp only [stepNat]
    rw [hfin_succ n]
    exact hadj (finOf n)
  have hstep_ne2 : ∀ n : ℕ, stepNat (n + 2) ≠ stepNat n := fun n h => by
    have h2 : finOf (n + 2) = finOf n + 2 := by
      rw [show n + 2 = (n + 1) + 1 by rfl, hfin_succ, hfin_succ, add_assoc, one_add_one_eq_two]
    have hfeq : finOf n + 2 = finOf n := by
      rw [← h2]; exact σ.injective h
    have h0 : (2 : Fin M) = 0 := add_left_eq_self.1 (add_comm (finOf n) 2 ▸ hfeq)
    have hv := congrArg Fin.val h0
    simp only [Fin.val_two' (by omega : 2 < M), Fin.val_zero] at hv
    omega
  have hblock_walk : ∀ (t : ℕ) (w : W),
      stepNat t = .vIn w → stepNat (t + 1) = .vMid w ⟨0, splitMidLen_pos v₀ pad w⟩ →
        (∀ k (hk : k < splitMidLen v₀ pad w), stepNat (t + 1 + k) = .vMid w ⟨k, hk⟩) ∧
        stepNat (t + 1 + splitMidLen v₀ pad w) = .vOut w ∧
        ∃ w', adjD w w' ∧ stepNat (t + 2 + splitMidLen v₀ pad w) = .vIn w' ∧
          stepNat (t + 3 + splitMidLen v₀ pad w) = .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩ := by
    intro t w ht0 ht1
    have hmid : ∀ k (hk : k < splitMidLen v₀ pad w),
        stepNat (t + 1 + k) = .vMid w ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero => intro _; exact ht1
      | succ k ih =>
          intro hk1
          have hk : k < splitMidLen v₀ pad w := by omega
          have hcur := ih hk
          have hnb := hstep_adj (t + 1 + k)
          rw [hcur] at hnb
          rcases (adj_vMid_iff v₀ pad adjD w ⟨k, hk⟩ _).1 hnb with hprev | hnext
          · exfalso
            have hprev_eq : stepNat (t + k) = midPrev v₀ pad w ⟨k, hk⟩ := by
              cases k with
              | zero => simpa only [add_zero, midPrev, ↓reduceDIte] using ht0
              | succ k' =>
                  have ih' := ih (by omega)
                  simpa only [midPrev, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
                    Nat.add_sub_cancel, add_assoc] using ih'
            exact hstep_ne2 (t + k) (by simpa only [add_assoc] using hprev.trans hprev_eq.symm)
          · dsimp only [midNext] at hnext
            rw [dif_neg (by omega)] at hnext
            simpa only [add_assoc] using hnext
    have hout : stepNat (t + 1 + splitMidLen v₀ pad w) = .vOut w := by
      let k := splitMidLen v₀ pad w - 1
      have hk : k < splitMidLen v₀ pad w := by have := splitMidLen_pos v₀ pad w; omega
      have hcur := hmid k hk
      have hnb := hstep_adj (t + 1 + k)
      rw [hcur] at hnb
      have hk_last : k + 1 = splitMidLen v₀ pad w := by have := splitMidLen_pos v₀ pad w; omega
      rcases (adj_vMid_iff v₀ pad adjD w ⟨k, hk⟩ _).1 hnb with hprev | hnext
      · exfalso
        have hprev_eq : stepNat (t + k) = midPrev v₀ pad w ⟨k, hk⟩ := by
          cases k with
          | zero => simpa only [add_zero, midPrev, ↓reduceDIte] using ht0
          | succ k' =>
              have ih' := hmid k' (by omega)
              simpa only [midPrev, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
                Nat.add_sub_cancel, add_assoc] using ih'
        have heq := hprev.trans hprev_eq.symm
        rw [show t + 1 + k + 1 = t + k + 2 by omega] at heq
        exact hstep_ne2 (t + k) heq
      · dsimp only [midNext] at hnext
        rw [dif_pos hk_last] at hnext
        rwa [show t + 1 + splitMidLen v₀ pad w = t + 1 + k + 1 by omega]
    have hnb_out := hstep_adj (t + 1 + splitMidLen v₀ pad w)
    rw [hout] at hnb_out
    have hne_out : stepNat (t + 2 + splitMidLen v₀ pad w) ≠
        .vMid w ⟨splitMidLen v₀ pad w - 1, by have := splitMidLen_pos v₀ pad w; omega⟩ := by
      rw [show t + 2 + splitMidLen v₀ pad w = (t + splitMidLen v₀ pad w) + 2 by omega,
        ← hmid (splitMidLen v₀ pad w - 1) (by have := splitMidLen_pos v₀ pad w; omega)]
      rw [show t + 1 + (splitMidLen v₀ pad w - 1) = t + splitMidLen v₀ pad w by
        have := splitMidLen_pos v₀ pad w; omega]
      exact hstep_ne2 _
    have hex_in : ∃ w', adjD w w' ∧ stepNat (t + 2 + splitMidLen v₀ pad w) = .vIn w' := by
      cases hx : stepNat (t + 2 + splitMidLen v₀ pad w) with
      | vIn w' =>
          rw [hx] at hnb_out
          exact ⟨w', hnb_out, rfl⟩
      | vMid u k' =>
          exfalso
          rw [hx] at hnb_out
          dsimp only [paddedSplitGraph, splitAdjRel] at hnb_out
          rcases hnb_out with ⟨rfl, hk'⟩
          have hk'eq : (⟨splitMidLen v₀ pad u - 1, by
              have := splitMidLen_pos v₀ pad u; omega⟩ : Fin (splitMidLen v₀ pad u)) = k' :=
            Fin.ext (by omega)
          rw [← hx, hk'eq] at hne_out
          exact hne_out rfl
      | vOut u =>
          exfalso
          rw [hx] at hnb_out
          exact hnb_out
    obtain ⟨w', hww', hw'⟩ := hex_in
    have hw'1 : stepNat (t + 3 + splitMidLen v₀ pad w) =
        .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩ := by
      let m0 : SplitV W v₀ pad := .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩
      let r := σ.symm m0
      have hr : σ r = m0 := σ.apply_symm_apply m0
      have hr_plus := (adj_vMid_iff v₀ pad adjD w' ⟨0, splitMidLen_pos v₀ pad w'⟩ _).1
        (by rw [← hr]; exact hadj r)
      have hr_minus := (adj_vMid_iff v₀ pad adjD w' ⟨0, splitMidLen_pos v₀ pad w'⟩ _).1
        (by rw [← hr]; have h := (hadj (r - 1)).symm; rwa [show r - 1 + 1 = r by abel] at h)
      have hne_r : σ (r - 1) ≠ σ (r + 1) :=
        fun h => adj_Fin_add_one_ne_sub_one hM3 r (σ.injective h)
      have hprev_w' : midPrev v₀ pad w' ⟨0, splitMidLen_pos v₀ pad w'⟩ = .vIn w' := by
        simp only [midPrev, ↓reduceDIte]
      have hid : finOf (t + 2 + splitMidLen v₀ pad w) = r - 1 ∨
          finOf (t + 2 + splitMidLen v₀ pad w) = r + 1 := by
        rcases hr_minus with hm | hm
        · left; exact σ.injective (hw'.trans (hm.trans hprev_w').symm)
        · rcases hr_plus with hp | hp
          · right; exact σ.injective (hw'.trans (hp.trans hprev_w').symm)
          · exfalso; exact hne_r (hm.trans hp.symm)
      rcases hid with hid | hid
      · dsimp only [stepNat]
        rw [show t + 3 + splitMidLen v₀ pad w = (t + 2 + splitMidLen v₀ pad w) + 1 by omega,
          hfin_succ, hid, sub_add_cancel]
        exact hr
      · exfalso
        have hbad : stepNat (t + 1 + splitMidLen v₀ pad w) = m0 := by
          dsimp only [stepNat]
          have hadd : finOf (t + 1 + splitMidLen v₀ pad w) + 1 =
              finOf (t + 2 + splitMidLen v₀ pad w) := by
            rw [← hfin_succ]; congr 1; omega
          have hsub : finOf (t + 1 + splitMidLen v₀ pad w) = r := by
            rw [hid] at hadd
            calc finOf (t + 1 + splitMidLen v₀ pad w)
                = finOf (t + 1 + splitMidLen v₀ pad w) + 1 - 1 := (add_sub_cancel_right _ _).symm
              _ = r + 1 - 1 := by rw [hadd]
              _ = r := add_sub_cancel_right _ _
          rw [hsub, hr]
        rw [hout] at hbad
        cases hbad
    exact ⟨hmid, hout, w', hww', hw', hw'1⟩
  let BlockState := {p : ℕ × W //
    stepNat p.1 = .vIn p.2 ∧ stepNat (p.1 + 1) = .vMid p.2 ⟨0, splitMidLen_pos v₀ pad p.2⟩}
  let initBlock : BlockState :=
    ⟨(0, v₀), by simpa only [stepNat, finOf, Nat.zero_mod, Fin.mk_zero] using hσ0,
      by simpa only [stepNat, finOf, zero_add, Nat.mod_eq_of_lt (by omega : 1 < M)] using hσ1⟩
  let nextBlock (s : BlockState) :
      {s' : BlockState // s'.1.1 = s.1.1 + 2 + splitMidLen v₀ pad s.1.2 ∧ adjD s.1.2 s'.1.2} :=
    let h := hblock_walk s.1.1 s.1.2 s.2.1 s.2.2
    let w' := Classical.choose h.2.2
    let hw' := Classical.choose_spec h.2.2
    ⟨⟨(s.1.1 + 2 + splitMidLen v₀ pad s.1.2, w'), hw'.2.1, hw'.2.2⟩, rfl, hw'.1⟩
  let seq : ℕ → BlockState := Nat.rec initBlock fun _ s => (nextBlock s).1
  let pos : ℕ → ℕ := fun r => (seq r).1.1
  let vert : ℕ → W := fun r => (seq r).1.2
  have hseq_step : ∀ r, pos (r + 1) = pos r + 2 + splitMidLen v₀ pad (vert r) ∧
      adjD (vert r) (vert (r + 1)) := fun r => (nextBlock (seq r)).2
  have hsum_pos : ∀ k, pos k = ∑ r ∈ Finset.range k, (2 + splitMidLen v₀ pad (vert r)) := by
    intro k
    induction k with
    | zero => simp only [pos, seq, initBlock, Finset.range_zero, Finset.sum_empty]
    | succ k ih =>
        rw [Finset.sum_range_succ, ← ih, (hseq_step k).1]
  have htotal_sum : ∑ w : W, (2 + splitMidLen v₀ pad w) = M := by
    rw [hM_card, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      sum_splitMidLen]
    ring
  have hwalk_lt : ∀ k, k ≤ Fintype.card W →
      (∀ r₁ r₂, r₁ < r₂ → r₂ < k → vert r₁ ≠ vert r₂) ∧
      (∀ r, r < k → pos r < M) := by
    intro k hk
    induction k with
    | zero =>
        exact ⟨fun _ _ _ h => absurd h (Nat.not_lt_zero _),
          fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ k ih =>
        obtain ⟨hinj, hlt⟩ := ih (Nat.le_of_succ_le hk)
        have hpos_k : pos k < M := by
          have him_inj : Set.InjOn vert (Finset.range k) := fun r₁ hr₁ r₂ hr₂ heq => by
            rw [Finset.coe_range, Set.mem_Iio] at hr₁ hr₂
            rcases lt_trichotomy r₁ r₂ with h | rfl | h
            · exact absurd heq (hinj r₁ r₂ h hr₂)
            · rfl
            · exact absurd heq.symm (hinj r₂ r₁ h hr₁)
          rw [hsum_pos k, ← Finset.sum_image (g := vert) him_inj]
          have hsub_ne : (Finset.range k).image vert ≠ Finset.univ := by
            intro heq
            have hcard := congrArg Finset.card heq
            rw [Finset.card_image_of_injOn him_inj, Finset.card_range, Finset.card_univ] at hcard
            omega
          have hex : ∃ w_out : W, w_out ∉ (Finset.range k).image vert := by
            by_contra! h
            exact hsub_ne (Finset.eq_univ_iff_forall.2 h)
          obtain ⟨w_out, hw_out⟩ := hex
          have hsub_erase : (Finset.range k).image vert ⊆ Finset.univ.erase w_out :=
            fun w hw => Finset.mem_erase.2 ⟨fun hweq => hw_out (hweq ▸ hw), Finset.mem_univ w⟩
          have hsum_le := Finset.sum_le_sum_of_subset hsub_erase
          have herase := Finset.add_sum_erase Finset.univ (fun w => 2 + splitMidLen v₀ pad w)
            (Finset.mem_univ w_out)
          have hpos_out := splitMidLen_pos v₀ pad w_out
          omega
        refine ⟨fun r₁ r₂ hr12 hr2 => ?_, fun r hr => ?_⟩
        · by_cases hk2 : r₂ = k
          · subst hk2
            have hr1_lt : pos r₁ < M := hlt r₁ hr12
            have hfin1 : finOf (pos r₁) = ⟨pos r₁, hr1_lt⟩ := Fin.ext (Nat.mod_eq_of_lt hr1_lt)
            have hfin2 : finOf (pos r₂) = ⟨pos r₂, hpos_k⟩ := Fin.ext (Nat.mod_eq_of_lt hpos_k)
            have hneq_fin : (⟨pos r₁, hr1_lt⟩ : Fin M) ≠ ⟨pos r₂, hpos_k⟩ := fun h => by
              have hval := congrArg Fin.val h
              have hmono : ∀ a b : ℕ, a < b → pos a < pos b := fun a b hab => by
                induction b with
                | zero => exact absurd hab (Nat.not_lt_zero _)
                | succ b ih =>
                    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with hlt' | rfl
                    · exact lt_trans (ih hlt') (by rw [(hseq_step b).1]; omega)
                    · rw [(hseq_step a).1]; omega
              have := hmono r₁ r₂ hr12
              omega
            intro heq
            apply hneq_fin
            apply σ.injective
            rw [← hfin1, ← hfin2]
            change stepNat (pos r₁) = stepNat (pos r₂)
            rw [(seq r₁).2.1, (seq r₂).2.1, heq]
          · exact hinj r₁ r₂ hr12 (by omega)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr' | rfl
          · exact hlt r hr'
          · exact hpos_k
  obtain ⟨hvert_inj, hpos_lt⟩ := hwalk_lt (Fintype.card W) le_rfl
  let m := Fintype.card W
  let τFun : Fin m → W := fun t => vert t.1
  have hτ_inj : Function.Injective τFun := fun t₁ t₂ heq => by
    rcases lt_trichotomy t₁.1 t₂.1 with h | h | h
    · exact absurd heq (hvert_inj t₁.1 t₂.1 h t₂.2)
    · exact Fin.ext h
    · exact absurd heq.symm (hvert_inj t₂.1 t₁.1 h t₁.2)
  let τ : Fin m ≃ W := Equiv.ofBijective τFun
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨hτ_inj, Fintype.card_fin m⟩)
  have him_univ : (Finset.range m).image vert = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn (fun r₁ hr₁ r₂ hr₂ heq => by
      rw [Finset.coe_range, Set.mem_Iio] at hr₁ hr₂
      exact congrArg Fin.val (hτ_inj (t₁ := ⟨r₁, hr₁⟩) (t₂ := ⟨r₂, hr₂⟩) heq)),
      Finset.card_range, Finset.card_univ]
  have hpos_m : pos m = M := by
    rw [hsum_pos m, ← Finset.sum_image (g := vert) (fun r₁ hr₁ r₂ hr₂ heq => by
      rw [Finset.coe_range, Set.mem_Iio] at hr₁ hr₂
      exact congrArg Fin.val (hτ_inj (t₁ := ⟨r₁, hr₁⟩) (t₂ := ⟨r₂, hr₂⟩) heq)),
      him_univ, htotal_sum]
  have hvert_m : vert m = vert 0 := by
    have hstep_m : stepNat (pos m) = stepNat 0 := by
      simp only [stepNat, hpos_m, finOf, Nat.mod_self, Nat.zero_mod]
    have hv := (seq m).2.1.symm.trans (hstep_m.trans (seq 0).2.1)
    cases hv
    rfl
  have hdir : IsDirTour adjD τ := fun t => by
    dsimp only [τ, Equiv.coe_fn_mk, τFun]
    by_cases hlast : t.1 + 1 = m
    · have ht0 : t + 1 = 0 := Fin.ext (by
        simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero]
        rw [hlast, Nat.mod_self])
      rw [ht0, Fin.val_zero, ← hvert_m, ← hlast]
      exact (hseq_step t.1).2
    · have ht1 : (t + 1).1 = t.1 + 1 := by
        simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [ht1]
      exact (hseq_step t.1).2
  refine ⟨τ, hdir, fun u w => ?_⟩
  rw [← htour]
  simp only [tourEdgeSet, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hfind : ∀ k ≤ m, i.1 < pos k → ∃ r, r < k ∧ pos r ≤ i.1 ∧ i.1 < pos (r + 1) := by
      intro k
      induction k with
      | zero =>
          intro _ hlt0
          have h0 : pos 0 = 0 := by simp only [pos, seq, initBlock]
          omega
      | succ k ih =>
          intro hk hlt
          by_cases hk' : i.1 < pos k
          · obtain ⟨r, hr, hlo, hhi⟩ := ih (Nat.le_of_succ_le hk) hk'
            exact ⟨r, by omega, hlo, hhi⟩
          · exact ⟨k, Nat.lt_succ_self k, by omega, hlt⟩
    obtain ⟨r, hr, hlo, hhi⟩ := hfind m le_rfl (hpos_m ▸ i.2)
    have hfin_i : i = finOf i.1 := Fin.ext (Nat.mod_eq_of_lt i.2).symm
    have hfin_i1 : i + 1 = finOf (i.1 + 1) := by rw [hfin_i, hfin_succ]
    have hσi : σ i = stepNat i.1 := by dsimp only [stepNat]; rw [← hfin_i]
    have hσi1 : σ (i + 1) = stepNat (i.1 + 1) := by dsimp only [stepNat]; rw [← hfin_i1]
    rw [hσi, hσi1] at hi
    have hwalk := hblock_walk (pos r) (vert r) (seq r).2.1 (seq r).2.2
    have hstep_pos : pos (r + 1) = pos r + 2 + splitMidLen v₀ pad (vert r) := (hseq_step r).1
    by_cases h0 : i.1 = pos r
    · exfalso
      have hs1 : stepNat i.1 = .vIn (vert r) := by rw [h0]; exact (seq r).2.1
      have hs2 : stepNat (i.1 + 1) = .vMid (vert r) ⟨0, splitMidLen_pos v₀ pad _⟩ := by
        rw [h0]; exact (seq r).2.2
      rw [hs1, hs2, Sym2.eq_iff] at hi
      rcases hi with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h
    · by_cases hmid : i.1 < pos r + splitMidLen v₀ pad (vert r)
      · exfalso
        let k₁ := i.1 - (pos r + 1)
        have hk₁ : k₁ < splitMidLen v₀ pad (vert r) := by omega
        have hk₂ : k₁ + 1 < splitMidLen v₀ pad (vert r) := by omega
        have hs1 : stepNat i.1 = .vMid (vert r) ⟨k₁, hk₁⟩ := by
          rw [show i.1 = pos r + 1 + k₁ by omega]; exact hwalk.1 k₁ hk₁
        have hs2 : stepNat (i.1 + 1) = .vMid (vert r) ⟨k₁ + 1, hk₂⟩ := by
          rw [show i.1 + 1 = pos r + 1 + (k₁ + 1) by omega]; exact hwalk.1 (k₁ + 1) hk₂
        rw [hs1, hs2, Sym2.eq_iff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
      · by_cases hout : i.1 = pos r + splitMidLen v₀ pad (vert r)
        · exfalso
          let k₁ := splitMidLen v₀ pad (vert r) - 1
          have hk₁ : k₁ < splitMidLen v₀ pad (vert r) := by
            have := splitMidLen_pos v₀ pad (vert r); omega
          have hs1 : stepNat i.1 = .vMid (vert r) ⟨k₁, hk₁⟩ := by
            rw [show i.1 = pos r + 1 + k₁ by omega]; exact hwalk.1 k₁ hk₁
          have hs2 : stepNat (i.1 + 1) = .vOut (vert r) := by
            rw [show i.1 + 1 = pos r + 1 + splitMidLen v₀ pad (vert r) by omega]; exact hwalk.2.1
          rw [hs1, hs2, Sym2.eq_iff] at hi
          rcases hi with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
        · have hlast : i.1 = pos r + 1 + splitMidLen v₀ pad (vert r) := by omega
          have hs1 : stepNat i.1 = .vOut (vert r) := by rw [hlast]; exact hwalk.2.1
          have hs2 : stepNat (i.1 + 1) = .vIn (vert (r + 1)) := by
            rw [show i.1 + 1 = pos (r + 1) by omega]
            exact (seq (r + 1)).2.1
          rw [hs1, hs2, Sym2.eq_iff] at hi
          rcases hi with ⟨hu, hw⟩ | ⟨hbad, _⟩
          · refine ⟨⟨r, hr⟩, ?_, ?_⟩
            · dsimp only [τ, Equiv.coe_fn_mk, τFun]; cases hu; rfl
            · dsimp only [τ, Equiv.coe_fn_mk, τFun]
              by_cases hr1 : r + 1 = m
              · have hwrap : (⟨r, hr⟩ + 1 : Fin m) = 0 := Fin.ext (by
                  simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero]
                  rw [hr1, Nat.mod_self])
                rw [hwrap, Fin.val_zero, ← hvert_m, ← hr1]
                cases hw; rfl
              · have hnext : (⟨r, hr⟩ + 1 : Fin m).1 = r + 1 := by
                  simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hnext]
                cases hw; rfl
          · cases hbad
  · rintro ⟨t, rfl, rfl⟩
    let i : Fin M := ⟨pos t.1 + 1 + splitMidLen v₀ pad (vert t.1), by
      have := hpos_lt t.1 t.2
      have hstep := (hseq_step t.1).1
      by_cases hlast : t.1 + 1 = m
      · omega
      · have := hpos_lt (t.1 + 1) (by omega); omega⟩
    refine ⟨i, ?_⟩
    have hfin_i : i = finOf i.1 := Fin.ext (Nat.mod_eq_of_lt i.2).symm
    have hfin_i1 : i + 1 = finOf (i.1 + 1) := by rw [hfin_i, hfin_succ]
    have hσi : σ i = .vOut (τ t) := by
      dsimp only [τ, Equiv.coe_fn_mk, τFun]
      rw [hfin_i]
      exact (hblock_walk (pos t.1) (vert t.1) (seq t.1).2.1 (seq t.1).2.2).2.1
    have hσi1 : σ (i + 1) = .vIn (τ (t + 1)) := by
      rw [hfin_i1]
      change stepNat (i.1 + 1) = .vIn (τ (t + 1))
      have hipos : i.1 + 1 = pos (t.1 + 1) := by dsimp only [i]; rw [(hseq_step t.1).1]; omega
      rw [hipos]
      dsimp only [τ, Equiv.coe_fn_mk, τFun]
      by_cases hlast : t.1 + 1 = m
      · have hwrap : t + 1 = 0 := Fin.ext (by
          simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m), Fin.val_zero]
          rw [hlast, Nat.mod_self])
        rw [hwrap, Fin.val_zero, ← hvert_m, ← hlast]
        exact (seq (t.1 + 1)).2.1
      · have hnext : (t + 1).1 = t.1 + 1 := by
          simp only [Fin.val_add, Fin.val_one' (by omega : 1 < m)]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hnext]
        exact (seq (t.1 + 1)).2.1
    ext
    simp only [hσi, hσi1]

end SplitGraph
