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

* `card_splitV`: `Fintype.card (SplitV W v₀ pad) = 3 * Fintype.card W + pad`.
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
theorem tourEdge_mem_top_edgeSet {V : Type*} [Fintype V]
    (hV : 3 ≤ Fintype.card V) (σ : Fin (Fintype.card V) ≃ V) (i : Fin (Fintype.card V)) :
    s(σ i, σ (i + ⟨1, by omega⟩)) ∈ (⊤ : SimpleGraph V).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj, ne_eq, EmbeddingLike.apply_eq_iff_eq]
  intro h
  have hval := congrArg Fin.val h
  rw [Fin.val_add] at hval
  dsimp only at hval
  by_cases hwrap : i.1 + 1 = Fintype.card V
  · rw [hwrap, Nat.mod_self] at hval
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hval
    omega

/-- The edge set in `K_V` traced by the cyclic ordering `σ : Fin |V| ≃ V`. -/
@[expose] def tourEdgeSet {V : Type*} [Fintype V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) :
    Finset ↥(⊤ : SimpleGraph V).edgeSet :=
  Finset.univ.image fun i => ⟨s(σ i, σ (i + ⟨1, by omega⟩)), tourEdge_mem_top_edgeSet hV σ i⟩

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
    have hterm : ∀ e : ↥(⊤ : SimpleGraph V).edgeSet,
        (if e.1 ∈ G.edgeSet then (0 : K) else -1) * (if e ∈ F then 1 else 0) =
          -(if e ∈ (F.filter fun e => e.1 ∉ G.edgeSet) then (1 : K) else 0) := fun e => by
      by_cases hg : e.1 ∈ G.edgeSet <;> by_cases hf : e ∈ F <;>
        simp only [Finset.mem_filter, hg, hf, not_true_eq_false, not_false_eq_true, and_self,
          and_false, false_and, ↓reduceIte, mul_one, mul_zero, neg_zero]
    simp only [hterm, Finset.sum_neg_distrib, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
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
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists]
  constructor
  · rintro ⟨F, hF, hFx, rfl⟩
    rw [htight ⟨F, hF⟩] at hFx
    exact ⟨F, hFx, rfl⟩
  · rintro ⟨F, hFG, rfl⟩
    refine ⟨F, hFG.1, ?_, rfl⟩
    exact (htight ⟨F, hFG.1⟩).2 hFG

end TSPPolytope

section SplitGraph

/-- Middle chain length of `w` in `SplitV W v₀ pad`: `pad + 1` at `v₀` and `1` elsewhere. -/
@[expose] def splitMidLen {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) : ℕ :=
  if w = v₀ then pad + 1 else 1

/-- Vertices of the `3`-split undirected graph of a digraph on `W`, with `pad` extra middle
nodes inserted at `v₀` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 11, Step (iii)]. -/
inductive SplitV (W : Type*) [DecidableEq W] (v₀ : W) (pad : ℕ) : Type _
  | vIn (w : W)
  | vMid (w : W) (k : Fin (splitMidLen v₀ pad w))
  | vOut (w : W)

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

@[no_expose] instance {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    DecidableEq (SplitV W v₀ pad) :=
  (splitVEquiv v₀ pad).decidableEq

@[no_expose] instance {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Fintype (SplitV W v₀ pad) :=
  Fintype.ofEquiv _ (splitVEquiv v₀ pad).symm

instance {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) :
    Nonempty (SplitV W v₀ pad) :=
  ⟨.vIn v₀⟩

private theorem sum_splitMidLen {W : Type*} [Fintype W] [DecidableEq W] (v₀ : W) (pad : ℕ) :
    ∑ w : W, splitMidLen v₀ pad w = Fintype.card W + pad := by
  simp only [splitMidLen]
  have hsplit : (Finset.univ : Finset W).sum (fun w => if w = v₀ then pad + 1 else 1) =
      ∑ w : W, (1 + if w = v₀ then pad else 0) :=
    Finset.sum_congr rfl fun w _ => by
      by_cases h : w = v₀
      · simp only [h, ↓reduceIte]; omega
      · simp only [h, ↓reduceIte, add_zero]
  rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

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
  symm := ⟨fun u v h => by
    cases u <;> cases v <;> simp only [splitAdjRel] at h ⊢ <;> tauto⟩
  loopless := ⟨fun u h => by
    cases u <;> simp only [splitAdjRel] at h
    omega⟩

private theorem splitMidLen_pos {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W) :
    0 < splitMidLen v₀ pad w := by
  dsimp only [splitMidLen]
  split_ifs <;> omega

/-- `τ : Fin |W| ≃ W` is a directed Hamiltonian tour of `(W, adjD)`. -/
@[expose] def IsDirTour {W : Type*} [Fintype W] [Nonempty W] (adjD : W → W → Prop)
    (τ : Fin (Fintype.card W) ≃ W) : Prop :=
  ∀ t : Fin (Fintype.card W), adjD (τ t) (τ (t + 1))

/-- Every edge between `vOut u` and `vIn w` belongs to the complete graph on `SplitV W v₀ pad`. -/
theorem splitV_top_edge_vOut_vIn {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (u w : W) :
    s(SplitV.vOut u, SplitV.vIn w) ∈ (⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
  intro h
  cases h

/-- Every directed Hamiltonian tour of `(W, adjD)` lifts to a subgraph tour of
`paddedSplitGraph v₀ pad adjD` matching the inter-gadget arcs. -/
theorem paddedSplitTour_of_dirTour {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
    (v₀ : W) (pad : ℕ) (adjD : W → W → Prop) (hW : 2 ≤ Fintype.card W)
    (τ : Fin (Fintype.card W) ≃ W) (hτ : IsDirTour adjD τ) :
    ∃ F : Finset ↥(⊤ : SimpleGraph (SplitV W v₀ pad)).edgeSet,
      IsSubgraphTour (paddedSplitGraph v₀ pad adjD) F ∧
      ∀ u w : W,
        (⟨s(SplitV.vOut u, SplitV.vIn w), splitV_top_edge_vOut_vIn v₀ pad u w⟩ ∈ F ↔
          ∃ t : Fin (Fintype.card W), τ t = u ∧ τ (t + 1) = w) := by
  classical
  let m := Fintype.card W
  have : NeZero m := ⟨by omega⟩
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
  have h1_m : (1 : Fin m).1 = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h1_pad : (1 : Fin (3 * m + pad)).1 = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h1_M : (1 : Fin (Fintype.card (SplitV W v₀ pad))).1 = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
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
        dsimp only [splitPos, splitMidLen]
        have hlt : (τ'.symm w).1 < m := (τ'.symm w).2
        by_cases hw : w = v₀
        · subst hw
          simp only [hτ'_symm0, ↓reduceIte]; omega
        · have h : τ'.symm w ≠ 0 := fun he => hw (τ'.symm.injective (he.trans hτ'_symm0.symm))
          simp only [h, hw, ↓reduceIte]; omega⟩
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
          simp only [ht, ↓reduceIte]
          have hj : 3 * (τ'.symm w).1 + pad - (pad + 3) = 3 * ((τ'.symm w).1 - 1) := by omega
          have h0 : ¬ 3 * (τ'.symm w).1 + pad = 0 := by omega
          have h1 : ¬ 3 * (τ'.symm w).1 + pad < pad + 2 := by omega
          have h2 : ¬ 3 * (τ'.symm w).1 + pad = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte, hj, Nat.mul_div_right _ (by omega : 0 < 3),
            Nat.mul_mod_right, ↓reduceIte]
          congr 1
          have hlt : (τ'.symm w).1 < m := (τ'.symm w).2
          have hfin : (⟨(τ'.symm w).1 - 1 + 1, by omega⟩ : Fin m) = τ'.symm w :=
            Fin.ext (by dsimp only; omega)
          rw [hfin, Equiv.apply_symm_apply]
    | vMid w k =>
        by_cases hw : w = v₀
        · subst hw
          have hk := k.2; simp only [splitMidLen, ↓reduceIte] at hk
          simp only [fromSplit, hpos_v0, toSplit]
          have h0 : ¬ 0 + 1 + k.1 = 0 := by omega
          have h1 : 0 + 1 + k.1 < pad + 2 := by omega
          simp only [h0, h1, ↓reduceDIte, Nat.add_sub_cancel_left]
        · have ht : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have ht1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
          have hk := k.2; simp only [splitMidLen, hw, ↓reduceIte] at hk
          have hk0 : k.1 = 0 := by omega
          have hlt : (τ'.symm w).1 < m := (τ'.symm w).2
          have hval : (fromSplit (.vMid w k)).1 = 3 * (τ'.symm w).1 + pad + 1 := by
            simp only [fromSplit, splitPos, ht, ↓reduceIte, hk0, add_zero]
          dsimp only [toSplit]
          split_ifs with h0 h1 h2 hmod0 hmod1
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · exfalso; omega
          · have hfin : (⟨((fromSplit (.vMid w k)).1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) =
                τ'.symm w := Fin.ext (by dsimp only; omega)
            have hmid_eq : ∀ u, u = w → ∀ a : Fin (splitMidLen v₀ pad u), a.1 = 0 →
                SplitV.vMid u a = SplitV.vMid w k := fun u hu a ha => by
              subst hu; congr 1; exact Fin.ext (ha.trans hk0.symm)
            exact hmid_eq _ (by rw [hfin, Equiv.apply_symm_apply]) _ rfl
          · exfalso; omega
    | vOut w =>
        by_cases hw : w = v₀
        · rw [hw]
          have hval : (fromSplit (.vOut v₀)).1 = pad + 2 := by
            simp only [fromSplit, hpos_v0, splitMidLen, ↓reduceIte]; omega
          dsimp only [toSplit]
          split_ifs with h0 h1 <;> first | rfl | omega
        · have ht : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have ht1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => ht (Fin.ext h)
          simp only [fromSplit, splitPos, splitMidLen, toSplit, ht, hw, ↓reduceIte]
          have hj : 3 * (τ'.symm w).1 + pad + 1 + 1 - (pad + 3) =
              3 * ((τ'.symm w).1 - 1) + 2 := by omega
          have h0 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 = 0 := by omega
          have h1 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 < pad + 2 := by omega
          have h2 : ¬ 3 * (τ'.symm w).1 + pad + 1 + 1 = pad + 2 := by omega
          simp only [h0, h1, h2, ↓reduceDIte, hj]
          have hdiv : (3 * ((τ'.symm w).1 - 1) + 2) / 3 = (τ'.symm w).1 - 1 := by omega
          have hmod : (3 * ((τ'.symm w).1 - 1) + 2) % 3 = 2 := by omega
          simp only [hmod, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, hdiv]
          have hlt : (τ'.symm w).1 < m := (τ'.symm w).2
          have hfin : (⟨(τ'.symm w).1 - 1 + 1, by omega⟩ : Fin m) = τ'.symm w :=
            Fin.ext (by dsimp only; omega)
          rw [hfin, Equiv.apply_symm_apply]
  have hright : ∀ i, fromSplit (toSplit i) = i := fun i => by
    have hi : i.1 < 3 * m + pad := i.2
    dsimp only [toSplit]
    split_ifs with h0 h1 h2 hmod0 hmod1
    · ext; simp only [fromSplit, hpos_v0]; exact h0.symm
    · ext; simp only [fromSplit, hpos_v0]; omega
    · ext; simp only [fromSplit, hpos_v0, splitMidLen, ↓reduceIte]; omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
      ext
      simp only [fromSplit, splitPos, Equiv.symm_apply_apply, ht0, ↓reduceIte, Fin.val_mk]
      omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
      ext
      simp only [fromSplit, splitPos, Equiv.symm_apply_apply, ht0, ↓reduceIte, Fin.val_mk]
      omega
    · have ht0 : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h; simp only [Fin.val_zero] at this; omega
      have hne : τ' ⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ ≠ v₀ := hτ'_ne ht0
      ext
      simp only [fromSplit, splitPos, splitMidLen, Equiv.symm_apply_apply, ht0, hne, ↓reduceIte,
        Fin.val_mk]
      omega
  let eFin : Fin (Fintype.card (SplitV W v₀ pad)) ≃ Fin (3 * m + pad) := finCongr hM_card
  let eSplit : SplitV W v₀ pad ≃ Fin (3 * m + pad) := ⟨fromSplit, toSplit, hleft, hright⟩
  let σ : Fin (Fintype.card (SplitV W v₀ pad)) ≃ SplitV W v₀ pad :=
    eFin.trans eSplit.symm
  have hσ_succ : ∀ i : Fin (3 * m + pad),
      (paddedSplitGraph v₀ pad adjD).Adj (toSplit i) (toSplit (i + 1)) := fun i => by
    have hmod_succ : (i + 1).1 = if i.1 + 1 = 3 * m + pad then 0 else i.1 + 1 := by
      have hlt : i.1 < 3 * m + pad := i.2
      simp only [Fin.val_add, h1_pad]
      split_ifs with h
      · rw [h, Nat.mod_self]
      · exact Nat.mod_eq_of_lt (by omega)
    dsimp only [paddedSplitGraph, toSplit]
    by_cases h0 : i.1 = 0
    · have h1 : ¬ i.1 + 1 = 3 * m + pad := by omega
      have ha : (i + 1).1 = 1 := by rw [hmod_succ, ite_eq_right h1, h0]
      simp only [h0, ↓reduceDIte, ha, Nat.one_ne_zero, show 1 < pad + 2 by omega, splitAdjRel,
        Nat.sub_self, and_self]
    · by_cases h1 : i.1 < pad + 1
      · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
        have ha : (i + 1).1 = i.1 + 1 := by rw [hmod_succ, ite_eq_right hm1]
        have hlt2 : i.1 < pad + 2 := by omega
        have hlt2' : i.1 + 1 < pad + 2 := by omega
        have ha0 : i.1 + 1 ≠ 0 := by omega
        simp only [h0, hlt2, ↓reduceDIte, ha, ha0, hlt2', splitAdjRel, true_and]
        left; omega
      · by_cases h1' : i.1 = pad + 1
        · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
          have ha : (i + 1).1 = pad + 2 := by rw [hmod_succ, ite_eq_right hm1, h1']
          simp only [h1', show pad + 1 ≠ 0 by omega, show pad + 1 < pad + 2 by omega, ↓reduceDIte,
            ha, show pad + 2 ≠ 0 by omega, show ¬ pad + 2 < pad + 2 by omega, splitAdjRel,
            splitMidLen, ↓reduceIte, Nat.add_sub_cancel]
          trivial
        · by_cases h2 : i.1 = pad + 2
          · have hm1 : ¬ i.1 + 1 = 3 * m + pad := by omega
            have ha : (i + 1).1 = pad + 3 := by rw [hmod_succ, ite_eq_right hm1, h2]
            simp only [h2, show pad + 2 ≠ 0 by omega, show ¬ pad + 2 < pad + 2 by omega,
              ↓reduceDIte, ha, show pad + 3 ≠ 0 by omega, show ¬ pad + 3 < pad + 2 by omega,
              show pad + 3 ≠ pad + 2 by omega, Nat.sub_self, Nat.zero_div, Nat.zero_mod,
              ↓reduceIte, splitAdjRel]
            have h01 : (0 + 1 : Fin m) = ⟨1, by omega⟩ :=
              Fin.ext (by rw [zero_add, h1_m])
            simpa only [hτ'0, h01] using hτ'_adj 0
          · have hge : pad + 3 ≤ i.1 := by omega
            have hlt1 : ¬ i.1 < pad + 2 := by omega
            by_cases hlast : i.1 + 1 = 3 * m + pad
            · have ha : (i + 1).1 = 0 := by rw [hmod_succ, ite_eq_left hlast]
              have hj : i.1 - (pad + 3) = 3 * (m - 1) - 1 := by omega
              have hmod2 : (i.1 - (pad + 3)) % 3 = 2 := by omega
              have hdiv : (i.1 - (pad + 3)) / 3 + 1 = m - 1 := by omega
              simp only [h0, hlt1, h2, ↓reduceDIte, ha, hmod2,
                show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, splitAdjRel]
              have hm_eq : (⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩ : Fin m) + 1 = 0 := by
                ext; simp only [Fin.val_add, h1_m, hdiv, Fin.val_zero]
                rw [show m - 1 + 1 = m by omega, Nat.mod_self]
              have hgoal := hτ'_adj ⟨(i.1 - (pad + 3)) / 3 + 1, by omega⟩
              rwa [hm_eq, hτ'0] at hgoal
            · have ha : (i + 1).1 = i.1 + 1 := by rw [hmod_succ, ite_eq_right hlast]
              have ha0 : i.1 + 1 ≠ 0 := by omega
              have ha1 : ¬ i.1 + 1 < pad + 2 := by omega
              have ha2 : i.1 + 1 ≠ pad + 2 := by omega
              let j := i.1 - (pad + 3)
              have hj_def : i.1 - (pad + 3) = j := rfl
              have hj' : i.1 + 1 - (pad + 3) = j + 1 := by omega
              rcases Nat.mod_lt j (by omega : 0 < 3) with hmod
              have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
              rcases hcases with hr | hr | hr
              · have hdiv' : (j + 1) / 3 = j / 3 := by omega
                have hmod' : (j + 1) % 3 = 1 := by omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj_def, hj', hr,
                  hdiv', hmod', Nat.one_ne_zero, ↓reduceIte, splitAdjRel, and_self]
              · have hdiv' : (j + 1) / 3 = j / 3 := by omega
                have hmod' : (j + 1) % 3 = 2 := by omega
                have ht0 : (⟨j / 3 + 1, by omega⟩ : Fin m) ≠ 0 := by
                  intro h; have := congrArg Fin.val h
                  simp only [Fin.val_zero] at this; omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj_def, hj', hr,
                  hdiv', hmod', Nat.one_ne_zero, show (2 : ℕ) ≠ 0 by omega,
                  show (2 : ℕ) ≠ 1 by omega, ↓reduceIte, splitAdjRel, splitMidLen, hτ'_ne ht0]
                trivial
              · have hdiv' : (j + 1) / 3 = j / 3 + 1 := by omega
                have hmod' : (j + 1) % 3 = 0 := by omega
                simp only [h0, hlt1, h2, ↓reduceDIte, ha, ha0, ha1, ha2, hj_def, hj', hr,
                  hdiv', hmod', show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega,
                  ↓reduceIte, splitAdjRel]
                have hfin : (⟨j / 3 + 1 + 1, by omega⟩ : Fin m) =
                    ⟨j / 3 + 1, by omega⟩ + 1 := by
                  ext
                  simp only [Fin.val_add, h1_m]
                  exact (Nat.mod_eq_of_lt (by omega)).symm
                rw [hfin]
                exact hτ'_adj ⟨j / 3 + 1, by omega⟩
  have hσ_adj : ∀ k : Fin (Fintype.card (SplitV W v₀ pad)),
      (paddedSplitGraph v₀ pad adjD).Adj (σ k) (σ (k + 1)) := fun k => by
    have hk : eFin (k + 1) = eFin k + 1 := by
      ext
      simp only [eFin, finCongr_apply, Fin.val_cast, Fin.val_add, h1_M, h1_pad, hM_card]
    simp only [σ, Equiv.trans_apply, eSplit, Equiv.coe_fn_symm_mk, hk]
    exact hσ_succ (eFin k)
  have h1_M_eq : (⟨1, by omega⟩ : Fin (Fintype.card (SplitV W v₀ pad))) = 1 :=
    Fin.ext h1_M.symm
  have hwrap : ∀ t : Fin m,
      fromSplit (.vOut (τ' t)) + 1 = fromSplit (.vIn (τ' (t + 1))) := fun t => by
    ext
    dsimp only [fromSplit, splitPos, splitMidLen]
    by_cases ht0 : t = 0
    · subst ht0
      have h1 : (1 : Fin m) ≠ 0 := by
        intro h; have := congrArg Fin.val h
        rw [h1_m, Fin.val_zero] at this; omega
      have hsymm1 : τ'.symm (τ' 1) = 1 := Equiv.symm_apply_apply _ _
      simp only [hτ'0, hτ'_symm0, ↓reduceIte, zero_add, hsymm1, h1, Fin.val_add, h1_pad, h1_m]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hne := hτ'_ne ht0
      have ht1 : 1 ≤ t.1 := Nat.pos_of_ne_zero fun h => ht0 (Fin.ext h)
      have ht_lt : t.1 < m := t.2
      by_cases hlast : t.1 + 1 = m
      · have ht0' : t + 1 = 0 := Fin.ext (by
          simp only [Fin.val_add, h1_m, Fin.val_zero]
          rw [hlast, Nat.mod_self])
        simp only [ht0, hne, ↓reduceIte, ht0', Fin.val_add, h1_pad, Equiv.symm_apply_apply]
        rw [show 3 * t.1 + pad + 1 + 1 + 1 = 3 * m + pad by omega, Nat.mod_self]
      · have ht0' : t + 1 ≠ 0 := fun h => by
          have := congrArg Fin.val h
          simp only [Fin.val_add, h1_m, Fin.val_zero] at this
          rw [Nat.mod_eq_of_lt (by omega)] at this; omega
        have ht1' : (t + 1).1 = t.1 + 1 := by
          simp only [Fin.val_add, h1_m]
          exact Nat.mod_eq_of_lt (by omega)
        simp only [ht0, hne, ↓reduceIte, ht0', Fin.val_add, h1_pad, Equiv.symm_apply_apply, ht1']
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
  refine ⟨tourEdgeSet σ hM3, ⟨⟨hM3, σ, rfl⟩, fun e he => ?_⟩, fun u w => ?_⟩
  · rw [tourEdgeSet, Finset.mem_image] at he
    obtain ⟨k, _, rfl⟩ := he
    dsimp only
    rw [h1_M_eq]
    exact (SimpleGraph.mem_edgeSet _).2 (hσ_adj k)
  · simp only [tourEdgeSet, h1_M_eq, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
    constructor
    · rintro ⟨k, hk⟩
      have hk_eq : (σ k = .vOut u ∧ σ (k + 1) = .vIn w) ∨
          (σ k = .vIn w ∧ σ (k + 1) = .vOut u) := by
        simpa only [Sym2.eq_iff] using hk
      have hnot_rev : ¬ (σ k = .vIn w ∧ σ (k + 1) = .vOut u) := by
        rintro ⟨h1, h2⟩
        have hk1 : eFin (k + 1) = eFin k + 1 := by
          ext
          simp only [eFin, finCongr_apply, Fin.val_cast, Fin.val_add, h1_M, h1_pad, hM_card]
        simp only [σ, Equiv.trans_apply, eSplit, Equiv.coe_fn_symm_mk, hk1] at h1 h2
        have heq1 := congrArg fromSplit h1
        have heq2 := congrArg fromSplit h2
        rw [hright] at heq1 heq2
        have hpos1 := congrArg Fin.val heq1
        have hpos2 := congrArg Fin.val heq2
        have hstep : (eFin k + 1).1 =
            if (eFin k).1 + 1 = 3 * m + pad then 0 else (eFin k).1 + 1 := by
          have hk_lt : (eFin k).1 < 3 * m + pad := (eFin k).2
          simp only [Fin.val_add, h1_pad]
          split_ifs with h <;> [rw [h, Nat.mod_self]; exact Nat.mod_eq_of_lt (by omega)]
        rw [hpos1] at hstep
        by_cases hw : w = v₀ <;> by_cases hu : u = v₀
        · subst hw hu
          simp only [fromSplit, hpos_v0, splitMidLen, ↓reduceIte] at hstep hpos2
          rw [ite_eq_right (by omega)] at hstep
          omega
        · subst hw
          have htu : τ'.symm u ≠ 0 := fun h => hu (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have htu1 : 1 ≤ (τ'.symm u).1 := Nat.pos_of_ne_zero fun h => htu (Fin.ext h)
          simp only [fromSplit, hpos_v0, splitPos, splitMidLen, htu, hu, ↓reduceIte] at hstep hpos2
          rw [ite_eq_right (by omega)] at hstep
          omega
        · subst hu
          have htw : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have htw1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => htw (Fin.ext h)
          simp only [fromSplit, splitPos, splitMidLen, htw, hτ'_symm0, ↓reduceIte] at hstep hpos2
          split_ifs at hstep <;> omega
        · have htw : τ'.symm w ≠ 0 := fun h => hw (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have htw1 : 1 ≤ (τ'.symm w).1 := Nat.pos_of_ne_zero fun h => htw (Fin.ext h)
          have htu : τ'.symm u ≠ 0 := fun h => hu (τ'.symm.injective (h.trans hτ'_symm0.symm))
          have htu1 : 1 ≤ (τ'.symm u).1 := Nat.pos_of_ne_zero fun h => htu (Fin.ext h)
          simp only [fromSplit, splitPos, splitMidLen, htw, htu, hu, ↓reduceIte] at hstep hpos2
          split_ifs at hstep <;> omega
      rcases hk_eq with ⟨hu, hw⟩ | hbad
      · have hk' := congrArg eSplit hu
        have hk'' := congrArg eSplit hw
        have hku : eFin k = fromSplit (.vOut u) := by
          simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, eSplit, Equiv.coe_fn_mk]
            using hk'
        have hkw : eFin (k + 1) = fromSplit (.vIn w) := by
          simpa only [σ, Equiv.trans_apply, Equiv.apply_symm_apply, eSplit, Equiv.coe_fn_mk]
            using hk''
        have hk1 : eFin (k + 1) = eFin k + 1 := by
          ext; simp only [eFin, finCongr_apply, Fin.val_cast, Fin.val_add, h1_M, h1_pad, hM_card]
        rw [hk1, hku] at hkw
        let tu := τ'.symm u
        have htu : τ' tu = u := τ'.apply_symm_apply u
        have hwrap_u := hwrap tu
        rw [htu] at hwrap_u
        have heq_in : eSplit.symm (eSplit (.vIn (τ' (tu + 1)))) =
            eSplit.symm (eSplit (.vIn w)) := by
          dsimp only [eSplit, Equiv.coe_fn_mk]
          rw [← hwrap_u, hkw]
        simp only [Equiv.symm_apply_apply, SplitV.vIn.injEq] at heq_in
        refine ⟨t₀ + tu, ?_, ?_⟩
        · exact htu
        · rw [add_assoc]
          exact heq_in
      · exact absurd hbad hnot_rev
    · rintro ⟨t, rfl, rfl⟩
      let t' : Fin m := t - t₀
      have ht'1 : τ' t' = τ t := by
        simp only [τ', t', Equiv.coe_fn_mk, show t₀ + (t - t₀) = t by abel]
      have ht'2 : τ' (t' + 1) = τ (t + 1) := by
        simp only [τ', t', Equiv.coe_fn_mk, show t₀ + (t - t₀ + 1) = t + 1 by abel]
      let k : Fin (Fintype.card (SplitV W v₀ pad)) := eFin.symm (fromSplit (.vOut (τ' t')))
      refine ⟨k, ?_⟩
      have hsk : σ k = .vOut (τ t) := by
        rw [← ht'1]
        simp only [σ, k, Equiv.trans_apply, Equiv.apply_symm_apply, eSplit, Equiv.coe_fn_symm_mk,
          hleft]
      have hk1 : eFin (k + 1) = eFin k + 1 := by
        ext; simp only [eFin, finCongr_apply, Fin.val_cast, Fin.val_add, h1_M, h1_pad, hM_card]
      have hstep : eFin k + 1 = fromSplit (.vIn (τ' (t' + 1))) := by
        simp only [k, Equiv.apply_symm_apply]
        exact hwrap t'
      have hsk1 : σ (k + 1) = .vIn (τ (t + 1)) := by
        rw [← ht'2]
        simp only [σ, Equiv.trans_apply, hk1, hstep, eSplit, Equiv.coe_fn_symm_mk, hleft]
      rw [hsk, hsk1]

private theorem tourEdgeSet_reverse {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) :
    tourEdgeSet
      { toFun := fun i => σ (-i)
        invFun := fun v => -(σ.symm v)
        left_inv := fun i => by simp only [Equiv.symm_apply_apply, neg_neg]
        right_inv := fun v => by simp only [neg_neg, Equiv.apply_symm_apply] } hV =
      tourEdgeSet σ hV := by
  have h1_eq : (⟨1, by omega⟩ : Fin (Fintype.card V)) = 1 :=
    Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)
  ext ⟨e, he⟩
  simp only [tourEdgeSet, h1_eq, Finset.mem_image, Finset.mem_univ, true_and, Subtype.mk.injEq,
    Equiv.coe_fn_mk]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨-(i + 1), ?_⟩
    rw [show -(i + 1) + 1 = -i by abel, Sym2.eq_swap]
    exact hi
  · rintro ⟨j, hj⟩
    refine ⟨-(j + 1), ?_⟩
    rw [show -(-(j + 1) + 1) = j by abel, show -(-(j + 1)) = j + 1 by abel, Sym2.eq_swap]
    exact hj

private theorem tourEdgeSet_shift {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (σ : Fin (Fintype.card V) ≃ V) (hV : 3 ≤ Fintype.card V) (s : Fin (Fintype.card V)) :
    tourEdgeSet
      { toFun := fun i => σ (s + i)
        invFun := fun v => σ.symm v - s
        left_inv := fun i => by simp only [Equiv.symm_apply_apply, add_sub_cancel_left]
        right_inv := fun v => by simp only [add_sub_cancel, Equiv.apply_symm_apply] } hV =
      tourEdgeSet σ hV := by
  have h1_eq : (⟨1, by omega⟩ : Fin (Fintype.card V)) = 1 :=
    Fin.ext (by rw [Fin.val_one']; exact (Nat.mod_eq_of_lt (by omega)).symm)
  ext ⟨e, he⟩
  simp only [tourEdgeSet, h1_eq, Finset.mem_image, Finset.mem_univ, true_and, Subtype.mk.injEq,
    Equiv.coe_fn_mk]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨s + i, ?_⟩
    rw [add_assoc]
    exact hi
  · rintro ⟨j, hj⟩
    refine ⟨j - s, ?_⟩
    rwa [show s + (j - s) = j by abel, show s + (j - s + 1) = j + 1 by abel]

/-- For `3 ≤ M`, `i - 1 ≠ i + 1` in `Fin M`. -/
theorem fin_sub_one_ne_add_one {M : ℕ} [NeZero M] (hM : 3 ≤ M) (i : Fin M) :
    i - 1 ≠ i + 1 := by
  intro h
  have h1 : (1 : Fin M).1 = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have hsum : i + (1 + 1) = i + 0 := by
    calc
      i + (1 + 1) = i + 1 + 1 := (add_assoc i 1 1).symm
      _ = i - 1 + 1 := by rw [← h]
      _ = i + 0 := by rw [sub_add_cancel, add_zero]
  have h20 : (1 + 1 : Fin M) = 0 := add_left_cancel hsum
  have hv := congrArg Fin.val h20
  rw [Fin.val_add, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
  omega

private def midPrev {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W)
    (k : Fin (splitMidLen v₀ pad w)) : SplitV W v₀ pad :=
  if h : k.1 = 0 then .vIn w else .vMid w ⟨k.1 - 1, by omega⟩

private def midNext {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ) (w : W)
    (k : Fin (splitMidLen v₀ pad w)) : SplitV W v₀ pad :=
  if h : k.1 + 1 = splitMidLen v₀ pad w then .vOut w
  else .vMid w ⟨k.1 + 1, by have := k.2; omega⟩

private theorem adj_vMid_iff {W : Type*} [DecidableEq W] (v₀ : W) (pad : ℕ)
    (adjD : W → W → Prop) (w : W) (k : Fin (splitMidLen v₀ pad w)) (x : SplitV W v₀ pad) :
    (paddedSplitGraph v₀ pad adjD).Adj (.vMid w k) x ↔
      x = midPrev v₀ pad w k ∨ x = midNext v₀ pad w k := by
  have hk_lt : k.1 < splitMidLen v₀ pad w := k.2
  have hvMid_eq : ∀ {w₁ w₂ k₁ k₂},
      SplitV.vMid (W := W) (v₀ := v₀) (pad := pad) w₁ k₁ = .vMid w₂ k₂ →
        w₁ = w₂ ∧ k₁.1 = k₂.1 := by
    rintro _ _ _ _ ⟨⟩
    exact ⟨rfl, rfl⟩
  cases x with
  | vIn u =>
      simp only [paddedSplitGraph, splitAdjRel, midPrev, midNext]
      by_cases h0 : k.1 = 0 <;> simp only [h0, ↓reduceDIte] <;>
        split_ifs <;> simp only [or_false, SplitV.vIn.injEq, eq_comm, and_true, and_false]
  | vMid u k' =>
      simp only [paddedSplitGraph, splitAdjRel]
      constructor
      · rintro ⟨hwu, hstep⟩
        subst hwu
        rcases hstep with hstep | hstep
        · right
          simp only [midNext, show ¬ k.1 + 1 = splitMidLen v₀ pad w by have := k'.2; omega,
            ↓reduceDIte]
          congr 1
          exact Fin.ext hstep.symm
        · left
          simp only [midPrev, show ¬ k.1 = 0 by omega, ↓reduceDIte]
          congr 1
          exact Fin.ext (by dsimp only; omega)
      · rintro (h | h)
        · by_cases h0 : k.1 = 0
          · simp only [midPrev, h0, ↓reduceDIte] at h
            cases h
          · simp only [midPrev, h0, ↓reduceDIte] at h
            obtain ⟨hwu, hval⟩ := hvMid_eq h
            subst hwu
            exact ⟨rfl, Or.inr (by dsimp only at hval; omega)⟩
        · by_cases hlast : k.1 + 1 = splitMidLen v₀ pad w
          · simp only [midNext, hlast, ↓reduceDIte] at h
            cases h
          · simp only [midNext, hlast, ↓reduceDIte] at h
            obtain ⟨hwu, hval⟩ := hvMid_eq h
            subst hwu
            exact ⟨rfl, Or.inl (by dsimp only at hval; omega)⟩
  | vOut u =>
      simp only [paddedSplitGraph, splitAdjRel, midPrev, midNext]
      by_cases hlast : k.1 + 1 = splitMidLen v₀ pad w <;> simp only [hlast, ↓reduceDIte] <;>
        split_ifs <;> simp only [or_false, false_or, SplitV.vOut.injEq, eq_comm, and_true,
          and_false]

/-- Every undirected tour of `paddedSplitGraph v₀ pad adjD` (`|W| ≥ 2`) induces a directed
Hamiltonian tour of `(W, adjD)` matching the inter-gadget arcs. -/
theorem exists_dirTour_of_paddedSplitTour {W : Type*} [Fintype W] [Nonempty W] [DecidableEq W]
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
  have h1_M : (1 : Fin M).1 = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  have h1_M_eq : (⟨1, by omega⟩ : Fin M) = 1 := Fin.ext h1_M.symm
  have hadj0 : ∀ i : Fin M, (paddedSplitGraph v₀ pad adjD).Adj (σ₀ i) (σ₀ (i + 1)) := fun i =>
    (SimpleGraph.mem_edgeSet _).1 (hsub ⟨s(σ₀ i, σ₀ (i + 1)), by
      rw [← h1_M_eq]; exact tourEdge_mem_top_edgeSet hM3 σ₀ i⟩
      (Finset.mem_image.2 ⟨i, Finset.mem_univ _, Subtype.ext (by dsimp only; rw [h1_M_eq])⟩))
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
    fun h => fin_sub_one_ne_add_one hM3 k0 (σ₀.injective h)
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
    (SimpleGraph.mem_edgeSet _).1 (hsub ⟨s(σ i, σ (i + 1)), by
      rw [← h1_M_eq]; exact tourEdge_mem_top_edgeSet hM3 σ i⟩
      (by
        rw [← htour]
        exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, Subtype.ext (by dsimp only; rw [h1_M_eq])⟩))
  let finOf : ℕ → Fin M := fun n => ⟨n % M, Nat.mod_lt _ hMpos⟩
  let stepNat : ℕ → SplitV W v₀ pad := fun n => σ (finOf n)
  have hfin_succ : ∀ n : ℕ, finOf (n + 1) = finOf n + 1 := fun n => by
    ext
    simp only [finOf, Fin.val_add, h1_M, Nat.mod_add_mod]
  have hstep_adj : ∀ n : ℕ, (paddedSplitGraph v₀ pad adjD).Adj (stepNat n) (stepNat (n + 1)) :=
    fun n => by
    dsimp only [stepNat]
    rw [hfin_succ n]
    exact hadj (finOf n)
  have hstep_ne2 : ∀ n : ℕ, stepNat (n + 2) ≠ stepNat n := fun n h => by
    have h2 : finOf (n + 2) = finOf (n + 1) + 1 := hfin_succ (n + 1)
    have hn : finOf n = finOf (n + 1) - 1 := by
      have hs : finOf (n + 1) = finOf n + 1 := hfin_succ n
      rw [hs, add_sub_cancel_right]
    have hfeq : finOf (n + 1) + 1 = finOf (n + 1) - 1 := by
      rw [← h2, ← hn]; exact σ.injective h
    exact fin_sub_one_ne_add_one hM3 (finOf (n + 1)) hfeq.symm
  have hblock_walk : ∀ (t : ℕ) (w : W),
      stepNat t = .vIn w → stepNat (t + 1) = .vMid w ⟨0, splitMidLen_pos v₀ pad w⟩ →
        (∀ k (hk : k < splitMidLen v₀ pad w), stepNat (t + 1 + k) = .vMid w ⟨k, hk⟩) ∧
        stepNat (t + 1 + splitMidLen v₀ pad w) = .vOut w ∧
        ∃ w', adjD w w' ∧ stepNat (t + 2 + splitMidLen v₀ pad w) = .vIn w' ∧
          stepNat (t + 3 + splitMidLen v₀ pad w) = .vMid w' ⟨0, splitMidLen_pos v₀ pad w'⟩ := by
    intro t w ht0 ht1
    have hmid_pair : ∀ k (hk : k < splitMidLen v₀ pad w),
        stepNat (t + 1 + k) = .vMid w ⟨k, hk⟩ ∧
        stepNat (t + k) = midPrev v₀ pad w ⟨k, hk⟩ := by
      intro k
      induction k with
      | zero =>
          intro _
          exact ⟨ht1, by simpa only [add_zero, midPrev, ↓reduceDIte] using ht0⟩
      | succ k ih =>
          intro hk1
          have hk : k < splitMidLen v₀ pad w := by omega
          obtain ⟨hcur, hprev_eq⟩ := ih hk
          have hnb := hstep_adj (t + 1 + k)
          rw [hcur] at hnb
          rcases (adj_vMid_iff v₀ pad adjD w ⟨k, hk⟩ _).1 hnb with hprev | hnext
          · exfalso
            rw [show t + 1 + k + 1 = t + k + 2 by omega] at hprev
            exact hstep_ne2 (t + k) (hprev.trans hprev_eq.symm)
          · simp only [midNext, show ¬ k + 1 = splitMidLen v₀ pad w by omega, ↓reduceDIte] at hnext
            refine ⟨by simpa only [add_assoc] using hnext, ?_⟩
            rw [show t + (k + 1) = t + 1 + k by omega]
            simpa only [midPrev, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
              Nat.add_sub_cancel] using hcur
    have hmid : ∀ k (hk : k < splitMidLen v₀ pad w), stepNat (t + 1 + k) = .vMid w ⟨k, hk⟩ :=
      fun k hk => (hmid_pair k hk).1
    have hout : stepNat (t + 1 + splitMidLen v₀ pad w) = .vOut w := by
      let k := splitMidLen v₀ pad w - 1
      have hk : k < splitMidLen v₀ pad w := by have := splitMidLen_pos v₀ pad w; omega
      obtain ⟨hcur, hprev_eq⟩ := hmid_pair k hk
      have hnb := hstep_adj (t + 1 + k)
      rw [hcur] at hnb
      have hk_last : k + 1 = splitMidLen v₀ pad w := by have := splitMidLen_pos v₀ pad w; omega
      rcases (adj_vMid_iff v₀ pad adjD w ⟨k, hk⟩ _).1 hnb with hprev | hnext
      · exfalso
        have heq := hprev.trans hprev_eq.symm
        rw [show t + 1 + k + 1 = t + k + 2 by omega] at heq
        exact hstep_ne2 (t + k) heq
      · simp only [midNext, hk_last, ↓reduceDIte] at hnext
        rwa [show t + 1 + splitMidLen v₀ pad w = t + 1 + k + 1 by omega]
    have hnb_out := hstep_adj (t + 1 + splitMidLen v₀ pad w)
    rw [hout, show t + 1 + splitMidLen v₀ pad w + 1 = t + 2 + splitMidLen v₀ pad w by omega]
      at hnb_out
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
          rcases hnb_out with ⟨hwu, hk'⟩
          subst hwu
          have hk'eq : (⟨splitMidLen v₀ pad w - 1, by
              have := splitMidLen_pos v₀ pad w; omega⟩ : Fin (splitMidLen v₀ pad w)) = k' :=
            Fin.ext (by dsimp only; omega)
          rw [← hk'eq] at hx
          exact hne_out hx
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
      have hadj_r : (paddedSplitGraph v₀ pad adjD).Adj m0 (σ (r + 1)) := by
        rw [← hr]; exact hadj r
      have hadj_rm : (paddedSplitGraph v₀ pad adjD).Adj m0 (σ (r - 1)) := by
        rw [← hr]; have h := (hadj (r - 1)).symm; rwa [show r - 1 + 1 = r by abel] at h
      have hr_plus :=
        (adj_vMid_iff v₀ pad adjD w' ⟨0, splitMidLen_pos v₀ pad w'⟩ (σ (r + 1))).1 hadj_r
      have hr_minus :=
        (adj_vMid_iff v₀ pad adjD w' ⟨0, splitMidLen_pos v₀ pad w'⟩ (σ (r - 1))).1 hadj_rm
      have hne_r : σ (r - 1) ≠ σ (r + 1) :=
        fun h => fin_sub_one_ne_add_one hM3 r (σ.injective h)
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
        dsimp only [m0] at hbad
        cases hbad
    exact ⟨hmid, hout, w', hww', hw', hw'1⟩
  let BlockState := {p : ℕ × W //
    stepNat p.1 = .vIn p.2 ∧ stepNat (p.1 + 1) = .vMid p.2 ⟨0, splitMidLen_pos v₀ pad p.2⟩}
  let initBlock : BlockState :=
    ⟨(0, v₀), by
      have h0 : finOf 0 = 0 := Fin.ext (by simp only [finOf, Nat.zero_mod, Fin.val_zero])
      simpa only [stepNat, h0] using hσ0,
      by
        have h1f : finOf (0 + 1) = 1 :=
          Fin.ext (by simp only [finOf, zero_add, h1_M, Nat.mod_eq_of_lt (by omega : 1 < M)])
        simpa only [stepNat, h1f] using hσ1⟩
  let nextBlock (s : BlockState) :
      {s' : BlockState // s'.1.1 = s.1.1 + 2 + splitMidLen v₀ pad s.1.2 ∧ adjD s.1.2 s'.1.2} :=
    let h := hblock_walk s.1.1 s.1.2 s.2.1 s.2.2
    let w' := Classical.choose h.2.2
    let hw' := Classical.choose_spec h.2.2
    ⟨⟨(s.1.1 + 2 + splitMidLen v₀ pad s.1.2, w'), hw'.2.1,
      by rw [show s.1.1 + 2 + splitMidLen v₀ pad s.1.2 + 1 =
          s.1.1 + 3 + splitMidLen v₀ pad s.1.2 by omega]; exact hw'.2.2⟩, rfl, hw'.1⟩
  let seq : ℕ → BlockState := Nat.rec initBlock fun _ s => (nextBlock s).1
  let pos : ℕ → ℕ := fun r => (seq r).1.1
  let vert : ℕ → W := fun r => (seq r).1.2
  have hseq_step : ∀ r, pos (r + 1) = pos r + 2 + splitMidLen v₀ pad (vert r) ∧
      adjD (vert r) (vert (r + 1)) := fun r => (nextBlock (seq r)).2
  have hsum_pos : ∀ k, pos k = ∑ r ∈ Finset.range k, (2 + splitMidLen v₀ pad (vert r)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Finset.sum_range_succ, ← ih, (hseq_step k).1, Nat.add_assoc]
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
          have him_sum := Finset.sum_image (f := fun w => 2 + splitMidLen v₀ pad w) him_inj
          rw [hsum_pos k, ← him_sum]
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
          have hsum_le := Finset.sum_le_sum_of_subset (f := fun w => 2 + splitMidLen v₀ pad w)
            hsub_erase
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
              dsimp only at hval
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
            rw [(seq r₁).2.1, (seq r₂).2.1]
            exact congrArg SplitV.vIn heq
          · exact hinj r₁ r₂ hr12 (by omega)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr' | rfl
          · exact hlt r hr'
          · exact hpos_k
  obtain ⟨hvert_inj, hpos_lt⟩ := hwalk_lt (Fintype.card W) le_rfl
  let m := Fintype.card W
  have h1_m : (1 : Fin m).1 = 1 := by
    rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
  let τFun : Fin m → W := fun t => vert t.1
  have hτ_inj : Function.Injective τFun := fun t₁ t₂ heq => by
    rcases lt_trichotomy t₁.1 t₂.1 with h | h | h
    · exact absurd heq (hvert_inj t₁.1 t₂.1 h t₂.2)
    · exact Fin.ext h
    · exact absurd heq.symm (hvert_inj t₂.1 t₁.1 h t₁.2)
  let τ : Fin m ≃ W := Equiv.ofBijective τFun
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨hτ_inj, Fintype.card_fin m⟩)
  have hτ_apply : ∀ x : Fin m, τ x = vert x.1 := fun _ => rfl
  have him_univ : (Finset.range m).image vert = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_image_of_injOn (fun r₁ hr₁ r₂ hr₂ heq => by
      rw [Finset.coe_range, Set.mem_Iio] at hr₁ hr₂
      exact congrArg Fin.val (@hτ_inj ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq)),
      Finset.card_range]
  have hpos_m : pos m = M := by
    have him_sum := Finset.sum_image (f := fun w => 2 + splitMidLen v₀ pad w) (g := vert)
      (fun r₁ hr₁ r₂ hr₂ heq => by
        rw [Finset.coe_range, Set.mem_Iio] at hr₁ hr₂
        exact congrArg Fin.val (@hτ_inj ⟨r₁, hr₁⟩ ⟨r₂, hr₂⟩ heq))
    rw [hsum_pos m, ← him_sum, him_univ, htotal_sum]
  have hvert_m : vert m = vert 0 := by
    have hstep_m : stepNat (pos m) = stepNat 0 := by
      simp only [stepNat, hpos_m, finOf, Nat.mod_self, Nat.zero_mod]
    have hv := (seq m).2.1.symm.trans (hstep_m.trans (seq 0).2.1)
    exact SplitV.vIn.inj hv
  have hdir : IsDirTour adjD τ := fun t => by
    rw [hτ_apply, hτ_apply]
    by_cases hlast : t.1 + 1 = m
    · have ht0 : t + 1 = 0 := Fin.ext (by
        simp only [Fin.val_add, h1_m, Fin.val_zero]
        rw [hlast, Nat.mod_self])
      rw [ht0, Fin.val_zero]
      have hstep' := (hseq_step t.1).2
      rwa [hlast, hvert_m] at hstep'
    · have ht1 : (t + 1).1 = t.1 + 1 := by
        simp only [Fin.val_add, h1_m]
        exact Nat.mod_eq_of_lt (by omega)
      rw [ht1]
      exact (hseq_step t.1).2
  refine ⟨τ, hdir, fun u w => ?_⟩
  rw [← htour]
  simp only [tourEdgeSet, h1_M_eq, Finset.mem_image, Finset.mem_univ, true_and, Subtype.ext_iff]
  constructor
  · rintro ⟨i, hi⟩
    have hfind : ∀ k ≤ m, i.1 < pos k → ∃ r, r < k ∧ pos r ≤ i.1 ∧ i.1 < pos (r + 1) := by
      intro k
      induction k with
      | zero =>
          intro _ hlt0
          have h0 : pos 0 = 0 := rfl
          omega
      | succ k ih =>
          intro hk hlt
          by_cases hk' : i.1 < pos k
          · obtain ⟨r, hr, hlo, hhi⟩ := ih (Nat.le_of_succ_le hk) hk'
            exact ⟨r, by omega, hlo, hhi⟩
          · exact ⟨k, Nat.lt_succ_self k, by omega, hlt⟩
    obtain ⟨r, hr, hlo, hhi⟩ := hfind m le_rfl (hpos_m ▸ i.2)
    have hfin_i : i = finOf i.1 := Fin.ext (Nat.mod_eq_of_lt i.2).symm
    have hfin_i1 : i + 1 = finOf (i.1 + 1) :=
      Fin.ext (by dsimp only [finOf]; rw [Fin.val_add, h1_M])
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
          rcases hi with ⟨_, h⟩ | ⟨h, _⟩ <;> cases h
        · have hlast : i.1 = pos r + 1 + splitMidLen v₀ pad (vert r) := by omega
          have hs1 : stepNat i.1 = .vOut (vert r) := by rw [hlast]; exact hwalk.2.1
          have hs2 : stepNat (i.1 + 1) = .vIn (vert (r + 1)) := by
            rw [show i.1 + 1 = pos (r + 1) by omega]
            exact (seq (r + 1)).2.1
          rw [hs1, hs2, Sym2.eq_iff] at hi
          rcases hi with ⟨hu, hw⟩ | ⟨hbad, _⟩
          · refine ⟨⟨r, hr⟩, ?_, ?_⟩
            · rw [hτ_apply]; cases hu; rfl
            · rw [hτ_apply]
              by_cases hr1 : r + 1 = m
              · have hwrap : (⟨r, hr⟩ + 1 : Fin m) = 0 := Fin.ext (by
                  simp only [Fin.val_add, h1_m, Fin.val_zero]
                  rw [hr1, Nat.mod_self])
                rw [hwrap, Fin.val_zero, ← hvert_m, ← hr1]
                cases hw; rfl
              · have hnext : (⟨r, hr⟩ + 1 : Fin m).1 = r + 1 := by
                  simp only [Fin.val_add, h1_m]
                  exact Nat.mod_eq_of_lt (by omega)
                rw [hnext]
                cases hw; rfl
          · cases hbad
  · rintro ⟨t, rfl, rfl⟩
    let i : Fin M := ⟨pos t.1 + 1 + splitMidLen v₀ pad (vert t.1), by
      have := hpos_lt t.1 t.2
      have hstep := (hseq_step t.1).1
      by_cases hlast : t.1 + 1 = m
      · rw [hlast, hpos_m] at hstep; omega
      · have := hpos_lt (t.1 + 1) (by omega); omega⟩
    refine ⟨i, ?_⟩
    have hfin_i : i = finOf i.1 := Fin.ext (Nat.mod_eq_of_lt i.2).symm
    have hfin_i1 : i + 1 = finOf (i.1 + 1) :=
      Fin.ext (by dsimp only [finOf]; rw [Fin.val_add, h1_M])
    have hσi : σ i = .vOut (τ t) := by
      rw [hτ_apply, hfin_i]
      exact (hblock_walk (pos t.1) (vert t.1) (seq t.1).2.1 (seq t.1).2.2).2.1
    have hσi1 : σ (i + 1) = .vIn (τ (t + 1)) := by
      rw [hfin_i1]
      change stepNat (i.1 + 1) = .vIn (τ (t + 1))
      have hipos : i.1 + 1 = pos (t.1 + 1) := by dsimp only [i]; rw [(hseq_step t.1).1]; omega
      rw [hipos, hτ_apply]
      by_cases hlast : t.1 + 1 = m
      · have hwrap : t + 1 = 0 := Fin.ext (by
          simp only [Fin.val_add, h1_m, Fin.val_zero]
          rw [hlast, Nat.mod_self])
        rw [hwrap, Fin.val_zero, ← hvert_m, ← hlast]
        exact (seq (t.1 + 1)).2.1
      · have hnext : (t + 1).1 = t.1 + 1 := by
          simp only [Fin.val_add, h1_m]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hnext]
        exact (seq (t.1 + 1)).2.1
    rw [hσi, hσi1]

end SplitGraph
