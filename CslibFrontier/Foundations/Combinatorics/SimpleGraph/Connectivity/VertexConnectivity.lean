/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib)

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Separator
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Vertex connectivity and internally disjoint paths in simple graphs

Pure graph-theoretic notions and structural facts for vertex connectivity and Menger's theorem in
`SimpleGraph V`:

* `SimpleGraph.InternallyDisjoint`: pairwise internally vertex-disjoint `u`–`v` walks.
* `SimpleGraph.IsVertexConnected`: `k`-vertex-connectedness (`|V| > k` and `G - X` is connected
  whenever `|X| < k`; [Diestel2025], §1.4).
* Weak duality for vertex-disjoint `A`–`B` paths and internally disjoint `u`–`v` paths.
* Equivalence between `IsVertexConnected k` and having no `u`–`v` vertex separator of fewer than
  `k` vertices (together with `|V| > k`), and the path-to-connectivity half of global Menger's
  theorem ([Diestel2025], Theorem 3.3.6 (i)), including the `Finset` / injective path-family
  equivalence for handling adjacent vertices.

## Main definitions

* `SimpleGraph.InternallyDisjoint`: pairwise internally vertex-disjoint `u`–`v` walks.
* `SimpleGraph.IsVertexConnected`: `k`-vertex-connected simple graphs.

## Main results

* `SimpleGraph.card_le_card_of_disjoint_of_isSeparator`,
  `SimpleGraph.card_le_card_of_internallyDisjoint_of_isVertexSeparator`: weak duality for `A`–`B`
  paths and `u`–`v` paths.
* `SimpleGraph.isVertexConnected_zero`, `SimpleGraph.isVertexConnected_one`: `0`- and
  `1`-connectivity.
* `SimpleGraph.isVertexConnected_iff_forall_isVertexSeparator`: characterization by minimum vertex
  separator size.
* `SimpleGraph.card_gt_of_injective_internallyDisjoint`,
  `SimpleGraph.isVertexConnected_of_forall_exists_internallyDisjoint`,
  `SimpleGraph.isVertexConnected_of_nontrivial_of_forall_exists_injective_internallyDisjoint`:
  deducing `IsVertexConnected k` from internally disjoint path families.
* `SimpleGraph.exists_injective_internallyDisjoint_iff_exists_finset`: converting between
  injective indexed families and `Finset`s of internally disjoint paths.

## References

* [R. Diestel, *Graph Theory*][Diestel2025], §1.4 and §3.3 (Corollary 3.3.5 (i), Theorem 3.3.6 (i))
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- A family `W` of `u`–`v` walks is pairwise *internally disjoint* if distinct walks share no
vertex other than `u` and `v`. -/
@[expose] def InternallyDisjoint {G : SimpleGraph V} {u v : V} {ι : Type*}
    (W : ι → G.Walk u v) : Prop :=
  Pairwise fun i j => ∀ x ∈ (W i).support, x ∈ (W j).support → x = u ∨ x = v

/-- **Weak duality for vertex-disjoint `A`–`B` paths**: `k` pairwise vertex-disjoint `A`–`B`
walks need at least `k` vertices in every `A`–`B` separator. -/
theorem card_le_card_of_disjoint_of_isSeparator {G : SimpleGraph V} {A B : Set V} {k : ℕ}
    {a b : Fin k → V} (ha : ∀ i, a i ∈ A) (hb : ∀ i, b i ∈ B)
    (W : ∀ i, G.Walk (a i) (b i))
    (hdisj : Pairwise fun i j => (W i).support.Disjoint (W j).support)
    {Y : Finset V} (hY : G.IsSeparator A B ↑Y) : k ≤ Y.card := by
  choose v hv hvY using fun i => hY.exists_mem_support (ha i) (hb i) (W i)
  have hinj : Function.Injective fun i => (⟨v i, Finset.mem_coe.mp (hvY i)⟩ : Y) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact hdisj hne (hv i) (heq ▸ hv j)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **Weak duality, undirected vertex form**: `k` pairwise internally disjoint `u`–`v` paths
force every `u`–`v` separator to have at least `k` vertices. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexSeparator {G : SimpleGraph V} {u v : V}
    {k : ℕ} {W : Fin k → G.Walk u v} (hdisj : InternallyDisjoint W)
    {T : Finset V} (hT : G.IsVertexSeparator u v T) : k ≤ T.card := by
  rw [isVertexSeparator_iff_forall_walk] at hT
  choose x hx hxT using fun i => hT.2.2 (W i)
  have hinj : Function.Injective fun i => (⟨x i, hxT i⟩ : T) := by
    intro i j hij
    by_contra hne
    have heq : x i = x j := congrArg Subtype.val hij
    rcases hdisj hne (x i) (hx i) (heq ▸ hx j) with h | h
    · exact hT.1 (h ▸ hxT i)
    · exact hT.2.1 (h ▸ hxT i)
  simpa using Fintype.card_le_of_injective _ hinj

/-- A graph `G` is `k`-vertex-connected (`k : ℕ`) if it has more than `k` vertices and `G - X` is
connected for every vertex set `X` with fewer than `k` vertices ([Diestel2025], §1.4). -/
@[expose] def IsVertexConnected (G : SimpleGraph V) (k : ℕ) : Prop :=
  (k : ℕ∞) < ENat.card V ∧ ∀ X : Set V, X.encard < k → (G.induce Xᶜ).Connected

namespace IsVertexConnected

theorem card_gt {G : SimpleGraph V} {k : ℕ} (h : G.IsVertexConnected k) :
    (k : ℕ∞) < ENat.card V :=
  h.1

theorem nonempty {G : SimpleGraph V} {k : ℕ} (h : G.IsVertexConnected k) : Nonempty V := by
  rw [← not_isEmpty_iff, ← ENat.card_eq_zero_iff_empty, ← ne_eq, ← pos_iff_ne_zero]
  exact lt_of_le_of_lt zero_le h.1

theorem nontrivial {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k) (h : G.IsVertexConnected k) :
    Nontrivial V := by
  rw [← ENat.one_lt_card_iff_nontrivial]
  exact lt_of_le_of_lt (by exact_mod_cast hk) h.1

theorem connected {G : SimpleGraph V} {k : ℕ} (hk : 1 ≤ k) (h : G.IsVertexConnected k) :
    G.Connected := by
  have hconn := h.2 ∅ (by simpa using show 0 < k by omega)
  refine { preconnected := fun u v => ?_, nonempty := h.nonempty }
  have hreach := hconn.preconnected ⟨u, Set.notMem_empty u⟩ ⟨v, Set.notMem_empty v⟩
  exact hreach.map ⟨Subtype.val, id⟩

theorem anti {G : SimpleGraph V} {k l : ℕ} (hkl : k ≤ l) (h : G.IsVertexConnected l) :
    G.IsVertexConnected k :=
  ⟨lt_of_le_of_lt (by exact_mod_cast hkl) h.1,
    fun X hX => h.2 X (lt_of_lt_of_le hX (by exact_mod_cast hkl))⟩

theorem mono {G H : SimpleGraph V} (hGH : G ≤ H) {k : ℕ} (h : G.IsVertexConnected k) :
    H.IsVertexConnected k :=
  ⟨h.1, fun X hX => (h.2 X hX).mono fun _ _ hadj => hGH hadj⟩

end IsVertexConnected

@[simp]
theorem isVertexConnected_zero {G : SimpleGraph V} : G.IsVertexConnected 0 ↔ Nonempty V := by
  simp [IsVertexConnected, pos_iff_ne_zero, ENat.card_eq_zero_iff_empty, not_isEmpty_iff]

theorem isVertexConnected_one {G : SimpleGraph V} :
    G.IsVertexConnected 1 ↔ Nontrivial V ∧ G.Connected := by
  refine ⟨fun h => ⟨h.nontrivial le_rfl, h.connected le_rfl⟩, fun ⟨hn, hc⟩ => ?_⟩
  refine ⟨by simp, fun X hX => ?_⟩
  have hXe : X = ∅ := by
    rw [Nat.cast_one, Order.lt_one_iff, Set.encard_eq_zero] at hX
    exact hX
  subst hXe
  have : Nonempty (∅ᶜ : Set V) := ⟨⟨Classical.arbitrary V, Set.notMem_empty _⟩⟩
  refine ⟨fun ⟨u, _⟩ ⟨v, _⟩ => ?_⟩
  obtain ⟨w⟩ := hc.preconnected u v
  exact ⟨w.induce _ fun x _ => Set.notMem_empty x⟩

/-- A graph `G` is `k`-vertex-connected iff `|V| > k` and no two distinct vertices are separated
by fewer than `k` vertices. -/
theorem isVertexConnected_iff_forall_isVertexSeparator {G : SimpleGraph V} {k : ℕ} :
    G.IsVertexConnected k ↔
      (k : ℕ∞) < ENat.card V ∧
        ∀ ⦃u v : V⦄, u ≠ v → ∀ T : Finset V, G.IsVertexSeparator u v T → k ≤ T.card := by
  constructor
  · intro h
    refine ⟨h.1, fun u v _ T hT => ?_⟩
    by_contra! hTk
    have hconn := h.2 (T : Set V) (by simpa [Set.encard_coe_eq_coe_finsetCard] using hTk)
    rw [isVertexSeparator_iff_not_reachable_induce] at hT
    obtain ⟨hu, hv, hnr⟩ := hT
    exact hnr (hconn.preconnected ⟨u, hu⟩ ⟨v, hv⟩)
  · rintro ⟨hcard, hsep⟩
    refine ⟨hcard, fun X hX => ?_⟩
    have hfin : X.Finite := Set.encard_lt_top_iff.mp (lt_of_lt_of_le hX le_top)
    let T := hfin.toFinset
    have hTX : (T : Set V) = X := hfin.coe_toFinset
    have hTcard : T.card < k := by
      have : (T.card : ℕ∞) < k := by
        simpa [← Set.encard_coe_eq_coe_finsetCard, hTX] using hX
      exact_mod_cast this
    have hne : Xᶜ.Nonempty := by
      rw [Set.nonempty_iff_ne_empty, ne_eq, Set.compl_empty_iff]
      intro huniv
      have := huniv ▸ hX
      rw [Set.encard_univ] at this
      exact absurd (lt_trans this hcard) (lt_irrefl _)
    have : Nonempty (Xᶜ : Set V) := hne.to_subtype
    refine ⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩
    by_cases huv : u = v
    · subst huv; exact Reachable.refl _
    · have huT : u ∉ T := fun h => hu (hTX ▸ Finset.mem_coe.mpr h)
      have hvT : v ∉ T := fun h => hv (hTX ▸ Finset.mem_coe.mpr h)
      by_contra hnr
      let f : G.induce (T : Set V)ᶜ →g G.induce Xᶜ := ⟨fun y => ⟨y.1, hTX ▸ y.2⟩, id⟩
      have hTsep : G.IsVertexSeparator u v T :=
        isVertexSeparator_iff_not_reachable_induce.mpr ⟨huT, hvT, fun hr => hnr (hr.map f)⟩
      exact absurd (hsep huv T hTsep) (not_le_of_gt hTcard)

/-- A `u`–`v` path (`u ≠ v`) whose support is not `[u, v]` contains an internal vertex `∉ {u, v}`.
-/
theorem exists_internal_mem_support_of_support_ne {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    {w : G.Walk u v} (hw : w.IsPath) (hs : w.support ≠ [u, v]) :
    ∃ x ∈ w.support, x ≠ u ∧ x ≠ v := by
  cases w with
  | nil => exact absurd rfl huv
  | @cons _ w₁ _ h₁ p =>
    cases p with
    | nil => exact absurd rfl hs
    | @cons _ w₂ _ h₂ q =>
      have hnd := hw.support_nodup
      rw [Walk.support_cons, List.nodup_cons] at hnd
      have hnd2 := hnd.2
      rw [Walk.support_cons, List.nodup_cons] at hnd2
      refine ⟨w₁, by simp, fun h => hnd.1 (h ▸ by simp), fun h => ?_⟩
      subst h
      exact hnd2.1 (Walk.end_mem_support q)

/-- If two distinct vertices `u ≠ v` are joined by `k` distinct pairwise internally disjoint paths,
then `G` has strictly more than `k` vertices. -/
theorem card_gt_of_injective_internallyDisjoint {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    {k : ℕ} {W : Fin k → G.Walk u v} (hinj : Function.Injective W) (hW : ∀ i, (W i).IsPath)
    (hdisj : InternallyDisjoint W) : (k : ℕ∞) < ENat.card V := by
  classical
  let I : Finset (Fin k) := Finset.univ.filter fun i => (W i).support ≠ [u, v]
  have hIcard : k - 1 ≤ I.card := by
    have hsub : (Finset.univ \ I).card ≤ 1 := by
      refine Finset.card_le_one.mpr fun i hi j hj => ?_
      simp only [I, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and,
        not_not] at hi hj
      exact hinj (Walk.ext_support (hi.trans hj.symm))
    have hle : I.card ≤ k := by
      simpa [Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ I
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ I), Finset.card_univ,
      Fintype.card_fin] at hsub
    omega
  choose x hxm hxu hxv using fun i (hi : i ∈ I) =>
    exists_internal_mem_support_of_support_ne huv (hW i) (Finset.mem_filter.mp hi).2
  let S : Finset V := insert u (insert v (I.attach.image fun i => x i.1 i.2))
  have hxinj : Function.Injective fun i : I => x i.1 i.2 := by
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    by_contra hne
    have hne' : i ≠ j := fun h => hne (Subtype.ext h)
    have heq : x i hi = x j hj := hij
    rcases hdisj hne' (x i hi) (hxm i hi) (heq ▸ hxm j hj) with h | h
    · exact hxu i hi h
    · exact hxv i hi h
  have hScard : k + 1 ≤ S.card := by
    have huS : u ∉ insert v (I.attach.image fun i => x i.1 i.2) := by
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, not_or,
        not_exists]
      exact ⟨huv, fun i hi => hxu i.1 i.2 hi⟩
    have hvS : v ∉ I.attach.image fun i => x i.1 i.2 := by
      simp only [Finset.mem_image, Finset.mem_attach, true_and, not_exists]
      exact fun i hi => hxv i.1 i.2 hi
    rw [Finset.card_insert_of_notMem huS, Finset.card_insert_of_notMem hvS,
      Finset.card_image_of_injective _ hxinj, Finset.card_attach]
    omega
  have hle : (S.card : ℕ∞) ≤ ENat.card V := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact Set.encard_le_card (s := (S : Set V))
  refine lt_of_lt_of_le ?_ hle
  exact_mod_cast (show k < S.card by omega)

/-- If `|V| > k` and every pair of distinct vertices has `k` pairwise internally disjoint paths,
then `G` is `k`-vertex-connected. -/
theorem isVertexConnected_of_forall_exists_internallyDisjoint {G : SimpleGraph V} {k : ℕ}
    (hcard : (k : ℕ∞) < ENat.card V)
    (hpaths : ∀ ⦃u v : V⦄, u ≠ v →
      ∃ W : Fin k → G.Walk u v, (∀ i, (W i).IsPath) ∧ InternallyDisjoint W) :
    G.IsVertexConnected k := by
  refine isVertexConnected_iff_forall_isVertexSeparator.mpr ⟨hcard, fun u v huv T hT => ?_⟩
  obtain ⟨W, _, hdisj⟩ := hpaths huv
  exact card_le_card_of_internallyDisjoint_of_isVertexSeparator hdisj hT

/-- In a graph with at least two vertices, having `k` distinct pairwise internally disjoint paths
between every pair of distinct vertices implies `G` is `k`-vertex-connected. -/
theorem isVertexConnected_of_nontrivial_of_forall_exists_injective_internallyDisjoint
    [Nontrivial V] {G : SimpleGraph V} {k : ℕ}
    (hpaths : ∀ ⦃u v : V⦄, u ≠ v →
      ∃ W : Fin k → G.Walk u v,
        Function.Injective W ∧ (∀ i, (W i).IsPath) ∧ InternallyDisjoint W) :
    G.IsVertexConnected k := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne V
  obtain ⟨W, hinj, hW, hdisj⟩ := hpaths huv
  exact isVertexConnected_of_forall_exists_internallyDisjoint
    (card_gt_of_injective_internallyDisjoint huv hinj hW hdisj)
    fun a b hab => let ⟨W', _, hW', hdisj'⟩ := hpaths hab; ⟨W', hW', hdisj'⟩

/-- If `u` and `v` are distinct and non-adjacent, pairwise internally disjoint `u`–`v` paths are
automatically distinct. -/
theorem injective_of_internallyDisjoint_of_not_adj {G : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (hadj : ¬ G.Adj u v) {ι : Type*} {W : ι → G.Walk u v} (hW : ∀ i, (W i).IsPath)
    (hdisj : InternallyDisjoint W) : Function.Injective W := by
  intro i j hij
  by_contra hne
  have hs : (W i).support ≠ [u, v] := by
    intro hsupp
    cases hw : W i with
    | nil => exact huv rfl
    | @cons _ w₁ _ h₁ p =>
      cases p with
      | nil => exact hadj h₁
      | @cons _ w₂ _ h₂ q =>
        rw [hw] at hsupp
        simp [Walk.support_cons] at hsupp
  obtain ⟨x, hxm, hxu, hxv⟩ := exists_internal_mem_support_of_support_ne huv (hW i) hs
  rcases hdisj hne x hxm (hij ▸ hxm) with h | h
  · exact hxu h
  · exact hxv h

/-- Equivalence between an injective `Fin k`-indexed family and a `k`-element `Finset` of
internally disjoint `u`–`v` paths. -/
theorem exists_injective_internallyDisjoint_iff_exists_finset {G : SimpleGraph V} {u v : V}
    {k : ℕ} :
    (∃ W : Fin k → G.Walk u v,
        Function.Injective W ∧ (∀ i, (W i).IsPath) ∧ InternallyDisjoint W) ↔
      ∃ P : Finset (G.Walk u v), P.card = k ∧ (∀ w ∈ P, w.IsPath) ∧
        (P : Set (G.Walk u v)).Pairwise
          (fun w₁ w₂ => ∀ x ∈ w₁.support, x ∈ w₂.support → x = u ∨ x = v) := by
  classical
  constructor
  · rintro ⟨W, hinj, hW, hdisj⟩
    refine ⟨Finset.univ.image W, by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      Fintype.card_fin], fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ hne => ?_⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw
      exact hW i
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw₁)
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw₂)
      exact hdisj (fun h => hne (congrArg W h))
  · rintro ⟨P, hPcard, hW, hdisj⟩
    let e := (P.equivFinOfCardEq hPcard).symm
    refine ⟨fun i => (e i).1, fun i j hij => e.injective (Subtype.ext hij),
      fun i => hW _ (e i).2, fun i j hij => ?_⟩
    exact hdisj (e i).2 (e j).2 fun h => hij (e.injective (Subtype.ext h))

/-- A simple `u`–`v` path containing the edge `s(u, v)` must be the single-edge walk `[u, v]`. -/
theorem support_eq_pair_of_mem_edges_of_isPath {G : SimpleGraph V} {u v : V} {w : G.Walk u v}
    (hw : w.IsPath) (he : s(u, v) ∈ w.edges) : w.support = [u, v] := by
  cases w with
  | nil => simp at he
  | @cons _ w₁ _ h₁ p =>
    cases p with
    | nil => rfl
    | @cons _ w₂ _ h₂ q =>
      exfalso
      have hnd := hw.support_nodup
      rw [Walk.support_cons, List.nodup_cons] at hnd
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with he | he
      · rcases Sym2.eq_iff.mp he with ⟨_, hvw⟩ | ⟨huw, _⟩
        · have hnd2 := hnd.2
          rw [Walk.support_cons, List.nodup_cons] at hnd2
          exact hnd2.1 (hvw ▸ Walk.end_mem_support q)
        · exact G.ne_of_adj h₁ huw
      · exact hnd.1 (Walk.fst_mem_support_of_mem_edges _ he)

/-- Distinct pairwise internally disjoint paths between `u` and `v` are pairwise edge-disjoint. -/
theorem edgeDisjoint_of_injective_internallyDisjoint {G : SimpleGraph V} {u v : V} {ι : Type*}
    {W : ι → G.Walk u v} (hinj : Function.Injective W) (hW : ∀ i, (W i).IsPath)
    (hdisj : InternallyDisjoint W) :
    Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
  intro i j hij e hei hej
  induction e using Sym2.ind with
  | _ x y =>
    have hx := hdisj hij x (Walk.fst_mem_support_of_mem_edges _ hei)
      (Walk.fst_mem_support_of_mem_edges _ hej)
    have hy := hdisj hij y (Walk.snd_mem_support_of_mem_edges _ hei)
      (Walk.snd_mem_support_of_mem_edges _ hej)
    have hxy : x ≠ y := G.ne_of_adj (Walk.adj_of_mem_edges _ hei)
    have heuv : s(x, y) = s(u, v) := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hxy
    have hi := support_eq_pair_of_mem_edges_of_isPath (hW i) (heuv ▸ hei)
    have hj := support_eq_pair_of_mem_edges_of_isPath (hW j) (heuv ▸ hej)
    exact hij (hinj (Walk.ext_support (hi.trans hj.symm)))

end SimpleGraph
