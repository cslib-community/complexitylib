/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.ReducedLaplacian
public import CslibFrontier.Foundations.Combinatorics.Digraph.MatrixTree
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Arborescence
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Polynomial-time spanning in-arborescence counting

Polynomial-time evaluation of spanning in-arborescence counts for both simple digraphs
(`Digraph`) and multidigraphs (`Multidigraph`) via Tutte's directed matrix-tree theorem and
`Cslib.Circuits.Rational.detRows_polytime`.

## Main definitions

* `Cslib.Complexity.Graph.toDigraph`: simple digraph induced by `G` on `{v // v ∈ G.vertices}`.
* `Cslib.Complexity.Graph.digraphInArborescenceCount`: reduced Laplacian determinant counting
  simple-digraph spanning in-arborescences rooted at `r` (`0` if `r ∉ G.vertices`).
* `Cslib.Complexity.Graph.validArcs`, `.arcSrc`, `.arcTgt`: list of pairs in `G.edges` whose
  endpoints both lie in `G.vertices`, giving a finite multidigraph on `{v // v ∈ G.vertices}`.
* `Cslib.Complexity.Graph.multiLaplacianCount`: reduced multidigraph Laplacian determinant over an
  arbitrary duplicate-free vertex list `vs` and arc list `arcs`.
* `Cslib.Complexity.Graph.multiInArborescenceCount`: reduced Laplacian determinant counting
  multidigraph spanning in-arborescences rooted at `r` (`0` if `r ∉ G.vertices`).

## Main results

* `Cslib.Complexity.Graph.digraphInArborescenceCount_eq_natCard`: exact count equality for
  `G.toDigraph` (`Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence`).
* `Cslib.Complexity.Graph.computableInPolyTime_digraphInArborescenceCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_digraphIsInArborescence`: polynomial-time
  computability on `encPair encGraph encNat`.
* `Cslib.Complexity.Graph.multiLaplacianCount_eq_natCard`: exact multidigraph arborescence count
  formula over any closed duplicate-free vertex list `vs` (`Multidigraph.Arborescence`), shared
  with BEST-theorem Eulerian-circuit counting.
* `Cslib.Complexity.Graph.multiInArborescenceCount_eq_natCard`,
  `Cslib.Complexity.Graph.computableInPolyTime_multiInArborescenceCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_multiIsInArborescence`: exact count and
  polynomial-time computability for multidigraph spanning in-arborescences.
-/

public section

namespace Cslib.Complexity.Graph

open Turing MultiTapeTM

private theorem card_filter_fst_eq_sum_snd {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (src tgt : E → V) (u : V) :
    (Finset.univ.filter fun e => src e = u ∧ tgt e ≠ u).card =
      ∑ w : V, (Finset.univ.filter fun e => src e = u ∧ tgt e = w).card -
        (Finset.univ.filter fun e => src e = u ∧ tgt e = u).card := by
  classical
  have hsum :
      ∑ w : V, (Finset.univ.filter fun e => src e = u ∧ tgt e = w).card =
        (Finset.univ.filter fun e => src e = u).card := by
    simpa only [Finset.filter_filter, Finset.mem_univ, and_true] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter fun e => src e = u) Finset.univ tgt
  have hpart :
      (Finset.univ.filter fun e => src e = u ∧ tgt e ≠ u).card +
          (Finset.univ.filter fun e => src e = u ∧ tgt e = u).card =
        (Finset.univ.filter fun e => src e = u).card := by
    simpa only [Finset.filter_filter, ne_eq, not_not] using
      Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter fun e => src e = u) (fun e => tgt e ≠ u)
  omega

/-! ### Simple-digraph spanning in-arborescences -/

/-- The simple digraph induced by `G` on its declared vertices: `u → v` holds iff `(u.1, v.1)`
appears in `G.edges`. -/
@[expose]
def toDigraph (G : Graph) : Digraph {v // v ∈ G.vertices} where
  Adj u v := (u.1, v.1) ∈ G.edges

/-- Entry `(u, v)` of the out-degree integer Laplacian of `G.toDigraph`. -/
@[expose]
def digraphLaplacianEntry (G : Graph) (u v : ℕ) : ℤ :=
  if u = v then
    (G.distinctVertices.countP fun w =>
      decide (w ≠ u) && G.edges.any fun e => decide (e.1 = u ∧ e.2 = w) : ℤ)
  else if G.edges.any fun e => decide (e.1 = u ∧ e.2 = v) then -1 else 0

/-- Number of spanning in-arborescences of `G.toDigraph` rooted at `r` (`0` if `r ∉ G.vertices`),
computed via the reduced out-degree Laplacian determinant. -/
@[expose]
def digraphInArborescenceCount (G : Graph) (r : ℕ) : ℕ :=
  if G.distinctVertices.any fun v => decide (v = r) then
    let rest := G.distinctVertices.filter fun v => decide (v ≠ r)
    (Cslib.Circuits.Rational.detRows
      (rest.map fun u => rest.map fun v => G.digraphLaplacianEntry u v)).toNat
  else 0

private lemma any_eq_decide_mem (arcs : List (ℕ × ℕ)) (u v : ℕ) :
    (arcs.any fun e => decide (e.1 = u ∧ e.2 = v)) = decide ((u, v) ∈ arcs) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, decide_eq_true_eq, Prod.exists]
  exact ⟨fun ⟨a, b, hab, ha, hb⟩ => ha ▸ hb ▸ hab,
    fun h => ⟨u, v, h, rfl, rfl⟩⟩

open Classical in
private lemma digraphLaplacianEntry_eq (G : Graph) (u v : {v // v ∈ G.vertices}) :
    G.digraphLaplacianEntry u.1 v.1 = ((G.toDigraph.adjMatrix ℤ).laplacian u v) := by
  classical
  rw [Matrix.laplacian_apply]
  by_cases huv : u = v
  · subst huv
    simp only [digraphLaplacianEntry, ↓reduceIte]
    have hdiag :
        ((G.distinctVertices.countP fun w =>
          decide (w ≠ u.1) && G.edges.any fun e => decide (e.1 = u.1 ∧ e.2 = w) : ℤ)) =
          ((Finset.univ.filter fun w : {v // v ∈ G.vertices} =>
            G.toDigraph.Adj u w ∧ w ≠ u).card : ℤ) := by
      have hcard :
          G.distinctVertices.countP (fun w =>
              decide (w ≠ u.1) && G.edges.any fun e => decide (e.1 = u.1 ∧ e.2 = w)) =
            (Finset.univ.filter fun i : Fin G.distinctVertices.length =>
              (decide (G.distinctVertices[i] ≠ u.1) &&
                G.edges.any fun e =>
                  decide (e.1 = u.1 ∧ e.2 = G.distinctVertices[i])) = true).card :=
        List.countP_eq_card_filter_getElem G.distinctVertices _
      rw [hcard, Nat.cast_inj]
      refine Finset.card_bij (fun i _ => G.vertexEquiv i) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
          decide_eq_true_eq, any_eq_decide_mem] at hi ⊢
        refine ⟨?_, fun h =>
          hi.1 ((Graph.vertexEquiv_getElem G i).symm.trans (congrArg Subtype.val h))⟩
        change (u.1, (G.vertexEquiv i).1) ∈ G.edges
        rw [Graph.vertexEquiv_getElem]
        exact hi.2
      · intro i _ j _ hij
        exact G.vertexEquiv.injective hij
      · intro w hw
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
        obtain ⟨i, hi⟩ := G.vertexEquiv.surjective w
        refine ⟨i, ?_, hi⟩
        have hval : G.distinctVertices[i] = w.1 :=
          (Graph.vertexEquiv_getElem G i).symm.trans (congrArg Subtype.val hi)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
          decide_eq_true_eq, any_eq_decide_mem, hval]
        exact ⟨fun h => hw.2 (Subtype.ext h), hw.1⟩
    rw [hdiag]
    have hsum :
        (∑ w : {v // v ∈ G.vertices}, G.toDigraph.adjMatrix ℤ u w - G.toDigraph.adjMatrix ℤ u u) =
          ((Finset.univ.filter fun w : {v // v ∈ G.vertices} =>
            G.toDigraph.Adj u w ∧ w ≠ u).card : ℤ) := by
      simp only [Digraph.adjMatrix_apply, Finset.sum_boole]
      have hsub :
          (Finset.univ.filter fun w : {v // v ∈ G.vertices} => G.toDigraph.Adj u w ∧ w ≠ u).card +
              (Finset.univ.filter fun w : {v // v ∈ G.vertices} =>
                G.toDigraph.Adj u w ∧ w = u).card =
            (Finset.univ.filter fun w : {v // v ∈ G.vertices} => G.toDigraph.Adj u w).card := by
        simpa only [Finset.filter_filter, ne_eq, not_not] using
          Finset.card_filter_add_card_filter_not
            (s := Finset.univ.filter fun w : {v // v ∈ G.vertices} => G.toDigraph.Adj u w)
            (fun w => w ≠ u)
      have hself :
          (Finset.univ.filter fun w : {v // v ∈ G.vertices} => G.toDigraph.Adj u w ∧ w = u).card =
            if G.toDigraph.Adj u u then 1 else 0 := by
        split_ifs with h
        · rw [Finset.card_eq_one]
          exact ⟨u, Finset.ext fun w => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            exact ⟨fun hw => hw.2, fun hw => by subst hw; exact ⟨h, rfl⟩⟩⟩
        · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro w _ hw
          exact h (hw.2 ▸ hw.1)
      have hle : (if G.toDigraph.Adj u u then 1 else 0) ≤
          (Finset.univ.filter fun w : {v // v ∈ G.vertices} => G.toDigraph.Adj u w).card := by
        rw [← hself, ← hsub]; omega
      have hcast : ((if G.toDigraph.Adj u u then (1 : ℕ) else 0 : ℕ) : ℤ) =
          if G.toDigraph.Adj u u then (1 : ℤ) else 0 := by split_ifs <;> rfl
      rw [← hcast, ← Nat.cast_sub hle, Nat.cast_inj]
      omega
    exact hsum.symm
  · have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    simp only [digraphLaplacianEntry, hne, ↓reduceIte, huv, any_eq_decide_mem,
      Digraph.adjMatrix_apply, zero_sub, decide_eq_true_eq]
    dsimp only [toDigraph]
    by_cases hadj : (u.1, v.1) ∈ G.edges <;> simp [hadj]

/-- `G.digraphInArborescenceCount r` equals the number of spanning in-arborescences of
`G.toDigraph` rooted at `r` (and `0` when `r ∉ G.vertices`). -/
theorem digraphInArborescenceCount_eq_natCard (G : Graph) (r : ℕ) :
    G.digraphInArborescenceCount r =
      if hr : r ∈ G.vertices then
        Nat.card {T : Digraph {v // v ∈ G.vertices} // T ≤ G.toDigraph ∧ T.IsInArborescence ⟨r, hr⟩}
      else 0 := by
  classical
  have hany : (G.distinctVertices.any fun v => decide (v = r)) = true ↔ r ∈ G.vertices := by
    simp [Graph.mem_distinctVertices]
  by_cases hr : r ∈ G.vertices
  · have htrue : (G.distinctVertices.any fun v => decide (v = r)) = true := hany.2 hr
    have hr_dist : r ∈ G.distinctVertices := Graph.mem_distinctVertices.2 hr
    simp only [digraphInArborescenceCount, htrue, ↓reduceIte]
    rw [dite_eq_left hr]
    have hdet := detRows_filter_ne_equiv_eq G.nodup_distinctVertices
      (Equiv.subtypeEquivRight fun _ => Graph.mem_distinctVertices) hr_dist
      (G.toDigraph.adjMatrix ℤ).laplacian G.digraphLaplacianEntry
      fun u v _ _ => G.digraphLaplacianEntry_eq ⟨u.1, Graph.mem_distinctVertices.1 u.2⟩
        ⟨v.1, Graph.mem_distinctVertices.1 v.2⟩
    rw [hdet, Digraph.det_laplacian_adjMatrix_submatrix_eq_natCard_isInArborescence]
    exact Int.toNat_natCast _
  · have hfalse : (G.distinctVertices.any fun v => decide (v = r)) = false :=
      Bool.eq_false_iff.2 (fun h => hr (hany.1 h))
    simp [digraphInArborescenceCount, hfalse, hr]

/-! ### Multidigraph spanning in-arborescences -/

/-- Directed pairs `(u, v)` listed in `G.edges` whose both endpoints lie in `G.vertices`, preserving
multiplicity. -/
@[expose]
def validArcs (G : Graph) : List (ℕ × ℕ) :=
  G.edges.filter fun e =>
    G.vertices.any (fun v => decide (v = e.1)) && G.vertices.any fun v => decide (v = e.2)

theorem mem_validArcs {G : Graph} {e : ℕ × ℕ} :
    e ∈ G.validArcs ↔ e ∈ G.edges ∧ e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices := by
  simp [validArcs]

theorem mem_validArcs_fst {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.1 ∈ G.vertices := by
  rcases mem_validArcs.1 he with ⟨_, h1, _⟩
  exact h1

theorem mem_validArcs_snd {G : Graph} {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.2 ∈ G.vertices := by
  rcases mem_validArcs.1 he with ⟨_, _, h2⟩
  exact h2

/-- Source vertex of an arc in `G.validArcs`. -/
@[expose]
def arcSrc (G : Graph) (e : Fin G.validArcs.length) : {v // v ∈ G.vertices} :=
  ⟨G.validArcs[e].1, mem_validArcs_fst (List.getElem_mem e.isLt)⟩

/-- Target vertex of an arc in `G.validArcs`. -/
@[expose]
def arcTgt (G : Graph) (e : Fin G.validArcs.length) : {v // v ∈ G.vertices} :=
  ⟨G.validArcs[e].2, mem_validArcs_snd (List.getElem_mem e.isLt)⟩

/-- Entry `(u, v)` of the out-degree integer Laplacian of the multidigraph with arc list `arcs`. -/
@[expose]
def multiLaplacianEntry (arcs : List (ℕ × ℕ)) (u v : ℕ) : ℤ :=
  if u = v then (arcs.countP fun e => decide (e.1 = u ∧ e.2 ≠ u) : ℤ)
  else -(arcs.countP fun e => decide (e.1 = u ∧ e.2 = v) : ℤ)

/-- Determinant of the reduced multidigraph Laplacian on duplicate-free vertex list `vs` after
deleting vertex `r`, converted to `ℕ`. -/
@[expose]
def multiLaplacianCount (vs : List ℕ) (arcs : List (ℕ × ℕ)) (r : ℕ) : ℕ :=
  let rest := vs.filter fun v => decide (v ≠ r)
  (Cslib.Circuits.Rational.detRows
    (rest.map fun u => rest.map fun v => multiLaplacianEntry arcs u v)).toNat

/-- Number of spanning in-arborescences of the multidigraph `(G.arcSrc, G.arcTgt)` rooted at `r`
(`0` if `r ∉ G.vertices`). -/
@[expose]
def multiInArborescenceCount (G : Graph) (r : ℕ) : ℕ :=
  if G.distinctVertices.any fun v => decide (v = r) then
    multiLaplacianCount G.distinctVertices G.validArcs r
  else 0

private lemma multiLaplacianEntry_eq {mem : ℕ → Prop} [Fintype {v // mem v}]
    (arcs : List (ℕ × ℕ)) (harcs : ∀ e ∈ arcs, mem e.1 ∧ mem e.2) (u v : {v // mem v}) :
    let src : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
    let tgt : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
    multiLaplacianEntry arcs u.1 v.1 = ((Multidigraph.arcMatrix src tgt ℤ).laplacian u v) := by
  classical
  intro src tgt
  rw [Matrix.laplacian_apply]
  by_cases huv : u = v
  · subst huv
    simp only [multiLaplacianEntry, ↓reduceIte, Multidigraph.arcMatrix_apply,
      ← Nat.cast_sum]
    have hle : (Finset.univ.filter fun e => src e = u ∧ tgt e = u).card ≤
        ∑ w : {v // mem v}, (Finset.univ.filter fun e => src e = u ∧ tgt e = w).card :=
      Finset.single_le_sum
        (f := fun w : {v // mem v} => (Finset.univ.filter fun e => src e = u ∧ tgt e = w).card)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
    rw [← Nat.cast_sub hle, ← card_filter_fst_eq_sum_snd src tgt u, Nat.cast_inj,
      List.countP_eq_card_filter_getElem]
    congr 1
    ext i
    simp [src, tgt, Subtype.ext_iff]
  · have hne : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    simp only [multiLaplacianEntry, hne, ↓reduceIte, huv, Multidigraph.arcMatrix_apply, zero_sub,
      neg_inj, Nat.cast_inj, List.countP_eq_card_filter_getElem]
    congr 1
    ext i
    simp [src, tgt, Subtype.ext_iff]

/-- General directed matrix-tree reduction for `multiLaplacianCount`: for any duplicate-free list
`vs` (characterizing `mem : ℕ → Prop`) closed under both endpoints of every arc in `arcs`, and any
root `r ∈ vs`, `multiLaplacianCount vs arcs r` equals the number of spanning in-arborescences
rooted at `⟨r, _⟩`. -/
theorem multiLaplacianCount_eq_natCard {vs : List ℕ} (hnd : vs.Nodup) {mem : ℕ → Prop}
    (hmem : ∀ v, v ∈ vs ↔ mem v) (arcs : List (ℕ × ℕ))
    (harcs : ∀ e ∈ arcs, mem e.1 ∧ mem e.2) {r : ℕ} (hr : r ∈ vs) :
    let src : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
    let tgt : Fin arcs.length → {v // mem v} := fun i =>
      ⟨arcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
    multiLaplacianCount vs arcs r =
      Nat.card {f : {v : {v // mem v} // v ≠ ⟨r, (hmem r).1 hr⟩} → Fin arcs.length //
        Multidigraph.IsInArborescence src tgt ⟨r, (hmem r).1 hr⟩ f} := by
  classical
  intro src tgt
  let : Fintype {v // mem v} :=
    Fintype.ofEquiv {v // v ∈ vs} (Equiv.subtypeEquivRight hmem)
  let e : {v // v ∈ vs} ≃ {v // mem v} := Equiv.subtypeEquivRight hmem
  have hdet := detRows_filter_ne_equiv_eq hnd e hr
    (Multidigraph.arcMatrix src tgt ℤ).laplacian (multiLaplacianEntry arcs)
    fun u v _ _ => multiLaplacianEntry_eq arcs harcs (e u) (e v)
  change (Cslib.Circuits.Rational.detRows _).toNat = _
  rw [hdet, Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence]
  exact Int.toNat_natCast _

/-- `G.multiInArborescenceCount r` equals the number of multidigraph spanning in-arborescences
of `(G.arcSrc, G.arcTgt)` rooted at `r` (and `0` if `r ∉ G.vertices`). -/
theorem multiInArborescenceCount_eq_natCard (G : Graph) (r : ℕ) :
    G.multiInArborescenceCount r =
      if hr : r ∈ G.vertices then
        Nat.card {f : {v : {v // v ∈ G.vertices} // v ≠ ⟨r, hr⟩} → Fin G.validArcs.length //
          Multidigraph.IsInArborescence G.arcSrc G.arcTgt ⟨r, hr⟩ f}
      else 0 := by
  classical
  have hany : (G.distinctVertices.any fun v => decide (v = r)) = true ↔ r ∈ G.vertices := by
    simp [Graph.mem_distinctVertices]
  by_cases hr : r ∈ G.vertices
  · have htrue : (G.distinctVertices.any fun v => decide (v = r)) = true := hany.2 hr
    have hr_dist : r ∈ G.distinctVertices := Graph.mem_distinctVertices.2 hr
    simp only [multiInArborescenceCount, htrue, ↓reduceIte]
    rw [dite_eq_left hr]
    exact multiLaplacianCount_eq_natCard G.nodup_distinctVertices
      (fun _ => Graph.mem_distinctVertices) G.validArcs
      (fun _ he => (mem_validArcs.1 he).2) hr_dist
  · have hfalse : (G.distinctVertices.any fun v => decide (v = r)) = false :=
      Bool.eq_false_iff.2 (fun h => hr (hany.1 h))
    simp [multiInArborescenceCount, hfalse, hr]

/-! ### Polynomial-time computability -/

private lemma computableInPolyTime_hasArc {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → Graph} (hg : ComputableInPolyTime g encIn encGraph) :
    ComputableInPolyTime
      (fun q : ((γ × ℕ) × ℕ) => (g q.1.1).edges.any fun e => decide (e.1 = q.1.2 ∧ e.2 = q.2))
      (encPair (encPair encIn encNat) encNat) encBool := by
  refine ComputableInPolyTime.anyWithInput (encA := encPair encNat encNat) ?_ ?_
  · have he : ComputableInPolyTime (fun x : Graph => x.edges) encGraph
        (encList (encPair encNat encNat)) := by fun_prop
    exact (he.comp hg).comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
  · fun_prop

@[fun_prop]
theorem computableInPolyTime_digraphLaplacianEntry :
    ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => p.1.1.digraphLaplacianEntry p.1.2 p.2)
      (encPair (encPair encGraph encNat) encNat) encIntBin := by
  have hhas : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ =>
        p.1.1.edges.any fun e => decide (e.1 = p.1.2 ∧ e.2 = p.2))
      (encPair (encPair encGraph encNat) encNat) encBool :=
    computableInPolyTime_hasArc (ComputableInPolyTime.id' (encIn := encGraph))
  have hdiag : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ =>
        (p.1.1.distinctVertices.countP fun w =>
          decide (w ≠ p.1.2) && p.1.1.edges.any fun e => decide (e.1 = p.1.2 ∧ e.2 = w) : ℤ))
      (encPair (encPair encGraph encNat) encNat) encIntBin := by
    have hverts : ComputableInPolyTime
        (fun p : (Graph × ℕ) × ℕ => p.1.1.distinctVertices)
        (encPair (encPair encGraph encNat) encNat) (encList encNat) :=
      computableInPolyTime_distinctVertices.comp
        ((ComputableInPolyTime.fst encGraph encNat).comp
          (ComputableInPolyTime.fst (encPair encGraph encNat) encNat))
    have hcnt : ComputableInPolyTime
        (fun p : (Graph × ℕ) × ℕ =>
          p.1.1.distinctVertices.countP fun w =>
            decide (w ≠ p.1.2) && p.1.1.edges.any fun e => decide (e.1 = p.1.2 ∧ e.2 = w))
        (encPair (encPair encGraph encNat) encNat) encUnary := by
      refine ComputableInPolyTime.countPWithInput hverts ?_
      have hne : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ => decide (q.2 ≠ q.1.1.2))
          (encPair (encPair (encPair encGraph encNat) encNat) encNat) encBool := by
        have heq := (ComputableInPolyTime.snd (encPair (encPair encGraph encNat) encNat)
          encNat).decide_eq'
          ((ComputableInPolyTime.snd encGraph encNat).comp
            ((ComputableInPolyTime.fst (encPair encGraph encNat) encNat).comp
              (ComputableInPolyTime.fst (encPair (encPair encGraph encNat) encNat) encNat)))
        simpa only [Function.comp_def, decide_not] using ComputableInPolyTime.bool_not.comp heq
      have hedge : ComputableInPolyTime
          (fun q : ((Graph × ℕ) × ℕ) × ℕ =>
            q.1.1.1.edges.any fun e => decide (e.1 = q.1.1.2 ∧ e.2 = q.2))
          (encPair (encPair (encPair encGraph encNat) encNat) encNat) encBool := by
        have hproj : ComputableInPolyTime
            (fun q : ((Graph × ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.1.2), q.2))
            (encPair (encPair (encPair encGraph encNat) encNat) encNat)
            (encPair (encPair encGraph encNat) encNat) := by fun_prop
        exact hhas.comp hproj
      exact ComputableInPolyTime.bool_and.comp (hne.prod hedge)
    exact ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp hcnt)
  have hoff : ComputableInPolyTime
      (fun p : (Graph × ℕ) × ℕ =>
        if p.1.1.edges.any fun e => decide (e.1 = p.1.2 ∧ e.2 = p.2) then (-1 : ℤ) else 0)
      (encPair (encPair encGraph encNat) encNat) encIntBin :=
    ComputableInPolyTime.ite' hhas (ComputableInPolyTime.const (-1))
      (ComputableInPolyTime.const 0)
  have heq : ComputableInPolyTime (fun p : (Graph × ℕ) × ℕ => decide (p.1.2 = p.2))
      (encPair (encPair encGraph encNat) encNat) encBool :=
    ((ComputableInPolyTime.snd encGraph encNat).comp
      (ComputableInPolyTime.fst (encPair encGraph encNat) encNat)).decide_eq'
      (ComputableInPolyTime.snd (encPair encGraph encNat) encNat)
  refine (ComputableInPolyTime.ite' heq hdiag hoff).of_enc_eq fun p => ?_
  simp [digraphLaplacianEntry]

/-- `Graph.digraphInArborescenceCount` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_digraphInArborescenceCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.digraphInArborescenceCount p.2)
      (encPair encGraph encNat) encNat := by
  have hverts : ComputableInPolyTime (fun p : Graph × ℕ => p.1.distinctVertices)
      (encPair encGraph encNat) (encList encNat) :=
    computableInPolyTime_distinctVertices.comp (ComputableInPolyTime.fst encGraph encNat)
  have hr_mem : ComputableInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.any fun v => decide (v = p.2))
      (encPair encGraph encNat) encBool := by
    refine ComputableInPolyTime.anyWithInput hverts ?_
    exact (ComputableInPolyTime.snd _ _).decide_eq'
      ((ComputableInPolyTime.snd encGraph encNat).comp (ComputableInPolyTime.fst _ _))
  have hrest : ComputableInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.filter fun v => decide (v ≠ p.2))
      (encPair encGraph encNat) (encList encNat) :=
    computableInPolyTime_filter_ne hverts (ComputableInPolyTime.snd encGraph encNat)
  have hentry : ComputableInPolyTime
      (fun q : ((Graph × ℕ) × ℕ) × ℕ => q.1.1.1.digraphLaplacianEntry q.1.2 q.2)
      (encPair (encPair (encPair encGraph encNat) encNat) encNat) encIntBin := by
    have hproj : ComputableInPolyTime
        (fun q : ((Graph × ℕ) × ℕ) × ℕ => ((q.1.1.1, q.1.2), q.2))
        (encPair (encPair (encPair encGraph encNat) encNat) encNat)
        (encPair (encPair encGraph encNat) encNat) := by fun_prop
    exact computableInPolyTime_digraphLaplacianEntry.comp hproj
  have hdet : ComputableInPolyTime
      (fun p : Graph × ℕ =>
        (Cslib.Circuits.Rational.detRows
          ((p.1.distinctVertices.filter fun v => decide (v ≠ p.2)).map fun u =>
            (p.1.distinctVertices.filter fun v => decide (v ≠ p.2)).map fun v =>
              p.1.digraphLaplacianEntry u v)).toNat)
      (encPair encGraph encNat) encNat :=
    ComputableInPolyTime.intBin_toNat.comp (computableInPolyTime_detRows_map hrest hentry)
  exact ComputableInPolyTime.ite' hr_mem hdet (ComputableInPolyTime.const 0)

/-- The number of spanning in-arborescences of a simple digraph `G.toDigraph` rooted at `r` is
computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_digraphIsInArborescence :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.vertices then
          Nat.card {T : Digraph {v // v ∈ p.1.vertices} //
            T ≤ p.1.toDigraph ∧ T.IsInArborescence ⟨p.2, hr⟩}
        else 0)
      (encPair encGraph encNat) encNat := by
  refine computableInPolyTime_digraphInArborescenceCount.of_enc_eq fun p => ?_
  rw [digraphInArborescenceCount_eq_natCard]

/-- Binary encoding of a list of directed arcs `(ℕ × ℕ)`. -/
abbrev encArcList : List (ℕ × ℕ) ↪ List Bool :=
  encList (encPair encNat encNat)

@[fun_prop]
theorem computableInPolyTime_validArcs :
    ComputableInPolyTime validArcs encGraph encArcList := by
  have h1 : ComputableInPolyTime (fun G : Graph => G.vertices) encGraph (encList encNat) := by
    fun_prop
  have h2 : ComputableInPolyTime (fun G : Graph => G.edges) encGraph
      (encList (encPair encNat encNat)) := by
    fun_prop
  refine ComputableInPolyTime.filterWithInput h2 ?_
  have hs1 : ComputableInPolyTime
      (fun q : Graph × (ℕ × ℕ) => q.1.vertices.any fun v => decide (v = q.2.1))
      (encPair encGraph (encPair encNat encNat)) encBool := by
    refine ComputableInPolyTime.anyWithInput (h1.comp (ComputableInPolyTime.fst _ _)) ?_
    exact (ComputableInPolyTime.snd _ _).decide_eq'
      ((ComputableInPolyTime.fst encNat encNat).comp
        ((ComputableInPolyTime.snd encGraph (encPair encNat encNat)).comp
          (ComputableInPolyTime.fst _ _)))
  have hs2 : ComputableInPolyTime
      (fun q : Graph × (ℕ × ℕ) => q.1.vertices.any fun v => decide (v = q.2.2))
      (encPair encGraph (encPair encNat encNat)) encBool := by
    refine ComputableInPolyTime.anyWithInput (h1.comp (ComputableInPolyTime.fst _ _)) ?_
    exact (ComputableInPolyTime.snd _ _).decide_eq'
      ((ComputableInPolyTime.snd encNat encNat).comp
        ((ComputableInPolyTime.snd encGraph (encPair encNat encNat)).comp
          (ComputableInPolyTime.fst _ _)))
  exact ComputableInPolyTime.bool_and.comp (hs1.prod hs2)

@[fun_prop]
theorem computableInPolyTime_multiLaplacianEntry {γ : Type} {encIn : γ ↪ List Bool}
    {arcs : γ → List (ℕ × ℕ)}
    (harcs : ComputableInPolyTime arcs encIn encArcList) :
    ComputableInPolyTime
      (fun p : (γ × ℕ) × ℕ => multiLaplacianEntry (arcs p.1.1) p.1.2 p.2)
      (encPair (encPair encIn encNat) encNat) encIntBin := by
  have harcs' : ComputableInPolyTime (fun p : (γ × ℕ) × ℕ => arcs p.1.1)
      (encPair (encPair encIn encNat) encNat) (encList (encPair encNat encNat)) :=
    harcs.comp ((ComputableInPolyTime.fst encIn encNat).comp (ComputableInPolyTime.fst _ _))
  have hdiag : ComputableInPolyTime
      (fun p : (γ × ℕ) × ℕ =>
        ((arcs p.1.1).countP fun e => decide (e.1 = p.1.2 ∧ e.2 ≠ p.1.2) : ℤ))
      (encPair (encPair encIn encNat) encNat) encIntBin := by
    have hcnt : ComputableInPolyTime
        (fun p : (γ × ℕ) × ℕ =>
          (arcs p.1.1).countP fun e => decide (e.1 = p.1.2 ∧ e.2 ≠ p.1.2))
        (encPair (encPair encIn encNat) encNat) encUnary := by
      refine ComputableInPolyTime.countPWithInput harcs' ?_
      fun_prop
    exact ComputableInPolyTime.intBin_natCast.comp
      (ComputableInPolyTime.unary_to_binary.comp hcnt)
  have hoff : ComputableInPolyTime
      (fun p : (γ × ℕ) × ℕ =>
        (0 : ℤ) - ((arcs p.1.1).countP fun e => decide (e.1 = p.1.2 ∧ e.2 = p.2) : ℤ))
      (encPair (encPair encIn encNat) encNat) encIntBin := by
    have hcnt : ComputableInPolyTime
        (fun p : (γ × ℕ) × ℕ =>
          (arcs p.1.1).countP fun e => decide (e.1 = p.1.2 ∧ e.2 = p.2))
        (encPair (encPair encIn encNat) encNat) encUnary := by
      refine ComputableInPolyTime.countPWithInput harcs' ?_
      fun_prop
    exact ComputableInPolyTime.intBin_sub' (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.intBin_natCast.comp (ComputableInPolyTime.unary_to_binary.comp hcnt))
  have heq : ComputableInPolyTime (fun p : (γ × ℕ) × ℕ => decide (p.1.2 = p.2))
      (encPair (encPair encIn encNat) encNat) encBool :=
    ((ComputableInPolyTime.snd encIn encNat).comp
      (ComputableInPolyTime.fst (encPair encIn encNat) encNat)).decide_eq'
      (ComputableInPolyTime.snd (encPair encIn encNat) encNat)
  refine (ComputableInPolyTime.ite' heq hdiag hoff).of_enc_eq fun p => ?_
  by_cases huv : p.1.2 = p.2 <;> simp [multiLaplacianEntry, huv]

/-- `multiLaplacianCount` is computable in polynomial time whenever its vertex list, arc list,
and root vertex are. -/
@[fun_prop]
theorem computableInPolyTime_multiLaplacianCount {γ : Type} {encIn : γ ↪ List Bool}
    {vs : γ → List ℕ} {arcs : γ → List (ℕ × ℕ)} {r : γ → ℕ}
    (hvs : ComputableInPolyTime vs encIn (encList encNat))
    (harcs : ComputableInPolyTime arcs encIn encArcList)
    (hr : ComputableInPolyTime r encIn encNat) :
    ComputableInPolyTime (fun x => multiLaplacianCount (vs x) (arcs x) (r x)) encIn encNat :=
  ComputableInPolyTime.intBin_toNat.comp
    (computableInPolyTime_detRows_map (computableInPolyTime_filter_ne hvs hr)
      (computableInPolyTime_multiLaplacianEntry harcs))

/-- `Graph.multiInArborescenceCount` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_multiInArborescenceCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.multiInArborescenceCount p.2)
      (encPair encGraph encNat) encNat := by
  have hverts : ComputableInPolyTime (fun p : Graph × ℕ => p.1.distinctVertices)
      (encPair encGraph encNat) (encList encNat) :=
    computableInPolyTime_distinctVertices.comp (ComputableInPolyTime.fst encGraph encNat)
  have hr_mem : ComputableInPolyTime
      (fun p : Graph × ℕ => p.1.distinctVertices.any fun v => decide (v = p.2))
      (encPair encGraph encNat) encBool := by
    refine ComputableInPolyTime.anyWithInput hverts ?_
    exact (ComputableInPolyTime.snd _ _).decide_eq'
      ((ComputableInPolyTime.snd encGraph encNat).comp (ComputableInPolyTime.fst _ _))
  have harcs : ComputableInPolyTime (fun p : Graph × ℕ => p.1.validArcs)
      (encPair encGraph encNat) (encList (encPair encNat encNat)) :=
    computableInPolyTime_validArcs.comp (ComputableInPolyTime.fst encGraph encNat)
  have hcnt := computableInPolyTime_multiLaplacianCount hverts harcs
    (ComputableInPolyTime.snd encGraph encNat)
  exact ComputableInPolyTime.ite' hr_mem hcnt (ComputableInPolyTime.const 0)

/-- The number of spanning in-arborescences of the multidigraph `(G.arcSrc, G.arcTgt)` rooted at
`r` is computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_multiIsInArborescence :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if hr : p.2 ∈ p.1.vertices then
          Nat.card {f : {v : {v // v ∈ p.1.vertices} // v ≠ ⟨p.2, hr⟩} → Fin p.1.validArcs.length //
            Multidigraph.IsInArborescence p.1.arcSrc p.1.arcTgt ⟨p.2, hr⟩ f}
        else 0)
      (encPair encGraph encNat) encNat := by
  refine computableInPolyTime_multiInArborescenceCount.of_enc_eq fun p => ?_
  rw [multiInArborescenceCount_eq_natCard]

end Cslib.Complexity.Graph
