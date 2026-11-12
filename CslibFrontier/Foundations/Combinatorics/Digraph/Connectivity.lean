/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/Connectivity.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.List.Chain
import Mathlib.Data.Finset.Card

/-!
# Directed paths, cuts and separators in digraphs

Pure graph-theoretic notions for Menger's theorem in directed graphs `Digraph V`:

* Simple directed `s`–`t` paths `Digraph.IsDipath` (duplicate-free vertex lists from `s` to `t`
  forming an adjacency chain).
* Arc cuts (`Digraph.IsArcCut`), outgoing arc cuts `δ^out(S)` (`Digraph.outArcs`), vertex cuts
  (`Digraph.IsVertexCut`), and `A`–`B` vertex separators (`Digraph.IsSeparator`).
* Pairwise arc-disjointness (`Digraph.ArcDisjoint`) and internal vertex-disjointness
  (`Digraph.InternallyDisjoint`).
* Weak duality and closed-set cut/separator certificates.

## Main definitions

* `Digraph.IsDipath`, `Digraph.ArcDisjoint`, `Digraph.InternallyDisjoint`: simple directed paths
  and disjointness predicates.
* `Digraph.IsArcCut`, `Digraph.IsVertexCut`, `Digraph.IsSeparator`, `Digraph.outArcs`: directed
  arc and vertex cuts / separators.

## Main results

* `Digraph.isVertexCut_iff_isSeparator`: single-terminal vertex cuts in terms of `IsSeparator`.
* `Digraph.isArcCut_outArcs`, `Digraph.isSeparator_of_forall_adj`,
  `Digraph.isVertexCut_of_forall_adj`: certificates for arc cuts, separators and vertex cuts.
* `Digraph.card_le_card_of_arcDisjoint_of_isArcCut`,
  `Digraph.card_le_card_of_internallyDisjoint_of_isVertexCut`,
  `Digraph.card_le_card_of_disjoint_of_isSeparator`: weak duality for arc-disjoint,
  internally disjoint, and vertex-disjoint directed paths.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], §4.1
-/

public section

namespace Digraph

variable {V : Type*}

/-- `p` is a simple directed `s`–`t` path in `G`: a duplicate-free vertex list starting at `s` and
ending at `t` whose consecutive pairs are arcs of `G`. -/
@[expose] def IsDipath (G : Digraph V) (s t : V) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some s ∧ p.getLast? = some t ∧ p.IsChain G.Adj

instance instDecidableIsDipath [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (s t : V)
    (p : List V) : Decidable (G.IsDipath s t p) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The consecutive pairs `p.zip p.tail` of `p` satisfy `r` iff `p` is an `r`-chain. -/
theorem isChain_iff_forall_mem_zip_tail {r : V → V → Prop} :
    ∀ {p : List V}, p.IsChain r ↔ ∀ e ∈ p.zip p.tail, r e.1 e.2
  | [] => by simp
  | [x] => by simp
  | x :: y :: rest => by
    rw [List.isChain_cons_cons, List.tail_cons, List.zip_cons_cons, List.forall_mem_cons,
      isChain_iff_forall_mem_zip_tail, List.tail_cons]

/-- The vertex lists `P i` are pairwise arc-disjoint: no directed step `(u, v)` occurs as a
consecutive pair in two distinct lists. -/
@[expose] def ArcDisjoint {ι : Type*} (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ e ∈ (P i).zip (P i).tail, e ∉ (P j).zip (P j).tail

/-- The vertex lists `P i` are pairwise internally disjoint with respect to `s` and `t`: two
distinct lists share no vertex other than `s` and `t`. -/
@[expose] def InternallyDisjoint {ι : Type*} (s t : V) (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ v ∈ P i, v ∈ P j → v = s ∨ v = t

/-- `C` is an `s`–`t` arc cut of `G`: every simple directed `s`–`t` path of `G` uses an arc in
`C`. -/
@[expose] def IsArcCut (G : Digraph V) (s t : V) (C : Finset (V × V)) : Prop :=
  ∀ p, G.IsDipath s t p → ∃ e ∈ p.zip p.tail, e ∈ C

/-- `T` is an `s`–`t` vertex cut of `G`: it avoids `s` and `t`, and every simple directed `s`–`t`
path of `G` visits a vertex of `T`. -/
@[expose] def IsVertexCut (G : Digraph V) (s t : V) (T : Finset V) : Prop :=
  s ∉ T ∧ t ∉ T ∧ ∀ p, G.IsDipath s t p → ∃ v ∈ p, v ∈ T

/-- `Y` separates `A` from `B` in `G`: every simple directed `A`–`B` path visits a vertex of `Y`.
A vertex of `A ∩ B` must lie in `Y`, because of its trivial one-vertex path. -/
@[expose] def IsSeparator (G : Digraph V) (A B Y : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ∀ p, G.IsDipath a b p → ∃ v ∈ p, v ∈ Y

theorem isVertexCut_iff_isSeparator {G : Digraph V} {s t : V} {T : Finset V} :
    G.IsVertexCut s t T ↔ s ∉ T ∧ t ∉ T ∧ G.IsSeparator {s} {t} ↑T := by
  refine ⟨fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩, fun ⟨hs, ht, h⟩ => ⟨hs, ht, ?_⟩⟩
  · rintro _ rfl _ rfl p hp
    exact h p hp
  · intro p hp
    exact h (Set.mem_singleton s) (Set.mem_singleton t) p hp

theorem IsSeparator.mono {G : Digraph V} {A B Y Y' : Set V} (h : G.IsSeparator A B Y)
    (hY : Y ⊆ Y') : G.IsSeparator A B Y' :=
  fun _ ha _ hb p hp => (h ha hb p hp).imp fun _ hx => ⟨hx.1, hY hx.2⟩

theorem isSeparator_of_subset_left {G : Digraph V} {A B Y : Set V} (h : A ⊆ Y) :
    G.IsSeparator A B Y := by
  intro a ha _ _ p ⟨_, hps, _, _⟩
  exact ⟨a, List.mem_of_head? hps, h ha⟩

/-- The arcs of `G` leaving a vertex set `S` (Schrijver's `δ^out(S)`). -/
@[expose] def outArcs [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (Finset.univ \ S)).filter fun e => G.Adj e.1 e.2

theorem mem_outArcs [Fintype V] [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj]
    {S : Finset V} {e : V × V} :
    e ∈ G.outArcs S ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp only [outArcs, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
    true_and, and_assoc]

/-- Any `G.Adj`-chain starting inside `S` and ending outside `S` has a consecutive pair leaving
`S`. -/
private theorem exists_boundary_zip_tail {G : Digraph V} {S : V → Prop} :
    ∀ {p : List V} {s t : V}, p.head? = some s → p.getLast? = some t →
      p.IsChain G.Adj → S s → ¬ S t → ∃ e ∈ p.zip p.tail, S e.1 ∧ ¬ S e.2 ∧ G.Adj e.1 e.2
  | [], _, _, hs, _, _, _, _ => by simp at hs
  | [x], s, t, hs, ht, _, hSs, hSt => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    simp only [List.getLast?_singleton, Option.some.injEq] at ht
    subst hs ht
    exact absurd hSs hSt
  | x :: y :: rest, s, t, hs, ht, hchain, hSs, hSt => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    subst hs
    rw [List.isChain_cons_cons] at hchain
    by_cases hy : S y
    · obtain ⟨e, he, hbd⟩ := exists_boundary_zip_tail (p := y :: rest) rfl (by simpa using ht)
        hchain.2 hy hSt
      exact ⟨e, List.mem_cons_of_mem (x, y) he, hbd⟩
    · exact ⟨(x, y), List.mem_cons_self, hSs, hy, hchain.1⟩

/-- `G.outArcs S` is an `s`–`t` arc cut whenever `s ∈ S` and `t ∉ S`. -/
theorem isArcCut_outArcs [Fintype V] [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    {s t : V} {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) : G.IsArcCut s t (G.outArcs S) := by
  rintro p ⟨_, hps, hpt, hchain⟩
  obtain ⟨e, he, heS, heS', hadj⟩ := exists_boundary_zip_tail hps hpt hchain hs ht
  exact ⟨e, he, mem_outArcs.mpr ⟨heS, heS', hadj⟩⟩

/-- Every `Y`-avoiding chain starting in `S` whose arcs out of `S` enter `Y` remains inside `S`. -/
private theorem prop_getLast_of_isChain {G : Digraph V} {S Y : V → Prop}
    (hstep : ∀ ⦃u v⦄, G.Adj u v → S u → ¬ Y v → S v) :
    ∀ {p : List V} {s t : V}, p.head? = some s → p.getLast? = some t →
      p.IsChain G.Adj → S s → (∀ x ∈ p, ¬ Y x) → S t
  | [], _, _, hs, _, _, _, _ => by simp at hs
  | [x], s, t, hs, ht, _, hSs, _ => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    simp only [List.getLast?_singleton, Option.some.injEq] at ht
    subst hs ht
    exact hSs
  | x :: y :: rest, s, t, hs, ht, hchain, hSs, hY => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    subst hs
    rw [List.isChain_cons_cons] at hchain
    have hSy := hstep hchain.1 hSs (hY y (List.mem_cons_of_mem x List.mem_cons_self))
    exact prop_getLast_of_isChain hstep (p := y :: rest) rfl (by simpa using ht) hchain.2 hSy
      fun z hz => hY z (List.mem_cons_of_mem x hz)

/-- **Closed-set certificate for directed separators.** If `S` holds on `A \ Y`, fails on `B \ Y`,
and every arc leaving `S` enters `Y`, then `Y` separates `A` from `B`. -/
theorem isSeparator_of_forall_adj {G : Digraph V} {A B Y : Set V} (S : V → Prop)
    (hstep : ∀ ⦃u v⦄, G.Adj u v → S u → v ∉ Y → S v)
    (hA : ∀ a ∈ A, a ∉ Y → S a) (hB : ∀ b ∈ B, b ∉ Y → ¬ S b) :
    G.IsSeparator A B Y := by
  intro a ha b hb p ⟨_, hps, hpt, hchain⟩
  by_contra hp
  push Not at hp
  have hSa := hA a ha (hp a (List.mem_of_head? hps))
  have hSb := prop_getLast_of_isChain hstep hps hpt hchain hSa hp
  exact hB b hb (hp b (List.mem_of_getLast? hpt)) hSb

/-- Closed-set certificate for a vertex cut: if `s ∈ S`, `t ∉ S`, `T` avoids `s` and `t`, and
every arc leaving `S` ends in `T`, then `T` is an `s`–`t` vertex cut. -/
theorem isVertexCut_of_forall_adj {G : Digraph V} {s t : V} {S T : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) (hsT : s ∉ T) (htT : t ∉ T) (hST : ∀ u ∈ S, ∀ v, G.Adj u v → v ∉ S → v ∈ T) :
    G.IsVertexCut s t T := by
  refine isVertexCut_iff_isSeparator.mpr ⟨hsT, htT, isSeparator_of_forall_adj (· ∈ S) ?_ ?_ ?_⟩
  · intro u v huv hu hv
    by_contra hvS
    exact hv (Finset.mem_coe.mpr (hST u hu v huv hvS))
  · rintro _ rfl _; exact hs
  · rintro _ rfl _; exact ht

/-- **Weak duality for arc-disjoint paths**: `k` pairwise arc-disjoint directed `s`–`t` paths need
at least `k` arcs in every `s`–`t` arc cut. -/
theorem card_le_card_of_arcDisjoint_of_isArcCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, G.IsDipath s t (P i)) (hdisj : ArcDisjoint P)
    {C : Finset (V × V)} (hC : G.IsArcCut s t C) : k ≤ C.card := by
  choose e he heC using fun i => hC (P i) (hP i)
  have hinj : Function.Injective fun i => (⟨e i, heC i⟩ : C) := by
    intro i j hij
    by_contra hne
    have heq : e i = e j := congrArg Subtype.val hij
    exact hdisj hne (e i) (he i) (heq ▸ he j)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **Weak duality for internally disjoint paths**: `k` pairwise internally disjoint directed
`s`–`t` paths need at least `k` vertices in every `s`–`t` vertex cut. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, G.IsDipath s t (P i)) (hdisj : InternallyDisjoint s t P)
    {T : Finset V} (hT : G.IsVertexCut s t T) : k ≤ T.card := by
  choose v hv hvT using fun i => hT.2.2 (P i) (hP i)
  have hinj : Function.Injective fun i => (⟨v i, hvT i⟩ : T) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    rcases hdisj hne (v i) (hv i) (heq ▸ hv j) with h | h
    · exact hT.1 (h ▸ hvT i)
    · exact hT.2.1 (h ▸ hvT i)
  simpa using Fintype.card_le_of_injective _ hinj

/-- **Weak duality for vertex-disjoint `A`–`B` paths**: `k` pairwise vertex-disjoint directed
`A`–`B` paths need at least `k` vertices in every `A`–`B` separator. -/
theorem card_le_card_of_disjoint_of_isSeparator {G : Digraph V} {A B : Set V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, ∃ a ∈ A, ∃ b ∈ B, G.IsDipath a b (P i))
    (hdisj : Pairwise fun i j => (P i).Disjoint (P j))
    {Y : Finset V} (hY : G.IsSeparator A B ↑Y) : k ≤ Y.card := by
  choose a ha b hb hPi using hP
  choose v hv hvY using fun i => hY (ha i) (hb i) (P i) (hPi i)
  have hinj : Function.Injective fun i => (⟨v i, hvY i⟩ : Y) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    exact hdisj hne (hv i) (heq ▸ hv j)
  simpa using Fintype.card_le_of_injective _ hinj

end Digraph
