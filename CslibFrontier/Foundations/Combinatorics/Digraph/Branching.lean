/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/Branching.lean`)

public import CslibFrontier.Foundations.Combinatorics.Digraph.Arborescence
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.Option
import CslibFrontier.Foundations.Combinatorics.FunctionalGraph
import Mathlib.Data.Finset.Card

/-!
# Branchings and out-arborescences

A digraph `B : Digraph V` is a **branching** (`Digraph.IsBranching`) in the sense of Edmonds
[Edmonds1967Branchings, Section 1] if every vertex has at most one incoming arc and there are no
directed cycles (so `B` is a directed forest of disjoint out-arborescences, with arcs directed away
from the roots). A **spanning out-arborescence** rooted at `r` (`Digraph.IsOutArborescence`) is
a digraph whose reversal is a spanning in-arborescence rooted at `r` (`Digraph.IsInArborescence`).

To connect optimum branchings directly with rooted minimum-cost spanning in-arborescence
algorithms, this module constructs the `Option V` super-root correspondence
(`Digraph.superRootExtend`, `Digraph.restrictOption`): adjoining a super-root `none` with an arc
`some v → none` for every vertex `v` without an incoming arc identifies the branchings `B ≤ G`
with the spanning in-arborescences `T ≤ Digraph.superRootDigraph G` rooted at `none`
(`Digraph.isBranching_iff_isInArborescence_superRootExtend`, `Digraph.restrictOption_spec`).

## Main definitions

* `Digraph.reverse`: reverse all arcs of a digraph.
* `Digraph.IsOutArborescence`, `Digraph.outParentDigraph`: spanning out-arborescences and parent
  representations with arcs `p v → v`.
* `Digraph.IsBranching`: digraphs in which each vertex has at most one incoming arc and no
  directed cycles exist.
* `Digraph.branchingDigraph`: the digraph of a parent-towards-root map `p : V → V` with fixed
  points acting as roots.
* `Digraph.superRootDigraph`, `Digraph.superRootExtend`, `Digraph.restrictOption`: the `Option V`
  super-root bijection between branchings of `G` and spanning in-arborescences rooted at `none`.

## Main results

* `Digraph.isOutArborescence_iff`, `Digraph.isOutArborescence_outParentDigraph_iff`:
  characterizations of spanning out-arborescences.
* `Digraph.isBranching_branchingDigraph_iff`, `Digraph.IsBranching.exists_branchingDigraph_eq`:
  parent-map characterization of finite branchings.
* `Digraph.isBranching_iff_isInArborescence_superRootExtend`, `Digraph.restrictOption_spec`:
  bijection with spanning in-arborescences on `Option V` rooted at `none`.
* `Digraph.IsBranching.card_arcs_le`, `Digraph.IsBranching.isOutArborescence_iff_card_arcs`:
  a finite branching on `n` vertices has at most `n - 1` arcs, with equality iff it is a spanning
  out-arborescence ([Edmonds1967Branchings, Section 1]).
* `Digraph.IsBranching.toSimpleGraph_isAcyclic`: every branching has an acyclic underlying simple
  graph.

## References

* [J. Edmonds, *Optimum Branchings*][Edmonds1967Branchings], Sections 1 and 2
-/

public section

namespace Digraph

variable {V : Type*}

/-! ### Reversal and out-arborescences -/

/-- The reversal of `G`, having an arc `u → v` iff `G` has `v → u`. -/
@[expose] def reverse (G : Digraph V) : Digraph V where
  Adj u v := G.Adj v u

instance (G : Digraph V) [DecidableRel G.Adj] : DecidableRel G.reverse.Adj :=
  fun u v => inferInstanceAs (Decidable (G.Adj v u))

@[simp]
theorem reverse_adj {G : Digraph V} {u v : V} : G.reverse.Adj u v ↔ G.Adj v u := Iff.rfl

@[simp]
theorem reverse_reverse (G : Digraph V) : G.reverse.reverse = G := rfl

theorem reverse_le_iff {G H : Digraph V} : G.reverse ≤ H.reverse ↔ G ≤ H :=
  ⟨fun h _ _ huv => h huv, fun h _ _ huv => h huv⟩

/-- `T` is a **spanning out-arborescence rooted at `r`**: an oriented spanning tree with every arc
directed away from `r` (`T.reverse.IsInArborescence r`). -/
abbrev IsOutArborescence (T : Digraph V) (r : V) : Prop :=
  T.reverse.IsInArborescence r

theorem isOutArborescence_iff {T : Digraph V} {r : V} :
    T.IsOutArborescence r ↔
      (∀ u, ¬ T.Adj u r) ∧ (∀ v, v ≠ r → ∃! u, T.Adj u v) ∧
        ∀ v, Relation.ReflTransGen T.Adj r v := by
  refine ⟨fun h => ⟨h.not_adj_root, h.existsUnique_adj, fun v => ?_⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, fun v => ?_⟩⟩
  · exact Relation.reflTransGen_swap.mp (h.reachable v)
  · exact Relation.reflTransGen_swap.mpr (h3 v)

/-- The out-arborescence digraph of a parent map `p` rooted at `r`: arcs `p v → v` for `v ≠ r`. -/
@[expose] def outParentDigraph (r : V) (p : V → V) : Digraph V :=
  (parentDigraph r p).reverse

@[simp]
theorem outParentDigraph_adj {r : V} {p : V → V} {u v : V} :
    (outParentDigraph r p).Adj u v ↔ v ≠ r ∧ p v = u := Iff.rfl

/-- `outParentDigraph r p` is a spanning out-arborescence rooted at `r` iff iterating `p` reaches
`r` from every vertex. -/
theorem isOutArborescence_outParentDigraph_iff {r : V} {p : V → V} :
    (outParentDigraph r p).IsOutArborescence r ↔ ∀ v, ∃ n, p^[n] v = r := by
  rw [IsOutArborescence, outParentDigraph, reverse_reverse]
  exact isInArborescence_parentDigraph_iff

/-- Every spanning out-arborescence rooted at `r` is `outParentDigraph r p` for some parent map `p`
with `p r = r`. -/
theorem IsOutArborescence.exists_outParentDigraph_eq {T : Digraph V} {r : V}
    (hT : T.IsOutArborescence r) : ∃ p : V → V, p r = r ∧ outParentDigraph r p = T := by
  obtain ⟨p, hpr, hp⟩ := IsInArborescence.exists_parentDigraph_eq hT
  exact ⟨p, hpr, by rw [outParentDigraph, hp, reverse_reverse]⟩

/-! ### Branchings -/

/-- A digraph `B` is a **branching** [Edmonds1967Branchings, Section 1] if each vertex has at most
one incoming arc and `B` has no directed cycles. -/
structure IsBranching (B : Digraph V) : Prop where
  /-- Each vertex has at most one incoming arc. -/
  in_unique : ∀ ⦃u₁ u₂ v : V⦄, B.Adj u₁ v → B.Adj u₂ v → u₁ = u₂
  /-- `B` has no directed cycles (including self-loops). -/
  acyclic : ∀ ⦃v : V⦄, ¬ Relation.TransGen B.Adj v v

theorem IsBranching.loopless {B : Digraph V} (hB : B.IsBranching) (v : V) : ¬ B.Adj v v :=
  fun h => hB.acyclic (Relation.TransGen.single h)

theorem IsBranching.no_two_cycle {B : Digraph V} (hB : B.IsBranching) {u v : V}
    (huv : B.Adj u v) : ¬ B.Adj v u :=
  fun hvu => hB.acyclic (Relation.TransGen.tail (Relation.TransGen.single huv) hvu)

theorem IsBranching.anti {B B' : Digraph V} (hle : B' ≤ B) (hB : B.IsBranching) :
    B'.IsBranching where
  in_unique _ _ _ h1 h2 := hB.in_unique (hle h1) (hle h2)
  acyclic v hc := by
    have htr : ∀ {x y : V}, Relation.TransGen B'.Adj x y → Relation.TransGen B.Adj x y := by
      intro x y hxy
      induction hxy with
      | single h => exact Relation.TransGen.single (hle h)
      | tail _ h ih => exact Relation.TransGen.tail ih (hle h)
    exact hB.acyclic (htr hc)

theorem isBranching_bot (V : Type*) : (⊥ : Digraph V).IsBranching where
  in_unique _ _ _ h := by simp at h
  acyclic _ h := by
    have : ∀ x y : V, Relation.TransGen (⊥ : Digraph V).Adj x y → False := by
      intro x y hxy
      induction hxy with
      | single h => simp at h
      | tail _ h => simp at h
    exact this _ _ h

/-- Helper: following a walk in `outParentDigraph` backward tracks iterates of `p`. -/
private theorem transGen_outParentDigraph_iterate {r : V} {p : V → V} {x y : V}
    (hxy : Relation.TransGen (outParentDigraph r p).Adj x y) :
    ∃ k, 0 < k ∧ p^[k] y = x := by
  induction hxy with
  | single h => exact ⟨1, Nat.zero_lt_one, by simpa using h.2⟩
  | tail _ h ih =>
    obtain ⟨k, hk, hpk⟩ := ih
    exact ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply, h.2, hpk]⟩

/-- A spanning out-arborescence is a branching. -/
theorem IsBranching.of_isOutArborescence {T : Digraph V} {r : V} (hT : T.IsOutArborescence r) :
    T.IsBranching := by
  obtain ⟨p, hpr, rfl⟩ := hT.exists_outParentDigraph_eq
  refine ⟨fun _ _ _ h1 h2 => h1.2.symm.trans h2.2, fun v hc => ?_⟩
  have hne : v ≠ r := by
    cases hc with
    | single h => exact h.1
    | tail _ h => exact h.1
  obtain ⟨k, hk, hpk⟩ := transGen_outParentDigraph_iterate hc
  obtain ⟨n, hn⟩ := (isOutArborescence_outParentDigraph_iff.mp hT) v
  have hnk : n ≤ k * n := Nat.le_mul_of_pos_left n hk
  have hcyc : p^[k * n] v = v := (show Function.IsPeriodicPt p k v from hpk).mul_const n
  have hfix : p^[k * n] v = r := by
    rw [← Nat.sub_add_cancel hnk, Function.iterate_add_apply, hn, Function.iterate_fixed hpr]
  exact hne (hcyc.symm.trans hfix)

/-! ### Parent-map representation of branchings -/

/-- The digraph of a parent-towards-root map `p`: an arc `p v → v` whenever `p v ≠ v`. Vertices
with `p v = v` are the roots of the branching's component out-arborescences. -/
@[expose] def branchingDigraph (p : V → V) : Digraph V where
  Adj u v := p v ≠ v ∧ p v = u

instance [DecidableEq V] (p : V → V) : DecidableRel (branchingDigraph p).Adj :=
  fun u v => inferInstanceAs (Decidable (p v ≠ v ∧ p v = u))

@[simp]
theorem branchingDigraph_adj {p : V → V} {u v : V} :
    (branchingDigraph p).Adj u v ↔ p v ≠ v ∧ p v = u := Iff.rfl

private theorem transGen_branchingDigraph_iterate {p : V → V} {x y : V}
    (hxy : Relation.TransGen (branchingDigraph p).Adj x y) :
    ∃ k, 0 < k ∧ p^[k] y = x ∧ ∀ i < k, p (p^[i] y) ≠ p^[i] y := by
  induction hxy with
  | single h =>
    exact ⟨1, Nat.zero_lt_one, by simpa using h.2, fun i hi => by
      obtain rfl : i = 0 := by omega
      simpa using h.1⟩
  | @tail b c _ hbc ih =>
    obtain ⟨k, hk, hpk, hne⟩ := ih
    refine ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply, hbc.2, hpk], fun i hi => ?_⟩
    rcases i with _ | i
    · simpa using hbc.1
    · simpa only [Function.iterate_succ_apply, hbc.2] using hne i (Nat.succ_lt_succ_iff.mp hi)

/-- `branchingDigraph p` is a branching when iterating `p` from every vertex reaches a fixed point
(root). On finite vertex types the converse also holds. -/
theorem isBranching_branchingDigraph_of_reach_fixed {p : V → V}
    (hfix : ∀ v, ∃ n, p (p^[n] v) = p^[n] v) : (branchingDigraph p).IsBranching := by
  refine ⟨fun _ _ _ h1 h2 => h1.2.symm.trans h2.2, fun v hc => ?_⟩
  obtain ⟨k, hk, hpk, hne⟩ := transGen_branchingDigraph_iterate hc
  obtain ⟨n, hn⟩ := hfix v
  have hnk : n ≤ k * n := Nat.le_mul_of_pos_left n hk
  have hcyc : p^[k * n] v = v := (show Function.IsPeriodicPt p k v from hpk).mul_const n
  have hstab : ∀ m, p^[n + m] v = p^[n] v := fun m => by
    rw [Nat.add_comm, Function.iterate_add_apply, Function.iterate_fixed hn]
  have hr : p^[k * n] v = p^[n] v := by
    simpa only [Nat.add_sub_cancel' hnk] using hstab (k * n - n)
  have hfv : p v = v := by
    rw [← hcyc, hr]
    exact hn
  exact hne 0 hk (by simpa using hfv)

/-- On a finite vertex type, `branchingDigraph p` is a branching iff iterating `p` reaches a fixed
point from every vertex. -/
theorem isBranching_branchingDigraph_iff [Finite V] {p : V → V} :
    (branchingDigraph p).IsBranching ↔ ∀ v, ∃ n, p (p^[n] v) = p^[n] v := by
  refine ⟨fun hB v => ?_, isBranching_branchingDigraph_of_reach_fixed⟩
  have := Fintype.ofFinite V
  obtain ⟨n, hn⟩ := Cslib.FunctionalGraph.exists_iterate_mem_periodicPts p v
  refine ⟨n, ?_⟩
  set k := Function.minimalPeriod p (p^[n] v) with hk
  have hkpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts hn
  have hper : p^[k] (p^[n] v) = p^[n] v := Function.isPeriodicPt_minimalPeriod p _
  by_contra hne
  have hall : ∀ i < k, p (p^[i] (p^[n] v)) ≠ p^[i] (p^[n] v) := by
    intro i hi heq
    have hloop : p^[i] (p^[n] v) = p^[n] v := by
      calc p^[i] (p^[n] v) = p^[k - i] (p^[i] (p^[n] v)) :=
            (Function.iterate_fixed heq (k - i)).symm
        _ = p^[k] (p^[n] v) := by
            rw [← Function.iterate_add_apply, Nat.sub_add_cancel hi.le]
        _ = p^[n] v := hper
    exact hne (hloop ▸ heq)
  have htg : ∀ m, 0 < m → m ≤ k →
      Relation.TransGen (branchingDigraph p).Adj (p^[m] (p^[n] v)) (p^[n] v) := by
    intro m hm hmk
    induction m with
    | zero => exact absurd hm (Nat.lt_irrefl 0)
    | succ m ih =>
      rcases eq_or_lt_of_le (Nat.zero_le m) with rfl | hmpos
      · exact Relation.TransGen.single ⟨hall 0 hkpos, rfl⟩
      · exact Relation.TransGen.head ⟨hall m hmk, by rw [Function.iterate_succ_apply']⟩
          (ih hmpos (Nat.le_of_succ_le hmk))
  have hcycle : Relation.TransGen (branchingDigraph p).Adj (p^[n] v) (p^[n] v) := by
    have h0 := htg k hkpos le_rfl
    rwa [hper] at h0
  exact hB.acyclic hcycle

/-- Every branching is `branchingDigraph p` for a parent-towards-root map `p` fixing every vertex
with no incoming arc. -/
theorem IsBranching.exists_branchingDigraph_eq {B : Digraph V} (hB : B.IsBranching) :
    ∃ p : V → V, (∀ v, p v = v ↔ ¬ ∃ u, B.Adj u v) ∧ branchingDigraph p = B := by
  classical
  let p : V → V := fun v => if h : ∃ u, B.Adj u v then h.choose else v
  refine ⟨p, fun v => ?_, ?_⟩
  · constructor
    · intro hp hv
      have hspec : B.Adj (p v) v := by
        simpa only [p, dite_eq_left hv] using hv.choose_spec
      rw [hp] at hspec
      exact hB.loopless v hspec
    · intro hno
      simp [p, dite_eq_right hno]
  · ext u v
    constructor
    · rintro ⟨hne, rfl⟩
      by_cases hv : ∃ w, B.Adj w v
      · have hpv : p v = hv.choose := dite_eq_left hv
        exact hpv ▸ hv.choose_spec
      · exact absurd (dite_eq_right hv) hne
    · intro huv
      have hne : u ≠ v := fun h => hB.loopless v (h ▸ huv)
      have hv : ∃ w, B.Adj w v := ⟨u, huv⟩
      have hspec : B.Adj (p v) v := by
        simpa only [p, dite_eq_left hv] using hv.choose_spec
      have hpeq : p v = u := hB.in_unique hspec huv
      exact ⟨hpeq ▸ hne, hpeq⟩

/-! ### Super-root bijection on `Option V` -/

/-- The super-root augmentation of `G` on `Option V`: real arcs of `G` are reversed (`some v →
some u` iff `G.Adj u v`), and every vertex `some v` also has a rootward arc to `none`. -/
@[expose] def superRootDigraph (G : Digraph V) : Digraph (Option V) where
  Adj x y := match x, y with
    | some v, some u => G.Adj u v
    | some _, none => True
    | none, _ => False

instance (G : Digraph V) [DecidableRel G.Adj] : DecidableRel (superRootDigraph G).Adj :=
  fun x y => by
    cases x <;> cases y
    · exact inferInstanceAs (Decidable False)
    · exact inferInstanceAs (Decidable False)
    · exact inferInstanceAs (Decidable True)
    · exact inferInstanceAs (Decidable (G.Adj _ _))

@[simp]
theorem superRootDigraph_some_some (G : Digraph V) (u v : V) :
    (superRootDigraph G).Adj (some v) (some u) ↔ G.Adj u v := Iff.rfl

@[simp]
theorem superRootDigraph_some_none (G : Digraph V) (v : V) :
    (superRootDigraph G).Adj (some v) none := trivial

@[simp]
theorem superRootDigraph_none (G : Digraph V) (y : Option V) :
    ¬ (superRootDigraph G).Adj none y := by
  cases y <;> simp [superRootDigraph]

/-- Extend a subdigraph `B : Digraph V` to `Option V` by sending every vertex without an incoming
arc in `B` to `none`, and reversing existing arcs of `B`. -/
@[expose] def superRootExtend (B : Digraph V) : Digraph (Option V) where
  Adj x y := match x, y with
    | some v, some u => B.Adj u v
    | some v, none => ¬ ∃ u, B.Adj u v
    | none, _ => False

@[simp]
theorem superRootExtend_some_some (B : Digraph V) (u v : V) :
    (superRootExtend B).Adj (some v) (some u) ↔ B.Adj u v := Iff.rfl

@[simp]
theorem superRootExtend_some_none (B : Digraph V) (v : V) :
    (superRootExtend B).Adj (some v) none ↔ ¬ ∃ u, B.Adj u v := Iff.rfl

@[simp]
theorem superRootExtend_none (B : Digraph V) (y : Option V) :
    ¬ (superRootExtend B).Adj none y := by
  cases y <;> simp [superRootExtend]

theorem superRootExtend_le_superRootDigraph {B G : Digraph V} (hBG : B ≤ G) :
    superRootExtend B ≤ superRootDigraph G := by
  intro x y hxy
  cases x <;> cases y <;> first | exact False.elim hxy | exact trivial | exact hBG hxy

/-- Restrict an `Option V` digraph back to `V` by forgetting `none` and reversing real arcs. -/
@[expose] def restrictOption (T : Digraph (Option V)) : Digraph V where
  Adj u v := T.Adj (some v) (some u)

instance (T : Digraph (Option V)) [DecidableRel T.Adj] :
    DecidableRel (restrictOption T).Adj :=
  fun u v => inferInstanceAs (Decidable (T.Adj (some v) (some u)))

@[simp]
theorem restrictOption_adj (T : Digraph (Option V)) (u v : V) :
    (restrictOption T).Adj u v ↔ T.Adj (some v) (some u) := Iff.rfl

@[simp]
theorem restrictOption_superRootExtend (B : Digraph V) :
    restrictOption (superRootExtend B) = B := rfl

private theorem reflTransGen_superRootExtend_some {B : Digraph V} {u v : V}
    (h : Relation.ReflTransGen B.Adj u v) :
    Relation.ReflTransGen (superRootExtend B).Adj (some v) (some u) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single (show (superRootExtend B).Adj (some c) (some b) from hbc)) ih

/-- Helper: if `T` is an in-arborescence rooted at `none`, its restriction to `V` is acyclic. -/
private theorem transGen_superRoot_of_restrict {T : Digraph (Option V)} {x y : V}
    (h : Relation.TransGen (restrictOption T).Adj x y) :
    Relation.TransGen T.Adj (some y) (some x) := by
  induction h with
  | single h => exact Relation.TransGen.single h
  | tail _ hbc ih => exact Relation.TransGen.head hbc ih

/-- For a finite vertex type, a digraph `B` is a branching iff its super-root extension on
`Option V` is a spanning in-arborescence rooted at `none`. -/
theorem isBranching_iff_isInArborescence_superRootExtend [Finite V] {B : Digraph V} :
    B.IsBranching ↔ (superRootExtend B).IsInArborescence none := by
  classical
  constructor
  · intro hB
    obtain ⟨p, hproot, rfl⟩ := hB.exists_branchingDigraph_eq
    have hpfix : ∀ v, ∃ n, p (p^[n] v) = p^[n] v :=
      isBranching_branchingDigraph_iff.mp hB
    refine ⟨fun _ h => superRootExtend_none _ _ h, ?_, ?_⟩
    · rintro (_ | v) hne
      · exact absurd rfl hne
      · by_cases hv : ∃ u, (branchingDigraph p).Adj u v
        · have ⟨u, hu⟩ := hv
          refine ⟨some u, hu, ?_⟩
          rintro (_ | w) hw
          · exact absurd hv hw
          · exact congrArg some (hB.in_unique hw hu)
        · refine ⟨none, hv, ?_⟩
          rintro (_ | w) hw
          · rfl
          · exact absurd ⟨w, hw⟩ hv
    · rintro (_ | v)
      · exact Relation.ReflTransGen.refl
      · obtain ⟨n, hn⟩ := hpfix v
        have hreach : Relation.ReflTransGen (branchingDigraph p).Adj (p^[n] v) v := by
          clear hn
          induction n with
          | zero => exact Relation.ReflTransGen.refl
          | succ m ih =>
            by_cases hfix : p (p^[m] v) = p^[m] v
            · have hle : Relation.ReflTransGen (branchingDigraph p).Adj (p^[m] v) v := ih
              rw [Function.iterate_succ_apply', hfix]
              exact hle
            · refine Relation.ReflTransGen.head ⟨hfix, ?_⟩ ih
              rw [Function.iterate_succ_apply']
        have hstep := reflTransGen_superRootExtend_some hreach
        have hr0 : (superRootExtend (branchingDigraph p)).Adj (some (p^[n] v)) none := by
          rw [superRootExtend_some_none, ← hproot (p^[n] v)]
          exact hn
        exact hstep.trans (Relation.ReflTransGen.single hr0)
  · intro hT
    refine ⟨fun u₁ u₂ v h1 h2 => ?_, fun v hc => ?_⟩
    · exact Option.some.inj ((hT.existsUnique_adj (some v) (Option.some_ne_none v)).unique h1 h2)
    · have hc' : Relation.TransGen (superRootExtend B).Adj (some v) (some v) :=
        transGen_superRoot_of_restrict hc
      obtain ⟨p, hpr, hp⟩ := hT.exists_parentDigraph_eq
      rw [← hp] at hc'
      have hreach := (isInArborescence_parentDigraph_iff.mp (hp ▸ hT)) (some v)
      have hstep : ∀ {x y : Option V}, Relation.TransGen (parentDigraph none p).Adj x y →
          ∃ k, 0 < k ∧ p^[k] x = y := by
        intro x y hxy
        induction hxy with
        | single h => exact ⟨1, Nat.zero_lt_one, by simpa using h.2⟩
        | tail _ h ih =>
          obtain ⟨k, hk, hpk⟩ := ih
          exact ⟨k + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply', hpk, h.2]⟩
      obtain ⟨k, hk, hpk⟩ := hstep hc'
      obtain ⟨n, hn⟩ := hreach
      have hnk : n ≤ k * n := Nat.le_mul_of_pos_left n hk
      have hcyc : p^[k * n] (some v) = some v :=
        (show Function.IsPeriodicPt p k (some v) from hpk).mul_const n
      have hfix : p^[k * n] (some v) = none := by
        rw [← Nat.sub_add_cancel hnk, Function.iterate_add_apply, hn, Function.iterate_fixed hpr]
      exact Option.some_ne_none v (hcyc.symm.trans hfix)

/-- Every spanning in-arborescence `T` on `Option V` rooted at `none` restricts to a branching on
`V` whose super-root extension equals `T`, and `T ≤ superRootDigraph G` iff the branching lies in
`G`. -/
theorem restrictOption_spec [Finite V] {T : Digraph (Option V)} (hT : T.IsInArborescence none) :
    (restrictOption T).IsBranching ∧ superRootExtend (restrictOption T) = T ∧
      ∀ G : Digraph V, T ≤ superRootDigraph G → restrictOption T ≤ G := by
  have hext : superRootExtend (restrictOption T) = T := by
    ext x y
    rcases x with _ | v <;> rcases y with _ | u
    · simp [hT.not_adj_root]
    · simp [hT.not_adj_root]
    · simp only [superRootExtend_some_none, restrictOption_adj]
      constructor
      · intro hnone
        obtain ⟨y, hy, -⟩ := hT.existsUnique_adj (some v) (Option.some_ne_none v)
        cases y with
        | none => exact hy
        | some u => exact absurd ⟨u, hy⟩ hnone
      · rintro hvn ⟨u, hvu⟩
        exact Option.some_ne_none u ((hT.existsUnique_adj (some v) (Option.some_ne_none v)).unique
          hvu hvn)
    · simp
  refine ⟨isBranching_iff_isInArborescence_superRootExtend.mpr (hext ▸ hT), hext, fun G hTG => ?_⟩
  intro u v huv
  exact hTG (show T.Adj (some v) (some u) from huv)

/-! ### Arc counts, spanning out-arborescences, and undirected forests -/

/-- A finite nonempty branching has at least one root (a vertex with no incoming arc). -/
theorem IsBranching.exists_not_adj_into [Finite V] [Nonempty V] {B : Digraph V}
    (hB : B.IsBranching) :
    ∃ r : V, ∀ u : V, ¬ B.Adj u r := by
  obtain ⟨p, hp, rfl⟩ := hB.exists_branchingDigraph_eq
  obtain ⟨n, hn⟩ := isBranching_branchingDigraph_iff.mp hB (Classical.arbitrary V)
  refine ⟨p^[n] (Classical.arbitrary V), fun u hu => ?_⟩
  rw [hp] at hn
  exact absurd ⟨u, hu⟩ hn

section ArcCount

variable [Fintype V]

/-- Every vertex without an incoming arc in a branching is a root; the number of arcs plus the
number of roots equals the number of vertices. -/
theorem IsBranching.card_arcs_add_card_roots {B : Digraph V} [DecidableRel B.Adj]
    (hB : B.IsBranching) :
    (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card +
        (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card =
      Fintype.card V := by
  classical
  let arcs := Finset.univ.filter fun e : V × V => B.Adj e.1 e.2
  let nonroots := Finset.univ.filter fun v : V => ∃ u, B.Adj u v
  let roots := Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v
  have hbij : arcs.card = nonroots.card := by
    refine Finset.card_bij (fun e _ => e.2) ?_ ?_ ?_
    · intro e he
      have hadj : B.Adj e.1 e.2 := (Finset.mem_filter.mp he).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨e.1, hadj⟩⟩
    · intro e₁ he₁ e₂ he₂ heq
      have h1 : B.Adj e₁.1 e₁.2 := (Finset.mem_filter.mp he₁).2
      have h2 : B.Adj e₂.1 e₂.2 := (Finset.mem_filter.mp he₂).2
      exact Prod.ext (hB.in_unique h1 (heq ▸ h2)) heq
    · intro v hv
      obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hv).2
      exact ⟨(u, v), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, rfl⟩
  have hdisj : Disjoint nonroots roots :=
    Finset.disjoint_filter.mpr fun _ _ h h' => h' h
  have hunion : nonroots ∪ roots = Finset.univ := by
    ext v
    simpa [nonroots, roots] using Classical.em (∃ u, B.Adj u v)
  have hpart : nonroots.card + roots.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
  simpa [arcs, roots] using (congrArg (· + roots.card) hbij).trans hpart

/-- **Edmonds (1967, Section 1):** No branching on `n` vertices has more than `n - 1` arcs. -/
theorem IsBranching.card_arcs_le {B : Digraph V} [DecidableRel B.Adj] (hB : B.IsBranching) :
    (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card ≤ Fintype.card V - 1 := by
  rcases isEmpty_or_nonempty V with hempty | hne
  · simp [Fintype.card_eq_zero]
  · obtain ⟨r, hr⟩ := hB.exists_not_adj_into
    have hpos : 0 < (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card :=
      Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun ⟨u, hu⟩ => hr u hu⟩⟩
    have hsum := hB.card_arcs_add_card_roots
    omega

/-- **Edmonds (1967, Section 1):** A branching on `n ≥ 1` vertices is a spanning out-arborescence
iff it has `n - 1` arcs. -/
theorem IsBranching.isOutArborescence_iff_card_arcs [Nonempty V] {B : Digraph V}
    [DecidableRel B.Adj] (hB : B.IsBranching) :
    (∃ r : V, B.IsOutArborescence r) ↔
      (Finset.univ.filter fun e : V × V => B.Adj e.1 e.2).card = Fintype.card V - 1 := by
  have hsum := hB.card_arcs_add_card_roots
  constructor
  · rintro ⟨r, hT⟩
    have huniv : (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v) = {r} := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hv
        by_contra hvr
        obtain ⟨u, hu, -⟩ := (isOutArborescence_iff.mp hT).2.1 v hvr
        exact hv ⟨u, hu⟩
      · rintro rfl ⟨u, hu⟩
        exact (isOutArborescence_iff.mp hT).1 u hu
    rw [huniv, Finset.card_singleton] at hsum
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    omega
  · intro hcard
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    have hroots : (Finset.univ.filter fun v : V => ¬ ∃ u, B.Adj u v).card = 1 := by omega
    obtain ⟨r, hrset⟩ := Finset.card_eq_one.mp hroots
    have hmem : ∀ v, (¬ ∃ u, B.Adj u v) ↔ v = r := fun v => by
      have := Finset.ext_iff.mp hrset v
      simpa using this
    refine ⟨r, isOutArborescence_iff.mpr ⟨fun u hu => (hmem r).mpr rfl ⟨u, hu⟩, ?_, ?_⟩⟩
    · intro v hvr
      have hex : ∃ u, B.Adj u v := by
        by_contra hv
        exact hvr ((hmem v).mp hv)
      obtain ⟨u, hu⟩ := hex
      exact ⟨u, hu, fun w hw => hB.in_unique hw hu⟩
    · obtain ⟨p, hp, hpeq⟩ := hB.exists_branchingDigraph_eq
      subst hpeq
      intro v
      obtain ⟨n, hn⟩ := isBranching_branchingDigraph_iff.mp hB v
      have hfix : p^[n] v = r := (hmem _).mp ((hp _).mp hn)
      have hwalk : ∀ m, Relation.ReflTransGen (branchingDigraph p).Adj (p^[m] v) v := by
        intro m
        induction m with
        | zero => exact Relation.ReflTransGen.refl
        | succ m ih =>
          by_cases hpm : p (p^[m] v) = p^[m] v
          · rw [Function.iterate_succ_apply', hpm]
            exact ih
          · refine Relation.ReflTransGen.head ⟨hpm, ?_⟩ ih
            rw [Function.iterate_succ_apply']
      simpa [hfix] using hwalk n

end ArcCount

/-! ### Acyclicity of the underlying undirected simple graph -/

/-- Along any non-nil trail of `SimpleGraph.fromRel B.Adj` starting with a forward arc `u → x`,
every edge in a branching points forward, giving a directed walk `TransGen B.Adj u v`. -/
private theorem transGen_of_walk_fromRel_isTrail {B : Digraph V} (hB : B.IsBranching) :
    ∀ {u x v : V} (hx : (SimpleGraph.fromRel B.Adj).Adj u x)
      (p' : (SimpleGraph.fromRel B.Adj).Walk x v),
      (SimpleGraph.Walk.cons hx p').IsTrail → B.Adj u x → Relation.TransGen B.Adj u v
  | u, x, _, _, .nil, _, hux => Relation.TransGen.single hux
  | u, x, _, hx, @SimpleGraph.Walk.cons _ _ _ y z hyz q, htr, hux => by
    have hne : u ≠ y := by
      intro huy
      have hnd := htr.edges_nodup
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons, List.mem_cons] at hnd
      apply hnd.1 (Or.inl ?_)
      subst huy
      exact Sym2.eq_swap
    have hxy : B.Adj x y := by
      rcases (SimpleGraph.fromRel_adj B.Adj x y).mp hyz |>.2 with h | h
      · exact h
      · exact absurd (hB.in_unique hux h) hne
    exact Relation.TransGen.head hux
      (transGen_of_walk_fromRel_isTrail hB hyz q htr.of_cons hxy)

/-- **Edmonds (1967, Section 1):** Every branching has an acyclic underlying undirected simple
graph (forest). -/
theorem IsBranching.toSimpleGraph_isAcyclic {B : Digraph V} (hB : B.IsBranching) :
    (SimpleGraph.fromRel B.Adj).IsAcyclic := by
  intro v c hc
  cases c with
  | nil => exact absurd hc SimpleGraph.Walk.not_isCycle_nil
  | @cons _ u _ huv p =>
    have htr : (SimpleGraph.Walk.cons huv p).IsTrail := hc.isCircuit.isTrail
    rcases (SimpleGraph.fromRel_adj B.Adj v u).mp huv |>.2 with hvu | huv'
    · exact hB.acyclic (transGen_of_walk_fromRel_isTrail hB huv p htr hvu)
    · have hc_rev : (SimpleGraph.Walk.cons huv p).reverse.IsCycle := hc.reverse
      have hlen : 3 ≤ (SimpleGraph.Walk.cons huv p).length := hc.three_le_length
      cases hrev : (SimpleGraph.Walk.cons huv p).reverse with
      | nil => exact absurd (hrev ▸ hc_rev) SimpleGraph.Walk.not_isCycle_nil
      | @cons _ w _ hwv q =>
        have htr_rev : (SimpleGraph.Walk.cons hwv q).IsTrail := hrev ▸ hc_rev.isCircuit.isTrail
        have hnd : (s(v, u) :: p.edges).Nodup := by simpa using htr.edges_nodup
        have hrev_edges : (s(v, w) :: q.edges) = p.edges.reverse ++ [s(v, u)] := by
          have := congrArg SimpleGraph.Walk.edges hrev
          simpa [SimpleGraph.Walk.edges_reverse, Sym2.eq_swap] using this.symm
        have hmem_edge : s(v, w) ∈ p.edges := by
          rcases hpe : p.edges.reverse with _ | ⟨e, es⟩
          · have hlen0 := congrArg List.length hpe
            simp only [List.length_reverse, SimpleGraph.Walk.length_edges, List.length_nil] at hlen0
            simp only [SimpleGraph.Walk.length_cons] at hlen
            omega
          · rw [hpe, List.cons_append, List.cons.injEq] at hrev_edges
            exact List.mem_reverse.mp (hpe ▸ hrev_edges.1 ▸ List.mem_cons_self)
        have hwu_ne : w ≠ u := by
          intro hwu
          rw [hwu] at hmem_edge
          exact (List.nodup_cons.mp hnd).1 hmem_edge
        have hvw : B.Adj v w := by
          rcases (SimpleGraph.fromRel_adj B.Adj v w).mp hwv |>.2 with h | h
          · exact h
          · exact absurd (hB.in_unique h huv') hwu_ne
        exact hB.acyclic (transGen_of_walk_fromRel_isTrail hB hwv q htr_rev hvw)

end Digraph
