/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Layouts.General
import Complexity.Foundations.Combinatorics.HypergraphCut

/-!
# Incidence layouts and support deficits

The incidence multigraph of a finite indexed support family has one vertex for each input and
each support, and one edge for each support membership. A support meeting both sides of an
input cut contributes an edge to every incidence-layout frontier inducing that cut.

For supports of size at most three and input incidence at most `T`, the existing connected
multigraph layout bound combines with the support-deficit obstruction to give
`2 * N < 3 * Q + max 3 T * log₂ (N + Q) + 2 * k + 1`.

## Main definitions

* `Cslib.Circuits.Frontier.Incidence.graph`: the incidence multigraph of a support family.
* `Cslib.Circuits.Frontier.Incidence.inputPrefix`: the input vertices in a layout prefix.

## Main results

* `Cslib.Circuits.Frontier.Incidence.maxDegreeLE`: support and input-incidence degree bounds.
* `Cslib.Circuits.Frontier.Incidence.card_crossing_le_width`: crossing supports are bounded
  by incidence-layout width.
* `Cslib.Circuits.Frontier.Incidence.two_mul_card_lt`: the connected support-family bound.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Incidence

open Finset

variable {ι κ : Type*}

/-- The bipartite incidence multigraph, with an edge from each input to each support containing
it. Distinct support indices remain distinct vertices, including repeated or empty supports. -/
def graph (S : κ → Finset ι) : Multigraph (ι ⊕ κ) {p : ι × κ // p.1 ∈ S p.2} where
  src e := .inl e.val.1
  tgt e := .inr e.val.2

/-- Every incidence edge joins the two different vertex classes. -/
theorem loopless (S : κ → Finset ι) : (graph S).Loopless := by
  intro e
  exact Sum.inl_ne_inr

/-- Adjacency between an input vertex and a support vertex is support membership. -/
@[simp]
theorem adj_inl_inr (S : κ → Finset ι) (i : ι) (j : κ) :
    (graph S).toSimpleGraph.Adj (.inl i) (.inr j) ↔ i ∈ S j := by
  rw [Multigraph.toSimpleGraph_adj]
  constructor
  · rintro ⟨_, ⟨⟨⟨i', j'⟩, hij⟩, he⟩⟩
    change s(Sum.inl i', Sum.inr j') = s(Sum.inl i, Sum.inr j) at he
    rcases Sym2.eq_iff.mp he with he | he
    · have hi := Sum.inl.inj he.1
      have hj := Sum.inr.inj he.2
      simpa only [hi, hj] using hij
    · exact (Sum.inl_ne_inr he.1).elim
  · intro hij
    exact ⟨Sum.inl_ne_inr, ⟨(i, j), hij⟩, rfl⟩

/-- Two input vertices are never adjacent in an incidence graph. -/
@[simp]
theorem not_adj_inl_inl (S : κ → Finset ι) (i i' : ι) :
    ¬(graph S).toSimpleGraph.Adj (.inl i) (.inl i') := by
  intro h
  obtain ⟨e, he⟩ := (Multigraph.toSimpleGraph_adj.mp h).2
  change s(Sum.inl e.val.1, Sum.inr e.val.2) = s(Sum.inl i, Sum.inl i') at he
  rcases Sym2.eq_iff.mp he with he | he
  · exact Sum.inr_ne_inl he.2
  · exact Sum.inr_ne_inl he.2

/-- Two support vertices are never adjacent in an incidence graph. -/
@[simp]
theorem not_adj_inr_inr (S : κ → Finset ι) (j j' : κ) :
    ¬(graph S).toSimpleGraph.Adj (.inr j) (.inr j') := by
  intro h
  obtain ⟨e, he⟩ := (Multigraph.toSimpleGraph_adj.mp h).2
  change s(Sum.inl e.val.1, Sum.inr e.val.2) = s(Sum.inr j, Sum.inr j') at he
  rcases Sym2.eq_iff.mp he with he | he
  · exact Sum.inl_ne_inr he.1
  · exact Sum.inl_ne_inr he.1

/-- The edge count of an incidence multigraph is the sum of the support sizes. -/
theorem card_edges [Fintype κ] (S : κ → Finset ι) :
    Nat.card {p : ι × κ // p.1 ∈ S p.2} = ∑ j, (S j).card := by
  classical
  let e : {p : ι × κ // p.1 ∈ S p.2} ≃ Σ j, ↥(S j) :=
    { toFun := fun p => ⟨p.val.2, ⟨p.val.1, p.property⟩⟩
      invFun := fun p => ⟨(p.2.val, p.1), p.2.property⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp

/-- Input-vertex degree is the number of supports containing that input. -/
theorem ncard_incidence_inl [DecidableEq ι] [Fintype κ] (S : κ → Finset ι) (i : ι) :
    ((graph S).incidenceSet (.inl i)).ncard =
      (univ.filter fun j => i ∈ S j).card := by
  classical
  have hi (e : (graph S).incidenceSet (.inl i)) : e.val.val.1 = i := by
    simpa only [Multigraph.incidenceSet, graph, Set.mem_ofPred_eq, Sum.inl.injEq,
      Sum.inr_ne_inl, or_false] using e.property
  let e : (graph S).incidenceSet (.inl i) ≃ ↥(univ.filter fun j => i ∈ S j) :=
    { toFun := fun p => ⟨p.val.val.2, mem_filter.mpr
        ⟨mem_univ _, by simpa only [hi p] using p.val.property⟩⟩
      invFun := fun p => ⟨⟨(i, p.val), (mem_filter.mp p.property).2⟩, Or.inl rfl⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (hi p).symm rfl
      right_inv := fun p => by apply Subtype.ext; rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_finsetCard]

/-- Support-vertex degree is the size of that support. -/
theorem ncard_incidence_inr (S : κ → Finset ι) (j : κ) :
    ((graph S).incidenceSet (.inr j)).ncard = (S j).card := by
  classical
  have hj (e : (graph S).incidenceSet (.inr j)) : e.val.val.2 = j := by
    simpa only [Multigraph.incidenceSet, graph, Set.mem_ofPred_eq, Sum.inl_ne_inr,
      Sum.inr.injEq, false_or] using e.property
  let e : (graph S).incidenceSet (.inr j) ≃ ↥(S j) :=
    { toFun := fun p => ⟨p.val.val.1, by simpa only [hj p] using p.val.property⟩
      invFun := fun p => ⟨⟨(p.val, j), p.property⟩, Or.inr rfl⟩
      left_inv := fun p => by
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext rfl (hj p).symm
      right_inv := fun p => by apply Subtype.ext; rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_eq_finsetCard]

/-- Bounds on support sizes and input incidences bound both classes of incidence-graph degrees. -/
theorem maxDegreeLE [Finite ι] [DecidableEq ι] [Fintype κ] (S : κ → Finset ι) {d T : ℕ}
    (hs : ∀ j, (S j).card ≤ d)
    (hT : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ T) :
    (graph S).MaxDegreeLE (max d T) := by
  intro v
  cases v with
  | inl i =>
    rw [ncard_incidence_inl]
    exact (hT i).trans (le_max_right _ _)
  | inr j =>
    rw [ncard_incidence_inr]
    exact (hs j).trans (le_max_left _ _)

variable [Fintype ι]

/-- The inputs occurring among the first `t` incidence-layout vertices. -/
def inputPrefix (π : Layout (ι ⊕ κ)) (t : ℕ) : Finset ι :=
  univ.filter fun i => (π (.inl i) : ℕ) < t

/-- An input belongs to the prefix exactly when its layout position is below `t`. -/
@[simp]
theorem mem_inputPrefix (π : Layout (ι ⊕ κ)) (t : ℕ) (i : ι) :
    i ∈ inputPrefix π t ↔ (π (.inl i) : ℕ) < t := by
  simp [inputPrefix]

/-- The empty layout prefix contains no inputs. -/
@[simp]
theorem inputPrefix_zero (π : Layout (ι ⊕ κ)) : inputPrefix π 0 = ∅ := by
  simp [inputPrefix]

/-- The full layout prefix contains every input. -/
theorem inputPrefix_last (π : Layout (ι ⊕ κ)) :
    inputPrefix π (Nat.card (ι ⊕ κ)) = univ := by
  ext i
  simp only [mem_inputPrefix, mem_univ, iff_true]
  exact (π (.inl i)).isLt

/-- Input prefixes grow with the layout position. -/
theorem inputPrefix_mono (π : Layout (ι ⊕ κ)) : Monotone (inputPrefix π) := by
  intro t u htu i hi
  exact (mem_inputPrefix π u i).mpr (((mem_inputPrefix π t i).mp hi).trans_le htu)

/-- Processing one layout vertex adds at most one input. -/
theorem card_inputPrefix_succ_le (π : Layout (ι ⊕ κ)) (t : ℕ) :
    (inputPrefix π (t + 1)).card ≤ (inputPrefix π t).card + 1 := by
  classical
  let A := univ.filter fun i => (π (.inl i) : ℕ) = t
  have hA : A.card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    apply Sum.inl.inj
    apply π.injective
    apply Fin.ext
    exact (mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm
  have hsub : inputPrefix π (t + 1) ⊆ inputPrefix π t ∪ A := by
    intro i hi
    have hi' := (mem_inputPrefix π (t + 1) i).mp hi
    by_cases hit : (π (.inl i) : ℕ) < t
    · exact mem_union_left _ ((mem_inputPrefix π t i).mpr hit)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, by omega⟩)
  exact (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left hA _))

variable [DecidableEq ι] [Fintype κ]

/-- Each support crossing the input cut contributes a distinct incidence edge to the layout
frontier, so the number of such supports is at most the layout width. -/
theorem card_crossing_le_width (S : κ → Finset ι) (π : Layout (ι ⊕ κ)) (t : ℕ) :
    (univ.filter fun j => ¬Disjoint (S j) (inputPrefix π t) ∧
      ¬Disjoint (S j) (inputPrefix π t)ᶜ).card ≤ (graph S).width π := by
  classical
  let C := univ.filter fun j => ¬Disjoint (S j) (inputPrefix π t) ∧
    ¬Disjoint (S j) (inputPrefix π t)ᶜ
  have hw (j : C) : ∃ i, i ∈ S j.val ∧
      ¬((π (.inl i) : ℕ) < t ↔ (π (.inr j.val) : ℕ) < t) := by
    obtain ⟨hleft, hright⟩ := (mem_filter.mp j.property).2
    by_cases hj : (π (.inr j.val) : ℕ) < t
    · obtain ⟨i, hiS, hi⟩ := not_disjoint_iff.mp hright
      have hi' : ¬(π (.inl i) : ℕ) < t := by simpa using hi
      exact ⟨i, hiS, fun h => hi' (h.mpr hj)⟩
    · obtain ⟨i, hiS, hi⟩ := not_disjoint_iff.mp hleft
      have hi' := (mem_inputPrefix π t i).mp hi
      exact ⟨i, hiS, fun h => hj (h.mp hi')⟩
  let edge (j : C) : (graph S).frontier π t :=
    ⟨⟨((hw j).choose, j.val), (hw j).choose_spec.1⟩, (hw j).choose_spec.2⟩
  have hinj : Function.Injective edge := by
    intro j j' h
    apply Subtype.ext
    exact congrArg (fun e : (graph S).frontier π t => e.val.val.2) h
  calc
    C.card = Nat.card C := (Nat.card_eq_finsetCard C).symm
    _ ≤ Nat.card ((graph S).frontier π t) := Nat.card_le_card_of_injective edge hinj
    _ = ((graph S).frontier π t).ncard := Nat.card_coe_set_eq _
    _ ≤ (graph S).width π := (graph S).ncard_frontier_le_width π t

/-- A connected family whose supports have size at most three satisfying the cut-deficit obstruction
has twice as many inputs as at most three times as many supports, up to the degree-layout and
rectangle-threshold terms. -/
theorem two_mul_card_lt (S : κ → Finset ι) {T k : ℕ}
    (hs : ∀ j, (S j).card ≤ 3)
    (hT : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ T)
    (hconn : (graph S).toSimpleGraph.Connected)
    (hcut : ∀ U : Finset ι,
      U.card < (univ.filter fun j => ¬Disjoint (S j) U).card + k ∨
      Uᶜ.card < (univ.filter fun j => ¬Disjoint (S j) Uᶜ).card + k) :
    2 * Fintype.card ι < 3 * Fintype.card κ +
      max 3 T * Nat.log 2 (Fintype.card ι + Fintype.card κ) + 2 * k + 1 := by
  classical
  obtain ⟨π, hπ⟩ := (graph S).exists_width_le_cycleRank_add hconn (maxDegreeLE S hs hT)
  have hchain := Cslib.HypergraphCut.card_lt_of_deficit_chain S (inputPrefix π)
    (m := Nat.card (ι ⊕ κ)) (W := (graph S).width π)
    (inputPrefix_zero π) (inputPrefix_last π)
    (fun t _ => inputPrefix_mono π (Nat.le_succ t))
    (fun t _ => card_inputPrefix_succ_le π t)
    (fun t _ => card_crossing_le_width S π t) hcut
  have he : Nat.card {p : ι × κ // p.1 ∈ S p.2} ≤ 3 * Fintype.card κ := by
    rw [card_edges]
    calc
      ∑ j, (S j).card ≤ ∑ _j : κ, 3 := sum_le_sum fun j _ => hs j
      _ = 3 * Fintype.card κ := by simp [Nat.mul_comm]
  have hv : Nat.card (ι ⊕ κ) = Fintype.card ι + Fintype.card κ := by
    simp [Nat.card_eq_fintype_card]
  have hc := (graph S).card_le_card_add_one_of_connected hconn
  rw [hv] at hc
  have hr : (graph S).cycleRank + (Fintype.card ι + Fintype.card κ) ≤
      3 * Fintype.card κ + 1 := by
    rw [Multigraph.cycleRank, hv]
    omega
  rw [hv] at hπ
  omega

end Cslib.Circuits.Frontier.Incidence
