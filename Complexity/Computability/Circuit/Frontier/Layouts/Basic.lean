/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Multigraph
public import Mathlib.Data.Nat.Log
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Sort

/-!
# Tools for layout bounds

This file collects the facts shared by the proofs of instances of the layout hypothesis
`Cslib.Circuits.Frontier.LayoutBound`: the subadditivity of edge cuts, the cut-counting identity
for disjoint sets, the handshake lemma for multigraphs, layouts that follow an injective key, and
the absorption of logarithmic error terms into the layout hypothesis.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_union_add`: the cut of a disjoint union
  `S ∪ T` together with twice the edges between `S` and `T` makes up the cuts of `S` and of `T`.
* `Cslib.Circuits.Frontier.Multigraph.edgeCut_nonempty`: in a connected multigraph, some edge
  leaves every set of vertices other than the empty set and the whole vertex set.
* `Cslib.Circuits.Frontier.Multigraph.sum_ncard_incidenceSet`: the handshake lemma.
* `Cslib.Circuits.Frontier.Layout.exists_lt_iff`: a layout ordered by an injective key.
* `Cslib.Circuits.Frontier.LayoutBound.mono`: a larger coefficient gives a weaker layout bound.
* `Cslib.Circuits.Frontier.LayoutBound.of_natLog`: error terms `D log₂ |V|` are absorbed into
  the layout hypothesis.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-! ### Edge cuts -/

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- Edge cuts are subadditive. -/
theorem edgeCut_union_subset (S T : Set V) : G.edgeCut (S ∪ T) ⊆ G.edgeCut S ∪ G.edgeCut T := by
  intro e
  simp only [mem_edgeCut, mem_union]
  tauto

/-- The cardinality of the edge cut of a union is at most the sum of the cardinalities of the edge
cuts. -/
theorem ncard_edgeCut_union_le [Finite E] (S T : Set V) :
    (G.edgeCut (S ∪ T)).ncard ≤ (G.edgeCut S).ncard + (G.edgeCut T).ncard :=
  (ncard_le_ncard (G.edgeCut_union_subset S T)).trans (ncard_union_le _ _)

/-- **The cut of a disjoint union.** The edges between `S` and `T` lie in the cuts of both `S`
and `T`, but not in the cut of `S ∪ T`. -/
theorem ncard_edgeCut_union_add [Finite E] {S T : Set V} (h : Disjoint S T) :
    (G.edgeCut (S ∪ T)).ncard + 2 * (G.edgeCut S ∩ G.edgeCut T).ncard =
      (G.edgeCut S).ncard + (G.edgeCut T).ncard := by
  have hd (v : V) : v ∈ S → v ∉ T := fun hv => disjoint_left.mp h hv
  have h₁ : G.edgeCut (S ∪ T) ∪ (G.edgeCut S ∩ G.edgeCut T) = G.edgeCut S ∪ G.edgeCut T := by
    ext e
    have := hd (G.src e)
    have := hd (G.tgt e)
    simp only [mem_union, mem_inter_iff, mem_edgeCut]
    tauto
  have h₂ : Disjoint (G.edgeCut (S ∪ T)) (G.edgeCut S ∩ G.edgeCut T) := by
    refine disjoint_left.mpr fun e he he' => ?_
    have := hd (G.src e)
    have := hd (G.tgt e)
    simp only [mem_union, mem_inter_iff, mem_edgeCut] at he he'
    tauto
  have := ncard_union_add_ncard_inter (G.edgeCut S) (G.edgeCut T)
  rw [← h₁, ncard_union_eq h₂] at this
  omega

/-- In a loopless multigraph, the edges leaving a single vertex are the edges at it. -/
theorem edgeCut_singleton (hG : G.Loopless) (v : V) : G.edgeCut {v} = G.incidenceSet v := by
  ext e
  have := hG e
  simp only [mem_edgeCut, mem_singleton_iff, mem_incidenceSet]
  constructor
  · intro h
    by_contra h'
    exact h (iff_of_false (not_or.mp h').1 (not_or.mp h').2)
  · rintro (h | h) <;> grind

variable {G} in
/-- In a connected multigraph, some edge leaves every set of vertices other than the empty set
and the whole vertex set. -/
theorem edgeCut_nonempty (hG : G.toSimpleGraph.Connected) {S : Set V} {u v : V} (hu : u ∈ S)
    (hv : v ∉ S) : (G.edgeCut S).Nonempty := by
  obtain ⟨p⟩ := hG.preconnected u v
  obtain ⟨d, -, hd₁, hd₂⟩ := p.exists_boundary_dart S hu hv
  obtain ⟨-, e, he⟩ := toSimpleGraph_adj.mp d.adj
  refine ⟨e, ?_⟩
  rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩ <;>
    simp only [mem_edgeCut, hs, ht] <;> tauto

/-- **The handshake lemma.** In a finite loopless multigraph, the numbers of edges at the
vertices add up to twice the number of edges. -/
theorem sum_ncard_incidenceSet [Fintype V] [Finite E] (hG : G.Loopless) :
    ∑ v, (G.incidenceSet v).ncard = 2 * Nat.card E := by
  classical
  have := Fintype.ofFinite E
  have hinc (v : V) : (G.incidenceSet v).ncard =
      ∑ e, if G.src e = v ∨ G.tgt e = v then 1 else 0 := by
    rw [Finset.sum_boole, ← ncard_coe_finset]
    congr 1
    ext e
    simp [mem_incidenceSet]
  simp only [hinc]
  rw [Finset.sum_comm, Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.card_eq_sum_ones,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_boole, mul_one]
  have : Finset.univ.filter (fun v => G.src e = v ∨ G.tgt e = v) = {G.src e, G.tgt e} := by
    ext v
    simp [eq_comm]
  rw [this, Finset.card_pair (hG e)]
  rfl

/-- No layout is wider than the number of edges. -/
theorem width_le_card [Finite E] (π : Layout V) : G.width π ≤ Nat.card E :=
  (G.width_le_iff π).2 fun _ => ncard_le_card _

end Multigraph

/-! ### Layouts following a key -/

namespace Layout

variable {V : Type*}

/-- **Layouts following a key.** Listing the vertices in increasing order of an injective key
gives a layout ordered by the key. -/
theorem exists_lt_iff [Finite V] {α : Type*} [LinearOrder α] {f : V → α}
    (hf : f.Injective) : ∃ π : Layout V, ∀ v w, π v < π w ↔ f v < f w := by
  let := LinearOrder.lift' f hf
  have := Fintype.ofFinite V
  let e := (Fintype.orderIsoFinOfCardEq V Nat.card_eq_fintype_card.symm).symm
  exact ⟨e.toEquiv, fun v w => e.lt_iff_lt⟩

/-- The first `t` vertices of a layout ordered by a key are those whose key is less than that of
the vertex numbered `t`. -/
theorem initial_eq_of_lt_iff {α : Type*} [LinearOrder α] {f : V → α} {π : Layout V}
    (hπ : ∀ v w, π v < π w ↔ f v < f w) {t : ℕ} (ht : t < Nat.card V) :
    π.initial t = {v | f v < f (π.symm ⟨t, ht⟩)} := by
  ext v
  rw [mem_initial, mem_ofPred_eq,← hπ, Equiv.apply_symm_apply, Fin.lt_def]

end Layout

/-! ### The layout hypothesis -/

/-- A larger coefficient gives a weaker layout bound. -/
theorem LayoutBound.mono {d : ℕ} {A A' : ℝ} (h : LayoutBound d A) (hAA' : A ≤ A') :
    LayoutBound d A' := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  refine ⟨C, fun V E _ _ G hconn hloop hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  refine ⟨π, hπ.trans ?_⟩
  have : (A + η) * G.cycleRank ≤ (A' + η) * G.cycleRank := by gcongr
  linarith

/-- **Logarithmic error terms.** To prove the layout hypothesis it suffices to find, for every
`η > 0`, layouts of width at most `(A + η) β₁ + D log₂ |V| + C`, for a constant `C`: the term
`D log₂ |V|` is at most `η |V|` plus a constant. -/
theorem LayoutBound.of_natLog {d D : ℕ} {A : ℝ}
    (h : ∀ η > 0, ∃ C : ℝ, ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.toSimpleGraph.Connected → G.Loopless → G.MaxDegreeLE d →
        ∃ π : Layout V, (G.width π : ℝ) ≤ (A + η) * G.cycleRank + D * Nat.log 2 (Nat.card V) + C) :
    LayoutBound d A := by
  intro η hη
  obtain ⟨C, hC⟩ := h η hη
  obtain ⟨m, hm⟩ := exists_nat_gt ((D : ℝ) / η)
  refine ⟨C + η * (m * m : ℕ), fun V E _ _ G hconn hloop hdeg => ?_⟩
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  refine ⟨π, hπ.trans ?_⟩
  have hDm : (D : ℝ) ≤ η * m := ((div_lt_iff₀ hη).mp hm).le.trans_eq (mul_comm _ _)
  have hlog : (m : ℝ) * Nat.log 2 (Nat.card V) ≤ Nat.card V + (m * m : ℕ) := by
    exact_mod_cast Nat.mul_log_le_add_sq Nat.one_lt_two m (Nat.card V)
  have hDlog : (D : ℝ) * Nat.log 2 (Nat.card V) ≤ η * (Nat.card V + (m * m : ℕ)) :=
    calc (D : ℝ) * Nat.log 2 (Nat.card V)
        ≤ (η * m) * Nat.log 2 (Nat.card V) :=
          mul_le_mul_of_nonneg_right hDm (Nat.cast_nonneg _)
      _ = η * ((m : ℝ) * Nat.log 2 (Nat.card V)) := mul_assoc _ _ _
      _ ≤ η * (Nat.card V + (m * m : ℕ)) := mul_le_mul_of_nonneg_left hlog hη.le
  linarith

end Cslib.Circuits.Frontier
