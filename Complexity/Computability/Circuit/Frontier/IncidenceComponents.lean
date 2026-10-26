/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Incidence
import Complexity.Foundations.Data.Finset.SubsetSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Sum

/-!
# Incidence bounds without connectedness

The hereditary obstruction on two disjoint coordinate sets controls the sum of the positive
excesses of the connected components. This removes connectedness from the incidence bound.
The component estimate reuses the connected incidence theorem and its multigraph layout bound.

## Main results

* `Cslib.Circuits.Frontier.Incidence.card_lt_of_partition`: the total cardinality bound from
  the largest positive excess of a partition containing every support.
* `Cslib.Circuits.Frontier.Incidence.two_mul_card_lt_of_partition`: the combined estimate from
  uniform bounds on every part's excess.
* `Cslib.Circuits.Frontier.Incidence.two_mul_card_lt_of_disjoint`: the rank-three incidence
  bound for support families whose incidence graph may be disconnected.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Incidence

open Finset

private theorem card_filter_mem_eq_sum {ι γ : Type*} [Fintype ι] [DecidableEq γ]
    (f : ι → γ) (s : Finset γ) :
    (univ.filter fun i => f i ∈ s).card =
      ∑ c ∈ s, (univ.filter fun i => f i = c).card := by
  exact (sum_card_fiberwise_eq_card_filter univ s f).symm

/-- A hereditary obstruction to two disjoint sets with excess at least `k` bounds the total
coordinate count in terms of the largest positive excess of a partition. Each support must lie
in the part assigned to its index. -/
theorem card_lt_of_partition {ι κ γ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [Finite γ] [DecidableEq γ] (S : κ → Finset ι) (a : ι → γ) (b : κ → γ)
    (hpart : ∀ j i, i ∈ S j → a i = b j) {M k : ℕ}
    (hM : ∀ c, (univ.filter fun i => a i = c).card ≤
      (univ.filter fun j => b j = c).card + M)
    (hdisj : ∀ U V : Finset ι, Disjoint U V →
      U.card < (univ.filter fun j => ¬ Disjoint (S j) U).card + k ∨
      V.card < (univ.filter fun j => ¬ Disjoint (S j) V).card + k) :
    Fintype.card ι < Fintype.card κ + M + 2 * k := by
  classical
  let := Fintype.ofFinite γ
  let N (c : γ) := (univ.filter fun i => a i = c).card
  let Q (c : γ) := (univ.filter fun j => b j = c).card
  let P := univ.filter fun c => Q c < N c
  have hsumN : ∑ c, N c = Fintype.card ι := by
    simpa [N] using (card_filter_mem_eq_sum a (univ : Finset γ)).symm
  have hsumQ : ∑ c, Q c = Fintype.card κ := by
    simpa [Q] using (card_filter_mem_eq_sum b (univ : Finset γ)).symm
  have hsumP : ∑ c ∈ P, (N c - Q c) = ∑ c, (N c - Q c) := by
    apply sum_subset (filter_subset _ _)
    intro c _ hc
    have : N c ≤ Q c := by simpa [P] using hc
    exact Nat.sub_eq_zero_of_le this
  have htot : Fintype.card ι ≤ Fintype.card κ + ∑ c ∈ P, (N c - Q c) := by
    have h := sum_le_sum (s := (univ : Finset γ)) fun c _ =>
      (show N c ≤ Q c + (N c - Q c) by omega)
    rw [sum_add_distrib, hsumN, hsumQ, ← hsumP] at h
    exact h
  by_contra hn
  have hlarge : 2 * k + M ≤ ∑ c ∈ P, (N c - Q c) := by omega
  obtain ⟨A, hA, hkA, hkB⟩ :=
    Finset.exists_subset_sum_ge P (fun c => N c - Q c) M k
      (fun c _ => by have := hM c; change N c ≤ Q c + M at this; omega) hlarge
  let U (C : Finset γ) := univ.filter fun i => a i ∈ C
  have hbad (C : Finset γ) (hC : C ⊆ P) (hkC : k ≤ ∑ c ∈ C, (N c - Q c)) :
      (univ.filter fun j => ¬ Disjoint (S j) (U C)).card + k ≤ (U C).card := by
    have ht : (univ.filter fun j => ¬ Disjoint (S j) (U C)).card ≤
        (univ.filter fun j => b j ∈ C).card := by
      apply card_le_card
      intro j hj
      obtain ⟨i, hiS, hiU⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
      have hiC : a i ∈ C := (mem_filter.mp hiU).2
      exact mem_filter.mpr ⟨mem_univ _, hpart j i hiS ▸ hiC⟩
    rw [card_filter_mem_eq_sum b C] at ht
    have heq : ∑ c ∈ C, N c = ∑ c ∈ C, Q c + ∑ c ∈ C, (N c - Q c) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro c hc
      have hpos : Q c < N c := (mem_filter.mp (hC hc)).2
      omega
    have hcard : (U C).card = ∑ c ∈ C, N c := card_filter_mem_eq_sum a C
    change _ ≤ ∑ c ∈ C, Q c at ht
    omega
  have hUV : Disjoint (U A) (U (P \ A)) := by
    rw [disjoint_left]
    intro i hiA hiB
    exact (mem_sdiff.mp (mem_filter.mp hiB).2).2 (mem_filter.mp hiA).2
  have h1 := hbad A hA hkA
  have h2 := hbad (P \ A) sdiff_subset hkB
  rcases hdisj (U A) (U (P \ A)) hUV with h | h <;> omega

/-- Uniform bounds on the excess of every part combine without multiplying the additive term
by the number of parts. The obstruction must hold for arbitrary disjoint coordinate sets. -/
theorem two_mul_card_lt_of_partition {ι κ γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Finite γ] [DecidableEq γ] (S : κ → Finset ι)
    (a : ι → γ) (b : κ → γ) (hpart : ∀ j i, i ∈ S j → a i = b j)
    {L k : ℕ}
    (hlocal : ∀ c, 2 * (univ.filter fun i => a i = c).card <
      3 * (univ.filter fun j => b j = c).card + L + 2 * k + 1)
    (hdisj : ∀ U V : Finset ι, Disjoint U V →
      U.card < (univ.filter fun j => ¬ Disjoint (S j) U).card + k ∨
      V.card < (univ.filter fun j => ¬ Disjoint (S j) V).card + k) :
    2 * Fintype.card ι < 3 * Fintype.card κ + L + 6 * k + 1 := by
  classical
  let := Fintype.ofFinite γ
  let N (c : γ) := (univ.filter fun i => a i = c).card
  let Q (c : γ) := (univ.filter fun j => b j = c).card
  let M := univ.sup fun c => N c - Q c
  have hM (c : γ) : N c ≤ Q c + M := by
    have := le_sup (f := fun c => N c - Q c) (mem_univ c)
    omega
  have hMbound : M ≤ (Fintype.card κ + L + 2 * k) / 2 := by
    apply Finset.sup_le
    intro c _
    have hloc := hlocal c
    change 2 * N c < 3 * Q c + L + 2 * k + 1 at hloc
    have hQ : Q c ≤ Fintype.card κ := card_le_univ _
    omega
  have htotal := card_lt_of_partition S a b hpart hM hdisj
  omega

private def partSupport {ι κ γ : Type*} [DecidableEq γ] (S : κ → Finset ι)
    (a : ι → γ) (b : κ → γ) (c : γ) :
    {j // b j = c} → Finset {i // a i = c} :=
  fun j => (S j.val).subtype fun i => a i = c

private theorem card_touched_part {ι κ γ : Type*} [DecidableEq ι]
    [Fintype κ] [DecidableEq γ] (S : κ → Finset ι) (a : ι → γ) (b : κ → γ)
    (hpart : ∀ j i, i ∈ S j → a i = b j) (c : γ) (U : Finset {i // a i = c}) :
    (univ.filter fun j => ¬ Disjoint (partSupport S a b c j) U).card =
      (univ.filter fun j => ¬ Disjoint (S j) (U.image Subtype.val)).card := by
  classical
  refine card_bij (fun j _ => j.val) ?_ ?_ ?_
  · intro j hj
    obtain ⟨i, hiS, hiU⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
    refine mem_filter.mpr ⟨mem_univ _, not_disjoint_iff.mpr ?_⟩
    exact ⟨i.val, mem_subtype.mp hiS, mem_image.mpr ⟨i, hiU, rfl⟩⟩
  · intro j _ j' _ hj
    exact Subtype.ext hj
  · intro j hj
    obtain ⟨x, hiS, hxU⟩ := not_disjoint_iff.mp (mem_filter.mp hj).2
    obtain ⟨i, hiU, rfl⟩ := mem_image.mp hxU
    have hjc : b j = c := (hpart j i.val hiS).symm.trans i.property
    refine ⟨⟨j, hjc⟩, mem_filter.mpr ⟨mem_univ _, not_disjoint_iff.mpr ?_⟩, rfl⟩
    exact ⟨i, mem_subtype.mpr hiS, hiU⟩

/-- The rank-three incidence bound for an arbitrary support family. It suffices that every two
disjoint coordinate sets have one side whose cardinality is smaller than its number of touching
supports plus `k`. No connectedness assumption is needed. -/
theorem two_mul_card_lt_of_disjoint {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (S : κ → Finset ι) {T k : ℕ} (hs : ∀ j, (S j).card ≤ 3)
    (hT : ∀ i, (univ.filter fun j => i ∈ S j).card ≤ T)
    (hdisj : ∀ U V : Finset ι, Disjoint U V →
      U.card < (univ.filter fun j => ¬ Disjoint (S j) U).card + k ∨
      V.card < (univ.filter fun j => ¬ Disjoint (S j) V).card + k) :
    2 * Fintype.card ι < 3 * Fintype.card κ +
      max 3 T * Nat.log 2 (Fintype.card ι + Fintype.card κ) + 6 * k + 1 := by
  classical
  let G := (graph S).toSimpleGraph
  let a (i : ι) := G.connectedComponentMk (.inl i)
  let b (j : κ) := G.connectedComponentMk (.inr j)
  have hpart : ∀ j i, i ∈ S j → a i = b j := by
    intro j i hi
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ((adj_inl_inr S i j).mpr hi)
  apply two_mul_card_lt_of_partition S a b hpart ?_ hdisj
  intro c
  let I := {i // a i = c}
  let J := {j // b j = c}
  let S' : J → Finset I := partSupport S a b c
  have hs' (j : J) : (S' j).card ≤ 3 := by
    change ((S j.val).subtype fun i => a i = c).card ≤ 3
    rw [card_subtype]
    exact (card_filter_le _ _).trans (hs j.val)
  have hT' (i : I) : (univ.filter fun j => i ∈ S' j).card ≤ T := by
    apply le_trans (card_le_card_of_injOn Subtype.val ?_ Subtype.val_injective.injOn)
      (hT i.val)
    intro j hj
    exact mem_filter.mpr ⟨mem_univ _, mem_subtype.mp (mem_filter.mp hj).2⟩
  have hconn : (graph S').toSimpleGraph.Connected := by
    let e : I ⊕ J ≃ c.supp :=
      (Equiv.subtypeSum (p := fun v : ι ⊕ κ => G.connectedComponentMk v = c)).symm
    let iso : (graph S').toSimpleGraph ≃g c.toSimpleGraph :=
      { toEquiv := e
        map_rel_iff' := by
          rintro (i | j) (i' | j')
          · change (graph S).toSimpleGraph.Adj (.inl i.val) (.inl i'.val) ↔
              (graph S').toSimpleGraph.Adj (.inl i) (.inl i')
            simp only [not_adj_inl_inl]
          · change (graph S).toSimpleGraph.Adj (.inl i.val) (.inr j'.val) ↔
              (graph S').toSimpleGraph.Adj (.inl i) (.inr j')
            rw [adj_inl_inr S i.val j'.val, adj_inl_inr S' i j']
            exact mem_subtype.symm
          · change (graph S).toSimpleGraph.Adj (.inr j.val) (.inl i'.val) ↔
              (graph S').toSimpleGraph.Adj (.inr j) (.inl i')
            rw [SimpleGraph.adj_comm (G := (graph S).toSimpleGraph),
              SimpleGraph.adj_comm (G := (graph S').toSimpleGraph)]
            rw [adj_inl_inr S i'.val j.val, adj_inl_inr S' i' j]
            exact mem_subtype.symm
          · change (graph S).toSimpleGraph.Adj (.inr j.val) (.inr j'.val) ↔
              (graph S').toSimpleGraph.Adj (.inr j) (.inr j')
            simp only [not_adj_inr_inr] }
    exact iso.connected_iff.mpr c.connected_toSimpleGraph
  have hcut (U : Finset I) :
      U.card < (univ.filter fun j => ¬ Disjoint (S' j) U).card + k ∨
      Uᶜ.card < (univ.filter fun j => ¬ Disjoint (S' j) Uᶜ).card + k := by
    have hd : Disjoint (U.image Subtype.val) (Uᶜ.image Subtype.val) := by
      rw [disjoint_left]
      intro i hiU hiV
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hiU
      obtain ⟨v, hv, hvu⟩ := mem_image.mp hiV
      have : v = u := Subtype.ext hvu
      exact mem_compl.mp hv (this.symm ▸ hu)
    have h := hdisj (U.image Subtype.val) (Uᶜ.image Subtype.val) hd
    rw [card_image_of_injective U Subtype.val_injective,
      card_image_of_injective Uᶜ Subtype.val_injective,
      ← card_touched_part S a b hpart c U,
      ← card_touched_part S a b hpart c Uᶜ] at h
    exact h
  have hc := two_mul_card_lt S' hs' hT' hconn hcut
  have hI : Fintype.card I = (univ.filter fun i => a i = c).card :=
    Fintype.card_subtype _
  have hJ : Fintype.card J = (univ.filter fun j => b j = c).card :=
    Fintype.card_subtype _
  rw [hI, hJ] at hc
  have hlog := Nat.log_mono_right (b := 2)
    (Nat.add_le_add (card_le_univ (univ.filter fun i => a i = c))
      (card_le_univ (univ.filter fun j => b j = c)))
  exact hc.trans_le (by gcongr)

end Cslib.Circuits.Frontier.Incidence
