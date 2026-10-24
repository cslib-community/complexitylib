/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Multigraph
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Independent local improvements of threshold cuts

A set `I` of vertices of a multigraph is *independent* when no edge has both endpoints in `I`.
Then every edge is at at most one vertex of `I`, so changing a cut only at the vertices of `I`
changes its size by the sum of the changes at the edges of each of them
(`ncard_edgeCut_add_sum_eq`). In particular, improvements of the cut at each vertex of `I`,
made simultaneously, improve the whole cut (`ncard_edgeCut_le_of_local`), and the gain is the
sum of the local gains (`ncard_edgeCut_eq_add_sum_sub`).

For a layout by keys, the cuts are the *threshold cuts* `{v | key v < t}`. Moving the key of
each vertex of an independent set to a median of the keys of its neighbours improves every
threshold cut at once (`ncard_edgeCut_threshold_le`): at every threshold, a median sides with
at least half of the neighbours. For a vertex with three edges, the median of the three keys of
its neighbours is such a median (`isMedianAt_median3`).

## Main definitions

* `Cslib.Circuits.Frontier.Multigraph.otherEnd`: the endpoint of an edge other than a vertex.
* `Cslib.Circuits.Frontier.Multigraph.IsMedianAt`: a median of the keys of the neighbours.
* `Cslib.Circuits.Frontier.median3`: the median of three values.

## Main results

* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_add_sum_eq`: the exact change of a cut
  under changes at an independent set.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_le_of_local`: independent local
  improvements improve the cut.
* `Cslib.Circuits.Frontier.Multigraph.ncard_edgeCut_threshold_le`: independent median updates
  improve every threshold cut.
* `Cslib.Circuits.Frontier.Multigraph.isMedianAt_median3`: the median of three keys.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set

/-- The median of three values. -/
def median3 {α : Type*} [LinearOrder α] (a b c : α) : α :=
  max (min a b) (min (max a b) c)

/-- At least two of three values are at most their median, and at least two are at least it. -/
theorem two_le_median3 {α : Type*} [LinearOrder α] (a b c : α) :
    2 ≤ (if a ≤ median3 a b c then 1 else 0) + (if b ≤ median3 a b c then 1 else 0) +
        (if c ≤ median3 a b c then 1 else 0) ∧
      2 ≤ (if median3 a b c ≤ a then 1 else 0) + (if median3 a b c ≤ b then 1 else 0) +
        (if median3 a b c ≤ c then 1 else 0) := by
  rcases le_total a b with hab | hab <;> rcases le_total b c with hbc | hbc <;>
    rcases le_total a c with hac | hac <;>
    simp [median3, hab, hbc, hac]

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-! ### Changes at an independent set -/

/-- **Independent sets count edges once.** If no edge has both endpoints in `I`, the edges of
a set `X` at the vertices of `I` are the disjoint union of those at each vertex of `I`. -/
private theorem ncard_inter_touching [Finite E] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I))
    (X : Set E) : (X ∩ G.touching I).ncard = ∑ v ∈ I, (X ∩ G.incidenceSet v).ncard := by
  classical
  have := Fintype.ofFinite E
  have hcount (Y : Set E) : Y.ncard = ∑ e, if e ∈ Y then 1 else 0 := by
    rw [Finset.sum_boole, ← ncard_coe_finset]
    congr 1
    ext e
    simp
  simp only [hcount]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases hX : e ∈ X
  · by_cases hs : G.src e ∈ I
    · rw [Finset.sum_eq_single_of_mem (G.src e) hs]
      · simp [mem_touching, mem_incidenceSet, hX, hs]
      · intro w hw hne
        have ht : G.tgt e ≠ w := fun ht => hI e ⟨hs, ht ▸ hw⟩
        simp [mem_incidenceSet, Ne.symm hne, ht]
    · by_cases ht : G.tgt e ∈ I
      · rw [Finset.sum_eq_single_of_mem (G.tgt e) ht]
        · simp [mem_touching, mem_incidenceSet, hX, ht]
        · intro w hw hne
          have hs' : G.src e ≠ w := fun h => hs (h ▸ hw)
          simp [mem_incidenceSet, Ne.symm hne, hs']
      · rw [Finset.sum_eq_zero]
        · simp [mem_touching, hs, ht]
        · intro w hw
          have hs' : G.src e ≠ w := fun h => hs (h ▸ hw)
          have ht' : G.tgt e ≠ w := fun h => ht (h ▸ hw)
          simp [mem_incidenceSet, hs', ht']
  · simp [hX]

/-- **The exact change of a cut** under changes at an independent set `I`: if `L` and `L'` agree
outside `I`, the cut of `L'` together with the local cuts of `L` at the vertices of `I` balances
the cut of `L` together with the local cuts of `L'`. -/
theorem ncard_edgeCut_add_sum_eq [Finite E] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {L L' : Set V} (hLL' : ∀ v ∉ I, v ∈ L ↔ v ∈ L') :
    (G.edgeCut L').ncard + ∑ v ∈ I, (G.edgeCut L ∩ G.incidenceSet v).ncard =
      (G.edgeCut L).ncard + ∑ v ∈ I, (G.edgeCut L' ∩ G.incidenceSet v).ncard := by
  -- Away from `I` the two cuts agree.
  have hfar : G.edgeCut L \ G.touching I = G.edgeCut L' \ G.touching I := by
    ext e
    simp only [mem_sdiff, mem_edgeCut, mem_touching, not_or, and_congr_left_iff]
    rintro ⟨hs, ht⟩
    rw [hLL' _ hs, hLL' _ ht]
  rw [← ncard_inter_add_ncard_sdiff_eq_ncard (G.edgeCut L) (G.touching I),
    ← ncard_inter_add_ncard_sdiff_eq_ncard (G.edgeCut L') (G.touching I), hfar,
    G.ncard_inter_touching hI, G.ncard_inter_touching hI]
  omega

/-- **Independent local improvements improve the cut.** If `L` and `L'` agree outside an
independent set `I`, and at each vertex of `I` at most as many edges cross `L'` as cross `L`,
then at most as many edges cross `L'` as cross `L`. -/
theorem ncard_edgeCut_le_of_local [Finite E] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {L L' : Set V} (hLL' : ∀ v ∉ I, v ∈ L ↔ v ∈ L')
    (hlocal : ∀ v ∈ I,
      (G.edgeCut L' ∩ G.incidenceSet v).ncard ≤ (G.edgeCut L ∩ G.incidenceSet v).ncard) :
    (G.edgeCut L').ncard ≤ (G.edgeCut L).ncard := by
  have := G.ncard_edgeCut_add_sum_eq hI hLL'
  have := Finset.sum_le_sum hlocal
  omega

/-- A strict local improvement at one vertex of `I` gives a strict improvement of the cut. -/
theorem ncard_edgeCut_lt_of_local [Finite E] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {L L' : Set V} (hLL' : ∀ v ∉ I, v ∈ L ↔ v ∈ L')
    (hlocal : ∀ v ∈ I,
      (G.edgeCut L' ∩ G.incidenceSet v).ncard ≤ (G.edgeCut L ∩ G.incidenceSet v).ncard)
    (hstrict : ∃ v ∈ I,
      (G.edgeCut L' ∩ G.incidenceSet v).ncard < (G.edgeCut L ∩ G.incidenceSet v).ncard) :
    (G.edgeCut L').ncard < (G.edgeCut L).ncard := by
  have := G.ncard_edgeCut_add_sum_eq hI hLL'
  have := Finset.sum_lt_sum hlocal hstrict
  omega

/-- **The gain is the sum of the local gains**: updated stars at an independent set do not
interact. -/
theorem ncard_edgeCut_eq_add_sum_sub [Finite E] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {L L' : Set V} (hLL' : ∀ v ∉ I, v ∈ L ↔ v ∈ L')
    (hlocal : ∀ v ∈ I,
      (G.edgeCut L' ∩ G.incidenceSet v).ncard ≤ (G.edgeCut L ∩ G.incidenceSet v).ncard) :
    (G.edgeCut L).ncard = (G.edgeCut L').ncard +
      ∑ v ∈ I, ((G.edgeCut L ∩ G.incidenceSet v).ncard -
        (G.edgeCut L' ∩ G.incidenceSet v).ncard) := by
  have := G.ncard_edgeCut_add_sum_eq hI hLL'
  have hs : ∑ v ∈ I, (G.edgeCut L ∩ G.incidenceSet v).ncard =
      ∑ v ∈ I, (G.edgeCut L' ∩ G.incidenceSet v).ncard + ∑ v ∈ I,
        ((G.edgeCut L ∩ G.incidenceSet v).ncard - (G.edgeCut L' ∩ G.incidenceSet v).ncard) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v hv => by have := hlocal v hv; omega
  omega

/-! ### Median updates of keys -/

variable [DecidableEq V]

/-- The endpoint of `e` other than `v`. When `v` is not an endpoint of `e`, this is the source
of `e`. -/
def otherEnd (v : V) (e : E) : V :=
  if G.src e = v then G.tgt e else G.src e

variable {G}

/-- An edge at `v` crosses a cut when its other end lies on the other side. -/
theorem mem_edgeCut_iff_otherEnd {L : Set V} {v : V} {e : E} (he : e ∈ G.incidenceSet v) :
    e ∈ G.edgeCut L ↔ ¬(v ∈ L ↔ G.otherEnd v e ∈ L) := by
  unfold otherEnd
  split_ifs with hs
  · rw [mem_edgeCut, hs]
  · rw [mem_edgeCut, he.resolve_left hs]
    exact not_congr Iff.comm

/-- In an independent set, the other ends of the edges at a vertex lie outside the set. -/
private theorem otherEnd_notMem {I : Finset V} (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {v : V}
    (hv : v ∈ I) {e : E} (he : e ∈ G.incidenceSet v) : G.otherEnd v e ∉ I := by
  unfold otherEnd
  split_ifs with hs
  · exact fun ht => hI e ⟨hs ▸ hv, ht⟩
  · exact fun hs' => hI e ⟨hs', he.resolve_left hs ▸ hv⟩

variable (G)

/-- `m` is a *median* at `v` of the keys of the neighbours of `v`: of the edges at `v`, at most
as many lead to keys above `m` as to keys at most `m`, and at most as many lead to keys below `m`
as to keys at least `m`. -/
def IsMedianAt {α : Type*} [LinearOrder α] (key : V → α) (v : V) (m : α) : Prop :=
  {e ∈ G.incidenceSet v | m < key (G.otherEnd v e)}.ncard ≤
      {e ∈ G.incidenceSet v | key (G.otherEnd v e) ≤ m}.ncard ∧
    {e ∈ G.incidenceSet v | key (G.otherEnd v e) < m}.ncard ≤
      {e ∈ G.incidenceSet v | m ≤ key (G.otherEnd v e)}.ncard

variable {G}

/-- **A median minimises the local threshold cuts.** If the neighbours of `v` keep their keys and
the new key of `v` is a median of theirs, then at every threshold at most as many edges at `v`
cross the new threshold cut as crossed the old one. -/
private theorem ncard_edgeCut_threshold_inter_le [Finite E] {α : Type*} [LinearOrder α]
    {key key' : V → α} {v : V}
    (hfix : ∀ e ∈ G.incidenceSet v, key' (G.otherEnd v e) = key (G.otherEnd v e))
    (hmed : G.IsMedianAt key v (key' v)) (t : α) :
    (G.edgeCut {w | key' w < t} ∩ G.incidenceSet v).ncard ≤
      (G.edgeCut {w | key w < t} ∩ G.incidenceSet v).ncard := by
  -- The edges at `v` towards keys below `t`, and the others.
  set A := {e ∈ G.incidenceSet v | key (G.otherEnd v e) < t}
  set B := {e ∈ G.incidenceSet v | ¬key (G.otherEnd v e) < t}
  have hcut (κ : V → α) (hκ : ∀ e ∈ G.incidenceSet v, κ (G.otherEnd v e) = key (G.otherEnd v e)) :
      G.edgeCut {w | κ w < t} ∩ G.incidenceSet v = if κ v < t then B else A := by
    ext e
    split_ifs with hv
    · simp only [mem_inter_iff, mem_ofPred_eq, B]
      refine ⟨fun ⟨he, hi⟩ => ⟨hi, ?_⟩, fun ⟨hi, he⟩ => ⟨?_, hi⟩⟩
      · rw [mem_edgeCut_iff_otherEnd hi, mem_ofPred_eq, mem_ofPred_eq, hκ e hi] at he
        tauto
      · rw [mem_edgeCut_iff_otherEnd hi, mem_ofPred_eq, mem_ofPred_eq, hκ e hi]
        tauto
    · simp only [mem_inter_iff, mem_ofPred_eq, A]
      refine ⟨fun ⟨he, hi⟩ => ⟨hi, ?_⟩, fun ⟨hi, he⟩ => ⟨?_, hi⟩⟩
      · rw [mem_edgeCut_iff_otherEnd hi, mem_ofPred_eq, mem_ofPred_eq, hκ e hi] at he
        tauto
      · rw [mem_edgeCut_iff_otherEnd hi, mem_ofPred_eq, mem_ofPred_eq, hκ e hi]
        tauto
  rw [hcut key' hfix, hcut key fun _ _ => rfl]
  obtain ⟨h₁, h₂⟩ := hmed
  -- The median sides with the larger of `A` and `B`.
  have hBA (hv' : key' v < t) : B.ncard ≤ A.ncard :=
    (ncard_le_ncard (s := B) (t := {e ∈ G.incidenceSet v | key' v < key (G.otherEnd v e)})
      fun e he => ⟨he.1, hv'.trans_le (not_lt.mp he.2)⟩).trans
      (h₁.trans (ncard_le_ncard fun e he => ⟨he.1, he.2.trans_lt hv'⟩))
  have hAB (hv' : ¬key' v < t) : A.ncard ≤ B.ncard :=
    (ncard_le_ncard (s := A) (t := {e ∈ G.incidenceSet v | key (G.otherEnd v e) < key' v})
      fun e he => ⟨he.1, he.2.trans_le (not_lt.mp hv')⟩).trans
      (h₂.trans (ncard_le_ncard fun e he => ⟨he.1, not_lt.mpr ((not_lt.mp hv').trans he.2)⟩))
  split_ifs with h h'
  exacts [le_rfl, hBA h, hAB h, le_rfl]

/-- **Median updates improve every threshold cut.** Moving the keys of the vertices of an
independent set `I` to medians of the keys of their neighbours does not increase the cut at any
threshold. -/
theorem ncard_edgeCut_threshold_le [Finite E] {α : Type*} [LinearOrder α] {I : Finset V}
    (hI : ∀ e, ¬(G.src e ∈ I ∧ G.tgt e ∈ I)) {key key' : V → α}
    (hfix : ∀ v ∉ I, key' v = key v) (hmed : ∀ v ∈ I, G.IsMedianAt key v (key' v)) (t : α) :
    (G.edgeCut {w | key' w < t}).ncard ≤ (G.edgeCut {w | key w < t}).ncard :=
  G.ncard_edgeCut_le_of_local hI (fun v hv => by simp only [mem_ofPred_eq, hfix v hv])
    fun v hv => ncard_edgeCut_threshold_inter_le
      (fun _ he => hfix _ (otherEnd_notMem hI hv he)) (hmed v hv) t

/-- **The median of three keys.** At a vertex with exactly three edges, the median of the keys of
the three neighbours is a median. -/
theorem isMedianAt_median3 {α : Type*} [LinearOrder α] (key : V → α) {v : V} {e₀ e₁ e₂ : E}
    (h01 : e₀ ≠ e₁) (h02 : e₀ ≠ e₂) (h12 : e₁ ≠ e₂) (hv : G.incidenceSet v = {e₀, e₁, e₂}) :
    G.IsMedianAt key v (median3 (key (G.otherEnd v e₀)) (key (G.otherEnd v e₁))
      (key (G.otherEnd v e₂))) := by
  classical
  -- Counting the edges at `v` with a property.
  have hcount (P : E → Prop) [DecidablePred P] : {e ∈ G.incidenceSet v | P e}.ncard =
      (if P e₀ then 1 else 0) + (if P e₁ then 1 else 0) + (if P e₂ then 1 else 0) := by
    have : {e ∈ G.incidenceSet v | P e} = ↑(({e₀, e₁, e₂} : Finset E).filter P) := by
      ext e
      simp [hv]
    rw [this, ncard_coe_finset, Finset.card_filter, Finset.sum_insert (by simp [h01, h02]),
      Finset.sum_insert (by simp [h12]), Finset.sum_singleton, add_assoc]
  obtain ⟨h₁, h₂⟩ := two_le_median3 (key (G.otherEnd v e₀)) (key (G.otherEnd v e₁))
    (key (G.otherEnd v e₂))
  refine ⟨?_, ?_⟩ <;> rw [hcount, hcount] <;> simp only [← not_le] <;> split_ifs at h₁ h₂ ⊢ <;>
    omega

end Multigraph

end Cslib.Circuits.Frontier
