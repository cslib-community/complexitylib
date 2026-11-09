/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.Expander.Hom
public import CslibFrontier.Foundations.Combinatorics.Expander.Perm
public import Mathlib.Data.Fintype.Inv
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Regular rotation maps of simple graphs

Reingold's algorithm for undirected connectivity [Reingold, Section 4][Reingold2008]
[Arora and Barak, Section 21.4][AroraBarak09] works on regular graphs of a fixed degree, so it first
turns the input graph into one, without changing which vertices are connected. Each vertex `v` of a
simple graph `G` on `V` is replaced by a cycle of *slots* `(v, w)`, one for each `w : V`, the end at
`v` of a potential edge `{v, w}`. The slots of `v` are joined in the cyclic order of a permutation
`σ` of `V` with a single cycle (such as `finRotate n` on `Fin n`), and the slot `(v, w)` is joined
to the slot `(w, v)` when `v` and `w` are adjacent, and carries a self-loop otherwise.
The result, `Cslib.RotationMap.slotGraph G σ`, is a `3`-regular multigraph on `V × V`, and
`(w, b)` is reachable from `(v, a)` exactly when `w` is reachable from `v` in `G`
(`reachable_slotGraph_iff`).

To reach a prescribed label type `B`, the labels are extended along an embedding `D ↪ B`; the new
labels carry self-loops (`Cslib.RotationMap.extendLabels`). This keeps the simple graph of the
rotation map (`toSimpleGraph_extendLabels`), and when `B` has at least twice as many elements as
`D`, at least half of the edges at every vertex are self-loops
(`card_le_two_mul_edgeCount_extendLabels`), which is what makes connected components
spectral expanders (`Cslib.RotationMap.spectralExpansion_le_of_preconnected`).

## Main definitions

* `Cslib.RotationMap.decodeLabel`: the partial inverse of an embedding of labels.
* `Cslib.RotationMap.extendLabels`: extend the labels of a rotation map by self-loops.
* `Cslib.RotationMap.slotSwap`: the involution of the slots exchanging the two ends of an edge.
* `Cslib.RotationMap.SlotLabel`, `Cslib.RotationMap.slotGraph`: the `3`-regular slot graph of a
  simple graph and its labels.

## Main results

* `Cslib.RotationMap.toSimpleGraph_extendLabels`: extending the labels does not change the
  simple graph.
* `Cslib.RotationMap.card_le_two_mul_edgeCount_extendLabels`: enough new labels
  make at least half of the edges self-loops.
* `Cslib.RotationMap.reachable_slotGraph_iff`: the slot graph has the connectivity of the
  simple graph.

## References

* [O. Reingold, *Undirected connectivity in log-space*][Reingold2008]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset

variable {V D B : Type*}

section ExtendLabels

variable [Fintype D] [DecidableEq B]

/-- The label of `D` that `enc` maps to `b`, if there is one, by Mathlib's computable inverse
`Function.Embedding.invOfMemRange` on the range of `enc`. -/
def decodeLabel (enc : D ↪ B) (b : B) : Option D :=
  if h : b ∈ Set.range enc then some (enc.invOfMemRange ⟨b, h⟩) else none

/-- `decodeLabel enc` is the partial inverse of `enc`. -/
theorem decodeLabel_eq_some_iff (enc : D ↪ B) {b : B} {i : D} :
    decodeLabel enc b = some i ↔ enc i = b := by
  unfold decodeLabel
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      exact enc.left_inv_of_invOfMemRange ⟨b, h⟩
    · rintro rfl
      exact enc.right_inv_of_invOfMemRange i
  · exact ⟨fun h' ↦ h'.elim, fun hi ↦ (h ⟨i, hi⟩).elim⟩

/-- `decodeLabel enc` recovers the labels of `D`. -/
@[simp]
theorem decodeLabel_apply (enc : D ↪ B) (i : D) : decodeLabel enc (enc i) = some i :=
  (decodeLabel_eq_some_iff enc).2 rfl

/-- `decodeLabel enc b` is `none` exactly when `b` is not a label of `D`. -/
theorem decodeLabel_eq_none_iff (enc : D ↪ B) {b : B} :
    decodeLabel enc b = none ↔ ∀ i, enc i ≠ b := by
  rw [Option.eq_none_iff_forall_ne_some]
  exact forall_congr' fun i ↦ not_congr (decodeLabel_eq_some_iff enc)

/-- `G` with its labels extended along an embedding `enc : D ↪ B`: the label `enc i` at a vertex is
its `i`-th edge in `G`, and every label outside the range of `enc` is a self-loop. -/
def extendLabels (G : RotationMap V D) (enc : D ↪ B) : RotationMap V B where
  rot p := (decodeLabel enc p.2).elim p fun i ↦ Prod.map id enc (G.rot (p.1, i))
  rot_involutive p := by
    obtain ⟨v, b⟩ := p
    rcases h : decodeLabel enc b with _ | i
    · simp only [h, Option.elim_none]
    · rw [decodeLabel_eq_some_iff] at h
      subst h
      simp only [decodeLabel_apply, Option.elim_some, Prod.map_fst, Prod.map_snd, id_eq,
        Prod.mk.eta, rot_rot, Prod.map_apply]

variable (G : RotationMap V D) (enc : D ↪ B)

/-- The label `enc i` of `G.extendLabels enc` is the `i`-th edge of `G`. -/
@[simp]
theorem rot_extendLabels_apply (v : V) (i : D) :
    (G.extendLabels enc).rot (v, enc i) = Prod.map id enc (G.rot (v, i)) := by
  simp only [extendLabels, decodeLabel_apply, Option.elim_some]

/-- The `enc i`-th neighbor in `G.extendLabels enc` is the `i`-th neighbor in `G`. -/
@[simp]
theorem neighbor_extendLabels_apply (v : V) (i : D) :
    (G.extendLabels enc).neighbor v (enc i) = G.neighbor v i := by
  simp only [neighbor, rot_extendLabels_apply, Prod.map_fst, id_eq]

/-- A label outside the range of `enc` is a self-loop of `G.extendLabels enc`. -/
theorem rot_extendLabels_of_forall_ne (v : V) {b : B} (hb : ∀ i, enc i ≠ b) :
    (G.extendLabels enc).rot (v, b) = (v, b) := by
  simp only [extendLabels, (decodeLabel_eq_none_iff enc).2 hb, Option.elim_none]

/-- A label outside the range of `enc` is a self-loop of `G.extendLabels enc`. -/
theorem neighbor_extendLabels_of_forall_ne (v : V) {b : B} (hb : ∀ i, enc i ≠ b) :
    (G.extendLabels enc).neighbor v b = v :=
  congrArg Prod.fst (G.rot_extendLabels_of_forall_ne enc v hb)

/-- Extending the labels does not change the simple graph: the new edges are self-loops. -/
@[simp]
theorem toSimpleGraph_extendLabels : (G.extendLabels enc).toSimpleGraph = G.toSimpleGraph := by
  ext u v
  simp only [toSimpleGraph_adj]
  refine and_congr_right fun huv ↦ ⟨fun ⟨b, hb⟩ ↦ ?_, fun ⟨i, hi⟩ ↦ ⟨enc i, by simpa using hi⟩⟩
  by_cases h : ∃ i, enc i = b
  · obtain ⟨i, rfl⟩ := h
    exact ⟨i, by simpa using hb⟩
  · push Not at h
    rw [G.neighbor_extendLabels_of_forall_ne enc u h] at hb
    exact (huv hb).elim

/-- If `B` has at least twice as many elements as `D`, at least half of the edges at every vertex of
`G.extendLabels enc` are self-loops. -/
theorem card_le_two_mul_edgeCount_extendLabels [Fintype B] [DecidableEq V]
    (hB : 2 * Fintype.card D ≤ Fintype.card B) (v : V) :
    Fintype.card B ≤ 2 * (G.extendLabels enc).edgeCount v v := by
  have hsub : (univ.map enc)ᶜ ⊆ ({b | (G.extendLabels enc).neighbor v b = v} : Finset B) := by
    intro b hb
    rw [mem_compl, mem_map] at hb
    rw [mem_filter]
    exact ⟨mem_univ b,
      G.neighbor_extendLabels_of_forall_ne enc v fun i hi ↦ hb ⟨i, mem_univ i, hi⟩⟩
  have hcard := card_le_card hsub
  rw [card_compl, card_map, card_univ] at hcard
  rw [edgeCount]
  omega

end ExtendLabels

section Slots

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The involution of the slots `V × V` of a simple graph `G`: the slot `(v, w)` is exchanged with
`(w, v)` when `v` and `w` are adjacent, and fixed otherwise. -/
def slotSwap (p : V × V) : V × V :=
  if G.Adj p.1 p.2 then p.swap else p

/-- Exchanging the ends of an edge twice gives back the slot. -/
theorem slotSwap_involutive : Function.Involutive (slotSwap G) := by
  rintro ⟨v, w⟩
  by_cases h : G.Adj v w
  · simp [slotSwap, h, h.symm]
  · simp [slotSwap, h]

/-- The three labels of the slot graph: `inl ()` for the edge of `G` at a slot, and
`inr ((), (), false)` and `inr ((), (), true)` for the cycle of the slots of a vertex, forwards and
backwards. -/
abbrev SlotLabel : Type :=
  Unit ⊕ Unit × (Unit × Bool)

/-- The **slot graph** of a simple graph `G` on `V`, a `3`-regular multigraph on the slots `V × V`
[Reingold, Section 4][Reingold2008]: the edge `inl ()` at `(v, w)` leads to `(w, v)` if
`v` and `w` are adjacent and is a self-loop otherwise, and the edges `inr ((), (), false)` and
`inr ((), (), true)` lead to `(v, σ w)` and `(v, σ⁻¹ w)`, so that the slots of each vertex form the
cycles of `σ`. -/
def slotGraph (σ : Equiv.Perm V) : RotationMap (V × V) SlotLabel :=
  (ofInvolutive (slotSwap G) (slotSwap_involutive G)).union
    ((loops V Unit).tensor (ofPerms fun _ : Unit ↦ σ))

variable (σ : Equiv.Perm V)

/-- The edge `inl ()` of `slotGraph G σ` exchanges the two ends of an edge of `G`. -/
@[simp]
theorem rot_slotGraph_inl (p : V × V) :
    (slotGraph G σ).rot (p, .inl ()) = (slotSwap G p, .inl ()) :=
  rfl

/-- The edge `inr ((), (), false)` of `slotGraph G σ` at `(v, w)` leads to `(v, σ w)` and
returns along `inr ((), (), true)`. -/
@[simp]
theorem rot_slotGraph_inr_false (p : V × V) :
    (slotGraph G σ).rot (p, .inr ((), (), false)) = ((p.1, σ p.2), .inr ((), (), true)) :=
  rfl

/-- The edge `inr ((), (), true)` of `slotGraph G σ` at `(v, w)` leads to `(v, σ⁻¹ w)` and
returns along `inr ((), (), false)`. -/
@[simp]
theorem rot_slotGraph_inr_true (p : V × V) :
    (slotGraph G σ).rot (p, .inr ((), (), true)) = ((p.1, σ.symm p.2), .inr ((), (), false)) :=
  rfl

/-- The edge `inl ()` exchanges the two ends of an edge of `G`. -/
@[simp]
theorem neighbor_slotGraph_inl (p : V × V) :
    (slotGraph G σ).neighbor p (.inl ()) = slotSwap G p :=
  rfl

/-- The edge `inr ((), (), false)` at `(v, w)` leads to `(v, σ w)`. -/
@[simp]
theorem neighbor_slotGraph_inr_false (p : V × V) :
    (slotGraph G σ).neighbor p (.inr ((), (), false)) = (p.1, σ p.2) :=
  rfl

/-- The edge `inr ((), (), true)` at `(v, w)` leads to `(v, σ⁻¹ w)`. -/
@[simp]
theorem neighbor_slotGraph_inr_true (p : V × V) :
    (slotGraph G σ).neighbor p (.inr ((), (), true)) = (p.1, σ.symm p.2) :=
  rfl

/-- The slot graph has three labels. -/
theorem card_slotLabel : Fintype.card SlotLabel = 3 :=
  rfl

/-- The slots of a vertex are reachable from each other along the cycles of `σ`. -/
private theorem reachable_slotGraph_zpow (v w : V) (i : ℤ) :
    (slotGraph G σ).toSimpleGraph.Reachable (v, w) (v, (σ ^ i) w) := by
  induction i using Int.induction_on with
  | zero => rfl
  | succ i ih =>
    rw [add_comm, zpow_add, zpow_one, Equiv.Perm.mul_apply]
    exact ih.trans ((slotGraph G σ).reachable_neighbor (v, (σ ^ i) w) (.inr ((), (), false)))
  | pred i ih =>
    rw [sub_eq_add_neg, add_comm, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply,
      Equiv.Perm.inv_def]
    exact ih.trans ((slotGraph G σ).reachable_neighbor (v, (σ ^ (-(i : ℤ))) w)
      (.inr ((), (), true)))

/-- Every edge of the slot graph stays at a vertex of `G` or follows an edge of `G`. -/
theorem reachable_fst_of_reachable_slotGraph {p q : V × V}
    (h : (slotGraph G σ).toSimpleGraph.Reachable p q) : G.Reachable p.1 q.1 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => rfl
  | tail _ hxy ih =>
    obtain ⟨-, i, rfl⟩ := hxy
    refine ih.trans ?_
    rcases i with _ | ⟨_, _, _ | _⟩
    · rw [neighbor_slotGraph_inl, slotSwap]
      split_ifs with hadj
      · exact hadj.reachable
      · rfl
    · rfl
    · rfl

/-- **The slot graph has the connectivity of the simple graph**: if `σ` has a single cycle, the slot
`(w, b)` is reachable from `(v, a)` exactly when `w` is reachable from `v` in `G`. -/
theorem reachable_slotGraph_iff (hσ : ∀ a b, σ.SameCycle a b) {v w a b : V} :
    (slotGraph G σ).toSimpleGraph.Reachable (v, a) (w, b) ↔ G.Reachable v w := by
  refine ⟨reachable_fst_of_reachable_slotGraph G σ, fun h ↦ ?_⟩
  have hcycle (u a b : V) : (slotGraph G σ).toSimpleGraph.Reachable (u, a) (u, b) := by
    obtain ⟨i, rfl⟩ := hσ a b
    exact reachable_slotGraph_zpow G σ u a i
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h generalizing b with
  | refl => exact hcycle v a b
  | @tail x y _ hxy ih =>
    have hswap : (slotGraph G σ).neighbor (x, y) (.inl ()) = (y, x) := by
      rw [neighbor_slotGraph_inl, slotSwap, ite_eq_left hxy]
      rfl
    exact (@ih y).trans ((hswap ▸ (slotGraph G σ).reachable_neighbor (x, y) (.inl ())).trans
      (hcycle y x b))

end Slots

end Cslib.RotationMap
