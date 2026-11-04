/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.VertexDesc
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedContraction
import Mathlib.Data.List.GetD

/-!
# The entries of the child networks from their descriptors

A child network of the contraction recursion of [OpenAI2026ETH] (`ModeSplitting.child`, §D.4.6,
p. 63) is carried natively as a network of vertex descriptors (`VertexDesc T`) with port lists. This
file proves that such a network has the contraction of the child, once each descriptor reads its
ports in the right order.

* **Port lists** (`DescribedNetwork.contraction_eq_of_ports`). Number the vertices and the edges of
  a Boolean tensor network `N`, and give each vertex any list of edges as its ports and a
  descriptor. If the evaluator at the descriptor of `v`, read at the bits of an assignment on its
  ports, is the tensor of `v` at that assignment, the described network has the contraction of
  `N`.
* **Retained vertices** (`ModeSplitting.child_tensor_inl_eq_tensor`). A vertex of group `g` keeps
  its tensor in the child of group `g`: a row reads its row ports and a column its column ports.
  So a retained vertex keeps its descriptor, and its ports are its parent ports, in the same
  order, renumbered as child edges.
* **Packet vertices** (`TensorNetwork.map_val_entry_child_inr`). Let the ports of the packet
  vertex `q` be the child edges of packet `q` in any order without repetition, and let its
  descriptor tag each port with whether it is a row port and with its slot, in the same order. Then
  along any ring map from `A_p` to the coefficient ring of the child, the descriptor's entry at the
  bits on its ports is the child's entry (`child_tensor_inr_cauchyModeSplitting`), for the
  packet's context matching the node `(t, ζ)`, the group `g`, the symbols of `q` and the exponents
  `β`. The tags are computed from the port list itself, so tags and bits align by construction
  (`NativePacket.sidePorts_map`).

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.contraction_eq_of_ports`: a described network with
  port lists has the contraction of the network it describes.
* `Cslib.Circuits.Frontier.NativePacket.sidePorts_map`: the ports of one side of a tagged list.
* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.child_tensor_inl_eq_tensor`: the entries
  of the retained vertices of a child.
* `Cslib.Circuits.Frontier.TensorNetwork.map_val_entry_child_inr`: the entries of the packet
  vertices of a Cauchy child, from their descriptors.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6, p. 63.
-/

public section

namespace Cslib.Circuits.Frontier

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

open Finset GaloisRingArith NativePacket

/-! ### Port lists -/

namespace DescribedNetwork

variable {T : Type} {R : Type*} [CommSemiring R] {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq E]

/-- **A described network with port lists has the contraction of the network it describes.**
Number the vertices of `N` by `ev` and its edges by `ee`, and give each vertex `v` a list of edges
`ports v` and a descriptor `desc v`. If the evaluator at `desc v`, read at the bits of every
assignment on `ports v`, is the tensor of `v` at that assignment, the described network with the
numbered ports and the descriptors has the contraction of `N`. -/
theorem contraction_eq_of_ports {k l : ℕ} (N : TensorNetwork R Bool V E) (ev : V ≃ Fin k)
    (ee : E ≃ Fin l) (ports : V → List E) (desc : V → T) (eval : T → List Bool → R)
    (h : ∀ v (x : E → Bool), eval (desc v) ((ports v).map x) = N.tensor v x) :
    (⟨l, List.ofFn fun i => ((ports (ev.symm i)).map fun e => (ee e : ℕ), desc (ev.symm i))⟩ :
      DescribedNetwork T).contraction eval = N.contraction := by
  simp only [contraction, TensorNetwork.contraction, List.map_ofFn, List.prod_ofFn]
  rw [← (ee.arrowCongr (Equiv.refl Bool)).symm.sum_comp]
  refine sum_congr rfl fun x _ => ?_
  rw [← ev.symm.prod_comp]
  refine prod_congr rfl fun v _ => ?_
  simp only [Function.comp_apply]
  rw [← h]
  congr 1
  simp only [wordBits, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, Equiv.arrowCongr_symm, Equiv.arrowCongr_apply,
    Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl, id_eq]
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

end DescribedNetwork

/-! ### The ports of one side of a tagged list -/

namespace NativePacket

/-- **The ports of one side of a tagged list.** If the ports of a vertex are tagged, in their
order, by whether they are row ports and by their slots, and the bits are read in the same order,
the ports of one side are the ports with that tag, with their slots and bits, in order. -/
theorem sidePorts_map {α : Type*} (cs : List α) (tag : α → Bool) (sl : α → ℕ) (y : α → Bool)
    (side : Bool) :
    sidePorts (cs.map fun c => (tag c, sl c)) (cs.map y) side =
      (cs.filter fun c => tag c == side).map fun c => (sl c, y c) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [sidePorts, List.length_map] at ih
    simp only [sidePorts, List.map_cons, List.length_cons, List.length_map,
      List.range_succ_eq_map, List.filter_cons, List.filter_map, List.getD_cons_zero,
      Function.comp_def, List.getD_cons_succ]
    by_cases hc : tag c == side
    · rw [ite_eq_left hc, ite_eq_left hc]
      simp only [List.map_cons, List.map_map]
      rw [← ih]
      rfl
    · rw [ite_eq_right hc, ite_eq_right hc]
      simp only [List.map_map]
      rw [← ih]
      rfl

end NativePacket

namespace TensorNetwork

/-! ### Retained vertices -/

namespace ModeSplitting

variable {R V E G P M : Type*} [CommRing R] [Fintype M] [DecidableEq V] [Fintype E]
  [DecidableEq E] [DecidableEq P] [DecidableEq G] [DecidableEq M] {N : TensorNetwork R Bool V E}
  {W : Matrix E E R} (S : ModeSplitting N W G P M)

/-- **The retained vertices of a child**: a vertex of group `g` keeps its tensor in the child of
group `g`, reading at each of its edges the child edge of that edge: a row its row ports and a
column its column ports. -/
theorem child_tensor_inl_eq_tensor (β : M → ℕ) (g : G) (v : {v // S.group v = g})
    (y : {e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g} → Bool) :
    (S.child β g).tensor (.inl v) y = N.tensor v.1 fun e =>
      if S.side v.1 then (if h : S.group (N.src e) = g then y (.inl ⟨e, h⟩) else false)
      else (if h : S.group (N.tgt e) = g then y (.inr ⟨e, h⟩) else false) := by
  simp only [child]
  by_cases hv : S.side v.1
  · rw [ite_eq_left hv]
    refine N.tensor_congr _ _ _ fun e he => ?_
    simp only [ite_eq_left hv]
    by_cases hs : N.src e = v.1
    · rw [dite_eq_left hs, dite_eq_left (hs ▸ v.2)]
    · have ht : N.tgt e = v.1 := he.resolve_left hs
      have := S.side_tgt e
      rw [ht, hv] at this
      exact absurd this (by decide)
  · rw [ite_eq_right hv]
    refine N.tensor_congr _ _ _ fun e he => ?_
    simp only [ite_eq_right hv]
    by_cases ht : N.tgt e = v.1
    · rw [dite_eq_left ht, dite_eq_left (ht ▸ v.2)]
    · have hs : N.src e = v.1 := he.resolve_right ht
      have := S.side_src e
      rw [hs] at this
      exact absurd this hv

end ModeSplitting

/-! ### Packet vertices -/

section Ports

variable {R V E G : Type*} [DecidableEq G] {N : TensorNetwork R Bool V E} {group : V → G}
  {slot : E → ℕ}

/-- The row ports of a list of child edges, with their slots and bits. -/
private theorem filter_isLeft_map {g : G}
    (cs : List ({e // group (N.src e) = g} ⊕ {e // group (N.tgt e) = g}))
    (y : {e // group (N.src e) = g} ⊕ {e // group (N.tgt e) = g} → Bool) :
    (cs.filter fun c => c.isLeft == true).map
        (fun c => (slot (Sum.elim Subtype.val Subtype.val c), y c)) =
      ((cs.filterMap Sum.getLeft?).map Subtype.val).map fun e =>
        (slot e, if h : group (N.src e) = g then y (.inl ⟨e, h⟩) else false) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rcases c with c | c
    · rw [List.filter_cons_of_pos rfl, List.filterMap_cons_some (f := Sum.getLeft?) rfl,
        List.map_cons, List.map_cons, List.map_cons, ih, dite_eq_left c.2]
      rfl
    · rw [List.filter_cons_of_neg (by simp), List.filterMap_cons_none (f := Sum.getLeft?) rfl, ih]

/-- The column ports of a list of child edges, with their slots and bits. -/
private theorem filter_isLeft_false_map {g : G}
    (cs : List ({e // group (N.src e) = g} ⊕ {e // group (N.tgt e) = g}))
    (y : {e // group (N.src e) = g} ⊕ {e // group (N.tgt e) = g} → Bool) :
    (cs.filter fun c => c.isLeft == false).map
        (fun c => (slot (Sum.elim Subtype.val Subtype.val c), y c)) =
      ((cs.filterMap Sum.getRight?).map Subtype.val).map fun e =>
        (slot e, if h : group (N.tgt e) = g then y (.inr ⟨e, h⟩) else false) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rcases c with c | c
    · rw [List.filter_cons_of_neg (by simp), List.filterMap_cons_none (f := Sum.getRight?) rfl,
        ih]
    · rw [List.filter_cons_of_pos rfl, List.filterMap_cons_some (f := Sum.getRight?) rfl,
        List.map_cons, List.map_cons, List.map_cons, ih, dite_eq_left c.2]
      rfl

end Ports

section Cauchy

variable {R V E G P : Type*} [CommRing R] [Fintype E] [DecidableEq E] [Fintype P] [DecidableEq G]
  [DecidableEq P] {N : TensorNetwork R Bool V E} {group : V → G} {packet : E → P} {slot : E → ℕ}
  {sym : P → G × G} {i : ℕ}
  (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
  (htgt : ∀ e, side (N.tgt e) = false)
  (horient : ∀ e, (group (N.src e), group (N.tgt e)) =
    if (slot e).testBit i then (sym (packet e)).swap else sym (packet e))
  {a : ℕ} (hslot : ∀ e, slot e < 2 ^ a) (hia : i < a) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
  (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) (hti : (2 : ℤ) ^ i ∣ t)
  (hti' : ¬ (2 : ℤ) ^ (i + 1) ∣ t)

/-- **The packet vertices of a Cauchy child, from their descriptors.** Let the ports of the
packet vertex `q` in the child of group `g` be the child edges of packet `q`, listed without
repetition in any order, and let the descriptor's ports tag each of them, in the same order, with
whether it is a row port and with its slot. Let the packet's context have the node `t` of
valuation `i < a`, `L = 2 ^ a` slots, `2 ^ (i + 1)` tiles and `p` exponents per tile, the symbols
of `q` against `g`, an interpolation value mapping to `ζ`, and the dense exponents of `β` at `q`.
Then along a ring map `ψ` from `A_p`, at the packet's precision, to `R`, the descriptor's entry at
the bits on its ports is the child's entry. -/
theorem map_val_entry_child_inr [DecidableEq V] {T : Type} {ev : T → List Bool → List ℕ}
    (β : P × Fin (2 ^ (i + 1)) × Fin p → ℕ) (g : G)
    (q : P)
    (cs : List ({e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti
        hti').group (N.src e) = g} ⊕
      {e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
        (N.tgt e) = g}))
    (hcs : cs.Nodup) (hcs' : ∀ c, c ∈ cs ↔ packet (Sum.elim Subtype.val Subtype.val c) = q)
    (c : PacketCtx) (βd : List ℕ) (ψ : Ring c.p c.fl →+* R) (hζ : ψ (val c.p c.fl c.ζ) = ζ)
    (ha : c.a = a) (hL : c.L = 2 ^ a) (hi : c.i = i) (htiles : c.tiles = 2 ^ (i + 1))
    (ht' : c.t = t) (hnb : c.nb = p) (he₁ : c.e₁ = decide ((sym q).1 = g))
    (he₂ : c.e₂ = decide ((sym q).2 = g)) (hdiffer : c.differ = decide ((sym q).1 ≠ (sym q).2))
    (hβ : ∀ Z : Fin (2 ^ (i + 1)) × Fin p, βd.getD (finProdFinEquiv Z) 0 = β (q, Z))
    (y : {e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
        (N.src e) = g} ⊕
      {e // (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
        (N.tgt e) = g} → Bool) :
    ψ (val c.p c.fl (VertexDesc.entry ev
        (.inr (c, cs.map fun e => (e.isLeft, slot (Sum.elim Subtype.val Subtype.val e)), βd))
        (cs.map y))) =
      ((cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').child β g).tensor
        (.inr q) y := by
  subst ha hi ht' hnb
  have hports : ∀ x ∈ cs.map (fun e => (e.isLeft, slot (Sum.elim Subtype.val Subtype.val e))),
      x.2 < 2 ^ c.a := by
    intro x hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hx
    exact hslot _
  have key := VertexDesc.map_val_entry_inr ev (c, cs.map fun e => (e.isLeft,
    slot (Sum.elim Subtype.val Subtype.val e)), βd) (cs.map y) ψ hp κ hL hia htiles ht hti hti'
    hports
  have hgoal : ψ (val c.p c.fl (VertexDesc.entry ev (.inr (c, cs.map fun e => (e.isLeft,
    slot (Sum.elim Subtype.val Subtype.val e)), βd)) (cs.map y))) = _ := key
  rw [hgoal]
  dsimp only
  have hrows : ((cs.filterMap Sum.getLeft?).map Subtype.val).Nodup :=
    ((hcs.filterMap fun _ _ _ h₁ h₂ => by
      rw [Option.mem_def, Sum.getLeft?_eq_some_iff] at h₁ h₂; rw [h₁, h₂])).map
      Subtype.val_injective
  have hcols : ((cs.filterMap Sum.getRight?).map Subtype.val).Nodup :=
    ((hcs.filterMap fun _ _ _ h₁ h₂ => by
      rw [Option.mem_def, Sum.getRight?_eq_some_iff] at h₁ h₂; rw [h₁, h₂])).map
      Subtype.val_injective
  have hrows' : ∀ e, e ∈ (cs.filterMap Sum.getLeft?).map Subtype.val ↔
      packet e = q ∧ group (N.src e) = g := by
    intro e
    simp only [List.mem_map, List.mem_filterMap, Sum.getLeft?_eq_some_iff]
    constructor
    · rintro ⟨e', ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨(hcs' _).1 hc, by simpa using e'.2⟩
    · rintro ⟨hq, hg⟩
      have hg' : (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
          (N.src e) = g := by simpa using hg
      exact ⟨⟨e, hg'⟩, ⟨_, (hcs' (.inl ⟨e, hg'⟩)).2 hq, rfl⟩, rfl⟩
  have hcols' : ∀ e, e ∈ (cs.filterMap Sum.getRight?).map Subtype.val ↔
      packet e = q ∧ group (N.tgt e) = g := by
    intro e
    simp only [List.mem_map, List.mem_filterMap, Sum.getRight?_eq_some_iff]
    constructor
    · rintro ⟨e', ⟨c, hc, rfl⟩, rfl⟩
      exact ⟨(hcs' _).1 hc, by simpa using e'.2⟩
    · rintro ⟨hq, hg⟩
      have hg' : (cauchyModeSplitting side hsrc htgt horient hslot hia κ ζ hp ht hti hti').group
          (N.tgt e) = g := by simpa using hg
      exact ⟨⟨e, hg'⟩, ⟨_, (hcs' (.inr ⟨e, hg'⟩)).2 hq, rfl⟩, rfl⟩
  rw [child_tensor_inr_cauchyModeSplitting side hsrc htgt horient hslot hia κ _ hp ht hti hti' β
    g q y hrows hrows' hcols hcols', sidePorts_map, sidePorts_map, filter_isLeft_map,
    filter_isLeft_false_map, hζ, he₁, he₂, hdiffer]
  congr 1
  funext Z
  exact hβ Z

end Cauchy

end TensorNetwork

end Cslib.Circuits.Frontier
