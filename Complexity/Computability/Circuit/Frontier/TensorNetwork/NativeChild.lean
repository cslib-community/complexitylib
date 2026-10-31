/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.DescribedLift
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildEntries
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ChildNumbering
public import Complexity.Computability.PolyTime.PacketPacking
public import Complexity.Foundations.Combinatorics.BudgetTuples
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# The native child networks of an active call

An active call of the contraction recursion of [OpenAI2026ETH] (§D.4.5–§D.4.7, pp. 62–64) on a
network of vertex descriptors evaluates, for each node `t`, each interpolation value `ζ`, each
exponent tuple `β` and each group `g`, the child network of group `g`. This file builds that child
natively as a network of descriptors (`NativeChild.nativeChild`), from the parent, the native
packing of its edges (`Cslib.PacketPacking.nativePacking`) and `(t, ζ, β, g)`, and proves that it
has the contraction of the child of the mode splitting at the node (`TensorNetwork.callSplitting`).

**The child.** Its vertices are numbered as in `ChildNumbering.childVertexEquiv` and its edges as
in `ChildNumbering.childEdgeEquiv`:

* the vertices of group `g`, in order, keep their descriptors, and their ports are their parent
  ports, *in the parent's order*, each renumbered to its child edge: a row port by its position
  among the row ports of group `g`, a column port by the number of row ports plus its position
  among the column ports (`NativeChild.childEdgeOf`). A retained vertex reads its ports in its own
  order, so its ports are not sorted;
* the packet `q` is a new vertex whose ports are its child edges in increasing order
  (`ChildNumbering.childPorts`), each tagged with whether it is a row port and with the slot of its
  parent edge, and whose descriptor carries the node, the value `ζ`, the symbols of `q` against
  `g` and the slice of `β` at `q` (`NativeChild.packetCtx`, `NativeChild.betaSlice`), at the
  child's precision `p_t`.

The modes of the node are listed packet-major (`NativeChild.modeList`): the mode `(q, y, b)` is at
`q · 2 ^ (i + 1) · p_t + y · p_t + b`, so the dense exponents of packet `q` are a slice of `β`, and
`β` stands for the mode tuple `BudgetTuples.ofList (modeList …) β`.

**Correctness** (`NativeChild.contraction_nativeChild`). Over `O = ℤ_(2)[U] / (f)` the parent is
the network `DescribedNetwork.toNetwork` with the lifts of its entries, and its packing is the
native packing, which is `PacketPacking.packing` of its edges (`PacketPacking.nativePacking_eq`),
moved to the ends of the parent (`NativeChild.parentPacking`). Along `reductionLift`, the entries of
the native child in `A_{p_t}` give the contraction of the child of `callSplitting` at the lift of
`ζ` and the mode tuple of `β`: the retained vertices by `ModeSplitting.child_tensor_inl_eq_tensor`
and the packets by `TensorNetwork.map_val_entry_child_inr`, assembled by
`DescribedNetwork.contraction_eq_of_ports`. The native child is again rows-first, with its retained
vertices as rows (`NativeChild.isRowsFirstBipartite_nativeChild`).

## Main definitions

* `Cslib.PacketPacking.Packing.relabel`: a packing moved to other ends of the edges.
* `Cslib.Circuits.Frontier.NativeChild.nativeChild`: the native child.
* `Cslib.Circuits.Frontier.NativeChild.childRows`: its number of rows.
* `Cslib.Circuits.Frontier.NativeChild.modeList`, `Cslib.Circuits.Frontier.NativeChild.modeWeights`:
  the modes of a node, packet-major, and their weights.
* `Cslib.Circuits.Frontier.NativeChild.parentPacking`: the packing of the parent over `O`.

## Main results

* `Cslib.Circuits.Frontier.NativeChild.contraction_nativeChild`: the native child has the
  contraction of the child.
* `Cslib.Circuits.Frontier.NativeChild.isRowsFirstBipartite_nativeChild`: it is rows-first.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5–§D.4.7, pp. 62–64.
-/

public section

/-! ### Moving a packing to other ends -/

namespace Cslib.PacketPacking

variable {E R C R' C' : Type*} {rowOf : E → R} {colOf : E → C} {a r : ℕ}

/-- **A packing moved to other ends of the edges**: the same packets, slots and symbols, with the
labels of the new ends read through `ρ` and `κ`, which agree with the old labels at the ends of
every edge. -/
@[expose] def Packing.relabel (P : Packing rowOf colOf a r) (rowOf' : E → R') (colOf' : E → C')
    (ρ : R' → Fin a → Fin r) (κ : C' → Fin a → Fin r)
    (hρ : ∀ e, ρ (rowOf' e) = P.rowLabel (rowOf e))
    (hκ : ∀ e, κ (colOf' e) = P.colLabel (colOf e)) :
    Packing rowOf' colOf' a r where
  rowLabel := ρ
  colLabel := κ
  numPackets := P.numPackets
  packet := P.packet
  slot := P.slot
  symbols := P.symbols
  injective := P.injective
  labels_eq e i := by rw [hρ, hκ]; exact P.labels_eq e i

end Cslib.PacketPacking

namespace Cslib.Circuits.Frontier

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

namespace NativeChild

open ChildNumbering GaloisRingArith NativePacket
open ContractionSchedule (nodePrecision)

/-! ### The native child -/

/-- **The groups of the vertices** in coordinate `i`: digit `i` of the row word of a row
(`v < r`), and of the column word of a column. -/
@[expose] def groupsOf (r i k : ℕ) (words : List (List ℕ) × List (List ℕ)) : List ℕ :=
  (List.range k).map fun v =>
    if v < r then (words.1.getD v []).getD i 0 else (words.2.getD (v - r) []).getD i 0

/-- The parent edges whose end `sel` is in group `g`, in order: the row ports of group `g` for
`sel = Prod.fst`, its column ports for `sel = Prod.snd`. -/
@[expose] def portEdges (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (sel : ℕ × ℕ → ℕ) :
    List ℕ :=
  (List.range ends.length).filter fun e => groups.getD (sel (ends.getD e (0, 0))) 0 = g

/-- The position of the edge `e` among the parent edges whose end `sel` is in group `g`. -/
@[expose] def portRank (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (sel : ℕ × ℕ → ℕ)
    (e : ℕ) : ℕ :=
  (List.range e).countP fun e' => groups.getD (sel (ends.getD e' (0, 0))) 0 = g

/-- **The child edge of the parent port `e` of the vertex `v`**: for a row, its position among the
row ports of group `g`; for a column, the number of row ports plus its position among the column
ports. -/
@[expose] def childEdgeOf (r : ℕ) (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (v e : ℕ) : ℕ :=
  if v < r then portRank groups g ends Prod.fst e
  else (portEdges groups g ends Prod.fst).length + portRank groups g ends Prod.snd e

/-- **The parent edge of the child edge `j`**: the `j`-th row port of group `g`, or the
`(j - R)`-th column port for `R` row ports. -/
@[expose] def parentEdge (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (j : ℕ) : ℕ :=
  if j < (portEdges groups g ends Prod.fst).length then
    (portEdges groups g ends Prod.fst).getD j 0
  else (portEdges groups g ends Prod.snd).getD (j - (portEdges groups g ends Prod.fst).length) 0

/-- **The context of the packet `q`** in the child of group `g` at the node `t` of valuation `i`
and the interpolation value `ζ`: the precision `p_t` and `p_t` exponents per tile, `2 ^ a` slots,
`2 ^ (i + 1)` tiles, and the symbols of `q` in coordinate `i` against `g`. -/
@[expose] def packetCtx (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ : List ℕ) (g q : ℕ) : PacketCtx where
  p := pt
  fl := fl
  a := a
  L := 2 ^ a
  i := i
  tiles := 2 ^ (i + 1)
  t := t
  nb := pt
  e₁ := decide ((PacketPacking.packetSymbols a 64 q i).1 = g)
  e₂ := decide ((PacketPacking.packetSymbols a 64 q i).2 = g)
  differ := decide ((PacketPacking.packetSymbols a 64 q i).1 ≠
    (PacketPacking.packetSymbols a 64 q i).2)
  cols := []
  ζ := ζ

/-- **The dense exponents of the packet `q`**: its slice of the packet-major list `β`. -/
@[expose] def betaSlice (i pt : ℕ) (β : List ℕ) (q : ℕ) : List ℕ :=
  (β.drop (q * (2 ^ (i + 1) * pt))).take (2 ^ (i + 1) * pt)

/-- The default vertex: no ports and the empty table. -/
abbrev defaultVertex : List ℕ × VertexDesc := ([], .inl [])

/-- **The native child** of group `g` at the node `t` of valuation `i`, the interpolation value
`ζ`, the precision `p_t` and the packet-major exponents `β`, of the rows-first parent `D` with `r`
rows and the native packing `pk` of its edges: the vertices of group `g` with their descriptors
and renumbered ports, then one packet vertex per packet. -/
@[expose] def nativeChild (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ : List ℕ) (r : ℕ)
    (D : DescribedNetwork VertexDesc)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (β : List ℕ) (g : ℕ) :
    DescribedNetwork VertexDesc :=
  let groups := groupsOf r i D.vertices.length pk.1
  let cedges := childEdgeList groups g D.edgeEnds (pk.2.2.map Prod.fst)
  ⟨cedges.length,
    ((List.range D.vertices.length).filter fun v => groups.getD v 0 = g).map (fun v =>
      (((D.vertices.getD v defaultVertex).1.map (childEdgeOf r groups g D.edgeEnds v)),
        (D.vertices.getD v defaultVertex).2)) ++
    (List.range pk.2.1).map fun q =>
      (childPorts cedges (groups.count g + q),
        .inr (packetCtx fl a i pt t ζ g q,
          (childPorts cedges (groups.count g + q)).map fun j =>
            (decide (j < (portEdges groups g D.edgeEnds Prod.fst).length),
              (pk.2.2.getD (parentEdge groups g D.edgeEnds j) (0, 0)).2),
          betaSlice i pt β q))⟩

/-- **The number of rows of the native child**: the number of vertices of group `g`. -/
@[expose] def childRows (r i : ℕ) (D : DescribedNetwork VertexDesc)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (g : ℕ) : ℕ :=
  (groupsOf r i D.vertices.length pk.1).count g

/-! ### The modes of a node -/

/-- The packet-major numbering of the modes `(q, y, b)`: `q · T p + y · p + b`. -/
@[expose] def modeEquiv (P T p : ℕ) : Fin P × Fin T × Fin p ≃ Fin (P * (T * p)) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

/-- **The modes of a node, packet-major.** -/
@[expose] def modeList (P T p : ℕ) : List (Fin P × Fin T × Fin p) :=
  List.ofFn (modeEquiv P T p).symm

/-- **The weights of the modes, packet-major**: the mode `(q, y, b)` has weight `b + 1`. -/
@[expose] def modeWeights (P T p : ℕ) : List ℕ :=
  (List.range (P * (T * p))).map fun j => j % p + 1

theorem modeEquiv_apply_val {P T p : ℕ} (Z : Fin P × Fin T × Fin p) :
    (modeEquiv P T p Z : ℕ) = Z.1 * (T * p) + (Z.2.1 * p + Z.2.2) := by
  simp only [modeEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq, finProdFinEquiv_apply_val]
  ring

theorem nodup_modeList (P T p : ℕ) : (modeList P T p).Nodup :=
  List.nodup_ofFn.mpr (modeEquiv P T p).symm.injective

theorem mem_modeList {P T p : ℕ} (Z : Fin P × Fin T × Fin p) : Z ∈ modeList P T p :=
  List.mem_ofFn.mpr ⟨modeEquiv P T p Z, by simp⟩

theorem idxOf_modeList {P T p : ℕ} (Z : Fin P × Fin T × Fin p) :
    (modeList P T p).idxOf Z = modeEquiv P T p Z := by
  have h : (modeList P T p)[(modeEquiv P T p Z : ℕ)]'(by simp [modeList]) = Z := by
    simp [modeList]
  have := List.Nodup.idxOf_getElem (nodup_modeList P T p) (modeEquiv P T p Z : ℕ)
    (by simp [modeList])
  rwa [h] at this

/-- The last coordinate of a mode is its number modulo `p`. -/
theorem val_modeEquiv_symm_snd_snd {P T p : ℕ} (j : Fin (P * (T * p))) :
    (((modeEquiv P T p).symm j).2.2 : ℕ) = j % p := by
  obtain ⟨Z, hZ⟩ : ∃ Z, (modeEquiv P T p).symm j = Z := ⟨_, rfl⟩
  have hj : (j : ℕ) = Z.1 * (T * p) + (Z.2.1 * p + Z.2.2) := by
    rw [← modeEquiv_apply_val, ← hZ, Equiv.apply_symm_apply]
  rw [hZ, hj, show (Z.1 : ℕ) * (T * p) + (Z.2.1 * p + Z.2.2) = Z.2.2 + p * (Z.1 * T + Z.2.1) by
    ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt Z.2.2.2]

/-- The weights listed along the modes are `modeWeights`. -/
theorem map_modeList_weight (P T p : ℕ) :
    (modeList P T p).map (fun Z => (Z.2.2 : ℕ) + 1) = modeWeights P T p := by
  apply List.ext_getElem (by simp [modeList, modeWeights])
  intro j h₁ h₂
  simp only [modeList, List.getElem_map, List.getElem_ofFn, modeWeights, List.getElem_range,
    val_modeEquiv_symm_snd_snd]

/-- **The slice of a packet** reads the mode tuple of `β`: entry `b + p y` of the slice of `q` is
the exponent of the mode `(q, y, b)`. -/
theorem getD_betaSlice {P i pt : ℕ} (β : List ℕ) (q : Fin P) (Z : Fin (2 ^ (i + 1)) × Fin pt) :
    (betaSlice i pt β q).getD (finProdFinEquiv Z) 0 =
      BudgetTuples.ofList (modeList P (2 ^ (i + 1)) pt) β (q, Z) := by
  have hZ : (finProdFinEquiv Z : ℕ) < 2 ^ (i + 1) * pt := (finProdFinEquiv Z).2
  rw [BudgetTuples.ofList, idxOf_modeList, modeEquiv_apply_val, betaSlice,
    List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hZ, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, finProdFinEquiv_apply_val]
  congr 2
  ring

/-! ### The native lists in a numbered network -/

section Bridge

variable {m k s : ℕ} (src tgt : Fin m → Fin k) (group : Fin k → Fin s) (g : Fin s)

/-- Reading the group of an end of an edge from the lists. -/
theorem getD_ofFn_group (sel : ℕ × ℕ → ℕ) (endF : Fin m → Fin k)
    (hsel : ∀ e, sel ((src e : ℕ), (tgt e : ℕ)) = endF e) (e : Fin m) :
    (List.ofFn fun v => (group v : ℕ)).getD
        (sel ((List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))).getD e (0, 0))) 0 =
      group (endF e) := by
  rw [List.getD_ofFn, hsel, List.getD_ofFn]

/-- **The native ports of group `g` at the end `sel`** are its members, in order. -/
theorem portEdges_eq (sel : ℕ × ℕ → ℕ) (endF : Fin m → Fin k)
    (hsel : ∀ e, sel ((src e : ℕ), (tgt e : ℕ)) = endF e) :
    portEdges (List.ofFn fun v => (group v : ℕ)) g (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ)))
        sel = (members fun e => group (endF e) = g).map Fin.val := by
  rw [portEdges, List.length_ofFn, ← List.map_coe_finRange_eq_range, List.filter_map, members]
  congr 1
  refine List.filter_congr fun e _ => ?_
  simp only [Function.comp_apply, getD_ofFn_group src tgt group sel endF hsel, Fin.val_inj]

/-- **The native position of a port** is its position among the members. -/
theorem portRank_eq (sel : ℕ × ℕ → ℕ) (endF : Fin m → Fin k)
    (hsel : ∀ e, sel ((src e : ℕ), (tgt e : ℕ)) = endF e) (e : Fin m) :
    portRank (List.ofFn fun v => (group v : ℕ)) g (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ)))
        sel e = rank (fun e => group (endF e) = g) e := by
  have hr : List.range e = ((List.finRange m).take e).map Fin.val := by
    rw [List.map_take, List.map_coe_finRange_eq_range, List.take_range, min_eq_left e.2.le]
  rw [portRank, rank, hr, List.countP_map]
  refine List.countP_congr fun u _ => ?_
  simp only [Function.comp_apply, getD_ofFn_group src tgt group sel endF hsel, Fin.val_inj,
    decide_eq_true_eq]

/-- Counting a group among the groups of the vertices gives the number of its vertices. -/
theorem count_ofFn_group :
    (List.ofFn fun v => (group v : ℕ)).count (g : ℕ) = (members fun v => group v = g).length := by
  rw [List.ofFn_eq_map, List.count, List.countP_map, members, ← List.countP_eq_length_filter]
  refine List.countP_congr fun u _ => ?_
  simp [Fin.val_inj]

/-- The native vertices of group `g` are its members, in order. -/
theorem filter_range_group :
    (List.range k).filter (fun v => (List.ofFn fun v => (group v : ℕ)).getD v 0 = (g : ℕ)) =
      (members fun v => group v = g).map Fin.val := by
  rw [← List.map_coe_finRange_eq_range, List.filter_map, members]
  congr 1
  refine List.filter_congr fun v _ => ?_
  simp only [Function.comp_apply, List.getD_ofFn, Fin.val_inj]

variable {r : ℕ} (hsrc : ∀ e, (src e : ℕ) < r) (htgt : ∀ e, r ≤ (tgt e : ℕ))
include hsrc

/-- **The child edge of a row port** is its number in `childEdgeEquiv`. -/
theorem childEdgeOf_src (e : Fin m) (h : group (src e) = g) :
    childEdgeOf r (List.ofFn fun v => (group v : ℕ)) g
        (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) (src e) e =
      (childEdgeEquiv src tgt group g (.inl ⟨e, h⟩) : ℕ) := by
  rw [childEdgeOf, ite_eq_left (hsrc e), portRank_eq src tgt group g Prod.fst src (fun _ => rfl)]
  simp [childEdgeEquiv]

omit hsrc in
include htgt in
/-- **The child edge of a column port** is its number in `childEdgeEquiv`. -/
theorem childEdgeOf_tgt (e : Fin m) (h : group (tgt e) = g) :
    childEdgeOf r (List.ofFn fun v => (group v : ℕ)) g
        (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) (tgt e) e =
      (childEdgeEquiv src tgt group g (.inr ⟨e, h⟩) : ℕ) := by
  rw [childEdgeOf, ite_eq_right (by have := htgt e; omega),
    portRank_eq src tgt group g Prod.snd tgt (fun _ => rfl),
    portEdges_eq src tgt group g Prod.fst src (fun _ => rfl), List.length_map]
  simp [childEdgeEquiv]

omit hsrc in
/-- **The parent edge of a numbered child edge.** -/
theorem parentEdge_childEdgeEquiv (c : ChildEdge src tgt group g) :
    parentEdge (List.ofFn fun v => (group v : ℕ)) g
        (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) (childEdgeEquiv src tgt group g c) =
      (Sum.elim (fun e => (e.1 : ℕ)) (fun e => (e.1 : ℕ)) c) := by
  rw [parentEdge, portEdges_eq src tgt group g Prod.fst src (fun _ => rfl),
    portEdges_eq src tgt group g Prod.snd tgt (fun _ => rfl), List.length_map]
  rcases c with c | c
  · have hlt := rank_lt (fun e => group (src e) = g) c.1 c.2
    simp only [childEdgeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.val_castAdd, rankEquiv_apply_val, Sum.elim_inl]
    rw [ite_eq_left hlt, List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
      getElem_rank (fun e => group (src e) = g) c.1 c.2]
  · have hlt := rank_lt (fun e => group (tgt e) = g) c.1 c.2
    simp only [childEdgeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, rankEquiv_apply_val, Sum.elim_inr]
    rw [ite_eq_right (by omega), Nat.add_sub_cancel_left,
      List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
      getElem_rank (fun e => group (tgt e) = g) c.1 c.2]

omit hsrc in
/-- A numbered child edge is a row port exactly when its number is below the number of row
ports. -/
theorem lt_length_portEdges_iff (c : ChildEdge src tgt group g) :
    (childEdgeEquiv src tgt group g c : ℕ) <
        (portEdges (List.ofFn fun v => (group v : ℕ)) g
          (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) Prod.fst).length ↔ c.isLeft := by
  rw [portEdges_eq src tgt group g Prod.fst src (fun _ => rfl), List.length_map]
  rcases c with c | c
  · simp only [childEdgeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, Fin.val_castAdd, rankEquiv_apply_val, Sum.isLeft_inl, iff_true]
    exact rank_lt (fun e => group (src e) = g) c.1 c.2
  · simp only [childEdgeEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
      finSumFinEquiv_apply_right, Fin.val_natAdd, Sum.isLeft_inr, Bool.false_eq_true, iff_false]
    omega

end Bridge

/-- A filter-map that keeps every entry is a map. -/
theorem map_filterMap_of_isSome {α β γ : Type*} (f : α → Option β) (y : β → γ) (d : γ)
    (l : List α) (h : ∀ x ∈ l, (f x).isSome) :
    (l.filterMap f).map y = l.map fun x => ((f x).map y).getD d := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (h x List.mem_cons_self)
    rw [List.filterMap_cons_some hb, List.map_cons, List.map_cons, hb,
      ih fun x' hx' => h x' (List.mem_cons_of_mem _ hx')]
    rfl

/-! ### The parent over `O` -/

section Parent

variable {fl : List ℕ} (hirr : Irreducible ((monicOf fl).map (Int.castRingHom (ZMod 2))))
  {D : DescribedNetwork VertexDesc} {r : ℕ} (hD : D.IsRowsFirstBipartite r)

/-- The valuation ring `O = ℤ_(2)[U] / (f)` of `f = monicOf fl`. -/
noncomputable abbrev RingO : Subring (AdjoinRoot ((monicOf fl).map (Int.castRingHom ℚ))) :=
  (AdjoinRoot.padicValuation 2 (monic_monicOf fl) hirr).integer

/-- **The parent over `O`**: the network of the descriptors with the lifts of their entries. -/
@[expose] noncomputable def parentNetwork :
    TensorNetwork (RingO hirr) Bool (Fin D.vertices.length) (Fin D.numEdges) :=
  D.toNetwork hD fun d bs => liftO hirr (d.entry bs)

/-- The sides of the parent: the first `r` vertices are the rows. -/
@[expose] def parentSide (r : ℕ) {k : ℕ} (v : Fin k) : Bool := decide ((v : ℕ) < r)

theorem parentSide_src (j : Fin D.numEdges) : parentSide r (D.srcFin hD j) = true :=
  decide_eq_true (DescribedNetwork.srcFin_lt hD j)

theorem parentSide_tgt (j : Fin D.numEdges) : parentSide r (D.tgtFin hD j) = false :=
  decide_eq_false (by have := DescribedNetwork.le_tgtFin hD j; omega)

/-- The row of an edge, among the rows. -/
@[expose] def rowOfP (j : Fin D.numEdges) : Fin r :=
  ⟨D.srcFin hD j, DescribedNetwork.srcFin_lt hD j⟩

/-- The column of an edge, among the columns. -/
@[expose] def colOfP (j : Fin D.numEdges) : Fin (D.vertices.length - r) :=
  ⟨D.tgtFin hD j - r, by
    have := DescribedNetwork.le_tgtFin hD j
    have := (D.tgtFin hD j).2
    omega⟩

/-- **The native packing of the parent**: `nativePacking` of its `(row, column)` edges, with `r`
rows, `k - r` columns, packets of `2 ^ a` slots and `64` symbols. -/
@[expose] def nativeParentPacking (r a : ℕ) (D : DescribedNetwork VertexDesc) :
    (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  PacketPacking.nativePacking r (D.vertices.length - r) a 64
    (D.edgeEnds.map fun e => (e.1, e.2 - r))

/-- The `(row, column)` edges of the parent. -/
theorem edgeEnds_shift :
    D.edgeEnds.map (fun e => (e.1, e.2 - r)) = PacketPacking.edgeList (rowOfP hD) (colOfP hD) := by
  rw [DescribedNetwork.edgeEnds_eq hD, PacketPacking.edgeList, List.map_ofFn]
  rfl

/-- **The packing of the parent over `O`**: `PacketPacking.packing` of its `(row, column)` edges,
moved to the ends of the parent. -/
@[expose] noncomputable def parentPacking (a : ℕ) :
    PacketPacking.Packing (D.srcFin hD) (D.tgtFin hD) a 64 :=
  (PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).relabel (D.srcFin hD) (D.tgtFin hD)
    (fun v => if h : (v : ℕ) < r then
      (PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).rowLabel ⟨v, h⟩ else fun _ => 0)
    (fun v => if h : r ≤ (v : ℕ) then
      (PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).colLabel ⟨v - r, by omega⟩
      else fun _ => 0)
    (fun e => by rw [dite_eq_left (DescribedNetwork.srcFin_lt hD e)]; rfl)
    (fun e => by rw [dite_eq_left (DescribedNetwork.le_tgtFin hD e)]; rfl)

/-- **The native packing of the parent is its packing over `O`** when `64 ^ a` is at most the
number of edges: the words of its labels, its number of packets, and the packet and slot of each
edge. -/
theorem nativeParentPacking_eq {a : ℕ} (hK : 64 ^ a ≤ D.numEdges) :
    nativeParentPacking r a D =
      ((List.ofFn fun v => BalancedSchedules.scheduleToWord
          ((PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).rowLabel v),
        List.ofFn fun w => BalancedSchedules.scheduleToWord
          ((PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).colLabel w)),
        (parentPacking hD a).numPackets,
        List.ofFn fun e => (((parentPacking hD a).packet e : ℕ),
          ((parentPacking hD a).slot e : ℕ))) := by
  rw [nativeParentPacking, edgeEnds_shift hD, PacketPacking.nativePacking_eq _ _ hK]
  rfl

/-- **The native groups of the parent** in coordinate `i < a` are the groups of the packing. -/
theorem groupsOf_eq {a i : ℕ} (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) :
    groupsOf r i D.vertices.length (nativeParentPacking r a D).1 =
      List.ofFn fun v => (packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩ v : ℕ) := by
  rw [nativeParentPacking_eq hD hK]
  apply List.ext_getElem (by simp [groupsOf])
  intro v h₁ h₂
  simp only [groupsOf, List.getElem_map, List.getElem_range, List.getElem_ofFn, packingGroup,
    parentSide, parentPacking, PacketPacking.Packing.relabel]
  have hvk : v < D.vertices.length := by simpa using h₂
  by_cases hv : v < r
  · rw [ite_eq_left hv, decide_eq_true hv, ite_eq_left rfl, dite_eq_left hv,
      List.getD_ofFn (fun v : Fin r => BalancedSchedules.scheduleToWord _) ⟨v, hv⟩,
      BalancedSchedules.scheduleToWord, List.getD_ofFn (fun t : Fin a => _) ⟨i, hia⟩]
  · have hvr : r ≤ v := by omega
    have hlt : v - r < D.vertices.length - r := by omega
    rw [ite_eq_right hv, decide_eq_false hv, ite_eq_right (by simp), dite_eq_left hvr,
      List.getD_ofFn (fun w : Fin (D.vertices.length - r) => BalancedSchedules.scheduleToWord _)
        ⟨v - r, hlt⟩, BalancedSchedules.scheduleToWord,
      List.getD_ofFn (fun t : Fin a => _) ⟨i, hia⟩]

/-- **The mode splitting at a node of the parent** over `O`: `callSplitting` of the parent with
its packing, at the node `t`, the precision `p`, and the lift of the interpolation value `ζ`. -/
@[expose] noncomputable def parentSplitting (a p u h : ℕ) (hua : u ≤ a) {t : ℤ}
    (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (ζ : List ℕ) :=
  TensorNetwork.callSplitting (RingO hirr)
    (AdjoinRoot.algebraMap_mem_integer_padicValuation _ hirr) (parentNetwork hirr hD)
    (parentSide r) (parentSide_src hD) (parentSide_tgt hD) (parentPacking hD a) p u h hua ht hq
    (liftO hirr ζ)

section Fields

variable {a p u h : ℕ} (hua : u ≤ a) {t : ℤ} (ht : t ∈ recoveryNodes a)
  (hq : 0 < taperMult u h t) (ζ : List ℕ)

/-- The rows of the splitting are the first `r` vertices. -/
theorem parentSplitting_side : (parentSplitting hirr hD a p u h hua ht hq ζ).side = parentSide r :=
  TensorNetwork.callSplitting_side (RingO hirr) _ (parentNetwork hirr hD) (parentSide r) _ _
    (parentPacking hD a) p u h hua ht hq (liftO hirr ζ)

/-- The groups of the splitting are the groups of the packing in coordinate `v₂(t)`. -/
theorem parentSplitting_group : (parentSplitting hirr hD a p u h hua ht hq ζ).group =
    packingGroup (parentSide r) (parentPacking hD a)
      ⟨_, padicValInt_lt_of_taperMult_pos hq hua⟩ :=
  TensorNetwork.callSplitting_group (RingO hirr) _ (parentNetwork hirr hD) (parentSide r) _ _
    (parentPacking hD a) p u h hua ht hq (liftO hirr ζ)

/-- The packets of the splitting are the packets of the packing. -/
theorem parentSplitting_packet :
    (parentSplitting hirr hD a p u h hua ht hq ζ).packet = (parentPacking hD a).packet :=
  TensorNetwork.callSplitting_packet (RingO hirr) _ (parentNetwork hirr hD) (parentSide r) _ _
    (parentPacking hD a) p u h hua ht hq (liftO hirr ζ)

end Fields

section Numbered

variable {P : ℕ} (group : Fin D.vertices.length → Fin 64) (packet : Fin D.numEdges → Fin P)
  (slot : Fin D.numEdges → ℕ) (g : Fin 64)

/-- The ports of a retained vertex: its parent ports, each as its child edge. -/
@[expose] def retainedPort (v : {v // group v = g}) (j : ℕ) :
    Option (ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :=
  if hj : j < D.numEdges then
    if (v.1 : ℕ) < r then
      if hg : group (D.srcFin hD ⟨j, hj⟩) = g then some (.inl ⟨⟨j, hj⟩, hg⟩) else none
    else if hg : group (D.tgtFin hD ⟨j, hj⟩) = g then some (.inr ⟨⟨j, hj⟩, hg⟩) else none
  else none

/-- **A parent port of a retained vertex is a child edge**, numbered by `childEdgeOf`. -/
theorem retainedPort_spec (v : {v // group v = g}) {j : ℕ}
    (hj : j ∈ (D.vertices[(v.1 : ℕ)]'v.1.2).1) :
    ∃ c, retainedPort hD group g v j = some c ∧
      (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g c : ℕ) =
        childEdgeOf r (List.ofFn fun v => (group v : ℕ)) g
          (List.ofFn fun e => ((D.srcFin hD e : ℕ), (D.tgtFin hD e : ℕ))) v j := by
  have hjm : j < D.numEdges := hD.1 _ (List.getElem_mem _) j hj
  have hends := (DescribedNetwork.mem_ports_iff hD v.1 ⟨j, hjm⟩).mp hj
  have hsrcr := DescribedNetwork.srcFin_lt hD
  have htgtr := DescribedNetwork.le_tgtFin hD
  by_cases hvr : (v.1 : ℕ) < r
  · have hs : D.srcFin hD ⟨j, hjm⟩ = v.1 := hends.resolve_right fun h => by
      have := htgtr ⟨j, hjm⟩
      rw [h] at this
      omega
    have hg : group (D.srcFin hD ⟨j, hjm⟩) = g := hs ▸ v.2
    refine ⟨.inl ⟨⟨j, hjm⟩, hg⟩, ?_, ?_⟩
    · simp only [retainedPort, dite_eq_left hjm, ite_eq_left hvr, dite_eq_left hg]
    · have := childEdgeOf_src (D.srcFin hD) (D.tgtFin hD) group g hsrcr ⟨j, hjm⟩ hg
      rw [show ((v.1 : Fin _) : ℕ) = (D.srcFin hD ⟨j, hjm⟩ : ℕ) by rw [hs]]
      exact this.symm
  · have ht : D.tgtFin hD ⟨j, hjm⟩ = v.1 := hends.resolve_left fun h => by
      have := hsrcr ⟨j, hjm⟩
      rw [h] at this
      exact hvr this
    have hg : group (D.tgtFin hD ⟨j, hjm⟩) = g := ht ▸ v.2
    refine ⟨.inr ⟨⟨j, hjm⟩, hg⟩, ?_, ?_⟩
    · simp only [retainedPort, dite_eq_left hjm, ite_eq_right hvr, dite_eq_left hg]
    · have := childEdgeOf_tgt (D.srcFin hD) (D.tgtFin hD) group g htgtr ⟨j, hjm⟩ hg
      rw [show ((v.1 : Fin _) : ℕ) = (D.tgtFin hD ⟨j, hjm⟩ : ℕ) by rw [ht]]
      exact this.symm

/-- **The ports of the packet vertex `q`**: the child edges of packet `q`, in increasing order of
their numbers. -/
@[expose] def packetPorts (q : Fin P) : List (ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :=
  ((List.finRange _).filter fun j =>
    childTgt (D.srcFin hD) (D.tgtFin hD) group packet g
      ((childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j) = .inr q).map
    (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm

/-- **The ports of the numbered child vertices**: the renumbered parent ports of a retained
vertex, and the child edges of a packet. -/
@[expose] def numberedPorts :
    ChildVertex group g P → List (ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :=
  Sum.elim (fun v => (D.vertices[(v.1 : ℕ)]'v.1.2).1.filterMap (retainedPort hD group g v))
    (packetPorts hD group packet g)

/-- **The descriptors of the numbered child vertices**: the parent descriptor of a retained
vertex, and the packet descriptor of a packet. -/
@[expose] def numberedDesc (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ β : List ℕ) :
    ChildVertex group g P → VertexDesc :=
  Sum.elim (fun v => (D.vertices[(v.1 : ℕ)]'v.1.2).2) fun q =>
    .inr (packetCtx fl a i pt t ζ g q,
      (packetPorts hD group packet g q).map fun c =>
        (c.isLeft, slot (Sum.elim Subtype.val Subtype.val c)),
      betaSlice i pt β q)

/-- The bit that a retained vertex reads at a parent port. -/
theorem getD_map_retainedPort (v : {v // group v = g}) {j : ℕ}
    (hj : j ∈ (D.vertices[(v.1 : ℕ)]'v.1.2).1)
    (y : ChildEdge (D.srcFin hD) (D.tgtFin hD) group g → Bool) :
    ((retainedPort hD group g v j).map y).getD false =
      if parentSide r v.1 then
        (if hg : group (D.srcFin hD ⟨j, hD.1 _ (List.getElem_mem _) j hj⟩) = g then
          y (.inl ⟨_, hg⟩) else false)
      else
        (if hg : group (D.tgtFin hD ⟨j, hD.1 _ (List.getElem_mem _) j hj⟩) = g then
          y (.inr ⟨_, hg⟩) else false) := by
  have hjm : j < D.numEdges := hD.1 _ (List.getElem_mem _) j hj
  by_cases hvr : (v.1 : ℕ) < r
  · simp only [retainedPort, dite_eq_left hjm, ite_eq_left hvr, parentSide, decide_eq_true hvr,
      ite_true]
    split_ifs <;> rfl
  · simp only [retainedPort, dite_eq_left hjm, ite_eq_right hvr, parentSide,
      decide_eq_false hvr, Bool.false_eq_true, ite_false]
    split_ifs <;> rfl

/-- The ports of a packet are its child edges. -/
theorem mem_packetPorts (q : Fin P) (c : ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :
    c ∈ packetPorts hD group packet g q ↔ packet (Sum.elim Subtype.val Subtype.val c) = q := by
  simp only [packetPorts, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases hc : (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j with c | c <;>
      rw [hc] at hj <;> simpa [childTgt] using hj
  · intro hc
    refine ⟨childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g c, ?_, by simp⟩
    rw [Equiv.symm_apply_apply]
    rcases c with c | c <;> simpa [childTgt] using hc

/-- The ports of a packet are distinct. -/
theorem nodup_packetPorts (q : Fin P) : (packetPorts hD group packet g q).Nodup :=
  ((List.nodup_finRange _).filter _).map (Equiv.injective _)

/-- **The native ports of a packet** are its numbered ports. -/
theorem childPorts_packet (q : Fin P) :
    childPorts (List.ofFn fun j =>
        (((childVertexEquiv (P := P) group g) (childSrc (D.srcFin hD) (D.tgtFin hD) group g
          ((childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j)) : ℕ),
        ((childVertexEquiv (P := P) group g) (childTgt (D.srcFin hD) (D.tgtFin hD) group packet g
          ((childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j)) : ℕ)))
        ((List.ofFn fun v => (group v : ℕ)).count (g : ℕ) + q) =
      (packetPorts hD group packet g q).map fun c =>
        (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g c : ℕ) := by
  have h1 : (List.ofFn fun v => (group v : ℕ)).count (g : ℕ) + q =
      ((childVertexEquiv (P := P) group g) (.inr q) : ℕ) := by
    rw [count_ofFn_group]
    simp [childVertexEquiv]
  rw [h1, childPorts, List.length_ofFn, ← List.map_coe_finRange_eq_range, List.filter_map,
    packetPorts, List.map_map]
  congr 1
  · funext j
    simp
  · refine List.filter_congr fun j _ => ?_
    simp only [Function.comp_apply, List.getD_ofFn, Fin.val_inj, Equiv.apply_eq_iff_eq,
      decide_eq_decide]
    constructor
    · rintro (h | h)
      · rcases hc : (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g).symm j with c | c <;>
          rw [hc] at h <;> simp [childSrc] at h
      · exact h
    · exact Or.inr

/-- **The native child is the numbered child**: with the groups, packets and slots of the native
packing given by functions, the native child lists the numbered child vertices with their
numbered ports and descriptors. -/
theorem nativeChild_eq (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ β : List ℕ)
    (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ))
    (hgroups : groupsOf r i D.vertices.length pk.1 = List.ofFn fun v => (group v : ℕ))
    (hpk1 : pk.2.1 = P) (hpk2 : pk.2.2 = List.ofFn fun e => ((packet e : ℕ), slot e)) :
    nativeChild fl a i pt t ζ r D pk β g =
      ⟨(members fun e => group (D.srcFin hD e) = g).length +
          (members fun e => group (D.tgtFin hD e) = g).length,
        List.ofFn fun c =>
          ((numberedPorts hD group packet g ((childVertexEquiv (P := P) group g).symm c)).map
              fun e => (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) group g e : ℕ),
            numberedDesc hD group packet slot g fl a i pt t ζ β
              ((childVertexEquiv (P := P) group g).symm c))⟩ := by
  have hpackets : pk.2.2.map Prod.fst = List.ofFn fun e => (packet e : ℕ) := by
    rw [hpk2, List.map_ofFn]
    rfl
  have hcedges := childEdgeList_eq (P := P) (D.srcFin hD) (D.tgtFin hD) group packet g
  have hsrcr := DescribedNetwork.srcFin_lt hD
  have htgtr := DescribedNetwork.le_tgtFin hD
  simp only [nativeChild]
  rw [hgroups, DescribedNetwork.edgeEnds_eq hD, hpackets, hpk1, hpk2, hcedges]
  simp only [DescribedNetwork.mk.injEq, List.length_ofFn, true_and]
  refine Eq.trans ?_ (List.ofFn_add (n := (members fun v => group v = g).length) (m := P)).symm
  congr 1
  · rw [filter_range_group, List.map_map]
    apply List.ext_getElem (by simp)
    intro n h₁ h₂
    have hn : n < (members fun v => group v = g).length := by simpa using h₁
    have hmem : group (members fun v => group v = g)[n] = g :=
      of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hn)).2
    have hevl : (childVertexEquiv (P := P) group g).symm
        (Fin.castLE (Nat.le_add_right _ _) ⟨n, hn⟩) =
          .inl ⟨(members fun v => group v = g)[n], hmem⟩ := by
      rw [childVertexEquiv, Equiv.symm_trans_apply,
        show Fin.castLE (Nat.le_add_right _ _) ⟨n, hn⟩ = Fin.castAdd _ ⟨n, hn⟩ from rfl,
        finSumFinEquiv_symm_apply_castAdd]
      rfl
    simp only [List.getElem_map, List.getElem_ofFn, Function.comp_apply]
    rw [hevl]
    refine Prod.ext ?_ ?_
    · simp only [numberedPorts, Sum.elim_inl]
      rw [List.getD_eq_getElem _ _ ((members fun v => group v = g)[n]).2]
      rw [map_filterMap_of_isSome _ _ 0 _ fun j hj => by
        obtain ⟨c, hc, -⟩ := retainedPort_spec hD group g ⟨_, hmem⟩ hj
        rw [hc]
        rfl]
      refine List.map_congr_left fun j hj => ?_
      obtain ⟨c, hc, hce⟩ := retainedPort_spec hD group g ⟨_, hmem⟩ hj
      rw [hc]
      exact hce.symm
    · simp only [numberedDesc, Sum.elim_inl]
      rw [List.getD_eq_getElem _ _ ((members fun v => group v = g)[n]).2]
  · apply List.ext_getElem (by simp)
    intro n h₁ h₂
    have hn : n < P := by simpa using h₁
    have hevr : (childVertexEquiv (P := P) group g).symm (Fin.natAdd _ ⟨n, hn⟩) =
        .inr ⟨n, hn⟩ := by
      rw [childVertexEquiv, Equiv.symm_trans_apply, finSumFinEquiv_symm_apply_natAdd]
      rfl
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [hevr]
    have hcpq := childPorts_packet hD group packet g ⟨n, hn⟩
    simp only at hcpq
    refine Prod.ext hcpq ?_
    simp only [numberedDesc, Sum.elim_inr]
    congr 2
    refine Prod.ext ?_ rfl
    rw [hcpq, List.map_map]
    refine List.map_congr_left fun c _ => ?_
    refine Prod.ext ?_ ?_
    · simp only [Function.comp_apply]
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact lt_length_portEdges_iff (D.srcFin hD) (D.tgtFin hD) group g c
    · simp only [Function.comp_apply]
      rw [parentEdge_childEdgeEquiv]
      rcases c with c | c <;> simp

/-- **The ports of a retained vertex are its child edges.** -/
theorem mem_filterMap_retainedPort (x : {v // group v = g})
    (c : ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :
    c ∈ (D.vertices[(x.1 : ℕ)]'x.1.2).1.filterMap (retainedPort hD group g x) ↔
      childSrc (P := P) (D.srcFin hD) (D.tgtFin hD) group g c = .inl x := by
  have hsrcr := DescribedNetwork.srcFin_lt hD
  have htgtr := DescribedNetwork.le_tgtFin hD
  rw [List.mem_filterMap]
  rcases c with ⟨e, he⟩ | ⟨e, he⟩
  · simp only [childSrc, Sum.elim_inl, Sum.inl.injEq, Subtype.ext_iff]
    constructor
    · rintro ⟨j, hj, hc⟩
      simp only [retainedPort] at hc
      split_ifs at hc with hjm hxr hg hg <;>
        simp only [Option.some.injEq, Sum.inl.injEq, reduceCtorEq,
          Subtype.mk.injEq] at hc
      subst hc
      rcases (DescribedNetwork.mem_ports_iff hD x.1 ⟨j, hjm⟩).mp hj with h | h
      · exact h
      · have := htgtr ⟨j, hjm⟩
        rw [h] at this
        omega
    · intro hs
      refine ⟨e.val, (DescribedNetwork.mem_ports_iff hD x.1 e).mpr (Or.inl hs), ?_⟩
      have hxr : (x.1 : ℕ) < r := hs ▸ hsrcr e
      simp only [retainedPort, dite_eq_left e.2, ite_eq_left hxr, Fin.eta]
      rw [dite_eq_left he]
  · simp only [childSrc, Sum.elim_inr, Sum.inl.injEq, Subtype.ext_iff]
    constructor
    · rintro ⟨j, hj, hc⟩
      simp only [retainedPort] at hc
      split_ifs at hc with hjm hxr hg hg <;>
        simp only [Option.some.injEq, Sum.inr.injEq, reduceCtorEq,
          Subtype.mk.injEq] at hc
      subst hc
      rcases (DescribedNetwork.mem_ports_iff hD x.1 ⟨j, hjm⟩).mp hj with h | h
      · have := hsrcr ⟨j, hjm⟩
        rw [h] at this
        exact absurd this hxr
      · exact h
    · intro ht
      refine ⟨e.val, (DescribedNetwork.mem_ports_iff hD x.1 e).mpr (Or.inr ht), ?_⟩
      have hxr : ¬ (x.1 : ℕ) < r := by have := htgtr e; rw [ht] at this; omega
      simp only [retainedPort, dite_eq_left e.2, ite_eq_right hxr, Fin.eta]
      rw [dite_eq_left he]

/-- A retained port names its parent edge. -/
theorem val_of_retainedPort_eq_some {x : {v // group v = g}} {j : ℕ}
    {c : ChildEdge (D.srcFin hD) (D.tgtFin hD) group g} (h : retainedPort hD group g x j = some c) :
    (Sum.elim (fun e => (e.1 : ℕ)) (fun e => (e.1 : ℕ)) c) = j := by
  simp only [retainedPort] at h
  split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h <;> rfl

include hD in
/-- The ports of a vertex of a rows-first network are distinct. -/
theorem nodup_ports (v : Fin D.vertices.length) : (D.vertices[v]).1.Nodup := by
  refine List.nodup_iff_count_le_one.mpr fun j => ?_
  by_cases hj : j ∈ (D.vertices[v]).1
  · have hjm : j < D.numEdges := hD.1 _ (List.getElem_mem _) j hj
    obtain ⟨s, t, hs, ht, -, -, hsc, htc, hinc⟩ := DescribedNetwork.incident_eq hD hjm
    rcases (DescribedNetwork.mem_ports_iff hD v ⟨j, hjm⟩).mp hj with h | h
    · have hv : (v : ℕ) = s := by
        rw [← h]
        simp [DescribedNetwork.srcFin, hinc]
      have : (D.vertices[v]).1 = (D.vertices[s]).1 := by simp only [Fin.getElem_fin, hv]
      rw [this, hsc]
    · have hv : (v : ℕ) = t := by
        rw [← h]
        simp [DescribedNetwork.tgtFin, hinc]
      have : (D.vertices[v]).1 = (D.vertices[t]).1 := by simp only [Fin.getElem_fin, hv]
      rw [this, htc]
  · rw [List.count_eq_zero.mpr hj]
    exact Nat.zero_le _

/-- **The numbered ports of a child vertex are its child edges**, without repetition. -/
theorem mem_numberedPorts (v : ChildVertex group g P)
    (c : ChildEdge (D.srcFin hD) (D.tgtFin hD) group g) :
    c ∈ numberedPorts hD group packet g v ↔
      childSrc (D.srcFin hD) (D.tgtFin hD) group g c = v ∨
        childTgt (D.srcFin hD) (D.tgtFin hD) group packet g c = v := by
  rcases v with x | q
  · rw [numberedPorts, Sum.elim_inl, mem_filterMap_retainedPort]
    refine ⟨Or.inl, fun h => h.resolve_right ?_⟩
    rcases c with c | c <;> simp [childTgt]
  · rw [numberedPorts, Sum.elim_inr, mem_packetPorts]
    rcases c with c | c <;> simp [childSrc, childTgt]

theorem nodup_numberedPorts (v : ChildVertex group g P) :
    (numberedPorts hD group packet g v).Nodup := by
  rcases v with x | q
  · exact (nodup_ports hD x.1).filterMap fun j j' c hc hc' => by
      rw [← val_of_retainedPort_eq_some hD group g hc, ← val_of_retainedPort_eq_some hD group g hc']
  · exact nodup_packetPorts hD group packet g q

end Numbered

/-- **Being rows-first depends only on the multisets of ports.** -/
theorem isRowsFirstBipartite_ofFn_iff {T T' : Type} {k l r : ℕ} (F : Fin k → List ℕ × T)
    (F' : Fin k → List ℕ × T') (h : ∀ x, (F x).1.Perm (F' x).1) :
    (⟨l, List.ofFn F⟩ : DescribedNetwork T).IsRowsFirstBipartite r ↔
      (⟨l, List.ofFn F'⟩ : DescribedNetwork T').IsRowsFirstBipartite r := by
  have hc (i : ℕ) : (List.ofFn F).map (fun v => v.1.count i) =
      (List.ofFn F').map (fun v => v.1.count i) := by
    simp only [List.map_ofFn]
    congr 1
    funext x
    exact (h x).count_eq i
  have hm : (∀ v ∈ List.ofFn F, ∀ i ∈ v.1, i < l) ↔ (∀ v ∈ List.ofFn F', ∀ i ∈ v.1, i < l) := by
    simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]
    exact forall_congr' fun x => forall_congr' fun i => imp_congr_left (h x).mem_iff
  simp only [DescribedNetwork.IsRowsFirstBipartite, List.map_take, List.map_drop, hc, hm]

section Rows

variable {a i : ℕ} (hK : 64 ^ a ≤ D.numEdges) (hia : i < a)

include hD hK hia in
/-- **The native child is rows-first**, with its retained vertices as its rows. -/
theorem isRowsFirstBipartite_nativeChild (pt : ℕ) (t : ℤ) (ζ β : List ℕ) (g : Fin 64) :
    (nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g).IsRowsFirstBipartite
      (childRows r i D (nativeParentPacking r a D) g) := by
  have hgroups := groupsOf_eq hD hK hia
  have hpk1 : (nativeParentPacking r a D).2.1 = (parentPacking hD a).numPackets := by
    rw [nativeParentPacking_eq hD hK]
  have hpk2 : (nativeParentPacking r a D).2.2 = List.ofFn fun e =>
      (((parentPacking hD a).packet e : ℕ), ((parentPacking hD a).slot e : ℕ)) := by
    rw [nativeParentPacking_eq hD hK]
  rw [childRows, hgroups, count_ofFn_group,
    nativeChild_eq hD _ (parentPacking hD a).packet (fun e => ((parentPacking hD a).slot e : ℕ)) g
      fl a i pt t ζ β _ hgroups hpk1 hpk2]
  -- The incidence of the numbered child, with zero tensors.
  let N : TensorNetwork ℕ Bool
      (ChildVertex (packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩) g
        (parentPacking hD a).numPackets)
      (ChildEdge (D.srcFin hD) (D.tgtFin hD)
        (packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩) g) :=
    { src := childSrc (D.srcFin hD) (D.tgtFin hD) _ g
      tgt := childTgt (D.srcFin hD) (D.tgtFin hD) _ (parentPacking hD a).packet g
      tensor := fun _ _ => 0
      tensor_congr := fun _ _ _ _ => rfl }
  have hside : ∀ e, ((childVertexEquiv (P := (parentPacking hD a).numPackets) _ g (N.src e) :
      Fin _) : ℕ) < (members fun v =>
        packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩ v = g).length ↔
      ¬ ((childVertexEquiv (P := (parentPacking hD a).numPackets) _ g (N.tgt e) : Fin _) : ℕ) <
        (members fun v =>
          packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩ v = g).length := by
    rintro (e | e) <;> simp only [N, childSrc, childTgt, childVertexEquiv, Sum.elim_inl,
      Sum.elim_inr, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      rankEquiv_apply_val, Sum.map_inr]
    · exact ⟨fun _ => by omega, fun _ => rank_lt _ _ e.2⟩
    · exact ⟨fun _ => by omega, fun _ => rank_lt _ _ e.2⟩
  have hexp := TensorNetwork.isRowsFirstBipartite_toExplicit N
    (childVertexEquiv (P := (parentPacking hD a).numPackets) _ g)
    (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) _ g) _ hside
  refine (isRowsFirstBipartite_ofFn_iff _ _ fun c => ?_).mpr hexp
  set v := (childVertexEquiv (P := (parentPacking hD a).numPackets) _ g).symm c
  refine (List.perm_ext_iff_of_nodup ((nodup_numberedPorts hD _ _ g v).map
    (Fin.val_injective.comp (Equiv.injective _)))
    ((N.nodup_explicitPorts _ v).map Fin.val_injective)).mpr fun n => ?_
  simp only [List.mem_map, TensorNetwork.mem_explicitPorts, mem_numberedPorts]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨_, by simpa [N] using he, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, by simpa [N] using hj, by simp⟩

end Rows


section Child

variable {a p u h : ℕ} (hK : 64 ^ a ≤ D.numEdges) (hua : u ≤ a) {t : ℤ}
  (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (ζ β : List ℕ) (g : Fin 64)

/-- The valuation of the node. -/
local notation "iₜ" => padicValInt 2 t
/-- The precision of the node. -/
local notation "ptₜ" => nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t)
/-- The mode splitting at the node. -/
local notation "S₀" => parentSplitting hirr hD a p u h hua ht hq ζ
/-- The mode tuple of `β`. -/
local notation "β₀" => BudgetTuples.ofList
  (modeList (PacketPacking.Packing.numPackets (parentPacking hD a))
  (2 ^ (padicValInt 2 t + 1)) (nodePrecision p h a (Fintype.card (Fin D.numEdges))
    (padicValInt 2 t))) β
/-- The numbering of the child vertices. -/
local notation "ev₀" =>
  childVertexEquiv (P := PacketPacking.Packing.numPackets (parentPacking hD a))
  (TensorNetwork.ModeSplitting.group (parentSplitting hirr hD a p u h hua ht hq ζ)) g
/-- The numbering of the child edges. -/
local notation "ee₀" => childEdgeEquiv (D.srcFin hD) (D.tgtFin hD)
  (TensorNetwork.ModeSplitting.group (parentSplitting hirr hD a p u h hua ht hq ζ)) g

/-- **The entries of the retained vertices** of the numbered child are the tensors of the child. -/
theorem entry_numbered_inl (v : {v // (S₀).group v = g})
    (y : ChildEdge (D.srcFin hD) (D.tgtFin hD) (S₀).group g → Bool) :
    reductionLift (monic_monicOf fl) hirr ptₜ (val ptₜ fl
        ((numberedDesc hD (S₀).group (S₀).packet (fun e => ((parentPacking hD a).slot e : ℕ)) g
          fl a iₜ ptₜ t ζ β (.inl v)).entry
          ((numberedPorts hD (S₀).group (S₀).packet g (.inl v)).map y))) =
      ((S₀).child β₀ g).tensor (.inl v) y := by
  rw [TensorNetwork.ModeSplitting.child_tensor_inl_eq_tensor (S₀) β₀ g v y,
    TensorNetwork.map_tensor,
    ← mk_liftO, parentSplitting_side hirr hD hua ht hq ζ]
  simp only [numberedDesc, numberedPorts, Sum.elim_inl, parentNetwork,
    DescribedNetwork.toNetwork, DescribedNetwork.wordBits]
  congr 3
  rw [map_filterMap_of_isSome _ _ false _ fun j hj => by
    obtain ⟨c, hc, -⟩ := retainedPort_spec hD (S₀).group g v hj
    rw [hc]
    rfl]
  refine List.map_congr_left fun j hj => ?_
  rw [getD_map_retainedPort hD (S₀).group g v hj y,
    List.getD_ofFn_of_lt _ (hD.1 _ (List.getElem_mem _) j hj)]
  rfl

/-- **The entries of the packet vertices** of the numbered child are the tensors of the child. -/
theorem entry_numbered_inr (q : Fin (parentPacking hD a).numPackets)
    (y : ChildEdge (D.srcFin hD) (D.tgtFin hD) (S₀).group g → Bool) :
    reductionLift (monic_monicOf fl) hirr ptₜ (val ptₜ fl
        ((numberedDesc hD (S₀).group (S₀).packet (fun e => ((parentPacking hD a).slot e : ℕ)) g
          fl a iₜ ptₜ t ζ β (.inr q)).entry
          ((numberedPorts hD (S₀).group (S₀).packet g (.inr q)).map y))) =
      ((S₀).child β₀ g).tensor (.inr q) y := by
  have hia : iₜ < a := padicValInt_lt_of_taperMult_pos hq hua
  have hsym := PacketPacking.packetSymbols_eq (rowOfP hD) (colOfP hD) _ _ q ⟨iₜ, hia⟩
  simp only [numberedDesc, numberedPorts, Sum.elim_inr]
  exact TensorNetwork.map_val_entry_child_inr (N := (parentNetwork hirr hD).map
      (Ideal.Quotient.mk (nodeIdeal (RingO hirr) (Fintype.card (Fin D.numEdges)) a h p t)))
    (parentSide r) (parentSide_src hD) (parentSide_tgt hD)
    (packingGroup_src_tgt (parentSide r) (parentSide_src hD) (parentSide_tgt hD)
      (parentPacking hD a) ⟨iₜ, hia⟩)
    (packing_slot_lt (parentPacking hD a)) hia _ _ (two_pow_eq_zero_twoPowIdeal _ _)
    (Finset.mem_of_mem_erase ht) (two_pow_padicValInt_dvd_and_not_dvd (Finset.ne_of_mem_erase ht)).1
    (two_pow_padicValInt_dvd_and_not_dvd (Finset.ne_of_mem_erase ht)).2 β₀ g q _
    (nodup_packetPorts hD (S₀).group (S₀).packet g q)
    (fun c => (mem_packetPorts hD (S₀).group (S₀).packet g q c).trans (by
      rw [parentSplitting_packet hirr hD hua ht hq ζ]
      exact Iff.rfl))
    (packetCtx fl a iₜ ptₜ t ζ g q) (betaSlice iₜ ptₜ β q)
    (reductionLift (monic_monicOf fl) hirr ptₜ) (mk_liftO hirr ptₜ ζ).symm rfl rfl rfl rfl rfl rfl
    (by simp only [packetCtx, hsym, Fin.val_inj]; rfl)
    (by simp only [packetCtx, hsym, Fin.val_inj]; rfl)
    (by simp only [packetCtx, hsym, ne_eq, Fin.val_inj]; rfl)
    (getD_betaSlice β q) y

include hK in
/-- **The native child has the contraction of the child** ([OpenAI2026ETH], §D.4.6). For a
rows-first parent with `64 ^ a` at most its number of edges, a node `t` of positive multiplicity
with `u ≤ a`, an interpolation value `ζ`, packet-major exponents `β` and a group `g`, the native
child at the precision `p_t` of the node, with the entries of its descriptors in `A_{p_t}` mapped
along `reductionLift` to `O / (2 ^ {p_t})`, has the contraction of the child of group `g` of the
mode splitting at `t` (`parentSplitting`) at the mode tuple of `β`. -/
theorem contraction_nativeChild :
    (nativeChild fl a (padicValInt 2 t)
        (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t)) t ζ r D
        (nativeParentPacking r a D) β g).contraction
      (fun d bs => reductionLift (monic_monicOf fl) hirr
        (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t))
        (val (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t)) fl
          (d.entry bs))) =
    ((parentSplitting hirr hD a p u h hua ht hq ζ).child
      (BudgetTuples.ofList (modeList (parentPacking hD a).numPackets (2 ^ (padicValInt 2 t + 1))
        (nodePrecision p h a (Fintype.card (Fin D.numEdges)) (padicValInt 2 t))) β)
      g).contraction := by
  have hia : iₜ < a := padicValInt_lt_of_taperMult_pos hq hua
  have hgroups : groupsOf r iₜ D.vertices.length (nativeParentPacking r a D).1 =
      List.ofFn fun v => ((S₀).group v : ℕ) := by
    rw [parentSplitting_group hirr hD hua ht hq ζ]
    exact groupsOf_eq hD hK hia
  have hpk1 : (nativeParentPacking r a D).2.1 = (parentPacking hD a).numPackets := by
    rw [nativeParentPacking_eq hD hK]
  have hpk2 : (nativeParentPacking r a D).2.2 =
      List.ofFn fun e => (((S₀).packet e : ℕ), ((parentPacking hD a).slot e : ℕ)) := by
    rw [nativeParentPacking_eq hD hK, parentSplitting_packet hirr hD hua ht hq ζ]
  rw [nativeChild_eq hD (S₀).group (S₀).packet (fun e => ((parentPacking hD a).slot e : ℕ)) g
    fl a iₜ ptₜ t ζ β _ hgroups hpk1 hpk2]
  refine DescribedNetwork.contraction_eq_of_ports ((S₀).child β₀ g) _ _ _ _ _ ?_
  rintro (v | q) y
  · exact entry_numbered_inl hirr hD hua ht hq ζ β g v y
  · exact entry_numbered_inr hirr hD hua ht hq ζ β g q y

end Child

end Parent

end NativeChild

end Cslib.Circuits.Frontier
