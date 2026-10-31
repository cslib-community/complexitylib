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
    (hρ : ∀ e, ρ (rowOf' e) = P.rowLabel (rowOf e)) (hκ : ∀ e, κ (colOf' e) = P.colLabel (colOf e)) :
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
  rw [← List.Nodup.idxOf_getElem (nodup_modeList P T p) _ (by simp [modeList]), h]

/-- The weights listed along the modes are `modeWeights`. -/
theorem map_modeList_weight (P T p : ℕ) :
    (modeList P T p).map (fun Z => (Z.2.2 : ℕ) + 1) = modeWeights P T p := by
  apply List.ext_getElem (by simp [modeList, modeWeights])
  intro j h₁ h₂
  simp only [modeList, List.getElem_map, List.getElem_ofFn, modeWeights, List.getElem_range]
  congr 1
  have := modeEquiv_apply_val (P := P) (T := T) (p := p) ((modeEquiv P T p).symm ⟨j, by simpa
    [modeList] using h₁⟩)
  rw [Equiv.apply_symm_apply] at this
  have hb := ((modeEquiv P T p).symm ⟨j, by simpa [modeList] using h₁⟩).2.2.2
  simp only at this
  rw [this, Nat.add_mod, Nat.add_mod (_ * p), Nat.mul_mod_left, show (T * p) = p * T by ring,
    ← Nat.mul_assoc, Nat.mul_mod_left]
  simp [Nat.mod_eq_of_lt hb]

/-- **The slice of a packet** reads the mode tuple of `β`: entry `y · p + b` of the slice of `q` is
the exponent of the mode `(q, y, b)`. -/
theorem getD_betaSlice {P i pt : ℕ} (β : List ℕ) (q : Fin P) (Z : Fin (2 ^ (i + 1)) × Fin pt) :
    (betaSlice i pt β q).getD (Z.1 * pt + Z.2) 0 =
      BudgetTuples.ofList (modeList P (2 ^ (i + 1)) pt) β (q, Z) := by
  have hZ : (Z.1 : ℕ) * pt + Z.2 < 2 ^ (i + 1) * pt := by
    have h1 := Z.1.2
    have h2 := Z.2.2
    calc (Z.1 : ℕ) * pt + Z.2 < Z.1 * pt + pt := by omega
      _ = (Z.1 + 1) * pt := by ring
      _ ≤ 2 ^ (i + 1) * pt := Nat.mul_le_mul_right _ h1
  rw [BudgetTuples.ofList, idxOf_modeList, modeEquiv_apply_val, betaSlice, List.getD_eq_getD_get?,
    List.getElem?_take_of_lt hZ, List.getElem?_drop, ← List.getD_eq_getD_get?]

end NativeChild

end Cslib.Circuits.Frontier
