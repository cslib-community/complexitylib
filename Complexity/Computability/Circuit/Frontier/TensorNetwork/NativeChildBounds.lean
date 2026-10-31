/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChild
import Mathlib.Data.List.GetD

/-!
# The sizes of the native child networks

The native child (`NativeChild.nativeChild`) of a rows-first parent with the native packing of its
edges keeps the two invariants of the recursion of [OpenAI2026ETH] (§D.4.6, p. 63) that its
running time needs:

* **at most `M / 16` edges** (`NativeChild.sixteen_mul_numEdges_nativeChild_le`) under the size
  hypothesis `2 Δ D² ≤ M` of (D.6), `D = 64 ^ (2 a)`, for a parent with `M` edges and maximum
  degree `Δ`: the child has one edge per port of its group, and each group has at most `2 M / 64`
  ports on each side (`PacketPacking.row_ports_packing_le`). This is
  `TensorNetwork.mul_card_edges_child_callSplitting_le` for the native numbering;
* **the degree bound** (`NativeChild.length_le_of_mem_vertices_nativeChild`): a vertex of the
  parent keeps its ports, and a packet vertex has at most `2 L` ports, `L = 2 ^ a`, so the child
  again has maximum degree at most `Δ` when `2 L ≤ Δ`. This is
  `TensorNetwork.ModeSplitting.rowsToColumnsLE_child` for the native numbering.

Both need `64 ^ a ≤ M`, under which the native packing is the packing of Lemma D.3
(`NativeChild.nativeParentPacking_eq`), and a node of valuation `i < a`.

## Main results

* `Cslib.Circuits.Frontier.NativeChild.numEdges_nativeChild_eq`: the edges of the child are the
  ports of its group.
* `Cslib.Circuits.Frontier.NativeChild.sixteen_mul_numEdges_nativeChild_le`: at most `M / 16`
  edges.
* `Cslib.Circuits.Frontier.NativeChild.length_le_of_mem_vertices_nativeChild`: the degree bound.
* `Cslib.Circuits.Frontier.NativeChild.numPackets_nativeParentPacking_mul_le`: at most `3 M / L`
  packets.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.3 (pp. 58–59) and
  §D.4.6 (p. 63).
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open Finset ChildNumbering

variable {r a i : ℕ} {D : DescribedNetwork VertexDesc} (hD : D.IsRowsFirstBipartite r)

/-- The group of a vertex of the parent in coordinate `i < a` of its packing. -/
noncomputable abbrev parentGroup (a : ℕ) {i : ℕ} (hia : i < a) :
    Fin D.vertices.length → Fin 64 :=
  packingGroup (parentSide r) (parentPacking hD a) ⟨i, hia⟩

/-- **The native child is the numbered child** of the packing of the parent, when `64 ^ a ≤ M` and
`i < a`. -/
theorem nativeChild_nativeParentPacking_eq (hK : 64 ^ a ≤ D.numEdges) (hia : i < a)
    (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) (g : Fin 64) :
    nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g =
      ⟨(members fun e => parentGroup hD a hia (D.srcFin hD e) = g).length +
          (members fun e => parentGroup hD a hia (D.tgtFin hD e) = g).length,
        List.ofFn fun c =>
          ((numberedPorts hD (parentGroup hD a hia) (parentPacking hD a).packet g
              ((childVertexEquiv (P := (parentPacking hD a).numPackets) (parentGroup hD a hia)
                g).symm c)).map
              fun e => (childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia) g e : ℕ),
            numberedDesc hD (parentGroup hD a hia) (parentPacking hD a).packet
              (fun e => ((parentPacking hD a).slot e : ℕ)) g fl a i pt t ζ β
              ((childVertexEquiv (P := (parentPacking hD a).numPackets) (parentGroup hD a hia)
                g).symm c))⟩ :=
  nativeChild_eq hD _ _ _ g fl a i pt t ζ β _ (groupsOf_eq hD hK hia)
    (by rw [nativeParentPacking_eq hD hK]) (by rw [nativeParentPacking_eq hD hK])

/-- The members of a predicate are as many as its elements. -/
theorem length_members {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (members p).length = #{v | p v} := by
  rw [← Fintype.card_subtype, Fintype.card_congr (rankEquiv p), Fintype.card_fin]

/-- **The edges of the native child are the ports of its group**: the row ports of group `g`, then
its column ports. -/
theorem numEdges_nativeChild_eq (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) (fl : List ℕ) (pt : ℕ)
    (t : ℤ) (ζ β : List ℕ) (g : Fin 64) :
    (nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g).numEdges =
      #{e | (parentPacking hD a).rowLabel (D.srcFin hD e) ⟨i, hia⟩ = g} +
        #{e | (parentPacking hD a).colLabel (D.tgtFin hD e) ⟨i, hia⟩ = g} := by
  rw [nativeChild_nativeParentPacking_eq hD hK hia]
  simp only [length_members]
  rw [card_packingGroup_src (parentSide r) (parentSide_src hD),
    card_packingGroup_tgt (parentSide r) (parentSide_tgt hD)]

/-- A row of a rows-first network is the row of at most as many edges as it has ports. -/
theorem card_rowOfP_le (v : Fin r) :
    #{e | rowOfP hD e = v} ≤ (D.vertices.getD v ([], .inl [])).1.length := by
  by_cases hv : (v : ℕ) < D.vertices.length
  · rw [List.getD_eq_getElem _ _ hv]
    calc #{e | rowOfP hD e = v}
        ≤ #((D.vertices[(v : ℕ)]'hv).1.toFinset) := by
          refine card_le_card_of_injOn (fun e => (e : ℕ)) (fun e he => ?_)
            (fun e _ e' _ h => Fin.ext h)
          simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at he
          rw [mem_coe, List.mem_toFinset]
          exact (DescribedNetwork.mem_ports_iff hD ⟨v, hv⟩ e).mpr
            (Or.inl (Fin.ext (show (D.srcFin hD e : ℕ) = v from congrArg Fin.val he)))
      _ ≤ _ := List.toFinset_card_le _
  · have : #{e | rowOfP hD e = v} = 0 := by
      refine card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e _ he => hv ?_)
      have := (D.srcFin hD e).2
      rw [show (D.srcFin hD e : ℕ) = v from congrArg Fin.val he] at this
      exact this
    omega

/-- A column of a rows-first network is the column of at most as many edges as it has ports. -/
theorem card_colOfP_le (w : Fin (D.vertices.length - r)) :
    #{e | colOfP hD e = w} ≤ (D.vertices.getD (r + w) ([], .inl [])).1.length := by
  have hv : r + (w : ℕ) < D.vertices.length := by have := w.2; omega
  rw [List.getD_eq_getElem _ _ hv]
  calc #{e | colOfP hD e = w}
      ≤ #((D.vertices[r + (w : ℕ)]'hv).1.toFinset) := by
        refine card_le_card_of_injOn (fun e => (e : ℕ)) (fun e he => ?_)
          (fun e _ e' _ h => Fin.ext h)
        simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at he
        rw [mem_coe, List.mem_toFinset]
        have hle := DescribedNetwork.le_tgtFin hD e
        have hw : (D.tgtFin hD e : ℕ) - r = w := congrArg Fin.val he
        exact (DescribedNetwork.mem_ports_iff hD ⟨r + w, hv⟩ e).mpr
          (Or.inr (Fin.ext (by simp only; omega)))
    _ ≤ _ := List.toFinset_card_le _

include hD in
/-- **At most `M / 16` edges in a native child**, under the size hypothesis `2 Δ D² ≤ M` of (D.6),
`D = 64 ^ (2 a)`, for a rows-first parent with `M ≥ 64 ^ a` edges and maximum degree `Δ`, at a node
of valuation `i < a`. -/
theorem sixteen_mul_numEdges_nativeChild_le (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) {Δ : ℕ}
    (hdeg : ∀ v ∈ D.vertices, v.1.length ≤ Δ) (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ D.numEdges)
    (fl : List ℕ) (pt : ℕ) (t : ℤ) (ζ β : List ℕ) (g : Fin 64) :
    16 * (nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g).numEdges ≤
      D.numEdges := by
  have hdeg' (v : ℕ) : (D.vertices.getD v ([], .inl [])).1.length ≤ Δ := by
    by_cases hv : v < D.vertices.length
    · rw [List.getD_eq_getElem _ _ hv]
      exact hdeg _ (List.getElem_mem hv)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  have hrow : ∀ v, #{e | rowOfP hD e = v} ≤ Δ := fun v => (card_rowOfP_le hD v).trans (hdeg' _)
  have hcol : ∀ w, #{e | colOfP hD e = w} ≤ Δ := fun w => (card_colOfP_le hD w).trans (hdeg' _)
  have hM' : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ Fintype.card (Fin D.numEdges) := by
    rwa [Fintype.card_fin]
  have h1 := PacketPacking.row_ports_packing_le (rowOfP hD) (colOfP hD) a 64 hrow hcol hM'
    ⟨i, hia⟩ g
  have h2 := PacketPacking.col_ports_packing_le (rowOfP hD) (colOfP hD) a 64 hrow hcol hM'
    ⟨i, hia⟩ g
  rw [Fintype.card_fin] at h1 h2
  rw [numEdges_nativeChild_eq hD hK hia]
  have e1 : #{e | (parentPacking hD a).rowLabel (D.srcFin hD e) ⟨i, hia⟩ = g} =
      #{e | (PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).rowLabel (rowOfP hD e)
        ⟨i, hia⟩ = g} := by
    congr 1
    refine filter_congr fun e _ => ?_
    simp only [parentPacking, PacketPacking.Packing.relabel,
      dite_eq_left (DescribedNetwork.srcFin_lt hD e)]
    rfl
  have e2 : #{e | (parentPacking hD a).colLabel (D.tgtFin hD e) ⟨i, hia⟩ = g} =
      #{e | (PacketPacking.packing (rowOfP hD) (colOfP hD) a 64).colLabel (colOfP hD e)
        ⟨i, hia⟩ = g} := by
    congr 1
    refine filter_congr fun e _ => ?_
    simp only [parentPacking, PacketPacking.Packing.relabel,
      dite_eq_left (DescribedNetwork.le_tgtFin hD e)]
    rfl
  rw [e1, e2]
  omega

include hD in
/-- **At most `3 M / L` packets** (Lemma D.3 (1)) in the native packing of a rows-first parent with
`M ≥ 64 ^ a` edges and maximum degree `Δ`, under (D.6): `2 Δ D² ≤ M` and `L D ≤ M`,
`D = 64 ^ (2 a)`, `L = 2 ^ a`. -/
theorem numPackets_nativeParentPacking_mul_le (hK : 64 ^ a ≤ D.numEdges) {Δ : ℕ}
    (hdeg : ∀ v ∈ D.vertices, v.1.length ≤ Δ) (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ D.numEdges)
    (hL : 2 ^ a * 64 ^ (2 * a) ≤ D.numEdges) :
    (nativeParentPacking r a D).2.1 * 2 ^ a ≤ 3 * D.numEdges := by
  have hdeg' (v : ℕ) : (D.vertices.getD v ([], .inl [])).1.length ≤ Δ := by
    by_cases hv : v < D.vertices.length
    · rw [List.getD_eq_getElem _ _ hv]
      exact hdeg _ (List.getElem_mem hv)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact Nat.zero_le _
  have h := PacketPacking.numPackets_packing_mul_le (rowOfP hD) (colOfP hD) a 64
    (fun v => (card_rowOfP_le hD v).trans (hdeg' _))
    (fun w => (card_colOfP_le hD w).trans (hdeg' _))
    (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
  rw [Fintype.card_fin] at h
  rw [nativeParentPacking_eq hD hK]
  exact h

/-- At most `2 ^ a` edges lie in a packet of a packing. -/
theorem card_packet_le {E R C : Type*} [Fintype E] {rowOf : E → R} {colOf : E → C} {r : ℕ}
    (Q : PacketPacking.Packing rowOf colOf a r) (q : Fin Q.numPackets) :
    #{e | Q.packet e = q} ≤ 2 ^ a := by
  calc #{e | Q.packet e = q} ≤ #(univ : Finset (Fin (2 ^ a))) :=
        card_le_card_of_injOn Q.slot (fun _ _ => mem_coe.mpr (mem_univ _)) fun e he e' he' h => by
          simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at he he'
          exact Q.injective (Prod.ext (he.trans he'.symm) h)
    _ = 2 ^ a := by rw [card_univ, Fintype.card_fin]

/-- Counting the elements of a sum type with a property. -/
private theorem card_filter_sum {A B : Type*} [Fintype A] [Fintype B] (p : A ⊕ B → Prop)
    [DecidablePred p] :
    #{x | p x} = #{a | p (.inl a)} + #{b | p (.inr b)} := by
  rw [← Fintype.card_subtype, Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum,
    Fintype.card_subtype, Fintype.card_subtype]

include hD in
/-- **The degree bound passes to the native child**: if the parent has maximum degree at most `Δ`
and `2 · 2 ^ a ≤ Δ`, every vertex of the child has at most `Δ` ports. A parent vertex keeps its
ports, and a packet vertex has one port per end in group `g` of an edge of its packet, of which
there are at most `2 ^ a`. -/
theorem length_le_of_mem_vertices_nativeChild (hK : 64 ^ a ≤ D.numEdges) (hia : i < a) {Δ : ℕ}
    (hdeg : ∀ v ∈ D.vertices, v.1.length ≤ Δ) (hL : 2 * 2 ^ a ≤ Δ) (fl : List ℕ) (pt : ℕ) (t : ℤ)
    (ζ β : List ℕ) (g : Fin 64) {v : List ℕ × VertexDesc}
    (hv : v ∈ (nativeChild fl a i pt t ζ r D (nativeParentPacking r a D) β g).vertices) :
    v.1.length ≤ Δ := by
  rw [nativeChild_nativeParentPacking_eq hD hK hia] at hv
  obtain ⟨c, rfl⟩ := List.mem_ofFn.mp hv
  simp only [List.length_map]
  rcases (childVertexEquiv (P := (parentPacking hD a).numPackets) (parentGroup hD a hia) g).symm c
    with u | q
  · simp only [numberedPorts, Sum.elim_inl]
    exact (List.length_filterMap_le _ _).trans (hdeg _ (List.getElem_mem _))
  · simp only [numberedPorts, Sum.elim_inr, packetPorts, List.length_map]
    set E := childEdgeEquiv (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia) g
    have hcount : ((List.finRange _).filter fun j =>
        decide (childTgt (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia)
          (parentPacking hD a).packet g (E.symm j) = .inr q)).length =
        #{c | childTgt (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia)
          (parentPacking hD a).packet g c = .inr q} := by
      rw [show ((List.finRange _).filter fun j =>
          decide (childTgt (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia)
            (parentPacking hD a).packet g (E.symm j) = .inr q)) =
          members (fun j => childTgt (D.srcFin hD) (D.tgtFin hD) (parentGroup hD a hia)
            (parentPacking hD a).packet g (E.symm j) = .inr q) from rfl, length_members,
        ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (E.symm.subtypeEquiv fun _ => Iff.rfl)
    rw [hcount, card_filter_sum]
    simp only [childTgt, Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq]
    have h1 : ∀ (P : Fin D.numEdges → Prop) [DecidablePred P],
        #{e : {e // P e} | (parentPacking hD a).packet e.1 = q} ≤ 2 ^ a := fun P _ =>
      (card_le_card_of_injOn Subtype.val (fun e he => by
          simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at he ⊢
          exact he)
        fun e _ e' _ h => Subtype.ext h).trans (card_packet_le _ q)
    have := h1 (fun e => parentGroup hD a hia (D.srcFin hD e) = g)
    have := h1 (fun e => parentGroup hD a hia (D.tgtFin hD e) = g)
    omega

end Cslib.Circuits.Frontier.NativeChild
