/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Mathlib.Logic.Equiv.Fin.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Foundations.Data.List.Lookup
import Mathlib.Data.List.GetD

/-!
# Numbering the vertices and edges of a child network

A child network of the contraction recursion (`TensorNetwork.ModeSplitting.child`, §D.4.6 of
[OpenAI2026ETH], p. 63) has as vertices the vertices of a group `g`, then one vertex per packet,
and as edges the row ports of group `g`, then the column ports of group `g`. A row port `e` joins
the row `src e` to the packet of `e`; a column port joins the column `tgt e` to it. A machine
numbers them (`childVertexEquiv`, `childEdgeEquiv`):

* the vertex `v` of group `g` by its position among the vertices of group `g` (`rank`), and the
  packet `q` by the number of vertices of group `g` plus `q`;
* the row ports of group `g` in edge order, then the column ports in edge order.

`childEdgeList` computes the ends of the numbered child edges from the list of groups of the
vertices and the edges with their packets, and `childEdgeList_eq` proves that it lists the
numbered ends of `childSrc` and `childTgt`. `childPorts` computes the ports of each numbered child
vertex, and `childPorts_eq` proves that they are the ports `TensorNetwork.explicitPorts` of the
written-out child. For a mode splitting `S` on `Fin` vertices, edges and packets, the ends of the
edges of `S.child β g` are by definition `childSrc` and `childTgt` for `S.group` and `S.packet`.
So a native child carries exactly the edge structure of the child network, and its contraction
transports along the numberings by reindexing.

The groups and packets come from the native packing (`Cslib.PacketPacking.nativePacking`); the
tensors of the child vertices are not treated here.

## Main definitions

* `Cslib.Circuits.Frontier.ChildNumbering.rank`, `Cslib.Circuits.Frontier.ChildNumbering.rankEquiv`:
  the position of an element among those with a property, as a numbering.
* `Cslib.Circuits.Frontier.ChildNumbering.childSrc`,
  `Cslib.Circuits.Frontier.ChildNumbering.childTgt`: the ends of the child edges.
* `Cslib.Circuits.Frontier.ChildNumbering.childVertexEquiv`,
  `Cslib.Circuits.Frontier.ChildNumbering.childEdgeEquiv`: the numberings.
* `Cslib.Circuits.Frontier.ChildNumbering.childEdgeList`,
  `Cslib.Circuits.Frontier.ChildNumbering.childPorts`: the native child edges and ports.

## Main results

* `Cslib.Circuits.Frontier.ChildNumbering.childEdgeList_eq`: the native child edges.
* `Cslib.Circuits.Frontier.ChildNumbering.childPorts_eq`: the native ports of the child vertices.
* `Cslib.Circuits.Frontier.ChildNumbering.computableInPolyTime_childEdgeList`,
  `Cslib.Circuits.Frontier.ChildNumbering.computableInPolyTime_childPorts`: both in polynomial
  time, with the vertex numbers in binary.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.4.6, p. 63.
-/

public section

namespace Cslib.Circuits.Frontier.ChildNumbering

/-! ### Positions -/

section Rank

variable {n : ℕ} (p : Fin n → Prop) [DecidablePred p]

/-- The elements with the property `p`, in increasing order. -/
@[expose] def members : List (Fin n) := (List.finRange n).filter fun v => p v

/-- The position of `v` among the elements with the property `p`: the number of earlier ones. -/
@[expose] def rank (v : Fin n) : ℕ := ((List.finRange n).take v).countP fun u => p u

/-- In a filtered list, an entry with the property sits at the number of earlier entries with
it. -/
private theorem getElem_filter_countP_take {α : Type*} (q : α → Bool) (l : List α) (i : ℕ)
    (hi : i < l.length) (hq : q l[i] = true) :
    ∃ h, (l.filter q)[(l.take i).countP q]'h = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    rcases i with _ | i
    · simp only [List.getElem_cons_zero] at hq
      simp [hq]
    · simp only [List.getElem_cons_succ] at hq ⊢
      obtain ⟨h, hget⟩ := ih i (by simpa using hi) hq
      by_cases hx : q x = true
      · simp only [List.take_succ_cons, List.countP_cons, hx, ↓reduceIte, List.filter_cons]
        exact ⟨by simpa using h, by simpa using hget⟩
      · simp only [List.take_succ_cons, List.countP_cons, hx, Bool.false_eq_true, ↓reduceIte,
          Nat.add_zero, List.filter_cons]
        exact ⟨h, hget⟩

private theorem rank_spec (v : Fin n) (hv : p v) :
    ∃ h : rank p v < (members p).length, (members p)[rank p v] = v := by
  obtain ⟨h, hget⟩ := getElem_filter_countP_take (fun u => decide (p u)) (List.finRange n) v
    (by simp) (by simpa using hv)
  exact ⟨h, by simpa [members, rank] using hget⟩

/-- The position of an element with the property is below the number of such elements. -/
theorem rank_lt (v : Fin n) (hv : p v) : rank p v < (members p).length :=
  (rank_spec p v hv).1

/-- The element at the position of `v` is `v`. -/
theorem getElem_rank (v : Fin n) (hv : p v) :
    (members p)[rank p v]'(rank_lt p v hv) = v :=
  (rank_spec p v hv).2

/-- The member at position `j` has position `j`. -/
theorem rank_getElem (j : ℕ) (hj : j < (members p).length) : rank p (members p)[j] = j := by
  have hmem : p (members p)[j] := of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hj)).2
  have h := getElem_rank p (members p)[j] hmem
  exact ((List.nodup_finRange n).filter _).getElem_inj_iff.mp h

/-- **The numbering of the elements with a property by their positions.** -/
@[expose] def rankEquiv : {v // p v} ≃ Fin (members p).length where
  toFun v := ⟨rank p v, rank_lt p v v.2⟩
  invFun j := ⟨(members p)[j], of_decide_eq_true (List.mem_filter.mp (List.getElem_mem j.2)).2⟩
  left_inv v := Subtype.ext (getElem_rank p v v.2)
  right_inv j := Fin.ext (rank_getElem p j j.2)

@[simp] theorem rankEquiv_apply_val (v : {v // p v}) : (rankEquiv p v : ℕ) = rank p v := rfl

@[simp] theorem rankEquiv_symm_apply_val (j : Fin (members p).length) :
    ((rankEquiv p).symm j : Fin n) = (members p)[j] := rfl

end Rank

/-! ### The child's numbering -/

section Child

variable {m n P r : ℕ} (src tgt : Fin m → Fin n) (group : Fin n → Fin r) (packet : Fin m → Fin P)
  (g : Fin r)

/-- The vertices of a child: the vertices of group `g`, then the packets. -/
abbrev ChildVertex (P : ℕ) : Type := {v : Fin n // group v = g} ⊕ Fin P

/-- The edges of a child: the row ports of group `g`, then its column ports. -/
abbrev ChildEdge : Type := {e : Fin m // group (src e) = g} ⊕ {e : Fin m // group (tgt e) = g}

/-- The child end of a child edge: the row of a row port, or the column of a column port. -/
@[expose] def childSrc : ChildEdge src tgt group g → ChildVertex group g P :=
  Sum.elim (fun e => .inl ⟨src e.1, e.2⟩) (fun e => .inl ⟨tgt e.1, e.2⟩)

/-- The packet end of a child edge. -/
@[expose] def childTgt : ChildEdge src tgt group g → ChildVertex group g P :=
  Sum.elim (fun e => .inr (packet e.1)) (fun e => .inr (packet e.1))

/-- **The numbering of the child vertices**: the vertices of group `g` by position, then the
packets. -/
@[expose] def childVertexEquiv :
    ChildVertex group g P ≃ Fin ((members fun v => group v = g).length + P) :=
  (Equiv.sumCongr (rankEquiv _) (Equiv.refl _)).trans finSumFinEquiv

/-- **The numbering of the child edges**: the row ports of group `g` in edge order, then its
column ports in edge order. -/
@[expose] def childEdgeEquiv : ChildEdge src tgt group g ≃
    Fin ((members fun e => group (src e) = g).length +
      (members fun e => group (tgt e) = g).length) :=
  (Equiv.sumCongr (rankEquiv _) (rankEquiv _)).trans finSumFinEquiv

end Child

/-! ### The native child -/

/-- **The ends of the numbered child edges**, from the groups of the vertices, the group `g`, the
`(row, column)` edges and their packets: the row ports of group `g`, then its column ports, each
from the position of its vertex among the vertices of group `g` to the number of such vertices
plus its packet. -/
@[expose] def childEdgeList (groups : List ℕ) (g : ℕ) (edges : List (ℕ × ℕ)) (packets : List ℕ) :
    List (ℕ × ℕ) :=
  ((edges.zip packets).filter fun q => groups.getD q.1.1 0 = g).map
      (fun q => ((groups.take q.1.1).count g, groups.count g + q.2)) ++
    ((edges.zip packets).filter fun q => groups.getD q.1.2 0 = g).map
      (fun q => ((groups.take q.1.2).count g, groups.count g + q.2))

/-- **The ports of the numbered child vertex `i`**: the numbered child edges at it, in increasing
order. -/
@[expose] def childPorts (edges : List (ℕ × ℕ)) (i : ℕ) : List ℕ :=
  (List.range edges.length).filter fun j =>
    (edges.getD j (0, 0)).1 = i ∨ (edges.getD j (0, 0)).2 = i

section Bridge

variable {m n P r : ℕ} (src tgt : Fin m → Fin n) (group : Fin n → Fin r) (packet : Fin m → Fin P)
  (g : Fin r)

/-- Counting a group among the groups of the earlier vertices gives the position. -/
private theorem count_take_ofFn (v : Fin n) :
    ((List.ofFn fun u => (group u : ℕ)).take v).count (g : ℕ) = rank (fun u => group u = g) v := by
  rw [List.ofFn_eq_map, ← List.map_take, List.count, List.countP_map, rank]
  refine List.countP_congr fun u _ => ?_
  simp [Fin.val_inj]

/-- Counting a group among the groups of all vertices gives the number of its vertices. -/
private theorem count_ofFn :
    (List.ofFn fun u => (group u : ℕ)).count (g : ℕ) = (members fun u => group u = g).length := by
  rw [List.ofFn_eq_map, List.count, List.countP_map, members, ← List.countP_eq_length_filter]
  refine List.countP_congr fun u _ => ?_
  simp [Fin.val_inj]

/-- A filter of the zipped edges and packets is a filter of the edge numbers. -/
private theorem filter_zip_ofFn (end_ : Fin m → Fin n) (sel : (ℕ × ℕ) × ℕ → ℕ)
    (hsel : ∀ e : Fin m, sel (((src e : ℕ), (tgt e : ℕ)), (packet e : ℕ)) = end_ e) :
    ((List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))).zip (List.ofFn fun e => (packet e : ℕ))).filter
        (fun q => (List.ofFn fun u => (group u : ℕ)).getD (sel q) 0 = (g : ℕ)) =
      (members fun e => group (end_ e) = g).map
        fun e => (((src e : ℕ), (tgt e : ℕ)), (packet e : ℕ)) := by
  have hzip : (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))).zip
      (List.ofFn fun e => (packet e : ℕ)) =
      (List.finRange m).map fun e => (((src e : ℕ), (tgt e : ℕ)), (packet e : ℕ)) := by
    apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp
  rw [hzip, List.filter_map, members]
  congr 1
  refine List.filter_congr fun e _ => ?_
  simp only [Function.comp_apply, hsel, List.getD_ofFn, Fin.val_inj]

private theorem finSumFinEquiv_symm_castLE {a b : ℕ} (h : a ≤ a + b) (i : Fin a) :
    finSumFinEquiv.symm (Fin.castLE h i) = Sum.inl i :=
  finSumFinEquiv_symm_apply_castAdd i

/-- **The native child edges are the numbered ends of the child edges.** -/
theorem childEdgeList_eq :
    childEdgeList (List.ofFn fun v => (group v : ℕ)) g
        (List.ofFn fun e => ((src e : ℕ), (tgt e : ℕ))) (List.ofFn fun e => (packet e : ℕ)) =
      List.ofFn fun j => (((childVertexEquiv (P := P) group g)
          (childSrc src tgt group g ((childEdgeEquiv src tgt group g).symm j)) : ℕ),
        ((childVertexEquiv group g)
          (childTgt src tgt group packet g ((childEdgeEquiv src tgt group g).symm j)) : ℕ)) := by
  rw [childEdgeList, count_ofFn,
    filter_zip_ofFn src tgt group packet g src (fun q => q.1.1) (fun _ => rfl),
    filter_zip_ofFn src tgt group packet g tgt (fun q => q.1.2) (fun _ => rfl), List.ofFn_add,
    List.map_map, List.map_map]
  congr 1
  · rw [← List.ofFn_getElem_eq_map]
    congr 1
    funext j
    simp only [childEdgeEquiv, childVertexEquiv, Equiv.symm_trans_apply,
      finSumFinEquiv_symm_castLE, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl,
      Sum.map_inr, childSrc, childTgt, Sum.elim_inl, Equiv.trans_apply, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd, rankEquiv_apply_val,
      rankEquiv_symm_apply_val, Equiv.refl_apply, Function.comp_apply, count_take_ofFn,
      Fin.getElem_fin]
  · rw [← List.ofFn_getElem_eq_map]
    congr 1
    funext j
    simp only [childEdgeEquiv, childVertexEquiv, Equiv.symm_trans_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr,
      childSrc, childTgt, Sum.elim_inr, Sum.map_inl, Equiv.trans_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
      rankEquiv_apply_val, rankEquiv_symm_apply_val, Equiv.refl_apply, Function.comp_apply,
      count_take_ofFn, Fin.getElem_fin]

end Bridge

section Ports

variable {R V E : Type*} [DecidableEq V] {k l : ℕ} (N : TensorNetwork R Bool V E) (ev : V ≃ Fin k)
  (ee : E ≃ Fin l)

/-- **The native ports are the ports of the written-out network**: for the list of the numbered
ends of the edges, the native ports of the vertex numbered `ev v` are the ports
`TensorNetwork.explicitPorts` of `v`. -/
theorem childPorts_eq (v : V) :
    childPorts (List.ofFn fun j => ((ev (N.src (ee.symm j)) : ℕ), (ev (N.tgt (ee.symm j)) : ℕ)))
        (ev v) = (N.explicitPorts ee v).map Fin.val := by
  rw [childPorts, TensorNetwork.explicitPorts, List.length_ofFn,
    ← List.map_coe_finRange_eq_range, List.filter_map]
  congr 1
  refine List.filter_congr fun j _ => ?_
  simp only [Function.comp_apply, List.getD_ofFn, Fin.val_inj, Equiv.apply_eq_iff_eq]

end Ports

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM

/-- The inputs `((groups, g), (edges, packets))` of `childEdgeList`, in binary. -/
abbrev ChildInput : Type := (List ℕ × ℕ) × (List (ℕ × ℕ) × List ℕ)

/-- The encoding of `ChildInput`. -/
@[expose] def encChildInput : ChildInput ↪ List Bool :=
  encPair (encPair (encList encNat) encNat) (encPair (encList (encPair encNat encNat))
    (encList encNat))

/-- Counting `g` among the first `v` groups, with `v` in binary. -/
private theorem computableInPolyTime_countTake {γ : Type} {encIn : γ ↪ List Bool}
    {groups : γ → List ℕ} {g v : γ → ℕ}
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat) (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => ((groups x).take (v x)).count (g x)) encIn encUnary := by
  have hcap := ComputableInPolyTime.binary_min_unary'
    ((ComputableInPolyTime.length_list _).comp hgroups) hv
  have htake : ComputableInPolyTime (fun x => (groups x).take (min (groups x).length (v x))) encIn
      (encList encNat) :=
    .of_tidy (ComputableTidilyInPolyTime.listTakeWithInput hgroups.tidy hcap.tidy)
  have htest : ComputableInPolyTime (fun p : γ × ℕ => decide (p.2 = g p.1))
      (encPair encIn encNat) encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
      (hg.comp (ComputableInPolyTime.fst _ _))
  have h := ComputableInPolyTime.countPWithInput (test := fun x a => decide (a = g x)) htake htest
  refine h.of_enc_eq fun x => ?_
  have htk : (groups x).take (min (groups x).length (v x)) = (groups x).take (v x) := by
    rcases le_total (groups x).length (v x) with hle | hle
    · rw [min_eq_left hle, List.take_length, List.take_of_length_le hle]
    · rw [min_eq_right hle]
  rw [htk, List.count]
  congr 2

/-- One half of the child edges: the ports at the end `sel` of group `g`. -/
private theorem computableInPolyTime_childHalf (sel : (ℕ × ℕ) → ℕ)
    (hsel : ComputableInPolyTime sel (encPair encNat encNat) encNat) :
    ComputableInPolyTime (fun x : ChildInput =>
      ((x.2.1.zip x.2.2).filter fun q => x.1.1.getD (sel q.1) 0 = x.1.2).map
        fun q => ((x.1.1.take (sel q.1)).count x.1.2, x.1.1.count x.1.2 + q.2))
      encChildInput (encList (encPair encNat encNat)) := by
  let encQ := encPair encChildInput (encPair (encPair encNat encNat) encNat)
  have hgroups : ComputableInPolyTime (fun x : ChildInput => x.1.1) encChildInput
      (encList encNat) := by unfold encChildInput; fun_prop
  have hg : ComputableInPolyTime (fun x : ChildInput => x.1.2) encChildInput encNat := by
    unfold encChildInput; fun_prop
  have hzip : ComputableInPolyTime (fun x : ChildInput => x.2.1.zip x.2.2) encChildInput
      (encList (encPair (encPair encNat encNat) encNat)) :=
    (ComputableInPolyTime.zip _ _).comp (by unfold encChildInput; fun_prop)
  have hgroupsQ : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) => p.1.1.1) encQ
      (encList encNat) := hgroups.comp (ComputableInPolyTime.fst _ _)
  have hgQ : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) => p.1.1.2) encQ encNat :=
    hg.comp (ComputableInPolyTime.fst _ _)
  have hselQ : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) => sel p.2.1) encQ
      encNat := hsel.comp (by unfold encQ; fun_prop)
  have hpQ : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) => p.2.2) encQ encNat := by
    unfold encQ; fun_prop
  have htest : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) =>
      decide (p.1.1.1.getD (sel p.2.1) 0 = p.1.1.2)) encQ encBool :=
    ComputableInPolyTime.decide_eq' (ComputableInPolyTime.listGetD_binary 0 hgroupsQ hselQ) hgQ
  have hfilter := ComputableInPolyTime.filterWithInput
    (test := fun x q => decide (x.1.1.getD (sel q.1) 0 = x.1.2)) hzip htest
  have hrank := ComputableInPolyTime.unary_to_binary.comp
    (computableInPolyTime_countTake hgroupsQ hgQ hselQ)
  have hcount := ComputableInPolyTime.unary_to_binary.comp
    (computableInPolyTime_countTake hgroupsQ hgQ
      (ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
        hgroupsQ)))
  have hpair : ComputableInPolyTime (fun p : ChildInput × ((ℕ × ℕ) × ℕ) =>
      ((p.1.1.1.take (sel p.2.1)).count p.1.1.2,
        (p.1.1.1.take p.1.1.1.length).count p.1.1.2 + p.2.2)) encQ (encPair encNat encNat) :=
    hrank.prod (ComputableInPolyTime.binary_add.comp (hcount.prod hpQ))
  have h := ComputableInPolyTime.mapWithInput
    (f := fun x q => ((x.1.1.take (sel q.1)).count x.1.2,
      (x.1.1.take x.1.1.length).count x.1.2 + q.2)) hfilter hpair
  refine h.of_enc_eq fun x => ?_
  simp only [List.take_length]

/-- **The native child edges are polynomial-time.** -/
theorem computableInPolyTime_childEdgeList :
    ComputableInPolyTime (fun x : ChildInput => childEdgeList x.1.1 x.1.2 x.2.1 x.2.2)
      encChildInput (encList (encPair encNat encNat)) := by
  have h := ComputableInPolyTime.listAppend'
    (computableInPolyTime_childHalf Prod.fst (by fun_prop))
    (computableInPolyTime_childHalf Prod.snd (by fun_prop))
  exact h

/-- **The native ports are polynomial-time.** -/
theorem computableInPolyTime_childPorts :
    ComputableInPolyTime (fun x : List (ℕ × ℕ) × ℕ => childPorts x.1 x.2)
      (encPair (encList (encPair encNat encNat)) encNat) (encList encUnary) := by
  let enc := encPair (encList (encPair encNat encNat)) encNat
  have hl : ComputableInPolyTime (fun x : List (ℕ × ℕ) × ℕ => x.1) enc
      (encList (encPair encNat encNat)) := ComputableInPolyTime.fst _ _
  have hrange : ComputableInPolyTime (fun x : List (ℕ × ℕ) × ℕ => List.range x.1.length) enc
      (encList encUnary) := ComputableInPolyTime.range.comp
        ((ComputableInPolyTime.length_list _).comp hl)
  let encJ := encPair enc encUnary
  have hentry : ComputableInPolyTime (fun p : (List (ℕ × ℕ) × ℕ) × ℕ => p.1.1.getD p.2 (0, 0))
      encJ (encPair encNat encNat) :=
    (ComputableInPolyTime.listGetD (0, 0)).comp ((hl.comp (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd _ _))
  have hi : ComputableInPolyTime (fun p : (List (ℕ × ℕ) × ℕ) × ℕ => p.1.2) encJ encNat :=
    (ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _)
  have htest := ComputableInPolyTime.decide_or
    (ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.fst _ _).comp hentry) hi)
    (ComputableInPolyTime.decide_eq' ((ComputableInPolyTime.snd _ _).comp hentry) hi)
  have h := ComputableInPolyTime.filterWithInput
    (test := fun x j => decide ((x.1.getD j (0, 0)).1 = x.2 ∨ (x.1.getD j (0, 0)).2 = x.2))
    hrange htest
  exact h

end PolyTime

end Cslib.Circuits.Frontier.ChildNumbering
