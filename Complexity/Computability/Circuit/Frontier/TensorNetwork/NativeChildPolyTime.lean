/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.NativeChild
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Mathlib.Data.List.GetD

/-!
# The native child networks in polynomial time

The native child of group `g` of an active call of the contraction recursion of [OpenAI2026ETH]
(§D.4.6, p. 63), `NativeChild.nativeChild`, and its number of rows, `NativeChild.childRows`, are
computable in polynomial time over the encodings of the native recursion. The counts are unary,
the node `t` is in binary sign-magnitude form, and the lists are binary, except the exponents
`β`, which are unary as in a packet descriptor. The parent is encoded by
`DescribedNetwork.encDescribed (VertexDesc.enc encT)`, for any encoding `encT` of the root
descriptors, and its packing by
`PacketPacking.encNativePacking`.

The theorems are stated in composition form, for components computed from any input. Besides the
components themselves, they ask for `2 ^ a`, `2 ^ (i + 1)` and the number of packets in unary.
Every packet vertex stores `2 ^ a` and `2 ^ (i + 1)` in unary in its context, and the child has
one packet vertex per packet. For the native parent packing
(`NativeChild.nativeParentPacking`), the packing itself and its number of packets, at most
`M (2 ^ a) ^ 12` for `M` edges, are computed here, with the number of rows in unary.

**The pieces.**
* The groups of the vertices are looked up in the label words, one vertex at a time.
* The child edges are `ChildNumbering.childEdgeList`, and the ports of a packet are
  `ChildNumbering.childPorts`.
* A retained vertex renumbers its ports by counting the earlier edges with an end in its group.
  `NativeChild.portRank_eq_countP` puts that count in a form without a unary loop over the port.
* A packet vertex tags each port with the slot of the parent edge, read off the ports of the
  group.

**The shape of the child**, for size bounds along the recursion:
* the child has at most twice as many edges as the parent;
* it has `childRows + P` vertices;
* each vertex is either a parent vertex, with its descriptor and its number of ports, or the
  vertex of a packet `q`, with its context, its tags and its slice of `β`.

## Main results

* `Cslib.Circuits.Frontier.NativeChild.computableInPolyTime_nativeChild`,
  `Cslib.Circuits.Frontier.NativeChild.computableInPolyTime_childRows`: the native child and its
  number of rows are polynomial-time.
* `Cslib.Circuits.Frontier.NativeChild.computableInPolyTime_nativeChild_nativeParentPacking`,
  `Cslib.Circuits.Frontier.NativeChild.computableInPolyTime_childRows_nativeParentPacking`: the
  same for the native parent packing.
* `Cslib.Circuits.Frontier.NativeChild.numPackets_nativeParentPacking_le`: the number of packets.
* `Cslib.Circuits.Frontier.NativeChild.numEdges_nativeChild_le`,
  `Cslib.Circuits.Frontier.NativeChild.length_vertices_nativeChild`,
  `Cslib.Circuits.Frontier.NativeChild.mem_vertices_nativeChild`: the shape of the child.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.6, p. 63.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open Turing.MultiTapeTM ChildNumbering NativePacket

variable {T : Type} {encT : T ↪ List Bool}

/-- **The rank of a port without a loop over the port**: the edges before `e` with an end in group
`g`, the edges past the list counting as `(0, 0)`. -/
theorem portRank_eq_countP (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ)) (sel : ℕ × ℕ → ℕ)
    (e : ℕ) :
    portRank groups g ends sel e =
      (List.range (min ends.length e)).countP
          (fun e' => decide (groups.getD (sel (ends.getD e' (0, 0))) 0 = g)) +
        (e - ends.length) * (if groups.getD (sel (0, 0)) 0 = g then 1 else 0) := by
  induction e with
  | zero => simp [portRank]
  | succ e ih =>
    have hstep : portRank groups g ends sel (e + 1) = portRank groups g ends sel e +
        if groups.getD (sel (ends.getD e (0, 0))) 0 = g then 1 else 0 := by
      simp only [portRank, List.range_succ, List.countP_append, List.countP_singleton,
        decide_eq_true_eq]
    rw [hstep, ih]
    rcases lt_or_ge e ends.length with h | h
    · rw [min_eq_right h.le, min_eq_right (show e + 1 ≤ ends.length by omega), List.range_succ,
        List.countP_append, List.countP_singleton, Nat.sub_eq_zero_of_le h.le,
        Nat.sub_eq_zero_of_le (show e + 1 ≤ ends.length by omega)]
      simp only [zero_mul, add_zero, decide_eq_true_eq]
    · rw [min_eq_left h, min_eq_left (show ends.length ≤ e + 1 by omega),
        List.getD_eq_default _ _ h, show e + 1 - ends.length = e - ends.length + 1 by omega]
      split_ifs <;> ring

section PolyTime

variable {δ : Type} {encIn : δ ↪ List Bool} {groups : δ → List ℕ} {g : δ → ℕ}
  {ends : δ → List (ℕ × ℕ)}

/-- Whether the end `sel` of the edge `e`, in unary, is in group `g`. -/
private theorem test_polyTime (sel : ℕ × ℕ → ℕ)
    (hsel : ComputableInPolyTime sel (encPair encNat encNat) encNat)
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun p : δ × ℕ =>
      decide ((groups p.1).getD (sel ((ends p.1).getD p.2 (0, 0))) 0 = g p.1))
      (encPair encIn encUnary) encBool := by
  have hentry : ComputableInPolyTime (fun p : δ × ℕ => (ends p.1).getD p.2 (0, 0))
      (encPair encIn encUnary) (encPair encNat encNat) :=
    (ComputableInPolyTime.listGetD (0, 0)).comp
      ((hends.comp (ComputableInPolyTime.fst _ _)).prod (ComputableInPolyTime.snd _ _))
  exact ComputableInPolyTime.decide_eq'
    (ComputableInPolyTime.listGetD_binary 0 (hgroups.comp (ComputableInPolyTime.fst _ _))
      (hsel.comp hentry))
    (hg.comp (ComputableInPolyTime.fst _ _))

/-- **The ports of a group are polynomial-time.** -/
theorem computableInPolyTime_portEdges (sel : ℕ × ℕ → ℕ)
    (hsel : ComputableInPolyTime sel (encPair encNat encNat) encNat)
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun x => portEdges (groups x) (g x) (ends x) sel) encIn
      (encList encUnary) :=
  ComputableInPolyTime.filterWithInput
    (test := fun x e => decide ((groups x).getD (sel ((ends x).getD e (0, 0))) 0 = g x))
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list _).comp hends))
    (test_polyTime sel hsel hgroups hg hends)

/-- **The rank of a port is polynomial-time**, with the port in binary. -/
theorem computableInPolyTime_portRank (sel : ℕ × ℕ → ℕ)
    (hsel : ComputableInPolyTime sel (encPair encNat encNat) encNat)
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat)))
    {e : δ → ℕ} (he : ComputableInPolyTime e encIn encNat) :
    ComputableInPolyTime (fun x => portRank (groups x) (g x) (ends x) sel (e x)) encIn encNat := by
  have hlen : ComputableInPolyTime (fun x => (ends x).length) encIn encUnary :=
    (ComputableInPolyTime.length_list _).comp hends
  have hcount := ComputableInPolyTime.countPWithInput
    (test := fun x e' => decide ((groups x).getD (sel ((ends x).getD e' (0, 0))) 0 = g x))
    (ComputableInPolyTime.range.comp (ComputableInPolyTime.binary_min_unary' hlen he))
    (test_polyTime sel hsel hgroups hg hends)
  have hdefault : ComputableInPolyTime (fun x => decide ((groups x).getD (sel (0, 0)) 0 = g x))
      encIn encBool :=
    ComputableInPolyTime.decide_eq'
      (ComputableInPolyTime.listGetD_binary 0 hgroups (ComputableInPolyTime.const (sel (0, 0))))
      hg
  have hextra : ComputableInPolyTime (fun x =>
      (e x - (ends x).length) * (if decide ((groups x).getD (sel (0, 0)) 0 = g x) then 1 else 0))
      encIn encNat :=
    ComputableInPolyTime.binary_mul'
      (ComputableInPolyTime.binary_sub' he (ComputableInPolyTime.unary_to_binary.comp hlen))
      (ComputableInPolyTime.ite hdefault (ComputableInPolyTime.const 1)
        (ComputableInPolyTime.const 0))
  refine (ComputableInPolyTime.binary_add.comp
    ((ComputableInPolyTime.unary_to_binary.comp hcount).prod hextra)).of_enc_eq fun x => ?_
  rw [portRank_eq_countP]
  simp only [decide_eq_true_eq, Function.comp_apply]

/-- **The child edge of a port is polynomial-time**, with the vertex and the port in binary. -/
theorem computableInPolyTime_childEdgeOf {r v e : δ → ℕ}
    (hr : ComputableInPolyTime r encIn encNat)
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat)))
    (hv : ComputableInPolyTime v encIn encNat) (he : ComputableInPolyTime e encIn encNat) :
    ComputableInPolyTime (fun x => childEdgeOf (r x) (groups x) (g x) (ends x) (v x) (e x))
      encIn encNat := by
  have hR : ComputableInPolyTime (fun x => (portEdges (groups x) (g x) (ends x) Prod.fst).length)
      encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp
      (computableInPolyTime_portEdges Prod.fst (ComputableInPolyTime.fst _ _) hgroups hg hends))
  refine (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hv hr)
    (computableInPolyTime_portRank Prod.fst (ComputableInPolyTime.fst _ _) hgroups hg hends he)
    (ComputableInPolyTime.binary_add.comp (hR.prod (computableInPolyTime_portRank Prod.snd
      (ComputableInPolyTime.snd _ _) hgroups hg hends he)))).of_enc_eq fun x => ?_
  simp only [childEdgeOf, decide_eq_true_eq, Function.comp_apply]

/-- **The parent edge of a child edge is polynomial-time**, with the child edge in binary and the
parent edge in unary. -/
theorem computableInPolyTime_parentEdge {j : δ → ℕ}
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat)))
    (hj : ComputableInPolyTime j encIn encNat) :
    ComputableInPolyTime (fun x => parentEdge (groups x) (g x) (ends x) (j x)) encIn
      encUnary := by
  have hfst := computableInPolyTime_portEdges Prod.fst (ComputableInPolyTime.fst _ _) hgroups hg
    hends
  have hsnd := computableInPolyTime_portEdges Prod.snd (ComputableInPolyTime.snd _ _) hgroups hg
    hends
  have hR : ComputableInPolyTime (fun x => (portEdges (groups x) (g x) (ends x) Prod.fst).length)
      encIn encNat :=
    ComputableInPolyTime.unary_to_binary.comp ((ComputableInPolyTime.length_list _).comp hfst)
  refine (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hj hR)
    (ComputableInPolyTime.listGetD_binary (encA := encUnary) 0 hfst hj)
    (ComputableInPolyTime.listGetD_binary (encA := encUnary) 0 hsnd
      (ComputableInPolyTime.binary_sub' hj hR))).of_enc_eq fun x => ?_
  simp only [parentEdge, decide_eq_true_eq]

/-- **The groups of the vertices are polynomial-time.** -/
theorem computableInPolyTime_groupsOf {r i k : δ → ℕ}
    {words : δ → List (List ℕ) × List (List ℕ)}
    (hr : ComputableInPolyTime r encIn encNat) (hi : ComputableInPolyTime i encIn encUnary)
    (hk : ComputableInPolyTime k encIn encUnary)
    (hwords : ComputableInPolyTime words encIn
      (encPair (encList (encList encNat)) (encList (encList encNat)))) :
    ComputableInPolyTime (fun x => groupsOf (r x) (i x) (k x) (words x)) encIn
      (encList encNat) := by
  let e := encPair encIn encUnary
  have hx : ComputableInPolyTime (fun p : δ × ℕ => p.1) e encIn := ComputableInPolyTime.fst _ _
  have hv : ComputableInPolyTime (fun p : δ × ℕ => p.2) e encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
  have hw₁ := (ComputableInPolyTime.fst _ _).comp (hwords.comp hx)
  have hw₂ := (ComputableInPolyTime.snd _ _).comp (hwords.comp hx)
  have hrow : ComputableInPolyTime (fun p : δ × ℕ =>
      (((words p.1).1.getD p.2 []).getD (i p.1) 0)) e encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      (((ComputableInPolyTime.listGetD (encA := encList encNat) (encL := encList (encList encNat))
        []).comp (hw₁.prod (ComputableInPolyTime.snd _ _))).prod (hi.comp hx))
  have hcol : ComputableInPolyTime (fun p : δ × ℕ =>
      (((words p.1).2.getD (p.2 - r p.1) []).getD (i p.1) 0)) e encNat :=
    (ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
      ((ComputableInPolyTime.listGetD_binary (encA := encList encNat) [] hw₂
        (ComputableInPolyTime.binary_sub' hv (hr.comp hx))).prod (hi.comp hx))
  have h := ComputableInPolyTime.mapWithInput
    (f := fun x v => if decide (v < r x) then ((words x).1.getD v []).getD (i x) 0
      else ((words x).2.getD (v - r x) []).getD (i x) 0)
    (ComputableInPolyTime.range.comp hk)
    (ComputableInPolyTime.ite (ComputableInPolyTime.binary_lt' hv (hr.comp hx)) hrow hcol)
  refine h.of_enc_eq fun x => ?_
  simp only [groupsOf, decide_eq_true_eq, Function.comp_apply]

/-- Taking a unary number of elements of a list. -/
private theorem listTake {α : Type} {encA : α ↪ List Bool} {l : δ → List α} {n : δ → ℕ}
    (hl : ComputableInPolyTime l encIn (encList encA))
    (hn : ComputableInPolyTime n encIn encUnary) :
    ComputableInPolyTime (fun x => (l x).take (n x)) encIn (encList encA) := by
  have hrev := ComputableInPolyTime.listReverseWithInput hl
  have hdrop := (ComputableInPolyTime.dropUnary (encA := encA) (encL := encList encA)).comp
    (hrev.prod (ComputableInPolyTime.unary_sub'
      ((ComputableInPolyTime.length_list _).comp hl) hn))
  refine (ComputableInPolyTime.listReverseWithInput hdrop).of_enc_eq fun x => ?_
  change encList encA ((l x).take (n x)) =
    encList encA (((l x).reverse.drop ((l x).length - n x)).reverse)
  rw [List.drop_reverse, List.reverse_reverse]
  rcases le_total (l x).length (n x) with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.sub_zero, List.take_length, List.take_of_length_le h]
  · rw [Nat.sub_sub_self h]

/-- Counting a group among the groups, in binary. -/
private theorem count_polyTime (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x => (groups x).count (g x)) encIn encNat := by
  have h := ComputableInPolyTime.countPWithInput (test := fun x v => decide (v = g x)) hgroups
    (ComputableInPolyTime.decide_eq' (ComputableInPolyTime.snd _ _)
      (hg.comp (ComputableInPolyTime.fst _ _)))
  refine (ComputableInPolyTime.unary_to_binary.comp h).of_enc_eq fun x => ?_
  rw [List.count]
  congr 2

/-- **The retained vertices**: the vertices of group `g` with their renumbered ports. -/
private theorem retained_polyTime {r : δ → ℕ} {V : δ → List (List ℕ × VertexDesc T)}
    (hr : ComputableInPolyTime r encIn encNat)
    (hV : ComputableInPolyTime V encIn (encList (encPair (encList encNat) (VertexDesc.enc encT))))
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat)
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun x =>
      ((List.range (V x).length).filter fun v => decide ((groups x).getD v 0 = g x)).map fun v =>
        (((V x).getD v defaultVertex).1.map (childEdgeOf (r x) (groups x) (g x) (ends x) v),
          ((V x).getD v defaultVertex).2))
      encIn (encList (encPair (encList encNat) (VertexDesc.enc encT))) := by
  let e₁ := encPair encIn encUnary
  have hx : ComputableInPolyTime (fun p : δ × ℕ => p.1) e₁ encIn := ComputableInPolyTime.fst _ _
  have hy : ComputableInPolyTime (fun p : δ × ℕ => p.2) e₁ encUnary :=
    ComputableInPolyTime.snd _ _
  have hfilter : ComputableInPolyTime (fun x => (List.range (V x).length).filter
      fun v => decide ((groups x).getD v 0 = g x)) encIn (encList encUnary) :=
    ComputableInPolyTime.filterWithInput (test := fun x v => decide ((groups x).getD v 0 = g x))
      (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list _).comp hV))
      (ComputableInPolyTime.decide_eq'
        ((ComputableInPolyTime.listGetD (encA := encNat) (encL := encList encNat) 0).comp
          ((hgroups.comp hx).prod hy)) (hg.comp hx))
  have hvtx : ComputableInPolyTime (fun p : δ × ℕ => (V p.1).getD p.2 defaultVertex) e₁
      (encPair (encList encNat) (VertexDesc.enc encT)) :=
    (ComputableInPolyTime.listGetD (encA := encPair (encList encNat) (VertexDesc.enc encT))
      (encL := encList (encPair (encList encNat) (VertexDesc.enc encT))) defaultVertex).comp
      ((hV.comp hx).prod hy)
  have hxx : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => q.1.1) (encPair e₁ encNat) encIn :=
    hx.comp (ComputableInPolyTime.fst _ _)
  have hr' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => r q.1.1) (encPair e₁ encNat) encNat :=
    hr.comp hxx
  have hgroups' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => groups q.1.1) (encPair e₁ encNat)
      (encList encNat) := hgroups.comp hxx
  have hg' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => g q.1.1) (encPair e₁ encNat) encNat :=
    hg.comp hxx
  have hends' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => ends q.1.1) (encPair e₁ encNat)
      (encList (encPair encNat encNat)) := hends.comp hxx
  have hv' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => q.1.2) (encPair e₁ encNat) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (hy.comp (ComputableInPolyTime.fst _ _))
  have he' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => q.2) (encPair e₁ encNat) encNat :=
    ComputableInPolyTime.snd _ _
  have hce : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ =>
      childEdgeOf (r q.1.1) (groups q.1.1) (g q.1.1) (ends q.1.1) q.1.2 q.2)
      (encPair e₁ encNat) encNat :=
    computableInPolyTime_childEdgeOf hr' hgroups' hg' hends' hv' he'
  have hports : ComputableInPolyTime (fun p : δ × ℕ =>
      ((V p.1).getD p.2 defaultVertex).1.map (childEdgeOf (r p.1) (groups p.1) (g p.1)
        (ends p.1) p.2)) e₁ (encList encNat) :=
    ComputableInPolyTime.mapWithInput
      (f := fun p e => childEdgeOf (r p.1) (groups p.1) (g p.1) (ends p.1) p.2 e)
      ((ComputableInPolyTime.fst _ _).comp hvtx) hce
  exact ComputableInPolyTime.mapWithInput
    (f := fun x v => (((V x).getD v defaultVertex).1.map
        (childEdgeOf (r x) (groups x) (g x) (ends x) v), ((V x).getD v defaultVertex).2))
    hfilter (hports.prod ((ComputableInPolyTime.snd _ _).comp hvtx))

variable {fl ζ β : δ → List ℕ} {a i pt r : δ → ℕ} {t : δ → ℤ}
  {D : δ → DescribedNetwork (VertexDesc T)}
  {pk : δ → (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)}

/-- **The context of a packet** is polynomial-time, with the packet in unary. -/
private theorem packetCtx_polyTime (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hT : ComputableInPolyTime (fun x => 2 ^ (i x + 1)) encIn encUnary)
    (hpt : ComputableInPolyTime pt encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat))
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun p : δ × ℕ =>
      packetCtx (fl p.1) (a p.1) (i p.1) (pt p.1) (t p.1) (ζ p.1) (g p.1) p.2)
      (encPair encIn encUnary) PacketCtx.enc := by
  let e₁ := encPair encIn encUnary
  have hx : ComputableInPolyTime (fun p : δ × ℕ => p.1) e₁ encIn := ComputableInPolyTime.fst _ _
  have hsym : ComputableInPolyTime (fun p : δ × ℕ =>
      PacketPacking.packetSymbols (a p.1) 64 p.2 (i p.1)) e₁ (encPair encNat encNat) :=
    PacketPacking.computableInPolyTime_packetSymbols (ha.comp hx) (ComputableInPolyTime.const 64)
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)) (hi.comp hx)
  have hs₁ := (ComputableInPolyTime.fst _ _).comp hsym
  have hs₂ := (ComputableInPolyTime.snd _ _).comp hsym
  have htuple : ComputableInPolyTime (fun p : δ × ℕ =>
      PacketCtx.equivProd (packetCtx (fl p.1) (a p.1) (i p.1) (pt p.1) (t p.1) (ζ p.1) (g p.1) p.2))
      e₁ PacketCtx.encProd :=
    ((hpt.comp hx).prod (hfl.comp hx)).prod (((ha.comp hx).prod (hL.comp hx)).prod
      (((hi.comp hx).prod (hT.comp hx)).prod ((ht.comp hx).prod ((hpt.comp hx).prod
        (((ComputableInPolyTime.decide_eq' hs₁ (hg.comp hx)).prod
          ((ComputableInPolyTime.decide_eq' hs₂ (hg.comp hx)).prod
            (ComputableInPolyTime.decide_not (ComputableInPolyTime.decide_eq' hs₁ hs₂)))).prod
          ((ComputableInPolyTime.const []).prod (hζ.comp hx)))))))
  have hsymm : ComputableInPolyTime PacketCtx.equivProd.symm PacketCtx.encProd PacketCtx.enc :=
    ComputableInPolyTime.of_eq fun y => by
      rw [PacketCtx.enc, encOfEquiv_apply, Equiv.apply_symm_apply]
  exact (hsymm.comp htuple).of_enc_eq fun p => by
    rw [Function.comp_apply, Equiv.symm_apply_apply]

/-- **The packet vertices**: one per packet, with its ports, their tags, its context and its slice
of the exponents. -/
private theorem packetVertices_polyTime {P : δ → ℕ} {cedges : δ → List (ℕ × ℕ)}
    {place : δ → List (ℕ × ℕ)}
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hT : ComputableInPolyTime (fun x => 2 ^ (i x + 1)) encIn encUnary)
    (hpt : ComputableInPolyTime pt encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat))
    (hβ : ComputableInPolyTime β encIn (encList encUnary))
    (hg : ComputableInPolyTime g encIn encNat)
    (hgroups : ComputableInPolyTime groups encIn (encList encNat))
    (hends : ComputableInPolyTime ends encIn (encList (encPair encNat encNat)))
    (hP : ComputableInPolyTime P encIn encUnary)
    (hcedges : ComputableInPolyTime cedges encIn (encList (encPair encNat encNat)))
    (hplace : ComputableInPolyTime place encIn (encList (encPair encNat encNat))) :
    ComputableInPolyTime (fun x => (List.range (P x)).map fun q =>
      (childPorts (cedges x) ((groups x).count (g x) + q),
        (Sum.inr (packetCtx (fl x) (a x) (i x) (pt x) (t x) (ζ x) (g x) q,
          (childPorts (cedges x) ((groups x).count (g x) + q)).map fun j =>
            (decide (j < (portEdges (groups x) (g x) (ends x) Prod.fst).length),
              ((place x).getD (parentEdge (groups x) (g x) (ends x) j) (0, 0)).2),
          betaSlice (i x) (pt x) (β x) q) : VertexDesc T)))
      encIn (encList (encPair (encList encNat) (VertexDesc.enc encT))) := by
  let e₁ := encPair encIn encUnary
  have hx : ComputableInPolyTime (fun p : δ × ℕ => p.1) e₁ encIn := ComputableInPolyTime.fst _ _
  have hy : ComputableInPolyTime (fun p : δ × ℕ => p.2) e₁ encUnary :=
    ComputableInPolyTime.snd _ _
  -- The ports.
  have hpq : ComputableInPolyTime (fun p : δ × ℕ =>
      childPorts (cedges p.1) ((groups p.1).count (g p.1) + p.2)) e₁ (encList encUnary) :=
    computableInPolyTime_childPorts.comp ((hcedges.comp hx).prod
      (ComputableInPolyTime.binary_add.comp (((count_polyTime hgroups hg).comp hx).prod
        (ComputableInPolyTime.unary_to_binary.comp hy))))
  have hpqb : ComputableInPolyTime (fun p : δ × ℕ =>
      childPorts (cedges p.1) ((groups p.1).count (g p.1) + p.2)) e₁ (encList encNat) :=
    (ComputableInPolyTime.mapWithInput (f := fun _ j => j) hpq
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))).of_enc_eq
      fun p => by rw [List.map_id']
  -- The tags of the ports.
  have hR : ComputableInPolyTime (fun x => (portEdges (groups x) (g x) (ends x) Prod.fst).length)
      encIn encUnary :=
    (ComputableInPolyTime.length_list _).comp (computableInPolyTime_portEdges Prod.fst
      (ComputableInPolyTime.fst _ _) hgroups hg hends)
  have hxu : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => q.1.1) (encPair e₁ encUnary) encIn :=
    hx.comp (ComputableInPolyTime.fst _ _)
  have hgroups' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => groups q.1.1) (encPair e₁ encUnary)
      (encList encNat) := hgroups.comp hxu
  have hg' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => g q.1.1) (encPair e₁ encUnary) encNat :=
    hg.comp hxu
  have hends' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => ends q.1.1) (encPair e₁ encUnary)
      (encList (encPair encNat encNat)) := hends.comp hxu
  have hj' : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ => q.2) (encPair e₁ encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)
  have hpe : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ =>
      parentEdge (groups q.1.1) (g q.1.1) (ends q.1.1) q.2) (encPair e₁ encUnary) encUnary :=
    computableInPolyTime_parentEdge hgroups' hg' hends' hj'
  have htag : ComputableInPolyTime (fun q : (δ × ℕ) × ℕ =>
      (decide (q.2 < (portEdges (groups q.1.1) (g q.1.1) (ends q.1.1) Prod.fst).length),
        ((place q.1.1).getD (parentEdge (groups q.1.1) (g q.1.1) (ends q.1.1) q.2) (0, 0)).2))
      (encPair e₁ encUnary) (encPair encBool encNat) :=
    (ComputableInPolyTime.unary_lt' (ComputableInPolyTime.snd _ _) (hR.comp hxu)).prod
      ((ComputableInPolyTime.snd _ _).comp
        ((ComputableInPolyTime.listGetD (encA := encPair encNat encNat)
          (encL := encList (encPair encNat encNat)) (0, 0)).comp ((hplace.comp hxu).prod hpe)))
  have htags := ComputableInPolyTime.mapWithInput
    (f := fun p j => (decide (j < (portEdges (groups p.1) (g p.1) (ends p.1) Prod.fst).length),
        ((place p.1).getD (parentEdge (groups p.1) (g p.1) (ends p.1) j) (0, 0)).2)) hpq htag
  -- The exponents.
  have hTp := ComputableInPolyTime.unary_mul' hT hpt
  have hdrop : ComputableInPolyTime (fun p : δ × ℕ =>
      (β p.1).drop (p.2 * (2 ^ (i p.1 + 1) * pt p.1))) e₁ (encList encUnary) :=
    (ComputableInPolyTime.dropUnary (encA := encUnary) (encL := encList encUnary)).comp
      ((hβ.comp hx).prod (ComputableInPolyTime.unary_mul' hy (hTp.comp hx)))
  have hslice : ComputableInPolyTime (fun p : δ × ℕ => betaSlice (i p.1) (pt p.1) (β p.1) p.2)
      e₁ (encList encUnary) := listTake hdrop (hTp.comp hx)
  have hpacket := hpqb.prod ((ComputableInPolyTime.sumInr (encList encNat) encPacketDesc).comp
    ((packetCtx_polyTime hfl ha hL hi hT hpt ht hζ hg).prod (htags.prod hslice)))
  exact ComputableInPolyTime.mapWithInput (ComputableInPolyTime.range.comp hP) hpacket

/-- The parts of a native packing. -/
private theorem packing_parts (hpk : ComputableInPolyTime pk encIn PacketPacking.encNativePacking) :
    ComputableInPolyTime (fun x => (pk x).1) encIn
        (encPair (encList (encList encNat)) (encList (encList encNat))) ∧
      ComputableInPolyTime (fun x => (pk x).2.2) encIn (encList (encPair encNat encNat)) := by
  have hpk' : ComputableInPolyTime pk encIn
      (encPair (encPair (encList (encList encNat)) (encList (encList encNat)))
        (encPair encNat (encList (encPair encNat encNat)))) := hpk
  exact ⟨(ComputableInPolyTime.fst _ _).comp hpk',
    (ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hpk')⟩

/-- **The number of rows of the native child is polynomial-time.** -/
theorem computableInPolyTime_childRows (hr : ComputableInPolyTime r encIn encNat)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)))
    (hpk : ComputableInPolyTime pk encIn PacketPacking.encNativePacking)
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x => childRows (r x) (i x) (D x) (pk x) (g x)) encIn encNat :=
  count_polyTime (computableInPolyTime_groupsOf hr hi ((ComputableInPolyTime.length_list _).comp
    (DescribedNetwork.vertices_polyTime.comp hD)) (packing_parts hpk).1) hg

/-- **The native child is polynomial-time.** The counts `a`, `i` and `p_t` are unary, the node
`t` is in binary sign-magnitude form, the lists `fl` and `ζ`, the number of rows `r` and the group
`g` are in binary, and the exponents `β` are unary. The child stores `2 ^ a` and `2 ^ (i + 1)` in
unary in every packet vertex and has one packet vertex per packet, so these and the number of
packets are asked for in unary. -/
theorem computableInPolyTime_nativeChild (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hT : ComputableInPolyTime (fun x => 2 ^ (i x + 1)) encIn encUnary)
    (hpt : ComputableInPolyTime pt encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat))
    (hr : ComputableInPolyTime r encIn encNat)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)))
    (hpk : ComputableInPolyTime pk encIn PacketPacking.encNativePacking)
    (hP : ComputableInPolyTime (fun x => (pk x).2.1) encIn encUnary)
    (hβ : ComputableInPolyTime β encIn (encList encUnary))
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x =>
      nativeChild (fl x) (a x) (i x) (pt x) (t x) (ζ x) (r x) (D x) (pk x) (β x) (g x))
      encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)) := by
  obtain ⟨hwords, hplace⟩ := packing_parts hpk
  have hV := DescribedNetwork.vertices_polyTime.comp hD
  have hends := (DescribedNetwork.computableInPolyTime_edgeEnds (VertexDesc.enc encT)).comp hD
  have hgroups := computableInPolyTime_groupsOf hr hi
    ((ComputableInPolyTime.length_list _).comp hV) hwords
  have hpackets : ComputableInPolyTime (fun x => (pk x).2.2.map Prod.fst) encIn
      (encList encNat) :=
    ComputableInPolyTime.mapWithInput (f := fun _ q => q.1) hplace
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _))
  have hcedges : ComputableInPolyTime (fun x =>
      childEdgeList (groupsOf (r x) (i x) (D x).vertices.length (pk x).1) (g x) (D x).edgeEnds
        ((pk x).2.2.map Prod.fst)) encIn (encList (encPair encNat encNat)) :=
    computableInPolyTime_childEdgeList.comp ((hgroups.prod hg).prod (hends.prod hpackets))
  have hpair := ((ComputableInPolyTime.length_list _).comp hcedges).prod
    (ComputableInPolyTime.listAppend' (retained_polyTime hr hV hgroups hg hends)
      (packetVertices_polyTime hfl ha hL hi hT hpt ht hζ hβ hg hgroups hends hP hcedges hplace))
  have hsymm : ComputableInPolyTime (DescribedNetwork.equivProd (T := VertexDesc T)).symm
      (encPair encUnary (encList (encPair (encList encNat) (VertexDesc.enc encT))))
      (DescribedNetwork.encDescribed (VertexDesc.enc encT)) :=
    ComputableInPolyTime.of_eq fun y => by
      rw [DescribedNetwork.encDescribed, encOfEquiv_apply, Equiv.apply_symm_apply]
  exact (hsymm.comp hpair).of_enc_eq fun x => by
    rw [Function.comp_apply]
    rfl

end PolyTime

/-! ### The child of the native parent packing -/

/-- A left fold of `max` over numbers at most `n`, from at most `n`, is at most `n`. -/
private theorem foldl_max_le {l : List ℕ} {m n : ℕ} (hm : m ≤ n) (hl : ∀ x ∈ l, x ≤ n) :
    l.foldl max m ≤ n := by
  induction l generalizing m with
  | nil => exact hm
  | cons x l ih =>
    exact ih (max_le hm (hl x List.mem_cons_self)) fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- **At most `M (2 ^ a) ^ 12` packets**: the native parent packing of a network with `M` edges
has at most one block of `2 ^ a` slots per edge, times the `4096 ^ a` words of pairs of
symbols. -/
theorem numPackets_nativeParentPacking_le (r a : ℕ) (D : DescribedNetwork (VertexDesc T)) :
    (nativeParentPacking r a D).2.1 ≤ D.numEdges * (2 ^ a) ^ 12 := by
  set pairs := PacketPacking.edgeWordPairs (PacketPacking.labelWords r (D.vertices.length - r) a 64
    (D.edgeEnds.map fun e => (e.1, e.2 - r))).1 (PacketPacking.labelWords r
    (D.vertices.length - r) a 64 (D.edgeEnds.map fun e => (e.1, e.2 - r))).2
    (D.edgeEnds.map fun e => (e.1, e.2 - r)) with hpairs
  have hlen : pairs.length = D.numEdges := by
    simp [hpairs, PacketPacking.edgeWordPairs, DescribedNetwork.edgeEnds]
  have hload : PacketPacking.maxLoadOf (PacketPacking.classIndices pairs) ≤ D.numEdges := by
    refine foldl_max_le (Nat.zero_le _) fun x hx => ?_
    simp only [PacketPacking.classIndices, List.map_map, List.mem_map, List.mem_range,
      Function.comp_apply] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have := List.countP_le_length (l := List.range j)
      (p := fun j' => decide (pairs.getD j' ([], []) = pairs.getD j ([], [])))
    rw [List.length_range] at this
    omega
  have hblocks : (PacketPacking.maxLoadOf (PacketPacking.classIndices pairs) + (2 ^ a - 1)) /
      2 ^ a ≤ D.numEdges := by
    have hL : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    rcases Nat.eq_zero_or_pos D.numEdges with h0 | hpos
    · rw [h0] at hload ⊢
      rw [Nat.le_zero.mp hload, zero_add]
      exact (Nat.div_eq_of_lt (by omega)).le
    · refine Nat.div_le_of_le_mul ?_
      have : 2 ^ a - 1 ≤ (2 ^ a - 1) * D.numEdges := Nat.le_mul_of_pos_right _ hpos
      have e : 2 ^ a * D.numEdges = D.numEdges + (2 ^ a - 1) * D.numEdges := by
        rw [Nat.sub_mul, one_mul]
        have : D.numEdges ≤ 2 ^ a * D.numEdges := Nat.le_mul_of_pos_left _ (by omega)
        omega
      omega
  have h64 : (64 * 64) ^ a = (2 ^ a) ^ 12 := by
    rw [← pow_mul, mul_comm a 12, pow_mul]
    norm_num
  change (PacketPacking.maxLoadOf (PacketPacking.classIndices pairs) + (2 ^ a - 1)) / 2 ^ a *
    (64 * 64) ^ a ≤ _
  rw [h64]
  exact Nat.mul_le_mul_right _ hblocks

section PolyTime

variable {δ : Type} {encIn : δ ↪ List Bool} {fl ζ β : δ → List ℕ} {a i pt r g : δ → ℕ}
  {t : δ → ℤ} {D : δ → DescribedNetwork (VertexDesc T)}

/-- **The native parent packing is polynomial-time**, with the number of rows and `a` in
unary. -/
theorem computableInPolyTime_nativeParentPacking (hr : ComputableInPolyTime r encIn encUnary)
    (ha : ComputableInPolyTime a encIn encUnary)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT))) :
    ComputableInPolyTime (fun x => nativeParentPacking (r x) (a x) (D x)) encIn
      PacketPacking.encNativePacking := by
  have hends := (DescribedNetwork.computableInPolyTime_edgeEnds (VertexDesc.enc encT)).comp hD
  have hrb := ComputableInPolyTime.unary_to_binary.comp hr
  have hshift : ComputableInPolyTime (fun x => (D x).edgeEnds.map fun e => (e.1, e.2 - r x))
      encIn (encList (encPair encNat encNat)) :=
    ComputableInPolyTime.mapWithInput (f := fun x e => (e.1, e.2 - r x)) hends
      (((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)).prod
        (ComputableInPolyTime.binary_sub' ((ComputableInPolyTime.snd _ _).comp
          (ComputableInPolyTime.snd _ _)) (hrb.comp (ComputableInPolyTime.fst _ _))))
  have hnC : ComputableInPolyTime (fun x => (D x).vertices.length - r x) encIn encUnary :=
    ComputableInPolyTime.unary_sub' ((ComputableInPolyTime.length_list _).comp
      (DescribedNetwork.vertices_polyTime.comp hD)) hr
  have hin : ComputableInPolyTime (fun x => (((r x, (D x).vertices.length - r x, a x), 64,
      (D x).edgeEnds.map fun e => (e.1, e.2 - r x)) : PacketPacking.PackingInput)) encIn
      (encPair (encPair encUnary (encPair encUnary encUnary))
        (encPair encNat (encList (encPair encNat encNat)))) :=
    (hr.prod (hnC.prod ha)).prod ((ComputableInPolyTime.const 64).prod hshift)
  have h := PacketPacking.computableInPolyTime_nativePacking.comp hin
  refine h.of_enc_eq fun x => ?_
  simp only [Function.comp_apply, nativeParentPacking]

/-- **The number of packets of the native parent packing in unary** is polynomial-time, with `a`
and `2 ^ a` in unary. -/
theorem computableInPolyTime_numPackets_nativeParentPacking
    (hr : ComputableInPolyTime r encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT))) :
    ComputableInPolyTime (fun x => (nativeParentPacking (r x) (a x) (D x)).2.1) encIn
      encUnary := by
  have hpk : ComputableInPolyTime (fun x => nativeParentPacking (r x) (a x) (D x)) encIn
      (encPair (encPair (encList (encList encNat)) (encList (encList encNat)))
        (encPair encNat (encList (encPair encNat encNat)))) :=
    computableInPolyTime_nativeParentPacking hr ha hD
  exact ComputableInPolyTime.binary_to_unary_bounded
    ((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hpk))
    (ComputableInPolyTime.unary_mul' (DescribedNetwork.numEdges_polyTime.comp hD)
      ((ComputableInPolyTime.unary_pow 12).comp hL))
    fun x => numPackets_nativeParentPacking_le (r x) (a x) (D x)

/-- **The native child of the native parent packing is polynomial-time**, with the number of rows
in unary (`computableInPolyTime_nativeChild` for `nativeParentPacking`). -/
theorem computableInPolyTime_nativeChild_nativeParentPacking
    (hfl : ComputableInPolyTime fl encIn (encList encNat))
    (ha : ComputableInPolyTime a encIn encUnary)
    (hL : ComputableInPolyTime (fun x => 2 ^ a x) encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hT : ComputableInPolyTime (fun x => 2 ^ (i x + 1)) encIn encUnary)
    (hpt : ComputableInPolyTime pt encIn encUnary) (ht : ComputableInPolyTime t encIn encIntBin)
    (hζ : ComputableInPolyTime ζ encIn (encList encNat))
    (hr : ComputableInPolyTime r encIn encUnary)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)))
    (hβ : ComputableInPolyTime β encIn (encList encUnary))
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x => nativeChild (fl x) (a x) (i x) (pt x) (t x) (ζ x) (r x) (D x)
      (nativeParentPacking (r x) (a x) (D x)) (β x) (g x))
      encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)) :=
  computableInPolyTime_nativeChild hfl ha hL hi hT hpt ht hζ
    (ComputableInPolyTime.unary_to_binary.comp hr) hD
    (computableInPolyTime_nativeParentPacking hr ha hD)
    (computableInPolyTime_numPackets_nativeParentPacking hr ha hL hD) hβ hg

/-- **The number of rows of the native child of the native parent packing is polynomial-time.** -/
theorem computableInPolyTime_childRows_nativeParentPacking
    (hr : ComputableInPolyTime r encIn encUnary) (ha : ComputableInPolyTime a encIn encUnary)
    (hi : ComputableInPolyTime i encIn encUnary)
    (hD : ComputableInPolyTime D encIn (DescribedNetwork.encDescribed (VertexDesc.enc encT)))
    (hg : ComputableInPolyTime g encIn encNat) :
    ComputableInPolyTime (fun x => childRows (r x) (i x) (D x)
      (nativeParentPacking (r x) (a x) (D x)) (g x)) encIn encNat :=
  computableInPolyTime_childRows (ComputableInPolyTime.unary_to_binary.comp hr) hi hD
    (computableInPolyTime_nativeParentPacking hr ha hD) hg

end PolyTime

/-! ### The shape of the native child -/

section Shape

variable (fl : List ℕ) (a i pt : ℕ) (t : ℤ) (ζ : List ℕ) (r : ℕ)
  (D : DescribedNetwork (VertexDesc T))
  (pk : (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ)) (β : List ℕ) (g : ℕ)

/-- **The child has at most twice as many edges as the parent**: one per end of a parent edge in
group `g`. -/
theorem numEdges_nativeChild_le :
    (nativeChild fl a i pt t ζ r D pk β g).numEdges ≤ 2 * D.numEdges := by
  have hends : D.edgeEnds.length = D.numEdges := by simp [DescribedNetwork.edgeEnds]
  have hzip : (D.edgeEnds.zip (pk.2.2.map Prod.fst)).length ≤ D.numEdges := by
    rw [List.length_zip]
    omega
  simp only [nativeChild, childEdgeList, List.length_append, List.length_map]
  have h₁ := List.length_filter_le (fun q : (ℕ × ℕ) × ℕ =>
    decide ((groupsOf r i D.vertices.length pk.1).getD q.1.1 0 = g))
    (D.edgeEnds.zip (pk.2.2.map Prod.fst))
  have h₂ := List.length_filter_le (fun q : (ℕ × ℕ) × ℕ =>
    decide ((groupsOf r i D.vertices.length pk.1).getD q.1.2 0 = g))
    (D.edgeEnds.zip (pk.2.2.map Prod.fst))
  omega

/-- **The vertices of the child**: its rows, the parent vertices of group `g`, then one packet
vertex per packet. -/
theorem length_vertices_nativeChild :
    (nativeChild fl a i pt t ζ r D pk β g).vertices.length = childRows r i D pk g + pk.2.1 := by
  simp only [nativeChild, childRows, List.length_append, List.length_map, List.length_range]
  congr 1
  rw [List.count_eq_countP, List.countP_eq_length_filter, groupsOf, List.filter_map,
    List.length_map]
  congr 1
  refine List.filter_congr fun v hv => ?_
  rw [List.mem_range] at hv
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem _ _ (by simpa using hv), List.getElem_map, List.getElem_range,
    beq_eq_decide]

/-- **Every vertex of the child is a parent vertex or a packet vertex.** A vertex of the child is
either a parent vertex with renumbered ports, with the same descriptor and the same number of
ports, or the vertex of a packet `q`, whose descriptor is its context, tags of its ports with
slots from the packing (or `0`), and its slice of `β`. -/
theorem mem_vertices_nativeChild {v : List ℕ × VertexDesc T}
    (hv : v ∈ (nativeChild fl a i pt t ζ r D pk β g).vertices) :
    (∃ w ∈ D.vertices, v.2 = w.2 ∧ v.1.length = w.1.length) ∨
      ∃ q < pk.2.1, ∃ tags : List (Bool × ℕ),
        v.2 = .inr (packetCtx fl a i pt t ζ g q, tags, betaSlice i pt β q) ∧
          tags.length = v.1.length ∧ ∀ b ∈ tags, b.2 = 0 ∨ ∃ y ∈ pk.2.2, b.2 = y.2 := by
  simp only [nativeChild, List.mem_append, List.mem_map, List.mem_filter, List.mem_range] at hv
  rcases hv with ⟨u, ⟨hu, -⟩, rfl⟩ | ⟨q, hq, rfl⟩
  · refine Or.inl ⟨D.vertices.getD u defaultVertex, ?_, rfl, List.length_map _⟩
    rw [List.getD_eq_getElem _ _ hu]
    exact List.getElem_mem hu
  · refine Or.inr ⟨q, hq, _, rfl, List.length_map _, fun b hb => ?_⟩
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    rcases lt_or_ge (parentEdge (groupsOf r i D.vertices.length pk.1) g D.edgeEnds j)
      pk.2.2.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact Or.inr ⟨_, List.getElem_mem h, rfl⟩
    · rw [List.getD_eq_default _ _ h]
      exact Or.inl rfl

/-- The slice of `β` at a packet has at most `2 ^ (i + 1) p_t` exponents. -/
theorem length_betaSlice_le (q : ℕ) : (betaSlice i pt β q).length ≤ 2 ^ (i + 1) * pt :=
  List.length_take_le _ _

/-- The exponents in the slice of `β` at a packet are exponents of `β`. -/
theorem mem_of_mem_betaSlice {q b : ℕ} (hb : b ∈ betaSlice i pt β q) : b ∈ β :=
  List.mem_of_mem_drop (List.mem_of_mem_take hb)

end Shape

end Cslib.Circuits.Frontier.NativeChild
