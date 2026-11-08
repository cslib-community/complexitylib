/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Parameterized.CrossComposition
public import Complexity.Computability.Complexity.Problems.Hamiltonian
public import Complexity.Computability.Complexity.Problems.LongPath
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# k-Path has no polynomial kernel unless `coNP ⊆ NP/poly`

k-Path (`Cslib.Complexity.LongPath`), parameterized by the number `k` of vertices of the path,
has no polynomial kernel and no polynomial compression unless `coNP ⊆ NP/poly`. Bodlaender,
Jansen and Kratsch attribute the kernel lower bound to Bodlaender, Downey, Fellows and Hermelin
[BodlaenderJansenKratsch2014, Section 1][BodlaenderDowneyFellowsHermelin2009]; the theorem number
in the latter is not verified here. This file derives it from the cross-composition theorem
[BodlaenderJansenKratsch2014, Corollary 2] (`Cslib.Complexity.not_hasPolyKernel_LongPath`,
`Cslib.Complexity.not_hasPolyCompression_LongPath`), with `coNP ⊄ NP/poly` an explicit
hypothesis. Like `Cslib.Complexity.not_hasPolyKernel_of_orCrossComposes`, only the
`NP ⊆ coNP/poly` conclusion of Corollary 2 is stated; the failure of the OR-distillation
conjecture and the collapse of the polynomial hierarchy are not formalized.

The OR-cross-composition from undirected Hamiltonian path (`Cslib.Complexity.HamPath`) into
k-Path is a construction within the framework of [BodlaenderJansenKratsch2014, Section 3]; it is
not taken from a source, and no novelty is claimed. Instances are related when their graphs have
equally many distinct declared vertices (`Cslib.Complexity.IsPolyEquivalence.of_key`), as the
relation of [BodlaenderJansenKratsch2014, Theorem 7] compares vertex counts. Entry `i` of the list
becomes a copy of its graph (`Cslib.Complexity.HamPath.pendantCopy`): every declared vertex `v`
is relabeled `Nat.pair i (p + 2)`, for `p` the position of the first occurrence of `v`, and two
pendant vertices `Nat.pair i 0` and `Nat.pair i 1` are attached to the copies of `s` and `t`. The
output (`Cslib.Complexity.HamPath.toLongPath`) is the disjoint union of the copies, with target
`N + 2` for `N` the common number of distinct vertices. A path on `N + 2` vertices stays in one
copy, as edges do not join copies, and visits every vertex of that copy. Its ends are then the
two pendant vertices, whose only neighbors are the copies of `s` and `t`, so removing them leaves
a Hamiltonian path from `s` to `t`; conversely, the pendant vertices extend a Hamiltonian path
(`Cslib.Complexity.HamPath.toLongPath_mem_iff`). The target is at most two more than the length
of an encoded entry, independent of the number of entries. The labels use positions, which are
bounded by the encoded length, because `Nat.pair` is computed in polynomial time on unary inputs
only. On one instance the construction is a polynomial-time reduction, so k-Path is `NP`-hard
(`Cslib.Complexity.LongPath_npHard`).

Instances are encoded as `encPair encGraph encNat`, with the target in binary, as for
`Cslib.Complexity.ColorfulPath_mem_FPT`; [BodlaenderJansenKratsch2014, Section 2] writes the
parameter in unary. A compression (`Cslib.Complexity.HasPolyCompression`) runs in time polynomial
in the encoded length plus the parameter, which covers the time bound of the source's
kernelizations and compressions [BodlaenderJansenKratsch2014, Definitions 1 and 2], while a
kernelization (`Cslib.Complexity.HasPolyKernel`) must run in time polynomial in the encoded length
alone. Membership of k-Path in `NP` is not proved here.

## Main definitions

* `Cslib.Complexity.HamPath.toLongPath`: the cross-composition of `HamPath` into k-Path.

## Main results

* `Cslib.Complexity.HamPath.toLongPath_mem_iff`: correctness on lists of related instances.
* `Cslib.Complexity.HamPath.orCrossComposes_LongPath`: `HamPath` OR-cross-composes into k-Path.
* `Cslib.Complexity.LongPath_npHard`: k-Path is `NP`-hard.
* `Cslib.Complexity.not_hasPolyKernel_LongPath`,
  `Cslib.Complexity.not_hasPolyCompression_LongPath`,
  `Cslib.Complexity.coNP_subset_NPPoly_of_hasPolyCompression_LongPath`: k-Path has no polynomial
  kernel and no polynomial compression unless `coNP ⊆ NP/poly`.

## References

* [H. L. Bodlaender, R. G. Downey, M. R. Fellows, D. Hermelin, *On problems without polynomial
  kernels*][BodlaenderDowneyFellowsHermelin2009]
* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace HamPath

/-- The label of the vertex `v` of the graph `G` in copy `i`: the pair of `i` and two more than
the position of the first occurrence of `v` in the vertex list of `G`. -/
def copyLabel (G : Graph) (i v : ℕ) : ℕ := Nat.pair i (G.1.idxOf v + 2)

/-- Copy `i` of the instance `x = (G, s, t)`: the vertices of `G`, relabeled by `copyLabel`, with
two pendant vertices `Nat.pair i 0` and `Nat.pair i 1` attached to `s` and to `t`. -/
def pendantCopy (x : Graph × ℕ × ℕ) (i : ℕ) : Graph :=
  (Nat.pair i 0 :: Nat.pair i 1 :: x.1.1.map (copyLabel x.1 i),
    (Nat.pair i 0, copyLabel x.1 i x.2.1) :: (Nat.pair i 1, copyLabel x.1 i x.2.2) ::
      x.1.2.map fun e => (copyLabel x.1 i e.1, copyLabel x.1 i e.2))

/-- The disjoint union of the pendant copies of a list of instances, copy `i` for entry `i`. -/
def pendantUnion (l : List (Graph × ℕ × ℕ)) : Graph :=
  (l.zipIdx.flatMap fun p => (pendantCopy p.1 p.2).1,
    l.zipIdx.flatMap fun p => (pendantCopy p.1 p.2).2)

/-- The cross-composition of `HamPath` into `LongPath`: the disjoint union of the pendant copies,
with target two more than the number of distinct vertices of the first entry. -/
def toLongPath (l : List (Graph × ℕ × ℕ)) : Graph × ℕ :=
  (pendantUnion l, (l.headD default).1.distinctVertices.length + 2)

/-! ### Polynomial time -/

private theorem computableInPolyTime_copyLabel {γ : Type} {enc : γ ↪ List Bool}
    {G : γ → Graph} {i v : γ → ℕ} (hG : ComputableInPolyTime G enc encGraph)
    (hi : ComputableInPolyTime i enc encUnary) (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun c => copyLabel (G c) (i c) (v c)) enc encNat := by
  have hpair : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hV : ComputableInPolyTime (fun c => (G c).1) enc (encList encNat) := by
    unfold encGraph at hG
    exact hG.fst'
  have hidx : ComputableInPolyTime (fun c => (G c).1.idxOf (v c)) enc encUnary :=
    idxOfWithInput hV hv
  exact unary_to_binary.comp (hpair.comp (hi.prod (by fun_prop)))

private abbrev encInst : Graph × ℕ × ℕ ↪ List Bool := encPair encGraph (encPair encNat encNat)

/-- Building a pendant copy is polynomial-time, with the copy index in unary. -/
private theorem computableInPolyTime_pendantCopy :
    ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => pendantCopy p.1 p.2)
      (encPair encInst encUnary) encGraph := by
  have hpair : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encUnary := by fun_prop
  have hG : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => p.1.1)
      (encPair encInst encUnary) encGraph := by fun_prop
  have hi : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => p.2)
      (encPair encInst encUnary) encUnary := by fun_prop
  have h0 : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => Nat.pair p.2 0)
      (encPair encInst encUnary) encNat :=
    unary_to_binary.comp (hpair.comp (hi.prod (const 0)))
  have h1 : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => Nat.pair p.2 1)
      (encPair encInst encUnary) encNat :=
    unary_to_binary.comp (hpair.comp (hi.prod (const 1)))
  have hs : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => copyLabel p.1.1 p.2 p.1.2.1)
      (encPair encInst encUnary) encNat :=
    computableInPolyTime_copyLabel hG hi (by fun_prop)
  have ht : ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => copyLabel p.1.1 p.2 p.1.2.2)
      (encPair encInst encUnary) encNat :=
    computableInPolyTime_copyLabel hG hi (by fun_prop)
  have hV : ComputableInPolyTime
      (fun p : (Graph × ℕ × ℕ) × ℕ => p.1.1.1.map (copyLabel p.1.1 p.2))
      (encPair encInst encUnary) (encList encNat) := by
    refine mapWithInput (by unfold encGraph at hG; exact hG.fst') ?_
    exact computableInPolyTime_copyLabel (hG.comp (fst _ _)) (hi.comp (fst _ _)) (snd _ _)
  have hE : ComputableInPolyTime
      (fun p : (Graph × ℕ × ℕ) × ℕ =>
        p.1.1.2.map fun e => (copyLabel p.1.1 p.2 e.1, copyLabel p.1.1 p.2 e.2))
      (encPair encInst encUnary) (encList (encPair encNat encNat)) := by
    refine mapWithInput (by unfold encGraph at hG; exact hG.snd') ?_
    exact (computableInPolyTime_copyLabel (hG.comp (fst _ _)) (hi.comp (fst _ _))
      (snd _ _).fst').prod
      (computableInPolyTime_copyLabel (hG.comp (fst _ _)) (hi.comp (fst _ _)) (snd _ _).snd')
  unfold pendantCopy encGraph
  exact (cons' h0 (cons' h1 hV)).prod (cons' (h0.prod hs) (cons' (h1.prod ht) hE))

/-- The cross-composition `toLongPath` is polynomial-time. -/
theorem computableInPolyTime_toLongPath :
    ComputableInPolyTime toLongPath (encList (encPair encGraph (encPair encNat encNat)))
      (encPair encGraph encNat) := by
  have hz : ComputableInPolyTime (fun l : List (Graph × ℕ × ℕ) => l.zipIdx) (encList encInst)
      (encList (encPair encInst encUnary)) :=
    (ComputableTidilyInPolyTime.zipIdx encInst).computableInPolyTime
  have hc := computableInPolyTime_pendantCopy
  unfold encGraph at hc
  have hU : ComputableInPolyTime pendantUnion (encList encInst) encGraph := by
    unfold pendantUnion encGraph
    exact (flatMapWithInput hz (hc.fst'.comp (snd _ _))).prod
      (flatMapWithInput hz (hc.snd'.comp (snd _ _)))
  have hk : ComputableInPolyTime
      (fun l : List (Graph × ℕ × ℕ) => (l.headD default).1.distinctVertices.length + 2)
      (encList encInst) encNat := by
    have hh : ComputableInPolyTime (fun l : List (Graph × ℕ × ℕ) => (l.headD default).1)
        (encList encInst) encGraph := (headD (encA := encInst) default).fst'
    have hn : ComputableInPolyTime
        (fun l : List (Graph × ℕ × ℕ) => (l.headD default).1.distinctVertices.length)
        (encList encInst) encUnary :=
      (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp hh)
    exact unary_to_binary.comp (by fun_prop)
  exact hU.prod hk

/-! ### Labels -/

private theorem unpair_copyLabel_fst (G : Graph) (i v : ℕ) :
    (Nat.unpair (copyLabel G i v)).1 = i := by
  simp only [copyLabel, Nat.unpair_pair]

private theorem copyLabel_ne_pair {G : Graph} {i v i' j : ℕ} (hj : j < 2) :
    copyLabel G i v ≠ Nat.pair i' j := by
  intro h
  rw [copyLabel, Nat.pair_eq_pair] at h
  omega

private theorem copyLabel_inj {G : Graph} {i u v : ℕ} (hu : u ∈ G.1) :
    copyLabel G i u = copyLabel G i v ↔ u = v := by
  rw [copyLabel, copyLabel, Nat.pair_eq_pair, ← List.idxOf_inj hu]
  omega

private theorem pair_zero_ne_pair_one (i i' : ℕ) : Nat.pair i 0 ≠ Nat.pair i' 1 := by
  intro h
  rw [Nat.pair_eq_pair] at h
  omega

/-! ### One copy -/

private theorem mem_pendantCopy_fst {x : Graph × ℕ × ℕ} {i w : ℕ} :
    w ∈ (pendantCopy x i).1 ↔
      w = Nat.pair i 0 ∨ w = Nat.pair i 1 ∨ ∃ v ∈ x.1.1, copyLabel x.1 i v = w := by
  simp only [pendantCopy, List.mem_cons, List.mem_map]

private theorem mem_pendantCopy_snd {x : Graph × ℕ × ℕ} {i : ℕ} {e : ℕ × ℕ} :
    e ∈ (pendantCopy x i).2 ↔ e = (Nat.pair i 0, copyLabel x.1 i x.2.1) ∨
      e = (Nat.pair i 1, copyLabel x.1 i x.2.2) ∨
      ∃ d ∈ x.1.2, (copyLabel x.1 i d.1, copyLabel x.1 i d.2) = e := by
  simp only [pendantCopy, List.mem_cons, List.mem_map]

private theorem unpair_of_mem_pendantCopy_fst {x : Graph × ℕ × ℕ} {i w : ℕ}
    (h : w ∈ (pendantCopy x i).1) : (Nat.unpair w).1 = i := by
  rcases mem_pendantCopy_fst.1 h with rfl | rfl | ⟨v, -, rfl⟩
  · simp only [Nat.unpair_pair]
  · simp only [Nat.unpair_pair]
  · exact unpair_copyLabel_fst _ _ _

private theorem unpair_of_mem_pendantCopy_snd {x : Graph × ℕ × ℕ} {i : ℕ} {e : ℕ × ℕ}
    (h : e ∈ (pendantCopy x i).2) : (Nat.unpair e.1).1 = i ∧ (Nat.unpair e.2).1 = i := by
  rcases mem_pendantCopy_snd.1 h with rfl | rfl | ⟨d, -, rfl⟩
  · exact ⟨by simp only [Nat.unpair_pair], unpair_copyLabel_fst _ _ _⟩
  · exact ⟨by simp only [Nat.unpair_pair], unpair_copyLabel_fst _ _ _⟩
  · exact ⟨unpair_copyLabel_fst _ _ _, unpair_copyLabel_fst _ _ _⟩

/-! ### The disjoint union -/

private theorem mem_pendantUnion_fst {l : List (Graph × ℕ × ℕ)} {w : ℕ} :
    w ∈ (pendantUnion l).1 ↔ ∃ x i, l[i]? = some x ∧ w ∈ (pendantCopy x i).1 := by
  simp only [pendantUnion, List.mem_flatMap, List.mem_zipIdx_iff_getElem?, Prod.exists]

private theorem mem_pendantUnion_snd {l : List (Graph × ℕ × ℕ)} {e : ℕ × ℕ} :
    e ∈ (pendantUnion l).2 ↔ ∃ x i, l[i]? = some x ∧ e ∈ (pendantCopy x i).2 := by
  simp only [pendantUnion, List.mem_flatMap, List.mem_zipIdx_iff_getElem?, Prod.exists]

/-- On the vertices of copy `i`, the union has the vertices of copy `i`. -/
private theorem mem_pendantUnion_fst_iff {l : List (Graph × ℕ × ℕ)} {x : Graph × ℕ × ℕ}
    {i w : ℕ} (hx : l[i]? = some x) (hw : (Nat.unpair w).1 = i) :
    w ∈ (pendantUnion l).1 ↔ w ∈ (pendantCopy x i).1 := by
  refine ⟨fun h => ?_, fun h => mem_pendantUnion_fst.2 ⟨x, i, hx, h⟩⟩
  obtain ⟨y, j, hy, hwy⟩ := mem_pendantUnion_fst.1 h
  obtain rfl : j = i := (unpair_of_mem_pendantCopy_fst hwy).symm.trans hw
  obtain rfl : y = x := Option.some_injective _ (hy.symm.trans hx)
  exact hwy

/-- On the edges at copy `i`, the union has the edges of copy `i`. -/
private theorem mem_pendantUnion_snd_iff {l : List (Graph × ℕ × ℕ)} {x : Graph × ℕ × ℕ}
    {i : ℕ} {e : ℕ × ℕ} (hx : l[i]? = some x) (he : (Nat.unpair e.1).1 = i) :
    e ∈ (pendantUnion l).2 ↔ e ∈ (pendantCopy x i).2 := by
  refine ⟨fun h => ?_, fun h => mem_pendantUnion_snd.2 ⟨x, i, hx, h⟩⟩
  obtain ⟨y, j, hy, hey⟩ := mem_pendantUnion_snd.1 h
  obtain rfl : j = i := (unpair_of_mem_pendantCopy_snd hey).1.symm.trans he
  obtain rfl : y = x := Option.some_injective _ (hy.symm.trans hx)
  exact hey

/-- Adjacent vertices of the union lie in the same copy. -/
private theorem unpair_fst_eq_of_adj {l : List (Graph × ℕ × ℕ)} {u v : ℕ}
    (h : (pendantUnion l).toSimpleGraph.Adj u v) : (Nat.unpair u).1 = (Nat.unpair v).1 := by
  rw [Graph.toSimpleGraph_adj] at h
  rcases h.2 with h | h
  · obtain ⟨y, j, -, hey⟩ := mem_pendantUnion_snd.1 h
    have := unpair_of_mem_pendantCopy_snd hey
    exact this.1.trans this.2.symm
  · obtain ⟨y, j, -, hey⟩ := mem_pendantUnion_snd.1 h
    have := unpair_of_mem_pendantCopy_snd hey
    exact this.2.trans this.1.symm

/-- Adjacency of the union at copy `i` is adjacency of copy `i`. -/
private theorem adj_pendantUnion_iff {l : List (Graph × ℕ × ℕ)} {x : Graph × ℕ × ℕ}
    {i u v : ℕ} (hx : l[i]? = some x) (hu : (Nat.unpair u).1 = i)
    (hv : (Nat.unpair v).1 = i) :
    (pendantUnion l).toSimpleGraph.Adj u v ↔ (pendantCopy x i).toSimpleGraph.Adj u v := by
  rw [Graph.toSimpleGraph_adj, Graph.toSimpleGraph_adj,
    mem_pendantUnion_snd_iff (e := (u, v)) hx hu, mem_pendantUnion_snd_iff (e := (v, u)) hx hv]

/-- **The union has a path on `k + 1` vertices exactly when some copy has one.** -/
private theorem pendantUnion_mem_LongPath_iff {l : List (Graph × ℕ × ℕ)} {k : ℕ} :
    (pendantUnion l, k + 1) ∈ LongPath ↔
      ∃ x i, l[i]? = some x ∧ (pendantCopy x i, k + 1) ∈ LongPath := by
  constructor
  · rintro ⟨q, ⟨hnd, hV, hch⟩, hlen⟩
    obtain ⟨w, q', rfl⟩ : ∃ w q', q = w :: q' := by
      cases q with
      | nil => simp at hlen
      | cons w q' => exact ⟨w, q', rfl⟩
    obtain ⟨x, i, hx, hw⟩ := mem_pendantUnion_fst.1 (hV w List.mem_cons_self)
    have hi : ∀ v ∈ w :: q', (Nat.unpair v).1 = i :=
      List.IsChain.induction (fun v => (Nat.unpair v).1 = i) (w :: q') hch
        (fun _ _ hab hu => (unpair_fst_eq_of_adj hab).symm.trans hu)
        (fun _ => unpair_of_mem_pendantCopy_fst hw)
    refine ⟨x, i, hx, w :: q', ⟨hnd, fun v hv => (mem_pendantUnion_fst_iff hx (hi v hv)).1
      (hV v hv), ?_⟩, hlen⟩
    refine (List.IsChain.iff_mem.1 hch).imp fun a b h => ?_
    exact (adj_pendantUnion_iff hx (hi a h.1) (hi b h.2.1)).1 h.2.2
  · rintro ⟨x, i, hx, q, ⟨hnd, hV, hch⟩, hlen⟩
    refine ⟨q, ⟨hnd, fun v hv => mem_pendantUnion_fst.2 ⟨x, i, hx, hV v hv⟩, ?_⟩, hlen⟩
    refine (List.IsChain.iff_mem.1 hch).imp fun a b h => ?_
    exact (adj_pendantUnion_iff hx (unpair_of_mem_pendantCopy_fst (hV a h.1))
      (unpair_of_mem_pendantCopy_fst (hV b h.2.1))).2 h.2.2

/-! ### Paths through one copy -/

section Copy

variable {G : Graph} {s t i : ℕ}

/-- The only neighbor of the pendant vertex `Nat.pair i 0` is the copy of `s`. -/
private theorem eq_of_adj_pair_zero {w : ℕ}
    (h : (pendantCopy (G, s, t) i).toSimpleGraph.Adj (Nat.pair i 0) w) :
    w = copyLabel G i s := by
  rw [Graph.toSimpleGraph_adj] at h
  rcases h.2 with h | h
  · rcases mem_pendantCopy_snd.1 h with h | h | ⟨d, -, h⟩
    · exact (Prod.mk.inj h).2
    · exact absurd (Prod.mk.inj h).1 (pair_zero_ne_pair_one i i)
    · exact absurd (Prod.mk.inj h).1 (copyLabel_ne_pair (by omega))
  · rcases mem_pendantCopy_snd.1 h with h | h | ⟨d, -, h⟩
    · exact absurd (Prod.mk.inj h).2.symm (copyLabel_ne_pair (by omega))
    · exact absurd (Prod.mk.inj h).2.symm (copyLabel_ne_pair (by omega))
    · exact absurd (Prod.mk.inj h).2 (copyLabel_ne_pair (by omega))

/-- The only neighbor of the pendant vertex `Nat.pair i 1` is the copy of `t`. -/
private theorem eq_of_adj_pair_one {w : ℕ}
    (h : (pendantCopy (G, s, t) i).toSimpleGraph.Adj (Nat.pair i 1) w) :
    w = copyLabel G i t := by
  rw [Graph.toSimpleGraph_adj] at h
  rcases h.2 with h | h
  · rcases mem_pendantCopy_snd.1 h with h | h | ⟨d, -, h⟩
    · exact absurd (Prod.mk.inj h).1.symm (pair_zero_ne_pair_one i i)
    · exact (Prod.mk.inj h).2
    · exact absurd (Prod.mk.inj h).1 (copyLabel_ne_pair (by omega))
  · rcases mem_pendantCopy_snd.1 h with h | h | ⟨d, -, h⟩
    · exact absurd (Prod.mk.inj h).2.symm (copyLabel_ne_pair (by omega))
    · exact absurd (Prod.mk.inj h).2.symm (copyLabel_ne_pair (by omega))
    · exact absurd (Prod.mk.inj h).2 (copyLabel_ne_pair (by omega))

/-- On copies of declared vertices, adjacency of the copy is adjacency of `G`. -/
private theorem adj_copyLabel_iff {u v : ℕ} (hu : u ∈ G.1) (hv : v ∈ G.1) :
    (pendantCopy (G, s, t) i).toSimpleGraph.Adj (copyLabel G i u) (copyLabel G i v) ↔
      G.toSimpleGraph.Adj u v := by
  have key : ∀ {u v : ℕ}, u ∈ G.1 → v ∈ G.1 →
      ((copyLabel G i u, copyLabel G i v) ∈ (pendantCopy (G, s, t) i).2 ↔ (u, v) ∈ G.2) := by
    intro u v hu hv
    rw [mem_pendantCopy_snd]
    constructor
    · rintro (h | h | ⟨d, hd, h⟩)
      · exact absurd (Prod.mk.inj h).1 (copyLabel_ne_pair (by omega))
      · exact absurd (Prod.mk.inj h).1 (copyLabel_ne_pair (by omega))
      · obtain ⟨h1, h2⟩ := Prod.mk.inj h
        rw [eq_comm, copyLabel_inj hu] at h1
        rw [eq_comm, copyLabel_inj hv] at h2
        subst h1 h2
        exact hd
    · exact fun h => Or.inr (Or.inr ⟨(u, v), h, rfl⟩)
  rw [Graph.toSimpleGraph_adj, Graph.toSimpleGraph_adj, key hu hv, key hv hu, Ne,
    copyLabel_inj hu]

private theorem pair_zero_mem_pendantCopy : Nat.pair i 0 ∈ (pendantCopy (G, s, t) i).1 :=
  mem_pendantCopy_fst.2 (Or.inl rfl)

private theorem pair_one_mem_pendantCopy : Nat.pair i 1 ∈ (pendantCopy (G, s, t) i).1 :=
  mem_pendantCopy_fst.2 (Or.inr (Or.inl rfl))

/-- A copy has two more distinct vertices than `G`. -/
private theorem card_pendantCopy :
    (pendantCopy (G, s, t) i).1.toFinset.card = G.distinctVertices.length + 2 := by
  have h0 : Nat.pair i 0 ∉ insert (Nat.pair i 1) (G.1.toFinset.image (copyLabel G i)) := by
    simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨pair_zero_ne_pair_one i i, fun v _ h => copyLabel_ne_pair (by omega) h⟩
  have h1 : Nat.pair i 1 ∉ G.1.toFinset.image (copyLabel G i) := by
    simp only [Finset.mem_image, not_exists, not_and]
    exact fun v _ h => copyLabel_ne_pair (by omega) h
  have hinj : Set.InjOn (copyLabel G i) G.1.toFinset := fun u hu v _ h =>
    (copyLabel_inj (List.mem_toFinset.1 (Finset.mem_coe.1 hu))).1 h
  have hV : (pendantCopy (G, s, t) i).1 =
      Nat.pair i 0 :: Nat.pair i 1 :: G.1.map (copyLabel G i) := rfl
  have hmap : (G.1.map (copyLabel G i)).toFinset = G.1.toFinset.image (copyLabel G i) := by
    ext w
    simp
  rw [hV, List.toFinset_cons, List.toFinset_cons, hmap,
    Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1,
    Finset.card_image_of_injOn hinj, Graph.length_distinctVertices]

/-- In a chain without repetitions of a symmetric relation, a vertex all of whose neighbors equal
`c` is the first or the last vertex. -/
private theorem head_or_last_of_forall_adj {R : ℕ → ℕ → Prop} {q : List ℕ} {z c : ℕ}
    (hnd : q.Nodup) (hch : q.IsChain R) (hz : z ∈ q) (hR : ∀ {w}, R w z ∨ R z w → w = c) :
    q.head? = some z ∨ q.getLast? = some z := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hz
  rcases List.eq_nil_or_concat l₁ with rfl | ⟨l₁, u, rfl⟩
  · exact Or.inl rfl
  rcases l₂ with _ | ⟨w, l₂⟩
  · right
    simp
  exfalso
  rw [List.concat_eq_append, List.append_assoc, List.cons_append, List.nil_append] at hnd hch
  have hu : u = c := hR (Or.inl (List.isChain_iff_forall_rel_of_append_cons_cons.1 hch
    (l₁ := l₁) (l₂ := w :: l₂) rfl))
  have hw : w = c := hR (Or.inr (List.isChain_iff_forall_rel_of_append_cons_cons.1 hch
    (l₁ := l₁ ++ [u]) (l₂ := l₂) (by simp only [List.append_assoc, List.cons_append,
      List.nil_append])))
  have hu' := (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1
  exact hu' (hu.trans hw.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self)

/-- A path of a copy from `Nat.pair i 0` to `Nat.pair i 1` through the copies of all declared
vertices gives a Hamiltonian path of `G` from `s` to `t`. -/
private theorem mem_HamPath_of_path {q : List ℕ} (hnd : q.Nodup)
    (hV : ∀ w ∈ q, w ∈ (pendantCopy (G, s, t) i).1)
    (hch : q.IsChain (pendantCopy (G, s, t) i).toSimpleGraph.Adj)
    (hcov : ∀ v ∈ G.1, copyLabel G i v ∈ q) (ha : q.head? = some (Nat.pair i 0))
    (hb : q.getLast? = some (Nat.pair i 1)) : (G, s, t) ∈ HamPath := by
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.1 hb
  obtain ⟨m, rfl⟩ : ∃ m, l = Nat.pair i 0 :: m := by
    cases l with
    | nil => exact absurd (Option.some_injective _ ha) (pair_zero_ne_pair_one i i).symm
    | cons a m =>
      rw [List.cons_append, List.head?_cons] at ha
      exact ⟨m, by rw [Option.some_injective _ ha]⟩
  have hnd' := List.nodup_cons.1 hnd
  have hb' : Nat.pair i 1 ∉ m := fun h =>
    (List.nodup_append.1 hnd'.2).2.2 _ h _ (List.mem_singleton_self _) rfl
  have hm : ∀ w ∈ m, ∃ v ∈ G.1, copyLabel G i v = w := by
    intro w hw
    rcases mem_pendantCopy_fst.1 (hV w (List.mem_cons_of_mem _ (List.mem_append_left _ hw)))
      with rfl | rfl | h
    · exact absurd (List.mem_append_left _ hw) hnd'.1
    · exact absurd hw hb'
    · exact h
  choose! dec hdec using hm
  obtain ⟨p, hpV, rfl⟩ : ∃ p : List ℕ, (∀ v ∈ p, v ∈ G.1) ∧ p.map (copyLabel G i) = m := by
    refine ⟨m.map dec, fun v hv => ?_, ?_⟩
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hv
      exact (hdec w hw).1
    · rw [List.map_map]
      exact List.map_congr_left (fun w hw => (hdec w hw).2) |>.trans (List.map_id _)
  have hpnd : p.Nodup := List.Nodup.of_map _ (List.nodup_append.1 hnd'.2).1
  rw [mem_HamPath_iff]
  refine ⟨p, hpnd, fun v => ⟨hpV v, fun hv => ?_⟩, ?_, ?_, ?_⟩
  · rcases List.mem_cons.1 (hcov v hv) with h | h
    · exact absurd h (copyLabel_ne_pair (by omega))
    rcases List.mem_append.1 h with h | h
    · obtain ⟨u, hu, huv⟩ := List.mem_map.1 h
      exact (copyLabel_inj (hpV u hu)).1 huv ▸ hu
    · exact absurd (List.mem_singleton.1 h) (copyLabel_ne_pair (by omega))
  · cases p with
    | nil =>
      simp only [List.map_nil] at hch
      exact absurd (eq_of_adj_pair_zero (List.isChain_cons_cons.1 hch).1)
        (copyLabel_ne_pair (by omega)).symm
    | cons v p =>
      simp only [List.map_cons, List.cons_append] at hch
      have h := eq_of_adj_pair_zero (List.isChain_cons_cons.1 hch).1
      rw [copyLabel_inj (hpV v List.mem_cons_self)] at h
      rw [List.head?_cons, h]
  · rcases List.eq_nil_or_concat p with rfl | ⟨p', v, rfl⟩
    · simp only [List.map_nil] at hch
      exact absurd (eq_of_adj_pair_zero (List.isChain_cons_cons.1 hch).1)
        (copyLabel_ne_pair (by omega)).symm
    · have h := eq_of_adj_pair_one (List.isChain_iff_forall_rel_of_append_cons_cons.1 hch
        (show Nat.pair i 0 :: (p'.concat v).map (copyLabel G i) ++ [Nat.pair i 1] =
          (Nat.pair i 0 :: p'.map (copyLabel G i)) ++ copyLabel G i v :: Nat.pair i 1 :: [] by
          simp)).symm
      rw [copyLabel_inj (hpV v (by simp))] at h
      simp [h]
  · have h := hch.infix ⟨[Nat.pair i 0], [Nat.pair i 1], rfl⟩
    rw [List.isChain_map] at h
    exact (List.IsChain.iff_mem.1 h).imp fun u v huv =>
      (adj_copyLabel_iff (hpV u huv.1) (hpV v huv.2.1)).1 huv.2.2

/-- A path of a copy on two more vertices than `G` has gives a Hamiltonian path of `G`. -/
private theorem mem_HamPath_of_mem_LongPath
    (h : (pendantCopy (G, s, t) i, G.distinctVertices.length + 2) ∈ LongPath) :
    (G, s, t) ∈ HamPath := by
  obtain ⟨q, ⟨hnd, hV, hch⟩, hlen⟩ := mem_LongPath_iff.1 h
  have hfin : q.toFinset = (pendantCopy (G, s, t) i).1.toFinset := by
    refine Finset.eq_of_subset_of_card_le
      (fun w hw => List.mem_toFinset.2 (hV w (List.mem_toFinset.1 hw))) ?_
    rw [card_pendantCopy, List.toFinset_card_of_nodup hnd, hlen]
  have hmem : ∀ w ∈ (pendantCopy (G, s, t) i).1, w ∈ q := fun w hw => by
    rw [← List.mem_toFinset, hfin, List.mem_toFinset]
    exact hw
  have hcov : ∀ v ∈ G.1, copyLabel G i v ∈ q := fun v hv =>
    hmem _ (mem_pendantCopy_fst.2 (Or.inr (Or.inr ⟨v, hv, rfl⟩)))
  have hend0 := head_or_last_of_forall_adj hnd hch (hmem _ pair_zero_mem_pendantCopy)
    (fun hw => eq_of_adj_pair_zero (hw.elim (fun h => h.symm) id))
  have hend1 := head_or_last_of_forall_adj hnd hch (hmem _ pair_one_mem_pendantCopy)
    (fun hw => eq_of_adj_pair_one (hw.elim (fun h => h.symm) id))
  have hab := pair_zero_ne_pair_one i i
  rcases hend0 with h0 | h0 <;> rcases hend1 with h1 | h1
  · exact absurd (Option.some_injective _ (h0.symm.trans h1)) hab
  · exact mem_HamPath_of_path hnd hV hch hcov h0 h1
  · refine mem_HamPath_of_path (List.nodup_reverse.2 hnd)
      (fun w hw => hV w (List.mem_reverse.1 hw))
      (List.isChain_reverse.2 (hch.imp fun _ _ h => h.symm))
      (fun v hv => List.mem_reverse.2 (hcov v hv)) ?_ ?_
    · rw [List.head?_reverse]
      exact h0
    · rw [List.getLast?_reverse]
      exact h1
  · exact absurd (Option.some_injective _ (h0.symm.trans h1)) hab

/-- A Hamiltonian path of `G` from `s` to `t`, with the pendant vertices at its ends, is a path of
the copy on two more vertices than `G` has. -/
private theorem mem_LongPath_of_mem_HamPath (h : (G, s, t) ∈ HamPath) :
    (pendantCopy (G, s, t) i, G.distinctVertices.length + 2) ∈ LongPath := by
  obtain ⟨p, hnd, hcov, hs, ht, hch⟩ := mem_HamPath_iff.1 h
  have hpV : ∀ v ∈ p, v ∈ G.1 := fun v hv => (hcov v).1 hv
  have hlen : p.length = G.distinctVertices.length := by
    rw [Graph.length_distinctVertices, ← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v
    simp only [List.mem_toFinset, hcov]
  have hinj : ∀ u ∈ p, ∀ v ∈ p, copyLabel G i u = copyLabel G i v → u = v :=
    fun u hu _ _ h => (copyLabel_inj (hpV u hu)).1 h
  refine mem_LongPath_iff.2
    ⟨Nat.pair i 0 :: (p.map (copyLabel G i) ++ [Nat.pair i 1]), ⟨?_, ?_, ?_⟩, ?_⟩
  · refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hnd.map_on hinj, List.nodup_singleton _,
      ?_⟩⟩
    · simp only [List.mem_append, List.mem_map, List.mem_singleton, not_or, not_exists, not_and]
      exact ⟨fun v _ h => copyLabel_ne_pair (by omega) h, pair_zero_ne_pair_one i i⟩
    · intro w hw w' hw' h
      obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
      rw [List.mem_singleton.1 hw'] at h
      exact copyLabel_ne_pair (by omega) h
  · intro w hw
    rw [mem_pendantCopy_fst]
    simp only [List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | ⟨v, hv, rfl⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨v, hpV v hv, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · rw [List.isChain_cons, List.isChain_append, List.isChain_map]
    refine ⟨fun y hy => ?_, ⟨(List.IsChain.iff_mem.1 hch).imp fun u v huv =>
      (adj_copyLabel_iff (hpV u huv.1) (hpV v huv.2.1)).2 huv.2.2, List.isChain_singleton _,
      fun x hx y hy => ?_⟩⟩
    · obtain ⟨p', rfl⟩ := List.head?_eq_some_iff.1 hs
      simp only [List.map_cons, List.cons_append, List.head?_cons, Option.mem_def,
        Option.some.injEq] at hy
      subst hy
      rw [Graph.toSimpleGraph_adj]
      exact ⟨(copyLabel_ne_pair (by omega)).symm, Or.inl (mem_pendantCopy_snd.2 (Or.inl rfl))⟩
    · rw [List.getLast?_map, ht] at hx
      simp only [Option.map_some, Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
      subst hx hy
      rw [Graph.toSimpleGraph_adj]
      exact ⟨copyLabel_ne_pair (by omega),
        Or.inr (mem_pendantCopy_snd.2 (Or.inr (Or.inl rfl)))⟩
  · simp only [List.length_cons, List.length_append, List.length_map, List.length_nil, hlen]

/-- **One copy**: the copy of `(G, s, t)` has a path on two more vertices than `G` has exactly
when `G` has a Hamiltonian path from `s` to `t`. -/
private theorem pendantCopy_mem_LongPath_iff :
    (pendantCopy (G, s, t) i, G.distinctVertices.length + 2) ∈ LongPath ↔
      (G, s, t) ∈ HamPath :=
  ⟨mem_HamPath_of_mem_LongPath, mem_LongPath_of_mem_HamPath⟩

end Copy

/-- **Correctness of the cross-composition**: on a nonempty list of instances whose graphs have
equally many distinct vertices, `toLongPath` gives a yes-instance of `LongPath` exactly when some
entry is a yes-instance of `HamPath`. -/
theorem toLongPath_mem_iff {l : List (Graph × ℕ × ℕ)} (hl : l ≠ [])
    (hkey : ∀ x ∈ l, ∀ y ∈ l, x.1.distinctVertices.length = y.1.distinctVertices.length) :
    toLongPath l ∈ LongPath ↔ ∃ x ∈ l, x ∈ HamPath := by
  obtain ⟨y, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  change (pendantUnion (y :: l'), y.1.distinctVertices.length + 1 + 1) ∈ LongPath ↔ _
  rw [pendantUnion_mem_LongPath_iff]
  constructor
  · rintro ⟨⟨G, s, t⟩, j, hx, hmem⟩
    have hxl := List.mem_of_getElem? hx
    refine ⟨(G, s, t), hxl, ?_⟩
    rw [hkey y List.mem_cons_self _ hxl] at hmem
    exact pendantCopy_mem_LongPath_iff.1 hmem
  · rintro ⟨⟨G, s, t⟩, hxl, hx⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hxl
    refine ⟨(G, s, t), j, hj, ?_⟩
    rw [hkey y List.mem_cons_self _ hxl]
    exact pendantCopy_mem_LongPath_iff.2 hx

end HamPath

/-! ### Kernelization lower bound -/

/-- **`HamPath` OR-cross-composes into k-Path** parameterized by the path length, with respect to
the polynomial equivalence relation of having equally many distinct vertices: `toLongPath` takes
the disjoint union of the pendant copies, whose target is two more than the common number of
distinct vertices. -/
theorem HamPath.orCrossComposes_LongPath :
    ORCrossComposes (encPair encGraph (encPair encNat encNat)) HamPath (encPair encGraph encNat)
      Prod.snd LongPath := by
  have hkey : ComputableInPolyTime (fun x : Graph × ℕ × ℕ => x.1.distinctVertices.length)
      (encPair encGraph (encPair encNat encNat)) encUnary :=
    (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp (by fun_prop))
  refine ⟨_, HamPath.toLongPath, fun n => n + 2, IsPolyEquivalence.of_key hkey, by fun_prop,
    HamPath.computableInPolyTime_toLongPath, fun l hl hrel => ?_, fun n l hl _ hlen => ?_⟩
  · exact HamPath.toLongPath_mem_iff hl fun x hx y hy => of_decide_eq_true (hrel x hx y hy)
  · obtain ⟨y, l', rfl⟩ := List.exists_cons_of_ne_nil hl
    have h1 := Graph.length_distinctVertices_le y.1
    have h2 := length_le_encPair_left encGraph (encPair encNat encNat) y
    have h3 := hlen y List.mem_cons_self
    change y.1.distinctVertices.length + 2 ≤ n + Nat.log 2 (l'.length + 1) + 2
    omega

/-- **k-Path is `NP`-hard**, by the cross-composition of `HamPath` on one instance: a graph has a
Hamiltonian path from `s` to `t` exactly when its pendant copy has a path on two more vertices than
the graph has. -/
theorem LongPath_npHard : NPHard (encPair encGraph encNat) LongPath := by
  refine HamPath_npHard.trans ⟨fun x => HamPath.toLongPath [x],
    HamPath.computableInPolyTime_toLongPath.comp (cons' id' (const [])), fun x => ?_⟩
  rw [HamPath.toLongPath_mem_iff (List.cons_ne_nil x []) (by simp), List.exists_mem_cons_iff]
  simp

/-- **k-Path has no polynomial kernel unless `coNP ⊆ NP/poly`**, attributed to
[BodlaenderDowneyFellowsHermelin2009] by [BodlaenderJansenKratsch2014, Section 1] and derived
here from [BodlaenderJansenKratsch2014, Corollary 2] (its `NP ⊆ coNP/poly` conclusion), with
`coNP ⊄ NP/poly` for some encoding as an explicit hypothesis. The target `k` is encoded in
binary. -/
theorem not_hasPolyKernel_LongPath {δ : Type} {encC : δ ↪ List Bool}
    (hcoNP : ¬ coNP encC ⊆ NPPoly encC) :
    ¬ HasPolyKernel (encPair encGraph encNat) Prod.snd LongPath :=
  not_hasPolyKernel_of_orCrossComposes HamPath_npHard HamPath.orCrossComposes_LongPath hcoNP

/-- **k-Path has no polynomial compression unless `coNP ⊆ NP/poly`**
[BodlaenderJansenKratsch2014, Corollary 2] (its `NP ⊆ coNP/poly` conclusion), with
`coNP ⊄ NP/poly` for some encoding as an explicit hypothesis. A compression may run in time
polynomial in the encoded length plus `k`, the time bound of
[BodlaenderJansenKratsch2014, Definition 1], so this also rules out kernelizations of these
instances with that time bound. -/
theorem not_hasPolyCompression_LongPath {δ : Type} {encC : δ ↪ List Bool}
    (hcoNP : ¬ coNP encC ⊆ NPPoly encC) :
    ¬ HasPolyCompression (encPair encGraph encNat) Prod.snd LongPath :=
  not_hasPolyCompression_of_orCrossComposes HamPath_npHard HamPath.orCrossComposes_LongPath hcoNP

/-- A polynomial compression of k-Path gives `coNP ⊆ NP/poly`, for every encoding of instances
[BodlaenderJansenKratsch2014, Corollary 2]. -/
theorem coNP_subset_NPPoly_of_hasPolyCompression_LongPath
    (h : HasPolyCompression (encPair encGraph encNat) Prod.snd LongPath) {δ : Type}
    (encC : δ ↪ List Bool) : coNP encC ⊆ NPPoly encC :=
  coNP_subset_NPPoly_of_orCrossComposes HamPath_npHard HamPath.orCrossComposes_LongPath h encC

end Cslib.Complexity
