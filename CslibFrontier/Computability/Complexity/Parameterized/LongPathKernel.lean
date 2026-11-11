/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.CrossComposition
public import CslibFrontier.Computability.Complexity.Problems.LongPath.Hardness
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Undirected
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# k-Path has no polynomial kernel unless `coNP ⊆ NP/poly`

k-Path (`Cslib.Complexity.LongPath`), parameterized by the number `k` of vertices of the path,
has no polynomial kernel and no polynomial compression unless `coNP ⊆ NP/poly`. Bodlaender,
Jansen and Kratsch [BodlaenderJansenKratsch2014, Section 1] attribute the kernel lower bound to
Bodlaender, Downey, Fellows and Hermelin [BodlaenderDowneyFellowsHermelin2009]; the theorem number
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
becomes its pendant copy (`Cslib.Complexity.HamPath.pendantCopy`, from
`CslibFrontier.Computability.Complexity.Problems.LongPath.Hardness`, where the same gadget gives
`Cslib.Complexity.LongPath_npHard`): every declared vertex `v` is relabeled `Nat.pair i (p + 2)`,
for `p` the position of the first occurrence of `v`, and two pendant vertices `Nat.pair i 0` and
`Nat.pair i 1` are attached to the copies of `s` and `t`. The output
(`Cslib.Complexity.HamPath.toLongPath`) is the disjoint union of the copies, with target `N + 2`
for `N` the common number of distinct vertices. A path on `N + 2` vertices stays in one copy, as
edges do not join copies, so the union has such a path exactly when some copy has one, that is,
when some entry has a Hamiltonian path (`Cslib.Complexity.HamPath.toLongPath_mem_iff`). The
target is at most two more than the length of an encoded entry, independent of the number of
entries.

Instances are encoded as `encPair encGraph encNat`, with the target in binary, as for
`Cslib.Complexity.ColorfulPath_mem_FPT`; [BodlaenderJansenKratsch2014, Section 2] writes the
parameter in unary. A compression (`Cslib.Complexity.HasPolyCompression`) runs in time polynomial
in the encoded length plus the parameter, which covers the time bound of the source's
kernelizations and compressions [BodlaenderJansenKratsch2014, Definitions 1 and 2], while a
kernelization (`Cslib.Complexity.HasPolyKernel`) must run in time polynomial in the encoded length
alone.

## Main definitions

* `Cslib.Complexity.HamPath.pendantUnion`: the disjoint union of the pendant copies of a list.
* `Cslib.Complexity.HamPath.toLongPath`: the cross-composition of `HamPath` into k-Path.

## Main results

* `Cslib.Complexity.HamPath.toLongPath_mem_iff`: correctness on lists of related instances.
* `Cslib.Complexity.HamPath.orCrossComposes_LongPath`: `HamPath` OR-cross-composes into k-Path.
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

/-- The disjoint union of the pendant copies of a list of instances, copy `i` for entry `i`. -/
def pendantUnion (l : List (Graph × ℕ × ℕ)) : Graph :=
  (l.zipIdx.flatMap fun p => (pendantCopy p.1 p.2).1,
    l.zipIdx.flatMap fun p => (pendantCopy p.1 p.2).2)

/-- The cross-composition of `HamPath` into `LongPath`: the disjoint union of the pendant copies,
with target two more than the number of distinct vertices of the first entry. -/
def toLongPath (l : List (Graph × ℕ × ℕ)) : Graph × ℕ :=
  (pendantUnion l, (l.headD default).1.distinctVertices.length + 2)

private abbrev encInst : Graph × ℕ × ℕ ↪ List Bool := encPair encGraph (encPair encNat encNat)

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
