/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Hamiltonian
public import Complexity.Computability.Complexity.Problems.LongPath
public import Complexity.Computability.Complexity.Reduction
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# k-Path is `NP`-complete

k-Path (`Cslib.Complexity.LongPath`) [CyganEtAl2015, Section 5.2] is `NP`-complete
(`Cslib.Complexity.LongPath_npComplete`), with the target `k` in binary.

**Membership.** A certificate is an ordering of the declared vertices, read by
`Cslib.Complexity.Graph.verifyOrdering` as for `Cslib.Complexity.HamPath`. The verifier
(`Cslib.Complexity.LongPath.verifier`) checks that the first `k` entries are `k` vertices with
consecutive ones adjacent. A path on `k` vertices extends to an ordering by appending the other
declared vertices. The first `k` entries, for `k` in binary, are the first `min (length) k`
entries, a count in unary, so the verifier is polynomial-time.

**Hardness.** The pendant copy (`Cslib.Complexity.HamPath.pendantCopy`) of an instance `(G, s, t)`
of undirected Hamiltonian path relabels every declared vertex `v` as `Nat.pair i (p + 2)`
(`Cslib.Complexity.HamPath.copyLabel`), for `p` the position of the first occurrence of `v`, and
attaches two pendant vertices `Nat.pair i 0` and `Nat.pair i 1` to the copies of `s` and `t`. A
path on `N + 2` vertices of the copy, for `N` the number of distinct vertices of `G`, visits every
vertex of the copy; its ends are the pendant vertices, and removing them leaves a Hamiltonian path
from `s` to `t`. Conversely, the pendant vertices extend a Hamiltonian path
(`Cslib.Complexity.HamPath.pendantCopy_mem_LongPath_iff`). With `i = 0` this is a
polynomial-time reduction, so k-Path is `NP`-hard (`Cslib.Complexity.LongPath_npHard`). The labels
use positions, which are bounded by the encoded length, because the library's pairing rule
`Turing.MultiTapeTM.ComputableInPolyTime.unary_pair` takes unary arguments and a vertex name,
written in binary, can be exponentially larger than its encoding. The copy index `i` is used by
the disjoint union of copies in `Complexity.Computability.Complexity.Parameterized.LongPathKernel`,
the OR-cross-composition behind the kernel lower bound for k-Path. The gadget was written for this
library; it is not taken from a source, and no novelty is claimed.

## Main definitions

* `Cslib.Complexity.LongPath.verifier`: the verifier for k-Path.
* `Cslib.Complexity.HamPath.copyLabel`: the label of a vertex in copy `i`.
* `Cslib.Complexity.HamPath.pendantCopy`: copy `i` of a graph with the two pendant vertices.

## Main results

* `Cslib.Complexity.LongPath.mem_NP`: k-Path belongs to `NP`.
* `Cslib.Complexity.HamPath.pendantCopy_mem_LongPath_iff`: correctness of the pendant copy.
* `Cslib.Complexity.LongPath_npHard`, `Cslib.Complexity.LongPath_npComplete`: k-Path is `NP`-hard
  and `NP`-complete.

## References

* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

namespace LongPath

/-- The verifier for `LongPath`: decode a list of vertices from the certificate
(`Graph.decodeVertexList`), check that it lists every declared vertex exactly once, and check that
its first `k` entries are `k` vertices with consecutive ones adjacent. -/
def verifier : (Graph × ℕ) × List Bool → Bool :=
  Graph.verifyOrdering (fun (G, _) => G.1) fun (G, k) p =>
    decide ((p.take k).length = k) && Graph.chainBool G.adjBool (p.take k)

/-- A path on `k` vertices extends to an enumeration of the declared vertices. -/
private theorem exists_enum_of_isVertexPath {G : Graph} {q : List ℕ} (hq : G.IsVertexPath q) :
    ∃ p : List ℕ, p.Nodup ∧ (∀ v, v ∈ p ↔ v ∈ G.1) ∧ p.take q.length = q := by
  refine ⟨q ++ (G.1.dedup.filter fun v => v ∉ q), ?_, fun v => ?_, List.take_left⟩
  · refine List.nodup_append.2 ⟨hq.1, (List.nodup_dedup _).filter _, fun a ha b hb hab => ?_⟩
    subst hab
    exact of_decide_eq_true (List.mem_filter.1 hb).2 ha
  · simp only [List.mem_append, List.mem_filter, List.mem_dedup, decide_eq_true_eq]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact hq.2.1 v h
      · exact h
    · intro h
      by_cases hv : v ∈ q
      · exact Or.inl hv
      · exact Or.inr ⟨h, hv⟩

/-- `LongPath.verifier` verifies `LongPath` with certificates of length `n ^ 2` for instances of
encoded length `n`: a path on `k` vertices extends to an ordering of the declared vertices, and the
first `k` entries of such an ordering form a path when there are `k` of them and consecutive ones
are adjacent. -/
theorem isVerifier :
    IsVerifier (encPair encGraph encNat) (Polynomial.X ^ 2) verifier LongPath := by
  have h := Graph.isVerifier_verifyOrdering (enc := encPair encGraph encNat)
    (V := fun x : Graph × ℕ => x.1.1)
    (check := fun x p =>
      decide ((p.take x.2).length = x.2) && Graph.chainBool x.1.adjBool (p.take x.2))
    (P := fun x p => (p.take x.2).length = x.2 ∧ (p.take x.2).IsChain x.1.toSimpleGraph.Adj)
    (fun x => (Graph.length_vertices_le_encGraph x.1).trans (length_le_encPair_left _ _ _))
    (fun x p => by
      simp only [Bool.and_eq_true, decide_eq_true_eq,
        Graph.chainBool_eq_true_iff (Graph.adjBool_eq_true_iff x.1)])
  intro x
  refine Iff.trans ?_ (h x)
  obtain ⟨G, k⟩ := x
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨p, hnd, hmem, htake⟩ := exists_enum_of_isVertexPath hq
    exact ⟨p, hnd, hmem, by rw [htake], by rw [htake]; exact hq.2.2⟩
  · rintro ⟨p, hnd, hmem, hk, hch⟩
    exact ⟨p.take k, ⟨(List.take_sublist _ _).nodup hnd,
      fun v hv => (hmem v).1 (List.mem_of_mem_take hv), hch⟩, hk⟩

/-- The `LongPath` verifier is polynomial-time: the first `k` entries, for `k` in binary, are the
first `min (length) k` entries, a count in unary. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair (encPair encGraph encNat) encBits) encBool := by
  refine Graph.computableInPolyTime_verifyOrdering (by unfold encGraph; fun_prop) ?_
  have htake : ComputableInPolyTime (fun q : (Graph × ℕ) × List ℕ => q.2.take q.1.2)
      (encPair (encPair encGraph encNat) (encList encNat)) (encList encNat) := by
    have hmin : ComputableInPolyTime
        (fun q : (Graph × ℕ) × List ℕ => min q.2.length q.1.2)
        (encPair (encPair encGraph encNat) (encList encNat)) encUnary :=
      binary_min_unary' ((length_list encNat).comp (snd _ _)) (by fun_prop)
    have h := (ComputableTidilyInPolyTime.takeUnary encNat).computableInPolyTime.comp
      ((snd _ _).prod hmin)
    convert h using 2 with q
    exact List.take_eq_take_iff.2 (by dsimp only; omega)
  exact bool_and' (((length_list_binary encNat).comp htake).decide_eq' (by fun_prop))
    (Graph.computableInPolyTime_chainBool (by fun_prop) htake)

/-- **k-Path belongs to `NP`.** -/
theorem mem_NP : LongPath ∈ NP (encPair encGraph encNat) :=
  ⟨_, verifier, computableInPolyTime_verifier, isVerifier⟩

end LongPath

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
theorem computableInPolyTime_pendantCopy :
    ComputableInPolyTime (fun p : (Graph × ℕ × ℕ) × ℕ => pendantCopy p.1 p.2)
      (encPair (encPair encGraph (encPair encNat encNat)) encUnary) encGraph := by
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

/-- Every vertex of copy `i` is a pair with first component `i`. -/
theorem unpair_of_mem_pendantCopy_fst {x : Graph × ℕ × ℕ} {i w : ℕ}
    (h : w ∈ (pendantCopy x i).1) : (Nat.unpair w).1 = i := by
  rcases mem_pendantCopy_fst.1 h with rfl | rfl | ⟨v, -, rfl⟩
  · simp only [Nat.unpair_pair]
  · simp only [Nat.unpair_pair]
  · exact unpair_copyLabel_fst _ _ _

/-- Both ends of every edge of copy `i` are pairs with first component `i`. -/
theorem unpair_of_mem_pendantCopy_snd {x : Graph × ℕ × ℕ} {i : ℕ} {e : ℕ × ℕ}
    (h : e ∈ (pendantCopy x i).2) : (Nat.unpair e.1).1 = i ∧ (Nat.unpair e.2).1 = i := by
  rcases mem_pendantCopy_snd.1 h with rfl | rfl | ⟨d, -, rfl⟩
  · exact ⟨by simp only [Nat.unpair_pair], unpair_copyLabel_fst _ _ _⟩
  · exact ⟨by simp only [Nat.unpair_pair], unpair_copyLabel_fst _ _ _⟩
  · exact ⟨unpair_copyLabel_fst _ _ _, unpair_copyLabel_fst _ _ _⟩

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
theorem pendantCopy_mem_LongPath_iff :
    (pendantCopy (G, s, t) i, G.distinctVertices.length + 2) ∈ LongPath ↔
      (G, s, t) ∈ HamPath :=
  ⟨mem_HamPath_of_mem_LongPath, mem_LongPath_of_mem_HamPath⟩

end Copy

end HamPath

/-- **k-Path is `NP`-hard**, by the pendant copy of an instance of `HamPath`: a graph has a
Hamiltonian path from `s` to `t` exactly when its pendant copy has a path on two more vertices than
the graph has. -/
theorem LongPath_npHard : NPHard (encPair encGraph encNat) LongPath := by
  have hk : ComputableInPolyTime (fun x : Graph × ℕ × ℕ => x.1.distinctVertices.length + 2)
      (encPair encGraph (encPair encNat encNat)) encNat := by
    have hn : ComputableInPolyTime (fun x : Graph × ℕ × ℕ => x.1.distinctVertices.length)
        (encPair encGraph (encPair encNat encNat)) encUnary :=
      (length_list encNat).comp (Graph.computableInPolyTime_distinctVertices.comp (by fun_prop))
    exact unary_to_binary.comp (by fun_prop)
  refine HamPath_npHard.trans ⟨fun x => (HamPath.pendantCopy x 0, x.1.distinctVertices.length + 2),
    (HamPath.computableInPolyTime_pendantCopy.comp (id'.prod (const 0))).prod hk, fun x => ?_⟩
  exact HamPath.pendantCopy_mem_LongPath_iff.symm

/-- **k-Path is `NP`-complete**, with the target `k` in binary. -/
theorem LongPath_npComplete : NPComplete (encPair encGraph encNat) LongPath :=
  ⟨LongPath.mem_NP, LongPath_npHard⟩

end Cslib.Complexity
