/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.BipartitePerfectMatching
public import Complexity.Algorithms.Lean.MaxFlow.BipartiteMatching
public import Complexity.Computability.Complexity.Classes.P
public import Complexity.Tactic.PolyTime
import Complexity.Algorithms.Lean.MaxFlow.AugmentingPath
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt

/-!
# Bipartite perfect matching is in P

A multi-tape Turing machine decides `Cslib.Complexity.BipartitePerfectMatching` in polynomial
time on the plain bit encoding `encBits`
(`Cslib.Complexity.BipartitePerfectMatching.mem_P`). The decider
(`Cslib.Complexity.BipartitePerfectMatching.decider`) takes `n = ⌊√|w|⌋`, computes a maximum
matching of the `n × n` adjacency matrix read from `w`, and accepts when `n * n = |w|` and the
matching covers every left vertex.

The maximum matching (`Cslib.Complexity.BipartitePerfectMatching.maximumMatching`) is built by
augmenting paths, as lists of pairs of natural numbers. One round labels the left vertices by
alternating paths: the free left vertices get the empty path, and in each of `n` synchronous passes
an unlabelled left vertex `u` matched to `v` gets the path of a labelled neighbour `u'` of `v`
extended by the edge `(u', v)`. If some labelled vertex has a free neighbour, the round augments
along the first such path, growing the matching by one edge. Otherwise the labelled vertices are the
breadth-first alternating layers and no layer reaches a free right vertex, so the counting lemma of
the Hopcroft–Karp development (`Cslib.Algorithms.Lean.MaxFlow.card_mul_le_of_noShortAug`, which
replaces the alternating-cycle argument in Berge's theorem [Berge1957]) shows the matching is
maximum. A matching has at most `n` edges, so `n` rounds from the empty matching reach a maximum
matching. This is the augmenting-path method for maximum bipartite matching ([CLRS2009],
Section 26.3) with one augmentation per breadth-first round, not the `O(√n)`-phase schedule of
Hopcroft and Karp [HopcroftKarp1973], which the polynomial bound does not need.

Labels and matchings hold at most `n + 1` edges with endpoints below `n`, written in unary, so every
state is polynomially bounded and both loops are polynomial-time by the iteration rules for plain
computability.

## Main definitions

* `Cslib.Complexity.BipartitePerfectMatching.maximumMatching`: a maximum matching of the graph of a
  word, as a list of edges.
* `Cslib.Complexity.BipartitePerfectMatching.decider`: the decider.
* `Cslib.Complexity.BipartitePerfectMatching.edgeSet`: the edges of `K_{n,n}` listed by a list of
  pairs.
* `Cslib.Complexity.BipartitePerfectMatching.encUnaryEdges`: the encoding of an edge list.

## Main results

* `Cslib.Complexity.BipartitePerfectMatching.isMaxMatching_maximumMatching`: the algorithm computes
  a maximum matching.
* `Cslib.Complexity.BipartitePerfectMatching.decider_eq_true_iff`: the decider decides the
  language.
* `Cslib.Complexity.BipartitePerfectMatching.computableInPolyTime_maximumMatching`,
  `Cslib.Complexity.BipartitePerfectMatching.computableInPolyTime_decider`: both are
  polynomial-time.
* `Cslib.Complexity.BipartitePerfectMatching.mem_P`: bipartite perfect matching is in `P`.

## References

* [C. Berge, *Two Theorems in Graph Theory*][Berge1957]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein,
  *Introduction to Algorithms*][CLRS2009]
* [J. E. Hopcroft, R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
-/

public section

namespace Cslib.Complexity.BipartitePerfectMatching

open Turing.MultiTapeTM

/-! ### The algorithm -/

/-- A labelling of the left vertices `0, …, n - 1`: entry `u` is `some q` when `u` has been reached
by the alternating path whose non-matching edges are `q`, and `none` while it is unreached. -/
abbrev Labelling := List (Option (List (ℕ × ℕ)))

/-- The candidate labels of the left vertex `u`: for each `v` with `(u, v) ∈ M` and each labelled
`u'` adjacent to `v`, the label of `u'` extended by the edge `(u', v)`. -/
@[expose] def labelCandidates (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) (lab : Labelling)
    (u : ℕ) : List (List (ℕ × ℕ)) :=
  (List.range n).flatMap fun v =>
    if decide ((u, v) ∈ M) then
      ((List.range n).filter fun u' => (lab.getD u' none).isSome && adj w n u' v).map
        fun u' => (lab.getD u' none).getD [] ++ [(u', v)]
    else []

/-- One synchronous labelling pass: a labelled vertex keeps its label, and an unlabelled one takes
its first candidate label, if any. -/
@[expose] def labelStep (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) (lab : Labelling) :
    Labelling :=
  (List.range n).map fun u =>
    if (lab.getD u none).isSome then lab.getD u none else (labelCandidates w n M lab u).head?

/-- The initial labelling: the free left vertices get the empty path. -/
@[expose] def initialLabelling (n : ℕ) (M : List (ℕ × ℕ)) : Labelling :=
  (List.range n).map fun u => if M.any (fun e => decide (e.1 = u)) then none else some []

/-- The labelling after `n` passes. -/
@[expose] def labelling (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) : Labelling :=
  (labelStep w n M)^[n] (initialLabelling n M)

/-- The augmenting paths read from a labelling: for each labelled `u` adjacent to a free right
vertex `v`, the label of `u` extended by the edge `(u, v)`. -/
@[expose] def augmentingPaths (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) (lab : Labelling) :
    List (List (ℕ × ℕ)) :=
  (List.range n).flatMap fun u =>
    ((List.range n).filter fun v =>
        (lab.getD u none).isSome && adj w n u v && !(M.any fun e => decide (e.2 = v))).map
      fun v => (lab.getD u none).getD [] ++ [(u, v)]

/-- Augment `M` along the non-matching edges `p` of a path: add `p` and drop the edges of `M` at
the left vertices of `p`. -/
@[expose] def augmentAlong (M p : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  p ++ M.filter fun e => !(p.any fun f => decide (f.1 = e.1))

/-- One augmentation round: augment along the first augmenting path found, if any. -/
@[expose] def augmentStep (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  augmentAlong M ((augmentingPaths w n M (labelling w n M)).headD [])

/-- A maximum matching of the graph `graph w n`, by `n` augmentation rounds from the empty
matching (`isMaxMatching_maximumMatching`). -/
@[expose] def maximumMatching (w : List Bool) (n : ℕ) : List (ℕ × ℕ) := (augmentStep w n)^[n] []

/-- Acceptance at side length `n`: `n * n` is the length of `w`, and `M` covers every left
vertex. -/
@[expose] def acceptsAt (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) : Bool :=
  decide (n * n = w.length) && (List.range n).all fun u => M.any fun e => decide (e.1 = u)

/-- The decider at side length `n`. -/
@[expose] def deciderAt (w : List Bool) (n : ℕ) : Bool := acceptsAt w n (maximumMatching w n)

/-- **The decider for bipartite perfect matching**: at side length `n = ⌊√|w|⌋`, accept when
`n * n = |w|` and a maximum matching of `graph w n` covers every left vertex. -/
@[expose] def decider (w : List Bool) : Bool := deciderAt w w.length.sqrt

/-! ### Polynomial time -/

/-- An edge list, as a list of pairs of unary natural numbers. -/
abbrev encUnaryEdges : List (ℕ × ℕ) ↪ List Bool := encList (encPair encUnary encUnary)

/-- An edge, as a pair of unary natural numbers. -/
private abbrev encEdge : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary

/-- A labelling: a list of optional edge lists. -/
private abbrev encLabelling : Labelling ↪ List Bool := encList (encOption (encList encEdge))

/-- The input of a round: the word, the unary side length and the matching. -/
private abbrev encRound : List Bool × ℕ × List (ℕ × ℕ) ↪ List Bool :=
  encPair encBits (encPair encUnary (encList encEdge))

private theorem computableInPolyTime_labelStep : ComputableInPolyTime
    (fun p : (List Bool × ℕ × List (ℕ × ℕ)) × Labelling => labelStep p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair encRound encLabelling) encLabelling := by
  simp only [labelStep, labelCandidates, adj]
  fun_prop

private theorem computableInPolyTime_initialLabelling : ComputableInPolyTime
    (fun x : List Bool × ℕ × List (ℕ × ℕ) => initialLabelling x.2.1 x.2.2) encRound
      encLabelling := by
  simp only [initialLabelling]
  fun_prop

private theorem computableInPolyTime_augmentingPaths : ComputableInPolyTime
    (fun p : (List Bool × ℕ × List (ℕ × ℕ)) × Labelling =>
      augmentingPaths p.1.1 p.1.2.1 p.1.2.2 p.2)
    (encPair encRound encLabelling) (encList (encList encEdge)) := by
  simp only [augmentingPaths, adj]
  fun_prop

private theorem computableInPolyTime_augmentAlong : ComputableInPolyTime
    (fun p : List (ℕ × ℕ) × List (ℕ × ℕ) => augmentAlong p.1 p.2)
    (encPair (encList encEdge) (encList encEdge)) (encList encEdge) := by
  simp only [augmentAlong]
  fun_prop

/-- A labelling after `i` passes: `n` entries, each a path of at most `i` edges with endpoints
below `n`. -/
private def LabellingSize (n i : ℕ) (lab : Labelling) : Prop :=
  lab.length = n ∧ ∀ o ∈ lab, ∀ q ∈ o, q.length ≤ i ∧ ∀ e ∈ q, e.1 < n ∧ e.2 < n

private theorem LabellingSize.getD {n i : ℕ} {lab : Labelling} (h : LabellingSize n i lab)
    (u : ℕ) :
    ((lab.getD u none).getD []).length ≤ i ∧
      ∀ e ∈ (lab.getD u none).getD [], e.1 < n ∧ e.2 < n := by
  rcases hlt : lab.getD u none with _ | q
  · simp
  · have hmem : some q ∈ lab := by
      rw [List.getD_eq_getElem?_getD] at hlt
      rcases hu : lab[u]? with _ | o
      · simp [hu] at hlt
      · simp only [hu, Option.getD_some] at hlt
        subst hlt
        exact List.mem_of_getElem? hu
    exact h.2 _ hmem q rfl

private theorem labellingSize_initialLabelling (n : ℕ) (M : List (ℕ × ℕ)) :
    LabellingSize n 0 (initialLabelling n M) := by
  refine ⟨by simp [initialLabelling], fun o ho q hq => ?_⟩
  simp only [initialLabelling, List.mem_map, List.mem_range] at ho
  obtain ⟨u, _, rfl⟩ := ho
  split at hq
  · simp at hq
  · simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    simp

private theorem labellingSize_labelStep {w : List Bool} {n i : ℕ} {M : List (ℕ × ℕ)}
    {lab : Labelling} (h : LabellingSize n i lab) :
    LabellingSize n (i + 1) (labelStep w n M lab) := by
  refine ⟨by simp [labelStep], fun o ho q hq => ?_⟩
  simp only [labelStep, List.mem_map, List.mem_range] at ho
  obtain ⟨u, hu, rfl⟩ := ho
  split at hq
  · have := h.getD u
    rw [Option.mem_def] at hq
    rw [hq, Option.getD_some] at this
    exact ⟨by omega, this.2⟩
  · have hq' := List.mem_of_mem_head? hq
    simp only [labelCandidates, List.mem_flatMap, List.mem_range] at hq'
    obtain ⟨v, hv, hq'⟩ := hq'
    split at hq'
    · simp only [List.mem_map, List.mem_filter, List.mem_range] at hq'
      obtain ⟨u', ⟨hu', _⟩, rfl⟩ := hq'
      have := h.getD u'
      refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun e he => ?_⟩
      rcases List.mem_append.mp he with he | he
      · exact this.2 e he
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨hu', hv⟩
    · simp at hq'

private theorem labellingSize_iterate (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) (i : ℕ) :
    LabellingSize n i ((labelStep w n M)^[i] (initialLabelling n M)) := by
  induction i with
  | zero => exact labellingSize_initialLabelling n M
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact labellingSize_labelStep ih

private theorem length_encEdge_le {n : ℕ} {e : ℕ × ℕ} (h : e.1 < n ∧ e.2 < n) :
    (encEdge e).length ≤ 3 * n := by
  simp only [encEdge, length_encPair, encUnary_apply, List.length_replicate]
  omega

private theorem length_encPath_le {n i : ℕ} {q : List (ℕ × ℕ)} (hq : q.length ≤ i)
    (he : ∀ e ∈ q, e.1 < n ∧ e.2 < n) :
    (encList encEdge q).length ≤ i * (6 * n + 1) := by
  calc (encList encEdge q).length ≤ q.length * (2 * (3 * n) + 1) :=
        length_encList_le encEdge q fun e h => length_encEdge_le (he e h)
    _ ≤ i * (6 * n + 1) := Nat.mul_le_mul hq (by omega)

private theorem length_encLabelling_le {n i : ℕ} {lab : Labelling} (h : LabellingSize n i lab) :
    (encLabelling lab).length ≤ n * (2 * (1 + i * (6 * n + 1)) + 1) := by
  have := length_encList_le (encOption (encList encEdge)) lab (b := 1 + i * (6 * n + 1))
    fun o ho => by
      rcases o with _ | q
      · simp
      · have := h.2 _ ho q rfl
        simp only [encOption_some, List.length_cons]
        have := length_encPath_le this.1 this.2
        omega
  rwa [h.1] at this

private theorem le_length_encRound (x : List Bool × ℕ × List (ℕ × ℕ)) :
    x.2.1 ≤ (encRound x).length := by
  have h1 : (encPair encUnary (encList encEdge) x.2).length ≤ (encRound x).length :=
    length_le_encPair_right encBits (encPair encUnary (encList encEdge)) x
  have h2 := length_le_encPair_left encUnary (encList encEdge) x.2
  simp only [encUnary_apply, List.length_replicate] at h2
  omega

private theorem labelling_size_le_cubic {n i N : ℕ} (hi : i ≤ n) (hn : n ≤ N) :
    n * (2 * (1 + i * (6 * n + 1)) + 1) ≤ 15 * (N + 1) ^ 3 := by
  have h1 : n * (2 * (1 + i * (6 * n + 1)) + 1) ≤ N * (2 * (1 + N * (6 * N + 1)) + 1) := by
    gcongr
    · omega
  refine h1.trans ?_
  ring_nf
  omega

private theorem computableInPolyTime_labelling : ComputableInPolyTime
    (fun x : List Bool × ℕ × List (ℕ × ℕ) => labelling x.1 x.2.1 x.2.2) encRound
      encLabelling := by
  have hcount : ComputableInPolyTime (fun x : List Bool × ℕ × List (ℕ × ℕ) => x.2.1)
      encRound encUnary := by fun_prop
  refine ComputableInPolyTime.iterateWith ComputableInPolyTime.id' hcount
    computableInPolyTime_initialLabelling computableInPolyTime_labelStep
    (bound := fun x => 15 * ((encRound x).length + 1) ^ 3)
    (PolyBounded.of_forall_le 15 3 fun _ => le_rfl) fun x i hi => ?_
  exact (length_encLabelling_le (labellingSize_iterate x.1 x.2.1 x.2.2 i)).trans
    (labelling_size_le_cubic hi (le_length_encRound x))

private theorem augmentStep_path_size (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) :
    ((augmentingPaths w n M (labelling w n M)).headD []).length ≤ n + 1 ∧
      ∀ e ∈ (augmentingPaths w n M (labelling w n M)).headD [], e.1 < n ∧ e.2 < n := by
  have hlab := labellingSize_iterate w n M n
  generalize hP : augmentingPaths w n M (labelling w n M) = P
  rcases P with _ | ⟨p, P⟩
  · simp
  · have hp : p ∈ augmentingPaths w n M (labelling w n M) := by
      rw [hP]
      exact List.mem_cons_self
    simp only [augmentingPaths, List.mem_flatMap, List.mem_range, List.mem_map,
      List.mem_filter] at hp
    obtain ⟨u, hu, v, ⟨hv, _⟩, rfl⟩ := hp
    have := hlab.getD u
    refine ⟨by rw [List.headD_cons, List.length_append, List.length_singleton]; exact
      Nat.add_le_add_right this.1 1, fun e he => ?_⟩
    rw [List.headD_cons] at he
    rcases List.mem_append.mp he with he | he
    · exact this.2 e he
    · rw [List.mem_singleton] at he
      subst he
      exact ⟨hu, hv⟩

private theorem computableInPolyTime_augmentStep : ComputableInPolyTime
    (fun x : List Bool × ℕ × List (ℕ × ℕ) => augmentStep x.1 x.2.1 x.2.2) encRound
      (encList encEdge) := by
  have hP : ComputableInPolyTime
      (fun x : List Bool × ℕ × List (ℕ × ℕ) =>
        augmentingPaths x.1 x.2.1 x.2.2 (labelling x.1 x.2.1 x.2.2))
      encRound (encList (encList encEdge)) :=
    computableInPolyTime_augmentingPaths.comp'
      (ComputableInPolyTime.id'.prod computableInPolyTime_labelling)
  have hp : ComputableInPolyTime
      (fun x : List Bool × ℕ × List (ℕ × ℕ) =>
        (augmentingPaths x.1 x.2.1 x.2.2 (labelling x.1 x.2.1 x.2.2)).headD [])
      encRound (encList encEdge) := (ComputableInPolyTime.headD []).comp' hP
  have hM : ComputableInPolyTime (fun x : List Bool × ℕ × List (ℕ × ℕ) => x.2.2)
      encRound (encList encEdge) := by fun_prop
  exact computableInPolyTime_augmentAlong.comp' (hM.prod hp)

/-- **A maximum bipartite matching is polynomial-time computable** from the word and the unary
side length, with the matching written as a list of unary pairs. -/
theorem computableInPolyTime_maximumMatching :
    ComputableInPolyTime (fun x : List Bool × ℕ => maximumMatching x.1 x.2)
      (encPair encBits encUnary) encUnaryEdges := by
  have hstep : ComputableInPolyTime
      (fun p : (List Bool × ℕ) × List (ℕ × ℕ) => augmentStep p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encUnary) (encList encEdge)) (encList encEdge) := by
    have hre : ComputableInPolyTime
        (fun p : (List Bool × ℕ) × List (ℕ × ℕ) => (p.1.1, p.1.2, p.2))
        (encPair (encPair encBits encUnary) (encList encEdge)) encRound := by fun_prop
    -- `have` then `exact`: elaborating the composite against the goal directly unfolds
    -- `augmentStep` and times out.
    have h := computableInPolyTime_augmentStep.comp' hre
    exact h
  refine ComputableInPolyTime.iterateWith_of_bounded_growth ComputableInPolyTime.id'
    (ComputableInPolyTime.snd encBits encUnary) (ComputableInPolyTime.const [])
    hstep (growth := fun x => (x.2 + 1) * (6 * x.2 + 1)) ?_ fun x M => ?_
  · refine PolyBounded.of_forall_le 7 2 fun x => ?_
    have : x.2 ≤ (encPair encBits encUnary x).length := by
      have := length_le_encPair_right encBits encUnary x
      simp only [encUnary_apply, List.length_replicate] at this
      exact this
    nlinarith
  · have hpath := augmentStep_path_size x.1 x.2 M
    simp only [augmentStep, augmentAlong, encList_append, List.length_append]
    have h1 := length_encPath_le hpath.1 hpath.2
    have h2 := length_encList_sublist encEdge (List.filter_sublist (l := M)
      (p := fun e => !(((augmentingPaths x.1 x.2 M (labelling x.1 x.2 M)).headD []).any
        fun f => decide (f.1 = e.1))))
    simp only [encUnaryEdges, encEdge] at h1 h2 ⊢
    omega

private theorem computableInPolyTime_acceptsAt : ComputableInPolyTime
    (fun p : (List Bool × ℕ) × List (ℕ × ℕ) => acceptsAt p.1.1 p.1.2 p.2)
    (encPair (encPair encBits encUnary) (encList encEdge)) encBool := by
  simp only [acceptsAt]
  fun_prop

private theorem computableInPolyTime_deciderAt :
    ComputableInPolyTime (fun x : List Bool × ℕ => deciderAt x.1 x.2)
      (encPair encBits encUnary) encBool := by
  have h := computableInPolyTime_acceptsAt.comp'
    (ComputableInPolyTime.id'.prod computableInPolyTime_maximumMatching)
  exact h

private theorem computableInPolyTime_sqrt_length :
    ComputableInPolyTime (fun w : List Bool => w.length.sqrt) encBits encUnary := by
  refine ComputableInPolyTime.binary_to_unary_bounded (bound := fun w => w.length) ?_ (by fun_prop)
    fun w => Nat.sqrt_le_self _
  exact ComputableInPolyTime.binary_sqrt'
    (ComputableInPolyTime.unary_to_binary.comp' ComputableInPolyTime.length_bits)

/-- **The decider runs in polynomial time** on a multi-tape Turing machine. -/
theorem computableInPolyTime_decider : ComputableInPolyTime decider encBits encBool := by
  have h := computableInPolyTime_deciderAt.comp'
    (ComputableInPolyTime.id'.prod computableInPolyTime_sqrt_length)
  exact h

/-! ### Correctness -/

section Correctness

open Cslib.Algorithms.Lean.MaxFlow

/-- The edges `(u, v)` of `K_{n,n}` with `(↑u, ↑v) ∈ M`. -/
def edgeSet (n : ℕ) (M : List (ℕ × ℕ)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun e => ((e.1 : ℕ), (e.2 : ℕ)) ∈ M

@[simp]
theorem mem_edgeSet {n : ℕ} {M : List (ℕ × ℕ)} {e : Fin n × Fin n} :
    e ∈ edgeSet n M ↔ ((e.1 : ℕ), (e.2 : ℕ)) ∈ M := by
  simp [edgeSet]

/-- Every listed edge has both endpoints below `n`. -/
private def EdgesBelow (n : ℕ) (M : List (ℕ × ℕ)) : Prop := ∀ e ∈ M, e.1 < n ∧ e.2 < n

private theorem any_fst_iff {n : ℕ} {M : List (ℕ × ℕ)} (hM : EdgesBelow n M) (u : Fin n) :
    M.any (fun e => decide (e.1 = u)) = true ↔ u ∈ matchedLeft (edgeSet n M) := by
  simp only [List.any_eq_true, decide_eq_true_eq, mem_matchedLeft, mem_edgeSet]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl⟩
    exact ⟨⟨b, (hM _ he).2⟩, he⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, rfl⟩

private theorem any_snd_iff {n : ℕ} {M : List (ℕ × ℕ)} (hM : EdgesBelow n M) (v : Fin n) :
    M.any (fun e => decide (e.2 = v)) = true ↔ v ∈ matchedRight (edgeSet n M) := by
  simp only [List.any_eq_true, decide_eq_true_eq, mem_matchedRight, mem_edgeSet]
  constructor
  · rintro ⟨⟨a, b⟩, he, rfl⟩
    exact ⟨⟨a, (hM _ he).1⟩, he⟩
  · rintro ⟨u, hu⟩
    exact ⟨_, hu, rfl⟩

/-- An edge of `K_{n,n}` as a pair of natural numbers. -/
private def toNatEdge {n : ℕ} (e : Fin n × Fin n) : ℕ × ℕ := ((e.1 : ℕ), (e.2 : ℕ))

private theorem toNatEdge_injective {n : ℕ} : Function.Injective (toNatEdge (n := n)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [toNatEdge, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

/-- The labelling invariant after `t` passes: the labelled vertices are the alternating layers up
to `t`, and every label is a layered alternating prefix from a free left vertex. -/
private def LabelInv (w : List Bool) (n : ℕ) (M : List (ℕ × ℕ)) (t : ℕ) (lab : Labelling) :
    Prop :=
  ∀ u : Fin n, ((lab.getD u none).isSome ↔ u ∈ altLeft (graph w n) (edgeSet n M) t) ∧
    ∀ q ∈ lab.getD u none, ∃ r j Q,
      IsLayeredPrefix (graph w n) (edgeSet n M) ∅ r u j Q ∧ Q.map toNatEdge = q

private theorem getD_map_range {β : Type*} (f : ℕ → Option β) {n u : ℕ} (hu : u < n) :
    ((List.range n).map f).getD u none = f u := by
  simp [List.getD_eq_getElem?_getD, hu]

private theorem labelInv_initialLabelling (w : List Bool) {n : ℕ} {M : List (ℕ × ℕ)}
    (hM : EdgesBelow n M) : LabelInv w n M 0 (initialLabelling n M) := by
  intro u
  rw [initialLabelling, getD_map_range _ u.isLt]
  by_cases hu : u ∈ matchedLeft (edgeSet n M)
  · have h := (any_fst_iff hM u).mpr hu
    simp only [h, ↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_iff, mem_altLeft_zero,
      not_not, hu, true_and]
    simp
  · have h : M.any (fun e => decide (e.1 = u)) = false := by
      rw [Bool.eq_false_iff]
      exact fun h' => hu ((any_fst_iff hM u).mp h')
    simp only [h, Bool.false_eq_true, ↓reduceIte, Option.isSome_some, true_iff, mem_altLeft_zero]
    refine ⟨hu, ?_⟩
    intro q hq
    simp only [Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact ⟨u, 0, [], .root (isLayer_zero.mpr hu), rfl⟩

private theorem mem_labelCandidates {w : List Bool} {n : ℕ} {M : List (ℕ × ℕ)} {lab : Labelling}
    {u : ℕ} {q : List (ℕ × ℕ)} :
    q ∈ labelCandidates w n M lab u ↔ ∃ v < n, (u, v) ∈ M ∧ ∃ u' < n,
      (lab.getD u' none).isSome ∧ adj w n u' v = true ∧
        q = (lab.getD u' none).getD [] ++ [(u', v)] := by
  simp only [labelCandidates, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨v, hv, hq⟩
    split at hq
    · rename_i hc
      simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true] at hq
      obtain ⟨u', ⟨hu', hs, ha⟩, rfl⟩ := hq
      exact ⟨v, hv, of_decide_eq_true hc, u', hu', hs, ha, rfl⟩
    · simp at hq
  · rintro ⟨v, hv, hM, u', hu', hs, ha, rfl⟩
    refine ⟨v, hv, ?_⟩
    rw [ite_eq_left (decide_eq_true hM)]
    simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.and_eq_true]
    exact ⟨u', ⟨hu', hs, ha⟩, rfl⟩

private theorem labelInv_labelStep {w : List Bool} {n : ℕ} {M : List (ℕ × ℕ)} {t : ℕ}
    {lab : Labelling} (h : LabelInv w n M t lab) :
    LabelInv w n M (t + 1) (labelStep w n M lab) := by
  intro u
  obtain ⟨hiff, hpre⟩ := h u
  rw [labelStep, getD_map_range _ u.isLt]
  by_cases hs : (lab.getD u none).isSome = true
  · rw [ite_eq_left hs]
    exact ⟨⟨fun _ => altLeft_mono (Nat.le_succ t) (hiff.mp hs), fun _ => hs⟩, hpre⟩
  · rw [ite_eq_right hs]
    have hnot : u ∉ altLeft (graph w n) (edgeSet n M) t := fun h' => hs (hiff.mpr h')
    rcases hE : labelCandidates w n M lab u with _ | ⟨q₀, E⟩
    · refine ⟨?_, by simp⟩
      simp only [List.head?_nil, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro hu
      rcases mem_altLeft_succ.mp hu with hu | ⟨v, huv, hv⟩
      · exact hnot hu
      obtain ⟨u', hu', hG⟩ := mem_altRight.mp hv
      have hmem : (lab.getD u' none).getD [] ++ [((u' : ℕ), (v : ℕ))] ∈
          labelCandidates w n M lab u :=
        mem_labelCandidates.mpr
          ⟨v, v.isLt, mem_edgeSet.mp huv, u', u'.isLt, (h u').1.mpr hu', hG, rfl⟩
      rw [hE] at hmem
      simp at hmem
    · have hq₀ : q₀ ∈ labelCandidates w n M lab u := by
        rw [hE]
        exact List.mem_cons_self
      obtain ⟨v, hv, huv, u', hu', hsu', ha, hq⟩ := mem_labelCandidates.mp hq₀
      have hu'alt : (⟨u', hu'⟩ : Fin n) ∈ altLeft (graph w n) (edgeSet n M) t :=
        (h ⟨u', hu'⟩).1.mp hsu'
      have hvR : (⟨v, hv⟩ : Fin n) ∈ altRight (graph w n) (edgeSet n M) t :=
        mem_altRight.mpr ⟨⟨u', hu'⟩, hu'alt, ha⟩
      have huv' : (u, (⟨v, hv⟩ : Fin n)) ∈ edgeSet n M := mem_edgeSet.mpr huv
      have hu1 : u ∈ altLeft (graph w n) (edgeSet n M) (t + 1) :=
        mem_altLeft_succ_of_mem huv' hvR
      refine ⟨by simp [hu1], ?_⟩
      intro q hq
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hsu'
      obtain ⟨r, j, Q, hQ, hQq⟩ := (h ⟨u', hu'⟩).2 q' hq'
      have hj : j ≤ t := hQ.isLayer.le_of_mem hu'alt
      have hlay : IsLayer (graph w n) (edgeSet n M) u (j + 1) := by
        refine ⟨mem_altLeft_succ_of_mem huv' (mem_altRight.mpr ⟨⟨u', hu'⟩, hQ.isLayer.1, ha⟩),
          fun i hi hui => hnot (altLeft_mono (by omega) hui)⟩
      refine ⟨r, j + 1, Q ++ [((⟨u', hu'⟩ : Fin n), (⟨v, hv⟩ : Fin n))],
        .snoc hQ ha huv' (Finset.notMem_empty _) hlay, ?_⟩
      rw [List.map_append, hQq, hq, hq']
      rfl

private theorem labelInv_iterate (w : List Bool) {n : ℕ} {M : List (ℕ × ℕ)} (hM : EdgesBelow n M)
    (t : ℕ) : LabelInv w n M t ((labelStep w n M)^[t] (initialLabelling n M)) := by
  induction t with
  | zero => exact labelInv_initialLabelling w hM
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    exact labelInv_labelStep ih

private theorem mem_augmentingPaths {w : List Bool} {n : ℕ} {M : List (ℕ × ℕ)} {lab : Labelling}
    {p : List (ℕ × ℕ)} :
    p ∈ augmentingPaths w n M lab ↔ ∃ u < n, ∃ v < n, (lab.getD u none).isSome ∧
      adj w n u v = true ∧ M.any (fun e => decide (e.2 = v)) = false ∧
        p = (lab.getD u none).getD [] ++ [(u, v)] := by
  simp only [augmentingPaths, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨u, hu, v, ⟨hv, ⟨hs, ha⟩, hf⟩, rfl⟩
    exact ⟨u, hu, v, hv, hs, ha, hf, rfl⟩
  · rintro ⟨u, hu, v, hv, hs, ha, hf, rfl⟩
    exact ⟨u, hu, v, ⟨hv, ⟨hs, ha⟩, hf⟩, rfl⟩

private theorem edgeSet_augmentAlong {n : ℕ} {M : List (ℕ × ℕ)} (P : List (Fin n × Fin n)) :
    edgeSet n (augmentAlong M (P.map toNatEdge)) = augment (edgeSet n M) P.toFinset := by
  ext e
  rw [mem_edgeSet, mem_augment, List.mem_toFinset, mem_matchedLeft, augmentAlong, List.mem_append,
    List.mem_filter, mem_edgeSet]
  have hval : ((e.1 : ℕ), (e.2 : ℕ)) ∈ P.map toNatEdge ↔ e ∈ P := by
    rw [List.mem_map]
    exact ⟨fun ⟨a, ha, h⟩ => toNatEdge_injective h ▸ ha, fun h => ⟨e, h, rfl⟩⟩
  have hany : ((P.map toNatEdge).any fun f => decide (f.1 = (e.1 : ℕ))) = true ↔
      ∃ v, (e.1, v) ∈ P.toFinset := by
    simp only [List.any_eq_true, List.mem_map, decide_eq_true_eq, List.mem_toFinset]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, h⟩
      exact ⟨a.2, by rw [show e.1 = a.1 from Fin.ext h.symm]; exact ha⟩
    · rintro ⟨v, hv⟩
      exact ⟨_, ⟨_, hv, rfl⟩, rfl⟩
  rw [hval, Bool.not_eq_true', ← Bool.not_eq_true, hany]

private theorem edgesBelow_augmentAlong {n : ℕ} {M p : List (ℕ × ℕ)} (hM : EdgesBelow n M)
    (hp : EdgesBelow n p) : EdgesBelow n (augmentAlong M p) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact hp e he
  · exact hM e (List.mem_filter.mp he).1

/-- A matching of `K_{n,n}` has at most `n` edges. -/
private theorem card_le_of_isMatching {n : ℕ} {G : Fin n × Fin n → Bool}
    {M : Finset (Fin n × Fin n)} (hM : IsMatching G M) : M.card ≤ n := by
  rw [← card_matchedLeft hM]
  simpa using Finset.card_le_univ (matchedLeft M)

/-- One augmentation round either grows the matching, or leaves it unchanged and it is
maximum. -/
private theorem augmentStep_spec {w : List Bool} {n : ℕ} {M : List (ℕ × ℕ)}
    (hM : EdgesBelow n M) (hmatch : IsMatching (graph w n) (edgeSet n M)) :
    EdgesBelow n (augmentStep w n M) ∧ IsMatching (graph w n) (edgeSet n (augmentStep w n M)) ∧
      ((edgeSet n M).card < (edgeSet n (augmentStep w n M)).card ∨
        (augmentStep w n M = M ∧ IsMaxMatching (graph w n) (edgeSet n M))) := by
  have hlab : LabelInv w n M n (labelling w n M) := labelInv_iterate w hM n
  rcases hP : augmentingPaths w n M (labelling w n M) with _ | ⟨p, P⟩
  · have hstep : augmentStep w n M = M := by
      simp only [augmentStep, hP, List.headD_nil, augmentAlong, List.nil_append, List.any_nil,
        Bool.not_false, List.filter_true]
    rw [hstep]
    refine ⟨hM, hmatch, .inr ⟨rfl, hmatch, fun M' hM' => ?_⟩⟩
    have hno : NoShortAug (graph w n) (edgeSet n M) (n + 1) := by
      intro j hj v hv
      obtain ⟨u, hu, hG⟩ := mem_altRight.mp (altRight_mono (Nat.lt_succ_iff.mp hj) hv)
      by_contra hfree
      have hs := (hlab u).1.mpr hu
      have hf : M.any (fun e => decide (e.2 = v)) = false :=
        Bool.eq_false_iff.mpr fun h => hfree ((any_snd_iff hM v).mp h)
      have hmem := mem_augmentingPaths.mpr ⟨u, u.isLt, v, v.isLt, hs, hG, hf, rfl⟩
      rw [hP] at hmem
      simp at hmem
    have hk := card_mul_le_of_noShortAug hmatch hM' hno
    have hle : (edgeSet n M).card ≤ n := card_le_of_isMatching hmatch
    nlinarith
  · have hp : p ∈ augmentingPaths w n M (labelling w n M) := by
      rw [hP]
      exact List.mem_cons_self
    obtain ⟨u, hu, v, hv, hs, ha, hf, hpq⟩ := mem_augmentingPaths.mp hp
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨r, j, Q, hQ, hQq⟩ := (hlab ⟨u, hu⟩).2 q hq
    have hvfree : (⟨v, hv⟩ : Fin n) ∉ matchedRight (edgeSet n M) := fun h' => by
      rw [(any_snd_iff hM ⟨v, hv⟩).mpr h'] at hf
      exact Bool.noConfusion hf
    have hpath : IsLayeredPath (graph w n) (edgeSet n M) ∅ j (⟨u, hu⟩ : Fin n) j
        [((⟨u, hu⟩ : Fin n), (⟨v, hv⟩ : Fin n))] :=
      .last hQ.isLayer ha hvfree (Finset.notMem_empty _)
    have haug := (hQ.append hpath).isAugmentingPath hmatch
    have hpP : p = (Q ++ [((⟨u, hu⟩ : Fin n), (⟨v, hv⟩ : Fin n))]).map toNatEdge := by
      rw [hpq, hq, List.map_append, hQq]
      rfl
    have hstep : augmentStep w n M = augmentAlong M p := by
      simp only [augmentStep, hP, List.headD_cons]
    have hsem : edgeSet n (augmentStep w n M) =
        augment (edgeSet n M) (Q ++ [((⟨u, hu⟩ : Fin n), (⟨v, hv⟩ : Fin n))]).toFinset := by
      rw [hstep, hpP, edgeSet_augmentAlong]
    refine ⟨?_, ?_, .inl ?_⟩
    · rw [hstep, hpP]
      refine edgesBelow_augmentAlong hM fun e he => ?_
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
      exact ⟨a.1.isLt, a.2.isLt⟩
    · rw [hsem]
      exact haug.isMatching_augment hmatch
    · rw [hsem]
      exact haug.card_augment hmatch

/-- The invariant after `t` rounds: a matching at least as large as `min t |M'|` for every
matching `M'`. -/
private def MatchInv (w : List Bool) (n t : ℕ) (M : List (ℕ × ℕ)) : Prop :=
  EdgesBelow n M ∧ IsMatching (graph w n) (edgeSet n M) ∧
    ∀ M' : Finset (Fin n × Fin n), IsMatching (graph w n) M' → min t M'.card ≤ (edgeSet n M).card

private theorem matchInv_iterate (w : List Bool) (n t : ℕ) :
    MatchInv w n t ((augmentStep w n)^[t] []) := by
  induction t with
  | zero =>
    refine ⟨by simp [EdgesBelow], ⟨by simp [edgeSet], by simp [edgeSet], by simp [edgeSet]⟩,
      fun M' _ => ?_⟩
    simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hB, hmatch, hmin⟩ := ih
    obtain ⟨hB', hmatch', hcases⟩ := augmentStep_spec hB hmatch
    refine ⟨hB', hmatch', fun M' hM' => ?_⟩
    have := hmin M' hM'
    rcases hcases with hlt | ⟨heq, hmax⟩
    · omega
    · rw [heq]
      exact (min_le_right _ _).trans (hmax.2 M' hM')

private theorem matchInv_maximumMatching (w : List Bool) (n : ℕ) :
    MatchInv w n n (maximumMatching w n) :=
  matchInv_iterate w n n

/-- Every edge listed by `maximumMatching w n` has both endpoints below `n`, so
`edgeSet n (maximumMatching w n)` is all of it. -/
theorem lt_of_mem_maximumMatching {w : List Bool} {n : ℕ} {e : ℕ × ℕ}
    (he : e ∈ maximumMatching w n) : e.1 < n ∧ e.2 < n :=
  (matchInv_maximumMatching w n).1 e he

/-- **The algorithm computes a maximum matching** of the graph read from the word. -/
theorem isMaxMatching_maximumMatching (w : List Bool) (n : ℕ) :
    IsMaxMatching (graph w n) (edgeSet n (maximumMatching w n)) := by
  obtain ⟨-, hmatch, hmin⟩ := matchInv_maximumMatching w n
  refine ⟨hmatch, fun M' hM' => ?_⟩
  have h1 := hmin M' hM'
  have h2 := card_le_of_isMatching hM'
  omega

private theorem deciderAt_eq_true_iff (w : List Bool) (n : ℕ) :
    deciderAt w n = true ↔ n * n = w.length ∧
      Cslib.Circuits.BipartiteMatching.HasPerfectMatching (graph w n) := by
  obtain ⟨hB, hmatch, hmin⟩ := matchInv_maximumMatching w n
  rw [deciderAt, acceptsAt, Bool.and_eq_true, decide_eq_true_eq,
    hasPerfectMatching_iff_exists_matching_card]
  refine and_congr_right fun _ => ?_
  rw [Fintype.card_fin, List.all_eq_true]
  have hall : (∀ u ∈ List.range n,
      (maximumMatching w n).any (fun e => decide (e.1 = u)) = true) ↔
      matchedLeft (edgeSet n (maximumMatching w n)) = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    constructor
    · intro h u
      exact (any_fst_iff hB u).mp (h u (List.mem_range.mpr u.isLt))
    · intro h u hu
      exact (any_fst_iff hB ⟨u, List.mem_range.mp hu⟩).mpr (h _)
  rw [hall]
  constructor
  · intro h
    refine ⟨_, hmatch, ?_⟩
    rw [← card_matchedLeft hmatch, h, Finset.card_univ, Fintype.card_fin]
  · rintro ⟨M', hM', hcard⟩
    have h1 := hmin M' hM'
    rw [hcard, min_self] at h1
    have h2 : (matchedLeft (edgeSet n (maximumMatching w n))).card = n := by
      rw [card_matchedLeft hmatch]
      exact le_antisymm (card_le_of_isMatching hmatch) h1
    exact Finset.eq_univ_of_card _ (by rw [h2, Fintype.card_fin])

/-- **The decider decides bipartite perfect matching.** -/
theorem decider_eq_true_iff (w : List Bool) : decider w = true ↔ w ∈ BipartitePerfectMatching := by
  rw [decider, deciderAt_eq_true_iff, mem_iff]
  constructor
  · exact fun h => ⟨_, h⟩
  · rintro ⟨n, hn, h⟩
    have hs : w.length.sqrt = n := by rw [← hn, Nat.sqrt_eq]
    rw [hs]
    exact ⟨hn, h⟩

end Correctness

/-- **Bipartite perfect matching is in `P`**: under the plain bit encoding, a multi-tape Turing
machine decides in polynomial time whether a word of length `n * n`, read as the row-major
adjacency matrix of a subgraph of `K_{n,n}`, describes a graph with a perfect matching. -/
theorem mem_P : (BipartitePerfectMatching : Set (List Bool)) ∈ P encBits :=
  ⟨decider, computableInPolyTime_decider, fun w => (decider_eq_true_iff w).symm⟩

end Cslib.Complexity.BipartitePerfectMatching
