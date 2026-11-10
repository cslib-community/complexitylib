/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Chain

/-!
# Multi-source shortest walks by breadth-first search

A digraph is given by a list `V` of vertices and a Boolean arc test `arc`; two Boolean tests `src`
and `tgt` mark the sources and the targets. Breadth-first search from all sources at once
(`Cslib.Reachability.findWalk`) either returns a `src`-to-`tgt` walk with the fewest vertices or
returns the list of vertices reachable from the sources, which then contains every source, is
closed under arcs inside `V` and contains no target (`Cslib.Reachability.IsSrcTgtSeparator`). Such
a separator rules out every `src`-to-`tgt` walk, so the two outcomes are exclusive and decide
whether a walk exists.

The search stores, for each vertex found, a walk from a source that reaches it. Round `k` adds the
vertices first reached by walks with `k + 2` vertices, so the first target found carries a
shortest walk. The number of rounds is bounded by `V.length`, since each round before the last
finds a new vertex of `V`.

`Cslib.Reachability.search` in `CslibFrontier.Algorithms.Reachability.BreadthFirst` computes the
reachable set from a single start element; the search here starts from many sources, records a
walk for every vertex it finds and stops at the first target.

## Main definitions

* `Cslib.Reachability.IsWalk`, `IsSrcTgtWalk`, `IsShortestSrcTgtWalk`: walks in the digraph,
  walks from a source to a target, and the shortest such walks (by number of vertices).
* `Cslib.Reachability.IsSrcTgtSeparator`: a set of vertices containing every source, closed under
  arcs and containing no target.
* `Cslib.Reachability.findWalk`: multi-source breadth-first search.

## Main results

* `Cslib.Reachability.isShortestSrcTgtWalk_of_findWalk_eq_inl`: a returned walk is a shortest
  `src`-to-`tgt` walk.
* `Cslib.Reachability.isSrcTgtSeparator_of_findWalk_eq_inr`: a returned vertex list is a
  separator.
* `Cslib.Reachability.IsSrcTgtSeparator.not_isSrcTgtWalk`: a separator rules out every
  `src`-to-`tgt` walk.
* `Cslib.Reachability.findWalk_isLeft_iff`: the search returns a walk exactly when one exists.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 22.2][CLRS2009]
-/

@[expose] public section

namespace Cslib.Reachability

variable {α : Type*}

/-- `p` is a walk in the digraph with vertex list `V` and arc test `arc`: every vertex of `p` lies
in `V` and consecutive vertices of `p` are joined by arcs. -/
def IsWalk (V : List α) (arc : α → α → Bool) (p : List α) : Prop :=
  (∀ z ∈ p, z ∈ V) ∧ List.IsChain (fun u v => arc u v = true) p

/-- `p` is a nonempty walk from a vertex accepted by `src` to a vertex accepted by `tgt`. A single
vertex accepted by both tests is such a walk. -/
def IsSrcTgtWalk (V : List α) (arc : α → α → Bool) (src tgt : α → Bool) (p : List α) : Prop :=
  ∃ hne : p ≠ [], src (p.head hne) = true ∧ tgt (p.getLast hne) = true ∧ IsWalk V arc p

/-- `p` is a `src`-to-`tgt` walk with the fewest vertices. -/
def IsShortestSrcTgtWalk (V : List α) (arc : α → α → Bool) (src tgt : α → Bool)
    (p : List α) : Prop :=
  IsSrcTgtWalk V arc src tgt p ∧ ∀ q, IsSrcTgtWalk V arc src tgt q → p.length ≤ q.length

/-- `R` separates the sources from the targets: it is a list of vertices of `V` that contains every
source in `V`, is closed under arcs into `V`, and contains no target. -/
def IsSrcTgtSeparator (V : List α) (arc : α → α → Bool) (src tgt : α → Bool)
    (R : List α) : Prop :=
  (∀ v ∈ R, v ∈ V) ∧ (∀ v ∈ V, src v = true → v ∈ R) ∧
    (∀ u ∈ R, ∀ v ∈ V, arc u v = true → v ∈ R) ∧ ∀ v ∈ R, tgt v = false

/-- A separator rules out every `src`-to-`tgt` walk. -/
theorem IsSrcTgtSeparator.not_isSrcTgtWalk {V : List α} {arc : α → α → Bool} {src tgt : α → Bool}
    {R : List α} (hR : IsSrcTgtSeparator V arc src tgt R) {p : List α} :
    ¬ IsSrcTgtWalk V arc src tgt p := by
  obtain ⟨-, hsrc, hcl, htgt⟩ := hR
  rintro ⟨hne, hhead, hlast, hmem, hchain⟩
  have key : ∀ (p : List α) (hne : p ≠ []), p.head hne ∈ R → (∀ z ∈ p, z ∈ V) →
      List.IsChain (fun u v => arc u v = true) p → p.getLast hne ∈ R := by
    intro p
    induction p with
    | nil => intro hne; exact absurd rfl hne
    | cons a t ih =>
      intro _ ha hmem hchain
      cases t with
      | nil => simpa using ha
      | cons b t =>
        have hb : b ∈ R := hcl a (by simpa using ha) b (hmem b (by simp)) (hchain.rel)
        rw [List.getLast_cons (List.cons_ne_nil b t)]
        exact ih (List.cons_ne_nil b t) (by simpa using hb)
          (fun z hz => hmem z (List.mem_cons_of_mem a hz)) (List.IsChain.tail hchain)
  have hR := key p hne (hsrc _ (hmem _ (List.head_mem hne)) hhead) hmem hchain
  rw [htgt _ hR] at hlast
  exact Bool.false_ne_true hlast

variable [DecidableEq α]

/-! ### The search -/

/-- The entries found before the first round: each source of `V` with the one-vertex walk. -/
def bfsInit (V : List α) (src : α → Bool) : List (α × List α) :=
  (V.filter src).map fun v => (v, [v])

/-- The entries added by one round: each vertex `v` of `V` not found yet that some found entry
`(u, w)` has an arc to, with the walk `w ++ [v]` (for the first such entry). -/
def bfsNew (V : List α) (arc : α → α → Bool) (found : List (α × List α)) :
    List (α × List α) :=
  V.filterMap fun v =>
    if found.any (fun e => e.1 == v) then none
    else (found.find? fun e => arc e.1 v).map fun e => (v, e.2 ++ [v])

/-- Rounds of breadth-first search, each found entry `(v, w)` carrying a walk `w` to `v`. A found
target returns its walk; a round adding nothing, or running out of rounds, returns the vertices
found. -/
def bfsLoop (V : List α) (arc : α → α → Bool) (tgt : α → Bool)
    (fuel : ℕ) (found : List (α × List α)) : List α ⊕ List α :=
  match found.find? (fun e => tgt e.1) with
  | some e => .inl e.2
  | none =>
    match fuel with
    | 0 => .inr (found.map Prod.fst)
    | fuel + 1 =>
      if (bfsNew V arc found).isEmpty then .inr (found.map Prod.fst)
      else bfsLoop V arc tgt fuel (found ++ bfsNew V arc found)

/-- **Multi-source breadth-first search**: `.inl p` for a shortest `src`-to-`tgt` walk `p`, or
`.inr R` for the list `R` of vertices reachable from the sources when no target is. -/
def findWalk (V : List α) (arc : α → α → Bool) (src tgt : α → Bool) : List α ⊕ List α :=
  bfsLoop V arc tgt V.length (bfsInit V src)

/-! ### Correctness -/

section Correctness

variable {V : List α} {arc : α → α → Bool} {src tgt : α → Bool}

/-- After round `k`, every found entry `(v, w)` has a walk `w` from a source to `v` with at most
`k + 1` vertices. -/
private def Sound (V : List α) (arc : α → α → Bool) (src : α → Bool) (k : ℕ)
    (found : List (α × List α)) : Prop :=
  ∀ e ∈ found, ∃ hne : e.2 ≠ [], src (e.2.head hne) = true ∧ e.2.getLast hne = e.1 ∧
    IsWalk V arc e.2 ∧ e.2.length ≤ k + 1

/-- After round `k`, every vertex reached from a source by a walk with at most `k + 1` vertices has
been found. -/
private def Complete (V : List α) (arc : α → α → Bool) (src : α → Bool) (k : ℕ)
    (found : List (α × List α)) : Prop :=
  ∀ q : List α, ∀ hne : q ≠ [], src (q.head hne) = true → IsWalk V arc q → q.length ≤ k + 1 →
    ∃ e ∈ found, e.1 = q.getLast hne

/-- Before round `k` looks for targets, every `src`-to-`tgt` walk has at least `k + 1` vertices. -/
private def NoShort (V : List α) (arc : α → α → Bool) (src tgt : α → Bool) (k : ℕ) : Prop :=
  ∀ q : List α, IsSrcTgtWalk V arc src tgt q → k + 1 ≤ q.length

private theorem of_mem_bfsNew {found : List (α × List α)} {x : α × List α}
    (hx : x ∈ bfsNew V arc found) :
    x.1 ∈ V ∧ (∀ e ∈ found, e.1 ≠ x.1) ∧ ∃ e ∈ found, arc e.1 x.1 = true ∧ x.2 = e.2 ++ [x.1] := by
  obtain ⟨v, hv, hfx⟩ := List.mem_filterMap.mp hx
  by_cases hany : found.any (fun e => e.1 == v) = true
  · simp [hany] at hfx
  · rw [ite_eq_right hany] at hfx
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hfx
    refine ⟨hv, fun e' he' heq => hany ?_, e, List.mem_of_find?_eq_some he,
      by simpa using List.find?_some he, rfl⟩
    exact List.any_eq_true.mpr ⟨e', he', by simpa using heq⟩

private theorem exists_mem_bfsNew {found : List (α × List α)} {v : α} (hv : v ∈ V)
    (hnot : ∀ e ∈ found, e.1 ≠ v) (harc : ∃ e ∈ found, arc e.1 v = true) :
    ∃ w, (v, w) ∈ bfsNew V arc found := by
  have hany : ¬ found.any (fun e => e.1 == v) = true := by
    rw [List.any_eq_true]
    rintro ⟨e, he, heq⟩
    exact hnot e he (by simpa using heq)
  obtain ⟨e, hfind⟩ : ∃ e, found.find? (fun e => arc e.1 v) = some e := by
    rcases h : found.find? (fun e => arc e.1 v) with _ | e
    · obtain ⟨e, he, harc⟩ := harc
      exact absurd harc (by simpa using List.find?_eq_none.mp h e he)
    · exact ⟨e, h⟩
  refine ⟨e.2 ++ [v], List.mem_filterMap.mpr ⟨v, hv, ?_⟩⟩
  rw [ite_eq_right hany, hfind]
  rfl

private theorem sound_step {k : ℕ} {found : List (α × List α)} (hS : Sound V arc src k found) :
    Sound V arc src (k + 1) (found ++ bfsNew V arc found) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨hne, hhead, hlast, hwalk, hlen⟩ := hS x hx
    exact ⟨hne, hhead, hlast, hwalk, by omega⟩
  · obtain ⟨hv, -, e, he, harc, hx2⟩ := of_mem_bfsNew hx
    obtain ⟨hne, hhead, hlast, ⟨hmem, hchain⟩, hlen⟩ := hS e he
    have hne' : x.2 ≠ [] := by simp [hx2]
    refine ⟨hne', ?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · simpa [hx2, List.head_append_of_ne_nil hne] using hhead
    · simp [hx2]
    · intro z hz
      rw [hx2, List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hmem z hz
      · exact hv
    · rw [hx2]
      refine List.IsChain.append hchain (List.isChain_singleton _) ?_
      intro a ha b hb
      rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at ha
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
      subst ha hb
      rwa [hlast]
    · simp only [hx2, List.length_append, List.length_singleton]
      omega

private theorem complete_step {k : ℕ} {found : List (α × List α)}
    (hC : Complete V arc src k found) :
    Complete V arc src (k + 1) (found ++ bfsNew V arc found) := by
  intro q hne hhead hwalk hlen
  by_cases hshort : q.length ≤ k + 1
  · obtain ⟨e, he, heq⟩ := hC q hne hhead hwalk hshort
    exact ⟨e, List.mem_append_left _ he, heq⟩
  · obtain ⟨hmem, hchain⟩ := hwalk
    rcases List.eq_nil_or_concat' q with rfl | ⟨L, b, rfl⟩
    · exact absurd rfl hne
    have hLlen : L.length = k + 1 := by simp at hlen hshort; omega
    have hLne : L ≠ [] := by
      intro h
      simp [h] at hLlen
    have hLchain : List.IsChain (fun u v => arc u v = true) L :=
      (List.isChain_append.mp hchain).1
    have hjoin : arc (L.getLast hLne) b = true := by
      have := (List.isChain_append.mp hchain).2.2
      exact this _ (by rw [List.getLast?_eq_some_getLast hLne]; rfl) _ (by simp)
    have hLhead : src (L.head hLne) = true := by
      simpa [List.head_append_of_ne_nil hLne] using hhead
    obtain ⟨e, he, heq⟩ := hC L hLne hLhead
      ⟨fun z hz => hmem z (List.mem_append_left _ hz), hLchain⟩ hLlen.le
    have hbV : b ∈ V := hmem b (by simp)
    rw [List.getLast_append_singleton]
    by_cases hfound : ∃ e' ∈ found, e'.1 = b
    · obtain ⟨e', he', heq'⟩ := hfound
      exact ⟨e', List.mem_append_left _ he', heq'⟩
    · push Not at hfound
      obtain ⟨w, hw⟩ := exists_mem_bfsNew hbV hfound ⟨e, he, heq ▸ hjoin⟩
      exact ⟨(b, w), List.mem_append_right _ hw, rfl⟩

omit [DecidableEq α] in
private theorem noShort_step {k : ℕ} {found : List (α × List α)}
    (hC : Complete V arc src k found) (hnone : found.find? (fun e => tgt e.1) = none) :
    NoShort V arc src tgt (k + 1) := by
  intro q ⟨hne, hhead, hlast, hwalk⟩
  by_contra hlt
  obtain ⟨e, he, heq⟩ := hC q hne hhead hwalk (by omega)
  have := List.find?_eq_none.mp hnone e he
  rw [heq] at this
  exact this hlast

omit [DecidableEq α] in
private theorem keys_subset {k : ℕ} {found : List (α × List α)} (hS : Sound V arc src k found) :
    ∀ v ∈ found.map Prod.fst, v ∈ V := by
  intro v hv
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
  obtain ⟨hne, -, hlast, ⟨hmem, -⟩, -⟩ := hS e he
  exact hlast ▸ hmem _ (List.getLast_mem hne)

private theorem card_step {found : List (α × List α)} (hne : (bfsNew V arc found).isEmpty = false) :
    ((found.map Prod.fst).toFinset.card + 1) ≤
      ((found ++ bfsNew V arc found).map Prod.fst).toFinset.card := by
  obtain ⟨x, hx⟩ : ∃ x, x ∈ bfsNew V arc found := by
    rcases h : bfsNew V arc found with _ | ⟨x, _⟩
    · simp [h] at hne
    · exact ⟨x, by simp⟩
  obtain ⟨-, hnot, -⟩ := of_mem_bfsNew hx
  have hx1 : x.1 ∉ (found.map Prod.fst).toFinset := by
    simp only [List.mem_toFinset, List.mem_map, not_exists, not_and]
    exact hnot
  rw [← Finset.card_insert_of_notMem hx1]
  refine Finset.card_le_card ?_
  intro a ha
  simp only [Finset.mem_insert, List.mem_toFinset, List.map_append, List.mem_append] at ha ⊢
  rcases ha with rfl | ha
  · exact .inr (List.mem_map_of_mem hx)
  · exact .inl ha

omit [DecidableEq α] in
private theorem separator_of_closed {k : ℕ} {found : List (α × List α)}
    (hS : Sound V arc src k found) (hC : Complete V arc src k found)
    (hnone : found.find? (fun e => tgt e.1) = none)
    (hcl : ∀ u ∈ found.map Prod.fst, ∀ v ∈ V, arc u v = true → v ∈ found.map Prod.fst) :
    IsSrcTgtSeparator V arc src tgt (found.map Prod.fst) := by
  refine ⟨keys_subset hS, fun v hv hsrc => ?_, hcl, fun v hv => ?_⟩
  · obtain ⟨e, he, heq⟩ := hC [v] (List.cons_ne_nil v []) hsrc
      ⟨by simpa using hv, List.isChain_singleton v⟩ (by simp)
    exact List.mem_map.mpr ⟨e, he, heq⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hv
    simpa using List.find?_eq_none.mp hnone e he

omit [DecidableEq α] in
private theorem inl_of_find?_eq_some {k : ℕ} {found : List (α × List α)} {e : α × List α}
    (hS : Sound V arc src k found) (hN : NoShort V arc src tgt k)
    (hfind : found.find? (fun e => tgt e.1) = some e) :
    IsShortestSrcTgtWalk V arc src tgt e.2 := by
  obtain ⟨hne, hhead, hlast, hwalk, hlen⟩ := hS e (List.mem_of_find?_eq_some hfind)
  have htgt : tgt e.1 = true := by simpa using List.find?_some hfind
  refine ⟨⟨hne, hhead, hlast ▸ htgt, hwalk⟩, fun q hq => ?_⟩
  have := hN q hq
  omega

private theorem bfsLoop_spec :
    ∀ (fuel k : ℕ) (found : List (α × List α)),
      Sound V arc src k found → Complete V arc src k found → NoShort V arc src tgt k →
      V.toFinset.card ≤ (found.map Prod.fst).toFinset.card + fuel →
      (∀ p, bfsLoop V arc tgt fuel found = .inl p → IsShortestSrcTgtWalk V arc src tgt p) ∧
      (∀ R, bfsLoop V arc tgt fuel found = .inr R → IsSrcTgtSeparator V arc src tgt R) := by
  intro fuel
  induction fuel with
  | zero =>
    intro k found hS hC hN hcard
    rcases hfind : found.find? (fun e => tgt e.1) with _ | e
    · refine ⟨fun p h => by simp [bfsLoop, hfind] at h, fun R h => ?_⟩
      simp only [bfsLoop, hfind, Sum.inr.injEq] at h
      subst h
      refine separator_of_closed hS hC hfind fun u _ v hv _ => ?_
      have hsub : (found.map Prod.fst).toFinset ⊆ V.toFinset := by
        intro a ha
        rw [List.mem_toFinset] at ha ⊢
        exact keys_subset hS a ha
      have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
      have : v ∈ V.toFinset := List.mem_toFinset.mpr hv
      rw [← heq] at this
      exact List.mem_toFinset.mp this
    · refine ⟨fun p h => ?_, fun R h => by simp [bfsLoop, hfind] at h⟩
      simp only [bfsLoop, hfind, Sum.inl.injEq] at h
      exact h ▸ inl_of_find?_eq_some hS hN hfind
  | succ fuel ih =>
    intro k found hS hC hN hcard
    rcases hfind : found.find? (fun e => tgt e.1) with _ | e
    · by_cases hempty : (bfsNew V arc found).isEmpty = true
      · refine ⟨fun p h => by simp [bfsLoop, hfind, hempty] at h, fun R h => ?_⟩
        simp only [bfsLoop, hfind, hempty, ite_true, Sum.inr.injEq] at h
        subst h
        refine separator_of_closed hS hC hfind fun u hu v hv harc => ?_
        by_contra hvnot
        have hnot : ∀ e ∈ found, e.1 ≠ v := fun e he heq =>
          hvnot (List.mem_map.mpr ⟨e, he, heq⟩)
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu
        obtain ⟨w, hw⟩ := exists_mem_bfsNew hv hnot ⟨e, he, harc⟩
        rw [List.isEmpty_iff] at hempty
        simp [hempty] at hw
      · have hloop : bfsLoop V arc tgt (fuel + 1) found =
            bfsLoop V arc tgt fuel (found ++ bfsNew V arc found) := by
          simp [bfsLoop, hfind, hempty]
        rw [hloop]
        refine ih (k + 1) _ (sound_step hS) (complete_step hC) (noShort_step hC hfind) ?_
        have := card_step (V := V) (arc := arc) (found := found) (by simpa using hempty)
        omega
    · refine ⟨fun p h => ?_, fun R h => by simp [bfsLoop, hfind] at h⟩
      simp only [bfsLoop, hfind, Sum.inl.injEq] at h
      exact h ▸ inl_of_find?_eq_some hS hN hfind

private theorem findWalk_spec :
    (∀ p, findWalk V arc src tgt = .inl p → IsShortestSrcTgtWalk V arc src tgt p) ∧
      (∀ R, findWalk V arc src tgt = .inr R → IsSrcTgtSeparator V arc src tgt R) := by
  refine bfsLoop_spec V.length 0 (bfsInit V src) ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp he
    obtain ⟨hvV, hsrc⟩ := List.mem_filter.mp hv
    exact ⟨List.cons_ne_nil v [], hsrc, rfl, ⟨by simpa using hvV, List.isChain_singleton v⟩,
      le_rfl⟩
  · intro q hne hhead hwalk hlen
    obtain ⟨v, rfl⟩ : ∃ v, q = [v] := by
      rcases q with _ | ⟨v, _ | ⟨w, t⟩⟩
      · exact absurd rfl hne
      · exact ⟨v, rfl⟩
      · simp at hlen
    refine ⟨(v, [v]), List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hwalk.1 v (by simp), hhead⟩,
      rfl⟩, rfl⟩
  · intro q ⟨hne, _⟩
    exact List.length_pos_of_ne_nil hne
  · exact (List.toFinset_card_le V).trans (Nat.le_add_left _ _)

/-- A walk returned by `findWalk` is a shortest `src`-to-`tgt` walk. -/
theorem isShortestSrcTgtWalk_of_findWalk_eq_inl {p : List α}
    (h : findWalk V arc src tgt = .inl p) : IsShortestSrcTgtWalk V arc src tgt p :=
  findWalk_spec.1 p h

/-- A vertex list returned by `findWalk` separates the sources from the targets. -/
theorem isSrcTgtSeparator_of_findWalk_eq_inr {R : List α}
    (h : findWalk V arc src tgt = .inr R) : IsSrcTgtSeparator V arc src tgt R :=
  findWalk_spec.2 R h

/-- `findWalk` returns a walk exactly when some `src`-to-`tgt` walk exists. -/
theorem findWalk_isLeft_iff :
    (findWalk V arc src tgt).isLeft ↔ ∃ p, IsSrcTgtWalk V arc src tgt p := by
  rcases h : findWalk V arc src tgt with p | R
  · exact ⟨fun _ => ⟨p, (isShortestSrcTgtWalk_of_findWalk_eq_inl h).1⟩, fun _ => rfl⟩
  · refine ⟨fun h' => by simp at h', fun ⟨p, hp⟩ => ?_⟩
    exact absurd hp (isSrcTgtSeparator_of_findWalk_eq_inr h).not_isSrcTgtWalk

end Correctness

end Cslib.Reachability
