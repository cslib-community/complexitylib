/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.List.SplitLengths
public import Mathlib.Data.Nat.Log

/-!
# Static multiway predecessor trees

This is an outer multiway tree for fusion-tree search, independently of node search.
Keys occur in leaves; each internal node caches the first key in its subtree. A node search
may scan its children linearly. No word-RAM running-time bound is asserted here.
Singleton branches are collapsed, so leaves need not all have the same depth.

## Main definitions

* `Tree`: singleton leaves and internal nodes with cached subtree minima.
* `Tree.keys`, `Tree.minimum`, `Tree.height`, `Tree.slots`: stored keys, cached minimum, height
  and scalar-slot count of a tree.
* `Tree.Valid`: occupancy and cached-minimum invariants.
* `Tree.join`, `Tree.chunks`, `Tree.buildAux`: node formation, block splitting and recursive
  height-bounded tree construction.
* `Tree.build`: executable construction from a list, with branching parameter `B`.
* `Tree.selectChild`, `Tree.listPredecessor`: linear child selection and list predecessor scan.
* `Tree.predecessor`: inclusive predecessor, using an explicit linear scan of child minima.

## Main results

* `Tree.keys_build`, `Tree.valid_build`: construction preserves all keys and supplies occupancy.
* `Tree.height_build_le`: height is at most `Nat.clog B n`, uniformly for `B ≥ 2`.
* `Tree.height_build_le_log_add_one`: height is at most `Nat.log B n + 1` for `B ≥ 2`.
* `Tree.slots_build_le`: keys, links, cached minima and headers occupy at most `14n + 2` slots.
* `Tree.predecessor_build_eq_some_iff`, `Tree.predecessor_build_eq_none_iff`:
  exact search semantics.

## References

See [FredmanWillard1993] for fusion trees and their multiway outer search tree.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.FusionTree

/-- A multiway tree representation. Well-formed leaves contain at most one key. The empty tree is
represented by an empty leaf. Internal nodes store one cached minimum and their child pointers. -/
inductive Tree where
  | leaf (keys : List ℕ)
  | node (minimum : ℕ) (children : List Tree)
  deriving Repr

namespace Tree

/-- Stored leaf keys in left-to-right order, without the cached internal minima. -/
def keys : Tree → List ℕ
  | .leaf xs => xs
  | .node _ cs => cs.flatMap keys

/-- Cached subtree minimum, with zero used for an empty leaf. -/
def minimum : Tree → ℕ
  | .leaf xs => xs.headD 0
  | .node m _ => m

/-- Height counts edges, so a leaf has height zero. -/
def height : Tree → ℕ
  | .leaf _ => 0
  | .node _ cs => (cs.map height).foldr max 0 + 1

/-- Every child has strictly smaller height than its parent node. -/
theorem height_lt_node_of_mem {m : ℕ} {cs : List Tree} {t : Tree} (ht : t ∈ cs) :
    t.height < (node m cs).height := by
  have hh : t.height ≤ (cs.map height).foldr max 0 := by
    induction cs with
    | nil => simp at ht
    | cons u us ih =>
      rcases List.mem_cons.mp ht with rfl | ht
      · simp
      · exact (ih ht).trans (by simp)
  simp only [height]
  omega

/-- An indexed child has strictly smaller height than its parent node. -/
theorem height_getElem_lt_node (m : ℕ) (cs : List Tree) (i : Fin cs.length) :
    cs[i].height < (node m cs).height :=
  height_lt_node_of_mem (List.getElem_mem i.isLt)

/-- Structural storage in scalar slots, including the list representation: a leaf has a tag and
a list reference; an internal node has a tag, minimum and child-list reference. Each list cell
has a tag, an entry and a next link. A key is counted as one scalar, not by its bit length.
There is no allocation of `B` slots at every node. -/
def slots : Tree → ℕ
  | .leaf xs => 2 + 3 * xs.length
  | .node _ cs => 3 + 3 * cs.length + (cs.map slots).sum

/-- Occupancy and cached-minimum invariants. Every non-root child is nonempty. -/
def Valid (B : ℕ) : Tree → Prop
  | .leaf xs => xs.length ≤ 1
  | .node m cs =>
    2 ≤ cs.length ∧ cs.length ≤ B ∧ m = (cs.flatMap keys).headD 0 ∧
      ∀ t ∈ cs, Valid B t ∧ t.keys ≠ []

/-- Form a node, collapsing groups of zero or one child. -/
def join : List Tree → Tree
  | [] => .leaf []
  | [t] => t
  | t :: u :: ts => .node (((t :: u :: ts).flatMap keys).headD 0) (t :: u :: ts)

/-- Split into at most `B` consecutive nonempty blocks of at most `k` elements, using Mathlib's
`List.splitLengths`. The caller must ensure that `B * k` covers the input. -/
def chunks (B k : ℕ) (xs : List ℕ) : List (List ℕ) :=
  ((List.replicate B k).splitLengths xs).filter (· ≠ [])

/-- Construct a tree of height at most `h`, for inputs of length at most `B ^ h`.
Singleton child groups are collapsed, including on incomplete rightmost branches. -/
def buildAux (B : ℕ) : ℕ → List ℕ → Tree
  | 0, xs => .leaf xs
  | h + 1, xs => join ((chunks B (B ^ h) xs).map (buildAux B h))

/-- Construct a static tree. For `2 ≤ B`, no input keys are lost, and the height is at most
`Nat.clog B xs.length`. Sorting and distinctness are requirements for ordered search, not for
construction or its shape bounds. -/
def build (B : ℕ) (xs : List ℕ) : Tree :=
  buildAux B (Nat.clog B xs.length) xs

private theorem keys_join (cs : List Tree) : (join cs).keys = cs.flatMap keys := by
  rcases cs with _ | ⟨t, _ | ⟨u, ts⟩⟩ <;> simp [join, keys]

private theorem chunks_length_le (B k : ℕ) (xs : List ℕ) : (chunks B k xs).length ≤ B := by
  exact (List.length_filter_le _ _).trans (by simp)

private theorem chunks_mem {B k : ℕ} {xs ys : List ℕ} (h : ys ∈ chunks B k xs) :
    ys ≠ [] ∧ ys.length ≤ k := by
  obtain ⟨hm, hn⟩ := List.mem_filter.mp h
  exact ⟨by simpa using hn,
    List.length_mem_splitLengths xs _ k (by simp) ys hm⟩

private theorem flatten_chunks {B k : ℕ} {xs : List ℕ} (h : xs.length ≤ B * k) :
    (chunks B k xs).flatten = xs := by
  rw [chunks, List.flatten_filter_ne_nil]
  apply List.flatten_splitLengths
  simpa using h

private theorem keys_buildAux {B h : ℕ} {xs : List ℕ} (hn : xs.length ≤ B ^ h) :
    (buildAux B h xs).keys = xs := by
  induction h generalizing xs with
  | zero => simp [buildAux, keys]
  | succ h ih =>
    rw [buildAux, keys_join, List.flatMap_map]
    have heq : (chunks B (B ^ h) xs).map (fun ys => (buildAux B h ys).keys) =
        (chunks B (B ^ h) xs).map id :=
      List.map_congr_left fun ys hy => ih (chunks_mem hy).2
    change ((chunks B (B ^ h) xs).map (fun ys => (buildAux B h ys).keys)).flatten = xs
    rw [heq, List.map_id]
    exact flatten_chunks (by simpa [Nat.pow_succ, Nat.mul_comm] using hn)

private theorem valid_join {B : ℕ} {cs : List Tree} (hl : cs.length ≤ B)
    (hc : ∀ t ∈ cs, Valid B t ∧ t.keys ≠ []) : Valid B (join cs) := by
  rcases cs with _ | ⟨t, _ | ⟨u, ts⟩⟩
  · simp [join, Valid]
  · exact (hc t (by simp)).1
  · simp only [join, Valid]
    exact ⟨by simp, hl, trivial, hc⟩

private theorem valid_buildAux {B h : ℕ} {xs : List ℕ} (hn : xs.length ≤ B ^ h) :
    Valid B (buildAux B h xs) := by
  induction h generalizing xs with
  | zero => simpa [buildAux, Valid] using hn
  | succ h ih =>
    apply valid_join
    · simpa only [List.length_map] using chunks_length_le B (B ^ h) xs
    · intro t ht
      obtain ⟨ys, hy, rfl⟩ := List.mem_map.mp ht
      have hm := chunks_mem hy
      exact ⟨ih hm.2, by simpa only [keys_buildAux hm.2] using hm.1⟩

private theorem foldr_max_le {ns : List ℕ} {h : ℕ} (hs : ∀ n ∈ ns, n ≤ h) :
    ns.foldr max 0 ≤ h := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    simp only [List.foldr_cons, max_le_iff]
    exact ⟨hs n (by simp), ih (fun n hn => hs n (by simp [hn]))⟩

private theorem height_join_le {cs : List Tree} {h : ℕ} (hc : ∀ t ∈ cs, t.height ≤ h) :
    (join cs).height ≤ h + 1 := by
  rcases cs with _ | ⟨t, _ | ⟨u, ts⟩⟩
  · simp [join, height]
  · exact (hc t (by simp)).trans (Nat.le_succ h)
  · simp only [join, height]
    apply Nat.add_le_add_right _ 1
    apply foldr_max_le
    intro n hn
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn
    exact hc t ht

private theorem height_buildAux_le (B h : ℕ) (xs : List ℕ) : (buildAux B h xs).height ≤ h := by
  induction h generalizing xs with
  | zero => simp [buildAux, height]
  | succ h ih =>
    apply height_join_le
    intro t ht
    obtain ⟨ys, _, rfl⟩ := List.mem_map.mp ht
    exact ih ys

/-- Construction preserves the complete input list, including its order. -/
theorem keys_build {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) : (build B xs).keys = xs :=
  keys_buildAux (Nat.le_pow_clog hB xs.length)

/-- Construction supplies the occupancy and cached-minimum invariants. -/
theorem valid_build {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) : Valid B (build B xs) :=
  valid_buildAux (Nat.le_pow_clog hB xs.length)

/-- The explicit height bound, uniform in the branching parameter. -/
theorem height_build_le (B : ℕ) (xs : List ℕ) :
    (build B xs).height ≤ Nat.clog B xs.length :=
  height_buildAux_le B _ xs

/-- A logarithmic height bound with a constant independent of the branching parameter. -/
theorem height_build_le_log_add_one {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) :
    (build B xs).height ≤ Nat.log B xs.length + 1 :=
  (height_build_le B xs).trans
    (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self hB xs.length)))

/-- Nonempty valid trees have storage bounded uniformly in their maximum node capacity. -/
private theorem slots_add_nine_le {B : ℕ} {t : Tree} (ht : Valid B t) (hne : t.keys ≠ []) :
    t.slots + 9 ≤ 14 * t.keys.length := by
  revert ht hne
  induction t using Tree.rec
      (motive_2 := fun cs =>
        (∀ t ∈ cs, Valid B t ∧ t.keys ≠ []) →
          (cs.map slots).sum + 9 * cs.length ≤ 14 * (cs.flatMap keys).length) with
  | leaf xs =>
    intro ht hne
    simp only [Valid, keys, slots] at *
    have hp : 0 < xs.length := List.length_pos_iff.mpr hne
    omega
  | node m cs ih =>
    intro ht _
    simp only [Valid] at ht
    have hs := ih ht.2.2.2
    simp only [slots, keys]
    omega
  | nil => simp
  | cons t ts iht ihts hc =>
    have hs := iht (hc t (by simp)).1 (hc t (by simp)).2
    have hts := ihts (fun u hu => hc u (by simp [hu]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, List.flatMap_cons,
      List.length_append]
    omega

/-- Empty valid trees are empty leaves, with a tag and a reference to the empty list. -/
private theorem slots_of_keys_eq_nil {B : ℕ} {t : Tree} (ht : Valid B t) (hne : t.keys = []) :
    t.slots = 2 := by
  cases t with
  | leaf xs =>
    simp only [keys] at hne
    simp [slots, hne]
  | node m cs =>
    simp only [Valid] at ht
    have hcs : cs ≠ [] := by intro h; simp [h] at ht
    obtain ⟨u, us, rfl⟩ := List.exists_cons_of_ne_nil hcs
    have hu := (ht.2.2.2 u (by simp)).2
    simp only [keys, List.flatMap_cons, List.append_eq_nil_iff] at hne
    exact (hu hne.1).elim

/-- Total keys, child pointers, cached minima, node headers and list links use at most `14n+2`
scalar slots. The numerical constant is independent of `B`. This is a structural bound,
not a word-RAM heap encoding or a bit-space bound for unbounded natural numbers. -/
theorem slots_build_le {B : ℕ} (hB : 2 ≤ B) (xs : List ℕ) :
    (build B xs).slots ≤ 14 * xs.length + 2 := by
  have hv := valid_build hB xs
  by_cases hn : xs = []
  · have he : (build B xs).keys = [] := by simpa only [keys_build hB] using hn
    rw [slots_of_keys_eq_nil hv he, hn]
    simp
  · have he : (build B xs).keys ≠ [] := by simpa only [keys_build hB] using hn
    have hs := slots_add_nine_le hv he
    rw [keys_build hB] at hs
    omega

/-- Linear semantic node search: select the last child whose cached minimum is at most `q`.
Only the selected subtree is searched recursively. -/
def selectChild (q : ℕ) : List Tree → Option Tree
  | [] => none
  | t :: ts => (selectChild q ts).or (if t.minimum ≤ q then some t else none)

/-- Any child selected by `selectChild` belongs to the input child list. -/
theorem selectChild_mem {q : ℕ} {cs : List Tree} {t : Tree}
    (h : selectChild q cs = some t) : t ∈ cs := by
  induction cs with
  | nil => simp [selectChild] at h
  | cons u us ih =>
    simp only [selectChild] at h
    cases hs : selectChild q us with
    | none =>
      simp only [hs, Option.or] at h
      split at h
      · cases h; simp
      · contradiction
    | some v =>
      simp only [hs, Option.or, Option.some.injEq] at h
      subst v
      exact List.mem_cons_of_mem u (ih hs)

/-- Rightmost qualifying key in an input list. For sorted input this is inclusive predecessor. -/
def listPredecessor (q : ℕ) : List ℕ → Option ℕ
  | [] => none
  | x :: xs => (listPredecessor q xs).or (if x ≤ q then some x else none)

/-- Inclusive predecessor by cached-minimum routing, descending into at most one child per node.
The linear node scan is explicit and is not charged as a constant-time operation. -/
def predecessor (q : ℕ) : Tree → Option ℕ
  | .leaf xs => listPredecessor q xs
  | .node _ cs =>
    match _hs : selectChild q cs with
    | none => none
    | some t => predecessor q t
termination_by t => sizeOf t
decreasing_by
  have hm := selectChild_mem _hs
  have ht := List.sizeOf_lt_of_mem hm
  simp_wf
  omega

/-- In a valid tree, `minimum` equals the first stored key (or `0` when empty). -/
theorem minimum_eq_headD {B : ℕ} {t : Tree} (ht : Valid B t) :
    t.minimum = t.keys.headD 0 := by
  cases t with
  | leaf xs => simp [minimum, keys]
  | node m cs =>
    simp only [Valid] at ht
    simpa only [minimum, keys] using ht.2.2.1

/-- `listPredecessor` returns `none` iff every element of the list exceeds `q`. -/
theorem listPredecessor_eq_none_iff (q : ℕ) (xs : List ℕ) :
    listPredecessor q xs = none ↔ ∀ x ∈ xs, q < x := by
  induction xs with
  | nil => simp [listPredecessor]
  | cons x xs ih =>
    cases hs : listPredecessor q xs with
    | none =>
      have ht := ih.mp hs
      by_cases hx : x ≤ q
      · simp [listPredecessor, hs, Option.or, hx]
      · have hlt : q < x := by omega
        simpa [listPredecessor, hs, Option.or, hx, hlt] using ht
    | some y =>
      have ht : ¬ ∀ x ∈ xs, q < x := by
        intro hall
        have hn := ih.mpr hall
        rw [hs] at hn
        contradiction
      simp [listPredecessor, hs, Option.or, ht]

private theorem listPredecessor_append (q : ℕ) (xs ys : List ℕ) :
    listPredecessor q (xs ++ ys) = (listPredecessor q ys).or (listPredecessor q xs) := by
  induction xs with
  | nil => simp [listPredecessor]
  | cons x xs ih =>
    simp only [List.cons_append, listPredecessor, ih]
    cases listPredecessor q ys <;> cases listPredecessor q xs <;> rfl

private theorem listPredecessor_ne_none_iff {q : ℕ} {xs : List ℕ}
    (hn : xs ≠ []) (hs : xs.Pairwise (· ≤ ·)) :
    listPredecessor q xs ≠ none ↔ xs.headD 0 ≤ q := by
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hn
  simp only [List.headD_cons]
  rw [ne_eq, listPredecessor_eq_none_iff]
  constructor
  · intro h
    by_contra hx
    apply h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · exact lt_of_lt_of_le (by omega) ((List.pairwise_cons.mp hs).1 y hy)
  · intro hx h
    have := h x (by simp)
    omega

private theorem selectChild_listPredecessor (q : ℕ) (cs : List Tree)
    (hc : ∀ t ∈ cs, t.keys ≠ [] ∧ t.keys.Pairwise (· ≤ ·) ∧
      t.minimum = t.keys.headD 0) :
    (selectChild q cs).bind (fun t => listPredecessor q t.keys) =
      listPredecessor q (cs.flatMap keys) := by
  induction cs with
  | nil => simp [selectChild, listPredecessor]
  | cons t ts ih =>
    have ht := hc t (by simp)
    have hts := ih (fun u hu => hc u (by simp [hu]))
    have hgate : listPredecessor q t.keys ≠ none ↔ t.minimum ≤ q := by
      rw [ht.2.2]
      exact listPredecessor_ne_none_iff ht.1 ht.2.1
    rw [List.flatMap_cons, listPredecessor_append, ← hts]
    simp only [selectChild]
    cases hs : selectChild q ts with
    | none =>
      by_cases hm : t.minimum ≤ q
      · simp [Option.or, hm]
      · have hp := not_iff_not.mpr hgate |>.mpr hm
        simp only [not_not] at hp
        simp [Option.or, hm, hp]
    | some u =>
      have hu := (hc u (List.mem_cons_of_mem t (selectChild_mem hs)))
      have hum : u.minimum ≤ q := by
        clear hts hgate ht ih hc hu
        induction ts with
        | nil => simp [selectChild] at hs
        | cons v vs ih =>
          cases hv : selectChild q vs with
          | none =>
            simp only [selectChild, hv, Option.or] at hs
            split at hs
            · cases hs; assumption
            · contradiction
          | some z =>
            have hz : z = u := by simpa [selectChild, hv, Option.or] using hs
            subst z
            exact ih hv
      have hup : listPredecessor q u.keys ≠ none :=
        (listPredecessor_ne_none_iff hu.1 hu.2.1).mpr (by simpa only [← hu.2.2] using hum)
      cases hp : listPredecessor q u.keys with
      | none => exact (hup hp).elim
      | some p => simp [hp, Option.or]

/-- Cached-minimum routing agrees with rightmost list search on every valid ordered tree. -/
theorem predecessor_eq_listPredecessor {B : ℕ} {t : Tree} (ht : Valid B t)
    (hs : t.keys.Pairwise (· ≤ ·)) (q : ℕ) :
    predecessor q t = listPredecessor q t.keys := by
  cases heqt : t with
  | leaf xs => simp [predecessor, keys]
  | node m cs =>
    simp only [heqt, Valid] at ht
    simp only [heqt, keys] at hs ⊢
    have hsort := (List.pairwise_flatMap.mp hs).1
    have hroute := selectChild_listPredecessor q cs (fun u hu =>
      ⟨(ht.2.2.2 u hu).2, hsort u hu, minimum_eq_headD (ht.2.2.2 u hu).1⟩)
    rw [← hroute, predecessor]
    cases hchild : selectChild q cs with
    | none => rfl
    | some u =>
      simp only [Option.bind_some]
      have hu := selectChild_mem hchild
      exact predecessor_eq_listPredecessor (ht.2.2.2 u hu).1 (hsort u hu) q
termination_by sizeOf t
decreasing_by
  have hlt := List.sizeOf_lt_of_mem hu
  subst t
  simp_wf
  omega

private theorem listPredecessor_some_spec {q p : ℕ} {xs : List ℕ}
    (hs : xs.Pairwise (· ≤ ·)) (hp : listPredecessor q xs = some p) :
    p ∈ xs ∧ p ≤ q ∧ ∀ x ∈ xs, x ≤ q → x ≤ p := by
  revert hs hp
  induction xs generalizing p with
  | nil => simp [listPredecessor]
  | cons x xs ih =>
    intro hs hp
    obtain ⟨hhead, hsort⟩ := List.pairwise_cons.mp hs
    cases htail : listPredecessor q xs with
    | none =>
      have hnone := (listPredecessor_eq_none_iff q xs).mp htail
      simp only [listPredecessor, htail, Option.or] at hp
      split at hp
      · cases hp
        refine ⟨by simp, by assumption, ?_⟩
        intro y hy hyq
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_rfl
        · have := hnone y hy
          omega
      · contradiction
    | some r =>
      have heq : r = p := by simpa [listPredecessor, htail, Option.or] using hp
      subst r
      obtain ⟨hmem, hle, hmax⟩ := ih hsort htail
      refine ⟨List.mem_cons_of_mem x hmem, hle, ?_⟩
      intro y hy hyq
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hhead p hmem
      · exact hmax y hy hyq

/-- The list search returns exactly the greatest stored key not exceeding the query. -/
theorem listPredecessor_eq_some_iff {q p : ℕ} {xs : List ℕ}
    (hs : xs.Pairwise (· ≤ ·)) :
    listPredecessor q xs = some p ↔
      p ∈ xs ∧ p ≤ q ∧ ∀ x ∈ xs, x ≤ q → x ≤ p := by
  constructor
  · exact listPredecessor_some_spec hs
  · intro hp
    cases hr : listPredecessor q xs with
    | none =>
      have := (listPredecessor_eq_none_iff q xs).mp hr p hp.1
      omega
    | some r =>
      have hs := listPredecessor_some_spec hs hr
      have hpr : p = r := le_antisymm (hs.2.2 p hp.1 hp.2.1) (hp.2.2 r hs.1 hs.2.1)
      simp only [hpr]

/-- Inclusive predecessor correctness for every sorted distinct input and every natural query. -/
theorem predecessor_build_eq_some_iff {B q p : ℕ} (hB : 2 ≤ B) {xs : List ℕ}
    (hs : xs.Pairwise (· < ·)) :
    predecessor q (build B xs) = some p ↔
      p ∈ xs ∧ p ≤ q ∧ ∀ x ∈ xs, x ≤ q → x ≤ p := by
  have hle : xs.Pairwise (· ≤ ·) := hs.imp (fun h => Nat.le_of_lt h)
  rw [predecessor_eq_listPredecessor (valid_build hB xs) (by rwa [keys_build hB]),
    keys_build hB]
  exact listPredecessor_eq_some_iff hle

/-- Empty output is equivalent to having no stored key at or below the query. -/
theorem predecessor_build_eq_none_iff {B q : ℕ} (hB : 2 ≤ B) {xs : List ℕ}
    (hs : xs.Pairwise (· < ·)) :
    predecessor q (build B xs) = none ↔ ∀ x ∈ xs, q < x := by
  have hle : xs.Pairwise (· ≤ ·) := hs.imp (fun h => Nat.le_of_lt h)
  rw [predecessor_eq_listPredecessor (valid_build hB xs) (by rwa [keys_build hB]),
    keys_build hB]
  exact listPredecessor_eq_none_iff q xs

end Tree
end Cslib.Algorithms.Lean.FusionTree
