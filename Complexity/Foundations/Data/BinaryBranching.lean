/-
Copyright (c) 2026 Samuel Schlesinger, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Complexity.Foundations.Combinatorics.SmallSubsets

/-!
# Binary branching

A *binary branching* `T : BinaryBranching σ` marks some states as leaves (`T.IsLeaf`) and gives
every state a `false` child and a `true` child (`T.next`). A word `w : List Bool` names the state
reached by following its branches (`walk`). It is a *node word* when its proper prefixes reach
inner states (`IsNodeWord`), and a *leaf word* when moreover it reaches a leaf (`IsLeafWord`).
Leaf words are determined by the positions of their `true` branches
(`IsLeafWord.eq_of_getD_eq`), so leaf words of length at most `Λ` with at most `ρ` `true`
branches number at most `∑_{j ≤ ρ} (Λ choose j)` (`card_le_sum_choose_of_isLeafWord`).

When no branch is infinite (`Terminating`, for instance when a measure decreases from every inner
state to its children, `Terminating.of_lt`), every node word extends to a leaf word. A depth-first
search (`searchStep`) keeps a stack of states and an accumulator, updated by an arbitrary function
at each leaf. Started from a state, it takes fewer than twice as many steps as the state has
leaves, and its accumulator becomes the fold of the update over a duplicate-free list of all leaf
words; meanwhile its stack holds at most `h + 1` states of the tree when the leaf words have length
at most `h` (`exists_iterate_searchStep`).

The sparsification procedures of Impagliazzo, Paturi and Zane and of counting sparsification are
binary branchings whose leaves are the sparse clause sets.

## Main definitions

* `Cslib.BinaryBranching`: leaves and children on a type of states.
* `Cslib.BinaryBranching.walk`, `.IsNodeWord`, `.IsLeafWord`: the tree of a state.
* `Cslib.BinaryBranching.walkSeq`: follow a branch sequence until a leaf.
* `Cslib.BinaryBranching.searchStep`: one step of depth-first search.
* `Cslib.BinaryBranching.Terminating`: every branch ends at a leaf.

## Main results

* `Cslib.BinaryBranching.IsLeafWord.eq_of_getD_eq`: leaf words are determined by their `true`
  branches.
* `Cslib.BinaryBranching.card_le_sum_choose_of_isLeafWord`: few short leaf words with few `true`
  branches.
* `Cslib.BinaryBranching.exists_iterate_searchStep`: depth-first search folds over the leaves.
-/

@[expose] public section

namespace Cslib

open Finset

/-- A *binary branching* on states `σ`: some states are leaves, and every state has a `false`
child and a `true` child, of which only those of inner states matter. -/
structure BinaryBranching (σ : Type*) where
  /-- The leaves. -/
  IsLeaf : σ → Prop
  /-- The `false` child and the `true` child of a state. -/
  next : σ → Bool → σ

namespace BinaryBranching

variable {σ α : Type*} (T : BinaryBranching σ)

/-- The state reached along a word of branches. -/
def walk : σ → List Bool → σ
  | s, [] => s
  | s, b :: w => walk (T.next s b) w

/-- A *node word*: its proper prefixes reach inner states. -/
def IsNodeWord : σ → List Bool → Prop
  | _, [] => True
  | s, b :: w => ¬ T.IsLeaf s ∧ IsNodeWord (T.next s b) w

/-- A *leaf word*: its proper prefixes reach inner states and it reaches a leaf. -/
def IsLeafWord : σ → List Bool → Prop
  | s, [] => T.IsLeaf s
  | s, b :: w => ¬ T.IsLeaf s ∧ IsLeafWord (T.next s b) w

/-- Follow the branch sequence `f` for at most `n` steps, stopping at a leaf. -/
noncomputable def walkSeq : ℕ → σ → (ℕ → Bool) → σ
  | 0, s, _ => s
  | n + 1, s, f =>
    open Classical in
    if T.IsLeaf s then s else walkSeq n (T.next s (f 0)) fun i => f (i + 1)

/-- One step of the depth-first search, on a stack of states and an accumulator: a leaf on top is
popped and the accumulator is updated with it by `f`; an inner state on top is replaced by its
`false` and `true` children. -/
noncomputable def searchStep (f : α → σ → α) : List σ × α → List σ × α
  | ([], acc) => ([], acc)
  | (s :: rest, acc) =>
    open Classical in
    if T.IsLeaf s then (rest, f acc s) else (T.next s false :: T.next s true :: rest, acc)

/-- Every branch ends at a leaf: the relation between the children of an inner state and the
state is well-founded. -/
def Terminating : Prop :=
  WellFounded fun t s => ¬ T.IsLeaf s ∧ ∃ b, T.next s b = t

variable {T}

/-! ### Termination -/

/-- A branching terminates when a natural-number measure decreases from every inner state to its
children. -/
theorem Terminating.of_lt (μ : σ → ℕ) (hμ : ∀ s, ¬ T.IsLeaf s → ∀ b, μ (T.next s b) < μ s) :
    T.Terminating :=
  Subrelation.wf (fun ⟨hs, b, hb⟩ => hb ▸ hμ _ hs b) (InvImage.wf μ wellFounded_lt)

/-- **Induction on a terminating branching.** A property of the leaves that passes from the two
children of every inner state to the state holds for every state. -/
@[elab_as_elim]
theorem Terminating.induction (hT : T.Terminating) {motive : σ → Prop}
    (leaf : ∀ s, T.IsLeaf s → motive s)
    (node : ∀ s, ¬ T.IsLeaf s → (∀ b, motive (T.next s b)) → motive s) (s : σ) : motive s :=
  WellFounded.induction hT s fun s ih => by
    by_cases hs : T.IsLeaf s
    · exact leaf s hs
    · exact node s hs fun b => ih _ ⟨hs, b, rfl⟩

/-! ### Words -/

theorem walk_append (s : σ) (u v : List Bool) : T.walk s (u ++ v) = T.walk (T.walk s u) v := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (T.next s a)

theorem walk_take_succ (s : σ) (w : List Bool) {i : ℕ} (hi : i < w.length) :
    T.walk s (w.take (i + 1)) = T.next (T.walk s (w.take i)) (w.getD i false) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, walk_append,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  rfl

/-- Every leaf word is a node word. -/
theorem IsLeafWord.isNodeWord {s : σ} {w : List Bool} (h : T.IsLeafWord s w) :
    T.IsNodeWord s w := by
  induction w generalizing s with
  | nil => trivial
  | cons b w ih => exact ⟨h.1, ih h.2⟩

/-- Walking along a leaf word reaches a leaf. -/
theorem IsLeafWord.isLeaf_walk {s : σ} {w : List Bool} (h : T.IsLeafWord s w) :
    T.IsLeaf (T.walk s w) := by
  induction w generalizing s with
  | nil => exact h
  | cons b w ih => exact ih h.2

/-- The only leaf word of a leaf is the empty word. -/
theorem IsLeafWord.eq_nil {s : σ} (hs : T.IsLeaf s) {w : List Bool} (hw : T.IsLeafWord s w) :
    w = [] := by
  cases w with
  | nil => rfl
  | cons b w => exact absurd hs hw.1

/-- A leaf word is a node word reaching a leaf. -/
theorem isLeafWord_iff {s : σ} {w : List Bool} :
    T.IsLeafWord s w ↔ T.IsNodeWord s w ∧ T.IsLeaf (T.walk s w) := by
  induction w generalizing s with
  | nil => exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  | cons b w ih =>
    exact ⟨fun h => ⟨⟨h.1, (ih.mp h.2).1⟩, (ih.mp h.2).2⟩, fun h => ⟨h.1.1, ih.mpr ⟨h.1.2, h.2⟩⟩⟩

theorem IsNodeWord.append {s : σ} {u v : List Bool} (hu : T.IsNodeWord s u)
    (hv : T.IsNodeWord (T.walk s u) v) : T.IsNodeWord s (u ++ v) := by
  induction u generalizing s with
  | nil => exact hv
  | cons b u ih => exact ⟨hu.1, ih hu.2 hv⟩

/-- The proper prefixes of a node word reach inner states. -/
theorem IsNodeWord.not_isLeaf_take {s : σ} {w : List Bool} (h : T.IsNodeWord s w) :
    ∀ i < w.length, ¬ T.IsLeaf (T.walk s (w.take i)) := by
  induction w generalizing s with
  | nil => intro i hi; simp at hi
  | cons b w ih =>
    intro i hi
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [List.take_succ_cons, walk]
      exact ih h.2 i (by simpa using hi)

/-- **Leaf words are determined by their `true` branches.** Two leaf words with `true` branches
at the same positions are equal. -/
theorem IsLeafWord.eq_of_getD_eq {s : σ} {w w' : List Bool} (hw : T.IsLeafWord s w)
    (hw' : T.IsLeafWord s w') (h : ∀ i, w.getD i false = w'.getD i false) : w = w' := by
  induction w generalizing s w' with
  | nil =>
    cases w' with
    | nil => rfl
    | cons b' w' => exact absurd hw hw'.1
  | cons b w ih =>
    cases w' with
    | nil => exact absurd hw' hw.1
    | cons b' w' =>
      have hb : b = b' := by simpa using h 0
      subst hb
      rw [ih hw.2 hw'.2 fun i => by simpa using h (i + 1)]

/-- Following a branch sequence ends at the state of some node word. -/
theorem exists_isNodeWord_walkSeq (n : ℕ) (s : σ) (f : ℕ → Bool) :
    ∃ w, T.IsNodeWord s w ∧ T.walkSeq n s f = T.walk s w := by
  induction n generalizing s f with
  | zero => exact ⟨[], trivial, rfl⟩
  | succ n ih =>
    unfold walkSeq
    split_ifs with hs
    · exact ⟨[], trivial, rfl⟩
    · obtain ⟨w, hw, heq⟩ := ih (T.next s (f 0)) fun i => f (i + 1)
      exact ⟨f 0 :: w, ⟨hs, hw⟩, heq⟩

/-- Following a branch sequence that agrees with a leaf word, for at least as many steps, ends at
that leaf. -/
theorem walkSeq_eq_walk {s : σ} {w : List Bool} (hw : T.IsLeafWord s w)
    {f : ℕ → Bool} (hf : ∀ i < w.length, f i = w.getD i false) {n : ℕ} (hn : w.length ≤ n) :
    T.walkSeq n s f = T.walk s w := by
  induction w generalizing s f n with
  | nil =>
    cases n with
    | zero => rfl
    | succ n => simp only [walkSeq, walk]; exact ite_eq_left hw
  | cons b w ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only [List.length_cons] at hn; omega⟩
    simp only [walkSeq, walk]
    rw [ite_eq_right hw.1]
    have hf0 : f 0 = b := by simpa using hf 0 (by simp)
    rw [hf0]
    refine ih hw.2 (fun i hi => ?_) (by simpa using hn)
    simpa using hf (i + 1) (by simpa using hi)

/-- **Few leaf words.** Leaf words of length at most `Λ` with at most `ρ` `true` branches number
at most `∑_{j ≤ ρ} (Λ choose j)`. -/
theorem card_le_sum_choose_of_isLeafWord {s : σ} {W : Finset (List Bool)}
    (hW : ∀ w ∈ W, T.IsLeafWord s w) {Λ ρ : ℕ} (hlen : ∀ w ∈ W, w.length ≤ Λ)
    (hρ : ∀ w ∈ W, ((range w.length).filter fun i => w.getD i false = true).card ≤ ρ) :
    W.card ≤ ∑ j ∈ range (ρ + 1), Λ.choose j := by
  classical
  let pos (w : List Bool) : Finset ℕ := (range Λ).filter fun i => w.getD i false = true
  have hpos (w : List Bool) (hw : w.length ≤ Λ) :
      pos w = (range w.length).filter fun i => w.getD i false = true := by
    ext i
    simp only [pos, mem_filter, mem_range]
    refine ⟨fun ⟨_, hi⟩ => ⟨?_, hi⟩, fun ⟨hi, h⟩ => ⟨by omega, h⟩⟩
    by_contra hge
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hi
    exact Bool.false_ne_true hi
  have hinj : Set.InjOn pos W := by
    intro w hw w' hw' h
    refine (hW w hw).eq_of_getD_eq (hW w' hw') fun i => ?_
    by_cases hi : i < Λ
    · have := congrArg (i ∈ ·) h
      simp only [pos, mem_filter, mem_range, hi, true_and, eq_iff_iff] at this
      cases hwi : w.getD i false <;> cases hw'i : w'.getD i false <;> simp_all
    · have hl := hlen w hw
      have hl' := hlen w' hw'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  calc W.card = (W.image pos).card := (card_image_of_injOn hinj).symm
    _ ≤ #{S ∈ (range Λ).powerset | #S ≤ ρ} := card_le_card fun S hS => by
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hS
        exact mem_filter.mpr ⟨mem_powerset.mpr (filter_subset _ _), hpos w (hlen w hw) ▸ hρ w hw⟩
    _ = ∑ j ∈ range (ρ + 1), Λ.choose j := by
        rw [card_filter_powerset_card_le_eq_sum_choose, card_range]

/-! ### Terminating branchings -/

section Terminating

variable (hT : T.Terminating)
include hT

/-- Every state has a leaf word. -/
theorem exists_isLeafWord (s : σ) : ∃ w, T.IsLeafWord s w := by
  induction s using Terminating.induction hT with
  | leaf s hs => exact ⟨[], hs⟩
  | node s hs ih =>
    obtain ⟨w, hw⟩ := ih false
    exact ⟨false :: w, hs, hw⟩

/-- Every node word extends to a leaf word. -/
theorem IsNodeWord.exists_isLeafWord_append {s : σ} {w : List Bool} (h : T.IsNodeWord s w) :
    ∃ u, T.IsLeafWord s (w ++ u) := by
  obtain ⟨u, hu⟩ := exists_isLeafWord hT (T.walk s w)
  rw [isLeafWord_iff] at hu
  exact ⟨u, isLeafWord_iff.mpr ⟨h.append hu.1, by rw [walk_append]; exact hu.2⟩⟩

omit hT in
/-- At an inner state, the leaf words are those of the two children after their branch. -/
private theorem nodup_and_mem_iff_isLeafWord {s : σ} (hs : ¬ T.IsLeaf s)
    {L₀ L₁ : List (List Bool)} (hnd₀ : L₀.Nodup) (hnd₁ : L₁.Nodup)
    (hL₀ : ∀ w, w ∈ L₀ ↔ T.IsLeafWord (T.next s false) w)
    (hL₁ : ∀ w, w ∈ L₁ ↔ T.IsLeafWord (T.next s true) w) :
    (L₀.map (false :: ·) ++ L₁.map (true :: ·)).Nodup ∧
      ∀ w, w ∈ L₀.map (false :: ·) ++ L₁.map (true :: ·) ↔ T.IsLeafWord s w := by
  refine ⟨(hnd₀.map List.cons_injective).append (hnd₁.map List.cons_injective)
    (List.disjoint_left.mpr fun w hw₀ hw₁ => ?_), fun w => ?_⟩
  · obtain ⟨u₀, -, rfl⟩ := List.mem_map.mp hw₀
    obtain ⟨u₁, -, hu₁⟩ := List.mem_map.mp hw₁
    exact Bool.false_ne_true (List.head_eq_of_cons_eq hu₁).symm
  · cases w with
    | nil => simp [IsLeafWord, hs]
    | cons b u => cases b <;> simp [IsLeafWord, hs, hL₀, hL₁]

/-- **Depth-first search.** Started from a state `s` above a stack `rest`, the search takes `N`
steps, fewer than twice the number of leaves of `s`, to return to `rest`. Meanwhile it folds the
update `f` over the leaves of `s`, in the order of a duplicate-free list `L` of the leaf words of
`s`: after each step the accumulator is the fold over a prefix of `L`. If the leaf words of `s`
have length at most `h`, the stack above `rest` consists of at most `h + 1` states of the tree of
`s`, reached along node words of length at most `h`. -/
theorem exists_iterate_searchStep (f : α → σ → α) (s : σ) {h : ℕ}
    (hh : ∀ w, T.IsLeafWord s w → w.length ≤ h) :
    ∃ L : List (List Bool), L.Nodup ∧ (∀ w, w ∈ L ↔ T.IsLeafWord s w) ∧
      ∃ N, N + 1 ≤ 2 * L.length ∧ ∀ rest acc,
        (T.searchStep f)^[N] (s :: rest, acc) = (rest, (L.map (T.walk s)).foldl f acc) ∧
        ∀ i ≤ N, ∃ stk L', L' <+: L ∧
          (T.searchStep f)^[i] (s :: rest, acc) = (stk ++ rest, (L'.map (T.walk s)).foldl f acc) ∧
          stk.length ≤ h + 1 ∧
          ∀ t ∈ stk, ∃ w, T.IsNodeWord s w ∧ w.length ≤ h ∧ T.walk s w = t := by
  classical
  induction s using Terminating.induction hT generalizing h with
  | leaf s hs =>
    refine ⟨[[]], List.nodup_singleton _, fun w => ⟨fun hw => ?_, fun hw => ?_⟩, 1, by simp,
      fun rest acc => ⟨by simp [searchStep, hs, walk], fun i hi => ?_⟩⟩
    · rw [List.mem_singleton.mp hw]
      exact hs
    · rw [hw.eq_nil hs]
      exact List.mem_singleton_self _
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
      · exact ⟨[s], [], List.nil_prefix, rfl, by simp,
          fun t ht => ⟨[], trivial, Nat.zero_le h, (List.mem_singleton.mp ht).symm⟩⟩
      · exact ⟨[], [[]], List.prefix_rfl, by simp [searchStep, hs, walk], by simp, by simp⟩
  | node s hs ih =>
    -- the two subtrees, one after the other
    have hh' (b : Bool) : ∀ w, T.IsLeafWord (T.next s b) w → w.length ≤ h - 1 := fun w hw => by
      have := hh (b :: w) ⟨hs, hw⟩
      simp only [List.length_cons] at this
      omega
    obtain ⟨u, hu⟩ := exists_isLeafWord hT s
    have hh1 : 1 ≤ h := by
      cases u with
      | nil => exact absurd hu hs
      | cons b u => have := hh _ hu; simp only [List.length_cons] at this; omega
    obtain ⟨L₀, hnd₀, hL₀, N₀, hN₀, h₀⟩ := ih false (hh' false)
    obtain ⟨L₁, hnd₁, hL₁, N₁, hN₁, h₁⟩ := ih true (hh' true)
    have hstep (rest : List σ) (acc : α) : T.searchStep f (s :: rest, acc) =
        (T.next s false :: T.next s true :: rest, acc) := by
      simp only [searchStep, hs, ↓reduceIte]
    obtain ⟨hnd, hL⟩ := nodup_and_mem_iff_isLeafWord hs hnd₀ hnd₁ hL₀ hL₁
    refine ⟨_, hnd, hL, N₁ + (N₀ + 1), by simp only [List.length_append, List.length_map]; omega,
      fun rest acc => ⟨?_, fun i hi => ?_⟩⟩
    · rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep, (h₀ _ acc).1,
        (h₁ _ _).1, List.map_append, List.foldl_append, List.map_map, List.map_map]
      rfl
    · -- the stack: the root, then the `false` subtree above the `true` child, then the `true`
      -- subtree
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact ⟨[s], [], List.nil_prefix, rfl, by simp,
          fun t ht => ⟨[], trivial, Nat.zero_le h, (List.mem_singleton.mp ht).symm⟩⟩
      by_cases hi₀ : i ≤ N₀ + 1
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        obtain ⟨stk, L', hL', heq, hlen, hmem⟩ := (h₀ (T.next s true :: rest) acc).2 j (by omega)
        refine ⟨stk ++ [T.next s true], L'.map (false :: ·),
          (hL'.map _).trans (List.prefix_append _ _), ?_, ?_, fun t ht => ?_⟩
        · rw [Function.iterate_succ_apply, hstep, heq, List.append_assoc, List.singleton_append,
            List.map_map]
          rfl
        · simp only [List.length_append, List.length_singleton]
          omega
        · rcases List.mem_append.mp ht with ht | ht
          · obtain ⟨w, hw, hwlen, rfl⟩ := hmem t ht
            exact ⟨false :: w, ⟨hs, hw⟩, by simp only [List.length_cons]; omega, rfl⟩
          · exact ⟨[true], ⟨hs, trivial⟩, by simp only [List.length_singleton]; omega,
              (List.mem_singleton.mp ht).symm⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = j + (N₀ + 1) := ⟨i - (N₀ + 1), by omega⟩
        obtain ⟨stk, L', hL', heq, hlen, hmem⟩ :=
          (h₁ rest ((L₀.map (T.walk (T.next s false))).foldl f acc)).2 j (by omega)
        refine ⟨stk, L₀.map (false :: ·) ++ L'.map (true :: ·),
          (List.prefix_append_right_inj _).mpr (hL'.map _), ?_, by omega, fun t ht => ?_⟩
        · rw [Function.iterate_add_apply, Function.iterate_succ_apply, hstep, (h₀ _ acc).1, heq,
            List.map_append, List.foldl_append, List.map_map, List.map_map]
          rfl
        · obtain ⟨w, hw, hwlen, rfl⟩ := hmem t ht
          exact ⟨true :: w, ⟨hs, hw⟩, by simp only [List.length_cons]; omega, rfl⟩

end Terminating

end BinaryBranching

end Cslib
