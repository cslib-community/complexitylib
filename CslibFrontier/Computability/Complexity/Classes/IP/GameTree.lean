/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Evaluating a game tree with an explicit stack

A game tree alternates a sum over the messages and a maximum over the replies. The value of a node
with `n + 1` rounds to go is its leaf value plus, for every message, the largest value over the
replies of the child reached by the message and the reply; a node with no rounds to go has its leaf
value (`Cslib.Complexity.GameTree.value`). The messages and the replies are the first `N` iterates
`next^[i] first` of an enumeration, whose last one `last` recognizes, and a node is identified by
the messages and replies leading to it, the most recent first. Every value is capped at `cap`, so
that all numbers stay at most `cap`; the cap does not change values that are at most `cap`.

The evaluator (`Cslib.Complexity.GameTree.step`) is the depth-first traversal with an explicit
stack. A frame stores the current message and reply of a node, the capped sum over the earlier
messages, which starts at the leaf value, and the maximum over the earlier replies to the current
message. A node with `n` rounds to go returns its value to the same stack after
`Cslib.Complexity.GameTree.time N n` steps (`Cslib.Complexity.GameTree.iterate_step_node`), at
most `(N + 1) ^ (2 * n + 1)` (`Cslib.Complexity.GameTree.time_le`); the evaluation from the empty
stack then stays put (`Cslib.Complexity.GameTree.iterate_step_eval`). Along the way the stack holds
at most `D` frames, the depth of the root, each storing two iterates and two numbers at most `cap`
(`Cslib.Complexity.GameTree.Good`, `Cslib.Complexity.GameTree.good_iterate_step`). Thus the retained
state has size polynomial in `D`, the size of the iterates and the size of `cap`. Overall time and
space bounds also require resource bounds for the leaf, successor and final-element callbacks;
the step count alone does not bound their cost. The certified specialization in `IP/PSPACE`
supplies these bounds for evaluating the optimal prover in the proof of `IP ⊆ PSPACE`
[Arora and Barak, Chapter 8][AroraBarak09].

## Main definitions

* `Cslib.Complexity.GameTree.value`: the value of a node.
* `Cslib.Complexity.GameTree.step`: one step of the evaluator.
* `Cslib.Complexity.GameTree.time`: the number of steps of an evaluation.
* `Cslib.Complexity.GameTree.Good`: the invariant bounding the states.

## Main results

* `Cslib.Complexity.GameTree.iterate_step_node`: a node returns its value.
* `Cslib.Complexity.GameTree.iterate_step_eval`: the evaluation from the empty stack.
* `Cslib.Complexity.GameTree.time_le`: the number of steps.
* `Cslib.Complexity.GameTree.good_iterate_step`: the states stay small.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity.GameTree

open Finset

variable {X : Type} (D N cap : ℕ) (first : X) (next : X → X) (last : X → Bool)
  (leaf : List (X × X) → ℕ)

/-- A frame: the current message and reply, the capped sum over the earlier messages, and the
maximum over the earlier replies to the current message. -/
abbrev Frame (X : Type) := X × X × ℕ × ℕ

/-- The messages and replies leading to the node of a stack, the most recent first. -/
def history (st : List (Frame X)) : List (X × X) := st.map fun f => (f.1, f.2.1)

@[simp] theorem history_nil : history ([] : List (Frame X)) = [] := rfl

@[simp] theorem history_cons (f : Frame X) (st : List (Frame X)) :
    history (f :: st) = (f.1, f.2.1) :: history st := rfl

@[simp] theorem length_history (st : List (Frame X)) : (history st).length = st.length :=
  List.length_map _

/-- The value of a node with `n` rounds to go: the leaf value plus, for every message, the largest
value over the replies of the child, capped at `cap`. -/
def value : ℕ → List (X × X) → ℕ
  | 0, h => min cap (leaf h)
  | n + 1, h => min cap (leaf h + ∑ i ∈ range N, (range N).sup fun j =>
      value n ((next^[i] first, next^[j] first) :: h))

/-- **One step of the evaluator.** Without a value to return, a node at depth `D` returns its leaf
value, and any other node pushes a frame for its first message and reply. A value returned into a
frame updates the maximum, and moves on to the next reply; after the last reply, it adds the
maximum to the sum and moves on to the next message; after the last message, it pops the frame and
returns the sum. A value returned into the empty stack is a fixed point. -/
def step : List (Frame X) × Option ℕ → List (Frame X) × Option ℕ
  | (st, none) =>
    if st.length = D then (st, some (min cap (leaf (history st))))
    else ((first, first, min cap (leaf (history st)), 0) :: st, none)
  | ([], some v) => ([], some v)
  | ((u, w, s, a) :: st, some v) =>
    if last w then
      if last u then (st, some (min cap (s + max a v)))
      else ((next u, first, min cap (s + max a v), 0) :: st, none)
    else ((u, next w, s, max a v) :: st, none)

/-- The number of steps to evaluate a node with `n` rounds to go. -/
def time : ℕ → ℕ
  | 0 => 1
  | n + 1 => 1 + N * N * (time n + 1)

variable {D N cap first next last leaf}

/-! ### Correctness -/

variable (N cap first next leaf) in
/-- The capped sum over the first `i` messages, starting at the leaf value. -/
private def partialSum (n : ℕ) (h : List (X × X)) (i : ℕ) : ℕ :=
  min cap (leaf h + ∑ a ∈ range i, (range N).sup fun j =>
    value N cap first next leaf n ((next^[a] first, next^[j] first) :: h))

variable (N cap first next leaf) in
/-- The maximum over the first `j` replies to the message `i`. -/
private def partialMax (n : ℕ) (h : List (X × X)) (i j : ℕ) : ℕ :=
  (range j).sup fun b => value N cap first next leaf n ((next^[i] first, next^[b] first) :: h)

private theorem min_cap_add (a b : ℕ) : min cap (min cap a + b) = min cap (a + b) := by
  lia

/-- A value returned into the empty stack is a fixed point. -/
private theorem step_nil_some (v : ℕ) : step D cap first next last leaf ([], some v) =
    ([], some v) := rfl

section Correctness

variable (hN : 0 < N) (hlast : ∀ i < N, last (next^[i] first) = decide (i + 1 = N))
include hN hlast

/-- **A node returns its value** after `time N n` steps, to the same stack. -/
theorem iterate_step_node (n : ℕ) (st : List (Frame X)) (hst : st.length + n = D) :
    (step D cap first next last leaf)^[time N n] (st, none) =
      (st, some (value N cap first next leaf n (history st))) := by
  induction n generalizing st with
  | zero =>
    simp only [time, Function.iterate_one, step, show st.length = D by lia, ite_true]
    rfl
  | succ n ih =>
    set F := step D cap first next last leaf
    set T := time N n + 1 with hT
    set S := partialSum N cap first next leaf n (history st)
    set M := partialMax N cap first next leaf n (history st)
    -- one reply: the child returns its value, which updates the maximum and moves on
    have hreply (i j : ℕ) (hi : i < N) (hj : j < N) :
        F^[T] ((next^[i] first, next^[j] first, S i, M i j) :: st, none) =
          if j + 1 < N then ((next^[i] first, next^[j + 1] first, S i, M i (j + 1)) :: st, none)
          else if i + 1 < N then ((next^[i + 1] first, next^[0] first, S (i + 1), M (i + 1) 0) ::
            st, none)
          else (st, some (S N)) := by
      rw [Function.iterate_succ_apply', ih _ (by simp only [List.length_cons]; lia)]
      have hmax : max (M i j) (value N cap first next leaf n
          ((next^[i] first, next^[j] first) :: history st)) = M i (j + 1) := by
        simp only [M, partialMax, range_add_one, sup_insert]
        exact max_comm _ _
      simp only [history_cons, F, step, hlast i hi, hlast j hj, decide_eq_true_eq]
      rw [hmax]
      by_cases hj' : j + 1 < N
      · rw [ite_eq_right (by lia : ¬ j + 1 = N), ite_eq_left hj',
          ← Function.iterate_succ_apply' next]
      · have hjN : j + 1 = N := by lia
        have hsum : min cap (S i + M i (j + 1)) = S (i + 1) := by
          simp only [S, partialSum, min_cap_add, sum_range_succ, M, partialMax, hjN, add_assoc]
        rw [ite_eq_left hjN, ite_eq_right hj', hsum]
        by_cases hi' : i + 1 < N
        · rw [ite_eq_right (by lia : ¬ i + 1 = N), ite_eq_left hi',
            ← Function.iterate_succ_apply' next]
          simp [M, partialMax]
        · rw [ite_eq_left (by lia : i + 1 = N), ite_eq_right hi', show i + 1 = N by lia]
    -- the replies to one message
    have hmessage (i : ℕ) (hi : i < N) (j : ℕ) (hj : j < N) :
        F^[j * T] ((next^[i] first, next^[0] first, S i, M i 0) :: st, none) =
          ((next^[i] first, next^[j] first, S i, M i j) :: st, none) := by
      induction j with
      | zero => rw [Nat.zero_mul]; rfl
      | succ j ihj =>
        rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ihj (by lia),
          hreply i j hi (by lia),
          ite_eq_left hj]
    have hmessages (i : ℕ) (hi : i < N) :
        F^[N * T] ((next^[i] first, next^[0] first, S i, M i 0) :: st, none) =
          if i + 1 < N then ((next^[i + 1] first, next^[0] first, S (i + 1), M (i + 1) 0) ::
            st, none)
          else (st, some (S N)) := by
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by lia⟩
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, hmessage i hi N' (by lia),
        hreply i N' hi (by lia), ite_eq_right (by lia)]
    -- all the messages
    have hall (i : ℕ) (hi : i < N) :
        F^[i * (N * T)] ((next^[0] first, next^[0] first, S 0, M 0 0) :: st, none) =
          ((next^[i] first, next^[0] first, S i, M i 0) :: st, none) := by
      induction i with
      | zero => rw [Nat.zero_mul]; rfl
      | succ i ihi =>
        rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ihi (by lia),
          hmessages i (by lia),
          ite_eq_left hi]
    have hstart : F (st, none) = ((next^[0] first, next^[0] first, S 0, M 0 0) :: st, none) := by
      simp only [F, step, show st.length ≠ D by lia, ite_false]
      simp [S, partialSum, M, partialMax]
    have htime : time N (n + 1) = N * T + (N - 1) * (N * T) + 1 := by
      rw [hT]
      rcases Nat.exists_eq_succ_of_ne_zero hN.ne' with ⟨N', rfl⟩
      simp only [time, Nat.succ_sub_one, Nat.succ_eq_add_one]
      ring
    rw [htime, Function.iterate_succ_apply, hstart, Function.iterate_add_apply,
      hall (N - 1) (by lia), hmessages (N - 1) (by lia), ite_eq_right (by lia)]
    rfl

/-- **The evaluation from the empty stack** returns the value of the root within `time N D` steps
and stays put afterwards. -/
theorem iterate_step_eval {K : ℕ} (hK : time N D ≤ K) :
    (step D cap first next last leaf)^[K] ([], none) =
      ([], some (value N cap first next leaf D [])) := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [Nat.add_comm, Function.iterate_add_apply, iterate_step_node hN hlast D [] (by simp),
    history_nil, Function.iterate_fixed (step_nil_some (D := D) (cap := cap) (first := first)
      (next := next) (last := last) (leaf := leaf) _)]

end Correctness

/-- The evaluation of a node with `n` rounds to go takes at most `(N + 1) ^ (2 * n + 1)` steps. -/
theorem time_le (n : ℕ) : time N n ≤ (N + 1) ^ (2 * n + 1) := by
  induction n with
  | zero => simp [time]
  | succ n ih =>
    have h1 : 1 ≤ (N + 1) ^ (2 * n + 1) := Nat.one_le_pow _ _ (Nat.succ_pos N)
    have h2 : N + 1 ≤ (N + 1) ^ (2 * n + 1) :=
      Nat.le_self_pow (by lia) (N + 1)
    calc time N (n + 1) = 1 + N * N * (time N n + 1) := rfl
      _ ≤ 1 + N * N * ((N + 1) ^ (2 * n + 1) + 1) := by gcongr
      _ ≤ (N + 1) ^ 2 * (N + 1) ^ (2 * n + 1) := by
        have := Nat.mul_le_mul_left (2 * N) h2
        nlinarith
      _ = (N + 1) ^ (2 * (n + 1) + 1) := by ring

/-! ### Bounds on the states -/

variable (D cap) in
/-- The invariant of the evaluation: at most `D` frames, whose messages and replies satisfy `P`,
and all numbers at most `cap`. -/
structure Good (P : X → Prop) (state : List (Frame X) × Option ℕ) : Prop where
  /-- At most `D` frames. -/
  length : state.1.length ≤ D
  /-- The frames store messages and replies satisfying `P`, and numbers at most `cap`. -/
  frames : ∀ f ∈ state.1, P f.1 ∧ P f.2.1 ∧ f.2.2.1 ≤ cap ∧ f.2.2.2 ≤ cap
  /-- The returned value is at most `cap`. -/
  value : ∀ v ∈ state.2, v ≤ cap

/-- A step preserves the invariant. -/
private theorem Good.step {P : X → Prop} (hfirst : P first) (hnext : ∀ x, P x → P (next x))
    {state : List (Frame X) × Option ℕ} (h : Good D cap P state) :
    Good D cap P (step D cap first next last leaf state) := by
  obtain ⟨st, _ | v⟩ := state
  · simp only [GameTree.step]
    split_ifs with hD
    · exact ⟨h.length, h.frames, by simp⟩
    · refine ⟨by simp only [List.length_cons]; have := h.length; lia, ?_, by simp⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨hfirst, hfirst, min_le_left _ _, Nat.zero_le _⟩
      · exact h.frames f hf
  · obtain _ | ⟨⟨u, w, s, a⟩, st⟩ := st
    · exact h
    have hv : v ≤ cap := h.value v rfl
    have hf0 := h.frames _ (List.mem_cons_self ..)
    have hrest : ∀ f ∈ st, P f.1 ∧ P f.2.1 ∧ f.2.2.1 ≤ cap ∧ f.2.2.2 ≤ cap :=
      fun f hf => h.frames f (List.mem_cons_of_mem _ hf)
    have hlen : st.length ≤ D := by
      have := h.length
      simp only [List.length_cons] at this
      lia
    simp only [GameTree.step]
    split_ifs
    · exact ⟨hlen, hrest, by simp⟩
    · refine ⟨by simpa using h.length, ?_, by simp⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨hnext _ hf0.1, hfirst, min_le_left _ _, Nat.zero_le _⟩
      · exact hrest f hf
    · refine ⟨by simpa using h.length, ?_, by simp⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact ⟨hf0.1, hnext _ hf0.2.1, hf0.2.2.1, max_le hf0.2.2.2 hv⟩
      · exact hrest f hf

/-- **The states stay small**: every state of the evaluation from the empty stack satisfies the
invariant. -/
theorem good_iterate_step {P : X → Prop} (hfirst : P first) (hnext : ∀ x, P x → P (next x))
    (k : ℕ) : Good D cap P ((step D cap first next last leaf)^[k] ([], none)) := by
  induction k with
  | zero => exact ⟨by simp, by simp, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact ih.step hfirst hnext

end Cslib.Complexity.GameTree
