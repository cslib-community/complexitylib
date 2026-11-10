/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.Savitch
public import CslibFrontier.Foundations.Data.BitString.Counter

/-!
# Following a walk by Savitch's midpoint recursion

Savitch's midpoint recursion (`Cslib.Reachability.reach`) decides whether `v` is reachable from `u`
within `2 ^ d` steps between words of width `w`. This file turns the recursion into a walk that
visits the vertices of such a path in order, one per step, holding only a stack of pending targets
with their levels.

A state of the walk (`Cslib.Reachability.Walk.State`) is the current vertex and the stack. A target
at level `0` is one step away: the walk moves to it and pops it. A target `t` at level `i + 1` is
split at the midpoint `m` of the current vertex and `t` (`Cslib.Reachability.Walk.midpoint`): the
walk replaces it by `m` and `t`, both at level `i`. The midpoint is the first word of width `w`, in
the order of the binary counter, that the current vertex reaches and that reaches `t` at level `i`
(`Cslib.Reachability.Walk.search`); when there is none, it is the word of zeros.

The midpoint is always a word of width `w`, so the shape of the run does not depend on the edges:
a target at level `d` is reached in exactly `2 ^ (d + 1) - 1` steps
(`Cslib.Reachability.Walk.iterate_step_frame`), a whole stack in
`Cslib.Reachability.Walk.stackSteps` steps (`Cslib.Reachability.Walk.iterate_step_stack`), every
word on the way has width `w` (`Cslib.Reachability.Walk.width_iterate`), and a run from a target at
level `d` holds at most `d + 1` targets, at levels at most `d`
(`Cslib.Reachability.Walk.levelsLE_iterate`). When `v` is reachable from `u` within `2 ^ d` steps,
each step of the run from `u` to `v` stays put or follows an edge
(`Cslib.Reachability.Walk.eq_or_edge_iterate`), because each target remains reachable from the
previous one at its level (`Cslib.Reachability.Walk.chain_iterate`).

The space of a step on multi-tape machines is in
`Cslib.Computability.Machines.Turing.MultiTape.Complexity.Space.SavitchWalk`.

## Main definitions

* `Cslib.Reachability.Walk.searchStep`, `Cslib.Reachability.Walk.search`: search in counter order.
* `Cslib.Reachability.Walk.midpoint`: the first midpoint of a call.
* `Cslib.Reachability.Walk.State`, `Cslib.Reachability.Walk.step`: the walk.
* `Cslib.Reachability.Walk.stackSteps`: the number of steps that clear a stack.
* `Cslib.Reachability.Walk.Width`, `Cslib.Reachability.Walk.LevelsLE`,
  `Cslib.Reachability.Walk.Chain`: the invariants of a run.

## Main results

* `Cslib.Reachability.Walk.search_eq`, `Cslib.Reachability.Walk.test_search`,
  `Cslib.Reachability.Walk.search_of_forall`: the search finds the first word that passes the test,
  and the word of zeros when there is none; `Cslib.Reachability.Walk.search_congr`: it depends only
  on the test at words of width `w`.
* `Cslib.Reachability.Walk.reach_midpoint`, `Cslib.Reachability.Walk.midpoint_of_reach_eq_false`:
  the midpoint splits a call, and is the word of zeros when the call fails.
* `Cslib.Reachability.Walk.iterate_step_frame`, `Cslib.Reachability.Walk.iterate_step_stack`,
  `Cslib.Reachability.Walk.iterate_step_run`: the walk reaches its targets in a fixed number of
  steps.
* `Cslib.Reachability.Walk.width_iterate`, `Cslib.Reachability.Walk.levelsLE_iterate`,
  `Cslib.Reachability.Walk.LevelsLE.length_le`, `Cslib.Reachability.Walk.LevelsLE.le_of_mem`: the
  shape of the states of a run.
* `Cslib.Reachability.Walk.chain_iterate`, `Cslib.Reachability.Walk.eq_or_edge_iterate`: a run
  between reachable vertices follows edges.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

public section

namespace Cslib.Reachability.Walk

open Cslib.BitString (increment lsbValue lsbValue_lt lsbValue_injective iterate_increment
  iterate_increment_lsbValue lsbValue_replicate_true mem_enumList)

/-! ### Search in counter order -/

/-- One round of a search through the words of a width in counter order: keep a word that passes
`test`, and otherwise move to the next word of the binary counter. -/
@[expose] def searchStep (test : List Bool → Bool) (m : List Bool) : List Bool :=
  if test m then m else increment m

/-- **Search in counter order.** From the word of `w` zeros, `2 ^ w` rounds of `searchStep` stop at
the first word of width `w`, in the order of the binary counter, that passes `test`; when there is
none, the counter wraps around to the word of zeros. -/
@[expose] def search (test : List Bool → Bool) (w : ℕ) : List Bool :=
  (searchStep test)^[2 ^ w] (List.replicate w false)

/-- A round of the search keeps the width. -/
@[simp] theorem length_searchStep (test : List Bool → Bool) (m : List Bool) :
    (searchStep test m).length = m.length := by
  unfold searchStep
  split_ifs <;> simp

/-- Rounds of the search keep the width. -/
@[simp] theorem length_iterate_searchStep (test : List Bool → Bool) (k : ℕ) (m : List Bool) :
    ((searchStep test)^[k] m).length = m.length := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply, ih, length_searchStep]

/-- The search returns a word of width `w`. -/
@[simp] theorem length_search (test : List Bool → Bool) (w : ℕ) : (search test w).length = w := by
  rw [search, length_iterate_searchStep, List.length_replicate]

/-- A word that passes `test` is a fixed point of the search. -/
private theorem iterate_searchStep_of_test {test : List Bool → Bool} {m : List Bool}
    (h : test m = true) (k : ℕ) : (searchStep test)^[k] m = m :=
  Function.iterate_fixed (by simp [searchStep, h]) k

/-- Before the first word that passes `test`, the search counts. -/
private theorem iterate_searchStep_eq_increment {test : List Bool → Bool} {m : List Bool} {k : ℕ}
    (h : ∀ j < k, test (increment^[j] m) = false) :
    (searchStep test)^[k] m = increment^[k] m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih fun j hj => h j (by omega)]
    simp [searchStep, h k (by omega)]

/-- Incrementing the word of ones gives the word of zeros. -/
private theorem increment_replicate_true :
    ∀ w, increment (List.replicate w true) = List.replicate w false
  | 0 => rfl
  | w + 1 => by simp only [List.replicate_succ, increment, increment_replicate_true w]

/-- The counter wraps around after `2 ^ w` increments. -/
private theorem iterate_increment_two_pow (w : ℕ) :
    increment^[2 ^ w] (List.replicate w false) = List.replicate w false := by
  have h₁ := Nat.one_le_two_pow (n := w)
  obtain ⟨hv, hl⟩ := iterate_increment w (2 ^ w - 1) (by omega)
  have hones : increment^[2 ^ w - 1] (List.replicate w false) = List.replicate w true :=
    lsbValue_injective (by rw [hl, List.length_replicate])
      (by have := lsbValue_replicate_true w; omega)
  rw [show 2 ^ w = 2 ^ w - 1 + 1 by omega, Function.iterate_succ_apply', hones,
    increment_replicate_true]

/-- **The search finds the first word that passes `test`**: if the `k`-th word of width `w` in
counter order passes it and no earlier word does, the search returns it. -/
theorem search_eq {test : List Bool → Bool} {w k : ℕ} (hk : k < 2 ^ w)
    (htest : test (increment^[k] (List.replicate w false)) = true)
    (hmin : ∀ j < k, test (increment^[j] (List.replicate w false)) = false) :
    search test w = increment^[k] (List.replicate w false) := by
  rw [search, show 2 ^ w = 2 ^ w - k + k by omega, Function.iterate_add_apply,
    iterate_searchStep_eq_increment hmin, iterate_searchStep_of_test htest]

/-- **The search succeeds when some word of width `w` passes `test`.** -/
theorem test_search {test : List Bool → Bool} {w : ℕ} {m : List Bool} (hm : m.length = w)
    (h : test m = true) : test (search test w) = true := by
  subst hm
  have hm : test (increment^[lsbValue m] (List.replicate m.length false)) = true := by
    rw [iterate_increment_lsbValue]
    exact h
  have hex : ∃ k, test (increment^[k] (List.replicate m.length false)) = true := ⟨_, hm⟩
  have hle := Nat.find_min' hex hm
  have hlt := lsbValue_lt m
  rw [search_eq (by omega) (Nat.find_spec hex) fun j hj => by simpa using Nat.find_min hex hj]
  exact Nat.find_spec hex

/-- **The search depends only on the words of width `w`**: tests that agree on them give the same
search, since every round keeps the width. -/
theorem search_congr {test test' : List Bool → Bool} {w : ℕ}
    (h : ∀ m : List Bool, m.length = w → test m = test' m) : search test w = search test' w := by
  have key (k : ℕ) : ∀ m : List Bool, m.length = w →
      (searchStep test)^[k] m = (searchStep test')^[k] m := by
    induction k with
    | zero => exact fun _ _ => rfl
    | succ k ih =>
      intro m hm
      have hs : searchStep test m = searchStep test' m := by simp only [searchStep, h m hm]
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hs]
      exact ih _ (by rw [length_searchStep, hm])
  exact key _ _ (List.length_replicate ..)

/-- **Without a word that passes `test`, the search returns the word of zeros**: the counter wraps
around after `2 ^ w` rounds. -/
theorem search_of_forall {test : List Bool → Bool} {w : ℕ}
    (h : ∀ m : List Bool, m.length = w → test m = false) :
    search test w = List.replicate w false := by
  rw [search, iterate_searchStep_eq_increment fun j _ => h _ (by simp),
    iterate_increment_two_pow]

/-! ### The midpoint of a call -/

/-- **The midpoint of a call** from `u` to `v` at level `i + 1`: the first word of width `w`, in
counter order, that `u` reaches and that reaches `v` at level `i` (`search`). It is the word of
zeros when there is no such word, and when `u` or `v` does not have width `w`. -/
@[expose] def midpoint (edge : List Bool → List Bool → Bool) (w i : ℕ) (u v : List Bool) :
    List Bool :=
  if u.length = w ∧ v.length = w then
    search (fun m => reach edge w i u m && reach edge w i m v) w
  else List.replicate w false

/-- The midpoint has width `w`. -/
@[simp] theorem length_midpoint (edge : List Bool → List Bool → Bool) (w i : ℕ)
    (u v : List Bool) : (midpoint edge w i u v).length = w := by
  unfold midpoint
  split_ifs <;> simp

/-- **The midpoint splits a call**: if `v` is reachable from `u` at level `i + 1`, the midpoint is
reachable from `u`, and reaches `v`, at level `i`. -/
theorem reach_midpoint {edge : List Bool → List Bool → Bool} {w i : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) (h : reach edge w (i + 1) u v = true) :
    reach edge w i u (midpoint edge w i u v) = true ∧
      reach edge w i (midpoint edge w i u v) v = true := by
  simp only [reach, List.any_eq_true, Bool.and_eq_true, mem_enumList] at h
  obtain ⟨m, hm, hum⟩ := h
  have := test_search (test := fun m => reach edge w i u m && reach edge w i m v) hm
    (by simpa using hum)
  rw [midpoint, ite_eq_left ⟨hu, hv⟩]
  simpa using this

/-- **A failed call has the word of zeros as midpoint.** -/
theorem midpoint_of_reach_eq_false {edge : List Bool → List Bool → Bool} {w i : ℕ}
    {u v : List Bool} (h : reach edge w (i + 1) u v = false) :
    midpoint edge w i u v = List.replicate w false := by
  rw [midpoint]
  split_ifs
  · refine search_of_forall fun m hm => ?_
    simp only [reach, List.any_eq_false, mem_enumList, Bool.and_eq_true] at h
    simpa using h m hm
  · rfl

/-! ### The walk -/

/-- A state of the walk: the current vertex, and the stack of pending targets with their levels,
the next target first. A target at level `i` is reachable within `2 ^ i` steps from the vertex or
target before it. -/
abbrev State : Type := List Bool × List (List Bool × ℕ)

/-- **One step of the walk**, with the edge test `edge` and words of width `w`.
* An empty stack is a fixed point: the walk has arrived.
* A target at level `0` is one step away: move to it and pop it.
* A target `t` at level `i + 1` is replaced by the midpoint of the current vertex and `t`, followed
  by `t`, both at level `i`. -/
@[expose] def step (edge : List Bool → List Bool → Bool) (w : ℕ) : State → State
  | (cur, []) => (cur, [])
  | (_, (t, 0) :: rest) => (t, rest)
  | (cur, (t, i + 1) :: rest) => (cur, (midpoint edge w i cur t, i) :: (t, i) :: rest)

section Run

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-- An empty stack is a fixed point of a step. -/
theorem step_nil (edge : List Bool → List Bool → Bool) (w : ℕ) (cur : List Bool) :
    step edge w (cur, []) = (cur, []) := rfl

/-- A target at level `0` is reached in one step, and popped. -/
theorem step_zero (edge : List Bool → List Bool → Bool) (w : ℕ) (cur t : List Bool)
    (rest : List (List Bool × ℕ)) : step edge w (cur, (t, 0) :: rest) = (t, rest) := rfl

/-- A target at level `i + 1` is split at the midpoint of the current vertex and the target. -/
theorem step_succ (edge : List Bool → List Bool → Bool) (w i : ℕ) (cur t : List Bool)
    (rest : List (List Bool × ℕ)) :
    step edge w (cur, (t, i + 1) :: rest) =
      (cur, (midpoint edge w i cur t, i) :: (t, i) :: rest) := rfl

/-- An empty stack is a fixed point of the walk. -/
theorem iterate_step_nil (edge : List Bool → List Bool → Bool) (w : ℕ) (cur : List Bool)
    (n : ℕ) : (step edge w)^[n] (cur, []) = (cur, []) :=
  Function.iterate_fixed rfl n

/-- The number of steps that clear a stack: `2 ^ (ℓ + 1) - 1` for each target at level `ℓ`. -/
@[expose] def stackSteps : List (List Bool × ℕ) → ℕ
  | [] => 0
  | (_, ℓ) :: rest => 2 ^ (ℓ + 1) - 1 + stackSteps rest

/-- **A target at level `d` is reached in `2 ^ (d + 1) - 1` steps**, whatever the edges: the walk
then stands on the target, with the rest of the stack untouched. -/
theorem iterate_step_frame (edge : List Bool → List Bool → Bool) (w d : ℕ) (cur t : List Bool)
    (rest : List (List Bool × ℕ)) :
    (step edge w)^[2 ^ (d + 1) - 1] (cur, (t, d) :: rest) = (t, rest) := by
  induction d generalizing cur t rest with
  | zero => rfl
  | succ d ih =>
    have h : 2 ^ (d + 1 + 1) - 1 = 2 ^ (d + 1) - 1 + (2 ^ (d + 1) - 1) + 1 := by
      have := Nat.one_le_two_pow (n := d + 1)
      rw [pow_succ 2 (d + 1)]
      omega
    rw [h, Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one,
      step_succ, ih, ih]

/-- **A stack is cleared in `stackSteps stack` steps**, whatever the edges: the walk then stands
on the last target, or where it started when the stack is empty. -/
theorem iterate_step_stack (edge : List Bool → List Bool → Bool) (w : ℕ) (cur : List Bool)
    (stack : List (List Bool × ℕ)) :
    (step edge w)^[stackSteps stack] (cur, stack) = ((stack.map Prod.fst).getLastD cur, []) := by
  induction stack generalizing cur with
  | nil => rfl
  | cons e stack ih =>
    obtain ⟨t, ℓ⟩ := e
    rw [stackSteps, Nat.add_comm (2 ^ (ℓ + 1) - 1), Function.iterate_add_apply,
      iterate_step_frame, ih, List.map_cons, List.getLastD_cons]

/-- **The run from `u` to a target `v` at level `d`** arrives at `v` with an empty stack after
`2 ^ (d + 1) - 1` steps, whatever the edges. -/
theorem iterate_step_run (edge : List Bool → List Bool → Bool) (w d : ℕ) (u v : List Bool) :
    (step edge w)^[2 ^ (d + 1) - 1] (u, [(v, d)]) = (v, []) :=
  iterate_step_frame edge w d u v []

/-! ### The shape of the states -/

/-- **The words of a state have width `w`**: the current vertex and every pending target. -/
@[expose] def Width (w : ℕ) (s : State) : Prop :=
  s.1.length = w ∧ ∀ e ∈ s.2, e.1.length = w

/-- A step keeps the width. -/
theorem width_step (edge : List Bool → List Bool → Bool) {w : ℕ} {s : State} (h : Width w s) :
    Width w (step edge w s) := by
  obtain ⟨cur, _ | ⟨⟨t, _ | i⟩, rest⟩⟩ := s
  · exact h
  · obtain ⟨-, hst⟩ := h
    exact ⟨hst _ List.mem_cons_self, fun e he => hst e (List.mem_cons_of_mem _ he)⟩
  · obtain ⟨hc, hst⟩ := h
    refine ⟨hc, fun e he => ?_⟩
    rcases List.mem_cons.mp he with rfl | he
    · exact length_midpoint ..
    · rcases List.mem_cons.mp he with rfl | he
      · exact hst (t, i + 1) List.mem_cons_self
      · exact hst e (List.mem_cons_of_mem _ he)

/-- Every state of a run keeps the width. -/
theorem width_iterate (edge : List Bool → List Bool → Bool) {w : ℕ} {s : State} (h : Width w s)
    (n : ℕ) : Width w ((step edge w)^[n] s) := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact width_step edge ih

/-- **The levels of a stack within depth `d`**: a target with `n` targets below it is at level at
most `d - n`. -/
@[expose] def LevelsLE (d : ℕ) : List (List Bool × ℕ) → Prop
  | [] => True
  | (_, ℓ) :: rest => ℓ + rest.length ≤ d ∧ LevelsLE d rest

/-- The stack of a single target at level `d` has its levels within depth `d`. -/
theorem levelsLE_singleton (d : ℕ) (v : List Bool) : LevelsLE d [(v, d)] :=
  ⟨by simp, trivial⟩

/-- A stack with its levels within depth `d` holds at most `d + 1` targets. -/
theorem LevelsLE.length_le {d : ℕ} :
    ∀ {stack : List (List Bool × ℕ)}, LevelsLE d stack → stack.length ≤ d + 1
  | [], _ => by simp
  | (_, _) :: _, h => by have := h.1; simp only [List.length_cons]; omega

/-- A stack with its levels within depth `d` has its targets at levels at most `d`. -/
theorem LevelsLE.le_of_mem {d : ℕ} :
    ∀ {stack : List (List Bool × ℕ)}, LevelsLE d stack → ∀ e ∈ stack, e.2 ≤ d
  | [], _, _, he => by simp at he
  | (_, _) :: _, h, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · have := h.1; dsimp only; omega
    · exact h.2.le_of_mem e he

/-- A step keeps the levels within depth `d`. -/
theorem levelsLE_step (edge : List Bool → List Bool → Bool) (w : ℕ) {d : ℕ} {s : State}
    (h : LevelsLE d s.2) : LevelsLE d (step edge w s).2 := by
  obtain ⟨cur, _ | ⟨⟨t, _ | i⟩, rest⟩⟩ := s
  · exact h
  · exact h.2
  · obtain ⟨hl, hr⟩ := h
    exact ⟨by simp only [List.length_cons]; omega, by omega, hr⟩

/-- **Every state of a run keeps the levels within depth `d`.** -/
theorem levelsLE_iterate (edge : List Bool → List Bool → Bool) (w : ℕ) {d : ℕ} {s : State}
    (h : LevelsLE d s.2) (n : ℕ) : LevelsLE d ((step edge w)^[n] s).2 := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact levelsLE_step edge w ih

/-! ### A run between reachable vertices -/

/-- **The chain of a state**: the current vertex reaches the first target, and each target the
next, at their levels, between words of width `w`. -/
@[expose] def Chain (edge : List Bool → List Bool → Bool) (w : ℕ) (cur : List Bool) :
    List (List Bool × ℕ) → Prop
  | [] => cur.length = w
  | (t, ℓ) :: rest => cur.length = w ∧ reach edge w ℓ cur t = true ∧ Chain edge w t rest

/-- The current vertex of a chain has width `w`. -/
theorem Chain.length_eq {cur : List Bool} :
    ∀ {stack : List (List Bool × ℕ)}, Chain edge w cur stack → cur.length = w
  | [], h => h
  | (_, _) :: _, h => h.1

/-- A step keeps the chain. -/
theorem chain_step {s : State} (h : Chain edge w s.1 s.2) :
    Chain edge w (step edge w s).1 (step edge w s).2 := by
  obtain ⟨cur, _ | ⟨⟨t, _ | i⟩, rest⟩⟩ := s
  · exact h
  · exact h.2.2
  · obtain ⟨hc, hr, hrest⟩ := h
    obtain ⟨h₁, h₂⟩ := reach_midpoint hc hrest.length_eq hr
    exact ⟨hc, h₁, length_midpoint .., h₂, hrest⟩

/-- Every state of a run keeps the chain. -/
theorem chain_iterate {s : State} (h : Chain edge w s.1 s.2) (n : ℕ) :
    Chain edge w ((step edge w)^[n] s).1 ((step edge w)^[n] s).2 := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact chain_step ih

/-- **A step from a chain stays put or follows an edge.** -/
theorem eq_or_edge_step {s : State} (h : Chain edge w s.1 s.2) :
    (step edge w s).1 = s.1 ∨ edge s.1 (step edge w s).1 = true := by
  obtain ⟨cur, _ | ⟨⟨t, _ | i⟩, rest⟩⟩ := s
  · exact Or.inl rfl
  · obtain ⟨-, hr, -⟩ := h
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with rfl | hr
    · exact Or.inl rfl
    · exact Or.inr hr
  · exact Or.inl rfl

/-- **Following a walk.** If `v` is reachable from `u` within `2 ^ d` steps between words of width
`w`, every step of the run from `u` to the target `v` at level `d` stays put or follows an edge. -/
theorem eq_or_edge_iterate {d : ℕ} {u v : List Bool} (hu : u.length = w) (hv : v.length = w)
    (h : reach edge w d u v = true) (n : ℕ) :
    ((step edge w)^[n + 1] (u, [(v, d)])).1 = ((step edge w)^[n] (u, [(v, d)])).1 ∨
      edge ((step edge w)^[n] (u, [(v, d)])).1 ((step edge w)^[n + 1] (u, [(v, d)])).1 =
        true := by
  rw [Function.iterate_succ_apply']
  exact eq_or_edge_step (chain_iterate (s := (u, [(v, d)])) ⟨hu, h, hv⟩ n)

end Run

end Cslib.Reachability.Walk
