/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Enumeration
public import Complexity.Foundations.Relation.RelatesWithinSteps
import Complexity.Foundations.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Savitch's midpoint reachability with an explicit stack

Savitch's theorem rests on the midpoint recursion: `v` is reachable from `u` within `2 ^ (i + 1)`
steps exactly when some midpoint is reachable from `u` and reaches `v` within `2 ^ i` steps each
(`Relation.RelatesWithinSteps.two_pow_succ_iff`). On the words of a fixed width `w`,
`Cslib.Reachability.reach` is this recursion, with the midpoints enumerated by
`Cslib.BitString.enumList`, and it decides walks of at most `2 ^ i` steps along the edges of an
edge test (`Cslib.Reachability.reach_iff`).

Savitch's algorithm runs the recursion on an explicit stack. A frame records a call in progress:
its level, its endpoints, the midpoint being tried, which doubles as the counter of the midpoints,
and the half being tried. A register holds the pending call or the value just returned. One total
step function (`Cslib.Reachability.Savitch.step`) handles the five cases: a call at level `0` tests
for an edge, a call at a higher level pushes a frame, a value returned into either half of a frame
moves to the other half, to the next midpoint or out of the frame, and an empty stack holding a
value is a fixed point. The midpoints advance by a binary counter of fixed width
(`Cslib.Reachability.Savitch.next`), which visits the words in the order of
`Cslib.BitString.enumList`. A call at level `i` returns within
`Cslib.Reachability.Savitch.callSteps w i` steps
(`Cslib.Reachability.Savitch.exists_iterate_step_call`), so
`Cslib.Reachability.Savitch.steps w d = 2 ^ ((w + 2) * (d + 1)) - 1` steps compute the recursion at
level `d` (`Cslib.Reachability.savitch_eq`).

The time and space of the algorithm on multi-tape machines are in
`Cslib.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability`.

## Main definitions

* `Cslib.Reachability.reach`: the midpoint recursion.
* `Cslib.Reachability.Savitch.next`: the binary counter of fixed width.
* `Cslib.Reachability.Savitch.Frame`, `Cslib.Reachability.Savitch.Reg`,
  `Cslib.Reachability.Savitch.State`, `Cslib.Reachability.Savitch.step`: the stack machine.
* `Cslib.Reachability.Savitch.callSteps`, `Cslib.Reachability.Savitch.steps`: the number of steps
  of a call, and of the algorithm.
* `Cslib.Reachability.savitch`: Savitch's algorithm.

## Main results

* `Cslib.Reachability.reach_iff`: the recursion decides walks of at most `2 ^ i` steps.
* `Cslib.Reachability.Savitch.next_getElem_enumList`: the counter visits the words in the order of
  `Cslib.BitString.enumList`.
* `Cslib.Reachability.Savitch.exists_iterate_step_call`: every call returns its value.
* `Cslib.Reachability.savitch_eq`, `Cslib.Reachability.savitch_iff`: the algorithm computes the
  recursion, and decides walks of at most `2 ^ d` steps.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.5][Sipser2013]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, Section 4.2][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Reachability

open Cslib.BitString (enumList enumList_succ mem_enumList)

/-! ### Reachability by midpoints -/

/-- **Reachability within `2 ^ i` steps, by midpoints.** At level `0`, `v` is `u` or one edge
away; at level `i + 1`, some word `m` of width `w` is reachable from `u` and reaches `v` at level
`i`. This is the recursion of Savitch's theorem [Sipser, Theorem 8.5][Sipser2013]. -/
def reach (edge : List Bool → List Bool → Bool) (w : ℕ) : ℕ → List Bool → List Bool → Bool
  | 0, u, v => decide (u = v) || edge u v
  | i + 1, u, v => (enumList w).any fun m => reach edge w i u m && reach edge w i m v

/-- A walk along edges between words of width `w` stays among the words of width `w`. -/
private theorem length_eq_of_relatesWithinSteps {edge : List Bool → List Bool → Bool} {w n : ℕ}
    {u v : List Bool} (hu : u.length = w)
    (h : Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
      u v n) : v.length = w := by
  induction h.reflTransGen with
  | refl => exact hu
  | tail _ hstep _ => exact hstep.2.1

/-- **The midpoint recursion decides walks of at most `2 ^ i` steps** between words of width `w`,
along the edges given by `edge` [Sipser, Theorem 8.5][Sipser2013]. -/
theorem reach_iff {edge : List Bool → List Bool → Bool} {w i : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) :
    reach edge w i u v = true ↔
      Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
        u v (2 ^ i) := by
  induction i generalizing u v with
  | zero =>
    rw [pow_zero, Relation.RelatesWithinSteps.one_iff, Relation.reflGen_iff]
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq, hu, hv, true_and]
    exact or_congr eq_comm Iff.rfl
  | succ i ih =>
    rw [Relation.RelatesWithinSteps.two_pow_succ_iff]
    simp only [reach, List.any_eq_true, Bool.and_eq_true, mem_enumList]
    constructor
    · rintro ⟨m, hm, h₁, h₂⟩
      exact ⟨m, (ih hu hm).mp h₁, (ih hm hv).mp h₂⟩
    · rintro ⟨m, h₁, h₂⟩
      have hm := length_eq_of_relatesWithinSteps hu h₁
      exact ⟨m, hm, (ih hu hm).mpr h₁, (ih hm hv).mpr h₂⟩

namespace Savitch

/-! ### The binary counter -/

/-- The successor of a word in the binary counter of its width, least significant bit first, or
`none` on the word of all ones, where the counter overflows. -/
def next : List Bool → Option (List Bool)
  | [] => none
  | false :: u => some (true :: u)
  | true :: u => (next u).map (false :: ·)

/-- The words of width `w + 1` at the indices `2 * j` and `2 * j + 1` extend the `j`-th word of
width `w` by `false` and by `true`. -/
private theorem getElem?_enumList_succ (w j : ℕ) :
    (enumList (w + 1))[2 * j]? = (enumList w)[j]?.map (false :: ·) ∧
      (enumList (w + 1))[2 * j + 1]? = (enumList w)[j]?.map (true :: ·) := by
  rw [enumList_succ]
  generalize enumList w = l
  induction l generalizing j with
  | nil => simp
  | cons u l ih =>
    rcases j with _ | j
    · simp
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 1 + 2 by ring]
      simpa using ih j

/-- The first word of width `w` is the word of all zeros. -/
private theorem getElem?_enumList_zero (w : ℕ) :
    (enumList w)[0]? = some (List.replicate w false) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [← Nat.mul_zero 2, (getElem?_enumList_succ w 0).1, ih]
    rfl

/-- **The counter visits the words in the order of `Cslib.BitString.enumList`**: it moves from
each word to the next one, and overflows on the last one. -/
theorem next_getElem_enumList (w k : ℕ) (hk : k < (enumList w).length) :
    next (enumList w)[k] = (enumList w)[k + 1]? := by
  induction w generalizing k with
  | zero =>
    obtain rfl : k = 0 := by simpa using hk
    rfl
  | succ w ih =>
    have hk' : k < 2 * 2 ^ w := by simpa [pow_succ, Nat.mul_comm] using hk
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · have hj : j < (enumList w).length := by simp only [BitString.length_enumList]; omega
      obtain ⟨h₀, h₁⟩ := getElem?_enumList_succ w j
      rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hj] at h₀
      rw [Option.some.inj h₀, h₁, List.getElem?_eq_getElem hj]
      rfl
    · have hj : j < (enumList w).length := by simp only [BitString.length_enumList]; omega
      have h₁ := (getElem?_enumList_succ w j).2
      rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hj] at h₁
      rw [Option.some.inj h₁, show 2 * j + 1 + 1 = 2 * (j + 1) by ring,
        (getElem?_enumList_succ w (j + 1)).1, next, ih j hj]

/-! ### The stack machine -/

/-- A frame of the stack: the call at level `level + 1` from `src` to `dst`, while it tries the
midpoint `mid` with two calls at level `level`. -/
structure Frame where
  /-- The level of the two calls on the halves; the frame answers a call at level `level + 1`. -/
  level : ℕ
  /-- The source of the call. -/
  src : List Bool
  /-- The target of the call. -/
  dst : List Bool
  /-- The midpoint being tried, which is also the counter of the midpoints tried so far. -/
  mid : List Bool
  /-- `false` while the first half, from `src` to `mid`, is being tried; `true` while the second
  half, from `mid` to `dst`, is, once the first half has succeeded. -/
  phase : Bool
deriving Inhabited

/-- The register of the machine: a pending call, or the value of a call that has returned. -/
inductive Reg where
  /-- A call asking whether `dst` is reachable from `src` within `2 ^ level` steps. -/
  | call (level : ℕ) (src dst : List Bool)
  /-- A call has returned `value`. -/
  | ret (value : Bool)
deriving Inhabited

/-- The answer held by a register: the returned value, or `false` while a call is pending. -/
def Reg.answer : Reg → Bool
  | .call .. => false
  | .ret b => b

/-- The state of the machine: the stack of frames, top frame first, and the register. -/
structure State where
  /-- The frames of the calls in progress, the innermost first. -/
  stack : List Frame
  /-- The pending call or the returned value. -/
  reg : Reg
deriving Inhabited

/-- **One step of Savitch's machine**, with the edge test `edge` and midpoints of width `w`.
* A call at level `0` returns whether `v` is `u` or one edge away.
* A call at level `i + 1` pushes a frame and calls the first half with the first midpoint, the word
  of all zeros.
* An empty stack with a returned value is a fixed point: the value is the answer.
* A value `true` returned into the first half moves the frame to the second half; returned into the
  second half, the frame returns `true`.
* A value `false` returned into either half advances the midpoint by the binary counter; when the
  counter overflows, every midpoint has failed and the frame returns `false`. -/
def step (edge : List Bool → List Bool → Bool) (w : ℕ) : State → State
  | ⟨stack, .call 0 u v⟩ => ⟨stack, .ret (decide (u = v) || edge u v)⟩
  | ⟨stack, .call (i + 1) u v⟩ =>
    ⟨⟨i, u, v, List.replicate w false, false⟩ :: stack, .call i u (List.replicate w false)⟩
  | ⟨[], .ret b⟩ => ⟨[], .ret b⟩
  | ⟨f :: stack, .ret true⟩ =>
    if f.phase then ⟨stack, .ret true⟩
    else ⟨{ f with phase := true } :: stack, .call f.level f.mid f.dst⟩
  | ⟨f :: stack, .ret false⟩ =>
    match next f.mid with
    | none => ⟨stack, .ret false⟩
    | some m => ⟨{ f with mid := m, phase := false } :: stack, .call f.level f.src m⟩

/-- The number of steps the machine takes for a call at level `i`, with midpoints of width `w`:
one step to push the frame, and for each of the `2 ^ w` midpoints at most two calls at level `i`,
each followed by one step to take its value. -/
def callSteps (w : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 1 + 2 * 2 ^ w * (callSteps w i + 1)

/-- The number of steps Savitch's algorithm runs the machine for: `2 ^ ((w + 2) * (d + 1)) - 1`,
at least `callSteps w d`, and written in binary as `(w + 2) * (d + 1)` ones. -/
def steps (w d : ℕ) : ℕ := 2 ^ ((w + 2) * (d + 1)) - 1

/-! ### Every call returns its value -/

section Correctness

variable {edge : List Bool → List Bool → Bool} {w : ℕ}

/-- The midpoints still to be tried by a frame that is at the `k`-th midpoint. -/
private theorem any_drop_enumList (P : List Bool → Bool) {k : ℕ} (hk : k < (enumList w).length) :
    ((enumList w).drop k).any P = (P (enumList w)[k] || ((enumList w).drop (k + 1)).any P) := by
  rw [List.drop_eq_getElem_cons hk, List.any_cons]

/-- The run of a frame at level `i + 1`, from `u` to `v`, at the `k`-th midpoint: if a `false`
returned into the frame is processed within `2 * j * (c + 1) + 1` steps, the frame returns its
value, in either phase. -/
private theorem run_frame {i c : ℕ} {u v : List Bool} {stack : List Frame}
    (ih : ∀ u v (stack : List Frame), ∃ T ≤ c,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩)
    {j k : ℕ} (hk : k < (enumList w).length)
    (hadv : ∀ ph, ∃ T ≤ 2 * j * (c + 1) + 1,
      (step edge w)^[T] ⟨⟨i, u, v, (enumList w)[k], ph⟩ :: stack, .ret false⟩ =
        ⟨stack, .ret (((enumList w).drop (k + 1)).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) :
    (∃ T ≤ (2 * j + 2) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (enumList w)[k], false⟩ :: stack, .call i u (enumList w)[k]⟩ =
        ⟨stack, .ret (((enumList w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) ∧
    (reach edge w i u (enumList w)[k] = true → ∃ T ≤ (2 * j + 1) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (enumList w)[k], true⟩ :: stack, .call i (enumList w)[k] v⟩ =
        ⟨stack, .ret (((enumList w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩) := by
  rw [any_drop_enumList _ hk]
  set m := (enumList w)[k]
  -- the second half
  have hsecond : reach edge w i u m = true → ∃ T ≤ (2 * j + 1) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, m, true⟩ :: stack, .call i m v⟩ =
        ⟨stack, .ret ((reach edge w i u m && reach edge w i m v) ||
          ((enumList w).drop (k + 1)).any fun m => reach edge w i u m && reach edge w i m v)⟩ := by
    intro hum
    obtain ⟨T₁, hT₁, h₁⟩ := ih m v (⟨i, u, v, m, true⟩ :: stack)
    rw [hum, Bool.true_and]
    cases hmv : reach edge w i m v
    · obtain ⟨T₂, hT₂, h₂⟩ := hadv true
      rw [hmv] at h₁
      exact ⟨T₂ + T₁, by nlinarith, Function.iterate_trans h₁ h₂⟩
    · rw [hmv] at h₁
      exact ⟨1 + T₁, by nlinarith, Function.iterate_trans h₁ rfl⟩
  refine ⟨?_, hsecond⟩
  -- the first half
  obtain ⟨T₁, hT₁, h₁⟩ := ih u m (⟨i, u, v, m, false⟩ :: stack)
  cases hum : reach edge w i u m
  · obtain ⟨T₂, hT₂, h₂⟩ := hadv false
    rw [hum] at h₁
    rw [Bool.false_and, Bool.false_or]
    exact ⟨T₂ + T₁, by nlinarith, Function.iterate_trans h₁ h₂⟩
  · obtain ⟨T₂, hT₂, h₂⟩ := hsecond hum
    rw [hum] at h₁ h₂
    exact ⟨T₂ + (1 + T₁), by nlinarith, Function.iterate_trans (Function.iterate_trans h₁ rfl) h₂⟩

/-- The runs of a frame, by induction on the number `j` of midpoints after the current one. -/
private theorem run_frames {i c : ℕ} {u v : List Bool} {stack : List Frame}
    (ih : ∀ u v (stack : List Frame), ∃ T ≤ c,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩) :
    ∀ j k (hk : k + j + 1 = (enumList w).length),
    ∃ T ≤ (2 * j + 2) * (c + 1),
      (step edge w)^[T] ⟨⟨i, u, v, (enumList w)[k], false⟩ :: stack, .call i u (enumList w)[k]⟩ =
        ⟨stack, .ret (((enumList w).drop k).any
          fun m => reach edge w i u m && reach edge w i m v)⟩ := by
  intro j
  induction j with
  | zero =>
    intro k hk
    refine (run_frame ih (by omega) fun ph => ⟨1, by omega, ?_⟩).1
    have hnext := next_getElem_enumList w k (by omega)
    rw [List.getElem?_eq_none (by omega)] at hnext
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [step, hnext]
  | succ j ih' =>
    intro k hk
    refine (run_frame ih (by omega) fun ph => ?_).1
    obtain ⟨T, hT, h⟩ := ih' (k + 1) (by omega)
    have hnext := next_getElem_enumList w k (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hnext
    refine ⟨T + 1, by nlinarith, Function.iterate_trans ?_ h⟩
    simp [step, hnext]

/-- **Every call returns its value**: from a call at level `i`, the machine returns
`reach edge w i u v` to the same stack within `callSteps w i` steps. -/
theorem exists_iterate_step_call (i : ℕ) (u v : List Bool) (stack : List Frame) :
    ∃ T ≤ callSteps w i,
      (step edge w)^[T] ⟨stack, .call i u v⟩ = ⟨stack, .ret (reach edge w i u v)⟩ := by
  induction i generalizing u v stack with
  | zero => exact ⟨1, le_rfl, rfl⟩
  | succ i ih =>
    have hlen : 0 + (2 ^ w - 1) + 1 = (enumList w).length := by
      have := Nat.one_le_two_pow (n := w)
      simp only [BitString.length_enumList]
      omega
    obtain ⟨T, hT, h⟩ := run_frames (u := u) (v := v) (stack := stack) ih _ 0 hlen
    have h₀ : (enumList w)[0]'(by omega) = List.replicate w false := by
      have := getElem?_enumList_zero w
      rw [List.getElem?_eq_getElem (by omega)] at this
      exact Option.some.inj this
    rw [h₀, List.drop_zero] at h
    refine ⟨T + 1, ?_, Function.iterate_trans rfl h⟩
    have := Nat.one_le_two_pow (n := w)
    have : (2 * (2 ^ w - 1) + 2) = 2 * 2 ^ w := by omega
    simp only [callSteps]
    rw [this] at hT
    omega

/-- An empty stack with a returned value is a fixed point. -/
private theorem iterate_step_ret_nil (b : Bool) (n : ℕ) :
    (step edge w)^[n] ⟨[], .ret b⟩ = ⟨[], .ret b⟩ :=
  Function.iterate_fixed rfl n

/-- The number of steps of a call at level `i` is below `2 ^ ((w + 2) * i + 1)`. -/
private theorem callSteps_add_one_le (w i : ℕ) : callSteps w i + 1 ≤ 2 ^ ((w + 2) * i + 1) := by
  induction i with
  | zero => simp [callSteps]
  | succ i ih =>
    have h₁ : 2 ^ ((w + 2) * (i + 1) + 1) = 2 * 2 ^ w * 2 * 2 ^ ((w + 2) * i + 1) := by
      rw [← pow_succ', ← pow_succ, ← pow_add]
      ring_nf
    have h₂ : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have h₃ := Nat.mul_le_mul_left (2 * 2 ^ w) ih
    simp only [callSteps, h₁]
    nlinarith

/-- Savitch's algorithm runs the machine for long enough to return from the call at level `d`. -/
private theorem callSteps_le_steps (w d : ℕ) : callSteps w d ≤ steps w d := by
  have h₁ := callSteps_add_one_le w d
  have h₂ : 2 ^ ((w + 2) * d + 1) ≤ 2 ^ ((w + 2) * (d + 1)) :=
    Nat.pow_le_pow_right two_pos (by nlinarith)
  simp only [steps]
  omega

end Correctness

end Savitch

/-! ### Savitch's algorithm -/

/-- **Savitch's algorithm**: run the machine from the call at level `d` from `u` to `v` on the
empty stack for `Savitch.steps w d` steps, and read the answer off the register. -/
def savitch (edge : List Bool → List Bool → Bool) (w d : ℕ) (u v : List Bool) : Bool :=
  ((Savitch.step edge w)^[Savitch.steps w d] ⟨[], .call d u v⟩).reg.answer

/-- **Savitch's machine computes the midpoint recursion.** -/
theorem savitch_eq (edge : List Bool → List Bool → Bool) (w d : ℕ) (u v : List Bool) :
    savitch edge w d u v = reach edge w d u v := by
  obtain ⟨T, hT, h⟩ := Savitch.exists_iterate_step_call (edge := edge) (w := w) d u v []
  have hN := Savitch.callSteps_le_steps w d
  rw [savitch, show Savitch.steps w d = Savitch.steps w d - T + T by omega,
    Function.iterate_add_apply, h, Savitch.iterate_step_ret_nil]
  rfl

/-- **Savitch's algorithm decides walks of at most `2 ^ d` steps** between words of width `w`
[Sipser, Theorem 8.5][Sipser2013]. -/
theorem savitch_iff {edge : List Bool → List Bool → Bool} {w d : ℕ} {u v : List Bool}
    (hu : u.length = w) (hv : v.length = w) :
    savitch edge w d u v = true ↔
      Relation.RelatesWithinSteps (fun a b => a.length = w ∧ b.length = w ∧ edge a b = true)
        u v (2 ^ d) := by
  rw [savitch_eq, reach_iff hu hv]

end Cslib.Reachability
