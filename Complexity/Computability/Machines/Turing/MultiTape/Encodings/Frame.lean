/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to crei/tidy-universal `Encodings/Basic.lean`)

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
import Mathlib.Data.List.GetD

/-!
# The bits of a framed word

`frame w` doubles every bit `b` of `w` into `true, b` and ends with `false`
(`Turing.MultiTapeTM.frame`). Its bits are therefore constants or bits of `w`
(`Turing.MultiTapeTM.getElem_frame`), which is what makes framed inputs easy to feed to circuits.

A frame followed by a word, as written on a work tape, splits at each framed bit into the pairs
before it, the pair `true, c` of the bit `c`, and the frame of the rest
(`Turing.MultiTapeTM.frame_append_cons`), so a machine can locate the tag and the bit of each pair
and overwrite the bit in place (`Turing.MultiTapeTM.set_frame_append_cons`).

## Main results

* `Turing.MultiTapeTM.getElem_frame`: the bit at each position of `frame w`.
* `Turing.MultiTapeTM.getElem?_frame_two_mul`, `Turing.MultiTapeTM.getElem?_frame_two_mul_add_one`,
  `Turing.MultiTapeTM.getElem?_frame_two_mul_length`: the marker, data, and terminator bits of
  `frame w` by position.
* `Turing.MultiTapeTM.forall_getElem?_frame_iff`: a predicate agrees with `frame w` placed at offset
  `base` iff it agrees with the markers, the bits of `w`, and the terminator.
* `Turing.MultiTapeTM.forall_getElem?_append_iff`: a predicate agrees with the bits of `u ++ w` iff
  it agrees with `u` and with `w` shifted by `u.length`.
* `Turing.MultiTapeTM.getD_frame_two_mul`, `Turing.MultiTapeTM.getD_frame_two_mul_add_one`:
  indexed access to markers and input bits with default `false`.
* `Turing.MultiTapeTM.length_flatMap_frame`: the length of a list of framed words.
* `Turing.MultiTapeTM.length_unframe_le`: the word framed at the start of a word is no longer than
  the word.
* `Turing.MultiTapeTM.frame_append_cons`: a frame split at a framed bit.
* `Turing.MultiTapeTM.getElem?_frame_append_length`,
  `Turing.MultiTapeTM.getElem?_frame_append_cons`: the terminator and the tags of a frame followed
  by a word.
* `Turing.MultiTapeTM.lt_length_frame_append_cons`,
  `Turing.MultiTapeTM.two_mul_length_le_length_frame_append`: positions within a frame followed by
  a word.
* `Turing.MultiTapeTM.set_frame_append_cons`: overwriting a framed bit in place.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- The bit at position `j` of `frame w`: `true` at even positions below `2 |w|`, the bit `w[j / 2]`
at odd ones, and the final `false`. -/
theorem getElem_frame (w : List Bool) (j : ℕ) (hj : j < (frame w).length) :
    (frame w)[j] = if h : j < 2 * w.length then
      (if j % 2 = 0 then true else w[j / 2]'(by omega)) else false := by
  induction w generalizing j with
  | nil =>
    simp only [frame_nil, List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    rfl
  | cons b w ih =>
    match j, hj with
    | 0, _ => simp
    | 1, _ => simp [show 1 < 2 * (w.length + 1) by omega]
    | j + 2, hj =>
      simp only [frame_cons, List.getElem_cons_succ, length_frame, List.length_cons] at hj ⊢
      rw [ih j (by simpa using (by omega : j < 2 * w.length + 1))]
      by_cases h : j < 2 * w.length
      · simp only [h, show j + 2 < 2 * (w.length + 1) by omega, dite_true, Nat.add_mod_right,
          show (j + 2) / 2 = j / 2 + 1 by omega, List.getElem_cons_succ]
      · simp only [h, show ¬j + 2 < 2 * (w.length + 1) by omega, dite_false]

/-! ### Indexed bit access -/

/-- The terminator of `frame w` sits at position `2 * w.length`. -/
theorem getElem?_frame_two_mul_length (w : List Bool) :
    (frame w)[2 * w.length]? = some false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hidx : 2 * (b :: w).length = 2 * w.length + 2 := by
      rw [List.length_cons]; omega
    rw [hidx, frame_cons]
    exact ih

/-- Each bit of `w` is preceded in `frame w` by a `true` marker at an even position. -/
theorem getElem?_frame_two_mul {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j]? = some true := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) = 2 * j + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

/-- The bit `w[j]` sits at the odd position `2 * j + 1` of `frame w`. -/
theorem getElem?_frame_two_mul_add_one {w : List Bool} {j : ℕ} (hj : j < w.length) :
    (frame w)[2 * j + 1]? = w[j]? := by
  induction w generalizing j with
  | nil => simp at hj
  | cons b w ih =>
    cases j with
    | zero => rfl
    | succ j =>
      have hj' : j < w.length := by simpa using hj
      have hidx : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by omega
      rw [hidx, frame_cons]
      exact ih hj'

/-- A predicate `P : ℕ → Prop` agrees with `frame w` shifted by `base` on
`[base, base + (frame w).length)` iff it is `false` at `base + 2 * w.length` and, for each
`j < w.length`, is `true` at `base + 2 * j` and agrees with `w[j]` at `base + 2 * j + 1`. -/
theorem forall_getElem?_frame_iff (w : List Bool) (base : ℕ) (P : ℕ → Prop) :
    (∀ p, base ≤ p → p < base + (frame w).length →
        (P p ↔ (frame w)[p - base]? = some true)) ↔
      (¬ P (base + 2 * w.length) ∧
        ∀ j < w.length, P (base + 2 * j) ∧ (P (base + 2 * j + 1) ↔ w[j]? = some true)) := by
  rw [length_frame]
  constructor
  · intro h
    refine ⟨?_, fun j hj => ⟨?_, ?_⟩⟩
    · have h0 := h (base + 2 * w.length) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length] at h0
      simpa using h0
    · have h1 := h (base + 2 * j) (by omega) (by omega)
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul hj] at h1
      simpa using h1
    · have h2 := h (base + 2 * j + 1) (by omega) (by omega)
      have hsub : base + 2 * j + 1 - base = 2 * j + 1 := by omega
      rw [hsub, getElem?_frame_two_mul_add_one hj] at h2
      exact h2
  · rintro ⟨hend, hstep⟩ p hlo hhi
    by_cases hlast : p = base + 2 * w.length
    · subst hlast
      rw [Nat.add_sub_cancel_left, getElem?_frame_two_mul_length]
      simp [hend]
    · have hd : p - base < 2 * w.length := by omega
      let j := (p - base) / 2
      have hj : j < w.length := by omega
      rcases Nat.mod_two_eq_zero_or_one (p - base) with hmod | hmod
      · have hp : p = base + 2 * j := by omega
        have hsub : p - base = 2 * j := by omega
        rw [hsub, getElem?_frame_two_mul hj, hp]
        simp [(hstep j hj).1]
      · have hp : p = base + 2 * j + 1 := by omega
        have hsub : p - base = 2 * j + 1 := by omega
        rw [hsub, getElem?_frame_two_mul_add_one hj, hp]
        exact (hstep j hj).2

/-- A predicate `P : ℕ → Prop` agrees with the bits of `u ++ w` iff it agrees with `u` below
`u.length` and with `w` shifted by `u.length` on `[u.length, u.length + w.length)`. -/
theorem forall_getElem?_append_iff (u w : List Bool) (P : ℕ → Prop) :
    (∀ p < (u ++ w).length, (P p ↔ (u ++ w)[p]? = some true)) ↔
      (∀ p < u.length, (P p ↔ u[p]? = some true)) ∧
        (∀ p, u.length ≤ p → p < u.length + w.length →
          (P p ↔ w[p - u.length]? = some true)) := by
  rw [List.length_append]
  constructor
  · intro h
    refine ⟨fun p hp => ?_, fun p hlo hhi => ?_⟩
    · have hp' := h p (by omega)
      rwa [List.getElem?_append_left hp] at hp'
    · have hp' := h p hhi
      rwa [List.getElem?_append_right hlo] at hp'
  · rintro ⟨hu, hw⟩ p hp
    by_cases hlt : p < u.length
    · rw [List.getElem?_append_left hlt]
      exact hu p hlt
    · have hle : u.length ≤ p := by omega
      rw [List.getElem?_append_right hle]
      exact hw p hle hp

/-- A list of framed words spends `2 * |t| + 1` bits on each word `t`. -/
theorem length_flatMap_frame (l : List (List Bool)) :
    (l.flatMap frame).length = (l.map fun t => 2 * t.length + 1).sum := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [List.flatMap_cons, List.length_append, length_frame, ih,
      List.map_cons, List.sum_cons]

/-- With default `false`, the even marker bit tests whether the input index is in bounds. -/
theorem getD_frame_two_mul (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i) false = decide (i < w.length) := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) = 2 * i + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih]
      simp

/-- With default `false`, the odd frame positions contain exactly the input bits. -/
theorem getD_frame_two_mul_add_one (w : List Bool) (i : ℕ) :
    (frame w).getD (2 * i + 1) false = w.getD i false := by
  induction w generalizing i with
  | nil => rcases i with _ | i <;> simp [frame_nil, List.getD_eq_getElem?_getD]
  | cons b w ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · rw [frame_cons, show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega, List.getD_cons_succ,
        List.getD_cons_succ, ih, List.getD_cons_succ]

/-- The word framed at the start of a word is no longer than the word. -/
theorem length_unframe_le : ∀ w : List Bool, (unframe w).length ≤ w.length
  | true :: _ :: v => by
    simp only [unframe, List.length_cons]
    have := length_unframe_le v
    omega
  | [] | [true] | false :: _ => by simp [unframe]

/-! ### Frames followed by a word -/

private theorem length_flatMap_pair (w : List Bool) :
    (w.flatMap fun b => [true, b]).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [List.flatMap_cons, List.length_append, ih, List.length_cons, List.length_nil]
    omega

/-- A frame split at a symbol. -/
theorem frame_append_cons (w v : List Bool) (c : Bool) :
    frame (w ++ c :: v) = (w.flatMap fun b => [true, b]) ++ true :: c :: frame v := by
  simp [frame]

/-- After the pairs of a frame comes its terminator `false`. -/
theorem getElem?_frame_append_length (w x : List Bool) :
    (frame w ++ x)[2 * w.length]? = some false := by
  rw [frame, List.append_assoc, List.getElem?_append_right (by rw [length_flatMap_pair]),
    length_flatMap_pair]
  simp

/-- Each pair of a frame starts with the tag `true`. -/
theorem getElem?_frame_append_cons (w v x : List Bool) (c : Bool) :
    (frame (w ++ c :: v) ++ x)[2 * w.length]? = some true := by
  rw [frame_append_cons, List.append_assoc,
    List.getElem?_append_right (by rw [length_flatMap_pair]), length_flatMap_pair]
  simp

/-- The second cell of a pair of a frame lies within the word. -/
theorem lt_length_frame_append_cons (w v x : List Bool) (c : Bool) :
    2 * w.length + 1 < (frame (w ++ c :: v) ++ x).length := by
  simp only [List.length_append, length_frame, List.length_cons]
  omega

/-- Setting the second cell of a pair of a frame replaces the framed symbol. -/
theorem set_frame_append_cons (w v x : List Bool) (c b : Bool) :
    (frame (w ++ c :: v) ++ x).set (2 * w.length + 1) b = frame (w ++ b :: v) ++ x := by
  rw [frame_append_cons, frame_append_cons, List.append_assoc, List.append_assoc,
    List.set_append_right _ _ (by rw [length_flatMap_pair]; omega), length_flatMap_pair]
  simp

/-- The pairs of a frame fit in the word. -/
theorem two_mul_length_le_length_frame_append (w x : List Bool) :
    2 * w.length ≤ (frame w ++ x).length := by
  simp only [List.length_append, length_frame]
  omega

end Turing.MultiTapeTM
