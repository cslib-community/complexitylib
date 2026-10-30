/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Machine

/-!
# Windowed simulation

In `n` steps, a head reads only cells within distance `n` of where it started. The windowed
simulation exploits this to simulate `n` steps on *windows*: for every tape, the zipper of the
cells within distance `n` of its head. It cuts the windows of radius `⌈n / 2⌉` around the heads,
simulates the first `⌈n / 2⌉` steps on them recursively, pastes the result back, and does the same
for the remaining `⌊n / 2⌋` steps. A single step is `Turing.MultiTapeTM.Universal.stepWith`.

Cutting and pasting take time linear in the window, so `n` steps take time `O(n log n)` for a
fixed machine; that cost analysis is in a separate module. This module defines the simulation and
proves that it computes the universal function.

A windowed configuration (`Turing.MultiTapeTM.Universal.Windowed.Win`) holds the state, then the
input window followed by the work windows. The `head` fields of the window zippers are not used.
Input cells are coded so that a step can be taken without the position of the input head:
`some 0` is the left end at position `0`, `some (a + 1)` the input symbol `a`, and `none` a blank
after the input.

## Main definitions

* `Turing.MultiTapeTM.Universal.Windowed.extract`, `.restore`: cutting windows and pasting them
  back.
* `Turing.MultiTapeTM.Universal.Windowed.wstep`: one step on windows.
* `Turing.MultiTapeTM.Universal.Windowed.sim`: the recursive simulation of `n` steps.
* `Turing.MultiTapeTM.Universal.Windowed.initWin`: the windows of the initial configuration.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.universal_eq_sim`: the windowed simulation of `t` steps
  from the radius-`t` windows of the initial configuration computes the universal function.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-- A windowed configuration: the state, then the input window followed by the work windows. -/
abbrev Win := Option ℕ × List Tape

/-- The cells of `t` within distance `r` of its head, as a zipper with head field `0`. -/
@[expose] def cut (r : ℕ) (t : Tape) : Tape := ⟨0, t.left.take r, t.right.take (r + 1)⟩

/-- The window `inner`, cut from `outer` with radius `r` and then run, with the cells of `outer`
beyond distance `r` of its head put back around it. -/
@[expose] def paste (r : ℕ) (outer inner : Tape) : Tape :=
  ⟨0, inner.left ++ outer.left.drop r, inner.right ++ outer.right.drop (r + 1)⟩

/-- The windows of radius `r`. -/
@[expose] def extract (r : ℕ) (w : Win) : Win := (w.1, w.2.map (cut r))

/-- The windows `inner`, extracted from `outer` with radius `r` and then run, pasted back. -/
@[expose] def restore (r : ℕ) (outer inner : Win) : Win :=
  (inner.1, List.zipWith (paste r) outer.2 inner.2)

/-- The input symbol of a coded input cell. -/
@[expose] def inSym (c : Option ℕ) : Option ℕ := c.bind fun v => if v = 0 then none else some (v - 1)

/-- A stand-in for the position of the input head on a coded input cell: `0` at the left end and
`1` elsewhere. `Turing.MultiTapeTM.Universal.moveInput` distinguishes only these cases. -/
@[expose] def inPos (c : Option ℕ) : ℕ := if c = some 0 then 0 else 1

/-- The input window, moved as the input head moved from `p` to `p'`. -/
@[expose] def moveIn (t : Tape) (p p' : ℕ) : Tape :=
  if p' = p + 1 then t.move .pos else if p' + 1 = p then t.move .neg else t

/-- One step on a windowed configuration, and the symbol it emits. -/
@[expose] def wstep (d : Desc) (w : Win) : Win × Option ℕ :=
  match w.2 with
  | [] => (w, none)
  | i :: ts =>
    (((stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.state,
      moveIn i (inPos i.read) (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.inputPos ::
        (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).1.workTapes),
      (stepWith d ⟨w.1, inPos i.read, ts⟩ (inSym i.read)).2)

/-- The number of steps of the first half of a block of `n` steps. -/
@[expose] def firstHalf (n : ℕ) : ℕ := n - n / 2

/-- The windowed simulation of `n` steps, and the symbols emitted. -/
@[expose] def sim (d : Desc) : ℕ → Win → Win × List ℕ
  | 0, w => (w, [])
  | 1, w => ((wstep d w).1, (wstep d w).2.toList)
  | n + 2, w =>
    let r₁ := sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)
    let w₁ := restore (firstHalf (n + 2)) w r₁.1
    let r₂ := sim d ((n + 2) / 2) (extract ((n + 2) / 2) w₁)
    (restore ((n + 2) / 2) w₁ r₂.1, r₁.2 ++ r₂.2)
termination_by n => n
decreasing_by all_goals first | omega | (simp only [firstHalf]; omega)

/-- The windows of the initial configuration on the input `x`: the input head on the first input
symbol, after the left end, and blank work tapes. -/
@[expose] def initWin (d : Desc) (x : List ℕ) : Win :=
  (some d.q₀, ⟨0, [some 0], x.map fun a => some (a + 1)⟩ :: List.replicate d.tapes ⟨0, [], []⟩)

/-! ### Cells of zippers -/

/-- The cell of `t` at offset `i` from its head; the cells beyond the lists are blank. -/
private def cellAt (t : Tape) (i : ℤ) : Option ℕ :=
  if 0 ≤ i then t.right.getD i.toNat none else t.left.getD (-i - 1).toNat none

private lemma getD_tail' (l : List (Option ℕ)) (m : ℕ) :
    l.tail.getD m none = l.getD (m + 1) none := by
  cases l <;> simp

private lemma getD_drop' (l : List (Option ℕ)) (k m : ℕ) :
    (l.drop k).getD m none = l.getD (k + m) none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]

private lemma getD_take' (l : List (Option ℕ)) (k m : ℕ) :
    (l.take k).getD m none = if m < k then l.getD m none else none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs <;> rfl

private lemma getD_append_left' {A B : List (Option ℕ)} {m : ℕ} (h : m < A.length) :
    (A ++ B).getD m none = A.getD m none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_append_right' {A B : List (Option ℕ)} {m : ℕ} (h : A.length ≤ m) :
    (A ++ B).getD m none = B.getD (m - A.length) none := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private lemma getD_eq_none' {l : List (Option ℕ)} {m : ℕ} (h : l.length ≤ m) :
    l.getD m none = none := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

private lemma cellAt_of_nonneg (t : Tape) {i : ℤ} (h : 0 ≤ i) :
    cellAt t i = t.right.getD i.toNat none := by
  simp only [cellAt, h, ↓reduceIte]

private lemma cellAt_of_neg (t : Tape) {i : ℤ} (h : i < 0) :
    cellAt t i = t.left.getD (-i - 1).toNat none := by
  simp only [cellAt, show ¬0 ≤ i by omega, ↓reduceIte]

private lemma cellAt_zero (t : Tape) : cellAt t 0 = t.read := by
  obtain ⟨_, _, _ | _⟩ := t <;> rfl

private lemma cellAt_write (t : Tape) (o : Option ℕ) (i : ℤ) :
    cellAt (t.write o) i = if i = 0 then o else cellAt t i := by
  rcases lt_trichotomy i 0 with hi | rfl | hi
  · rw [cellAt_of_neg _ hi, cellAt_of_neg _ hi, ite_eq_right (by omega)]
    rfl
  · simp [cellAt, Tape.write]
  · rw [cellAt_of_nonneg _ hi.le, cellAt_of_nonneg _ hi.le, ite_eq_right (by omega)]
    simp only [Tape.write]
    rw [show i.toNat = (i - 1).toNat + 1 by omega, List.getD_cons_succ, getD_tail']

private lemma cellAt_move (t : Tape) (m : SignType) (i : ℤ) :
    cellAt (t.move m) i = cellAt t (i + m) := by
  rcases m with _ | _ | _
  · simp [Tape.move, SignType.zero_eq_zero]
  · rw [show ((SignType.neg : SignType) : ℤ) = -1 by simp [SignType.neg_eq_neg_one]]
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · rw [cellAt_of_neg _ hi, cellAt_of_neg _ (by omega)]
      simp only [Tape.move, getD_tail']
      congr 1
      omega
    · simp only [cellAt, Tape.move]
      cases t.left <;> rfl
    · rw [cellAt_of_nonneg _ hi.le, cellAt_of_nonneg _ (by omega)]
      simp only [Tape.move]
      rw [show i.toNat = (i + -1).toNat + 1 by omega, List.getD_cons_succ]
  · rw [show ((SignType.pos : SignType) : ℤ) = 1 by simp [SignType.pos_eq_one]]
    rcases lt_trichotomy i (-1) with hi | rfl | hi
    · rw [cellAt_of_neg _ (by omega), cellAt_of_neg _ (by omega)]
      simp only [Tape.move]
      rw [show (-i - 1).toNat = (-(i + 1) - 1).toNat + 1 by omega, List.getD_cons_succ]
    · simp only [cellAt, Tape.move, Tape.read]
      cases t.right <;> rfl
    · rw [cellAt_of_nonneg _ (by omega), cellAt_of_nonneg _ (by omega)]
      simp only [Tape.move, getD_tail']
      congr 1
      omega

private lemma head_move (t : Tape) (m : SignType) : (t.move m).head = t.head + m := by
  rcases m with _ | _ | _ <;>
    simp [Tape.move, SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one, sub_eq_add_neg]

private lemma head_apply (t : Tape) (a : Option (Option ℕ) × SignType) :
    (t.apply a).head = t.head + a.2 := by
  obtain ⟨_ | o, m⟩ := a <;> simp [Tape.apply, head_move, Tape.write]

private lemma cellAt_apply (t : Tape) (a : Option (Option ℕ) × SignType) (h z : ℤ) :
    cellAt (t.apply a) (z - (h + a.2)) =
      if z = h then a.1.getD (cellAt t (z - h)) else cellAt t (z - h) := by
  simp only [Tape.apply, cellAt_move]
  rw [show z - (h + a.2) + a.2 = z - h by ring]
  obtain ⟨_ | o, m⟩ := a
  · simp
  · simp [cellAt_write, sub_eq_zero]

private lemma apply_none_zero (t : Tape) : t.apply (none, 0) = t := rfl

private lemma length_left_apply (t : Tape) (a : Option (Option ℕ) × SignType)
    (h : 1 ≤ t.left.length) : ((t.apply a).left.length : ℤ) = t.left.length + a.2 := by
  obtain ⟨_ | o, _ | _ | _⟩ := a <;>
    simp [Tape.apply, Tape.move, Tape.write, SignType.zero_eq_zero, SignType.neg_eq_neg_one,
      SignType.pos_eq_one] <;> omega

private lemma length_right_apply (t : Tape) (a : Option (Option ℕ) × SignType)
    (h : 2 ≤ t.right.length) : ((t.apply a).right.length : ℤ) + a.2 = t.right.length := by
  obtain ⟨_ | o, _ | _ | _⟩ := a <;>
    simp [Tape.apply, Tape.move, Tape.write, Tape.read, SignType.zero_eq_zero,
      SignType.neg_eq_neg_one, SignType.pos_eq_one] <;> omega

private lemma cellAt_cut (r : ℕ) (t : Tape) (i : ℤ) :
    cellAt (cut r t) i = if -(r : ℤ) ≤ i ∧ i ≤ r then cellAt t i else none := by
  simp only [cellAt, cut, getD_take']
  split_ifs <;> first | rfl | omega

/-- The cells of `A ++ B.drop k`, when `A` is either exactly the part of the list `B` before `k`,
shifted by `s`, or `B` has no cells at `k` and beyond and neither has `A`. -/
private lemma getD_append_drop {A B : List (Option ℕ)} {k : ℕ} {s : ℤ}
    (hk : k ≤ B.length → (A.length : ℤ) + s = k)
    (hA : ∀ m : ℕ, (k : ℤ) ≤ m + s → A.getD m none = none) (m : ℕ) :
    (A ++ B.drop k).getD m none =
      if (m : ℤ) + s < k then A.getD m none else B.getD (m + s).toNat none := by
  by_cases hm : m < A.length
  · rw [getD_append_left' hm]
    split_ifs with h
    · rfl
    · rw [hA m (by omega)]
      by_cases hb : k ≤ B.length
      · have := hk hb
        omega
      · rw [getD_eq_none' (by omega)]
  · rw [getD_append_right' (by omega), getD_drop', getD_eq_none' (l := A) (by omega)]
    by_cases hb : k ≤ B.length
    · have := hk hb
      rw [ite_eq_right (by omega)]
      congr 1
      omega
    · rw [getD_eq_none' (by omega)]
      split_ifs
      · rfl
      · rw [getD_eq_none' (by omega)]

private lemma cellAt_paste {r : ℕ} {O I : Tape} {h h' : ℤ} (h₁ : h - r ≤ h') (h₂ : h' ≤ h + r)
    (hL : r ≤ O.left.length → (I.left.length : ℤ) + h = r + h')
    (hR : r + 1 ≤ O.right.length → (I.right.length : ℤ) + h' = h + r + 1)
    (hB : ∀ z, (z < h - r ∨ h + r < z) → cellAt I (z - h') = none) (z : ℤ) :
    cellAt (paste r O I) (z - h') =
      if h - r ≤ z ∧ z ≤ h + r then cellAt I (z - h') else cellAt O (z - h) := by
  by_cases hz : 0 ≤ z - h'
  · have e := getD_append_drop (A := I.right) (B := O.right) (k := r + 1) (s := h' - h)
      (by intro hb; have := hR hb; push_cast; omega)
      (fun m hm => by
        have := hB (h' + m) (Or.inr (by push_cast at hm; omega))
        simpa [cellAt] using this) (z - h').toNat
    simp only [cellAt, paste, ite_eq_left hz, e]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · have e := getD_append_drop (A := I.left) (B := O.left) (k := r) (s := h - h')
      (by intro hb; have := hL hb; omega)
      (fun m hm => by
        have := hB (h' - m - 1) (Or.inl (by omega))
        simp only [cellAt] at this
        rw [ite_eq_right (by omega)] at this
        rw [← this]
        congr 1
        omega) (-(z - h') - 1).toNat
    simp only [cellAt, paste, ite_eq_right hz, e]
    split_ifs <;> first | rfl | omega | (congr 1; omega)

/-! ### Steps on windows -/

/-- The action taken in the state `q`, with the input head reading `a` and the work-tape heads
reading `rs`. In a halting configuration, or without a matching transition, it changes nothing
but the state. -/
private def act (d : Desc) : Option ℕ → Option ℕ → List (Option ℕ) → Act
  | none, _, _ => ⟨.zero, [], none, none⟩
  | some q, a, rs =>
    match d.table.find? (·.1 = ⟨q, a, rs⟩) with
    | none => ⟨.zero, [], none, none⟩
    | some e => e.2

private lemma applyTapes_nil' (ts : List Tape) : applyTapes ts [] = ts := by
  cases ts <;> rfl

private lemma length_applyTapes (ts : List Tape) (as : List (Option (Option ℕ) × SignType)) :
    (applyTapes ts as).length = ts.length := by
  induction ts generalizing as with
  | nil => rfl
  | cons t ts ih => cases as <;> simp [applyTapes, ih]

private lemma getElem?_applyTapes (ts : List Tape) (as : List (Option (Option ℕ) × SignType))
    (k : ℕ) : (applyTapes ts as)[k]? = ts[k]?.map (·.apply (as.getD k (none, .zero))) := by
  induction ts generalizing as k with
  | nil => rfl
  | cons t ts ih =>
    cases as with
    | nil => simp [applyTapes, apply_none_zero]
    | cons a as => cases k <;> simp [applyTapes, ih]

private lemma stepWith_eq (d : Desc) (c : SCfg) (a : Option ℕ) :
    stepWith d c a = (⟨(act d c.state a (c.workTapes.map Tape.read)).state,
      moveInput c.inputPos a (act d c.state a (c.workTapes.map Tape.read)).inputTape,
      applyTapes c.workTapes (act d c.state a (c.workTapes.map Tape.read)).workTapes⟩,
      (act d c.state a (c.workTapes.map Tape.read)).output) := by
  obtain ⟨_ | q, p, ts⟩ := c
  · simp [stepWith, act, moveInput, applyTapes_nil']
  · simp only [stepWith, act]
    split <;> (rename_i h; simp [h, moveInput, applyTapes_nil'])

private lemma wstep_eq (d : Desc) (q : Option ℕ) (i : Tape) (ts : List Tape) :
    wstep d (q, i :: ts) =
      (((act d q (inSym i.read) (ts.map Tape.read)).state,
        moveIn i (inPos i.read) (moveInput (inPos i.read) (inSym i.read)
          (act d q (inSym i.read) (ts.map Tape.read)).inputTape) ::
          applyTapes ts (act d q (inSym i.read) (ts.map Tape.read)).workTapes),
        (act d q (inSym i.read) (ts.map Tape.read)).output) := by
  simp only [wstep, stepWith_eq]

/-- The coded input cell at position `z`: `some 0` at `0`, `some (a + 1)` for the input symbol `a`
and blank elsewhere. -/
private def inCell (x : List ℕ) (z : ℤ) : Option ℕ :=
  if z = 0 then some 0 else if 0 < z then x[(z - 1).toNat]?.map (· + 1) else none

private lemma inSym_inCell (x : List ℕ) (p : ℕ) : inSym (inCell x p) = inputSymbol x p := by
  rcases p with _ | p
  · simp [inSym, inCell, inputSymbol]
  · have h1 : ((p + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have h2 : (0 : ℤ) < ((p + 1 : ℕ) : ℤ) := by omega
    have h3 : (((p + 1 : ℕ) : ℤ) - 1).toNat = p := by omega
    rw [inCell, ite_eq_right h1, ite_eq_left h2, h3]
    cases h : x[p]? <;> simp [inputSymbol, inSym, h]

private lemma inPos_inCell (x : List ℕ) (p : ℕ) : inPos (inCell x p) = 0 ↔ p = 0 := by
  rcases p with _ | p
  · simp [inPos, inCell]
  · have h1 : ((p + 1 : ℕ) : ℤ) ≠ 0 := by omega
    have h2 : (0 : ℤ) < ((p + 1 : ℕ) : ℤ) := by omega
    rw [inCell, ite_eq_right h1, ite_eq_left h2]
    cases x[(((p + 1 : ℕ) : ℤ) - 1).toNat]? <;> simp [inPos]

private lemma moveIn_eq (i : Tape) {P p : ℕ} (hP : P = 0 ∨ P = 1) (hPp : P = 0 ↔ p = 0)
    (a : Option ℕ) (mv : SignType) :
    ∃ m : SignType, moveIn i P (moveInput P a mv) = i.move m ∧
      ((moveInput p a mv : ℕ) : ℤ) = p + m := by
  rcases hP with rfl | rfl
  · obtain rfl : p = 0 := hPp.1 rfl
    rcases mv with _ | _ | _
    · exact ⟨.zero, by simp [moveIn, moveInput, Tape.move], by simp [moveInput,
        SignType.zero_eq_zero]⟩
    · exact ⟨.zero, by simp [moveIn, moveInput, Tape.move], by simp [moveInput,
        SignType.zero_eq_zero]⟩
    · exact ⟨.pos, by simp [moveIn, moveInput], by simp [moveInput, SignType.pos_eq_one]⟩
  · have hp : p ≠ 0 := fun h => absurd (hPp.2 h) (by omega)
    rcases mv with _ | _ | _
    · exact ⟨.zero, by simp [moveIn, moveInput, Tape.move], by simp [moveInput,
        SignType.zero_eq_zero]⟩
    · exact ⟨.neg, by simp [moveIn, moveInput], by simp [moveInput, SignType.neg_eq_neg_one]; omega⟩
    · by_cases ha : a.isSome
      · exact ⟨.pos, by simp [moveIn, moveInput, ha], by simp [moveInput, SignType.pos_eq_one, ha, hp]⟩
      · exact ⟨.zero, by simp [moveIn, moveInput, ha, Tape.move], by
          simp [moveInput, SignType.zero_eq_zero, ha, hp]⟩

/-! ### Windows agreeing with tapes -/

/-- An abstract tape: its cells by absolute position, and the position of its head. -/
private abbrev ATape := (ℤ → Option ℕ) × ℤ

/-- The window `W`, with its head at the head of `F`, agrees with `F` within distance `n` of the
head. -/
private def Agr (n : ℕ) (W : Tape) (F : ATape) : Prop :=
  ∀ z, F.2 - n ≤ z → z ≤ F.2 + n → cellAt W (z - F.2) = F.1 z

/-- A run of `n` steps took the window `W` agreeing with `F` to `W'`, and the tape `F` to `F'`: the
head moved by at most `n`, the cells of `F` within distance `n` of its head are mirrored in `W'`,
the other cells of `F` and `W` are unchanged, and lists of `W` long enough for the run keep their
place. -/
private structure Tr (n : ℕ) (W : Tape) (F : ATape) (W' : Tape) (F' : ATape) : Prop where
  le_head : F.2 - n ≤ F'.2
  head_le : F'.2 ≤ F.2 + n
  real : ∀ z, z < F.2 - n ∨ F.2 + n < z → F'.1 z = F.1 z
  agree : ∀ z, F.2 - n ≤ z → z ≤ F.2 + n → cellAt W' (z - F'.2) = F'.1 z
  outside : ∀ z, z < F.2 - n ∨ F.2 + n < z → cellAt W' (z - F'.2) = cellAt W (z - F.2)
  left : n ≤ W.left.length → (W'.left.length : ℤ) + F.2 = W.left.length + F'.2
  right : n + 1 ≤ W.right.length → (W'.right.length : ℤ) + F'.2 = W.right.length + F.2

/-- The effect of an action on an abstract tape. -/
private def absApply (F : ATape) (a : Option (Option ℕ) × SignType) : ATape :=
  (fun z => if z = F.2 then a.1.getD (F.1 z) else F.1 z, F.2 + a.2)

/-- A work tape as an abstract tape. -/
private def realView (t : Tape) : ATape := (fun z => cellAt t (z - t.head), t.head)

private lemma realView_apply (t : Tape) (a : Option (Option ℕ) × SignType) :
    realView (t.apply a) = absApply (realView t) a := by
  simp only [realView, absApply, head_apply]
  congr 1
  funext z
  exact cellAt_apply t a t.head z

private lemma sign_bounds (m : SignType) : -1 ≤ (m : ℤ) ∧ (m : ℤ) ≤ 1 := by
  rcases m with _ | _ | _ <;>
    simp [SignType.zero_eq_zero, SignType.neg_eq_neg_one, SignType.pos_eq_one]

private lemma tr_zero {W : Tape} {F : ATape} (h : Agr 0 W F) : Tr 0 W F W F :=
  ⟨by omega, by omega, fun _ _ => rfl, h, fun _ _ => rfl, fun _ => by omega, fun _ => by omega⟩

private lemma tr_apply {W : Tape} {F : ATape} (h : Agr 1 W F)
    (a : Option (Option ℕ) × SignType) : Tr 1 W F (W.apply a) (absApply F a) := by
  obtain ⟨f, p⟩ := F
  have hm := sign_bounds a.2
  refine ⟨?_, ?_, fun z hz => ?_, fun z h1 h2 => ?_, fun z hz => ?_, fun hl => ?_, fun hr => ?_⟩
  · simp only [absApply]
    omega
  · simp only [absApply]
    omega
  · simp only [absApply]
    rw [ite_eq_right (by omega)]
  · simp only [absApply] at h1 h2 ⊢
    rw [cellAt_apply]
    split_ifs with hz
    · rw [h z h1 h2]
    · exact h z h1 h2
  · simp only [absApply] at hz ⊢
    rw [cellAt_apply, ite_eq_right (by omega)]
  · have := length_left_apply W a (by omega)
    simp only [absApply]
    omega
  · have := length_right_apply W a (by omega)
    simp only [absApply]
    omega

private lemma Agr.mono {n m : ℕ} {W : Tape} {F : ATape} (h : Agr n W F) (hmn : m ≤ n) :
    Agr m W F :=
  fun z h1 h2 => h z (by omega) (by omega)

private lemma Agr.cut {r : ℕ} {W : Tape} {F : ATape} (h : Agr r W F) : Agr r (cut r W) F :=
  fun z h1 h2 => by
    rw [cellAt_cut, ite_eq_left (by omega)]
    exact h z h1 h2

private lemma tr_paste {r : ℕ} {O I : Tape} {F F' : ATape} (hT : Tr r (cut r O) F I F')
    {lo hi : ℤ} (hO : ∀ z, lo ≤ z → z ≤ hi → cellAt O (z - F.2) = F.1 z) :
    (∀ z, lo ≤ z → z ≤ hi → cellAt (paste r O I) (z - F'.2) = F'.1 z) ∧
    (∀ z, z < F.2 - r ∨ F.2 + r < z → cellAt (paste r O I) (z - F'.2) = cellAt O (z - F.2)) ∧
    (r ≤ O.left.length → ((paste r O I).left.length : ℤ) + F.2 = O.left.length + F'.2) ∧
    (r + 1 ≤ O.right.length →
      ((paste r O I).right.length : ℤ) + F'.2 = O.right.length + F.2) := by
  have hl : r ≤ O.left.length → (I.left.length : ℤ) + F.2 = r + F'.2 := fun hl => by
    have := hT.left (by simp only [cut, List.length_take]; omega)
    simp only [cut, List.length_take] at this
    omega
  have hr : r + 1 ≤ O.right.length → (I.right.length : ℤ) + F'.2 = F.2 + r + 1 := fun hr => by
    have := hT.right (by simp only [cut, List.length_take]; omega)
    simp only [cut, List.length_take] at this
    omega
  have hP := cellAt_paste (O := O) hT.le_head hT.head_le hl hr
    (fun z hz => by rw [hT.outside z hz, cellAt_cut, ite_eq_right (by omega)])
  refine ⟨fun z h1 h2 => ?_, fun z hz => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hP]
    split_ifs with hz
    · exact hT.agree z hz.1 hz.2
    · rw [hO z h1 h2, hT.real z (by omega)]
  · rw [hP, ite_eq_right (by omega)]
  · have := hl h
    simp only [paste, List.length_append, List.length_drop]
    omega
  · have := hr h
    simp only [paste, List.length_append, List.length_drop]
    omega

private lemma agr_mid {n r s : ℕ} (hn : r + s = n) {W I : Tape} {F F₁ : ATape} (hW : Agr n W F)
    (h₁ : Tr r (cut r W) F I F₁) : Agr s (cut s (paste r W I)) F₁ := by
  obtain ⟨a, -, -, -⟩ := tr_paste h₁ (lo := F.2 - n) (hi := F.2 + n) hW
  have := h₁.le_head
  have := h₁.head_le
  exact Agr.cut fun z h1 h2 => a z (by omega) (by omega)

private lemma tr_comp {n r s : ℕ} (hn : r + s = n) {W I J : Tape} {F F₁ F₂ : ATape}
    (hW : Agr n W F) (h₁ : Tr r (cut r W) F I F₁) (h₂ : Tr s (cut s (paste r W I)) F₁ J F₂) :
    Tr n W F (paste s (paste r W I) J) F₂ := by
  have b₁ := h₁.le_head
  have b₂ := h₁.head_le
  have b₃ := h₂.le_head
  have b₄ := h₂.head_le
  obtain ⟨a₁, o₁, l₁, r₁⟩ := tr_paste h₁ (lo := F.2 - n) (hi := F.2 + n) hW
  obtain ⟨a₂, o₂, l₂, r₂⟩ := tr_paste h₂ (lo := F.2 - n) (hi := F.2 + n) a₁
  refine ⟨by omega, by omega, fun z hz => ?_, a₂, fun z hz => ?_, fun hl => ?_, fun hr => ?_⟩
  · rw [h₂.real z (by omega), h₁.real z (by omega)]
  · rw [o₂ z (by omega), o₁ z (by omega)]
  · have := l₁ (by omega)
    have := l₂ (by omega)
    omega
  · have := r₁ (by omega)
    have := r₂ (by omega)
    omega

/-! ### Correctness of the windowed simulation -/

private theorem sim_induction {motive : ℕ → Prop} (zero : motive 0) (one : motive 1)
    (step : ∀ n, (∀ m < n + 2, motive m) → motive (n + 2)) (n : ℕ) : motive n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact zero
    | 1, _ => exact one
    | n + 2, ih => exact step n ih

private lemma sim_zero (d : Desc) (w : Win) : sim d 0 w = (w, []) := by
  rw [sim]

private lemma sim_one (d : Desc) (w : Win) : sim d 1 w = ((wstep d w).1, (wstep d w).2.toList) := by
  rw [sim]

private lemma sim_add_two (d : Desc) (n : ℕ) (w : Win) :
    sim d (n + 2) w =
      (restore ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1)
        (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).1,
      (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).2 ++
        (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).2) := by
  rw [sim]

private lemma exists_getElem?_of_length {α β : Type} {l : List α} {l' : List β} {k : ℕ} {a : α}
    (h : l'.length = l.length) (hk : l[k]? = some a) : ∃ b, l'[k]? = some b := by
  have : k < l.length := (List.getElem?_eq_some_iff.1 hk).1
  exact ⟨l'[k], List.getElem?_eq_getElem (by omega)⟩

private lemma length_restore (r : ℕ) (o i : Win) :
    (restore r o i).2.length = min o.2.length i.2.length :=
  List.length_zipWith

private lemma getElem?_extract {r k : ℕ} {w : Win} {W : Tape} (h : w.2[k]? = some W) :
    (extract r w).2[k]? = some (cut r W) := by
  simp [extract, h]

private lemma getElem?_restore {r k : ℕ} {o i : Win} {W I : Tape} (hW : o.2[k]? = some W)
    (hI : i.2[k]? = some I) : (restore r o i).2[k]? = some (paste r W I) := by
  simp [restore, List.getElem?_zipWith, hW, hI]

/-- `n` steps from `c`, collecting the emitted symbols. -/
private def run (d : Desc) (x : List ℕ) (n : ℕ) (c : SCfg) : SCfg × List ℕ :=
  (stepOut d x)^[n] (c, [])

private lemma iterate_stepOut (d : Desc) (x : List ℕ) (n : ℕ) (c : SCfg) (o : List ℕ) :
    (stepOut d x)^[n] (c, o) = ((run d x n c).1, o ++ (run d x n c).2) := by
  induction n generalizing c o with
  | zero => simp [run]
  | succ n ih =>
    have h : run d x (n + 1) c = (stepOut d x)^[n] (stepOut d x (c, [])) :=
      Function.iterate_succ_apply _ _ _
    rw [h, Function.iterate_succ_apply, stepOut, stepOut, ih, ih]
    simp

private lemma run_add (d : Desc) (x : List ℕ) (m n : ℕ) (c : SCfg) :
    run d x (m + n) c = ((run d x n (run d x m c).1).1,
      (run d x m c).2 ++ (run d x n (run d x m c).1).2) := by
  change (stepOut d x)^[m + n] (c, []) = _
  rw [add_comm, Function.iterate_add_apply]
  exact iterate_stepOut d x n _ _

private lemma length_workTapes_run (d : Desc) (x : List ℕ) (n : ℕ) (c : SCfg) :
    (run d x n c).1.workTapes.length = c.workTapes.length := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_add]
    change (step d x (run d x n c).1).1.workTapes.length = _
    rw [step_eq_stepWith, stepWith_eq, length_applyTapes, ih]

/-- A configuration as abstract tapes: the coded input, then the work tapes. -/
private def view (x : List ℕ) (c : SCfg) : List ATape :=
  (inCell x, (c.inputPos : ℤ)) :: c.workTapes.map realView

private lemma length_view_run (d : Desc) (x : List ℕ) (n : ℕ) (c : SCfg) :
    (view x (run d x n c).1).length = (view x c).length := by
  simp [view, length_workTapes_run]

/-- **Correctness of the windowed simulation.** If every window agrees with its tape within
distance `n` of the head, then `n` windowed steps emit the symbols and reach the state of `n`
steps, and the windows keep agreeing with the tapes. -/
private theorem sim_spec (d : Desc) (x : List ℕ) (n : ℕ) : ∀ (c : SCfg) (w : Win),
    w.1 = c.state → w.2.length = (view x c).length →
    (∀ (k : ℕ) W F, w.2[k]? = some W → (view x c)[k]? = some F → Agr n W F) →
    (sim d n w).2 = (run d x n c).2 ∧ (sim d n w).1.1 = (run d x n c).1.state ∧
    (sim d n w).1.2.length = w.2.length ∧
    ∀ (k : ℕ) W F W' F', w.2[k]? = some W → (view x c)[k]? = some F →
      (sim d n w).1.2[k]? = some W' →
      (view x (run d x n c).1)[k]? = some F' → Tr n W F W' F' := by
  induction n using sim_induction with
  | zero =>
    intro c w hq _ hagr
    rw [sim_zero]
    refine ⟨rfl, hq, rfl, fun k W F W' F' hW hF hW' hF' => ?_⟩
    change (view x c)[k]? = some F' at hF'
    obtain rfl : W' = W := Option.some.inj (hW'.symm.trans hW)
    obtain rfl : F' = F := Option.some.inj (hF'.symm.trans hF)
    exact tr_zero (hagr k W' F' hW hF)
  | one =>
    rintro ⟨q, p, ts⟩ ⟨st, _ | ⟨i, ws⟩⟩ hq hlen hagr
    · simp [view] at hlen
    simp only at hq
    subst hq
    have hlen' : ws.length = ts.length := by simpa [view] using hlen
    have hi : Agr 1 i (inCell x, p) := hagr 0 i _ rfl rfl
    have hws : ∀ k W t, ws[k]? = some W → ts[k]? = some t → Agr 1 W (realView t) :=
      fun k W t hW ht => hagr (k + 1) W (realView t) (by simpa using hW) (by simp [view, ht])
    have hread : i.read = inCell x p := by
      have := hi p (by simp) (by simp)
      rwa [sub_self, cellAt_zero] at this
    have hreads : ws.map Tape.read = ts.map Tape.read := by
      apply List.ext_getElem?
      intro k
      simp only [List.getElem?_map]
      rcases hW : ws[k]? with _ | W
      · have : ts[k]? = none := by
          rw [List.getElem?_eq_none_iff] at hW ⊢
          omega
        simp [this]
      · obtain ⟨t, ht⟩ := exists_getElem?_of_length hlen'.symm hW
        have := hws k W t hW ht t.head (by simp [realView]) (by simp [realView])
        simp only [realView, sub_self, cellAt_zero] at this
        simp [ht, this]
    have hstep : step d x ⟨st, p, ts⟩ =
        (⟨(act d st (inputSymbol x p) (ts.map Tape.read)).state,
          moveInput p (inputSymbol x p) (act d st (inputSymbol x p) (ts.map Tape.read)).inputTape,
          applyTapes ts (act d st (inputSymbol x p) (ts.map Tape.read)).workTapes⟩,
          (act d st (inputSymbol x p) (ts.map Tape.read)).output) := by
      rw [step_eq_stepWith, stepWith_eq]
    obtain ⟨m, hm₁, hm₂⟩ := moveIn_eq i (P := inPos i.read) (p := p)
      (by unfold inPos; split_ifs <;> simp) (by rw [hread, inPos_inCell]) (inputSymbol x p)
      (act d st (inputSymbol x p) (ts.map Tape.read)).inputTape
    have hw : wstep d (st, i :: ws) =
        (((act d st (inputSymbol x p) (ts.map Tape.read)).state,
          i.move m :: applyTapes ws (act d st (inputSymbol x p) (ts.map Tape.read)).workTapes),
          (act d st (inputSymbol x p) (ts.map Tape.read)).output) := by
      rw [wstep_eq, hreads, hread, inSym_inCell, ← hm₁, hread]
    have hrun : run d x 1 ⟨st, p, ts⟩ =
        ((step d x ⟨st, p, ts⟩).1, (step d x ⟨st, p, ts⟩).2.toList) := by
      simp [run, stepOut]
    rw [sim_one, hw, hrun, hstep]
    refine ⟨rfl, rfl, by simp [length_applyTapes], fun k W F W' F' hW hF hW' hF' => ?_⟩
    rcases k with _ | k
    · simp only [List.getElem?_cons_zero, view, Option.some.injEq] at hW hF hW' hF'
      subst hW hF hW' hF'
      rw [hm₂, show ((inCell x, (p : ℤ) + m) : ATape) = absApply (inCell x, p) (none, m) by
        simp [absApply]]
      exact tr_apply hi (none, m)
    · simp only [List.getElem?_cons_succ, view, List.getElem?_map, getElem?_applyTapes,
        Option.map_eq_some_iff] at hW hF hW' hF'
      obtain ⟨t, ht, rfl⟩ := hF
      obtain ⟨W₀, hW₀, rfl⟩ := hW'
      obtain ⟨_, ht', rfl⟩ := hF'
      obtain ⟨_, ht'', rfl⟩ := ht'
      rw [hW] at hW₀
      cases hW₀
      rw [ht] at ht''
      cases ht''
      rw [realView_apply]
      exact tr_apply (hws k W t hW ht) _
  | step n ih =>
    intro c w hq hlen hagr
    have hrs : firstHalf (n + 2) + (n + 2) / 2 = n + 2 := by simp only [firstHalf]; omega
    have hr : firstHalf (n + 2) < n + 2 := by simp only [firstHalf]; omega
    have hs : (n + 2) / 2 < n + 2 := by omega
    rw [sim_add_two]
    generalize firstHalf (n + 2) = r at hrs hr ⊢
    generalize (n + 2) / 2 = s at hrs hs ⊢
    obtain ⟨o₁, q₁, l₁, t₁⟩ := ih r hr c (extract r w) hq (by simpa [extract] using hlen)
      (fun k W F hW hF => by
        simp only [extract, List.getElem?_map, Option.map_eq_some_iff] at hW
        obtain ⟨W₀, hW₀, rfl⟩ := hW
        exact ((hagr k W₀ F hW₀ hF).mono (by omega)).cut)
    have hle : ∀ r w, (extract r w).2.length = w.2.length := by simp [extract]
    have hlen₁ : (extract s (restore r w (sim d r (extract r w)).1)).2.length =
        (view x (run d x r c).1).length := by
      rw [hle]
      simp only [restore, List.length_zipWith, l₁, hle, length_view_run]
      omega
    obtain ⟨o₂, q₂, l₂, t₂⟩ := ih s hs (run d x r c).1 (extract s (restore r w (sim d r
      (extract r w)).1)) q₁ hlen₁ (fun k W F₁ hW hF₁ => by
        simp only [extract, restore, List.getElem?_map, Option.map_eq_some_iff,
          List.getElem?_zipWith_eq_some] at hW
        obtain ⟨_, ⟨W₀, I, hW₀, hI, rfl⟩, rfl⟩ := hW
        obtain ⟨F, hF⟩ := exists_getElem?_of_length (length_view_run d x r c).symm hF₁
        exact agr_mid hrs (hagr k W₀ F hW₀ hF)
          (t₁ k _ F I F₁ (getElem?_extract hW₀) hF hI hF₁))
    rw [← hrs, run_add]
    refine ⟨by rw [o₁, o₂], q₂, ?_, fun k W F W' F' hW hF hW' hF' => ?_⟩
    · rw [length_restore, l₂, hle, length_restore, l₁, hle]
      omega
    · simp only [restore, List.getElem?_zipWith_eq_some] at hW'
      obtain ⟨_, J, ⟨W₀, I, hW₀, hI, rfl⟩, hJ, rfl⟩ := hW'
      rw [hW] at hW₀
      cases hW₀
      obtain ⟨F₁, hF₁⟩ := exists_getElem?_of_length (length_view_run d x r c) hF
      exact tr_comp rfl (hrs ▸ hagr k W F hW hF)
        (t₁ k _ F I F₁ (getElem?_extract hW) hF hI hF₁)
        (t₂ k _ F₁ J F' (getElem?_extract (getElem?_restore hW hI)) hF₁ hJ hF')

/-- The input window of `initWin` agrees with the coded input everywhere. -/
private lemma cellAt_initWin_input (x : List ℕ) (z : ℤ) :
    cellAt ⟨0, [some 0], x.map fun a => some (a + 1)⟩ (z - (1 : ℕ)) = inCell x z := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [cellAt_of_neg _ (by omega), getD_eq_none' (by simp; omega)]
    simp [inCell, show z ≠ 0 by omega, show ¬0 < z by omega]
  · simp [cellAt, inCell]
  · rw [cellAt_of_nonneg _ (by omega)]
    simp [inCell, show z ≠ 0 by omega, hz, List.getD_eq_getElem?_getD]
    cases x[z.toNat - 1]? <;> simp

/-- **The windowed simulation computes the universal function**: started from the radius-`t`
windows of the initial configuration, `t` windowed steps give the output and the halting status
after `t` steps. -/
theorem universal_eq_sim (d : Desc) (x : List ℕ) (t : ℕ) :
    universal (d, x, t) = ((sim d t (extract t (initWin d x))).2,
      (sim d t (extract t (initWin d x))).1.1.isNone) := by
  have hagr : ∀ (k : ℕ) W F, (extract t (initWin d x)).2[k]? = some W →
      (view x (init d))[k]? = some F → Agr t W F := by
    intro k W F hW hF
    rcases k with _ | k
    · simp only [extract, initWin, view, List.map_cons, List.getElem?_cons_zero,
        Option.some.injEq] at hW hF
      subst hW hF
      exact Agr.cut fun z _ _ => cellAt_initWin_input x z
    · simp only [extract, initWin, view, init, List.map_cons, List.getElem?_cons_succ,
        List.getElem?_map, List.getElem?_replicate, Option.map_eq_some_iff] at hW hF
      split_ifs at hW hF with hk
      · obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hW
        obtain ⟨_, ⟨_, rfl⟩, rfl⟩ := hF
        exact Agr.cut fun z _ _ => rfl
      · simp at hW
  obtain ⟨o, q, -, -⟩ := sim_spec d x t (init d) (extract t (initWin d x)) rfl
    (by simp [extract, initWin, view, init]) hagr
  change ((run d x t (init d)).2, (run d x t (init d)).1.state.isNone) = _
  rw [o, q]

end Turing.MultiTapeTM.Universal.Windowed
