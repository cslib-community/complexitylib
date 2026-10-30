/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Windowed
import Mathlib.Tactic.Linarith

/-!
# The size of windowed configurations

Encodings of windowed configurations and of the problems, solutions and saved data of the
divide-and-conquer form of the windowed simulation, and bounds on their sizes.

A windowed configuration satisfies `Turing.MultiTapeTM.Universal.Windowed.WInv D B h L` when its
state is at most `D`, it has at most `D + 1` windows, the heads of its windows are within `h` of
`0`, every window holds at most `L` cells and every cell is at most `B`. Its encoded length is then
at most `winBound D B h L`. The windowed simulation of `n` steps with a description of length at
most `B` preserves the bounds on the state and the cells, moves the heads by at most one, adds at
most `2 * n` cells to every window, and emits at most `n` symbols, each at most the length of the
description.

## Main definitions

* `Turing.MultiTapeTM.Universal.Windowed.eWin`: the encoding of windowed configurations.
* `Turing.MultiTapeTM.Universal.Windowed.cells`: the number of cells of a window.
* `Turing.MultiTapeTM.Universal.Windowed.WInv`: bounds on a windowed configuration.
* `Turing.MultiTapeTM.Universal.Windowed.winBound`: the resulting bound on its encoded length.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.length_eWin_le`: the size of a windowed configuration.
* `Turing.MultiTapeTM.Universal.Windowed.WInv.sim`: the bounds after the windowed simulation.
* `Turing.MultiTapeTM.Universal.Windowed.WInv.restore_sim`: the bounds after simulating on cut
  windows and pasting them back.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

/-! ### Encodings -/

/-- Windowed configurations: the state and the windows. -/
abbrev eWin : Win ↪ List Bool := encPair eSym (encList eTape)

/-- Problems of the divide-and-conquer simulation: the description, the number of steps in unary
and the windows. -/
abbrev Prob := Desc × ℕ × Win

/-- The encoding of problems. -/
abbrev eProb : Prob ↪ List Bool := encPair eDesc (encPair encUnary eWin)

/-- Solutions: the windows after the steps and the emitted symbols. -/
abbrev Sol := Win × List ℕ

/-- The encoding of solutions. -/
abbrev eSol : Sol ↪ List Bool := encPair eWin (encList encUnary)

/-- Saved data: the number of steps of the second half, the windows after the first half and the
symbols it emitted. -/
abbrev Saved := ℕ × Win × List ℕ

/-- The encoding of saved data. -/
abbrev eSaved : Saved ↪ List Bool := encPair encUnary (encPair eWin (encList encUnary))

/-! ### Bounds -/

/-- The number of cells of a window. -/
@[expose] def cells (t : Tape) : ℕ := t.left.length + t.right.length

/-- Bounds on a windowed configuration: the state is at most `D`, there are at most `D + 1`
windows, their heads are within `h` of `0`, they hold at most `L` cells each, and every cell is at
most `B`. -/
structure WInv (D B h L : ℕ) (w : Win) : Prop where
  state : w.1.getD 0 ≤ D
  tapes : w.2.length ≤ D + 1
  head : ∀ t ∈ w.2, t.head.natAbs ≤ h
  cells : ∀ t ∈ w.2, cells t ≤ L
  val : ∀ t ∈ w.2, ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ B

/-- The bound on the encoded length of a windowed configuration satisfying `WInv D B h L`. -/
@[expose] def winBound (D B h L : ℕ) : ℕ :=
  2 * D + 3 + (D + 1) * (4 * h + 4 * L * (2 * B + 3) + 9)

/-- **The size of a windowed configuration.** -/
theorem length_eWin_le {D B h L : ℕ} {w : Win} (hw : WInv D B h L w) :
    (eWin w).length ≤ winBound D B h L := by
  obtain ⟨q, ts⟩ := w
  have h₁ := length_eSym_le hw.state
  have h₂ := length_encList_le eTape ts (b := 2 * h + 4 + 2 * L * (2 * B + 3)) fun t ht => by
    have hi := length_encInt_le t.head
    have hl := length_cells_le fun o ho => hw.val t ht o (List.mem_append_left t.right ho)
    have hr := length_cells_le fun o ho => hw.val t ht o (List.mem_append_right t.left ho)
    have hh := hw.head t ht
    have hc := Nat.mul_le_mul_right (2 * B + 3) (hw.cells t ht)
    simp only [cells] at hc
    simp only [eTape_apply, length_encPair]
    nlinarith
  have h₃ := Nat.mul_le_mul_right (2 * (2 * h + 4 + 2 * L * (2 * B + 3)) + 1) hw.tapes
  simp only [length_encPair, winBound]
  nlinarith

/-- Weakening the bounds. -/
theorem WInv.mono {D B h L h' L' : ℕ} {w : Win} (hw : WInv D B h L w) (hh : h ≤ h')
    (hL : L ≤ L') : WInv D B h' L' w :=
  ⟨hw.state, hw.tapes, fun t ht => (hw.head t ht).trans hh, fun t ht => (hw.cells t ht).trans hL,
    hw.val⟩

/-- Cutting windows of radius `r`: the heads are at `0` and every window holds at most `2 * r + 1`
cells, and at most as many as before. -/
theorem WInv.extract {D B h L : ℕ} {w : Win} (hw : WInv D B h L w) (r : ℕ) :
    WInv D B 0 (min L (2 * r + 1)) (Windowed.extract r w) := by
  refine ⟨hw.state, by simpa [Windowed.extract] using hw.tapes, ?_, ?_, ?_⟩ <;>
    simp only [Windowed.extract, List.mem_map] <;> rintro _ ⟨t, ht, rfl⟩
  · simp [cut]
  · have := hw.cells t ht
    simp only [Windowed.cells, cut, List.length_take] at this ⊢
    omega
  · intro o ho
    simp only [cut, List.mem_append] at ho
    exact hw.val t ht o (List.mem_append.mpr (ho.imp List.mem_of_mem_take List.mem_of_mem_take))

private lemma q₀_le' (d : Desc) : d.q₀ ≤ descLen d := by
  simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega

private lemma tapes_le' (d : Desc) : d.tapes ≤ descLen d := by
  simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]; omega

/-- The windows of the initial configuration. -/
theorem winv_initWin (d : Desc) (x : List ℕ) :
    WInv (descLen d) (descLen d + listMax id x + 1) 0 (x.length + 1) (initWin d x) := by
  refine ⟨by simpa [initWin] using q₀_le' d, by simpa [initWin] using tapes_le' d, ?_, ?_, ?_⟩ <;>
    simp only [initWin, List.mem_cons, List.mem_replicate] <;> rintro t (rfl | ⟨-, rfl⟩)
  · simp
  · simp
  · simp [cells]; omega
  · simp [cells]
  · intro o ho
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_map] at ho
    rcases ho with rfl | ⟨a, ha, rfl⟩
    · simp
    · have := le_listMax (f := id) ha
      simp only [id] at this
      simp only [Option.getD_some]
      omega
  · simp

/-! ### One step -/

/-- The cells of a window are at most `B`. -/
private abbrev ValLe (B : ℕ) (t : Tape) : Prop := ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ B

private lemma valLe_move {B : ℕ} {t : Tape} (h : ValLe B t) (m : SignType) :
    ValLe B (t.move m) := by
  have hl : ∀ o ∈ t.left, o.getD 0 ≤ B := fun o ho => h o (List.mem_append_left _ ho)
  have hr : ∀ o ∈ t.right, o.getD 0 ≤ B := fun o ho => h o (List.mem_append_right _ ho)
  have hd : ∀ {l : List (Option ℕ)}, (∀ o ∈ l, o.getD 0 ≤ B) → (l.headD none).getD 0 ≤ B := by
    intro l hl
    cases l with
    | nil => simp
    | cons o l => exact hl o (List.mem_cons_self ..)
  intro o ho
  rcases m with _ | _ | _ <;>
    simp only [Tape.move, Tape.read, List.mem_append, List.mem_cons] at ho
  · exact h o (List.mem_append.mpr ho)
  · rcases ho with ho | rfl | ho
    · exact hl o (List.mem_of_mem_tail ho)
    · exact hd hl
    · exact hr o ho
  · rcases ho with (rfl | ho) | ho
    · exact hd hr
    · exact hl o ho
    · exact hr o (List.mem_of_mem_tail ho)

private lemma valLe_apply {B : ℕ} {t : Tape} (h : ValLe B t) {a : TapeAct}
    (ha : (a.1.getD none).getD 0 ≤ B) : ValLe B (t.apply a) := by
  obtain ⟨_ | o, m⟩ := a
  · exact valLe_move h m
  · refine valLe_move (fun o' ho' => ?_) m
    simp only [Option.elim, Tape.write, List.mem_append, List.mem_cons] at ho'
    rcases ho' with ho' | rfl | ho'
    · exact h o' (List.mem_append_left _ ho')
    · exact ha
    · exact h o' (List.mem_append_right _ (List.mem_of_mem_tail ho'))

private lemma head_move (t : Tape) (m : SignType) : (t.move m).head.natAbs ≤ t.head.natAbs + 1 := by
  rcases m with _ | _ | _ <;> simp only [Tape.move] <;> omega

private lemma cells_move (t : Tape) (m : SignType) : cells (t.move m) ≤ cells t + 1 := by
  rcases m with _ | _ | _ <;> simp only [Tape.move, cells, List.length_cons, List.length_tail] <;>
    omega

private lemma head_apply (t : Tape) (a : TapeAct) :
    (t.apply a).head.natAbs ≤ t.head.natAbs + 1 := by
  obtain ⟨_ | o, m⟩ := a
  · exact head_move t m
  · exact head_move (t.write o) m

private lemma cells_apply (t : Tape) (a : TapeAct) : cells (t.apply a) ≤ cells t + 2 := by
  obtain ⟨_ | o, m⟩ := a
  · have := cells_move t m
    simp only [Tape.apply, Option.elim]
    omega
  · have := cells_move (t.write o) m
    have : cells (t.write o) ≤ cells t + 1 := by
      simp only [cells, Tape.write, List.length_cons, List.length_tail]; omega
    simp only [Tape.apply, Option.elim]
    omega

/-- How a window may change in `n` steps: the head moves by at most one and at most `2 * n` cells
are added. -/
private abbrev Grow (n : ℕ) (t t' : Tape) : Prop :=
  t'.head.natAbs ≤ t.head.natAbs + 1 ∧ cells t' ≤ cells t + 2 * n

private lemma forall₂_grow_refl (n : ℕ) (ts : List Tape) : List.Forall₂ (Grow n) ts ts :=
  List.forall₂_same.mpr fun _ _ => ⟨by omega, by omega⟩

private lemma grow_moveIn (t : Tape) (p p' : ℕ) : Grow 1 t (moveIn t p p') := by
  unfold moveIn
  split_ifs
  · exact ⟨head_move t _, by have := cells_move t .pos; omega⟩
  · exact ⟨head_move t _, by have := cells_move t .neg; omega⟩
  · exact ⟨by omega, by omega⟩

private lemma valLe_moveIn {B : ℕ} {t : Tape} (h : ValLe B t) (p p' : ℕ) :
    ValLe B (moveIn t p p') := by
  unfold moveIn
  split_ifs
  · exact valLe_move h _
  · exact valLe_move h _
  · exact h

/-- Applying actions moves every head by at most one and adds at most two cells. -/
private lemma forall₂_applyTapes (ts : List Tape) (as : List TapeAct) :
    List.Forall₂ (Grow 1) ts (applyTapes ts as) := by
  induction ts generalizing as with
  | nil => cases as <;> exact .nil
  | cons t ts ih =>
    cases as with
    | nil => exact forall₂_grow_refl 1 _
    | cons a as => exact .cons ⟨head_apply t a, by have := cells_apply t a; omega⟩ (ih as)

private lemma valLe_applyTapes {B : ℕ} {ts : List Tape} (hts : ∀ t ∈ ts, ValLe B t)
    {as : List TapeAct} (has : ∀ a ∈ as, (a.1.getD none).getD 0 ≤ B) :
    ∀ t ∈ applyTapes ts as, ValLe B t := by
  induction ts generalizing as with
  | nil => cases as <;> simp [applyTapes]
  | cons t ts ih =>
    cases as with
    | nil => exact hts
    | cons a as =>
      simp only [applyTapes, List.mem_cons, forall_eq_or_imp]
      exact ⟨valLe_apply (hts t (List.mem_cons_self ..)) (has a (List.mem_cons_self ..)),
        ih (fun t ht => hts t (List.mem_cons_of_mem _ ht))
          (fun a ha => has a (List.mem_cons_of_mem _ ha))⟩

private lemma length_act_le {d : Desc} {e : Key × Act} (he : e ∈ d.table) :
    (eAct e.2).length ≤ descLen d := by
  have := length_le_encList_of_mem (encPair eKey eAct) he
  simp only [descLen, eDesc_apply, length_encPair] at this ⊢
  omega

private lemma getD_le_length (o : Option ℕ) : o.getD 0 ≤ (eSym o).length := by
  cases o <;> simp

private lemma state_le {d : Desc} {e : Key × Act} (he : e ∈ d.table) :
    e.2.state.getD 0 ≤ descLen d := by
  have := length_act_le he
  have := getD_le_length e.2.state
  simp only [eAct_apply, length_encPair] at *
  omega

private lemma output_le {d : Desc} {e : Key × Act} (he : e ∈ d.table) :
    e.2.output.getD 0 ≤ descLen d := by
  have := length_act_le he
  have := getD_le_length e.2.output
  simp only [eAct_apply, length_encPair] at *
  omega

private lemma write_le {d : Desc} {e : Key × Act} (he : e ∈ d.table) {ta : TapeAct}
    (hta : ta ∈ e.2.workTapes) : (ta.1.getD none).getD 0 ≤ descLen d := by
  have h₁ := length_act_le he
  have h₂ := length_le_encList_of_mem eTA hta
  have h₃ := getD_le_length (ta.1.getD none)
  have h₄ : (eSym (ta.1.getD none)).length ≤ (encOption eSym ta.1).length := by
    cases ta.1 <;> simp
  simp only [eAct_apply, length_encPair] at *
  omega

/-- The three outcomes of a step: halted, no transition, or a transition from the table. -/
private lemma stepWith_cases (d : Desc) (c : SCfg) (a : Option ℕ) :
    stepWith d c a = (c, none) ∨ stepWith d c a = (⟨none, c.inputPos, c.workTapes⟩, none) ∨
      ∃ e ∈ d.table, stepWith d c a = (⟨e.2.state, moveInput c.inputPos a e.2.inputTape,
        applyTapes c.workTapes e.2.workTapes⟩, e.2.output) := by
  unfold stepWith
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr (Or.inl rfl)
    · next e he => exact Or.inr (Or.inr ⟨e, List.mem_of_find?_eq_some he, rfl⟩)

/-- The outcomes of a windowed step. -/
private lemma wstep_cases (d : Desc) (w : Win) :
    wstep d w = (w, none) ∨ ∃ i ts p p', w.2 = i :: ts ∧
      (wstep d w = ((w.1, moveIn i p p' :: ts), none) ∨
        wstep d w = ((none, moveIn i p p' :: ts), none) ∨
        ∃ e ∈ d.table,
          wstep d w = ((e.2.state, moveIn i p p' :: applyTapes ts e.2.workTapes), e.2.output)) := by
  obtain ⟨q, _ | ⟨i, ts⟩⟩ := w
  · exact Or.inl rfl
  · refine Or.inr ⟨i, ts, inPos i.read,
      (stepWith d ⟨q, inPos i.read, ts⟩ (inSym i.read)).1.inputPos, rfl, ?_⟩
    rcases stepWith_cases d ⟨q, inPos i.read, ts⟩ (inSym i.read) with h | h | ⟨e, he, h⟩ <;>
      simp only [wstep, h]
    · simp
    · simp
    · exact Or.inr (Or.inr ⟨e, he, rfl⟩)

/-! ### Pasting -/

/-- Pasting replaces the cells of the cut window by those of the inner window. -/
private lemma cells_paste (r : ℕ) (o i : Tape) :
    cells (paste r o i) + cells (cut r o) = cells o + cells i := by
  simp only [cells, paste, cut, List.length_append, List.length_drop, List.length_take]
  omega

private lemma forall₂_zipWith_paste {r k : ℕ} {ts ts' : List Tape}
    (h : List.Forall₂ (fun t t' => cells t' ≤ cells (cut r t) + k) ts ts') :
    List.Forall₂ (fun t t' => t'.head = 0 ∧ cells t' ≤ cells t + k) ts
      (List.zipWith (paste r) ts ts') := by
  induction h with
  | nil => exact .nil
  | @cons t t' _ _ h _ ih =>
    exact .cons ⟨rfl, by have := cells_paste r t t'; omega⟩ ih

private lemma exists_of_forall₂ {α β : Type} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction h with
  | nil => simp at hb
  | cons hab _ ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨a, ha, h⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, h⟩

private lemma forall₂_trans {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (H : ∀ a b c, R a b → S b c → T a c) {l₁ : List α} {l₂ : List β}
    {l₃ : List γ} (h₁ : List.Forall₂ R l₁ l₂) (h₂ : List.Forall₂ S l₂ l₃) :
    List.Forall₂ T l₁ l₃ := by
  induction h₁ generalizing l₃ with
  | nil => cases h₂; exact .nil
  | cons h _ ih =>
    cases h₂ with
    | cons h' h₂ => exact .cons (H _ _ _ h h') (ih h₂)

private lemma exists_of_mem_zipWith {α β γ : Type} {f : α → β → γ} {l₁ : List α} {l₂ : List β}
    {c : γ} (h : c ∈ List.zipWith f l₁ l₂) : ∃ a ∈ l₁, ∃ b ∈ l₂, c = f a b := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨a, List.mem_cons_self .., b, List.mem_cons_self .., rfl⟩
      · obtain ⟨a', ha', b', hb', rfl⟩ := ih h
        exact ⟨a', List.mem_cons_of_mem _ ha', b', List.mem_cons_of_mem _ hb', rfl⟩

private lemma valLe_restore {B r : ℕ} {outer inner : Win} (ho : ∀ t ∈ outer.2, ValLe B t)
    (hi : ∀ t ∈ inner.2, ValLe B t) : ∀ t ∈ (restore r outer inner).2, ValLe B t := by
  intro t ht
  obtain ⟨o, hmo, i, hmi, rfl⟩ := exists_of_mem_zipWith ht
  intro v hv
  simp only [paste, List.mem_append] at hv
  rcases hv with (hv | hv) | (hv | hv)
  · exact hi i hmi v (List.mem_append_left _ hv)
  · exact ho o hmo v (List.mem_append_left _ (List.mem_of_mem_drop hv))
  · exact hi i hmi v (List.mem_append_right _ hv)
  · exact ho o hmo v (List.mem_append_right _ (List.mem_of_mem_drop hv))

private lemma valLe_extract {B r : ℕ} {w : Win} (h : ∀ t ∈ w.2, ValLe B t) :
    ∀ t ∈ (extract r w).2, ValLe B t := by
  simp only [extract, List.mem_map]
  rintro _ ⟨t, ht, rfl⟩ o ho
  simp only [cut, List.mem_append] at ho
  exact h t ht o (List.mem_append.mpr (ho.imp List.mem_of_mem_take List.mem_of_mem_take))

/-! ### The windowed simulation -/

/-- The windowed simulation of `n + 2` steps: the first half on cut windows, pasted back, then the
second half. -/
theorem sim_add_two (d : Desc) (n : ℕ) (w : Win) :
    sim d (n + 2) w =
      (restore ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1)
        (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
          (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).1,
        (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).2 ++
          (sim d ((n + 2) / 2) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
            (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))).2) := by
  rw [sim]

private lemma firstHalf_lt (n : ℕ) : firstHalf (n + 2) < n + 2 := by
  simp only [firstHalf]; omega

private lemma half_lt (n : ℕ) : (n + 2) / 2 < n + 2 := by omega

private lemma firstHalf_add_half (n : ℕ) : firstHalf n + n / 2 = n := by
  simp only [firstHalf]; omega

/-- Paste the windows, simulated for `m` steps after cutting with radius `r`, back. -/
private lemma forall₂_restore {r m : ℕ} {w inner : Win}
    (h : List.Forall₂ (Grow m) (extract r w).2 inner.2) :
    List.Forall₂ (fun t t' => t'.head = 0 ∧ cells t' ≤ cells t + 2 * m) w.2
      (restore r w inner).2 :=
  forall₂_zipWith_paste (List.forall₂_map_left_iff.mp h |>.imp fun _ _ h => h.2)

/-- Window by window, the windowed simulation of `n` steps moves the heads by at most one and
adds at most `2 * n` cells. -/
private lemma forall₂_sim (d : Desc) (n : ℕ) (w : Win) :
    List.Forall₂ (Grow n) w.2 (sim d n w).1.2 := by
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  rcases n with _ | _ | n
  · rw [sim]; exact forall₂_grow_refl 0 _
  · rw [sim]
    rcases wstep_cases d w with h | ⟨i, ts, p, p', hw, h | h | ⟨e, -, h⟩⟩ <;> rw [h] <;>
      try rw [hw]
    · exact forall₂_grow_refl 1 _
    · exact .cons (grow_moveIn i p p') (forall₂_grow_refl 1 _)
    · exact .cons (grow_moveIn i p p') (forall₂_grow_refl 1 _)
    · exact .cons (grow_moveIn i p p') (forall₂_applyTapes ts _)
  · rw [sim_add_two]
    have h₁ := forall₂_restore (ih _ (firstHalf_lt n) (extract (firstHalf (n + 2)) w))
    have h₂ := forall₂_restore (ih _ (half_lt n) (extract ((n + 2) / 2)
      (restore (firstHalf (n + 2)) w
        (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1)))
    have hs := firstHalf_add_half (n + 2)
    exact forall₂_trans (fun _ _ _ ha hb => ⟨by omega, by omega⟩) h₁ h₂

/-- The windowed simulation keeps a bound on the state above the length of the description. -/
private lemma state_sim {d : Desc} {D : ℕ} (hD : descLen d ≤ D) (n : ℕ) {w : Win}
    (hw : w.1.getD 0 ≤ D) : (sim d n w).1.1.getD 0 ≤ D := by
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  rcases n with _ | _ | n
  · rw [sim]; exact hw
  · rw [sim]
    rcases wstep_cases d w with h | ⟨i, ts, p, p', -, h | h | ⟨e, he, h⟩⟩ <;> rw [h]
    · exact hw
    · exact hw
    · simp
    · exact (state_le he).trans hD
  · rw [sim_add_two]
    exact ih _ (half_lt n) (ih _ (firstHalf_lt n) hw)

/-- The windowed simulation keeps a bound on the cells above the length of the description. -/
private lemma valLe_sim {d : Desc} {B : ℕ} (hB : descLen d ≤ B) (n : ℕ) {w : Win}
    (hw : ∀ t ∈ w.2, ValLe B t) : ∀ t ∈ (sim d n w).1.2, ValLe B t := by
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  rcases n with _ | _ | n
  · rw [sim]; exact hw
  · rw [sim]
    rcases wstep_cases d w with h | ⟨i, ts, p, p', hw', h | h | ⟨e, he, h⟩⟩ <;> rw [h]
    · exact hw
    all_goals
      rw [hw'] at hw
      simp only [List.mem_cons, forall_eq_or_imp] at hw ⊢
      refine ⟨valLe_moveIn hw.1 p p', ?_⟩
    · exact hw.2
    · exact hw.2
    · exact valLe_applyTapes hw.2 fun ta hta => (write_le he hta).trans hB
  · rw [sim_add_two]
    exact valLe_restore (valLe_restore hw (ih _ (firstHalf_lt n) (valLe_extract hw)))
      (ih _ (half_lt n) (valLe_extract
        (valLe_restore hw (ih _ (firstHalf_lt n) (valLe_extract hw)))))

/-- **The bounds after the windowed simulation** of `n` steps, for a description of length at most
`B`: the heads move by at most one and every window gains at most `2 * n` cells. -/
theorem WInv.sim {d : Desc} {B h L : ℕ} (hDB : descLen d ≤ B) {w : Win}
    (hw : WInv (descLen d) B h L w) (n : ℕ) :
    WInv (descLen d) B (h + 1) (L + 2 * n) (Windowed.sim d n w).1 := by
  have hf := forall₂_sim d n w
  refine ⟨state_sim le_rfl n hw.state, by rw [length_sim]; exact hw.tapes, fun t' ht' => ?_,
    fun t' ht' => ?_, valLe_sim hDB n hw.val⟩ <;>
    obtain ⟨t, ht, hg⟩ := exists_of_forall₂ hf ht'
  · have := hw.head t ht
    have := hg.1
    omega
  · have := hw.cells t ht
    have := hg.2
    omega

/-- **The bounds after simulating on cut windows and pasting them back**: simulating `m` steps on
the windows of radius `r` and pasting the result back adds at most `2 * m` cells to every window,
and puts the heads at `0`. -/
theorem WInv.restore_sim {d : Desc} {B h L : ℕ} (hDB : descLen d ≤ B) {w : Win}
    (hw : WInv (descLen d) B h L w) (r m : ℕ) :
    WInv (descLen d) B 0 (L + 2 * m) (restore r w (Windowed.sim d m (Windowed.extract r w)).1) := by
  have hf := forall₂_restore (forall₂_sim d m (Windowed.extract r w))
  refine ⟨state_sim le_rfl m hw.state, ?_, fun t' ht' => ?_, fun t' ht' => ?_,
    valLe_restore hw.val (valLe_sim hDB m (valLe_extract hw.val))⟩
  · rw [← hf.length_eq]
    exact hw.tapes
  · obtain ⟨t, -, hg⟩ := exists_of_forall₂ hf ht'
    simp [hg.1]
  · obtain ⟨t, ht, hg⟩ := exists_of_forall₂ hf ht'
    have := hw.cells t ht
    have := hg.2
    omega

/-- The windowed simulation of `n` steps emits at most `n` symbols, each at most the length of the
description. -/
private lemma sim_out (d : Desc) (n : ℕ) (w : Win) :
    (sim d n w).2.length ≤ n ∧ ∀ o ∈ (sim d n w).2, o ≤ descLen d := by
  induction n using Nat.strong_induction_on generalizing w with
  | _ n ih =>
  rcases n with _ | _ | n
  · rw [sim]; simp
  · rw [sim]
    rcases wstep_cases d w with h | ⟨i, ts, p, p', -, h | h | ⟨e, he, h⟩⟩ <;> rw [h]
    · simp
    · simp
    · simp
    · have := output_le he
      revert this
      cases e.2.output <;> simp
  · rw [sim_add_two]
    have h₁ := ih _ (firstHalf_lt n) (extract (firstHalf (n + 2)) w)
    have h₂ := ih _ (half_lt n) (extract ((n + 2) / 2) (restore (firstHalf (n + 2)) w
      (sim d (firstHalf (n + 2)) (extract (firstHalf (n + 2)) w)).1))
    have hs := firstHalf_add_half (n + 2)
    refine ⟨by rw [List.length_append]; omega, fun o ho => ?_⟩
    rcases List.mem_append.mp ho with ho | ho
    · exact h₁.2 o ho
    · exact h₂.2 o ho

/-- The windowed simulation of `n` steps emits at most `n` symbols. -/
theorem length_sim_out (d : Desc) (n : ℕ) (w : Win) : (sim d n w).2.length ≤ n :=
  (sim_out d n w).1

/-- The symbols emitted by the windowed simulation are at most the length of the description. -/
theorem le_of_mem_sim_out {d : Desc} {n : ℕ} {w : Win} {o : ℕ} (ho : o ∈ (sim d n w).2) :
    o ≤ descLen d :=
  (sim_out d n w).2 o ho

/-- The size of the emitted symbols. -/
theorem length_encList_sim_out_le (d : Desc) (n : ℕ) (w : Win) :
    (encList encUnary (sim d n w).2).length ≤ n * (2 * descLen d + 1) :=
  (length_encList_le encUnary _ (b := descLen d) fun o ho => by
    simpa [encUnary_apply] using le_of_mem_sim_out ho).trans
    (Nat.mul_le_mul_right _ (length_sim_out d n w))

end Turing.MultiTapeTM.Universal.Windowed
