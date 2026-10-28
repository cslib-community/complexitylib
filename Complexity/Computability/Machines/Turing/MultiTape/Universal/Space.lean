/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is the space of a run path since cslib #1133 and #1122

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Bound
public import Complexity.Computability.Machines.Turing.MultiTape.Universal.Correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The simulation in the space of the simulated machine

A zipper holds a cell only at a position its head has visited, and the visited positions of a
head that moves by at most one cell per step form an interval around `0`. So the configuration of
the simulation after `j` steps takes space linear in the number of visited cells, times the size
of a symbol, plus the length of the input head in binary
(`Turing.MultiTapeTM.Universal.length_eCfg_le_space`). For the description of a machine, the
visited cells are those of the machine (`Turing.MultiTapeTM.Universal.simSpace_desc`).

## Main definitions

* `Turing.MultiTapeTM.Universal.simSpace`: the number of cells visited by the simulation.

## Main results

* `Turing.MultiTapeTM.Universal.length_eCfg_le_space`: the size of the configuration, in the
  visited cells.
* `Turing.MultiTapeTM.Universal.simSpace_desc`: for descriptions of machines, the visited cells
  are the space of the machine.
-/

namespace Turing.MultiTapeTM.Universal

/-! ### Zippers within the visited positions -/

/-- The cells of the zipper `t` are at positions in `V`. -/
structure Tape.Covered (t : Tape) (V : Set ℤ) : Prop where
  left : ∀ k < t.left.length, t.head - 1 - k ∈ V
  right : ∀ k < t.right.length, t.head + k ∈ V

lemma Tape.Covered.mono {t : Tape} {V W : Set ℤ} (h : t.Covered V) (hVW : V ⊆ W) :
    t.Covered W :=
  ⟨fun k hk => hVW (h.left k hk), fun k hk => hVW (h.right k hk)⟩

/-- An action keeps a zipper covered, if the heads before and after are covered. -/
lemma Tape.Covered.apply {t : Tape} {V : Set ℤ} (h : t.Covered V) (hh : t.head ∈ V)
    (a : Option (Option ℕ) × SignType) (ha : (t.apply a).head ∈ V) : (t.apply a).Covered V := by
  obtain ⟨hl, hr⟩ := h
  obtain ⟨w, m⟩ := a
  have hw : (w.elim t t.write).Covered V ∧ (w.elim t t.write).head = t.head := by
    rcases w with _ | o
    · exact ⟨⟨hl, hr⟩, rfl⟩
    · refine ⟨⟨hl, fun k hk => ?_⟩, rfl⟩
      simp only [Option.elim, Tape.write, List.length_cons, List.length_tail] at hk ⊢
      rcases k with _ | k
      · simpa using hh
      · exact hr (k + 1) (by omega)
  obtain ⟨⟨hl', hr'⟩, hhd⟩ := hw
  simp only [Tape.apply] at ha ⊢
  generalize w.elim t t.write = u at *
  rcases m with _ | _ | _
  · exact ⟨hl', hr'⟩
  · have ha' : u.head - 1 ∈ V := by simpa [Tape.move] using ha
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only [Tape.move, List.length_tail] at hk ⊢
      rw [show u.head - 1 - 1 - (k : ℤ) = u.head - 1 - ((k + 1 : ℕ) : ℤ) by push_cast; omega]
      exact hl' (k + 1) (by omega)
    · simp only [Tape.move, List.length_cons] at hk ⊢
      rcases k with _ | k
      · simpa using ha'
      · rw [show u.head - 1 + ((k + 1 : ℕ) : ℤ) = u.head + k by push_cast; omega]
        exact hr' k (by omega)
  · refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · simp only [Tape.move, List.length_cons] at hk ⊢
      rcases k with _ | k
      · simpa [hhd] using hh
      · rw [show u.head + 1 - 1 - ((k + 1 : ℕ) : ℤ) = u.head - 1 - k by push_cast; omega]
        exact hl' k (by omega)
    · simp only [Tape.move, List.length_tail] at hk ⊢
      rw [show u.head + 1 + (k : ℤ) = u.head + ((k + 1 : ℕ) : ℤ) by push_cast; omega]
      exact hr' (k + 1) (by omega)

/-- A covered zipper holds at most as many cells as there are positions in `V`. -/
lemma Tape.Covered.length_le {t : Tape} {V : Finset ℤ} (h : t.Covered V) :
    t.left.length + t.right.length ≤ V.card := by
  let f : ℕ → ℤ := fun k => if k < t.left.length then t.head - 1 - k
    else t.head + (k - t.left.length : ℕ)
  have := Finset.card_le_card_of_injOn f (s := Finset.range (t.left.length + t.right.length))
    (t := V) (fun k hk => by
      simp only [Finset.coe_range, Set.mem_Iio] at hk
      simp only [Finset.mem_coe, f]
      split_ifs with h'
      · exact h.left k h'
      · exact h.right _ (by omega))
    (fun a ha b hb hab => by
      simp only [Finset.coe_range, Set.mem_Iio, f] at ha hb hab
      split_ifs at hab <;> omega)
  simpa using this

/-! ### A step on a single work tape -/

lemma apply_none (t : Tape) : t.apply (none, 0) = t := rfl

lemma getD_applyTapes (ts : List Tape) (as : List TapeAct) {i : ℕ} (hi : i < ts.length) :
    (applyTapes ts as).getD i .blank = (ts.getD i .blank).apply (as.getD i (none, 0)) := by
  induction ts generalizing as i with
  | nil => simp at hi
  | cons t ts ih =>
    rcases as with _ | ⟨a, as⟩
    · rcases i with _ | i <;> simp [applyTapes, apply_none, List.getD_eq_getElem?_getD]
    · rcases i with _ | i
      · simp [applyTapes]
      · simpa [applyTapes] using ih as (by simpa using hi)

lemma length_step_workTapes (d : Desc) (x : List ℕ) (c : SCfg) :
    (step d x c).1.workTapes.length = c.workTapes.length := by
  rw [step_eq_stepWith, show stepWith d c (inputSymbol x c.inputPos) =
      stepWith ((d, c), inputSymbol x c.inputPos).1.1 ((d, c), inputSymbol x c.inputPos).1.2
        ((d, c), inputSymbol x c.inputPos).2 from rfl, stepWith_eq]
  split_ifs
  · exact length_applyTapes_eq _ _
  · rfl
  · rfl

/-- A step applies an action to every work tape. -/
lemma step_tape (d : Desc) (x : List ℕ) (c : SCfg) (i : ℕ) :
    ∃ a, (step d x c).1.workTapes.getD i .blank = (c.workTapes.getD i .blank).apply a := by
  rcases Nat.lt_or_ge i c.workTapes.length with hi | hi
  · rw [step_eq_stepWith, show stepWith d c (inputSymbol x c.inputPos) =
      stepWith ((d, c), inputSymbol x c.inputPos).1.1 ((d, c), inputSymbol x c.inputPos).1.2
        ((d, c), inputSymbol x c.inputPos).2 from rfl, stepWith_eq]
    split_ifs
    · exact ⟨_, getD_applyTapes _ _ hi⟩
    · exact ⟨(none, 0), (apply_none _).symm⟩
    · exact ⟨(none, 0), (apply_none _).symm⟩
  · refine ⟨(none, 0), ?_⟩
    rw [apply_none, List.getD_eq_default _ _ hi, List.getD_eq_default _ _
      (by rw [length_step_workTapes]; exact hi)]

lemma head_apply (t : Tape) (a : TapeAct) :
    (t.apply a).head = t.head - 1 ∨ (t.apply a).head = t.head ∨ (t.apply a).head = t.head + 1 := by
  obtain ⟨w, m⟩ := a
  have : (w.elim t t.write).head = t.head := by cases w <;> rfl
  rcases m with _ | _ | _ <;> simp [Tape.apply, Tape.move, this]

/-! ### Visited positions -/

variable (d : Desc) (x : List ℕ)

/-- The configuration of the simulation after `j` steps. -/
@[expose] public def run (j : ℕ) : SCfg := ((stepOut d x)^[j] (init d, [])).1

/-- The head of work tape `i` after `j` steps. -/
@[expose] public def headAt (j i : ℕ) : ℤ := ((run d x j).workTapes.getD i .blank).head

/-- The positions visited by the head of work tape `i` up to step `j`. -/
@[expose] public def visited (j i : ℕ) : Finset ℤ := (Finset.range (j + 1)).image (headAt d x · i)

/-- The number of work-tape cells visited by the simulation up to step `j`. -/
@[expose] public def simSpace (j : ℕ) : ℕ := ∑ i ∈ Finset.range d.tapes, (visited d x j i).card

lemma run_succ (j : ℕ) : run d x (j + 1) = (step d x (run d x j)).1 := by
  simp only [run, Function.iterate_succ_apply', stepOut]

lemma visited_mono {j j' : ℕ} (h : j ≤ j') (i : ℕ) : visited d x j i ⊆ visited d x j' i :=
  Finset.image_subset_image fun a ha => by
    simp only [Finset.mem_range] at ha ⊢
    omega

lemma headAt_mem (j i : ℕ) : headAt d x j i ∈ visited d x j i :=
  Finset.mem_image.mpr ⟨j, by simp, rfl⟩

lemma headAt_zero (i : ℕ) : headAt d x 0 i = 0 := by
  simp only [headAt, run, Function.iterate_zero_apply, init]
  rcases Nat.lt_or_ge i d.tapes with h | h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h, Tape.blank]

/-- Every work tape is covered by the positions its head has visited. -/
lemma covered (j i : ℕ) : ((run d x j).workTapes.getD i .blank).Covered (visited d x j i) := by
  induction j with
  | zero =>
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;>
    · simp only [run, Function.iterate_zero_apply, init] at hk
      rcases Nat.lt_or_ge i d.tapes with h | h <;>
        simp [List.getD_eq_getElem?_getD, h, Tape.blank] at hk
  | succ j ih =>
    obtain ⟨a, ha⟩ := step_tape d x (run d x j) i
    rw [run_succ, ha]
    refine (ih.mono (visited_mono d x (Nat.le_succ j) i)).apply
      (visited_mono d x (Nat.le_succ j) i (headAt_mem d x j i)) a ?_
    rw [← ha, ← run_succ]
    exact headAt_mem d x (j + 1) i

/-- The visited positions contain every position between `0` and the head. -/
lemma mem_visited (j i : ℕ) {z : ℤ} (hz : min 0 (headAt d x j i) ≤ z ∧ z ≤ max 0 (headAt d x j i)) :
    z ∈ visited d x j i := by
  induction j generalizing z with
  | zero =>
    rw [headAt_zero] at hz
    rw [show z = 0 by omega, ← headAt_zero d x i]
    exact headAt_mem d x 0 i
  | succ j ih =>
    obtain ⟨a, ha⟩ := step_tape d x (run d x j) i
    have hstep : headAt d x (j + 1) i = headAt d x j i - 1 ∨
        headAt d x (j + 1) i = headAt d x j i ∨ headAt d x (j + 1) i = headAt d x j i + 1 := by
      simp only [headAt, run_succ, ha]
      exact head_apply _ a
    by_cases h : z = headAt d x (j + 1) i
    · exact h ▸ headAt_mem d x (j + 1) i
    · exact visited_mono d x (Nat.le_succ j) i (ih (by omega))

lemma natAbs_headAt_lt (j i : ℕ) : (headAt d x j i).natAbs < (visited d x j i).card := by
  have := Finset.card_le_card (s := Finset.Icc (min 0 (headAt d x j i)) (max 0 (headAt d x j i)))
    (t := visited d x j i) fun z hz => mem_visited d x j i (Finset.mem_Icc.mp hz)
  rw [Int.card_Icc] at this
  omega

/-! ### The size of the configuration -/

lemma length_eTape_le_space {D : ℕ} {t : Tape} {V : Finset ℤ} (hc : t.Covered V)
    (hh : t.head.natAbs < V.card) (hv : ∀ o ∈ t.left ++ t.right, o.getD 0 ≤ D) :
    (eTape t).length ≤ 3 * (2 * D + 5) * V.card := by
  have h₁ := length_encInt_le t.head
  have h₂ := length_cells_le fun o ho => hv o (List.mem_append_left t.right ho)
  have h₃ := length_cells_le fun o ho => hv o (List.mem_append_right t.left ho)
  have h₄ := hc.length_le
  have h₅ := Nat.mul_le_mul_right (2 * D + 3) (show t.left.length ≤ V.card by omega)
  have h₆ := Nat.mul_le_mul_right (2 * D + 3) (show t.right.length ≤ V.card by omega)
  have h₇ : 3 * (2 * D + 5) * V.card = 3 * (V.card * (2 * D + 3)) + 6 * V.card := by ring
  simp only [eTape_apply, length_encPair]
  omega

lemma length_encList_eq_sum {α : Type} [Inhabited α] (enc : α ↪ List Bool) (l : List α) :
    (encList enc l).length =
      ∑ i ∈ Finset.range l.length, (2 * (enc (l.getD i default)).length + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [encList_cons, List.length_append, length_frame, ih, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

lemma length_run_workTapes (j : ℕ) : (run d x j).workTapes.length = d.tapes := by
  induction j with
  | zero => simp [run, init]
  | succ j ih => rw [run_succ, length_step_workTapes, ih]

/-- **The size of the configuration** after `j` steps, in the number of visited cells: linear in
the visited cells and the number of work tapes, times the size of a symbol, plus the length of
the position of the input head in binary. -/
public theorem length_eCfg_le_space (j : ℕ) :
    (eCfg (run d x j)).length ≤ 2 * descLen d + 3 + 2 * (encNat (x.length + 1)).length + 1 +
      3 * (2 * (descLen d) + 5) * 2 * simSpace d x j + d.tapes := by
  obtain ⟨hinv, -, -⟩ := inv_iterate d x j
  have hk := length_run_workTapes d x j
  have h₁ := length_eSym_le hinv.state
  have h₂ := ComputableTidilyInO.length_encNat_mono hinv.inputPos
  have h₃ : (encList eTape (run d x j).workTapes).length ≤
      ∑ i ∈ Finset.range d.tapes, (2 * (3 * (2 * descLen d + 5) * (visited d x j i).card) + 1) := by
    rw [length_encList_eq_sum, hk]
    refine Finset.sum_le_sum fun i hi => Nat.add_le_add_right (Nat.mul_le_mul_left 2
      (length_eTape_le_space (covered d x j i) (natAbs_headAt_lt d x j i) fun o ho => ?_)) 1
    have hi : i < (run d x j).workTapes.length := by rw [hk]; exact Finset.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ hi] at ho
    exact (hinv.workTapes _ (List.getElem_mem hi)).val o ho
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h₃
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at h₃
  simp only [eCfg_apply, length_encPair, simSpace, run] at *
  nlinarith

/-! ### Descriptions of machines -/

variable {k : ℕ} {Symbol State : Type} [Fintype State] [Fintype Symbol]
  (eS : State ↪ ℕ) (eY : Symbol ↪ ℕ)

/-- The heads of the simulation are those of the machine. -/
lemma headAt_desc (tm : MultiTapeTM k Symbol State) (x : List Symbol) (j : ℕ) (i : Fin k) :
    headAt (desc eS eY tm) (x.map eY) j i = (tm.runFrom (tm.initCfg x) j).workTapePos i := by
  have := congrArg (·.workTapePos i) (toCfg_iterate eS eY tm x j).1
  simpa [SCfg.toCfg, Cfg.map, headAt, run, List.getD_eq_getElem?_getD] using this.symm

/-- **The space of the simulation** of the description of a machine is the space of the machine. -/
public theorem simSpace_desc (tm : MultiTapeTM k Symbol State) (x : List Symbol) (j : ℕ) :
    simSpace (desc eS eY tm) (x.map eY) j =
      (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg x) j).space := by
  -- vendored: `space` is the space of a run path since cslib #1117
  rw [MultiTapeNTM.RunPath.space]
  simp only [simSpace, MultiTapeNTM.RunPath.spaceUsedByTape]
  rw [show (desc eS eY tm).tapes = k from rfl, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.ext fun z => ?_)
  rw [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic]
  simp only [visited, Finset.mem_image, Finset.mem_range, headAt_desc]
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, by omega, rfl⟩

end Turing.MultiTapeTM.Universal
