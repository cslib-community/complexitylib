/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Moving words between the ends of tapes

Small native machines that move a word along its tape or between two tapes, specified by runs
between `Turing.tapesCfg` configurations (`Turing.MultiTapeTM.RunsBetween`), so that the words may
sit anywhere on their tapes. They implement a stack kept on a tape that grows to the left.

## Main definitions

* `Turing.MultiTapeTM.seekEnd`: move the head from the first cell of a word to the cell after it.
* `Turing.MultiTapeTM.copyBack`: move a word, read from its end, to the front of the word on a
  second tape.
* `Turing.MultiTapeTM.eraseFrame`: erase a framed word (`Turing.MultiTapeTM.frame`) at the front
  of a tape.
* `Turing.MultiTapeTM.popFrame`: move a framed word at the front of a tape to a blank second tape,
  prefixed by `[true, true]`, or write `[false]` there if the first tape is blank.

## Main results

* `Turing.MultiTapeTM.runsBetween_seekEnd`, `Turing.MultiTapeTM.runsBetween_copyBack`,
  `Turing.MultiTapeTM.runsBetween_eraseFrame`, `Turing.MultiTapeTM.runsBetween_popFrame_nil`,
  `Turing.MultiTapeTM.runsBetween_popFrame_frame`: their runs, in time linear in the words moved.
-/

public section

namespace Turing

variable {Symbol : Type*} {input : List Symbol}

/-! ### Shifted words -/

lemma tapeOfList_eq_ite (w : List Symbol) (z : ℤ) :
    tapeOfList w z = if 0 ≤ z then w[z.toNat]? else none := by
  cases z with
  | ofNat n => simp
  | negSucc n => simp

lemma tapeOfList_cons_of_ne (x : Symbol) (l : List Symbol) {z : ℤ} (hz : z ≠ 0) :
    tapeOfList (x :: l) z = tapeOfList l (z - 1) := by
  rcases z with (_ | n) | n
  · exact absurd rfl hz
  · change tapeOfList (x :: l) ((n + 1 : ℕ) : ℤ) = tapeOfList l (((n + 1 : ℕ) : ℤ) - 1)
    have h : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    rw [h]
    rfl
  · rw [tapeOfList_negSucc, ((tapeOfList_eq_none_iff _ _).mpr (Or.inl (by omega)))]

/-- Writing after the end of a shifted word appends to it. -/
lemma update_shifted_append (w : List Symbol) (x : Symbol) (o : ℤ) :
    Function.update (fun z => tapeOfList w (z - o)) (o + w.length) (some x) =
      fun z => tapeOfList (w ++ [x]) (z - o) := by
  funext z
  rw [tapeOfList_append_single]
  by_cases hz : z = o + w.length
  · subst hz
    simp
  · rw [Function.update_of_ne hz, Function.update_of_ne (by omega)]

/-- Erasing the first cell of a shifted word drops its first letter. -/
lemma update_shifted_cons_none (x : Symbol) (l : List Symbol) (o : ℤ) :
    Function.update (fun z => tapeOfList (x :: l) (z - o)) o none =
      fun z => tapeOfList l (z - (o + 1)) := by
  funext z
  by_cases hz : z = o
  · subst hz
    rw [Function.update_self]
    exact ((tapeOfList_eq_none_iff _ _).mpr (by omega)).symm
  · rw [Function.update_of_ne hz, tapeOfList_cons_of_ne _ _ (by omega)]
    congr 1
    omega

/-- Erasing the last cell of a shifted word drops its last letter. -/
lemma update_shifted_append_none (l : List Symbol) (x : Symbol) (o : ℤ) :
    Function.update (fun z => tapeOfList (l ++ [x]) (z - o)) (o + l.length) none =
      fun z => tapeOfList l (z - o) := by
  funext z
  by_cases hz : z = o + l.length
  · subst hz
    rw [Function.update_self]
    exact ((tapeOfList_eq_none_iff _ _).mpr (by omega)).symm
  · rw [Function.update_of_ne hz, tapeOfList_append_single, Function.update_of_ne (by omega)]

/-- Writing before the first cell of a shifted word prepends to it. -/
lemma update_shifted_pred (v : List Symbol) (x : Symbol) (o : ℤ) :
    Function.update (fun z => tapeOfList v (z - o)) (o - 1) (some x) =
      fun z => tapeOfList (x :: v) (z - (o - 1)) := by
  funext z
  by_cases hz : z = o - 1
  · subst hz
    simp [tapeOfList_zero]
  · rw [Function.update_of_ne hz, tapeOfList_cons_of_ne _ _ (by omega)]
    congr 1
    omega

/-- The first letter of a shifted word, read at its first cell. -/
lemma tapeOfList_cons_sub_self (x : Symbol) (l : List Symbol) (o : ℤ) :
    tapeOfList (x :: l) (o - o) = some x := by
  rw [sub_self, tapeOfList_zero]
  rfl

/-- The cell after a shifted word is blank. -/
lemma tapeOfList_add_length_sub (w : List Symbol) (o : ℤ) :
    tapeOfList w (o + w.length - o) = none := by
  rw [tapeOfList_eq_none_iff]
  omega

/-- The cell before a shifted word is blank. -/
lemma tapeOfList_sub_one_sub (w : List Symbol) (o : ℤ) : tapeOfList w (o - 1 - o) = none := by
  rw [tapeOfList_eq_none_iff]
  omega

namespace MultiTapeTM

/-- A run of one more step, split after its first step. -/
private lemma runFrom_succ_eq_step {k : ℕ} {State : Type*} (tm : MultiTapeTM k Symbol State)
    (c : Cfg k Symbol State input) (n : ℕ) : tm.runFrom c (n + 1) = tm.runFrom (tm.step c) n := by
  rw [Nat.add_comm, runFrom_add, runFrom_one]

/-! ### Moving the head to the end of a word -/

/-- Moves the head of its only tape right until it reads a blank. -/
noncomputable def seekEnd (Symbol : Type*) : MultiTapeTM 1 Symbol Unit :=
  ofTr () fun _ _ work =>
    match work 0 with
    | some _ =>
      { inputTape := 0, workTapes := fun _ => (none, 1), output := none, state := some () }
    | none => { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

theorem runFrom_seekEnd (w suf pre : List Symbol) (hw : w = pre ++ suf) (o : ℤ)
    (out : List Symbol) :
    (seekEnd Symbol).runFrom ((tapesCfg input (fun _ => w) (fun _ => o)
      (fun _ => o + pre.length) out).withState (some ())) (suf.length + 1) =
      (tapesCfg input (fun _ => w) (fun _ => o) (fun _ => o + w.length) out).withState none := by
  induction suf generalizing pre with
  | nil =>
    subst hw
    simp only [List.append_nil, List.length_nil, Nat.zero_add]
    rw [runFrom_one]
    refine step_tapesCfg (a := ⟨0, fun _ => (none, 0), none, none⟩) ?_ rfl rfl
      (fun _ => rfl) (fun _ => by simp)
    simp only [seekEnd, tr_ofTr, tapeOfList_add_length_sub]
  | cons x suf ih =>
    rw [show (x :: suf).length + 1 = 1 + (suf.length + 1) by simp; omega, runFrom_add, runFrom_one,
      step_tapesCfg (a := ⟨0, fun _ => (none, 1), none, some ()⟩)
        (h' := fun _ => o + (pre ++ [x]).length) ?_ rfl rfl (fun _ => rfl)
        (fun _ => by simp; omega)]
    · exact ih (pre ++ [x]) (by simp [hw])
    · have : tapeOfList w (o + pre.length - o) = some x := by
        rw [add_sub_cancel_left, tapeOfList_ofNat, hw]
        simp
      simp only [seekEnd, tr_ofTr, this]

theorem runsBetween_seekEnd (w : List Symbol) (o : ℤ) (out : List Symbol) :
    RunsBetween (seekEnd Symbol) (tapesCfg input (fun _ => w) (fun _ => o) (fun _ => o) out)
      (tapesCfg input (fun _ => w) (fun _ => o) (fun _ => o + w.length) out)
      (w.length + 1) (w.length + 1 + 1) := by
  have := runFrom_seekEnd (input := input) w w [] (by simp) o out
  exact (RunsBetween.of_runFrom (by simpa using this)).mono le_rfl (by omega)

/-! ### Moving a word to the front of another -/

/-- The states of `Turing.MultiTapeTM.copyBack`. -/
inductive CopyBackState
  /-- Step both heads left. -/
  | first
  /-- Move one letter. -/
  | loop
  deriving DecidableEq

instance : Fintype CopyBackState := ⟨{.first, .loop}, fun q => by cases q <;> simp⟩

/-- Started with the head of tape `0` on the cell after a word and the head of tape `1` on the
first cell of another, moves the first word letter by letter, from its end, to the front of the
second, erasing it, and halts with both heads on the first cells of their words. -/
noncomputable def copyBack (Symbol : Type*) : MultiTapeTM 2 Symbol CopyBackState :=
  ofTr .first fun q _ work =>
    match q with
    | .first =>
      { inputTape := 0, workTapes := fun _ => (none, -1), output := none, state := some .loop }
    | .loop =>
      match work 0 with
      | some x =>
        { inputTape := 0, workTapes := ![(some none, -1), (some (some x), -1)], output := none,
          state := some .loop }
      | none => { inputTape := 0, workTapes := fun _ => (none, 1), output := none, state := none }

theorem runFrom_copyBack_loop (w v u : List Symbol) (oA oB oB' : ℤ) (hu : u = w ++ v)
    (hB : oB' = oB - w.length) (out : List Symbol) :
    (copyBack Symbol).runFrom ((tapesCfg input ![w, v] ![oA, oB] ![oA + w.length - 1, oB - 1]
      out).withState (some .loop)) (w.length + 1) =
      (tapesCfg input ![[], u] ![oA, oB'] ![oA, oB'] out).withState none := by
  induction w using List.reverseRecOn generalizing v oB with
  | nil =>
    subst hu hB
    simp only [List.length_nil, Nat.zero_add, Nat.cast_zero, sub_zero, add_zero]
    rw [runFrom_one]
    refine step_tapesCfg (a := ⟨0, fun _ => (none, 1), none, none⟩) ?_ rfl rfl
      (fun i => by fin_cases i <;> rfl) (fun i => by fin_cases i <;> simp)
    simp only [copyBack, tr_ofTr, Matrix.cons_val_zero, tapeOfList_sub_one_sub]
  | append_singleton l x ih =>
    rw [show (l ++ [x]).length + 1 = 1 + (l.length + 1) by simp; omega, runFrom_add, runFrom_one,
      step_tapesCfg (a := ⟨0, ![(some none, -1), (some (some x), -1)], none, some .loop⟩)
        (ws' := ![l, x :: v]) (o' := ![oA, oB - 1]) (h' := ![oA + l.length - 1, oB - 1 - 1])
        ?_ rfl rfl ?_ ?_]
    · exact ih (x :: v) (oB - 1) (by simp [hu]) (by simp [hB]; omega)
    · have hr : tapeOfList (l ++ [x]) (oA + ((l ++ [x]).length : ℤ) - 1 - oA) = some x := by
        rw [show oA + ((l ++ [x]).length : ℤ) - 1 - oA = (l.length : ℕ) by simp; omega,
          tapeOfList_ofNat]
        simp
      simp only [copyBack, tr_ofTr, Matrix.cons_val_zero, hr]
    · intro i
      fin_cases i
      · dsimp only [Fin.zero_eta, Matrix.cons_val_zero]
        rw [show oA + ((l ++ [x]).length : ℤ) - 1 = oA + l.length by
          simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one]; omega,
          update_shifted_append_none]
      · dsimp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact update_shifted_pred v x oB
    · intro i
      fin_cases i
      · simp; omega
      · simp; omega

theorem runsBetween_copyBack (w v : List Symbol) (oA oB : ℤ) (out : List Symbol) :
    RunsBetween (copyBack Symbol) (tapesCfg input ![w, v] ![oA, oB] ![oA + w.length, oB] out)
      (tapesCfg input ![[], w ++ v] ![oA, oB - w.length] ![oA, oB - w.length] out)
      (w.length + 2) (2 * (w.length + 2 + 1)) := by
  refine RunsBetween.of_runFrom ?_
  rw [show w.length + 2 = 1 + (w.length + 1) by omega, runFrom_add, runFrom_one,
    step_tapesCfg (a := ⟨0, fun _ => (none, -1), none, some .loop⟩)
      (ws' := ![w, v]) (o' := ![oA, oB]) (h' := ![oA + w.length - 1, oB - 1])
      (by simp only [copyBack, tr_ofTr, q₀_ofTr]) rfl rfl (fun i => by fin_cases i <;> rfl)
      (fun i => by fin_cases i <;> simp <;> omega)]
  exact runFrom_copyBack_loop w v _ oA oB _ rfl rfl out

/-! ### Erasing a framed word -/

/-- The states of `Turing.MultiTapeTM.eraseFrame`. -/
inductive EraseFrameState
  /-- At the start of a pair, or at the final `false`. -/
  | loop
  /-- At the second cell of a pair. -/
  | bit
  deriving DecidableEq

instance : Fintype EraseFrameState := ⟨{.loop, .bit}, fun q => by cases q <;> simp⟩

/-- Erases the framed word at the head of its only tape, moving right, and halts on the cell after
it. -/
noncomputable def eraseFrame : MultiTapeTM 1 Bool EraseFrameState :=
  ofTr .loop fun q _ work =>
    match q, work 0 with
    | .loop, some true =>
      { inputTape := 0, workTapes := fun _ => (some none, 1), output := none, state := some .bit }
    | .loop, some false =>
      { inputTape := 0, workTapes := fun _ => (some none, 1), output := none, state := none }
    | .bit, some _ =>
      { inputTape := 0, workTapes := fun _ => (some none, 1), output := none, state := some .loop }
    | _, none => { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

theorem runFrom_eraseFrame (w rest u : List Bool) (o o' : ℤ) {input : List Bool}
    (hu : u = frame w ++ rest) (ho : o' = o + (2 * w.length + 1 : ℕ)) (out : List Bool) :
    eraseFrame.runFrom ((tapesCfg input (fun _ => u) (fun _ => o) (fun _ => o) out).withState
      (some .loop)) (2 * w.length + 1) =
      (tapesCfg input (fun _ => rest) (fun _ => o') (fun _ => o') out).withState none := by
  induction w generalizing u o with
  | nil =>
    subst hu ho
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, frame_nil, List.singleton_append]
    rw [runFrom_one]
    refine step_tapesCfg (a := ⟨0, fun _ => (some none, 1), none, none⟩) ?_ rfl rfl
      (fun _ => update_shifted_cons_none _ _ _) (fun _ => by simp)
    simp only [eraseFrame, tr_ofTr, tapeOfList_cons_sub_self]
  | cons b w ih =>
    subst hu
    rw [frame_cons, show 2 * (b :: w).length + 1 = 2 * w.length + 1 + 1 + 1 by simp; omega,
      runFrom_succ_eq_step, runFrom_succ_eq_step, List.cons_append, List.cons_append,
      step_tapesCfg (a := ⟨0, fun _ => (some none, 1), none, some .bit⟩)
        (ws' := fun _ => b :: (frame w ++ rest)) (o' := fun _ => o + 1) (h' := fun _ => o + 1)
        (by simp only [eraseFrame, tr_ofTr, tapeOfList_cons_sub_self]) rfl rfl
        (fun _ => update_shifted_cons_none _ _ _) (fun _ => by simp),
      step_tapesCfg (a := ⟨0, fun _ => (some none, 1), none, some .loop⟩)
        (ws' := fun _ => frame w ++ rest) (o' := fun _ => o + 1 + 1) (h' := fun _ => o + 1 + 1)
        (by simp only [eraseFrame, tr_ofTr, tapeOfList_cons_sub_self]) rfl rfl
        (fun _ => update_shifted_cons_none _ _ _) (fun _ => by simp)]
    exact ih _ (o + 1 + 1) rfl (by simp [ho]; omega)

theorem runsBetween_eraseFrame (w rest : List Bool) (o : ℤ) {input : List Bool}
    (out : List Bool) :
    RunsBetween eraseFrame (tapesCfg input (fun _ => frame w ++ rest) (fun _ => o) (fun _ => o) out)
      (tapesCfg input (fun _ => rest) (fun _ => o + (frame w).length)
        (fun _ => o + (frame w).length) out)
      (2 * w.length + 1) (2 * w.length + 1 + 1) :=
  (RunsBetween.of_runFrom (runFrom_eraseFrame (input := input) w rest _ o _ rfl
    (by simp [length_frame]) out)).mono le_rfl (by omega)

/-! ### Popping a framed word -/

/-- The states of `Turing.MultiTapeTM.popFrame`. -/
inductive PopFrameState
  /-- Reading the first cell of tape `0`. -/
  | start
  /-- Writing the second `true` of the prefix. -/
  | pre
  /-- At the start of a pair, or at the final `false`. -/
  | loop
  /-- At the second cell of a pair. -/
  | bit
  deriving DecidableEq

instance : Fintype PopFrameState := ⟨{.start, .pre, .loop, .bit}, fun q => by cases q <;> simp⟩

/-- If tape `0` is blank under its head, writes `false` at the head of tape `1`. Otherwise writes
`[true, true]` and then moves the framed word at the head of tape `0` there, erasing it. Both
heads move right as they go. The specifications below start with a blank tape `1`; the loop
`Turing.MultiTapeTM.runFrom_popFrame_loop` appends to any word ending before the head. -/
noncomputable def popFrame : MultiTapeTM 2 Bool PopFrameState :=
  ofTr .start fun q _ work =>
    match q, work 0 with
    | .start, none =>
      { inputTape := 0, workTapes := ![(none, 0), (some (some false), 1)], output := none,
        state := none }
    | .start, some _ =>
      { inputTape := 0, workTapes := ![(none, 0), (some (some true), 1)], output := none,
        state := some .pre }
    | .pre, _ =>
      { inputTape := 0, workTapes := ![(none, 0), (some (some true), 1)], output := none,
        state := some .loop }
    | .loop, some true =>
      { inputTape := 0, workTapes := ![(some none, 1), (some (some true), 1)], output := none,
        state := some .bit }
    | .loop, some false =>
      { inputTape := 0, workTapes := ![(some none, 1), (some (some false), 1)], output := none,
        state := none }
    | .bit, some b =>
      { inputTape := 0, workTapes := ![(some none, 1), (some (some b), 1)], output := none,
        state := some .loop }
    | _, none => { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }

theorem runFrom_popFrame_loop (w rest u acc acc' : List Bool) (oS oS' oR hR' : ℤ)
    {input : List Bool} (hu : u = frame w ++ rest) (hacc : acc' = acc ++ frame w)
    (hS : oS' = oS + (2 * w.length + 1 : ℕ)) (hR : hR' = oR + acc'.length) (out : List Bool) :
    popFrame.runFrom ((tapesCfg input ![u, acc] ![oS, oR] ![oS, oR + acc.length] out).withState
      (some .loop)) (2 * w.length + 1) =
      (tapesCfg input ![rest, acc'] ![oS', oR] ![oS', hR'] out).withState none := by
  induction w generalizing u acc oS with
  | nil =>
    subst hu hacc hS hR
    simp only [List.length_nil, Nat.mul_zero, Nat.zero_add, frame_nil, List.singleton_append]
    rw [runFrom_one]
    refine step_tapesCfg (a := ⟨0, ![(some none, 1), (some (some false), 1)], none, none⟩) ?_ rfl
      rfl ?_ ?_
    · simp only [popFrame, tr_ofTr, Matrix.cons_val_zero, tapeOfList_cons_sub_self]
    · intro i
      fin_cases i
      · dsimp only [Fin.zero_eta, Matrix.cons_val_zero]
        exact update_shifted_cons_none _ _ _
      · dsimp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        exact update_shifted_append _ _ _
    · intro i
      fin_cases i <;> simp; omega
  | cons b w ih =>
    subst hu
    rw [frame_cons, show 2 * (b :: w).length + 1 = 2 * w.length + 1 + 1 + 1 by simp; omega,
      runFrom_succ_eq_step, runFrom_succ_eq_step, List.cons_append, List.cons_append,
      step_tapesCfg (a := ⟨0, ![(some none, 1), (some (some true), 1)], none, some .bit⟩)
        (ws' := ![b :: (frame w ++ rest), acc ++ [true]]) (o' := ![oS + 1, oR])
        (h' := ![oS + 1, oR + (acc ++ [true]).length])
        (by simp only [popFrame, tr_ofTr, Matrix.cons_val_zero, tapeOfList_cons_sub_self]) rfl rfl
        (fun i => by
          fin_cases i
          · dsimp only [Fin.zero_eta, Matrix.cons_val_zero]
            exact update_shifted_cons_none _ _ _
          · dsimp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
            exact update_shifted_append _ _ _)
        (fun i => by fin_cases i <;> simp; omega),
      step_tapesCfg (a := ⟨0, ![(some none, 1), (some (some b), 1)], none, some .loop⟩)
        (ws' := ![frame w ++ rest, acc ++ [true] ++ [b]]) (o' := ![oS + 1 + 1, oR])
        (h' := ![oS + 1 + 1, oR + (acc ++ [true] ++ [b]).length])
        (by simp only [popFrame, tr_ofTr, Matrix.cons_val_zero, tapeOfList_cons_sub_self]) rfl rfl
        (fun i => by
          fin_cases i
          · dsimp only [Fin.zero_eta, Matrix.cons_val_zero]
            exact update_shifted_cons_none _ _ _
          · dsimp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
            exact update_shifted_append _ _ _)
        (fun i => by fin_cases i <;> simp; omega)]
    exact ih _ _ (oS + 1 + 1) rfl (by simp [hacc, frame_cons]) (by simp [hS]; omega)

/-- On a blank tape `0`, `popFrame` writes `[false]`. -/
theorem runsBetween_popFrame_nil (oS oR : ℤ) {input : List Bool} (out : List Bool) :
    RunsBetween popFrame (tapesCfg input ![[], []] ![oS, oR] ![oS, oR] out)
      (tapesCfg input ![[], [false]] ![oS, oR] ![oS, oR + 1] out) 1 (2 * (1 + 1)) := by
  refine RunsBetween.of_runFrom ?_
  rw [runFrom_one]
  refine step_tapesCfg (a := ⟨0, ![(none, 0), (some (some false), 1)], none, none⟩) ?_ rfl rfl ?_
    ?_
  · have : tapeOfList ([] : List Bool) (oS - oS) = none := by rw [tapeOfList_nil]
    simp only [popFrame, tr_ofTr, q₀_ofTr, Matrix.cons_val_zero, this]
  · intro i
    fin_cases i
    · rfl
    · simpa using update_shifted_append ([] : List Bool) false oR
  · intro i
    fin_cases i <;> simp

/-- On a framed word `frame w` at the head of tape `0`, `popFrame` moves it to tape `1` as
`frame (true :: w)`. -/
theorem runsBetween_popFrame_frame (w rest : List Bool) (oS oR : ℤ) {input : List Bool}
    (out : List Bool) :
    RunsBetween popFrame (tapesCfg input ![frame w ++ rest, []] ![oS, oR] ![oS, oR] out)
      (tapesCfg input ![rest, frame (true :: w)] ![oS + (frame w).length, oR]
        ![oS + (frame w).length, oR + (frame (true :: w)).length] out)
      (2 * w.length + 3) (2 * (2 * w.length + 3 + 1)) := by
  refine RunsBetween.of_runFrom ?_
  obtain ⟨x, l, hxl⟩ : ∃ x l, frame w ++ rest = x :: l := by
    cases w <;> exact ⟨_, _, rfl⟩
  rw [show 2 * w.length + 3 = 2 * w.length + 1 + 1 + 1 by omega, runFrom_succ_eq_step,
    runFrom_succ_eq_step,
    step_tapesCfg (a := ⟨0, ![(none, 0), (some (some true), 1)], none, some .pre⟩)
      (ws' := ![frame w ++ rest, [true]]) (o' := ![oS, oR]) (h' := ![oS, oR + 1])
      (by simp only [popFrame, tr_ofTr, q₀_ofTr, Matrix.cons_val_zero, hxl,
        tapeOfList_cons_sub_self])
      rfl rfl
      (fun i => by
        fin_cases i
        · rfl
        · simpa using update_shifted_append ([] : List Bool) true oR)
      (fun i => by fin_cases i <;> simp),
    step_tapesCfg (a := ⟨0, ![(none, 0), (some (some true), 1)], none, some .loop⟩)
      (ws' := ![frame w ++ rest, [true, true]]) (o' := ![oS, oR])
      (h' := ![oS, oR + ([true, true] : List Bool).length])
      (by simp only [popFrame, tr_ofTr]) rfl rfl
      (fun i => by
        fin_cases i
        · rfl
        · simpa using update_shifted_append ([true] : List Bool) true oR)
      (fun i => by fin_cases i <;> simp; omega)]
  exact runFrom_popFrame_loop w rest _ [true, true] _ oS _ oR _ rfl (by simp [frame_cons])
    (by simp [length_frame]) (by simp [length_frame]) out

end MultiTapeTM

end Turing
