/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Algorithms.WordRAM.Stack.Controller

/-!
# Controller certificates on concrete stack code

The adaptive size/push client passes an observed size into a subsequent operation using one
fixed continuation fragment. Additional tests exercise charged branching and initialization,
both exact execution paths, the smallest admissible word width, and rejection of a false budget.
-/

@[expose] public section

namespace ComplexityTests.WordRAMController

open Cslib Cslib.WordRAM Cslib.WordRAM.Stack

private def sizePrep : Code .standard 9 := ram[tag ← #2; arg ← #0]
private def pushPrep : Code .standard 9 := ram[arg ← out; tag ← #0]

private def entry (w : ℕ) (s : List ℕ) (x : Data 9) : Prop :=
  Rep w 2 2 s x ∧ s.length < 2

private def mid (w a : ℕ) (s : List ℕ) (x : Data 9) : Prop :=
  entry w s x ∧ x.regs out = a ∧ a = s.length

private theorem size_refines {w : ℕ} (h4 : Fits w 4) :
    Refines w (entry w) (D := spec w 2) (.liftBind .size fun a => .pure a)
      (mid w) (fun _ _ => 9) (.seq sizePrep program) := by
  have h2 : Fits w 2 := h4.of_le (by decide)
  have hcall := Refines.call (certificate h2 h4) .size
    (pre := entry w) (prep := sizePrep) (setup := fun _ _ => 2) (body := fun _ _ => 7)
    (fun _ _ h => ⟨h.1, trivial⟩)
    (by
      intro s x _
      have he : (implementation w 2).prepare .size x = (x.set tag 2).set arg 0 := by
        ext i
        · fin_cases i <;> simp +decide [implementation, DynamicProgram.prepare, Data.set, tag, arg]
        · rfl
      rw [he]
      exact (Exec.seq (Exec.const h2) (Exec.const (fits_zero w))).within)
    (by
      intro s x hx y n he
      obtain ⟨z, hz, _, _, _⟩ := Stack.execute h2 h4 hx.1 .size trivial
      obtain ⟨_, rfl⟩ := he.unique hz
      exact le_rfl)
  have hs : (spec w 2).Hoare (fun s => s.length < 2)
      (.liftBind .size fun a => .pure a) (fun a s => a = s.length ∧ s.length < 2) :=
    Stateful.Spec.Hoare.call _ _ _ (fun _ h => ⟨trivial, rfl, h⟩)
  exact (hcall.hoare hs (fun _ _ h => h.2)).consequence
    (fun _ _ h => h)
    (fun a s x h => ⟨⟨h.1.1, h.2.2⟩, Option.some.inj h.1.2, h.2.1⟩)
    (fun _ _ _ => le_rfl)

private theorem push_refines {w a : ℕ} (h4 : Fits w 4) :
    Refines w (mid w a) (D := spec w 2) (.liftBind (.push a) fun b => .pure b)
      (fun _ s y => Rep w 2 2 s y) (fun _ _ => 9) (.seq pushPrep program) := by
  have h2 : Fits w 2 := h4.of_le (by decide)
  have hv : ∀ s x, mid w a s x → (spec w 2).valid s (.push a) := by
    intro s x hx
    exact ⟨hx.1.2, hx.2.1 ▸ hx.1.1.bounded.1 out⟩
  have hcall := Refines.call (certificate h2 h4) (.push a)
    (pre := mid w a) (prep := pushPrep) (setup := fun _ _ => 2) (body := fun _ _ => 7)
    (fun s x h => ⟨h.1.1, hv s x h⟩)
    (by
      intro s x hx
      have he : (implementation w 2).prepare (.push a) x =
          (x.set arg (x.regs out)).set tag 0 := by
        ext i
        · fin_cases i <;> simp_all +decide [implementation, DynamicProgram.prepare,
            Data.set, tag, arg, mid]
        · rfl
      rw [he]
      exact (Exec.seq Exec.copy (Exec.const (fits_zero w))).within)
    (by
      intro s x hx y n he
      obtain ⟨z, hz, _, _, _⟩ := Stack.execute h2 h4 hx.1.1 (.push a) (hv s x hx)
      obtain ⟨_, rfl⟩ := he.unique hz
      exact le_rfl)
  exact hcall.consequence (fun _ _ h => h) (fun _ _ _ h => h.1)
    (fun _ _ _ => le_rfl)

/-- The second operation's argument is the first observation, with fixed code for every answer. -/
private theorem adaptive_refines {w : ℕ} (h4 : Fits w 4) :
    Refines w (entry w) (D := spec w 2)
      (((.liftBind .size fun a => .pure a) : (spec w 2).Client ℕ).bind fun a =>
        .liftBind (.push a) fun b => .pure b)
      (fun _ s y => Rep w 2 2 s y) (fun _ _ => 18)
      (.seq (.seq sizePrep program) (.seq pushPrep program)) :=
  Refines.bind (size_refines h4) (fun _ => push_refines h4) (fun _ _ _ _ _ _ _ => le_rfl)

/-- Initialization is an actual register write, followed by the composed adaptive certificate. -/
private theorem initialized_adaptive :
    ∃ y, ExecWithin 3 (.seq (.op (.const ptr 2))
        (.seq (.seq sizePrep program) (.seq pushPrep program))) (Data.init []) y 19 ∧
      Rep 3 2 2 [0] y := by
  have h4 : Fits 3 4 := by decide
  have hinit : ∀ s x, s = ([] : List ℕ) ∧ x = (Data.init [] : Data 9) →
      ∃ y, ExecWithin (B := .standard) 3 (.op (.const ptr 2)) x y 1 ∧ entry 3 s y := by
    rintro s x ⟨rfl, rfl⟩
    refine ⟨initial 2, ?_, initial_rep h4, by decide⟩
    have hi : (Data.init ([] : List ℕ) : Data 9).set ptr 2 = initial 2 := by
      ext i <;> simp [Data.init, Data.set, initial, Function.update_apply]
    simpa only [hi] using (Exec.const (B := Basis.standard) (x := Data.init [])
      (d := ptr) (show Fits 3 2 by decide)).within
  have h := Refines.prepend (budget' := fun _ _ => 19) hinit (adaptive_refines h4)
    (fun _ _ _ _ _ => le_rfl)
  obtain ⟨_, y, he, hr⟩ := h [] (Data.init []) ⟨rfl, rfl⟩
  exact ⟨y, he, hr⟩

/-- A different observation drives the same continuation code to push one rather than zero. -/
private theorem populated_adaptive :
    ∃ x y, Rep 3 2 2 [5] x ∧
      ExecWithin 3 (.seq (.seq sizePrep program) (.seq pushPrep program)) x y 18 ∧
      Rep 3 2 2 [1, 5] y := by
  let x := ((initial 2).set len 1).write 2 5
  have h4 : Fits 3 4 := by decide
  have hr : Rep 3 2 2 [5] x := by
    refine ⟨((initial_rep (capacity := 2) h4).bounded.set (show Fits 3 1 by decide)).write
      (show Fits 3 5 by decide), ?_, ?_, by decide, ?_⟩
    · simp +decide [x, Data.set, Data.write, initial, len, ptr]
    · simp [x, Data.set, Data.write]
    · intro i
      fin_cases i
      simp [x, Data.set, Data.write]
  obtain ⟨_, y, he, hy⟩ := adaptive_refines h4 [5] x ⟨hr, by decide⟩
  exact ⟨x, y, hr, he, hy⟩

private theorem branch_refines {w n : ℕ} (h2 : Fits w 2) :
    Refines (D := spec w 2) (B := .standard) w
      (fun s x => s = [] ∧ x.regs out = n ∧ x.regs len = 0)
      (if n = 0 then .pure 1 else .pure 2)
      (fun (a : ℕ) _ y => y.regs out = a) (fun _ _ => 3)
      (.branch (.eq out len) (.op (.const out 1)) (.op (.const out 2))) := by
  apply Refines.branch (n = 0)
  · intro s x hx
    change x.regs out = x.regs len ↔ n = 0
    rw [hx.2.1, hx.2.2]
  · apply Refines.pure
    intro s x _
    exact ⟨x.set out 1, (Exec.const (h2.of_le (by decide))).within, by simp [Data.set]⟩
  · apply Refines.pure
    intro s x _
    exact ⟨x.set out 2, (Exec.const h2).within, by simp [Data.set]⟩

example :
    (∃ y, ExecWithin (B := .standard) 2
      (.branch (.eq out len) (.op (.const out 1)) (.op (.const out 2)))
      (Data.init []) y 3 ∧ y.regs out = 1) ∧
    (∃ y, ExecWithin (B := .standard) 2
      (.branch (.eq out len) (.op (.const out 1)) (.op (.const out 2)))
      ((Data.init []).set out 1) y 3 ∧ y.regs out = 2) ∧
    Executes 2 (Stack.Controller.code.program out) (State.init [0]) 1 49 ∧
    Executes 2 (Stack.Controller.code.program out) (State.init [3]) 3 29 := by
  obtain ⟨_, y₀, he₀, hr₀⟩ := branch_refines (n := 0) (show Fits 2 2 by decide)
    [] (Data.init []) ⟨rfl, rfl, rfl⟩
  obtain ⟨_, y₁, he₁, hr₁⟩ := branch_refines (n := 1) (show Fits 2 2 by decide)
    [] ((Data.init []).set out 1) ⟨rfl, by simp [Data.set], by decide⟩
  exact ⟨⟨y₀, he₀, hr₀⟩, ⟨y₁, he₁, hr₁⟩,
    Stack.Controller.executes (by decide) (by decide),
    Stack.Controller.executes (by decide) (by decide)⟩

/-- The actual zero-input execution refutes a forty-eight-step whole-program budget. -/
theorem rejects_short_budget :
    ¬∃ t ≤ 48, Executes 2 (Stack.Controller.code.program out) (State.init [0]) 1 t := by
  rintro ⟨t, ht, he⟩
  have hx := Stack.Controller.executes (w := 2) (n := 0) (by decide) (by decide)
  have hn : t = 49 := (he.unique hx).2
  omega

-- A second matching certificate must not hide the usable one or force its false premise.
@[program_certificate]
private theorem unusable_controller {w n : ℕ} (impossible : False) :
    Refines w (fun s x => s = [] ∧ x = Data.init [n]) (Stack.Controller.client w n)
      (fun a s y => Rep w 2 1 s y ∧ y.regs out = a)
      (fun _ _ => if n = 0 then 48 else 28) Stack.Controller.code := impossible.elim

example {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    Refines w (fun s x => s = [] ∧ x = Data.init [n]) (Stack.Controller.client w n)
      (fun a s y => Rep w 2 1 s y ∧ y.regs out = a)
      (fun _ _ => if n = 0 then 48 else 28) Stack.Controller.code := by
  stateful

@[program_certificate]
private theorem nonuniform_positive_polytime :
    ComputableInPolyTime .standard Stack.Controller.positive (fun _ n => [n]) id :=
  Stack.Controller.positive_polytime.computableInPolyTime

attribute [local fun_prop] nonuniform_positive_polytime

example :
    UniformComputableInPolyTime .standard Stack.Controller.positive (fun _ n => [n]) id ∧
    UniformComputableInPolyTime .standard Stack.Controller.positive (fun _ n => [n]) id ∧
    ComputableInPolyTime .standard Stack.Controller.positive (fun _ n => [n]) id ∧
    ComputableInPolyTime .standard Stack.Controller.positive (fun _ n => [n]) id :=
  ⟨by polytime, by fun_prop, by polytime, by fun_prop⟩

/-- The family puts its width in the instruction's literal, rather than reading it at runtime. -/
private def widthCountdown (w : ℕ) : Code .standard 3 :=
  .seq (.op (.const 0 w)) (.seq (.op (.const 1 1))
    (.seq (.loop (.lt 2 0) (.op (.bin .sub 0 0 1)))
      (.seq (.op (.load 0 1)) (.loop (.lt 2 0) (.op (.bin .sub 0 0 1))))))

/-- One subtraction per iteration, including the loop's branches and final exit. -/
private theorem countdown_exec {w : ℕ} {x : Data 3}
    (h1 : x.regs 1 = 1) (h2 : x.regs 2 = 0) (hf : Fits w (x.regs 0)) :
    ∃ y, ExecWithin (B := .standard) w (.loop (.lt 2 0) (.op (.bin .sub 0 0 1)))
      x y (x.regs 0 * 3 + 2) ∧
      y.regs 0 = 0 ∧ y.regs 1 = 1 ∧ y.regs 2 = 0 ∧ y.mem = x.mem := by
  let I : Data 3 → Prop := fun y =>
    y.regs 1 = 1 ∧ y.regs 2 = 0 ∧ Fits w (y.regs 0) ∧ y.mem = x.mem
  obtain ⟨y, he, hI, hc⟩ := ExecWithin.loop_invariant (B := Basis.standard)
    (cond := .lt 2 0) (body := .op (.bin .sub 0 0 1)) I (fun y => y.regs 0)
    (T := 1) (by
      intro y hy hc
      have hb : Fits w (BinOp.sub.eval (y.regs 0) (y.regs 1)) := by
        exact hy.2.2.1.of_le (Nat.sub_le _ _)
      refine ⟨y.set 0 (BinOp.sub.eval (y.regs 0) (y.regs 1)),
        ExecWithin.bin hb, ?_, ?_⟩
      · simpa +decide [I, Data.set] using And.intro hy.1
          (And.intro hy.2.1 (And.intro hb hy.2.2.2))
      · change y.regs 2 < y.regs 0 at hc
        simp only [Data.set, Function.update_self, BinOp.eval, hy.1]
        have := hy.2.1
        omega)
    (show I x from ⟨h1, h2, hf, rfl⟩)
  refine ⟨y, he, ?_, hI.1, hI.2.1, hI.2.2.2⟩
  change ¬y.regs 2 < y.regs 0 at hc
  have := hI.2.1
  omega

/-- The encoded second word varies with width; both countdowns are charged in the budget. -/
private theorem widthCountdown_computes :
    ComputableInTime .standard (fun _ => 0) (fun w n => [n, w])
      (fun n w => 3 * w + 3 * n + 8) (fun _ w => 1 ≤ w) := by
  apply ComputableInTime.of_code widthCountdown 0
      (time := fun n w => 3 * w + 3 * n + 7)
  · exact ⟨12, fun _ => by simp [widthCountdown]⟩
  · intro n w hw hi
    have h1 : Fits w 1 := fits_one (by omega)
    let x : Data 3 := ((Data.init [n, w]).set 0 w).set 1 1
    have hx0 : x.regs 0 = w := by simp +decide [x, Data.set]
    obtain ⟨y, hy, hy0, hy1, hy2, hym⟩ := countdown_exec (x := x)
      (by simp [x, Data.set]) (by simp +decide [x, Data.set, Data.init])
      (by simpa +decide [x, Data.set] using fits_self w)
    have hn : Fits w n := hi.2 n (by simp)
    let z := y.set 0 (y.mem (y.regs 1))
    have hz0 : z.regs 0 = n := by simp [z, Data.set, hy1, hym, x, Data.init]
    obtain ⟨v, hv, hv0, _, _, _⟩ := countdown_exec (x := z)
      (by simpa +decide [z, Data.set] using hy1)
      (by simpa +decide [z, Data.set] using hy2) (hz0 ▸ hn)
    refine ⟨v, ?_, hv0⟩
    have he := ExecWithin.seq
      (ExecWithin.const (x := Data.init [n, w]) (d := 0) (fits_self w))
      (ExecWithin.seq (ExecWithin.const h1)
        (ExecWithin.seq hy (ExecWithin.seq (ExecWithin.load (d := 0) (a := 1)) hv)))
    exact he.mono (by rw [hx0, hz0]; omega)

-- A concrete fitting instance demonstrates that the family contract is not vacuous.
example : InputFits 3 [5, 3] ∧
    (∃ r, ∃ P : WordSizeDependentProgram .standard r, P.BoundedCode ∧
      ∃ t, Executes 3 (P 3) (State.init [5, 3]) 0 t ∧ t ≤ 32) := by
  obtain ⟨r, P, hP, hp⟩ := widthCountdown_computes
  exact ⟨by decide, r, P, hP, hp 5 3 (show 1 ≤ 3 by decide) (by decide)⟩

example (_f : ℕ → ℕ) : True := by
  fail_if_success
    have : UniformComputableInPolyTime .standard _f (fun _ n => [n]) id := by polytime
  trivial

-- A RAM hypothesis is not a Turing-machine certificate.
example (_f : ℕ → ℕ)
    (_h : UniformComputableInPolyTime .standard _f (fun _ n => [n]) id) : True := by
  fail_if_success
    have : Turing.MultiTapeTM.ComputableTidilyInPolyTime _f
        Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat := by polytime
  trivial

/-- info: 'Cslib.WordRAM.Refines.bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Refines.bind
/-- info: 'Cslib.WordRAM.Refines.call' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Refines.call

end ComplexityTests.WordRAMController
