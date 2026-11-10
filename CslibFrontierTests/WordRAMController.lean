/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontierTests.WordRAMDynamic
public import CslibFrontier.DataStructure.Stack.Controller
public import CslibFrontier.Computability.WordRAM.Controller
public import CslibFrontier.Tactic.PolyTime

/-!
# Controller certificates on concrete code

An adaptive client of the exchange cell passes the first answer into a second exchange with one
fixed continuation fragment. Additional tests exercise charged branching and initialization,
both exact execution paths, the smallest admissible word width, rejection of a false budget, and
`fun_prop` reuse of the compiled stack controller's polynomial-time certificate.
-/

@[expose] public section

namespace CslibFrontierTests.WordRAMController

open Cslib Cslib.WordRAM WordRAMDynamicTests

private def firstPrep (v : ℕ) : Code .standard 3 := .op (.const 1 v)
private def secondPrep : Code .standard 3 := .op (.copy 1 2)

private def entry (w : ℕ) (s : ℕ) (x : Data 3) : Prop := (exchangeCertificate w).rep s x

private def mid (w a : ℕ) (s : ℕ) (x : Data 3) : Prop := entry w s x ∧ x.regs 2 = a

private theorem exchange_exec (w : ℕ) (x : Data 3) : ∃ y, Exec w (exchangeProgram w).code x y 3 :=
  ⟨_, (Exec.const (fits_zero w)).seq (Exec.load.seq Exec.store)⟩

private theorem first_refines {w v : ℕ} (hv : Fits w v) :
    Refines w (entry w) (D := exchangeSpec w) (.liftBind v fun a => .pure a)
      (mid w) (fun _ _ => 4) (.seq (firstPrep v) (exchangeProgram w).code) := by
  have hcall := Refines.call (exchangeCertificate w) v
    (pre := entry w) (prep := firstPrep v) (setup := fun _ _ => 1) (body := fun _ _ => 3)
    (fun _ _ h => ⟨h, hv⟩)
    (by
      intro s x _
      have he : (exchangeProgram w).prepare v x = x.set 1 v := by
        ext i
        · fin_cases i <;> simp [exchangeProgram, DynamicProgram.prepare, Data.set]
        · rfl
      rw [he]
      exact (Exec.const hv).within)
    (by
      intro s x _ y n he
      obtain ⟨z, hz⟩ := exchange_exec w ((exchangeProgram w).prepare v x)
      obtain ⟨_, rfl⟩ := he.unique hz
      exact le_rfl)
  exact hcall.consequence (fun _ _ h => h)
    (fun a s x h => ⟨h.1, Option.some.inj (h.2 : some (x.regs 2) = some a)⟩)
    (fun _ _ _ => le_rfl)

private theorem second_refines {w a : ℕ} :
    Refines w (mid w a) (D := exchangeSpec w) (.liftBind a fun b => .pure b)
      (mid w) (fun _ _ => 4) (.seq secondPrep (exchangeProgram w).code) := by
  have hv : ∀ s x, mid w a s x → (exchangeSpec w).valid s a := fun s x hx =>
    hx.2 ▸ hx.1.1.1 2
  have hcall := Refines.call (exchangeCertificate w) a
    (pre := mid w a) (prep := secondPrep) (setup := fun _ _ => 1) (body := fun _ _ => 3)
    (fun s x h => ⟨h.1, hv s x h⟩)
    (by
      intro s x hx
      have he : (exchangeProgram w).prepare a x = x.set 1 (x.regs 2) := by
        ext i
        · fin_cases i <;> simp_all [exchangeProgram, DynamicProgram.prepare, Data.set, mid]
        · rfl
      rw [he]
      exact Exec.copy.within)
    (by
      intro s x _ y n he
      obtain ⟨z, hz⟩ := exchange_exec w ((exchangeProgram w).prepare a x)
      obtain ⟨_, rfl⟩ := he.unique hz
      exact le_rfl)
  exact hcall.consequence (fun _ _ h => h)
    (fun b s x h => ⟨h.1, Option.some.inj (h.2 : some (x.regs 2) = some b)⟩)
    (fun _ _ _ => le_rfl)

/-- Exchange `v` in, then put the old contents back: the second argument is the first answer, with
fixed code for every answer. -/
private def swapBack (w v : ℕ) : (exchangeSpec w).Client ℕ := do
  let a ← (exchangeSpec w).call v
  (exchangeSpec w).call a

private def swapCode (v : ℕ) : Code .standard 3 :=
  .seq (.seq (firstPrep v) (exchangeProgram 0).code) (.seq secondPrep (exchangeProgram 0).code)

/-- The second operation's argument is the first observation. -/
private theorem adaptive_refines {w v : ℕ} (hv : Fits w v) :
    Refines w (entry w) (swapBack w v) (mid w) (fun _ _ => 8) (swapCode v) :=
  Refines.bind_ofFn (first_refines hv) (fun _ => second_refines) (fun _ _ _ _ _ _ _ => le_rfl)

/-- Initialization is an actual register write, followed by the composed adaptive certificate. -/
private theorem initialized_refines {w v : ℕ} (hv : Fits w v) :
    Refines w (D := exchangeSpec w) (fun s x => s = 0 ∧ x = Data.init []) (swapBack w v) (mid w)
      (fun _ _ => 9)
      (.seq (.op (.const 2 0)) (swapCode v)) := by
  refine Refines.prepend (setup := fun _ _ => 1) ?_ (adaptive_refines hv)
    (fun _ _ _ _ _ => le_rfl)
  rintro s x ⟨rfl, rfl⟩
  refine ⟨(Data.init [] : Data 3).set 2 0, (Exec.const (fits_zero w)).within, ?_⟩
  exact ⟨((Data.Bounded.init (by simp [InputFits, fits_zero])).set (fits_zero w)), rfl⟩

/-- The same continuation code restores a different observed cell. -/
example : ∃ y, ExecWithin 3 (swapCode 6) ⟨fun _ => 0, fun _ => 5⟩ y 8 ∧
    y.mem 0 = 5 ∧ y.regs 2 = 6 := by
  have hr : entry 3 5 ⟨fun _ => 0, fun _ => 5⟩ :=
    ⟨⟨fun _ => fits_zero 3, fun _ => show Fits 3 5 by decide⟩, rfl⟩
  obtain ⟨_, y, he, ⟨hent, hy⟩⟩ :=
    (adaptive_refines (w := 3) (show Fits 3 6 by decide)).toOfFn hr
  exact ⟨y, he, hent.2, hy⟩

private theorem branch_refines {w n : ℕ} (h2 : Fits w 2) :
    Refines (D := exchangeSpec w) (B := .standard) w
      (fun s (x : Data 3) => s = 0 ∧ x.regs 2 = n ∧ x.regs 0 = 0)
      (if n = 0 then .pure 1 else .pure 2)
      (fun (a : ℕ) _ y => y.regs 2 = a) (fun _ _ => 3)
      (.branch (.eq 2 0) (.op (.const 2 1)) (.op (.const 2 2))) := by
  apply Refines.branch (n = 0)
  · intro s x hx
    change x.regs 2 = x.regs 0 ↔ n = 0
    rw [hx.2.1, hx.2.2]
  · apply Refines.pure
    intro s x _
    exact ⟨x.set 2 1, (Exec.const (h2.of_le (by decide))).within, by simp [Data.set]⟩
  · apply Refines.pure
    intro s x _
    exact ⟨x.set 2 2, (Exec.const h2).within, by simp [Data.set]⟩

private theorem swap_executes :
    Executes 2 ((exchangeProgram 2).code.program (2 : Fin 3)) (State.init [0]) 1 4 := by
  obtain ⟨y, he⟩ := exchange_exec 2 (Data.init [0])
  have hy : y.regs 2 = 1 := by
    obtain ⟨rfl, -⟩ := he.unique ((Exec.const (fits_zero 2)).seq (Exec.load.seq Exec.store))
    simp [Data.set, Data.write, Data.init]
  simpa only [hy, State.init] using he.executes 2

example :
    (∃ y, ExecWithin (B := .standard) 2
      (.branch (.eq 2 0) (.op (.const 2 1)) (.op (.const 2 2)))
      (Data.init [] : Data 3) y 3 ∧ y.regs 2 = 1) ∧
    (∃ y, ExecWithin (B := .standard) 2
      (.branch (.eq 2 0) (.op (.const 2 1)) (.op (.const 2 2)))
      ((Data.init [] : Data 3).set 2 1) y 3 ∧ y.regs 2 = 2) ∧
    Executes 2 ((exchangeProgram 2).code.program (2 : Fin 3)) (State.init [0]) 1 4 := by
  obtain ⟨_, y₀, he₀, hr₀⟩ := (branch_refines (n := 0) (show Fits 2 2 by decide)).toOfFn
    (x := Data.init []) ⟨rfl, rfl, rfl⟩
  obtain ⟨_, y₁, he₁, hr₁⟩ := (branch_refines (n := 1) (show Fits 2 2 by decide)).toOfFn
    (x := (Data.init []).set 2 1) ⟨rfl, by simp [Data.set], by decide⟩
  exact ⟨⟨y₀, he₀, hr₀⟩, ⟨y₁, he₁, hr₁⟩, swap_executes⟩

/-- The actual execution refutes a three-step whole-program budget. -/
theorem rejects_short_budget :
    ¬∃ t ≤ 3, Executes 2 ((exchangeProgram 2).code.program (2 : Fin 3)) (State.init [0]) 1 t := by
  rintro ⟨t, ht, he⟩
  have hn : t = 4 := (he.unique swap_executes).2
  omega

private theorem nonuniform_positive_polytime :
    ComputableInPolyTime .standard DataStructure.Stack.Controller.positive (fun _ n => [n]) id :=
  DataStructure.Stack.Controller.positive_polytime.computableInPolyTime

attribute [local fun_prop] nonuniform_positive_polytime

example :
    UniformComputableInPolyTime .standard DataStructure.Stack.Controller.positive
      (fun _ n => [n]) id ∧
    ComputableInPolyTime .standard DataStructure.Stack.Controller.positive (fun _ n => [n]) id :=
  ⟨by fun_prop, by fun_prop⟩

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

/-! ## Relational demonic caller admissibility regression -/

/-- Operations for the relational controller regression test. -/
inductive ChoiceOp : Type
  | choose
  | bad

/-- Return types for `ChoiceOp`. -/
abbrev ChoiceResult : ChoiceOp → Type
  | .choose => Bool
  | .bad => Unit

/-- Relational specification where `choose` may return either Boolean, while `bad` is never
admissible (`valid := False`). -/
abbrev choiceSpec : DataStructure.StateTransitionSpec where
  State := Unit
  Op := ChoiceOp
  Result := ChoiceResult
  step _ o _ a :=
    match o, a with
    | .choose, _ => True
    | .bad, () => True
  valid _ o :=
    match o with
    | .choose => True
    | .bad => False

/-- Concrete implementation that angelically realizes `choose` by writing `1` (`true`) to register
`0`. -/
def choiceProg : DynamicProgram choiceSpec 1 where
  code := .op (.const 0 1)
  output := 0
  input _ := true
  encode _ _ := 0
  decode o regs :=
    match o with
    | .choose => some (regs 0 != 0)
    | .bad => some ()

/-- Dynamic certificate for `choiceProg`. -/
def choiceCert : DynamicCertificate choiceProg 3 where
  rep _ x := x.Bounded 3
  bounded hr := hr
  arguments_fit _ _ _ _ := fits_zero 3
  execute {_ x} o hr hv := by
    cases o with
    | choose =>
      have hex : Exec 3 choiceProg.code (choiceProg.prepare .choose x)
          ((choiceProg.prepare .choose x).set 0 1) 1 :=
        Exec.const (B := Basis.standard) (x := choiceProg.prepare .choose x) (d := 0)
          (show Fits 3 1 by decide)
      refine ⟨(choiceProg.prepare .choose x).set 0 1, (), true, 1, hex, trivial,
        by simp [choiceProg, Data.set], ?_⟩
      exact (choiceProg.prepare_bounded hr (fun _ _ => fits_zero 3)).set (show Fits 3 1 by decide)
    | bad => exact False.elim hv

private theorem choose_refines :
    Refines 3 (D := choiceSpec) (fun _ (x : Data 1) => x.Bounded 3)
      (.liftBind .choose fun b => .pure b)
      (fun _ _ y => y.Bounded 3)
      (fun _ _ => 2)
      (.seq (.op (.const 0 0)) choiceProg.code) := by
  have hcall := Refines.call choiceCert .choose
    (pre := fun _ (x : Data 1) => x.Bounded 3)
    (prep := .op (.const 0 0)) (setup := fun _ _ => 1) (body := fun _ _ => 1)
    (fun _ _ hx => ⟨hx, trivial⟩)
    (fun _ x _ => by
      have hprep : choiceProg.prepare .choose x = x.set 0 0 := by
        ext i
        · fin_cases i; rfl
        · rfl
      rw [hprep]
      exact (Exec.const (B := Basis.standard) (x := x) (d := 0) (fits_zero 3)).within)
    (by
      intro _ x _ y n he
      have hex : Exec 3 choiceProg.code (choiceProg.prepare .choose x)
          ((choiceProg.prepare .choose x).set 0 1) 1 :=
        Exec.const (B := Basis.standard) (x := choiceProg.prepare .choose x) (d := 0)
          (show Fits 3 1 by decide)
      obtain ⟨_, rfl⟩ := he.unique hex
      exact le_rfl)
  exact hcall.consequence (fun _ _ h => h)
    (fun _ _ _ h => h.1)
    (fun _ _ _ => le_rfl)

/-- A caller whose continuation is admissible after *both* permitted answers (`true` and `false`) of
`choose`. -/
def validAfterBothClient : choiceSpec.Client Unit := do
  let b ← choiceSpec.call .choose
  if b then .pure () else .pure ()

/-- `Refines.bind` certifies `validAfterBothClient` on the relational specification `choiceSpec`. -/
example :
    Refines 3 (D := choiceSpec) (fun _ (x : Data 1) => x.Bounded 3)
      validAfterBothClient
      (fun _ _ y => y.Bounded 3)
      (fun _ _ => 3)
      (.seq (.seq (.op (.const 0 0)) choiceProg.code) (.op (.const 0 0))) := by
  refine Refines.bind (next := fun _ _ _ => 1) choose_refines
    (fun b => ?_)
    (fun _ _ _ _ _ _ _ => le_rfl)
    (fun _ _ _ b s' _ _ => by cases b <;> exact .pure s' ())
  cases b <;>
    exact Refines.pure () fun _ x hx =>
      ⟨x.set 0 0, (Exec.const (B := Basis.standard) (x := x) (d := 0) (fits_zero 3)).within,
        hx.set (fits_zero 3)⟩

/-- A caller that issues `bad` (`valid := False`) when `choose` returns `false`, while succeeding
when `choose` returns `true`. -/
def badAfterFalseClient : choiceSpec.Client Unit := do
  let b ← choiceSpec.call .choose
  if b then .pure () else choiceSpec.call .bad

/-- Choosing `true` produces a valid `ClientRun` of `badAfterFalseClient`. -/
example : choiceSpec.ClientRun () badAfterFalseClient () () [⟨ChoiceOp.choose, true, ()⟩] :=
  DataStructure.StateTransitionSpec.ClientRun.liftBind (D := choiceSpec) (s₁ := ()) ChoiceOp.choose
    (fun b => if b then .pure () else .liftBind .bad fun u => .pure u)
    true trivial trivial (DataStructure.StateTransitionSpec.ClientRun.pure (D := choiceSpec) () ())

/-- `Refines` rejects `badAfterFalseClient` for any machine program and budget, because the
permitted `false` outcome of `choose` reaches `bad` and violates demonic caller admissibility. -/
example (budget : Unit → Data 1 → ℕ) (code : Code .standard 1) :
    ¬ Refines 3 (D := choiceSpec) (fun _ x => x = Data.init [])
        badAfterFalseClient (fun _ _ _ => True) budget code := by
  intro href
  obtain ⟨hdemonic, _⟩ := href () (Data.init []) rfl
  obtain ⟨_, hk⟩ :=
    (choiceSpec.demonicValid_liftBind_iff () ChoiceOp.choose
      (fun b : Bool => if b then .pure () else .liftBind ChoiceOp.bad fun u => .pure u)).mp hdemonic
  have hfalse := hk () false trivial
  obtain ⟨hbad, _⟩ :=
    (choiceSpec.demonicValid_liftBind_iff () ChoiceOp.bad (fun u => .pure u)).mp hfalse
  exact hbad

/-- info: 'Cslib.WordRAM.Refines.bind' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Refines.bind
/-- info: 'Cslib.WordRAM.Refines.bind_ofFn' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Refines.bind_ofFn
/-- info: 'Cslib.WordRAM.Refines.call' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Refines.call

end CslibFrontierTests.WordRAMController
