/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Dynamic
public import Complexity.Algorithms.WordRAM.Stack

/-! Nonvacuous fixed-program clients: a persistent exchange cell and a read-only array.
Both obtain arbitrary-history theorems from the same certificate interface. -/

@[expose] public section

open Cslib Cslib.WordRAM

namespace WordRAMDynamicTests

/-- Exchange returns the previous contents of the single maintained cell. -/
abbrev exchangeSpec (w : ℕ) : Stateful.Spec where
  State := ℕ
  Op := ℕ
  Result _ := ℕ
  step s o := (o, s)
  valid _ o := Fits w o

/-- One fixed program loads the old cell before overwriting it with the argument. -/
def exchangeProgram (w : ℕ) : DynamicProgram (exchangeSpec w) 3 where
  code := .seq (.op (.const 0 0)) (.seq (.op (.load 2 0)) (.op (.store 0 1)))
  output := 2
  input i := i == 1
  encode o _ := o
  decode _ regs := some (regs 2)

/-- The exchange cell has a genuine execution proof at every bounded word size. -/
def exchangeCertificate (w : ℕ) : DynamicCertificate (exchangeProgram w) w where
  rep s x := x.Bounded w ∧ x.mem 0 = s
  bounded h := h.1
  arguments_fit _ h _ _ := h
  execute {s x} o hr hv := by
    let x₀ := (exchangeProgram w).prepare o x
    let x₁ := x₀.set 0 0
    let x₂ := x₁.set 2 (x₁.mem (x₁.regs 0))
    let y := x₂.write (x₂.regs 0) (x₂.regs 1)
    have he : Exec w (exchangeProgram w).code x₀ y 3 :=
      (Exec.const (fits_zero w)).seq (Exec.load.seq Exec.store)
    have hy : y.mem 0 = o := by simp [y, x₂, x₁, x₀, DynamicProgram.prepare, exchangeProgram,
      Data.set, Data.write]
    have hout : y.regs 2 = s := by
      simp [y, x₂, x₁, x₀, Data.set, Data.write, DynamicProgram.prepare, hr.2]
    refine ⟨y, 3, he, ?_, ⟨?_, hy⟩⟩
    · exact congrArg some hout
    · exact he.bounded ((exchangeProgram w).prepare_bounded hr.1 (fun _ _ => hv))

/-- A concrete initial representation exists even at word size zero. -/
theorem exchange_initial (w : ℕ) :
    (exchangeCertificate w).rep 0 (⟨fun _ => 0, fun _ => 0⟩ : Data 3) :=
  ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩, rfl⟩

/-- The exchange cell supports arbitrary admissible adaptive clients. -/
example (w : ℕ) {α : Type} (p : (exchangeSpec w).Client α)
    (hv : (exchangeSpec w).ValidHistory 0 ((exchangeSpec w).runClient 0 p).2.2) :
    ∃ y ts, Stateful.Executes ((exchangeProgram w).ExecOp w) p
        ⟨fun _ => 0, fun _ => 0⟩ ((exchangeSpec w).runClient 0 p).1 y ts ∧
      (exchangeCertificate w).rep ((exchangeSpec w).runClient 0 p).2.1 y :=
  (exchangeCertificate w).realization.exists_executes p (exchange_initial w) hv

/-- Read-only array queries preserve the abstract array and return the selected entry. -/
abbrev lookupSpec (n : ℕ) : Stateful.Spec where
  State := Fin n → ℕ
  Op := Fin n
  Result _ := ℕ
  step s i := (s, s i)

/-- Array lookup uses one load and the final halt. -/
def lookupProgram (n : ℕ) : DynamicProgram (lookupSpec n) 2 where
  code := .op (.load 1 0)
  output := 1
  input i := i == 0
  encode i _ := i
  decode _ regs := some (regs 1)

/-- Every represented bounded array has a uniform two-instruction query implementation. -/
def lookupCertificate (w n : ℕ) (hn : Fits w n) :
    DynamicCertificate (lookupProgram n) w where
  rep s x := x.Bounded w ∧ ∀ i : Fin n, x.mem i = s i
  bounded h := h.1
  arguments_fit i _ _ _ := lt_trans i.isLt hn
  execute {s x} i hr _ := by
    let x₀ := (lookupProgram n).prepare i x
    let y := x₀.set 1 (x₀.mem (x₀.regs 0))
    have he : Exec w (lookupProgram n).code x₀ y 1 := Exec.load
    refine ⟨y, 1, he, ?_, ⟨?_, ?_⟩⟩
    · simp [lookupProgram, y, x₀, Data.set, DynamicProgram.prepare, hr.2]
    · exact he.bounded ((lookupProgram n).prepare_bounded hr.1
        (fun _ _ => lt_trans i.isLt hn))
    · exact hr.2

/-- A represented read-only array exists for every width and admissible array size. -/
example (w n : ℕ) (hn : Fits w n) :
    (lookupCertificate w n hn).rep (fun _ => 0) ⟨fun _ => 0, fun _ => 0⟩ :=
  ⟨⟨fun _ => fits_zero w, fun _ => fits_zero w⟩, fun _ => rfl⟩

/-- Framing protects a second cell during a concrete store to the first. -/
example (w : ℕ) (x : Data 2) (h0 : x.regs 0 = 0) (h1 : x.mem 1 = 7) :
    (HeapAssertion.pointsto 1 7).holds (x.write 0 (x.regs 1)).mem := by
  have he : TraceExec (B := .standard) w (.op (.store 0 1)) x (x.write 0 (x.regs 1)) 1
      [.write 0 (x.regs 1)] := by
    simpa [Op.probes, h0] using
      (TraceExec.op (o := .store 0 1) (w := w) (x := x) rfl)
  exact he.frame h1 (by simp [HeapAssertion.pointsto, Probe.writes])

/-- An adaptive client chooses whether to pop from the observed size. -/
def stackClient : (Stack.spec 4 2).Client (Option ℕ × ℕ) :=
  .liftBind (.push 7) fun _ =>
    .liftBind .size fun (n : ℕ) =>
      if n = 1 then
        .liftBind .pop fun v => .liftBind .size fun (m : ℕ) => .pure (v, m)
      else .pure (none, n)

/-- The test client is admissible from the concrete empty representation. -/
example : (Stack.spec 4 2).ValidHistory [] ((Stack.spec 4 2).runClient [] stackClient).2.2 :=
  by
    change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
    decide

/-- The concrete stack realizes an adaptive observation with a cumulative native cost bound. -/
example : ∃ y ts,
    Stateful.Executes ((Stack.implementation 4 2).ExecOp 4) stackClient
        (Stack.initial 3) (some 7, 0) y ts ∧ Stack.Rep 4 3 2 [] y ∧
      Stateful.total DynamicProgram.OperationTrace.instructions ts ≤ 48 := by
  exact Stack.run_client (base := 3) (by decide : Fits 4 2) (by decide : Fits 4 (3 + 2))
      stackClient (Stack.initial_rep (by decide : Fits 4 (3 + 2))) (by
        change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
        decide)

/-- Typed push, empty pop, and size queries on `Stack.implementation 4 2`, plus decoder rejection
and loop-fuel exhaustion on `exchangeProgram 4`. -/
example :
    ((Stack.implementation 4 2).eval 4 0 (.push 7) (Stack.initial 3)).map
      (fun (y, answer, cost) => (y.mem 3, y.regs Stack.len, answer, cost)) =
        some (7, 1, (), 8) ∧
    ((Stack.implementation 4 2).eval 4 0 .pop (Stack.initial 3)).map
      (fun (_, answer, _) => answer) = some none ∧
    ((Stack.implementation 4 2).eval 4 0 .size (Stack.initial 3)).map
      (fun (_, answer, _) => answer) = some 0 ∧
    ({ exchangeProgram 4 with decode := fun _ _ => none }).eval 4 0 7
      ⟨fun _ => 0, fun _ => 0⟩ = none ∧
    ({ exchangeProgram 4 with code := .loop (.eq 0 0) (.op (.copy 0 0)) }).eval 4 2 7
      ⟨fun _ => 0, fun _ => 0⟩ = none := by
  decide

/-- Successful evaluation of a represented, admissible call supplies native execution evidence. -/
example {y : Data 9} {cost : ℕ}
    (he : (Stack.implementation 4 2).eval 4 0 (.push 7) (Stack.initial 3) =
      some (y, (), cost)) :
    ∃ probes, (Stack.implementation 4 2).ExecOp 4 (Stack.initial 3) (.push 7) () y
      ⟨cost, probes⟩ :=
  (Stack.certificate (w := 4) (capacity := 2) (base := 3) (by decide) (by decide)).execOp_of_eval
    (Stack.initial_rep (by decide)) (by decide) he

/-- A full stack rejects another push, while the largest fitting word remains a valid value. -/
example : ¬(Stack.spec 4 2).valid [4, 7] (.push 2) ∧
    (Stack.spec 4 2).valid [] (.push 15) := by decide

/--
info: 'Cslib.WordRAM.DynamicCertificate.realization' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms DynamicCertificate.realization
/--
info: 'Cslib.WordRAM.TraceExec.exec' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms TraceExec.exec

end WordRAMDynamicTests
