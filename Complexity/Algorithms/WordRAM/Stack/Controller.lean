/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Stack
public import Complexity.Tactic.WordRAM

/-!
# An adaptive stack client executed entirely on the word RAM

The client pushes its input, pops it, and replaces a returned zero by another push and pop of
one. Its fixed controller explicitly executes initialization, argument preparation and branch
instructions. Input placement follows `WordRAM.Data.init`; no additional heap initialization is
needed because the reserved stack starts empty.

## Main definitions

* `roundTrip`: push the argument register and pop its value back.
* `code`: initialize one reserved cell and execute the adaptive controller.
* `client`: the same adaptive computation over the abstract stack interface.

## Main results

* `execute`: the whole controller returns `max n 1`, leaving its stack empty.
* `refines`: the fixed machine controller implements the abstract adaptive client.
* `executes`: a halting flat program, with all controller costs and its final halt charged.
* `positive_polytime`: a reusable polynomial RAM-time certificate for the complete client.

## References

The stack implementation and specification are those of `WordRAM.Stack` and
`Algorithms.Lean.Queue`. This example is a certificate-composition test, not a new stack algorithm.
-/

@[expose] public section

namespace Cslib.WordRAM.Stack.Controller

open Cslib.Algorithms.Lean.Queue

/-- Push the argument register, then pop it; argument tags and clearing are real instructions. -/
def roundTrip : Code .standard 9 := ram[
  tag ← #0; ⟪program⟫; tag ← #1; arg ← #0; ⟪program⟫ ]

/-- One reserved stack cell at address two, outside the singleton input at address one. -/
def setup : Code .standard 9 := ram[
  ptr ← #2; len ← #0; addr ← #1; arg ← *addr ]

/-- Fixed adaptive code: replace a popped zero using another pair of stack operations. -/
def code : Code .standard 9 := ram[
  ⟪setup⟫; ⟪roundTrip⟫;
  if out = len then [ arg ← #1; ⟪roundTrip⟫ ] else [ out ← out ] ]

/-- The abstract controller observes its first pop before deciding whether to call again. -/
def client (w n : ℕ) : (spec w 1).Client ℕ :=
  .liftBind (.push n) fun _ => .liftBind .pop fun (a : Option ℕ) =>
    if a = some 0 then
      .liftBind (.push 1) fun _ => .liftBind .pop fun (b : Option ℕ) => .pure (b.getD 0)
    else .pure (a.getD 0)

private theorem prepare_push {w n : ℕ} {x : Data 9} (hn : x.regs arg = n) :
    (implementation w 1).prepare (.push n) x = x.set tag 0 := by
  ext i
  · fin_cases i <;> simp_all +decide [implementation, DynamicProgram.prepare, Data.set,
      tag, arg]
  · rfl

private theorem prepare_pop (w : ℕ) (x : Data 9) :
    (implementation w 1).prepare .pop x = (x.set tag 1).set arg 0 := by
  ext i
  · fin_cases i <;> simp +decide [implementation, DynamicProgram.prepare, Data.set, tag, arg]
  · rfl

/-- A full push/pop round trip costs twenty-one instructions, including argument delivery. -/
private theorem roundTrip_exec {w n : ℕ} {x : Data 9} (h3 : Fits w 3)
    (hr : Rep w 2 1 [] x) (hn : x.regs arg = n) :
    ∃ y, Exec w roundTrip x y 21 ∧ Rep w 2 1 [] y ∧ y.regs out = n := by
  have h2 : Fits w 2 := h3.of_le (by decide)
  have h1 : Fits w 1 := h3.of_le (by decide)
  have hfit : Fits w n := hn ▸ hr.bounded.1 arg
  obtain ⟨y, hy, _, hry, _⟩ := Stack.execute h2 h3 hr (.push n) ⟨by decide, hfit⟩
  obtain ⟨z, hz, ha, hrz, _⟩ := Stack.execute h2 h3 hry .pop trivial
  have hp : Exec (B := .standard) w (.op (.const tag 0)) x
      ((implementation w 1).prepare (.push n) x) 1 := by
    rw [prepare_push hn]
    exact Exec.const (fits_zero w)
  refine ⟨z, ?_, hrz, ?_⟩
  · exact Exec.seq hp (Exec.seq hy (Exec.seq (Exec.const h1)
      (Exec.seq (Exec.const (fits_zero w)) (by simpa only [prepare_pop] using hz))))
  · change some (if z.regs present = 0 then none else some (z.regs out)) = some (some n) at ha
    split at ha
    · cases ha
    · exact Option.some.inj (Option.some.inj ha)

/-- Initialize the empty representation and load the input in four actual instructions. -/
private theorem setup_exec {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    ∃ x, Exec w setup (Data.init [n]) x 4 ∧ Rep w 2 1 [] x ∧ x.regs arg = n := by
  let x := (((Data.init [n]).set ptr 2).set len 0).set addr 1 |>.set arg n
  have h2 : Fits w 2 := h3.of_le (by decide)
  have h1 : Fits w 1 := h3.of_le (by decide)
  have he : Exec w setup (Data.init [n]) x 4 := by
    ram_eval [setup, x, Data.init, h2, h1]
  refine ⟨x, he, ⟨he.bounded (Data.Bounded.init hn), ?_, ?_, by decide, ?_⟩, ?_⟩
  · simp +decide [x, Data.set, ptr, len, addr, arg]
  · simp +decide [x, Data.set, ptr, len, addr, arg]
  · intro i
    exact Fin.elim0 i
  · simp [x, Data.set]

private theorem rep_set_arg {w : ℕ} {x : Data 9} (hr : Rep w 2 1 [] x)
    (h1 : Fits w 1) : Rep w 2 1 [] (x.set arg 1) := by
  refine ⟨(Exec.const (B := Basis.standard) (d := arg) (x := x) h1).bounded hr.bounded,
    ?_, ?_, by decide, fun i => Fin.elim0 i⟩
  · simpa +decide [Data.set, arg, ptr] using hr.pointer
  · simpa +decide [Data.set, arg, len] using hr.length_eq

/-- The exact controller time includes setup, adaptive control and argument preparation.
The final halt is added separately by `Exec.executes`. -/
theorem execute {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    ∃ y, Exec w code (Data.init [n]) y (if n = 0 then 48 else 28) ∧
      Rep w 2 1 [] y ∧ y.regs out = max n 1 := by
  obtain ⟨x, hx, hrx, hnx⟩ := setup_exec h3 hn
  obtain ⟨y, hy, hry, hny⟩ := roundTrip_exec h3 hrx hnx
  have hl : y.regs len = 0 := hry.length_eq
  have h1 : Fits w 1 := h3.of_le (by decide)
  by_cases hn0 : n = 0
  · obtain ⟨z, hz, hrz, hnz⟩ := roundTrip_exec h3 (rep_set_arg hry h1)
      (n := 1) (by simp [Data.set])
    refine ⟨z, ?_, hrz, ?_⟩
    · rw [ite_eq_left hn0]
      exact Exec.seq hx (Exec.seq hy (Exec.branch_pos (c := .eq out len) (by
        change y.regs out = y.regs len
        omega) (Exec.seq (Exec.const h1) hz)))
    · simpa [hn0] using hnz
  · have hc : Exec (B := .standard) w (.op (.copy out out)) y y 1 := by
      convert (Exec.copy (B := Basis.standard) (x := y) (d := out) (s := out)) using 1
      ext i <;> simp [Data.set]
    refine ⟨y, ?_, hry, ?_⟩
    · simp only [hn0, ↓reduceIte]
      exact Exec.seq hx (Exec.seq hy (Exec.branch_neg (by
        change ¬y.regs out = y.regs len
        omega) hc))
    · rw [hny, max_eq_left (by omega)]

/-- The abstract client returns the same positive value and restores the empty stack. -/
private theorem runClient_client (w n : ℕ) :
    ((spec w 1).runClient [] (client w n)).1 = max n 1 ∧
      ((spec w 1).runClient [] (client w n)).2.1 = [] := by
  by_cases hn : n = 0
  · simp [client, -PFunctor.FreeM.pure_eq_pure, hn]
  · simp [client, -PFunctor.FreeM.pure_eq_pure, hn,
      max_eq_left (show 1 ≤ n by omega)]

/-- Both adaptive histories respect the one-cell capacity and word bounds. -/
private theorem client_valid {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    (spec w 1).ValidHistory [] ((spec w 1).runClient [] (client w n)).2.2 := by
  have h1 : Fits w 1 := h3.of_le (by decide)
  have hfit : Fits w n := hn.2 n (by simp)
  by_cases hn0 : n = 0 <;>
    simp [client, -PFunctor.FreeM.pure_eq_pure, hn0, hfit, h1]

/-- The full fixed controller refines the adaptive client, including setup and argument work. -/
@[program_certificate]
theorem refines {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    Refines w (fun s x => s = [] ∧ x = Data.init [n]) (client w n)
      (fun a s y => Rep w 2 1 s y ∧ y.regs out = a)
      (fun _ _ => if n = 0 then 48 else 28) code := by
  rintro s x ⟨rfl, rfl⟩
  obtain ⟨y, he, hr, ha⟩ := execute h3 hn
  obtain ⟨hv, hs⟩ := runClient_client w n
  refine ⟨client_valid h3 hn, y, he.within, ?_, ?_⟩
  · simpa only [hs] using hr
  · simpa only [hv] using ha

/-- A single flat program computes the positive replacement, including its final halt. -/
theorem executes {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    Executes w (code.program out) (State.init [n]) (max n 1)
      ((if n = 0 then 48 else 28) + 1) := by
  obtain ⟨y, he, _, ha⟩ := execute h3 hn
  simpa only [ha, State.init] using he.executes out

/-- The shared refinement API produces a uniform forty-nine-instruction certificate. -/
theorem executes_le {w n : ℕ} (h3 : Fits w 3) (hn : InputFits w [n]) :
    ∃ t ≤ 49, Executes w (code.program out) (State.init [n]) (max n 1) t := by
  obtain ⟨t, ht, hb⟩ := (refines h3 hn).executes out id
    (fun _ _ _ h => h.2) ⟨rfl, rfl⟩
  refine ⟨t, ?_, ?_⟩
  · split at hb <;> omega
  · simpa only [id_eq, (runClient_client w n).1, State.init] using ht

/-- The word-valued function computed by the adaptive stack controller. -/
def positive (n : ℕ) : ℕ := max n 1

/-- Uniform computation at every fitting word size of at least two bits. -/
theorem computesInTime :
    (code.program out).ComputesInTime (fun _ n => [n]) (fun _ _ => 49)
      (fun _ w => 2 ≤ w) positive := by
  intro n w hw hn
  have h3 : Fits w 3 := (show Fits 2 3 by decide).mono hw
  obtain ⟨t, ht, he⟩ := executes_le h3 hn
  exact ⟨t, he, ht⟩

/-- The same fixed controller has a constant, hence polynomial, RAM instruction bound.
The size parameter is the numerical magnitude `n`; the admissible width is logarithmic in it. -/
@[fun_prop, program_certificate]
theorem positive_polytime :
    UniformComputableInPolyTime .standard positive (fun _ n => [n]) id := by
  apply UniformComputableInPolyTime.of_program (code.program out) (.const 49) 2 (by decide)
  apply computesInTime.mono (fun _ _ => le_rfl)
  intro n w hw
  change 2 * (Nat.log 2 n + 1) ≤ w at hw
  omega

/-- The logarithmic threshold used by the function certificate fits every input, so the
uniform computation theorem has a successful execution for every natural input. -/
theorem input_fits (n : ℕ) : InputFits (logWidth 2 n) [n] := by
  have hw : 2 ≤ logWidth 2 n := by unfold logWidth; omega
  refine ⟨?_, ?_⟩
  · exact (show Fits 2 1 by decide).mono hw
  · intro v hv
    have hvn : v = n := by simpa using hv
    subst v
    exact (fits_of_lt_pow (k := 1) (n := n) (by simp)).mono
      (logWidth_mono (by decide) le_rfl)

end Cslib.WordRAM.Stack.Controller
