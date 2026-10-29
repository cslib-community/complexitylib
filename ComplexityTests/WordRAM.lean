/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.WordRAM.ElementDistinctness

/-!
# Word-RAM clients

Model regressions for the bounded-word RAM: overflow faults instead of wrapping, a program that
reads the word size can tell word sizes apart, the interpreter runs flat programs, the program
notation and `ram_eval` execute straight-line code symbolically, and the compiled element
distinctness program answers correctly on inputs with and without duplicates within its time
bound.
-/

namespace ComplexityTests.WordRAM

open Cslib.WordRAM

/-! ## The machine -/

/-- Overflow faults (`8` at width `3`, or `5 + 5` at width `3`), running off the end of a program
faults, a program reading the word size tells word sizes apart, and the input length is at
address `0` followed by the words. -/
example :
    (run (B := .standard) 3 [.op (.const (0 : Fin 1) 8), .halt 0] 5 (.init []) = none ∧
      run (B := .standard) 3 [.op (.const (0 : Fin 1) 7), .halt 0] 5 (.init []) = some (7, 2)) ∧
    run 3 [.op (.const (0 : Fin 1) 5), .op (.bin .add 0 0 0), .halt 0] 5 (.init []) = none ∧
    run (B := .standard) 8 [.op (.const (0 : Fin 1) 5)] 5 (.init []) = none ∧
    (run 4 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (4, 2) ∧
      run 5 [.op (.width (0 : Fin 1)), .halt 0] 5 (.init []) = some (5, 2)) ∧
    run (B := .standard) 8 [.op (.load (1 : Fin 2) 0), .halt 1] 5 (.init [5, 6, 7]) =
      some (3, 2) ∧
    Executes (B := .standard) 8 [.op (.load (1 : Fin 2) 0), .halt 1] (.init [5, 6, 7]) 3 2 :=
  ⟨by decide, by decide, by decide, by decide, by decide, .of_run (fuel := 5) (by decide)⟩

/-- Truncated subtraction, division by zero and the bitwise operations. -/
example : BinOp.sub.eval 3 5 = 0 ∧ BinOp.div.eval 7 0 = 0 ∧ BinOp.mod.eval 7 0 = 7 ∧
    BinOp.and.eval 6 3 = 2 ∧ BinOp.xor.eval 6 3 = 5 ∧ BinOp.shiftLeft.eval 3 2 = 12 := by
  decide

/-! ## Structured programs and notation -/

section Notation

/-- Register names for the examples. -/
abbrev a : Fin 3 := 0
/-- Register names for the examples. -/
abbrev b : Fin 3 := 1
/-- Register names for the examples. -/
abbrev c : Fin 3 := 2

/-- A straight-line program with a conditional and a store. -/
def straight : Code .standard 3 := ram[
  b ← #5;
  c ← #7;
  c ← b + c;
  if b < c then [ c ← c - b ] else [ c ← #0 ];
  *b ← c ]

/-- Desugared syntax of `straight` and concrete evaluation counting the taken branch instruction. -/
example :
    straight = .seq (.op (.const b 5)) (.seq (.op (.const c 7)) (.seq (.op (.bin .add c b c))
      (.seq (.branch (.lt b c) (.op (.bin .sub c c b)) (.op (.const c 0))) (.op (.store b c))))) ∧
    (straight.eval 8 0 (.init [])).map (·.2) = some 6 :=
  ⟨rfl, by decide⟩

/-- `ram_eval` executes the program symbolically on arbitrary data. -/
example (x : Data 3) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 := by
  refine ⟨?y, ?run, ?mem⟩
  case run => ram_eval [straight]
  case mem => simp

/-- `ram_eval` at a symbolic word size, from facts stated with `Fits`. -/
example (w : ℕ) (x : Data 3) (h5 : Fits w 5) (h7 : Fits w 7) (h12 : Fits w 12) :
    ∃ y, ExecWithin w straight x y 6 ∧ y.mem 5 = 7 := by
  refine ⟨?y, ?run, ?mem⟩
  case run => ram_eval [straight, h5, h7, h12]
  case mem => simp

/-- Counting to three in a loop. -/
def count : Code .standard 3 := ram[ a ← #0; b ← #3; c ← #1; while a < b do [ a ← a + c ] ]

/-- `ram_eval` with three loop iterations: three constants, three iterations of an addition, a
branch and a jump, and a branch and a jump to leave the loop. -/
example (x : Data 3) : ∃ y, Exec 8 count x y 14 ∧ y.regs a = 3 := by
  refine ⟨?y, ?run, ?val⟩
  case run => ram_eval 3 [count]
  case val => simp

/-- Loop assembly, reading the word size, preservation of unwritten registers, and unreserved
identifiers `ram` and `width`. -/
example {w n : ℕ} {x y : Data 3} (h : Exec w straight x y n) (ram width : ℕ) :
    (ram[ while a < b do [ a ← a + c ] ] : Code .standard 3).assemble 0 =
      [.branch (.lt a b) 2, .jump 4, .op (.bin .add a a c), .jump 0] ∧
    ((ram[ a ← width% ] : Code .standard 3).eval 7 0 (.init [])).map (·.1.regs a) = some 7 ∧
    y.regs a = x.regs a ∧
    ram + width = width + ram :=
  ⟨rfl, by decide, h.regs_eq (by decide), Nat.add_comm _ _⟩

end Notation

/-! ## Running a program on other registers -/

section Rename

/-- Register names for a two-register program. -/
abbrev p : Fin 2 := 0
/-- Register names for a two-register program. -/
abbrev q : Fin 2 := 1

/-- A two-register program. -/
def double : Code .standard 2 := ram[ p ← #3; q ← p + p ]

/-- `double` runs on registers `2` and `0` of a three-register machine and leaves register `1`
alone, with the same instruction count. -/
example (x : Data 3) : ∃ y, Exec 8 (double.rename ![2, 0]) x y 2 ∧
    y.regs 2 = 3 ∧ y.regs 0 = 6 ∧ y.regs 1 = x.regs 1 := by
  have hf : Function.Injective (![2, 0] : Fin 2 → Fin 3) := by decide
  have e : Exec 8 double (x.comap ![2, 0]) (((x.comap ![2, 0]).set p 3).set q 6) 2 := by
    ram_eval [double]
  refine ⟨_, e.rename hf, ?_, ?_, ?_⟩
  · exact hf.extend_apply _ _ (0 : Fin 2)
  · exact hf.extend_apply _ _ (1 : Fin 2)
  · exact Function.extend_apply' _ _ _ (by decide)

end Rename

/-! ## Contract boundaries

These adversarial clients record the scope of the conditional time predicates. In particular,
word-count size alone does not bound input bit lengths, and an input-dependent prescribed width
can communicate information that the encoding does not contain.
-/

section Contracts

/-- The word size itself supplies the answer on two identically encoded instances. -/
private def widthAdvice : Program .standard 2 :=
  [.op (.width 0), .op (.const 1 1), .op (.bin .sub 0 0 1), .halt 0]

example :
    (∀ b : Bool, InputFits (if b then 2 else 1) []) ∧
    UniformDecidableInTime .standard {b : Bool | b = true} (fun _ _ => [])
      (fun _ _ => 4) (fun b w => w = if b then 2 else 1) := by
  refine ⟨fun b => ⟨fits_zero _, by simp⟩, 2, widthAdvice, ?_⟩
  intro b w hw _
  subst w
  cases b
  · exact ⟨0, 4, .of_run (fuel := 4) (by decide), le_rfl, by decide, by decide⟩
  · exact ⟨1, 4, .of_run (fuel := 4) (by decide), le_rfl, by decide, by decide⟩

/-- Even a nonuniform family cannot separate identically encoded instances at one common
width: selecting code by width gives both instances the same initial state and program. -/
example (time : Bool → ℕ → ℕ) (bits : Bool → ℕ) :
    ¬DecidableInTime .standard {b : Bool | b = true} (fun _ _ => []) time
      (fun b w => bits b ≤ w) := by
  rintro ⟨r, p, _, hp⟩
  let w := max (bits false) (bits true)
  have hi : InputFits w [] := ⟨fits_zero w, by simp⟩
  obtain ⟨v₀, n₀, he₀, _, _, hb₀⟩ := hp false w (le_max_left _ _) hi
  obtain ⟨v₁, n₁, he₁, _, _, hb₁⟩ := hp true w (le_max_right _ _) hi
  have hv := (he₀.unique he₁).1
  have h1 : v₁ = 1 := hb₁.mpr rfl
  have : false = true := hb₀.mp (hv.trans h1)
  cases this

/-- If the prescribed width never fits the input, the conditional contract accepts any set
without a successful run. -/
example (A : Set Bool) :
    UniformDecidableInTime .standard A (fun _ _ => [1]) (fun _ _ => 0)
      (fun _ w => w = 0) := by
  refine ⟨0, [], ?_⟩
  intro b w hw hi
  subst w
  have h := hi.1
  change 1 < 1 at h
  exact False.elim (Nat.lt_irrefl 1 h)

/-- A constant-answer program works at every fitting width for arbitrary singleton words. -/
private def accept : Program .standard 1 := [.op (.const 0 1), .halt 0]

example : UniformLinearTime .standard (Set.univ : Set ℕ) (fun _ n => [n]) (fun _ => 1) := by
  refine ⟨1, 1, by decide, 1, accept, ?_⟩
  intro n w _ hi
  have h1 : Fits w 1 := hi.1
  refine ⟨1, 2, .of_run (fuel := 2) ?_, le_rfl, le_rfl, by simp⟩
  simp [WordSizeDependentProgram.const, run, step, accept, Op.eval, Data.put, h1, Data.set,
    State.init]

/-- The encoding above is injective and has constant word-count size, but no width depending
only on that size can fit all its instances. -/
example (w : ℕ) : Function.Injective (fun n : ℕ => [n]) ∧ ¬∀ n, InputFits w [n] := by
  refine ⟨fun _ _ h => List.singleton_injective h, ?_⟩
  intro h
  have hi := (h (2 ^ w)).2 (2 ^ w) (by simp)
  exact Nat.lt_irrefl _ hi

end Contracts

/-! ## Element distinctness -/

section ElementDistinctness

open Cslib.Algorithms.WordRAM.ElementDistinctness Cslib.Algorithms.WordRAM.ElementDistinctness.Reg

/-- Distinct entries (`[2, 0, 1]`), duplicates (`[1, 0, 1]`), the empty list, the threshold word
size `logWidth 2 3 = 4` versus faulting at width `2`, and `ReadsWidth` checks. -/
example :
    (run 8 (decider.program ans) 200 (.init [2, 0, 1])).map (·.1) = some 1 ∧
    (run 8 (decider.program ans) 200 (.init [1, 0, 1])).map (·.1) = some 0 ∧
    (run 8 (decider.program ans) 200 (.init [])).map (·.1) = some 1 ∧
    (logWidth 2 3 = 4 ∧ run 4 (decider.program ans) 200 (.init [2, 0, 1]) = some (1, 58) ∧
      58 ≤ 16 * (3 + 1) ∧ run 2 (decider.program ans) 200 (.init [2, 0, 1]) = none) ∧
    (¬decider.ReadsWidth ∧ ¬(decider.program ans).ReadsWidth) := by
  decide

/-- The client has an input-fit certificate at its actual logarithmic threshold, so its
correctness contract gives an unconditional answer there for every promised instance. -/
example (a : Input) :
    (decider.program ans).Answers (logWidth 2 a.1.length) a.1 a.1.Nodup
      (16 * (a.1.length + 1)) :=
  decidesInTime_nodup a _ le_rfl (inputFits a le_rfl)

/-- The one-digit convention includes the empty input at its advertised threshold. -/
example : logWidth 2 0 = 2 ∧ InputFits (logWidth 2 0) [] ∧
    (run (logWidth 2 0) (decider.program ans) 16 (.init [])).map (·.1) = some 1 := by
  decide

/-- The decider also decides at a prescribed width above its threshold, and element distinctness
for small entries is uniformly in polynomial time. -/
example : (decider.program ans).DecidesInTime (fun _ (l : Input) => l.1) {l | l.1.Nodup}
      (fun l _ => 16 * (l.1.length + 1)) (fun l w => w = logWidth 2 l.1.length + 7) ∧
    UniformPolynomialTime .standard {l : Input | l.1.Nodup} (fun _ l => l.1)
      (fun l => l.1.length) := by
  refine ⟨decidesInTime_nodup.mono (fun _ _ => le_rfl) ?_,
    uniformLinearTime_nodup.polynomialTime⟩
  intro a w hw
  omega

end ElementDistinctness

/-! ## Axioms -/

/--
info: 'Cslib.WordRAM.UniformDecidableInTime.decidableInTime' depends on axioms: [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.UniformDecidableInTime.decidableInTime

/--
info: 'Cslib.WordRAM.Executes.mono_width' depends on axioms:
[propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.Executes.mono_width

/--
info: 'Cslib.WordRAM.executes_iff_exists_run_eq' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.executes_iff_exists_run_eq

/--
info: 'Cslib.WordRAM.ExecWithin.loop_invariant' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.WordRAM.ExecWithin.loop_invariant

end ComplexityTests.WordRAM
