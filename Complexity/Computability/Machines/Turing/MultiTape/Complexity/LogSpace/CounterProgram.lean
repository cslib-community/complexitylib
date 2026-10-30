/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
import Mathlib.Data.List.GetD

/-!
# Counter programs with random access to the input

A **counter program** (`Turing.CounterProgram`) is a finite list of instructions over a fixed
number of registers holding natural numbers. An instruction assigns to a register the value of an
arithmetic expression (`Turing.CounterProgram.Expr`: constants, registers, sums, truncated
differences, products, quotients, remainders and binary digit tests), branches on a comparison of
two expressions, branches on the input bit at the position given by an expression (or on its
absence past the end of the input), emits an output bit, or halts with a
final output word. Labels are natural numbers; a label outside the program halts.

Counter programs are the classical description of logarithmic-space algorithms: a constant number
of counters, each bounded by a polynomial in the input length, with random read-only access to
the input. A program whose registers stay at most `(n + 1) ^ d` on inputs of length `n` computes a
function in logarithmic space (`Turing.CounterProgram.computableInLogSpace`), as a query machine
(`Turing.QueryMachine`) whose steps are computed in space linear in the binary registers. For
programs that never emit, the hypotheses can be established with a reachability predicate
(`Turing.CounterProgram.Reaches`) that records an invariant of the states passed through
(`Turing.CounterProgram.computableInLogSpace_of_reaches`). Programs that emit are treated with
the reachability predicate that records the emitted bits (`Turing.CounterProgram.ReachesOut`).
The parts of the simulation by a query machine live in the namespace
`Turing.CounterProgram.Simulation`.

## Main definitions

* `Turing.CounterProgram.Expr`, `Turing.CounterProgram.Instr`: expressions and instructions.
* `Turing.CounterProgram`: counter programs.
* `Turing.CounterProgram.Config`: configurations, a label and the values of the registers.
* `Turing.CounterProgram.step`, `Turing.CounterProgram.Reaches`: steps and reachability.
* `Turing.CounterProgram.Running`: the configurations at running instructions, with bounded
  registers.
* `Turing.CounterProgram.CodeAt`: a list of instructions placed at a label.
* `Turing.CounterProgram.toQueryMachine`: a counter program as a query machine.

## Main results

* `Turing.CounterProgram.Expr.eval_inSpace`: expressions are evaluated in linear space.
* `Turing.CounterProgram.Reaches.assign`, `Turing.CounterProgram.Reaches.lt`,
  `Turing.CounterProgram.Reaches.read`: stepping through running instructions.
* `Turing.CounterProgram.computableInLogSpace`: counter programs with polynomially bounded
  registers run in logarithmic space.
* `Turing.CounterProgram.computableInLogSpace_of_reaches`: the same, for programs without
  emissions, from a reachability statement.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.4][Sipser2013]
-/

@[expose] public section

namespace Turing

namespace CounterProgram

/-- Arithmetic expressions over the registers. -/
inductive Expr : Type where
  /-- A constant. -/
  | const (k : ℕ)
  /-- The value of a register. -/
  | reg (i : ℕ)
  /-- A sum. -/
  | add (a b : Expr)
  /-- Truncated subtraction. -/
  | sub (a b : Expr)
  /-- A binary digit, with value zero or one. -/
  | bit (a i : Expr)
  /-- A product. -/
  | mul (a b : Expr)
  /-- A quotient, `0` for the divisor `0`. -/
  | div (a b : Expr)
  /-- A remainder; the remainder of `a` by `0` is `a`. -/
  | mod (a b : Expr)
  deriving Inhabited

namespace Expr

/-- The value of an expression; a register outside the list reads `0`. -/
def eval (regs : List ℕ) : Expr → ℕ
  | const k => k
  | reg i => regs.getD i 0
  | add a b => a.eval regs + b.eval regs
  | sub a b => a.eval regs - b.eval regs
  | bit a i => ((a.eval regs).testBit (i.eval regs)).toNat
  | mul a b => a.eval regs * b.eval regs
  | div a b => a.eval regs / b.eval regs
  | mod a b => a.eval regs % b.eval regs

@[simp] theorem eval_const (regs : List ℕ) (k : ℕ) : (const k).eval regs = k := rfl
@[simp] theorem eval_reg (regs : List ℕ) (i : ℕ) : (reg i).eval regs = regs.getD i 0 := rfl
@[simp] theorem eval_add (regs : List ℕ) (a b : Expr) :
    (add a b).eval regs = a.eval regs + b.eval regs := rfl
@[simp] theorem eval_sub (regs : List ℕ) (a b : Expr) :
    (sub a b).eval regs = a.eval regs - b.eval regs := rfl
@[simp] theorem eval_bit (regs : List ℕ) (a i : Expr) :
    (bit a i).eval regs = ((a.eval regs).testBit (i.eval regs)).toNat := rfl
@[simp] theorem eval_mul (regs : List ℕ) (a b : Expr) :
    (mul a b).eval regs = a.eval regs * b.eval regs := rfl
@[simp] theorem eval_div (regs : List ℕ) (a b : Expr) :
    (div a b).eval regs = a.eval regs / b.eval regs := rfl
@[simp] theorem eval_mod (regs : List ℕ) (a b : Expr) :
    (mod a b).eval regs = a.eval regs % b.eval regs := rfl

/-- A power of an expression. -/
def pow (e : Expr) : ℕ → Expr
  | 0 => const 1
  | k + 1 => mul (pow e k) e

/-- The sum of a list of expressions. -/
def sum : List Expr → Expr
  | [] => const 0
  | e :: es => add e (sum es)

@[simp] theorem eval_pow (regs : List ℕ) (e : Expr) (k : ℕ) :
    (pow e k).eval regs = e.eval regs ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [pow, ih, pow_succ]

@[simp] theorem eval_sum (regs : List ℕ) (es : List Expr) :
    (sum es).eval regs = (es.map fun e => e.eval regs).sum := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [sum, ih]

end Expr

/-- Instructions of counter programs, with natural numbers as labels. -/
inductive Instr : Type where
  /-- Assign to register `i` the value of `e`, then go to `next`. -/
  | assign (i : ℕ) (e : Expr) (next : ℕ)
  /-- Go to `yes` if the value of `a` is less than that of `b`, to `no` otherwise. -/
  | lt (a b : Expr) (yes no : ℕ)
  /-- Read the input bit at the position given by `e`: go to `onTrue` on `true`, `onFalse` on
  `false`, and `onEnd` past the end of the input. -/
  | read (e : Expr) (onTrue onFalse onEnd : ℕ)
  /-- Emit the bit `b`, then go to `next`. -/
  | emit (b : Bool) (next : ℕ)
  /-- Halt, emitting the word `out`. -/
  | halt (out : List Bool)
  deriving Inhabited

namespace Instr

/-- The instructions that neither emit nor halt. -/
def IsStep : Instr → Prop
  | assign .. | lt .. | read .. => True
  | emit .. | halt .. => False

/-- Halting with output `[true]`, the verdict of a decider that accepts. -/
abbrev accept : Instr := halt [true]

/-- Halting with output `[false]`, the verdict of a decider that rejects. -/
abbrev reject : Instr := halt [false]

/-- The largest label an instruction jumps to. -/
def maxLabel : Instr → ℕ
  | assign _ _ next => next
  | lt _ _ yes no => max yes no
  | read _ onTrue onFalse onEnd => max onTrue (max onFalse onEnd)
  | emit _ next => next
  | halt _ => 0

end Instr

end CounterProgram

/-- A **counter program**: a list of instructions, indexed by their labels, over a fixed number of
registers. -/
structure CounterProgram : Type where
  /-- The instructions; the instruction at label `c` is the `c`-th one. -/
  code : List CounterProgram.Instr
  /-- The number of registers. -/
  registers : ℕ

namespace CounterProgram

open Instr

variable (P : CounterProgram) (w : List Bool)

/-- The configurations: a label and the values of the registers. -/
abbrev Config : Type := ℕ × List ℕ

/-- The instruction at a label; outside the program, a halt with empty output. -/
def instr (c : ℕ) : Instr := P.code.getD c (halt [])

/-- The initial configuration: label `0`, all registers `0`. -/
def init : Config := (0, List.replicate P.registers 0)

/-- The label a read jumps to, given the bit read. -/
def readLabel (onTrue onFalse onEnd : ℕ) : Option Bool → ℕ
  | some true => onTrue
  | some false => onFalse
  | none => onEnd

namespace Instr

/-- The position an instruction reads, or `0` if it does not read. -/
def query (i : Instr) (regs : List ℕ) : ℕ :=
  match i with
  | read e .. => e.eval regs
  | _ => 0

/-- The configuration after an instruction, given the input bit read. -/
def exec (i : Instr) (s : Config) (b : Option Bool) : Config :=
  match i with
  | assign j e next => (next, s.2.set j (e.eval s.2))
  | lt x y yes no => (if x.eval s.2 < y.eval s.2 then yes else no, s.2)
  | read _ onTrue onFalse onEnd => (readLabel onTrue onFalse onEnd b, s.2)
  | emit _ next => (next, s.2)
  | halt _ => s

/-- The bits an instruction emits. -/
def emitted : Instr → List Bool
  | emit b _ => [b]
  | _ => []

/-- Whether an instruction halts. -/
def halts : Instr → Bool
  | halt _ => true
  | _ => false

/-- The final word of a halting instruction. -/
def finish : Instr → List Bool
  | halt out => out
  | _ => []

end Instr

/-- The position read in a configuration, or `0` if the instruction does not read. -/
def query (s : Config) : ℕ := (P.instr s.1).query s.2

/-- The configuration after the instruction at the current label, given the input bit read. -/
def exec (s : Config) (b : Option Bool) : Config := (P.instr s.1).exec s b

/-- The bits emitted by the instruction at the current label. -/
def emitted (s : Config) : List Bool := (P.instr s.1).emitted

/-- Whether the instruction at the current label halts. -/
def halted (s : Config) : Bool := (P.instr s.1).halts

/-- The final word of a halting configuration. -/
def finish (s : Config) : List Bool := (P.instr s.1).finish

/-- A counter program as a query machine. -/
def toQueryMachine : QueryMachine Config where
  init := P.init
  query := P.query
  next p := P.exec p.1 p.2
  emit p := P.emitted p.1
  halted := P.halted
  finish := P.finish

/-- A step of a counter program on the input `w`. -/
def step (s : Config) : Config := P.toQueryMachine.step w s

/-- The configuration after `t` steps on the input `w`. -/
def run (t : ℕ) : Config := P.toQueryMachine.run w t

theorem step_eq (s : Config) :
    P.step w s = if P.halted s = true then s else P.exec s w[P.query s]? := rfl

theorem run_succ (t : ℕ) : P.run w (t + 1) = P.step w (P.run w t) :=
  QueryMachine.run_succ _ _ _

theorem step_of_isStep {s : Config} (h : (P.instr s.1).IsStep) :
    P.step w s = P.exec s w[P.query s]? := by
  have : P.halted s = false := by
    unfold halted
    revert h
    cases P.instr s.1 <;> simp [IsStep, Instr.halts]
  simp [step, QueryMachine.step, toQueryMachine, this, QueryMachine.read]

theorem step_assign {s : Config} {i : ℕ} {e : Expr} {next : ℕ}
    (h : P.instr s.1 = assign i e next) : P.step w s = (next, s.2.set i (e.eval s.2)) := by
  rw [P.step_of_isStep w (by rw [h]; trivial), exec, h, Instr.exec]

theorem step_lt {s : Config} {x y : Expr} {yes no : ℕ} (h : P.instr s.1 = lt x y yes no) :
    P.step w s = (if x.eval s.2 < y.eval s.2 then yes else no, s.2) := by
  rw [P.step_of_isStep w (by rw [h]; trivial), exec, h, Instr.exec]

theorem step_read {s : Config} {e : Expr} {onTrue onFalse onEnd : ℕ}
    (h : P.instr s.1 = read e onTrue onFalse onEnd) :
    P.step w s = (readLabel onTrue onFalse onEnd w[e.eval s.2]?, s.2) := by
  rw [P.step_of_isStep w (by rw [h]; trivial), exec, h, Instr.exec, query, h, Instr.query]

/-! ### Reachability -/

/-- `P.Reaches w Q s s'`: from `s`, the program reaches `s'` on the input `w`, and every
configuration before `s'` satisfies `Q`. This is the reflexive and transitive closure of the steps
from configurations satisfying `Q`, stated with a number of steps, the form in which the runs of
`Turing.CounterProgram.computableInLogSpace` are given. -/
def Reaches (Q : Config → Prop) (s s' : Config) : Prop :=
  ∃ t, (P.step w)^[t] s = s' ∧ ∀ t' < t, Q ((P.step w)^[t'] s)

variable {P w} {Q : Config → Prop} {s s' s'' : Config}

theorem Reaches.refl (s : Config) : P.Reaches w Q s s := ⟨0, rfl, fun _ h => absurd h (by omega)⟩

theorem Reaches.trans (h : P.Reaches w Q s s') (h' : P.Reaches w Q s' s'') :
    P.Reaches w Q s s'' := by
  obtain ⟨t, rfl, ht⟩ := h
  obtain ⟨t', rfl, ht'⟩ := h'
  refine ⟨t' + t, by rw [Function.iterate_add_apply], fun u hu => ?_⟩
  rcases lt_or_ge u t with hlt | hge
  · exact ht u hlt
  · have := ht' (u - t) (by omega)
    rwa [← Function.iterate_add_apply, Nat.sub_add_cancel hge] at this

/-- One step from a configuration satisfying `Q`. -/
theorem Reaches.single (hs : Q s) : P.Reaches w Q s (P.step w s) :=
  ⟨1, rfl, fun t ht => by rw [show t = 0 by omega]; exact hs⟩

theorem Reaches.head (hs : Q s) (h : P.Reaches w Q (P.step w s) s') : P.Reaches w Q s s' :=
  (Reaches.single hs).trans h

theorem Reaches.mono {Q' : Config → Prop} (h : P.Reaches w Q s s') (hQ : ∀ s, Q s → Q' s) :
    P.Reaches w Q' s s' :=
  let ⟨t, ht, hQt⟩ := h
  ⟨t, ht, fun u hu => hQ _ (hQt u hu)⟩

/-! ### Running configurations -/

variable (P) in
/-- The configurations at an assignment, a comparison or a read, with all registers at most
`B`. -/
def Running (B : ℕ) (s : Config) : Prop := (P.instr s.1).IsStep ∧ ∀ r ∈ s.2, r ≤ B

variable {B : ℕ} {regs : List ℕ}

/-- Stepping through an assignment. -/
theorem Reaches.assign {c i : ℕ} {e : Expr} {next : ℕ} (hc : P.instr c = .assign i e next)
    (hB : ∀ r ∈ regs, r ≤ B) (h : P.Reaches w (P.Running B) (next, regs.set i (e.eval regs)) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hB⟩ (by rwa [P.step_assign w hc])

/-- Stepping through a comparison. -/
theorem Reaches.lt {c : ℕ} {x y : Expr} {yes no : ℕ} (hc : P.instr c = .lt x y yes no)
    (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Running B) (if x.eval regs < y.eval regs then yes else no, regs) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hB⟩ (by rwa [P.step_lt w hc])

/-- Stepping through a read. -/
theorem Reaches.read {c : ℕ} {e : Expr} {onTrue onFalse onEnd : ℕ}
    (hc : P.instr c = .read e onTrue onFalse onEnd) (hB : ∀ r ∈ regs, r ≤ B)
    (h : P.Reaches w (P.Running B) (readLabel onTrue onFalse onEnd w[e.eval regs]?, regs) s') :
    P.Reaches w (P.Running B) (c, regs) s' :=
  Reaches.head ⟨by rw [hc]; trivial, hB⟩ (by rwa [P.step_read w hc])

/-! ### Placing code -/

variable (P) in
/-- `P.CodeAt b l`: the instructions of `l` are at the labels from `b` on. -/
def CodeAt (b : ℕ) (l : List Instr) : Prop := ∀ i (hi : i < l.length), P.instr (b + i) = l[i]

variable {b : ℕ} {l l₁ l₂ : List Instr} {ins : Instr}

theorem codeAt_nil : P.CodeAt b [] := fun _ hi => absurd hi (by simp)

theorem codeAt_cons : P.CodeAt b (ins :: l) ↔ P.instr b = ins ∧ P.CodeAt (b + 1) l := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun i hi => ?_⟩
    rw [Nat.add_assoc, Nat.add_comm 1 i]
    exact h (i + 1) (by simpa using hi)
  · rintro ⟨h₀, h⟩ i hi
    rcases i with _ | i
    · exact h₀
    · rw [List.getElem_cons_succ, show b + (i + 1) = b + 1 + i by omega]
      exact h i (by simpa using hi)

theorem codeAt_append : P.CodeAt b (l₁ ++ l₂) ↔ P.CodeAt b l₁ ∧ P.CodeAt (b + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i (by simp only [List.length_append]; omega), List.getElem_append_left]
    · rw [Nat.add_assoc, h _ (by simp only [List.length_append]; omega),
        List.getElem_append_right (by omega)]
      simp
  · rintro ⟨h₁, h₂⟩ i hi
    rcases lt_or_ge i l₁.length with hlt | hge
    · rw [List.getElem_append_left hlt]
      exact h₁ i hlt
    · rw [List.getElem_append_right hge,
        ← h₂ (i - l₁.length) (by simp only [List.length_append] at hi; omega)]
      congr 1
      omega

/-- The blocks of a code made of blocks of a fixed length. -/
theorem CodeAt.flatMap_range {f : ℕ → List Instr} {m : ℕ} (hf : ∀ i, (f i).length = m) :
    ∀ {k : ℕ}, P.CodeAt b ((List.range k).flatMap f) → ∀ i < k, P.CodeAt (b + m * i) (f i)
  | 0, _, i, hi => absurd hi (by omega)
  | k + 1, h, i, hi => by
    rw [List.range_succ, List.flatMap_append, codeAt_append] at h
    rcases lt_or_ge i k with hlt | hge
    · exact CodeAt.flatMap_range hf h.1 i hlt
    · have hlen : ((List.range k).flatMap f).length = m * k := by
        simp [List.length_flatMap, hf, Nat.mul_comm]
      have := h.2
      rw [hlen, List.flatMap_singleton] at this
      rwa [show i = k by omega]

/-- Code placed in a program made of pieces. -/
theorem codeAt_of_code_eq {pre post : List Instr} (h : P.code = pre ++ l ++ post) :
    P.CodeAt pre.length l := fun i hi => by
  rw [instr, h, List.getD_eq_getElem _ _ (by simp only [List.length_append]; omega),
    List.getElem_append_left (by simp only [List.length_append]; omega),
    List.getElem_append_right (by omega)]
  simp

/-! ### The parts of a step, in linear space -/

section Computability

open MultiTapeTM ComputableTidilyInSpace

/-- **Expressions are evaluated in linear space** in the binary registers. -/
theorem Expr.eval_inSpace : ∀ e : Expr,
    ComputableTidilyInSpace (fun regs => e.eval regs) (encList encNat) encNat
      fun regs => (encList encNat regs).length
  | .const k => budget_const k (.refl _)
  | .reg i => budget_comp getD
      (budget_prod (of_inO (.of_linear (.of_eq (f := id) fun _ => rfl)))
        (budget_const i (.refl _)))
      (.of_le_linear 16 (8 * (2 * (encNat i).length + 3)) fun regs => by
        simp only [length_encPair, id]; omega)
  | .add a b =>
    have h := budget_prod (Expr.eval_inSpace a) (Expr.eval_inSpace b)
    budget_comp natAdd h (.add h.length_le (.const 1 _))
  | .sub a b => budget_natSub (Expr.eval_inSpace a) (Expr.eval_inSpace b)
  | .bit a i =>
    have h : ComputableTidilyInSpace
        (fun regs => (a.eval regs).testBit (i.eval regs)) (encList encNat) encBool
        (fun regs => (encList encNat regs).length) :=
      budget_comp_lin (g := fun p : ℕ × ℕ => p.1.testBit p.2)
        (f := fun regs => (a.eval regs, i.eval regs)) natTestBit (linear_mul 32)
        (budget_prod (Expr.eval_inSpace a) (Expr.eval_inSpace i))
    budget_finite Bool.toNat h
  | .mul a b =>
    have h := budget_prod (Expr.eval_inSpace a) (Expr.eval_inSpace b)
    budget_comp natMul h (.const_mul 32 (.add h.length_le (.const 1 _)))
  | .div a b =>
    have h := budget_prod (Expr.eval_inSpace a) (Expr.eval_inSpace b)
    budget_comp natDiv h (.const_mul 16 (.add h.length_le (.const 1 _)))
  | .mod a b =>
    have h := budget_prod (Expr.eval_inSpace a) (Expr.eval_inSpace b)
    budget_comp natMod h (.const_mul 16 (.add h.length_le (.const 1 _)))

namespace Simulation

/-! The parts of the simulation of a counter program by a query machine. -/

/-- The encoding of configurations: the label and the registers, in binary. -/
abbrev encConfig : Config ↪ List Bool := encPair encNat (encList encNat)

/-- The encoding of a configuration with the bit read. -/
abbrev encConfigRead : Config × Option Bool ↪ List Bool := encPair encConfig (encOption encBool)

theorem evalConfig_inSpace (e : Expr) :
    ComputableTidilyInSpace (fun s : Config => e.eval s.2) encConfig encNat
      fun s => (encConfig s).length :=
  budget_comp (e.eval_inSpace) (snd _ _) (.of_le fun s => by simp only [length_encPair]; omega)

theorem fst_inSpace :
    ComputableTidilyInSpace (fun x : Config × Option Bool => x.1) encConfigRead encConfig
      fun x => (encConfigRead x).length := fst _ _

theorem regs_inSpace :
    ComputableTidilyInSpace (fun x : Config × Option Bool => x.1.2) encConfigRead
      (encList encNat) fun x => (encConfigRead x).length :=
  budget_comp_lin (snd _ _) (.refl _) fst_inSpace

theorem evalConfigRead_inSpace (e : Expr) :
    ComputableTidilyInSpace (fun x : Config × Option Bool => e.eval x.1.2) encConfigRead encNat
      fun x => (encConfigRead x).length :=
  budget_comp (e.eval_inSpace) regs_inSpace
    (.of_le fun x => by simp only [length_encPair]; omega)

theorem query_inSpace :
    ComputableTidilyInSpace P.query encConfig encNat fun s => (encConfig s).length :=
  dispatch P.code (.halt []) (fun i s => i.query s.2)
    (fun i => by
      cases i with
      | read e => exact evalConfig_inSpace e
      | _ => exact budget_const 0 (.refl _))
    (fst _ _)

theorem halted_inSpace :
    ComputableTidilyInSpace P.halted encConfig encBool fun s => (encConfig s).length :=
  dispatch P.code (.halt []) (fun i _ => i.halts)
    (fun _ => budget_const _ (.refl _)) (fst _ _)

theorem finish_inSpace :
    ComputableTidilyInSpace P.finish encConfig encBits fun s => (encConfig s).length :=
  dispatch P.code (.halt []) (fun i _ => i.finish)
    (fun _ => budget_const _ (.refl _)) (fst _ _)

theorem label_inSpace :
    ComputableTidilyInSpace (fun x : Config × Option Bool => x.1.1) encConfigRead encNat
      fun x => (encConfigRead x).length :=
  budget_comp_lin (fst _ _) (.refl _) fst_inSpace

theorem emitted_inSpace :
    ComputableTidilyInSpace (fun x : Config × Option Bool => P.emitted x.1) encConfigRead
      encBits fun x => (encConfigRead x).length :=
  dispatch P.code (.halt []) (fun i _ => i.emitted)
    (fun _ => budget_const _ (.refl _)) label_inSpace

theorem exec_inSpace :
    ComputableTidilyInSpace (fun x : Config × Option Bool => P.exec x.1 x.2) encConfigRead
      encConfig fun x => (encConfigRead x).length := by
  refine dispatch P.code (.halt []) (fun i x => i.exec x.1 x.2) (fun i => ?_) label_inSpace
  cases i with
  | assign j e next =>
    have hv := budget_prod regs_inSpace
      (budget_prod (budget_const (encB := encNat) j (.refl _)) (evalConfigRead_inSpace e))
    exact budget_prod (budget_const next (.refl _))
      (budget_comp ComputableTidilyInSpace.set hv
        (.const_mul 128 (.add hv.length_le (.const 1 _))))
  | lt x y yes no =>
    have hxy := budget_prod (evalConfigRead_inSpace x) (evalConfigRead_inSpace y)
    refine (budget_prod (budget_ite (budget_comp natLt hxy (.add hxy.length_le (.const 1 _)))
      (budget_const (encB := encNat) yes (.refl _)) (budget_const no (.refl _)))
      regs_inSpace).of_enc_eq fun s => ?_
    simp [Instr.exec]
  | read e onTrue onFalse onEnd =>
    exact budget_prod (budget_finite (readLabel onTrue onFalse onEnd) (snd _ _)) regs_inSpace
  | emit b next => exact budget_prod (budget_const next (.refl _)) regs_inSpace
  | halt out => exact fst_inSpace

end Simulation

end Computability

/-! ### Logarithmic space -/

section LogSpace

open MultiTapeTM

variable (P w)

/-- The largest label the program jumps to. -/
def maxLabel : ℕ := listMax Instr.maxLabel P.code

theorem Instr.exec_fst_le {i : Instr} (hi : i.halts = false) (s : Config) (b : Option Bool) :
    (i.exec s b).1 ≤ i.maxLabel := by
  cases i with
  | assign => exact le_rfl
  | lt x y yes no =>
    simp only [Instr.exec, Instr.maxLabel]
    split_ifs <;> omega
  | read e t f n =>
    simp only [Instr.exec, Instr.maxLabel]
    rcases b with _ | _ | _ <;> simp [readLabel]
  | emit => exact le_rfl
  | halt => simp [Instr.halts] at hi

theorem Instr.exec_snd_length (i : Instr) (s : Config) (b : Option Bool) :
    (i.exec s b).2.length = s.2.length := by
  cases i <;> simp only [Instr.exec, List.length_set]

/-- The labels of a run are bounded by the largest label of the program. -/
theorem run_fst_le (t : ℕ) : (P.run w t).1 ≤ P.maxLabel := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    rw [run_succ, step_eq]
    split_ifs with h
    · exact ih
    · have hh : (P.instr (P.run w t).1).halts = false := by simpa [halted] using h
      refine (Instr.exec_fst_le hh _ _).trans ?_
      rcases lt_or_ge (P.run w t).1 P.code.length with hlt | hge
      · rw [instr, List.getD_eq_getElem _ _ hlt]
        exact le_listMax (List.getElem_mem hlt)
      · rw [instr, List.getD_eq_default _ _ hge] at hh
        simp [Instr.halts] at hh

/-- The number of registers is fixed. -/
theorem run_snd_length (t : ℕ) : (P.run w t).2.length = P.registers := by
  induction t with
  | zero => simp [run, toQueryMachine, init]
  | succ t ih =>
    rw [run_succ, step_eq]
    split_ifs
    · exact ih
    · rw [exec, Instr.exec_snd_length, ih]

theorem Simulation.length_encConfig_le {N d : ℕ} {s : Config} (hl : s.1 ≤ P.maxLabel)
    (hn : s.2.length = P.registers) (hr : ∀ r ∈ s.2, r ≤ (N + 1) ^ d) :
    (Simulation.encConfig s).length ≤
      (2 * (encNat P.maxLabel).length + 1 + P.registers * (2 * d + 3)) * (Nat.log2 N + 1) := by
  have hL : 1 ≤ Nat.log2 N + 1 := Nat.le_add_left _ _
  have hlab := ComputableTidilyInO.length_encNat_mono hl
  have hregs :
      (encList encNat s.2).length ≤ P.registers * (2 * (d + 1) * (Nat.log2 N + 1) + 1) := by
    rw [length_encList, ← hn]
    refine (List.sum_le_length_nsmul (n := 2 * (d + 1) * (Nat.log2 N + 1) + 1) _
      fun x hx => ?_).trans (by simp)
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hx
    have := length_encNat_le_of_le_pow (hr r hr')
    nlinarith
  simp only [length_encPair]
  nlinarith

/-- **Counter programs run in logarithmic space.** Let a counter program halt on every encoded
input `enc a`, first after `time a` steps, with output `encOut (f a)`. If its registers along these
runs stay at most `(n + 1) ^ d`, where `n` is the length of the input, then `f` is computable in
logarithmic space. -/
theorem computableInLogSpace {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}
    {f : α → β} (time : α → ℕ)
    (hhalt : ∀ a, P.halted (P.run (enc a) (time a)) = true)
    (hpre : ∀ a, ∀ t < time a, P.halted (P.run (enc a) t) = false)
    (hf : ∀ a, encOut (f a) = P.toQueryMachine.output (enc a) (time a))
    (hbound : ∃ d, ∀ a, ∀ t ≤ time a, ∀ r ∈ (P.run (enc a) t).2, r ≤ ((enc a).length + 1) ^ d) :
    ComputableInLogSpace f enc encOut := by
  obtain ⟨d, hd⟩ := hbound
  exact P.toQueryMachine.computableInLogSpace (encS := Simulation.encConfig)
    (Simulation.query_inSpace (P := P)).computableInSpace
    (Simulation.exec_inSpace (P := P)).computableInSpace
    (Simulation.emitted_inSpace (P := P)).computableInSpace
    (Simulation.halted_inSpace (P := P)).computableInSpace
    (Simulation.finish_inSpace (P := P)).computableInSpace time hhalt hpre hf
    ⟨_, fun a t ht => Simulation.length_encConfig_le P (P.run_fst_le _ t) (P.run_snd_length _ t)
      (hd a t ht)⟩

/-- **Counter programs without emissions run in logarithmic space**, stated with reachability: if
on every encoded input `enc a` the program reaches a halting instruction with final word
`encOut (f a)`, passing only through assignments, comparisons and reads, and its registers stay
at most `(n + 1) ^ d` until then, where `n` is the length of the input, then `f` is computable in
logarithmic space. -/
theorem computableInLogSpace_of_reaches {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} (d : ℕ)
    (h : ∀ a, ∃ s, P.Reaches (enc a) (P.Running (((enc a).length + 1) ^ d)) P.init s ∧
      P.instr s.1 = .halt (encOut (f a)) ∧ ∀ r ∈ s.2, r ≤ ((enc a).length + 1) ^ d) :
    ComputableInLogSpace f enc encOut := by
  choose s hs using h
  choose t ht hpre using fun a => (hs a).1
  have hhalt (a : α) := (hs a).2.1
  have hreg (a : α) := (hs a).2.2
  have hrun (a : α) (u : ℕ) : P.run (enc a) u = (P.step (enc a))^[u] P.init := rfl
  have hstep (a : α) {u : ℕ} (hu : u < t a) : P.halted (P.run (enc a) u) = false := by
    have := (hpre a u hu).1
    rw [hrun, halted]
    revert this
    cases P.instr ((P.step (enc a))^[u] P.init).1 <;> simp [IsStep, Instr.halts]
  refine P.computableInLogSpace t (fun a => ?_) (fun a u hu => hstep a hu) (fun a => ?_)
    ⟨d, fun a u hu => ?_⟩
  · rw [hrun, ht, halted, hhalt]
    rfl
  · rw [P.toQueryMachine.output_eq_of_not_halted _ (fun i hi => hstep a hi)]
    have hnil : ((List.range (t a)).map fun i => P.toQueryMachine.emit
        (P.toQueryMachine.run (enc a) i,
          P.toQueryMachine.read (enc a) (P.toQueryMachine.run (enc a) i))).flatten = [] := by
      simp only [List.flatten_eq_nil_iff, List.mem_map, List.mem_range]
      rintro _ ⟨i, hi, rfl⟩
      have := (hpre a i hi).1
      simp only [toQueryMachine, emitted]
      revert this
      change (P.instr ((P.step (enc a))^[i] P.init).1).IsStep →
        (P.instr ((P.step (enc a))^[i] P.init).1).emitted = []
      cases P.instr ((P.step (enc a))^[i] P.init).1 <;> simp [IsStep, Instr.emitted]
    rw [hnil, List.nil_append]
    change _ = P.finish ((P.step (enc a))^[t a] P.init)
    rw [ht, finish, hhalt]
    rfl
  · rcases lt_or_eq_of_le hu with hlt | rfl
    · exact (hpre a u hlt).2
    · rw [hrun, ht]
      exact hreg a

end LogSpace

end CounterProgram

end Turing
