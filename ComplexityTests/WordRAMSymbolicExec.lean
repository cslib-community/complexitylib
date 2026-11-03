/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.ExactNotation
import Complexity.Computability.WordRAM.SymbolicExec

/-!
# Symbolic execution of structured word-RAM code

Regressions for `wram_exec` and `wram_simp`: a concrete program runs to its exact result and
instruction count; registers and memory hold symbolic values, reads after writes to other
addresses reduce, and a conditional the facts do not decide splits; execution stops at a
subprogram, continues from its specification and resumes; and goals of the wrong form, or
programs with nothing to execute, fail with an explanation. The simplification procedures
`Data.reduceRegs` and `Data.reduceMem` read through writes on their own, and `wram_bounded`
proves the fitting conditions it can.
-/

namespace ComplexityTests.WordRAMSymbolicExec

open Cslib.WordRAM

/-- Register names for the examples. -/
abbrev a : Fin 4 := 0
/-- Register names for the examples. -/
abbrev b : Fin 4 := 1
/-- Register names for the examples. -/
abbrev c : Fin 4 := 2
/-- Register names for the examples. -/
abbrev d : Fin 4 := 3

/-! ## Concrete values -/

/-- Constants, an addition, a conditional and a store. -/
def straight : Code .standard 4 := ram[
  b ← #5;
  c ← #7;
  c ← b + c;
  if b < c then [ c ← c - b ] else [ c ← #0 ];
  *b ← c ]

/-- The conditional is decided, and the bound of six instructions is exact. -/
example (x : Data 4) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 ∧ y.regs c = 7 := by
  unfold straight
  wram_exec
  wram_simp

/-- The data reached, stated in closed form. -/
example (x : Data 4) :
    ExecWithin 8 straight x (((((x.set b 5).set c 7).set c 12).set c 7).write 5 7) 6 := by
  unfold straight
  wram_exec

/-- A fitting condition that neither `simp` nor the discharger proves remains as a goal, tagged
`hfit`, after the main goal. -/
example (w : ℕ) (x : Data 4) (h : x.regs a = 3) (h7 : Fits w 7) :
    ∃ y, ExecWithin w ram[ b ← a + a ] x y 1 ∧ y.regs b = 6 := by
  wram_exec [h]
  · wram_simp
  case hfit => exact h7.of_le (by omega)

/-! ## Symbolic values -/

/-- Copy the cell at address `p` to address `p + 1`, read the cell at `p` again, and decrement it
unless it is zero, over the exact basis. -/
def shiftDecrement : Code .exact 4 := ram_exact[
  c ← a + b;
  d ← *a;
  *c ← d;
  d ← *a;
  if d < b then [ d ← b - b ] else [ d ← d - b ] ]

/-- The second read of address `p` reduces past the write at `p + 1`; the conditional on the
cell's contents splits into both alternatives. -/
example (w p : ℕ) (x : Data 4) (ha : x.regs a = p) (hb : x.regs b = 1) (hfit : Fits w (p + 1))
    (hv : Fits w (x.mem p)) :
    ∃ y, ExecWithin w shiftDecrement x y 9 ∧ y.mem (p + 1) = x.mem p ∧
      y.regs d = x.mem p - 1 := by
  unfold shiftDecrement
  wram_exec (disch := first | omega | exact hv.of_le (by omega)) [ha, hb, hfit]
  case pos => wram_simp; omega
  case neg => wram_simp

/-- A conditional decided by the given facts takes one alternative. -/
example (w p : ℕ) (x : Data 4) (ha : x.regs a = p) (hb : x.regs b = 1) (hfit : Fits w (p + 1))
    (hv : Fits w (x.mem p)) (hpos : 0 < x.mem p) :
    ∃ y, ExecWithin w shiftDecrement x y 10 ∧ y.regs d + 1 = x.mem p := by
  unfold shiftDecrement
  wram_exec (disch := first | omega | exact hv.of_le (by omega)) [ha, hb, hfit]
  wram_simp
  omega

/-- A conditional in the middle of a program. -/
def maxThenStore : Code .exact 4 := ram_exact[
  if a < b then [ c ← b ] else [ c ← a ];
  *d ← c ]

/-- `wram_exec -split` stops at the conditional, `WP.cut` joins its alternatives in one assertion,
and execution resumes once from there. -/
example (w u v q : ℕ) (x : Data 4) (ha : x.regs a = u) (hb : x.regs b = v) (hd : x.regs d = q) :
    ∃ y, ExecWithin w maxThenStore x y 4 ∧ y.mem q = max u v := by
  unfold maxThenStore
  wram_exec -split [ha, hb, hd]
  refine WP.cut (fun y t => t ≤ 3 ∧ y.regs c = max u v ∧ y.regs d = q) ?_
    fun y t ⟨ht, hc, hd'⟩ => ?_
  · wram_exec [ha, hb, hd]
    all_goals refine ⟨?_, by wram_simp [hd]⟩
    case pos => wram_simp [hb]; omega
    case neg => wram_simp [ha]; omega
  · wram_exec [hc, hd']
    wram_simp

/-! ## Subprograms -/

/-- A subprogram, with its own specification. -/
def double : Code .standard 4 := ram[ b ← a + a ]

theorem double_spec {w : ℕ} {x : Data 4} (h : Fits w (x.regs a + x.regs a)) :
    ExecWithin w double x (x.set b (x.regs a + x.regs a)) 1 :=
  ExecWithin.bin h

/-- A program calling the subprogram. -/
def callDouble : Code .standard 4 := ram[ a ← #3; ⟪double⟫; c ← b ]

/-- Execution stops at the subprogram, continues from its specification, and resumes. -/
example (x : Data 4) : ∃ y, ExecWithin 8 callDouble x y 3 ∧ y.regs c = 6 := by
  unfold callDouble
  wram_exec
  refine WP.of_execWithin (double_spec (by wram_simp; decide)) ?_
  wram_exec
  wram_simp

/-- At a stop, `WP.name` names the data reached for the hypotheses of a specification;
`wram_bounded` shows it word-sized, and `WP.bounded` lets the postcondition assume that the final
data is. -/
example (x : Data 4) (hx : x.Bounded 8) :
    ∃ y, ExecWithin 8 callDouble x y 3 ∧ (y.Bounded 8 → y.regs c = 6) := by
  unfold callDouble
  wram_exec
  refine WP.name fun y hy => ?_
  have hyb : y.Bounded 8 := by rw [hy]; wram_bounded; decide
  refine WP.of_execWithin (double_spec (by rw [hy]; wram_simp; decide)) (WP.bounded ?_ ?_)
  · exact hyb.set (by rw [hy]; wram_simp; decide)
  · wram_exec
    exact fun _ => ⟨by omega, fun _ => by wram_simp [hy]⟩

/-! ## Reads and word bounds -/

/-- A register name given as `⟨k, _⟩`, as in larger programs. -/
abbrev e : Fin 8 := ⟨5, by decide⟩

/-- `Data.reduceRegs` reads past other registers and a memory write, comparing register names by
evaluation, whether literals or abbreviations. -/
example (x : Data 8) (p : ℕ) : ((((x.set e 1).write p 3).set 6 2).set 7 4).regs e = 1 := by
  simp only [↓Data.reduceRegs]

/-- `Data.reduceMem` reads a cell written at an address that is a different term, which the
discharger proves equal, past a register. -/
example (x : Data 4) (p : ℕ) : ((x.write (p + 1) 7).set a 0).mem (1 + p) = 7 := by
  wram_simp

/-- `Data.reduceMem` leaves a read whose address the discharger cannot compare. -/
example (x : Data 4) (p q : ℕ) (h : (x.write p 7).mem q = 0) :
    ((x.write p 7).set a 0).mem q = 0 := by
  simp only [Data.reduceMem]
  exact h

/-- `wram_bounded` proves the fitting conditions of values read from the data and of values with a
hypothesis. -/
example (w p : ℕ) (x : Data 4) (hx : x.Bounded w) (hp : Fits w p) :
    (((x.set a (x.regs b)).write p (x.mem 3)).set c p).Bounded w := by
  wram_bounded

/-! ## Failures -/

/-- error: wram_exec: nothing to execute in
  WP 8 callDouble x fun y t => t ≤ 3 ∧ y.regs c = 6
The program starts with a loop, a random sample or a program given by name. Apply its
specification with `WP.of_execWithin`, or unfold it. -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : ∃ y, ExecWithin 8 callDouble x y 3 ∧ y.regs c = 6 := by
  wram_exec

/-- error: wram_exec: expected a goal `WP w c x Q`, `∃ y, ExecWithin w c x y T ∧ P y`,
`ExecWithin w c x y T` or `∃ y T, ExecWithin w c x y T ∧ Q y T`, got
  (x.set c 7).regs c = 7 -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : (x.set c 7).regs c = 7 := by
  wram_exec

/-- error: wram_exec: unknown option; the only option is `-split` -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 := by
  wram_exec +decide

end ComplexityTests.WordRAMSymbolicExec
