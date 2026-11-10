/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.ExactNotation
import CslibFrontier.Computability.WordRAM.SymbolicExec

/-!
# Symbolic execution of structured word-RAM code

Regressions for `wram_exec` and `wram_simp`: a concrete program runs to its exact result and
instruction count; registers and memory hold symbolic values, reads after writes to other
addresses reduce, and a conditional the facts do not decide splits; instructions `Op.alu` of other
bases, such as `Basis.additive`, run too; execution stops at a subprogram, continues from its
specification and resumes; and goals of the wrong form, or programs with nothing to execute, fail
with an explanation. The simplification procedures `Data.reduceRegs` and `Data.reduceMem` read
through writes on their own, also with register names that have free variables and banks separated
by quantified hypotheses, `Data.reduceWriteMem` unfolds memory that is not read at an address, and
`wram_bounded` proves the fitting conditions it can.
-/

namespace CslibFrontierTests.WordRAMSymbolicExec

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
example (w : ℕ) (x : Data 4) (h : x.regs a = 3) (h7 : 7 ≤ w) :
    ∃ y, ExecWithin w ram[ b ← a + a ] x y 1 ∧ y.regs b = 6 := by
  wram_exec [h]
  · wram_simp
  case hfit => exact (fits_self w).of_le (by omega)

/-- The default discharger proves a fitting condition from the word-size facts in context with
`fits`. -/
example (w : ℕ) (x : Data 4) (h : x.regs a = 3) (h7 : Fits w 7) :
    ∃ y, ExecWithin w ram[ b ← a + a ] x y 1 ∧ y.regs b = 6 := by
  wram_exec [h]
  wram_simp

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
  wram_exec [ha, hb, hfit]
  case pos => wram_simp; omega
  case neg => wram_simp

/-- A conditional decided by the given facts takes one alternative. -/
example (w p : ℕ) (x : Data 4) (ha : x.regs a = p) (hb : x.regs b = 1) (hfit : Fits w (p + 1))
    (hv : Fits w (x.mem p)) (hpos : 0 < x.mem p) :
    ∃ y, ExecWithin w shiftDecrement x y 10 ∧ y.regs d + 1 = x.mem p := by
  unfold shiftDecrement
  wram_exec [ha, hb, hfit]
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

/-! ## Other bases -/

/-- Addition and truncated subtraction over `Basis.additive`: instructions `Op.alu` of a basis given
by a definition. -/
def addSub : Code .additive 4 :=
  .seq (.op (.addAdditive c a b)) (.op (.alu ⟨.bin .sub, by decide⟩ a ![c, b]))

/-- `WP.alu` evaluates the operation on the values read (`Basis.reduceInterp`); the fitting
conditions are hypotheses. -/
example (w u v : ℕ) (x : Data 4) (ha : x.regs a = u) (hb : x.regs b = v) (huv : Fits w (u + v))
    (hu : Fits w u) :
    ∃ y, ExecWithin w addSub x y 2 ∧ y.regs a = u ∧ y.regs c = u + v := by
  unfold addSub
  wram_exec [ha, hb]
  wram_simp

/-- An instruction `Op.alu` of the standard basis, written with the constructor. -/
example (w u v : ℕ) (x : Data 4) (ha : x.regs a = u) (hb : x.regs b = v) (h : Fits w (u * v)) :
    ∃ y, ExecWithin w (.op (.alu (B := .standard) (.bin .mul) c ![a, b])) x y 1 ∧
      y.regs c = u * v := by
  wram_exec [ha, hb]
  wram_simp

-- Exact subtraction written as `Op.alu`: its value depends on comparing the operands, so it does
-- not unfold to `some v`; `Op.exactBin` instructions have their own rules.
/-- error: wram_exec: could not evaluate
  Basis.exact.interp 8 (StandardOp.bin BinOp.sub) fun a => x.regs (![WordRAMSymbolicExec.a, b] a)
It simplifies to
  StandardOp.evalExact 8 (StandardOp.bin BinOp.sub) fun a => x.regs (![WordRAMSymbolicExec.a, b] a)
which does not have the form
  some ?v -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) (ha : x.regs a = 2) (hb : x.regs b = 1) :
    ∃ y, ExecWithin 8 (.op (.alu (B := .exact) (.bin .sub) c ![a, b])) x y 1 ∧ y.regs c = 1 := by
  wram_exec [ha, hb]

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

/-- Memory that is not read at an address becomes `Function.update` (`Data.reduceWriteMem`), while a
read the discharger cannot decide keeps its form. -/
example (x : Data 4) (p q : ℕ) (P : (ℕ → ℕ) → Prop) (hP : P (Function.update x.mem p 7))
    (hq : (x.write p 7).mem q = 0) :
    P ((x.write p 7).set a 0).mem ∧ ((x.write p 7).set a 0).mem q = 0 := by
  wram_simp
  guard_target =ₛ P (Function.update x.mem p 7) ∧ (x.write p 7).mem q = 0
  exact ⟨hP, hq⟩

/-- Register names with free variables: a hypothesis `i ≠ j` in either direction, a register
outside the range of a renaming `f`, and renamed registers of an injective `f`. -/
example {r s : ℕ} (x : Data s) (f : Fin r → Fin s) (hf : f.Injective) (i j : Fin r) (k : Fin s)
    (hij : i ≠ j) (hk : k ∉ Set.range f) :
    (((x.set (f i) 1).set (f j) 2).set k 3).regs (f i) = 1 ∧
      (((x.set (f i) 1).set (f j) 2).set k 3).regs (f j) = 2 ∧
      (((x.set k 3).set (f i) 1).set (f j) 2).regs k = 3 := by
  wram_simp

/-- A hypothesis `¬i = j`, as `by_cases` gives it, separates names too. -/
example {r : ℕ} (x : Data r) (i j : Fin r) (h : ¬i = j) : (x.set j 1).regs i = x.regs i := by
  wram_simp

/-- Renamed registers of an injective `f` whose arguments are literals. -/
example {s : ℕ} (x : Data s) (f : Fin 3 → Fin s) (hf : f.Injective) :
    ((x.set (f 0) 1).set (f 1) 2).regs (f 2) = x.regs (f 2) := by
  wram_simp

/-- Register names that unfold to `⟨k, _⟩` are compared by the discharger on their values. -/
example {r : ℕ} (x : Data (r + 3)) (i : Fin r) :
    ((x.set (i.castAdd 3) 5).set ⟨r + 1, by omega⟩ 6).regs (i.castAdd 3) = 5 := by
  wram_simp

/-- A literal register name is compared with a name that unfolds to `⟨k, _⟩` by its value, as for a
bank `⟨20 + m % 54, _⟩` next to scratch registers `10` and `11`. -/
example (x : Data 240) (m : ℕ) :
    (((x.set 10 5).set ⟨20 + m % 54, by omega⟩ 6).set 11 7).regs ⟨20 + (m + 1) % 54, by omega⟩ =
      x.regs ⟨20 + (m + 1) % 54, by omega⟩ := by
  wram_simp

/-- Names the procedure cannot compare are left: a read of `j` after setting `i`. -/
example {r : ℕ} (x : Data r) (i j : Fin r) (p : ℕ) (h : (x.set i 1).regs j = 0) :
    ((x.set i 1).write p 2).regs j = 0 := by
  wram_simp
  guard_target =ₛ (x.set i 1).regs j = 0
  exact h

/-- A renamed bank, as an inline call copies arguments into a subprogram's registers: the copies
read a register outside the range of the renaming, and the arguments read back. -/
example {r s : ℕ} (w : ℕ) (x : Data s) (f : Fin r → Fin s) (hf : f.Injective) (t₁ t₂ : Fin r)
    (z : Fin s) (ht : t₂ ≠ t₁) (hz : z ∉ Set.range f) (hz0 : x.regs z = 0) :
    ∃ y, ExecWithin (B := .standard) w (.seq (.op (.copy (f t₂) z)) (.op (.copy (f t₁) z))) x y 2 ∧
      y.regs (f t₂) = 0 ∧ y.regs (f t₁) = 0 ∧ y.regs z = 0 := by
  wram_exec [hz0]
  wram_simp [hz0]

/-- Two renamed banks separated by quantified hypotheses, as a call copies its arguments `src` into
scratch registers `tmp`: the instances `src 4 ≠ tmp 9` and `frontier ≠ tmp 2`, also stated as
`¬tmp j = frontier`, read past the copies. -/
example {r : ℕ} (w : ℕ) (x : Data r) (src : Fin 5 → Fin r) (tmp : Fin 10 → Fin r)
    (frontier : Fin r) (hi : tmp.Injective) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, ¬tmp j = frontier) :
    ∃ y, ExecWithin (B := .standard) w
        (.seq (.op (.copy (tmp 2) (src 4))) (.op (.copy (tmp 9) (src 3)))) x y 2 ∧
      y.regs (src 4) = x.regs (src 4) ∧ y.regs frontier = x.regs frontier ∧
      y.regs (tmp 2) = x.regs (src 4) := by
  wram_exec
  wram_simp

/-- A quantified hypothesis with a premise is not instantiated: the read past `set` stays. -/
example {r : ℕ} (x : Data r) (tmp : Fin 10 → Fin r) (_hne : ∀ i j, i ≠ j → tmp i ≠ tmp j)
    (p : ℕ) (h : (x.set (tmp 1) 5).regs (tmp 2) = 0) :
    ((x.set (tmp 1) 5).write p 2).regs (tmp 2) = 0 := by
  wram_simp
  guard_target =ₛ (x.set (tmp 1) 5).regs (tmp 2) = 0
  exact h

/-- `Data.set_set`: setting a register twice keeps the second value. -/
example (x : Data 4) : ExecWithin (B := .standard) 8 ram[ c ← #1; c ← #2 ] x (x.set c 2) 2 := by
  wram_exec
  exact Data.set_set x c 1 2

/-- `wram_bounded` proves the fitting conditions of values read from the data and of values with a
hypothesis. -/
example (w p : ℕ) (x : Data 4) (hx : x.Bounded w) (hp : Fits w p) :
    (((x.set a (x.regs b)).write p (x.mem 3)).set c p).Bounded w := by
  wram_bounded

/-! ## Exact instruction counts -/

/-- The exact count of six instructions, and the data reached, from `Exec`. -/
example (x : Data 4) :
    Exec 8 straight x (((((x.set b 5).set c 7).set c 12).set c 7).write 5 7) 6 := by
  unfold straight
  wram_exec

/-- The exact count with a property of the data reached. -/
example (x : Data 4) : ∃ y, Exec 8 straight x y 6 ∧ y.mem 5 = 7 ∧ y.regs c = 7 := by
  unfold straight
  wram_exec
  wram_simp

/-- A wrong exact count remains as a goal: the program takes six instructions, not seven. -/
example (x : Data 4) (h : (6 : ℕ) = 7) : ∃ y, Exec 8 straight x y 7 ∧ y.mem 5 = 7 := by
  unfold straight
  wram_exec
  exact ⟨h, by wram_simp⟩

/-- Both alternatives of a conditional, with their own exact counts; side conditions with free
variables go to the discharger. -/
example (w p : ℕ) (x : Data 4) (ha : x.regs a = p) (hb : x.regs b = 1) (hfit : Fits w (p + 1))
    (hv : Fits w (x.mem p)) :
    ∃ y, Exec w shiftDecrement x y (if x.mem p < 1 then 6 else 7) ∧
      y.mem (p + 1) = x.mem p := by
  unfold shiftDecrement
  wram_exec [ha, hb, hfit]
  case pos => exact ⟨by simp [hc], by wram_simp⟩
  case neg => exact ⟨by simp [hc], by wram_simp⟩

/-- An exact specification of the subprogram. -/
theorem double_exec {w : ℕ} {x : Data 4} (h : Fits w (x.regs a + x.regs a)) :
    Exec w double x (x.set b (x.regs a + x.regs a)) 1 :=
  Exec.bin h

/-- Execution stops at the subprogram, continues from its exact specification, and resumes. -/
example (x : Data 4) : ∃ y, Exec 8 callDouble x y 3 ∧ y.regs c = 6 := by
  unfold callDouble
  wram_exec
  refine WP.Exact.of_exec (double_exec (by wram_simp; decide)) ?_
  wram_exec
  wram_simp

/-- Instructions `Op.alu` with an exact count (`WP.Exact.alu`), over `Basis.additive`, where the
operation is evaluated by `Basis.reduceInterp`, and over the standard basis. -/
example (w u v : ℕ) (x : Data 4) (ha : x.regs a = u) (hb : x.regs b = v) (huv : Fits w (u + v))
    (hu : Fits w u) :
    ∃ y, Exec w addSub x y 2 ∧ y.regs a = u ∧ y.regs c = u + v := by
  unfold addSub
  wram_exec [ha, hb]
  wram_simp

example (w u v : ℕ) (x : Data 4) (ha : x.regs a = u) (hb : x.regs b = v) (h : Fits w (u * v)) :
    ∃ y, Exec w (.op (.alu (B := .standard) (.bin .mul) c ![a, b])) x y 1 ∧ y.regs c = u * v := by
  wram_exec [ha, hb]
  wram_simp

/-- An exact count is a bound: `WP.Exact.toWP` turns an exact goal into a bounded one. -/
example (x : Data 4) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 :=
  WP.exists_execWithin <| WP.Exact.toWP <| by
    unfold straight
    wram_exec
    wram_simp

/-! ## Failures -/

/-- error: wram_exec: nothing to execute in
  WP 8 callDouble x fun y t => t ≤ 3 ∧ y.regs c = 6
The program starts with a loop, a random sample or a program given by name. Apply its
specification with `WP.of_execWithin`, or unfold it. -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : ∃ y, ExecWithin 8 callDouble x y 3 ∧ y.regs c = 6 := by
  wram_exec

/-- error: wram_exec: expected a goal `WP w c x Q`, `∃ y, ExecWithin w c x y T ∧ P y`,
`ExecWithin w c x y T` or `∃ y T, ExecWithin w c x y T ∧ Q y T`, or one of these with `Exec`
and `WP.Exact`, got
  (x.set c 7).regs c = 7 -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : (x.set c 7).regs c = 7 := by
  wram_exec

/-- error: wram_exec: unknown option; the only option is `-split` -/
#guard_msgs (whitespace := lax) in
example (x : Data 4) : ∃ y, ExecWithin 8 straight x y 6 ∧ y.mem 5 = 7 := by
  wram_exec +decide

end CslibFrontierTests.WordRAMSymbolicExec
