/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Loop
import Complexity.Computability.WordRAM.Compile

/-!
# Native prime-selector controller regressions

These execute the actual selector/trial-division controller with small explicit score programs.
The scores isolate enumeration, endpoints, minimum updates and stable ties. They are not
modular triangle counters and do not certify the missing concrete-counter instantiation.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMPrimeSelection

open Cslib.WordRAM
open Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

private abbrev p : Fin 128 := 65
private abbrev result : Fin 128 := 70
private abbrev divisor : Fin 128 := 127

private def remainderScore : Code .standard 128 := ram[
  divisor ← #5; result ← p % divisor ]

private def constantScore : Code .standard 128 := ram[ result ← #1 ]

private def runScore (D : ℕ) (score : Code .standard 128) : Code .standard 160 :=
  .seq (ram[ Reg.window ← #D; Reg.side ← #0; Reg.inputAB ← #10;
    Reg.inputBC ← #20; Reg.inputAC ← #30; Reg.scratch ← #100 ]) (program score)

-- The lower endpoint 3 belongs to the D=36 window. Prime 5 then improves its score to zero.
#guard match (runScore 36 remainderScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 5 && y.regs Reg.bestCount == 0 &&
      y.regs Reg.found == 1 && y.mem 1 == 999 && y.regs Reg.inputAB == 10
  | none => false

-- Equal scores retain the first prime, including the closed lower endpoint.
#guard match (runScore 36 constantScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 3 && y.regs Reg.bestCount == 1 && y.mem 1 == 999
  | none => false

-- D=25 excludes the prime at the open upper endpoint 5 and the candidate below sqrt(D)/2.
#guard match (runScore 25 remainderScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 3 && y.regs Reg.bestCount == 3
  | none => false

-- No admitted geometry is asserted here: an empty window leaves the explicit zero default.
#guard match (runScore 4 constantScore).eval 10 1000 (.init [999]) with
  | some (y, _) => y.regs Reg.best == 0 && y.regs Reg.found == 0 && y.mem 1 == 999
  | none => false

private def admittedEntry : Code .standard 160 :=
  .seq (ram[ Reg.window ← #16 ]) (program constantScore)

-- A fully discharged component client: actual State.init, real argument delivery and constant
-- score code, native trial/selection loop, same-y prefix/halt and the complete memory frame.
-- This proves nonvacuity of the controller rule, not a modular-counter specialization.
example : ∃ y t, t + 1 ≤ 287 ∧
    Runs 12 (admittedEntry.program Reg.best) (State.init [999]) ⟨admittedEntry.size, y⟩ t ∧
    Executes 12 (admittedEntry.program Reg.best) (State.init [999])
      (y.regs Reg.best) (t + 1) ∧ y.Bounded 12 ∧
    y.regs Reg.best ∈ Nat.sqrtPrimeWindow 16 ∧ y.regs Reg.bestCount = 1 ∧
    y.regs Reg.found = 1 ∧ y.mem 1 = 999 := by
  have hinput : InputFits 12 [999] := by decide
  let x : Data 160 := (Data.init (r := 160) [999]).set Reg.window 16
  have hsetup : ExecWithin (B := .standard) 12 (ram[ Reg.window ← #16 ])
      (Data.init (r := 160) [999]) x 1 :=
    ExecWithin.const (by decide)
  have hcount (z : Data 160) (hm : z.mem = (Data.init (r := 160) [999]).mem)
      (_ : ∀ i, 131 ≤ i.val ∧ i.val ≤ 136 → z.regs i = x.regs i)
      (_ : z.regs Reg.cursor ∈ Nat.sqrtPrimeWindow 16) :
      ∃ a, ExecWithin 12 (count constantScore) z a 7 ∧ a.regs Reg.countResult = 1 ∧
        a.mem = (Data.init (r := 160) [999]).mem := by
    let u := (((((z.set Reg.countSide (z.regs Reg.side)).set Reg.countPrime
      (z.regs Reg.cursor)).set Reg.countAB (z.regs Reg.inputAB)).set Reg.countBC
      (z.regs Reg.inputBC)).set Reg.countAC (z.regs Reg.inputAC)).set Reg.countScratch
      (z.regs Reg.scratch)
    have hdeliver : ExecWithin (B := .standard) 12
        (ram[ Reg.countSide ← Reg.side; Reg.countPrime ← Reg.cursor;
          Reg.countAB ← Reg.inputAB; Reg.countBC ← Reg.inputBC;
          Reg.countAC ← Reg.inputAC; Reg.countScratch ← Reg.scratch ]) z u 6 := by
      ram_eval [u, Reg.countSide, Reg.countPrime, Reg.countAB, Reg.countBC, Reg.countAC,
        Reg.countScratch, Reg.side, Reg.cursor, Reg.inputAB, Reg.inputBC, Reg.inputAC,
        Reg.scratch, Fin.mk.injEq]
    have htail : ExecWithin 12 (constantScore.rename counterRegisters) u
        (u.set Reg.countResult 1) 1 := by
      change ExecWithin 12 (.op (.const Reg.countResult 1)) u _ 1
      exact ExecWithin.const (by decide)
    refine ⟨u.set Reg.countResult 1, hdeliver.seq htail, ?_, hm⟩
    simp
  have htwo : 2 ∈ Nat.sqrtPrimeWindow 16 :=
    Nat.mem_sqrtPrimeWindow_iff_sq.2 ⟨by decide, by decide, by decide⟩
  obtain ⟨y, he, hf, hp, hc, _, hm, _⟩ := exec_of_count (w := 12) (D := 16) (T := 7)
    constantScore (fun _ => 1) (fun mem => mem = (Data.init (r := 160) [999]).mem) x
    (by decide) ⟨2, htwo⟩ rfl (by decide) rfl hcount
  have hsqrt : Nat.sqrt 16 = 4 := (Nat.eq_sqrt.2 ⟨by decide, by decide⟩).symm
  simp only [hsqrt, Nat.reduceAdd, Nat.reduceMul] at he
  have hall : ExecWithin 12 admittedEntry (Data.init (r := 160) [999]) y 286 := hsetup.seq he
  have hbounded : y.Bounded 12 := hall.bounded (Data.Bounded.init hinput)
  have hsentinel : y.mem 1 = 999 := congrFun hm 1
  obtain ⟨t, ht, hr⟩ := hall
  refine ⟨y, t, by omega, ?_, ?_, hbounded, hp, hc, hf, hsentinel⟩
  · simpa only [Nat.zero_add, State.init] using hr.runs (pc := 0)
      (p := admittedEntry.program Reg.best) (Program.Contains.self _).append_left
  · simpa only [State.init] using hr.executes Reg.best

end ComplexityTests.WordRAMPrimeSelection
