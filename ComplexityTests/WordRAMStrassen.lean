/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Leaf
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.Initialize
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Strassen.LeafStep

/-!
# Native explicit-stack Strassen execution regressions

These run actual finite native code. They check signed scalar leaves, all seven products at
positive depth, and a two-level cyclic-coefficient matrix with dirty scratch. They do not
replace the general execution or resource proof, and do not claim a complete triangle counter.
-/

-- These commands deliberately execute the real standard WordRAM interpreter.
set_option linter.hashCommand false

namespace ComplexityTests.WordRAMStrassen

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.Strassen

private def arguments (a b out scratch p depth : ℕ) : Code .standard 64 := ram[
  Reg.inputA ← #a; Reg.inputB ← #b; Reg.output ← #out; Reg.scratch ← #scratch;
  Reg.modulus ← #p; Reg.depth ← #depth ]

private def complete (a b out scratch p depth : ℕ) : Code .standard 64 :=
  .seq (arguments a b out scratch p depth) program

-- All seven child products contribute, with negative intermediate values and dirty output.
-- [-1 2; 3 -4] [5 -6; 7 8] = [9 22; -13 -50].
#guard match (complete 1 5 9 13 1 1).eval 16 10000
    (.init ([3, 4, 6, 9, 10, 13, 14, 16] ++ List.replicate 30 99 ++ [123])) with
  | some (y, _) => y.mem 9 == encode 9 && y.mem 10 == encode 22 &&
      y.mem 11 == encode (-13) && y.mem 12 == encode (-50) &&
      y.mem 1 == 3 && y.mem 8 == 16 && y.mem 39 == 123 && y.regs Reg.active == 0
  | none => false

-- The depth-zero path still uses actual cyclic coefficient multiplication.
#guard match (complete 1 4 7 10 3 0).eval 16 2000
    (.init ([2, 5, 6, 9, 10, 4] ++ List.replicate 14 99 ++ [123])) with
  | some (y, _) => y.mem 7 == encode 7 && y.mem 8 == encode 19 &&
      y.mem 9 == encode (-20) && y.mem 21 == 123 && y.regs Reg.active == 0
  | none => false

private def matrixA : List ℕ := (List.range 32).map fun i => encode ((i : ℤ) - 17)

private def identityB : List ℕ := (List.range 32).map fun i =>
  if i % 2 = 0 ∧ i / 2 ∈ [0, 3, 12, 15] then encode 1 else 0

-- The Morton-ordered 4×4 identity over Z[X]/(X²-1) leaves all 32 signed coefficients intact.
-- Both recursion levels, frame reuse, all operand-copy cases and canonical cancellations run.
#guard match (complete 1 33 65 97 2 2).eval 24 200000
    (.init (matrixA ++ identityB ++ List.replicate 100 99 ++ [123])) with
  | some (y, _) => (List.range 32).all (fun i =>
      y.mem (65 + i) == matrixA[i]! && y.mem (1 + i) == matrixA[i]!) &&
      y.mem 165 == 123 && y.regs Reg.active == 0
  | none => false

private def leafArguments : Code .standard 64 := ram[
  Reg.inputA ← #1; Reg.inputB ← #2; Reg.output ← #3; Reg.modulus ← #1;
  Reg.frame ← #10; Reg.frames ← #10; Reg.frameWidth ← #7; Reg.active ← #1 ]

private def leafRun : Code .standard 64 := .seq leafArguments leaf

private def leafInput : List ℕ := [7, 4, 99, 123]

-- A kernel-checked native ABI seam: the same actual initialized prefix/halting state
-- contains the signed result and sentinel, and the root return clears the real active flag.
example : InputFits 10 leafInput ∧ ∃ y t, t + 1 ≤ 71 ∧
    Runs 10 (leafRun.program Reg.output) (State.init leafInput) ⟨leafRun.size, y⟩ t ∧
    Executes 10 (leafRun.program Reg.output) (State.init leafInput) 3 (t + 1) ∧
    y.Bounded 10 ∧ y.mem 3 = encode (-6) ∧ y.mem 4 = 123 ∧ y.regs Reg.active = 0 := by
  have hi : InputFits 10 leafInput := by decide
  let x₀ := (((Data.init leafInput).set Reg.inputA 1).set Reg.inputB 2).set Reg.output 3
  let x := ((((x₀.set Reg.modulus 1).set Reg.frame 10).set Reg.frames 10).set
    Reg.frameWidth 7).set Reg.active 1
  have ha : ExecWithin 10 leafArguments (.init leafInput) x 8 := by
    ram_eval [leafArguments, x, x₀, Reg.inputA, Reg.inputB, Reg.output, Reg.modulus,
      Reg.frame, Reg.frames, Reg.frameWidth, Reg.active]
  obtain ⟨y, hy, hv, hf, _, hflag, hr⟩ := exec_leaf (w := 8) (p := 1) (A := 3) (B := 2)
    x (fun _ => -3) (fun _ => 2) (by decide) (by decide)
    (by intro i hi'; decide) (by intro i hi'; decide)
    (by
      intro i hi'
      obtain rfl : i = 0 := by omega
      decide)
    (by
      intro i hi'
      obtain rfl : i = 0 := by omega
      decide)
    (by decide) (by decide) (by decide) (by decide)
    (Or.inl (by decide)) (Or.inl (by decide)) (by decide) (by decide)
  have he : ExecWithin 10 leafRun (.init leafInput) y 70 := ha.seq hy
  have hp : y.regs Reg.output = 3 := (hr Reg.output (by decide) (by decide) (by decide)).trans
    (by decide)
  have hxout : x.regs Reg.output = 3 := by decide
  have hvalue : y.mem 3 = encode (-6) := by
    simpa only [hxout, Nat.add_zero, show Cslib.CyclicIntRing.convolution 1
      (fun _ => -3) (fun _ => 2) 0 = -6 from by decide] using hv 0 (by decide)
  have hsentinel : y.mem 4 = 123 := (hf 4 (Or.inr (by decide))).trans (by decide)
  have hactive : y.regs Reg.active = 0 := by
    simpa only [show x.regs Reg.frames = 10 from by decide,
      show x.regs Reg.frame = 10 from by decide, Nat.lt_irrefl, ite_false] using hflag
  have hyb : y.Bounded 10 := he.bounded (Data.Bounded.init hi)
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, y, t, by omega, ?_, ?_, hyb,
    hvalue, hsentinel, hactive⟩
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := leafRun.program Reg.output) (Program.Contains.self _).append_left
  · simpa only [State.init, hp] using hex.executes Reg.output

-- The complete fixed controller also has a fully admitted initialized scalar execution:
-- actual Power call, computed frame placement, all frame stores/loads, depth dispatch,
-- coefficient computation, root return, loop exit and halt refer to the same state.
example : ∃ y t, t + 1 ≤ 118 ∧
    Runs 10 ((complete 1 2 3 10 1 0).program Reg.output) (State.init leafInput)
      ⟨(complete 1 2 3 10 1 0).size, y⟩ t ∧
    Executes 10 ((complete 1 2 3 10 1 0).program Reg.output) (State.init leafInput) 3 (t + 1) ∧
    y.Bounded 10 ∧ y.mem 3 = encode (-6) ∧ y.mem 4 = 123 := by
  let x₀ := (((Data.init leafInput).set Reg.inputA 1).set Reg.inputB 2).set Reg.output 3
  let x := ((x₀.set Reg.scratch 10).set Reg.modulus 1).set Reg.depth 0
  have hargs : ExecWithin 10 (arguments 1 2 3 10 1 0) (.init leafInput) x 6 := by
    ram_eval [arguments, x, x₀, Reg.inputA, Reg.inputB, Reg.output,
      Reg.scratch, Reg.modulus, Reg.depth]
  obtain ⟨s, hs, _, hsframes, hsframe, _, hsactive, hszero, hsone, _, hswidth,
    hsparams, hsfields, hsmem⟩ := exec_setup (w := 10) x (by decide)
  have hsa : s.regs Reg.inputA = 1 := (hsparams Reg.inputA (by decide)).trans (by decide)
  have hsb : s.regs Reg.inputB = 2 := (hsparams Reg.inputB (by decide)).trans (by decide)
  have hso : s.regs Reg.output = 3 := (hsparams Reg.output (by decide)).trans (by decide)
  have hsp : s.regs Reg.modulus = 1 := (hsparams Reg.modulus (by decide)).trans (by decide)
  have hsd : s.regs Reg.depth = 0 := (hsparams Reg.depth (by decide)).trans (by decide)
  have hsf : s.regs Reg.frame = 11 := by
    rw [hsframe, hsframes]
    decide
  have hsm (a : ℕ) (ha : a < 11) : s.mem a = x.mem a :=
    hsmem a (Or.inl (by simpa only [hsf] using ha))
  obtain ⟨y, hy, values, frame, _, hyactive, hyregs⟩ := exec_step_leaf
    (w := 8) (p := 1) (A := 3) (B := 2) s (fun _ => -3) (fun _ => 2)
    hszero hsone hswidth hsd hsfields (by rw [hsf]; decide) hsp
    (by decide) (by intro i hi; decide) (by intro i hi; decide)
    (by
      intro i hi
      obtain rfl : i = 0 := by omega
      rw [hsa, Nat.add_zero, hsm 1 (by decide)]
      decide)
    (by
      intro i hi
      obtain rfl : i = 0 := by omega
      rw [hsb, Nat.add_zero, hsm 2 (by decide)]
      decide)
    (by decide) (by rw [hsa]; decide) (by rw [hsb]; decide) (by rw [hso]; decide)
    (Or.inl (by omega)) (Or.inl (by omega))
  have hy0 : y.regs Reg.zero = 0 :=
    (hyregs Reg.zero (by decide) (by decide) (by decide) (by decide)).trans hszero
  have hyflag : y.regs Reg.active = 0 := by
    simpa only [hsframe, Nat.lt_irrefl, ite_false] using hyactive
  have hloop : ExecWithin 10 (.loop (.lt Reg.zero Reg.active) step) s y 81 := by
    have hexit : ExecWithin 10 (.loop (.lt Reg.zero Reg.active) step) y y 2 :=
      .loop_exit (by simp only [Cond.holds_lt, hy0, hyflag, Nat.lt_irrefl, not_false_eq_true])
    exact .loop_iter (by simp only [Cond.holds_lt, hszero, hsactive]; decide) hy hexit
  have he : ExecWithin 10 (complete 1 2 3 10 1 0) (.init leafInput) y 117 :=
    hargs.seq (hs.seq hloop)
  have hyout : y.regs Reg.output = 3 :=
    (hyregs Reg.output (by decide) (by decide) (by decide) (by decide)).trans hso
  have hvalue : y.mem 3 = encode (-6) := by
    simpa only [hso, Nat.add_zero, show Cslib.CyclicIntRing.convolution 1
      (fun _ => -3) (fun _ => 2) 0 = -6 from by decide] using values 0 (by decide)
  have hsentinel : y.mem 4 = 123 :=
    (frame 4 (Or.inr (by omega))).trans ((hsm 4 (by decide)).trans (by decide))
  have hyb := he.bounded (Data.Bounded.init (show InputFits 10 leafInput from by decide))
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨y, t, by omega, ?_, ?_, hyb, hvalue, hsentinel⟩
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := (complete 1 2 3 10 1 0).program Reg.output) (Program.Contains.self _).append_left
  · simpa only [State.init, hyout] using hex.executes Reg.output

end ComplexityTests.WordRAMStrassen
