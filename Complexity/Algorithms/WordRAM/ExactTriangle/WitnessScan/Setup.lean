/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.WitnessScan.Program

/-!
# Native interval-verifier initialization

The actual header caches one original weight and computes two original row pointers. Its
numeric address bound covers every intermediate product/sum, including empty intervals at
the one-past-end boundary. These are internal rules for composing the verifier loop.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan

open Cslib.WordRAM

/-- Initialize the actual verifier in fifteen instructions, preserving the original arguments
and memory. In particular the weight is loaded from the original A–B array, not supplied as
an accepted modular candidate. -/
theorem exec_setup {W : ℕ} (A : Args) (x : Data 32) (v : ℤ)
    (hx : A.InRegisters x) (ha : A.a < A.n) (hb : A.b < A.n)
    (hc : A.first + A.length ≤ A.n)
    (hread : x.mem (A.ab + (A.a * A.n + A.b)) = Signed.encode v)
    (hfit : Fits W A.addressBound) :
    ∃ y, ExecWithin W setup x y 15 ∧ A.InRegisters y ∧ y.mem = x.mem ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.zero = 0 ∧ y.regs Reg.found = 0 ∧
      y.regs Reg.index = 0 ∧ y.regs Reg.rowB = A.bc + A.b * A.n + A.first ∧
      y.regs Reg.rowA = A.ac + A.a * A.n + A.first ∧
      y.regs Reg.wab = Signed.encode v := by
  obtain ⟨hab, hbc, hac, hn, ha', hb', hf, hl⟩ := hx
  have hstepA : A.a * A.n + A.n ≤ A.n * A.n := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right A.n (Nat.succ_le_of_lt ha)
  have hstepB : A.b * A.n + A.n ≤ A.n * A.n := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right A.n (Nat.succ_le_of_lt hb)
  have hiab : A.a * A.n + A.b < A.n * A.n := by omega
  have hrowB : A.b * A.n + A.first ≤ A.n * A.n := by omega
  have hrowA : A.a * A.n + A.first ≤ A.n * A.n := by omega
  have hmulA : A.a * A.n ≤ A.n * A.n := Nat.mul_le_mul_right _ ha.le
  have hmulB : A.b * A.n ≤ A.n * A.n := Nat.mul_le_mul_right _ hb.le
  have h1 : Fits W 1 := hfit.of_le (by unfold Args.addressBound; omega)
  have hfirst : Fits W A.first := hfit.of_le (by unfold Args.addressBound; omega)
  have hmA : Fits W (A.a * A.n) := hfit.of_le (by unfold Args.addressBound; omega)
  have hmB : Fits W (A.b * A.n) := hfit.of_le (by unfold Args.addressBound; omega)
  have hpair : Fits W (A.a * A.n + A.b) := hfit.of_le (by unfold Args.addressBound; omega)
  have hpaddr : Fits W (A.a * A.n + A.b + A.ab) :=
    hfit.of_le (by unfold Args.addressBound; omega)
  have hrB : Fits W (A.b * A.n + A.first) :=
    hfit.of_le (by unfold Args.addressBound; omega)
  have hrA : Fits W (A.a * A.n + A.first) :=
    hfit.of_le (by unfold Args.addressBound; omega)
  have hpB : Fits W (A.b * A.n + A.first + A.bc) :=
    hfit.of_le (by unfold Args.addressBound; omega)
  have hpA : Fits W (A.a * A.n + A.first + A.ac) :=
    hfit.of_le (by unfold Args.addressBound; omega)
  have hread' : x.mem (A.a * A.n + A.b + A.ab) = Signed.encode v := by
    simpa only [Nat.add_comm] using hread
  let y := x.set Reg.one 1 |>.set Reg.zero 0 |>.set Reg.found 0 |>.set Reg.index 0
    |>.set Reg.witness A.first |>.set Reg.address (A.a * A.n)
    |>.set Reg.address (A.a * A.n + A.b) |>.set Reg.address (A.a * A.n + A.b + A.ab)
    |>.set Reg.wab (Signed.encode v) |>.set Reg.rowB (A.b * A.n)
    |>.set Reg.rowB (A.b * A.n + A.first) |>.set Reg.rowB (A.b * A.n + A.first + A.bc)
    |>.set Reg.rowA (A.a * A.n) |>.set Reg.rowA (A.a * A.n + A.first)
    |>.set Reg.rowA (A.a * A.n + A.first + A.ac)
  have he : ExecWithin W setup x y 15 := by
    ram_eval [setup, y, hab, hbc, hac, hn, ha', hb', hf, hl, hread',
      h1, hfirst, hmA, hmB, hpair, hpaddr, hrA, hrB, hpA, hpB,
      Reg.one, Reg.zero, Reg.found, Reg.index, Reg.witness, Reg.address, Reg.ab, Reg.bc,
      Reg.ac, Reg.a, Reg.b, Reg.size, Reg.first, Reg.rowA, Reg.rowB, Reg.wab, Reg.length,
      Fin.mk.injEq]
  refine ⟨y, he, ?_, rfl, ?_⟩
  · simpa +decide [Args.InRegisters, y, Reg.one, Reg.zero, Reg.found, Reg.index, Reg.witness,
      Reg.address, Reg.ab, Reg.bc, Reg.ac, Reg.a, Reg.b, Reg.size, Reg.first, Reg.rowA,
      Reg.rowB, Reg.wab, Reg.length] using
      (show Args.InRegisters A x from ⟨hab, hbc, hac, hn, ha', hb', hf, hl⟩)
  · simp +decide [y, Reg.one, Reg.zero, Reg.found, Reg.index, Reg.witness, Reg.address,
      Reg.rowA, Reg.rowB, Reg.wab, Nat.add_comm, Nat.add_left_comm]

end Cslib.Algorithms.WordRAM.ExactTriangle.WitnessScan
