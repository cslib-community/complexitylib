/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Program

/-!
# Exact physical input and answer words

The callable compiler relates clipped memory to source memory. Two actual in-place span loops
make the restored input and returned answers exact physical words. These are internal execution
interfaces; both loops charge their setup, address calculations, remainders and stores.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct

open Cslib.WordRAM

private theorem normalizeBank_injective : Function.Injective normalizeBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 163 => k.val) h)

private theorem exec_normalizeBank {W b n M : ℕ} (x : Data 163)
    (hb : x.regs Reg.result = b) (hn : x.regs Reg.second = n)
    (hm : x.regs Reg.third = M) (hM : 0 < M) (hfit : Fits W (b + n + M + 2)) :
    ∃ y, ExecWithin W (ArrayNormalize.program.rename normalizeBank) x y (7 * n + 4) ∧
      y.mem = ArrayNormalize.normalizePrefix x.mem b M n ∧ y.regs Reg.result = b ∧
      ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := by
  obtain ⟨a, ha, am, ab, an, aM⟩ := ArrayNormalize.exec (x.comap normalizeBank) hb hn hm hM hfit
  refine ⟨a.extend normalizeBank x, ha.rename normalizeBank_injective, am,
    (normalizeBank_injective.extend_apply _ _ ArrayNormalize.base).trans ab, ?_⟩
  intro i hi
  have hnot : ¬∃ j, normalizeBank j = i := by
    rintro ⟨j, hj⟩
    have h := congrArg (fun k : Fin 163 => k.val) hj
    change j.val = i.val at h
    omega
  exact Function.extend_apply' _ _ _ hnot

/-- Normalize precisely the local original input; high product/caller registers survive. -/
theorem exec_restoreInput {W b n M : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (hn : x.regs Reg.inputSize = n) (hm : x.regs Reg.modulus = M) (hM : 0 < M)
    (hfit : Fits W (b + n + M + 2)) :
    ∃ y, ExecWithin W restoreInput x y (7 * n + 7) ∧
      y.mem = ArrayNormalize.normalizePrefix x.mem b M n ∧
      ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := by
  let z := ((x.set Reg.result b).set Reg.second n).set Reg.third M
  have hz : ExecWithin (B := .standard) W
      (ram[ Reg.result ← Reg.base; Reg.second ← Reg.inputSize;
        Reg.third ← Reg.modulus ]) x z 3 := by
    ram_eval [z, hb, hn, hm, Reg.result, Reg.second, Reg.third, Reg.base, Reg.inputSize,
      Reg.modulus, QueriedProduct.inputSize, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yr, yh⟩ := exec_normalizeBank (W := W) (b := b) (n := n) (M := M) z
    (by simp [z, Reg.result, Reg.second, Reg.third])
    (by simp [z, Reg.second, Reg.third]) (by simp [z]) hM hfit
  refine ⟨y, (hz.seq hy).mono (by omega), ym, ?_⟩
  intro i hi
  rw [yh i hi]
  have h0 : i ≠ Reg.result := by intro h; subst i; simp [Reg.result] at hi
  have h1 : i ≠ Reg.second := by intro h; subst i; simp [Reg.second] at hi
  have h2 : i ≠ Reg.third := by intro h; subst i; simp [Reg.third] at hi
  simp only [z, Data.set_regs, Function.update_of_ne h0, Function.update_of_ne h1,
    Function.update_of_ne h2]

/-- Normalize the answer span, preserving all high registers, and return its absolute pointer. -/
theorem exec_returnOutput {W b o n M : ℕ} (x : Data 163) (hb : x.regs Reg.base = b)
    (ho : x.regs Reg.output = o) (hn : x.regs Reg.queryCount = n)
    (hm : x.regs Reg.modulus = M) (hM : 0 < M) (hfit : Fits W (b + o + n + M + 2)) :
    ∃ y, ExecWithin W returnOutput x y (7 * n + 7) ∧
      y.mem = ArrayNormalize.normalizePrefix x.mem (b + o) M n ∧
      y.regs Reg.result = b + o ∧
      ∀ i : Fin 163, 7 ≤ i.val → y.regs i = x.regs i := by
  have haddr : Fits W (b + o) := hfit.of_le (by omega)
  let z := ((x.set Reg.result (b + o)).set Reg.second n).set Reg.third M
  have hz : ExecWithin W
      (ram[ Reg.result ← Reg.base + Reg.output;
        Reg.second ← Reg.queryCount; Reg.third ← Reg.modulus ]) x z 3 := by
    ram_eval [z, hb, ho, hn, hm, haddr, Reg.result, Reg.second, Reg.third, Reg.base,
      Reg.output, Reg.queryCount, Reg.modulus, QueriedProduct.output,
      QueriedProduct.queryCount, Fin.mk.injEq]
  obtain ⟨y, hy, ym, yr, yh⟩ :=
    exec_normalizeBank (W := W) (b := b + o) (n := n) (M := M) z
    (by simp [z, Reg.result, Reg.second, Reg.third])
    (by simp [z, Reg.second, Reg.third]) (by simp [z]) hM (by
      simpa only [Nat.add_assoc] using hfit)
  refine ⟨y, (hz.seq hy).mono (by omega), ym, yr, ?_⟩
  intro i hi
  rw [yh i hi]
  have h0 : i ≠ Reg.result := by intro h; subst i; simp [Reg.result] at hi
  have h1 : i ≠ Reg.second := by intro h; subst i; simp [Reg.second] at hi
  have h2 : i ≠ Reg.third := by intro h; subst i; simp [Reg.third] at hi
  simp only [z, Data.set_regs, Function.update_of_ne h0, Function.update_of_ne h1,
    Function.update_of_ne h2]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.CallableProduct
