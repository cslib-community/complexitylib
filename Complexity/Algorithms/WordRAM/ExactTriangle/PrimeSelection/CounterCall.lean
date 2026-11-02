/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.Exec

/-!
# Actual modular counting inside the selector register bank

Six real copies deliver the original side, current prime, matrix pointers and workspace to
the complete native counter. The entire counter runs in its low 128-register bank. This
rule composes its actual execution and memory frame; it assumes no counter answer, run,
layout, multiplication or time contract.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM Cslib.WordRAM.Signed

/-- Execute the real counter, including argument delivery, from original signed arrays and
numerical admission. Sources may alias below scratch; the scratch region may be dirty.
Selector metadata is outside the low counter bank. -/
theorem exec_count {w n p scratch a b c A : ℕ} (x : Data 160) (u v z : ℕ → ℤ)
    (hp0 : 0 < p) (hn : x.regs Reg.side = n) (hp : x.regs Reg.cursor = p)
    (hAB : x.regs Reg.inputAB = a) (hBC : x.regs Reg.inputBC = b)
    (hAC : x.regs Reg.inputAC = c) (hs : x.regs Reg.scratch = scratch)
    (ha : a + n * n ≤ scratch) (hb : b + n * n ≤ scratch) (hc : c + n * n ≤ scratch)
    (hu : ∀ i < n * n, (u i).natAbs ≤ A)
    (hv : ∀ i < n * n, (v i).natAbs ≤ A)
    (hz : ∀ i < n * n, (z i).natAbs ≤ A)
    (hinU : ∀ i < n * n, x.mem (a + i) = encode (u i))
    (hinV : ∀ i < n * n, x.mem (b + i) = encode (v i))
    (hinZ : ∀ i < n * n, x.mem (c + i) = encode (z i))
    (hmag : GenericRAM.Signed.Fits w (CountPrime.magnitudeBudget p (Nat.clog 2 n) A : ℤ))
    (hw : Fits (w + 2) (CountPrime.addressBudget n p (Nat.clog 2 n) scratch a b c)) :
    ∃ y, ExecWithin (w + 2) (count CountPrime.program) x y (CountPrime.cost n p + 6) ∧
      y.regs Reg.countResult = Cslib.Algorithms.ExactTriangle.countZeroMod
        (fun α β : Fin n => u (α.val * n + β.val))
        (fun α β : Fin n => v (α.val * n + β.val))
        (fun α β : Fin n => z (α.val * n + β.val)) p ∧
      ∀ d, d < scratch ∨ CountPrime.memoryEnd n p (Nat.clog 2 n) scratch ≤ d →
        y.mem d = x.mem d := by
  let args := (((((x.set Reg.countSide n).set Reg.countPrime p).set Reg.countAB a).set
    Reg.countBC b).set Reg.countAC c).set Reg.countScratch scratch
  have deliver : ExecWithin (B := .standard) (w + 2)
      (ram[ Reg.countSide ← Reg.side; Reg.countPrime ← Reg.cursor;
        Reg.countAB ← Reg.inputAB; Reg.countBC ← Reg.inputBC;
        Reg.countAC ← Reg.inputAC; Reg.countScratch ← Reg.scratch ]) x args 6 := by
    ram_eval [args, hn, hp, hAB, hBC, hAC, hs, Reg.countSide, Reg.countPrime,
      Reg.countAB, Reg.countBC, Reg.countAC, Reg.countScratch, Reg.side, Reg.cursor,
      Reg.inputAB, Reg.inputBC, Reg.inputAC, Reg.scratch, Fin.mk.injEq]
  obtain ⟨q, hq, _, hresult, frame⟩ := CountPrime.exec (args.comap counterRegisters) u v z
    hp0 (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) ha hb hc hu hv hz
    hinU hinV hinZ hmag hw
  have hinj : Function.Injective counterRegisters := by
    intro i j h
    exact Fin.ext (congrArg (fun i : Fin 160 => i.val) h)
  let y := q.extend counterRegisters args
  have hyresult : y.regs Reg.countResult = q.regs CountPrime.Reg.result := by
    change Function.extend counterRegisters q.regs args.regs
      (counterRegisters CountPrime.Reg.result) = _
    exact hinj.extend_apply _ _ _
  refine ⟨y, ?_, hyresult.trans hresult, frame⟩
  exact (deliver.seq (hq.rename hinj)).mono (by omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
