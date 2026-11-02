/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Program

/-!
# Actual selector trial-division calls

Argument delivery and register renaming compose the existing native primality kernel. Every
memory cell and every register above the six-register trial bank survive the call.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

open Cslib.WordRAM

private theorem trial_injective : Function.Injective trialRegisters := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun i : Fin 160 => i.val) h

/-- Test the actual current candidate in at most `7p+7` charged instructions, including
argument delivery. The input must be at least two; no primality bit is supplied. -/
theorem exec_trial {w : ℕ} (x : Data 160) (hp : 2 ≤ x.regs Reg.cursor)
    (hfit : Fits w (x.regs Reg.cursor + 2)) :
    ∃ y, ExecWithin w trial x y (7 * x.regs Reg.cursor + 7) ∧
      y.regs Reg.trialFlag = (if (x.regs Reg.cursor).Prime then 1 else 0) ∧
      y.mem = x.mem ∧ ∀ i, 6 ≤ i.val → y.regs i = x.regs i := by
  let p := x.set Reg.trialArg (x.regs Reg.cursor)
  obtain ⟨z, hz, hflag, _, hmem⟩ := PrimeTrial.exec (p.comap trialRegisters)
    (by change 2 ≤ x.regs Reg.cursor; exact hp)
    (by change Fits w (x.regs Reg.cursor + 2); exact hfit)
  let y := z.extend trialRegisters p
  have hyflag : y.regs Reg.trialFlag = z.regs PrimeTrial.flag := by
    change Function.extend trialRegisters z.regs p.regs (trialRegisters PrimeTrial.flag) = _
    exact trial_injective.extend_apply _ _ _
  have hcopy : ExecWithin (B := .standard) w (ram[ Reg.trialArg ← Reg.cursor ]) x p 1 :=
    ExecWithin.copy
  refine ⟨y, ?_, hyflag.trans hflag, hmem, ?_⟩
  · exact (hcopy.seq (hz.rename trial_injective)).mono (by
      change 1 + (7 * (x.regs Reg.cursor - 2) + 6) ≤ 7 * x.regs Reg.cursor + 7
      omega)
  · intro i hi
    change Function.extend trialRegisters z.regs p.regs i = x.regs i
    rw [Function.extend_apply']
    · have hne : i ≠ Reg.trialArg := by
        intro h
        subst i
        change 6 ≤ 0 at hi
        omega
      exact Function.update_of_ne hne _ _
    · rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      dsimp only [trialRegisters] at hv
      omega

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
