/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.ParameterSelecting.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Properties
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Frame
public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Header

/-!
# Fixed banks and native code properties of the assembled solver

All three actual component banks are embedded injectively. Parameter and selector calls retain
saved original data above their bank; the complete callable solver retains its existing low160
and original-argument frames. Register transport does not relocate a memory address implicitly.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting

open Cslib.WordRAM

/-- The actual16-register parameter placement is injective. -/
theorem parameterBank_injective : Function.Injective parameterBank := by
  intro i j h
  apply Fin.ext
  have h' := congrArg Fin.val h
  dsimp only [parameterBank] at h'
  omega

/-- The full actual selector bank is embedded without aliasing. -/
theorem selectorBank_injective : Function.Injective selectorBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 640 => k.val) h)

/-- The full actual exhaustive bank is embedded without aliasing. -/
theorem slowBank_injective : Function.Injective slowBank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 640 => k.val) h)

/-- Parameters preserve the complete original protocol and all high saved arguments. -/
theorem parameters_preserves (j : Fin 640) (hj : j.val < 144 ∨ 160 ≤ j.val) :
    parameters.Preserves j :=
  DyadicParameters.program.preserves_rename_of_forall_ne parameterBank j (by
    intro i hi
    have hv := congrArg Fin.val hi
    dsimp only [parameterBank] at hv
    have := i.isLt
    omega)

/-- The assembled program cannot inspect physical width. -/
theorem program_not_readsWidth : ¬program.ReadsWidth := by
  have hp : ¬parameters.ReadsWidth := by decide +kernel
  have hs : ¬selectPrime.ReadsWidth := by
    simpa only [selectPrime, Code.readsWidth_rename] using
      PrimeSelection.not_readsWidth (show ¬CountPrime.program.ReadsWidth by decide +kernel)
  have hb : ¬(ThreeSum.Host.Slow.program.rename slowBank).ReadsWidth := by decide +kernel
  simpa only [program, fast, solve, slow, save, selectArguments, slowArguments, restore,
    Code.ReadsWidth, CallableFixedPrime.program_not_readsWidth, hp, hs, hb,
    Op.ReadsWidth, false_or, or_false, Op.bin] using (show ¬False by decide)

/-- The complete parameter/selection/fast/slow composition is one fixed finite native program. -/
theorem program_fixed : (program.program Reg.result).length ≤ 434000 ∧
    ¬(program.program Reg.result).ReadsWidth := by
  refine ⟨?_, Code.not_readsWidth_program program_not_readsWidth _⟩
  have hp := DyadicParameters.program_fixed.1
  have hs := CountPrime.program_fixed.1
  have hc := CallableFixedPrime.program_fixed.1
  simp only [Code.program, List.length_append, Code.length_assemble,
    List.length_singleton] at hp hs hc ⊢
  have hcounter : CountPrime.program.size ≤ 32768 := by
    have hle : CountPrime.program.size ≤ CountPrime.entryProgram.size := by
      change _ ≤ CountPrime.input.size + CountPrime.program.size
      omega
    omega
  have hslow : ThreeSum.Host.Slow.program.size ≤ 128 := by decide +kernel
  have htotal : program.size = save.size +
      (parameters.size + ((slow.size + fast.size + 2) + restore.size)) := by
    dsimp only [program, Code.size]
  have hfast : fast.size = 8 + (selectPrime.size + (1 + CallableFixedPrime.program.size)) := by
    dsimp only [fast, solve, selectArguments, Code.size]
  have hsmall : slow.size = 6 + (ThreeSum.Host.Slow.program.size + 1) := by
    change 6 + ((ThreeSum.Host.Slow.program.rename slowBank).size + 1) = _
    rw [Code.size_rename]
  have hparams : parameters.size = DyadicParameters.program.size := Code.size_rename _ _
  have hselect : selectPrime.size = CountPrime.program.size + 50 := by
    simpa only [selectPrime, Code.size_rename] using PrimeSelection.program_size CountPrime.program
  have hsave : save.size = 8 := rfl
  have hrestore : restore.size = 7 := rfl
  rw [htotal, hfast, hsmall, hparams, hselect, hsave, hrestore]
  omega

end Cslib.Algorithms.WordRAM.ExactTriangle.ParameterSelecting
