/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SpernerHardness

/-!
# Tests for `PPAD`-completeness of `Sperner2D`

Kernel-checked clients (with no `native_decide`) exercising:

1. `EndOfLine_searchReducible_Sperner2D`, `Sperner2D_searchHard`, and `Sperner2D_searchComplete`.
2. Collapse of uniform `PPAD` into `FPSearch` from a polynomial-time solver for `Sperner2D`.
3. Reduction of an explicit 1-bit `endOfLineRel` family (`0 → 1`) to `Sperner2D`, with checked
   witness/non-witness behavior and a concrete `EndOfLine` circuit instance.
-/

public section

namespace CslibFrontierTests.SpernerHardness

open Cslib Cslib.BitString Cslib.Complexity Turing.MultiTapeTM

/-- Constant predecessor map sending both 1-bit vertices to `0`. -/
def oneBitPred (_ : Bool × List Bool) : List Bool := [false]

/-- Constant successor map sending both 1-bit vertices to `1`. -/
def oneBitSucc (_ : Bool × List Bool) : List Bool := [true]

example : SearchReducible encEndOfLine encSperner2D EndOfLine Sperner2D :=
  EndOfLine_searchReducible_Sperner2D

example : SearchHard @PPAD encSperner2D Sperner2D :=
  Sperner2D_searchHard

example : SearchComplete @PPAD encSperner2D Sperner2D :=
  Sperner2D_searchComplete

/-- Any polynomial-time solver for `Sperner2D` puts every problem in `PPAD` into `FPSearch`. -/
theorem ppad_subset_FPSearch_of_sperner2D (h : Sperner2D ∈ FPSearch encSperner2D)
    {α : Type} (enc : α ↪ List Bool) : PPAD enc ⊆ FPSearch enc :=
  Sperner2D_searchHard.subset_FPSearch (fun _ _ hR => (mem_PPAD.mp hR).1) h enc

/-- The concrete 1-bit directed edge `0 → 1` gives a uniform `PPAD` search family. -/
theorem oneBitEol_mem_PPAD :
    endOfLineRel (fun _ : Bool => 1) oneBitPred oneBitSucc ∈ PPAD encBool :=
  endOfLineRel_mem_PPAD (.const 1) (.const _) (.const _) (fun _ _ _ => rfl) (fun _ _ _ => rfl)

/-- The concrete 1-bit `endOfLineRel` family reduces in polynomial time to `Sperner2D`. -/
theorem oneBitEol_searchReducible_Sperner2D :
    SearchReducible encBool encSperner2D
      (endOfLineRel (fun _ : Bool => 1) oneBitPred oneBitSucc) Sperner2D :=
  Sperner2D_searchComplete.2 encBool _ oneBitEol_mem_PPAD

example : endOfLineRel (fun _ : Bool => 1) oneBitPred oneBitSucc false [true] ∧
    ¬endOfLineRel (fun _ : Bool => 1) oneBitPred oneBitSucc false [false] := by
  unfold endOfLineRel hasIn hasOut oneBitPred oneBitSucc zeroVertex
  decide

example : EndOfLine (0, ([], []), ([], [])) [] := by
  unfold EndOfLine endOfLineRel hasIn hasOut zeroVertex
  decide

end CslibFrontierTests.SpernerHardness
