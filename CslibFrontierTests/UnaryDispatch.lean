/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.UnaryDispatch

namespace CslibFrontierTests.UnaryDispatch

open Turing Turing.MultiTapeTM

private def output : Option (Fin 2) → Option Bool
  | none => none
  | some j => some (decide (j.val = 1))

-- The continuation state type depends on the selected case.
private abbrev States (j : Option (Fin 2)) := Fin (j.elim 0 Fin.val + 1)

private def family (j : Option (Fin 2)) : MultiTapeTM 2 Bool (States j) :=
  .ofTr 0 fun _ _ _ => ⟨0, fun _ => (none, 0), output j, none⟩

private theorem run_family (j : Option (Fin 2)) (input out : List Bool)
    (ws : Fin 2 → List Bool) :
    RunsBetween (family j) (tapesCfg input ws 0 0 out)
      (tapesCfg input ws 0 0 (out ++ (output j).toList)) 1 4 := by
  apply RunsBetween.of_runFrom
  rw [runFrom_one]
  rw [step_of_state rfl]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [family, Action.apply, tapesCfg, Cfg.withState]
  rfl


example : Finite (Turing.MultiTapeTM.UnaryDispatch.State 2 States) := inferInstance

-- Default, first and last cases yield distinct observable outputs, with exact dispatch clocks.
example : RunsBetween (Turing.MultiTapeTM.UnaryDispatch.machine 0 family)
    (tapesCfg [] ![[], [false, true]] 0 0 [true])
    (tapesCfg [] ![[], [false, true]] 0 0 [true]) 3 8 := by
  exact Turing.MultiTapeTM.UnaryDispatch.runsBetween 0 family [] [true]
    ![[], [false, true]] none rfl (run_family none [] [true] _)

example : RunsBetween (Turing.MultiTapeTM.UnaryDispatch.machine 0 family)
    (tapesCfg [] ![[true], [false, true]] 0 0 [true])
    (tapesCfg [] ![[true], [false, true]] 0 0 [true, false]) 5 12 := by
  exact Turing.MultiTapeTM.UnaryDispatch.runsBetween 0 family [] [true]
    ![[true], [false, true]] (some 0) rfl (run_family (some 0) [] [true] _)

example : RunsBetween (Turing.MultiTapeTM.UnaryDispatch.machine 0 family)
    (tapesCfg [] ![[true, true], [false, true]] 0 0 [true])
    (tapesCfg [] ![[true, true], [false, true]] 0 0 [true, true]) 7 16 := by
  exact Turing.MultiTapeTM.UnaryDispatch.runsBetween 0 family [] [true]
    ![[true, true], [false, true]] (some 1) rfl (run_family (some 1) [] [true] _)

end CslibFrontierTests.UnaryDispatch
