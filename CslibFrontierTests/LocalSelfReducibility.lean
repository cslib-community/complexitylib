/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.LocalSelfReducibility
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Equality
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Local self-reduction clients

A native zero-query singleton and an empty-language self-reduction with a genuinely active
local query. Word tests distinguish ceiling from floor logarithms and reject changed prefixes,
changed lengths, increasing queries, and self-queries.
-/

public section

namespace Cslib.Complexity.LocalSelfReducibilityTest

open Turing.MultiTapeTM

example : LocalSelfReductionQuery [false, true] [false, false] := by decide

-- At length three the ceiling window has two bits, rather than one.
example : LocalSelfReductionQuery [false, true, false] [false, false, true] := by decide

example : ¬ LocalSelfReductionQuery [true, false] [false, false] := by decide
example : ¬ LocalSelfReductionQuery [false, true] [false] := by decide
example : ¬ LocalSelfReductionQuery [false, false] [false, true] := by decide
example : ¬ LocalSelfReductionQuery [false, true] [false, true] := by decide
example : ¬ LocalSelfReductionQuery [] [] := by decide
example : ¬ LocalSelfReductionQuery [true] [false] := by decide

/-- A satisfiable native language instance, including both singleton membership branches. -/
theorem singleton_mem_L : ({true} : Set Bool) ∈ L encBool :=
  ⟨id, ComputableInLogSpace.id, fun a => by simp⟩

example : LogSpaceTruthTableSelfReducible encBool ({true} : Set Bool) :=
  .of_mem_L singleton_mem_L

example : LogSpaceDTTSelfReducible encBool ({true} : Set Bool) :=
  .of_mem_L singleton_mem_L

example : LogSpaceCTTSelfReducible encBool ({true} : Set Bool) :=
  .of_mem_L singleton_mem_L

/-- One active query on `[false, true]`, and zero queries elsewhere.
This uses native equality/branching/count/query/evaluation certificates. -/
theorem empty_active : LogSpaceTruthTableSelfReducible encBits (∅ : Set (List Bool)) := by
  let r : List Bool → ℕ := fun x => if x = [false, true] then 1 else 0
  refine ⟨r, fun _ => [false, false], fun _ => false, ?_,
    ComputableInLogSpace.const _, ComputableInLogSpace.const _, ?_, ?_⟩
  · dsimp only [r]
    fun_prop
  · intro x i hi
    by_cases hx : x = [false, true]
    · subst x
      exact (by decide : LocalSelfReductionQuery [false, true] [false, false])
    · simp [r, hx] at hi
  · intro x
    simp

example (x : List Bool) :
    ¬ LocalSelfReductionQuery x x := fun h => h.ne rfl

example : LogSpaceTruthTableAutoreducible encBool ({true} : Set Bool) :=
  (LogSpaceDTTSelfReducible.of_mem_L singleton_mem_L).logSpaceTruthTableSelfReducible
    |>.logSpaceTruthTableAutoreducible

example : LogSpaceTruthTableAutoreducible encBool ({true} : Set Bool) :=
  (LogSpaceCTTSelfReducible.of_mem_L singleton_mem_L).logSpaceTruthTableSelfReducible
    |>.logSpaceTruthTableAutoreducible

example : truthTableUnaryDependency ({true} : Set Bool) true (fun _ : Unit => 2)
    (fun p => p.2 == 0) (fun p => p.2.headD false) () false = false := by
  simp [truthTableUnaryDependency]

example (a b : Bool) (hb : b = !a) : a = !b :=
  unary_bool_dependency_update Bool.not (by decide) hb

end Cslib.Complexity.LocalSelfReducibilityTest
