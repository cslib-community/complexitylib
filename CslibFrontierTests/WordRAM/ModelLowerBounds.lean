/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.OutputLowerBound
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.LowerBound

/-! # Nonvacuity and boundary checks for native resource lower bounds -/

public section

namespace Cslib.WordRAM.Tests.ModelLowerBounds

open Cslib.Algorithms.WordRAM.ThreeSum

-- Both sides of the adversary are actual repeated-value integer inputs in the promise domain.
example (κ : ℕ) : ¬Cslib.Algorithms.ThreeSum.HasSolution
    (fun i : Fin (hardInputBounded κ 0).val.length => (hardInputBounded κ 0).val[i]) :=
  hardInput_no_solution 0

example (κ : ℕ) : Cslib.Algorithms.ThreeSum.HasSolution
    (fun i : Fin (hardInputSetBounded κ 1 0).val.length =>
      (hardInputSetBounded κ 1 0).val[i]) :=
  hardInput_set_solution 1 0 (by decide)

-- The zero-square output requires exactly the charged halt, with no stores.
example : InputFits 0 [] := by decide

example : ExecutesList 0 ([.halt 0] : Program .standard 1) (.init []) [] 1 := by
  refine ⟨.init [], 0, 0, .refl _, rfl, ?_, by decide, rfl⟩
  exact outputList_init []

-- This actual initialized program changes a zero data cell and returns the one-entry matrix.
example : InputFits 1 [0] := by decide

/-- A four-step initialized program materializing a one-entry nonzero output. -/
@[expose] def oneOutput : Program .standard 1 :=
  [.op (.const 0 1), .op (.store 0 0), .op (.const 0 0), .halt 0]

/-- The concrete execution, including its final halt. -/
theorem oneOutput_executes : ExecutesList 1 oneOutput (.init [0]) [1] 4 := by
  let x := (Data.init [0] : Data 1)
  let x₁ := x.set 0 1
  let x₂ := x₁.write 1 1
  let x₃ := x₂.set 0 0
  have h₁ : Next 1 oneOutput (.init [0]) ⟨1, x₁⟩ := by
    simp [Next, step, oneOutput, Op.eval, Data.put, Fits, State.init, x₁, x]
  have h₂ : Next 1 oneOutput ⟨1, x₁⟩ ⟨2, x₂⟩ := by
    simp [Next, step, oneOutput, Op.eval, x₂, x₁, Data.set]
  have h₃ : Next 1 oneOutput ⟨2, x₂⟩ ⟨3, x₃⟩ := by
    simp [Next, step, oneOutput, Op.eval, Data.put, Fits, x₃]
  refine ⟨⟨3, x₃⟩, 3, 0,
    ((Relation.RelatesInSteps.single h₁).tail _ _ _ _ h₂).tail _ _ _ _ h₃, ?_, ?_, by decide, rfl⟩
  · simp [step, oneOutput, x₃, Data.set]
  · simp [outputList, x₃, x₂, x₁, x, Data.set, Data.write, Data.init]

example : 1 * 1 + 1 ≤ 4 :=
  ExecutesList.denseMatrix_lowerBound (m := 1) (n := 1) oneOutput_executes

-- The actual existing domain is admitted at its common size-only physical-width threshold.
example (κ : ℕ) : Decision.Admissible κ [1, -1, 0]
    (Decision.width κ 123357 3) := by
  refine ⟨by simp, ?_⟩
  intro z hz
  have hpow : 1 ≤ (3 + 2 : ℕ) ^ κ := Nat.one_le_pow _ _ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  have habs : |z| ≤ (1 : ℤ) := by rcases hz with rfl | rfl | rfl <;> norm_num
  exact habs.trans (by exact_mod_cast hpow)

-- Every promised input admits a fitting width at the size-only threshold, so the promised-domain
-- sublinear lower bound is nonvacuous and matches the upper theorem's domain.
example (κ : ℕ) : InputAdmissible
    (fun _ (input : Decision.MagnitudeBoundedInput κ) => input.val.map Signed.encode)
    (fun input W => Decision.width κ 123357 input.val.length ≤ W) := by
  intro input
  obtain ⟨W, hW, hfit⟩ := inputAdmissible_of_widthIndependent
    (fun input : Decision.MagnitudeBoundedInput κ => input.val.map Signed.encode)
    (fun input => Decision.width κ 123357 input.val.length) input
  exact ⟨W, hW, hfit⟩

example (κ : ℕ) :
    ¬UniformDecidableInO .standard
      {input : Decision.MagnitudeBoundedInput κ |
        Cslib.Algorithms.ThreeSum.HasSolution (fun i : Fin input.val.length => input.val[i])}
      (fun _ input => input.val.map Signed.encode) (fun input => input.val.length)
      (fun n _ => ⌈(n : ℝ) ^ (1 / 2 : ℝ)⌉₊)
      (fun input W => Decision.width κ 123357 input.val.length ≤ W) :=
  not_uniformDecidableInO_sublinear .standard κ (by norm_num)

end Cslib.WordRAM.Tests.ModelLowerBounds
