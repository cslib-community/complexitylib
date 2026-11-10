/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (formal abstract regression tests)

import ComplexityAbstracts.MatrixMultiplicationAbstract
import Lean.Util.CollectAxioms

/-! # Rational-field clients of the matrix multiplication abstract

Check a characteristic-zero instance and the exact input/output convention.
-/

namespace ComplexityTests.Abstracts.MatrixMultiplicationTests

example : ComplexityAbstracts.MatrixMultiplicationAbstract.exponent ℚ ≤ 9 / 4 :=
  ComplexityAbstracts.MatrixMultiplicationAbstract.exponent_le_nine_quarters ℚ

example (A : Matrix (Fin 2) (Fin 2) ℚ) :
    ComplexityAbstracts.MatrixMultiplicationAbstract.entries A
      (finProdFinEquiv (0, 1)) = A 0 1 := by
  simp [ComplexityAbstracts.MatrixMultiplicationAbstract.entries]

/-- Returning the first input for the product fails already at `A = 1`, `B = 0`. -/
example : ¬ ComplexityAbstracts.MatrixMultiplicationAbstract.ComputesProduct
    (n := 1) (Cslib.Circuits.Circuit.wiring (Cslib.Circuits.arithSignature ℚ)
      (fun _ => 0)) := by
  intro h
  have hbad := congrFun (h (fun _ _ => 1) (fun _ _ => 0)) 0
  change (1 : ℚ) = ∑ _ : Fin 1, (1 : ℚ) * 0 at hbad
  norm_num at hbad


open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ComplexityAbstracts.MatrixMultiplicationAbstract.circuits_nine_quarters,
      ``ComplexityAbstracts.MatrixMultiplicationAbstract.exponent_le_nine_quarters] do
    let axioms ← collectAxioms name
    let disallowed := axioms.filter fun ax =>
      !allowed.contains ax
    unless disallowed.isEmpty do
      throwError "unexpected abstract axioms: {disallowed}"

end ComplexityTests.Abstracts.MatrixMultiplicationTests
