/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational

/-!
# Rational hitting list regression tests

Concrete formulas, their node counts, explicit admissibility and nonzeroness witnesses on `1 × 1`
and `2 × 2` rational matrices, formulas outside the domain, exact matrix evaluation, the boundary
cases `s = 0` and `n = 0`, and nonvacuity checks for the headline theorems. The hitting list itself
is astronomically long and is never evaluated; only its dimension is computed, by the kernel. The
executable pieces of the generator are run instead: the staged determinant, single grid points,
and the generator on a grid of side `2` or `4` with the parameters for `n = s = 0`, whose output
is fed to the finite tests. The finite tests are also run on a hand-built `2 × 2` list.
-/

namespace ComplexityTests.RationalHitting

open Cslib.Circuits.Rational

/-! ### Concrete formulas -/

/-- The commutator `x₀ x₁ - x₁ x₀`, written with the constant `-1`. -/
def commutator : Formula 2 :=
  .add (.mul (.var 0) (.var 1)) (.mul (.const (-1)) (.mul (.var 1) (.var 0)))

/-- The formula `x₀ - x₀`, identically zero wherever defined. -/
def cancel : Formula 1 := .add (.var 0) (.mul (.const (-1)) (.var 0))

-- The previous fully qualified name still accepts the original rational-formula type.
#guard_msgs (drop warning) in
example : Cslib.Circuits.Rational.Formula.nodeCount (Formula.var 0 : Formula 1) = 1 := rfl

example : Cslib.Circuits.Formula.nodeCount (Formula.var 0 : Formula 1) = 1 := by simp
example : Cslib.Circuits.Formula.nodeCount (Formula.inv (.const 0) : Formula 1) = 2 := by simp
example : Cslib.Circuits.Formula.nodeCount commutator = 9 := by simp [commutator]
example : Cslib.Circuits.Formula.nodeCount cancel = 5 := by simp [cancel]

/-- info: [9, 5] -/
#guard_msgs in
#eval [Cslib.Circuits.Formula.nodeCount commutator, Cslib.Circuits.Formula.nodeCount cancel]

-- The generic formula decidable equality distinguishes the order of the factors.
example : (Formula.mul (.var 0) (.var 1) : Formula 2) ≠ .mul (.var 1) (.var 0) := by decide
example : (Formula.var 0 : Formula 2) ≠ .var 1 := by decide
example : (Formula.const 1 : Formula 2) ≠ .const 2 := by decide
example : commutator = commutator := by decide

/-! ### Evaluation with a genuine two-sided inverse -/

-- In `ℚ`, the inverse of `2` is `1 / 2`, and the inverse of `0` is undefined, not `0`.
example : (Formula.inv (.var 0) : Formula 1).Eval (RingHom.id ℚ) ![2] (1 / 2) :=
  Formula.Eval.inv (a := 2) (Formula.Eval.var 0) (by norm_num) (by norm_num)

example : ¬ ∃ v, (Formula.inv (.var 0) : Formula 1).Eval (RingHom.id ℚ) ![0] v := by
  rintro ⟨v, a, ha, h, -⟩
  simp only [Formula.eval_var_iff, Matrix.cons_val_zero] at ha
  simp [ha] at h

/-- An upper unitriangular `2 × 2` matrix. -/
def unipotent : Mat 2 := !![1, 1; 0, 1]

/-- The inverse of `unipotent`. -/
def unipotentInv : Mat 2 := !![1, -1; 0, 1]

theorem unipotent_mul : unipotent * unipotentInv = 1 := by
  simp [unipotent, unipotentInv, Matrix.one_fin_two]

theorem unipotentInv_mul : unipotentInv * unipotent = 1 := by
  simp [unipotent, unipotentInv, Matrix.one_fin_two]

theorem evaluates_inv_unipotent :
    Evaluates (.inv (.var 0) : Formula 1) ![unipotent] unipotentInv :=
  Formula.Eval.inv (Formula.Eval.var 0) unipotent_mul unipotentInv_mul

-- The executable evaluator agrees, by the soundness and completeness theorem.
example : (Formula.inv (.var 0) : Formula 1).evalMatrix? ![unipotent] = some unipotentInv :=
  (Formula.evalMatrix?_eq_some_iff _ _ _).mpr evaluates_inv_unipotent

-- Compiled evaluation on `1 × 1` and `2 × 2` matrices.
/-- info: [true, true, true, true, true, true] -/
#guard_msgs in
#eval [
  decide ((Formula.inv (.var 0) : Formula 1).evalMatrix? ![unipotent] = some unipotentInv),
  decide ((Formula.inv (.var 0) : Formula 1).evalMatrix? ![!![2]] = some !![1 / 2]),
  decide ((Formula.inv (.var 0) : Formula 1).evalMatrix? ![!![0]] = none),
  decide ((Formula.inv (.const 0) : Formula 1).evalMatrix? ![unipotent] = none),
  decide ((Formula.inv cancel).evalMatrix? ![unipotent] = none),
  decide (cancel.evalMatrix? ![unipotent] = some 0)]

-- The inverse of a singular constant is undefined, as a proof.
example (X : Tuple 1 2) : (Formula.inv (.const 0) : Formula 1).evalMatrix? X = none := by
  simp

/-! ### Admissibility and nonzeroness witnesses -/

theorem nonzero_var : Nonzero (.var 0 : Formula 1) :=
  ⟨1, one_pos, fun _ => 1, 1, rfl, one_ne_zero⟩

theorem admissible_var : Admissible (.var 0 : Formula 1) := nonzero_var.admissible

/-- The `2 × 2` matrix unit `E₀₁`. -/
def e01 : Mat 2 := !![0, 1; 0, 0]

/-- The `2 × 2` matrix unit `E₁₀`. -/
def e10 : Mat 2 := !![0, 0; 1, 0]

theorem evaluates_commutator :
    Evaluates commutator ![e01, e10] (e01 * e10 + algebraMap ℚ (Mat 2) (-1) * (e10 * e01)) :=
  .add (.mul (.var 0) (.var 1)) (.mul (.const (-1)) (.mul (.var 1) (.var 0)))

theorem nonzero_commutator : Nonzero commutator := by
  refine ⟨2, two_pos, ![e01, e10], _, evaluates_commutator, fun h => ?_⟩
  have h00 := congrFun (congrFun h 0) 0
  simp [e01, e10, Matrix.algebraMap_eq_diagonal] at h00

/-- On `1 × 1` matrices the commutator vanishes wherever it is defined. -/
theorem commutator_eq_zero_of_dim_one {d : ℕ} (hd : d = 1) (X : Tuple 2 d) {v : Mat d}
    (h : Evaluates commutator X v) : v = 0 := by
  subst hd
  obtain ⟨_, _, ⟨_, _, rfl, rfl, rfl⟩, ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩, rfl⟩ := h
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Matrix.algebraMap_eq_diagonal, mul_comm]

-- The commutator is admissible, also on `1 × 1` matrices, but not nonzero there.
theorem admissible_commutator : Admissible commutator := nonzero_commutator.admissible

/-- The zero constant is admissible but not nonzero. -/
theorem not_nonzero_const_zero : ¬ Nonzero (.const 0 : Formula 1) := by
  rintro ⟨d, _, X, v, hv, hne⟩
  exact hne (by simpa [Evaluates] using hv)

theorem admissible_const_zero : Admissible (.const 0 : Formula 1) :=
  ⟨1, one_pos, fun _ => 0, _, Formula.Eval.const 0⟩

theorem not_nonzero_cancel : ¬ Nonzero cancel := by
  rintro ⟨d, _, X, v, hv, hne⟩
  obtain ⟨_, _, rfl, ⟨_, _, rfl, rfl, rfl⟩, rfl⟩ := hv
  exact hne (by simp)

-- The inverse of the zero constant and of an identically zero formula are not admissible.
theorem not_admissible_inv_const_zero : ¬ Admissible (.inv (.const 0) : Formula 1) :=
  fun h => not_nonzero_const_zero ((admissible_inv_iff_nonzero _).mp h)

theorem not_admissible_inv_cancel : ¬ Admissible (.inv cancel) :=
  fun h => not_nonzero_cancel ((admissible_inv_iff_nonzero _).mp h)

theorem admissible_inv_var : Admissible (.inv (.var 0) : Formula 1) :=
  (admissible_inv_iff_nonzero _).mpr nonzero_var

-- The executable tests give the expected answers, by their correctness theorems.
example : (Formula.var 0 : Formula 1).admissible? = true :=
  (Formula.admissible?_eq_true_iff _).mpr admissible_var
example : (Formula.const 0 : Formula 1).admissible? = true :=
  (Formula.admissible?_eq_true_iff _).mpr admissible_const_zero
example : (Formula.const 0 : Formula 1).nonzero? = false :=
  Bool.eq_false_iff.mpr fun h => not_nonzero_const_zero ((Formula.nonzero?_eq_true_iff _).mp h)
example : (Formula.inv cancel).admissible? = false :=
  Bool.eq_false_iff.mpr fun h =>
    not_admissible_inv_cancel ((Formula.admissible?_eq_true_iff _).mp h)
example : commutator.nonzero? = true := (Formula.nonzero?_eq_true_iff _).mpr nonzero_commutator

example : Decidable (Admissible commutator) := inferInstance
example : Decidable (Nonzero (.inv cancel)) := inferInstance

/-! ### The finite tests on a small hand-built list -/

/-- A two-element list of `2 × 2` substitutions for one variable: a singular nilpotent matrix and
an invertible unipotent one. -/
def smallList : Output 1 := ⟨2, two_pos, [![e01], ![unipotent]]⟩

/-- The singular substitution alone. -/
def singularList : Output 1 := ⟨2, two_pos, [![e01]]⟩

-- Compiled: the variable is invertible at `unipotent`, so its inverse is defined there; `x₀ - x₀`
-- is defined but zero everywhere, so its inverse is defined nowhere; at `e01` alone the variable
-- is singular and its inverse undefined.
/-- info: [true, true, false, true, false, false, false, true] -/
#guard_msgs in
#eval [
  smallList.nonzeroTest (.var 0),
  smallList.admissibilityTest (.inv (.var 0)),
  smallList.nonzeroTest cancel,
  smallList.admissibilityTest cancel,
  smallList.admissibilityTest (.inv cancel),
  singularList.nonzeroTest (.var 0),
  singularList.admissibilityTest (.inv (.var 0)),
  singularList.admissibilityTest (.var 0)]

-- A small-dimension witness exists for every admissible formula.
example : ∃ d, 0 < d ∧ d ≤ 256 * (2 + 9 + 3) ^ 10 ∧
    ∃ (X : Tuple 2 d) (v : Mat d), Evaluates commutator X v := by
  simpa [commutator] using admissible_commutator.exists_dimension_le

/-! ### Boundary cases -/

-- `s = 0`: every list hits, as every formula has a node.
example (n : ℕ) (H : Output n) : Hits 0 H := hits_zero H
example (n : ℕ) : Hits 0 (hittingList n 0) := hittingList_hits n 0

-- `n = 0`: the zero-variable statements carry no hypothesis.
example (s : ℕ) : Hits s (hittingList 0 s) := hittingList_hits 0 s
example (s : ℕ) : (hittingList 0 s).dimension ≤ 256 * (s + 1) ^ 10 := by
  simpa using hittingList_dimension_le 0 s
example (s : ℕ) : (encodeOutput (hittingList 0 s)).length ≤
    PolynomialBounds.outputConstant * (s + 1) ^ 104 := by
  simpa using hittingList_encoding_length_le 0 s

theorem nonzero_const_one : Nonzero (.const 1 : Formula 0) :=
  ⟨1, one_pos, Fin.elim0, 1, by simp [Evaluates], one_ne_zero⟩

-- The zero-variable list is nonempty: it hits the constant `1`.
example : (hittingList 0 1).tuples ≠ [] := by
  obtain ⟨X, hX, -⟩ :=
    hittingList_hits 0 1 (.const 1) (by simp) nonzero_const_one.admissible nonzero_const_one
  exact List.ne_nil_of_mem hX

/-! ### The list's dimension, computed by the kernel -/

example (n s : ℕ) : (hittingList n s).dimension =
    2 ^ (Parameters.exponent n s + 1) * 2 ^ Parameters.exponent n s := rfl

example : (hittingList 0 0).dimension = 8 := by decide
example : (hittingList 1 1).dimension = 32768 := by decide

-- The parameters for `n = s = 0`: the grid has side `385`, so the list is never computed in full.
/-- info: [2, 1, 4, 385] -/
#guard_msgs in
#eval [Parameters.truncation 0 0, Parameters.exponent 0 0, Parameters.ambientDimension 0 0,
  Parameters.gridSize 0 0]

/-! ### Executable pieces of the generator -/

-- The staged division-free determinant, compiled.
/-- info: [5, -2, 0, 1] -/
#guard_msgs in
#eval [DeterminantAlgorithm.determinant (DeterminantAlgorithm.tabulate !![2, 1; 1, 3]),
  DeterminantAlgorithm.determinant (DeterminantAlgorithm.tabulate !![1, 2; 3, 4]),
  DeterminantAlgorithm.determinant (DeterminantAlgorithm.tabulate !![1, 2, 3; 4, 5, 6; 7, 8, 9]),
  DeterminantAlgorithm.determinant (DeterminantAlgorithm.tabulate (1 : Matrix (Fin 4) (Fin 4) ℤ))]

-- Two grid points of the generator for `n = s = 0`, with `8 × 8` integer lift matrices: the
-- normalizing matrix is tested for singularity by the staged determinant, and is singular at the
-- first point only.
/-- info: [false, true] -/
#guard_msgs in
#eval [ExecutableGenerator.atPoint 0 (Parameters.truncation 0 0) (Parameters.exponent 0 0)
    ![1, 1, 1] |>.isSome,
  ExecutableGenerator.atPoint 0 (Parameters.truncation 0 0) (Parameters.exponent 0 0)
    ![1, 2, 1] |>.isSome]

-- The generator with the parameters for `n = s = 0` (dimension `8`), on the grid of side `4`
-- instead of `385`: `48` of the `64` points survive the singularity test.
/-- info: 48 -/
#guard_msgs in
#eval (ExecutableGenerator.output 0 (Parameters.truncation 0 0) (Parameters.exponent 0 0)
  4).tuples.length

/-- The generator for one variable with the parameters for `n = s = 0` and a grid of side `2`; a
list of `8 × 8` rational matrices, small enough to compute in full. -/
def smallGenerated : Output 1 :=
  ExecutableGenerator.output 1 (Parameters.truncation 0 0) (Parameters.exponent 0 0) 2

-- Its length, the diagonal of its first matrix, and the domain test run on it. The determinant
-- test is not run here: `Matrix.det` is a permutation sum, which takes over ten seconds per
-- `8 × 8` determinant in the interpreter; it is checked on the `2 × 2` list above.
/-- info: 4 -/
#guard_msgs in
#eval smallGenerated.tuples.length

/-- info: some [-5 / 4, -5 / 4, -5 / 4, -5 / 4, 1 / 4, 1 / 4, 1 / 4, 1 / 4] -/
#guard_msgs in
#eval smallGenerated.tuples.head?.map fun X => (List.finRange 8).map fun i => X 0 i i

/-- info: [true, true] -/
#guard_msgs in
#eval [smallGenerated.admissibilityTest cancel,
  smallGenerated.admissibilityTest (.mul (.var 0) (.add (.var 0) (.const 1)))]

/-! ### The encoding-length constant -/

example : PolynomialBounds.outputConstant = 18805804774818203755428413960 := by decide
example : PolynomialBounds.outputConstant < 2 * 10 ^ 28 := by decide

/-! ### Nonvacuity of the headline theorems -/

-- The hypotheses of the hitting property are satisfiable, and the list is nonempty.
example : ∃ X ∈ (hittingList 1 1).tuples, ∃ v, Evaluates (.var 0) X v ∧ IsUnit v :=
  hittingList_hits 1 1 (.var 0) (by simp) admissible_var nonzero_var

-- Positive dimension is not enough: the list for the commutator must use dimension at least 2.
example : 2 ≤ (hittingList 2 9).dimension := by
  obtain ⟨X, -, v, hv, hu⟩ := hittingList_hits 2 9 commutator (by simp [commutator])
    admissible_commutator nonzero_commutator
  by_contra h
  have hd : (hittingList 2 9).dimension = 1 := by
    have := (hittingList 2 9).dimension_pos
    omega
  have hv0 := commutator_eq_zero_of_dim_one hd X hv
  subst hv0
  have : Nonempty (Fin (hittingList 2 9).dimension) := ⟨⟨0, by omega⟩⟩
  exact not_isUnit_zero hu

end ComplexityTests.RationalHitting
