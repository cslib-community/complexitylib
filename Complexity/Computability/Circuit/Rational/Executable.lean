/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Rational.Determinant
import Batteries.Data.Vector.Lemmas

/-!
# The executable hitting-list generator

A computable version of `Generator.list` that never computes in the cyclotomic field. At each
grid point it materializes the integer lift matrices as dense tables, tests singularity with
the staged integer determinant, and computes each normalized entry as a ratio of two integer
determinants (Cramer's rule). The resulting list, in the same order, is proved equal to the
noncomputable specification.

## Main definitions

* `Rational.ExecutableGenerator.atPoint`: the normalized tuple at one grid point, if any.
* `Rational.ExecutableGenerator.output`: the computable list for fixed parameters.
* `Rational.ExecutableGenerator.list`: the computable list for `n` variables and `s` nodes.
* `Rational.ExecutableGenerator.encoded`: its binary encoding.

## Main results

* `Rational.ExecutableGenerator.atPoint_spec`: pointwise agreement with the specification.
* `Rational.ExecutableGenerator.list_spec`: `list = Generator.list`.
* `Rational.ExecutableGenerator.exact_output`: the dimension, encoding-length and hitting
  guarantees of the computed list.

## References

* Adapted from OpenAI's formalization [OpenAI2026RationalHitting] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Computability/RationalHitting/Executable.lean), via the complexitylib port
  [Schlesinger2026RationalHitting] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.Circuits

namespace Rational.ExecutableGenerator
open Matrix DeterminantAlgorithm

/-- Dense, staged integer input tables. No quotient-field element is computed. -/
def inputTables (n N e : ℕ) (x : Fin 3 → ℕ) :
    Vector (Table (Generator.matrixDimension e)) (n + 1) :=
  Vector.ofFn fun a => tabulate (Generator.integralLift n N e x a)

@[simp] lemma inputTables_denote (n N e : ℕ) (x : Fin 3 → ℕ) (a : Fin (n + 1)) :
    denote ((inputTables n N e x).get a) = Generator.integralLift n N e x a := by
  simp [inputTables]

/-- Cramer's numerators are computed by the staged division-free algorithm. -/
def normalizedEntry {d : ℕ} (A B : Table d) (den : ℤ) (i j : Fin d) : ℚ :=
  Rat.divInt (determinant (tabulate ((denote A).updateCol i (fun r => denote B r j)))) den

private lemma normalizedEntry_spec {d : ℕ} (A B : Table d) (hA : (denote A).det ≠ 0) (i j : Fin d) :
    normalizedEntry A B (determinant A) i j =
      (((denote A).map (Int.castRingHom ℚ))⁻¹ * (denote B).map (Int.castRingHom ℚ)) i j := by
  rw [normalizedEntry, determinant_eq, denote_tabulate, determinant_eq]
  exact (EncodingBounds.normalized_entry_ratio (denote A) (denote B) hA i j).symm

/-- A finite vector of dense rational matrix tables. -/
abbrev RationalTable (n d : ℕ) := Vector (Vector (Vector ℚ d) d) n

/-- Read a dense rational table as a matrix substitution. -/
def tuple {n d : ℕ} (T : RationalTable n d) : Tuple n d :=
  fun a i j => ((T.get a).get i).get j

/-- Compute the normalized tuple entrywise using determinant ratios. -/
def normalized {n d : ℕ} (A : Vector (Table d) (n + 1)) (den : ℤ) : RationalTable n d :=
  Vector.ofFn fun a => Vector.ofFn fun i => Vector.ofFn fun j =>
    normalizedEntry (A.get 0) (A.get a.succ) den i j

@[simp] lemma tuple_normalized {n d : ℕ} (A : Vector (Table d) (n + 1)) (den : ℤ)
    (a : Fin n) (i j : Fin d) :
    tuple (normalized A den) a i j = normalizedEntry (A.get 0) (A.get a.succ) den i j := by
  simp [tuple, normalized]

/-- The only singularity test; all repeated algebra is materialized in dense tables. -/
def atPoint (n N e : ℕ) (x : Fin 3 → ℕ) : Option (Tuple n (Generator.matrixDimension e)) :=
  let A := inputTables n N e x
  let den := determinant (A.get 0)
  if den = 0 then none else some (tuple (normalized A den))

private lemma U_det_eq_zero (n N e : ℕ) (x : Fin 3 → ℕ) :
    (Generator.integralLift n N e x 0).det = 0 ↔ (Generator.rationalLift n N e x 0).det = 0 := by
  have he := congrArg Matrix.det (Generator.U_cast n N e x 0)
  rw [Matrix.det_smul] at he
  simp only [Fintype.card_fin] at he
  change ((Generator.integralLift n N e x 0).map (fun z : ℤ => (z : ℚ))).det =
    (CyclotomicRing.dimension e : ℚ) ^ (Generator.matrixDimension e) *
      (Generator.rationalLift n N e x 0).det at he
  have hc : (CyclotomicRing.dimension e : ℚ) ^ (Generator.matrixDimension e) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (CyclotomicRing.dimension_pos e).ne')
  constructor
  · intro h
    have hv : (((Generator.integralLift n N e x 0).det : ℤ) : ℚ) = 0 := by simp [h]
    rw [Int.cast_det, he] at hv
    exact (mul_eq_zero.mp hv).resolve_left hc
  · intro h
    have hv : (((Generator.integralLift n N e x 0).det : ℤ) : ℚ) = 0 := by
      rw [Int.cast_det, he, h, mul_zero]
    exact_mod_cast hv

/-- Exact pointwise equality, including points rejected by the original determinant test. -/
theorem atPoint_spec (n N e : ℕ) (x : Fin 3 → ℕ) :
    atPoint n N e x = Generator.atPoint n N e x := by
  simp only [atPoint, determinant_eq, inputTables_denote, Generator.atPoint]
  by_cases hz : (Generator.rationalLift n N e x 0).det = 0
  · simp [hz, (U_det_eq_zero n N e x).mpr hz]
  · have hu := mt (U_det_eq_zero n N e x).mp hz
    simp only [hz, hu, ite_false, Option.some.injEq]
    funext a i j
    rw [tuple_normalized]
    have hh := normalizedEntry_spec ((inputTables n N e x).get 0)
      ((inputTables n N e x).get a.succ) (by simpa using hu) i j
    simp only [inputTables_denote, determinant_eq] at hh
    rw [hh, Generator.tupleAt_integer n N e x hz a]

/-- A computable generator preserving the list and its order. -/
def output (n N e H : ℕ) : Output n where
  dimension := Generator.matrixDimension e
  dimension_pos := Nat.mul_pos (CyclotomicRing.dimension_pos e) (CyclotomicRing.degree_pos e)
  tuples := (Generator.grid H).filterMap fun x => atPoint n N e (fun i => (x i).val + 1)

private theorem output_spec (n N e H : ℕ) : output n N e H = Generator.output n N e H := by
  simp only [output, Generator.output, atPoint_spec]

/-- The executable hitting list for the selected parameter values. -/
def list (n s : ℕ) : Output n :=
  output n (Parameters.truncation n s) (Parameters.exponent n s) (Parameters.gridSize n s)

theorem list_spec (n s : ℕ) : list n s = Generator.list n s := output_spec ..

/-- The complete binary encoding of the executable hitting list. -/
def encoded (n s : ℕ) : List Bool := encodeOutput (list n s)

theorem encoded_spec (n s : ℕ) : encoded n s = encodeOutput (Generator.list n s) := by
  rw [encoded, list_spec]

/-- The hitting property and output-size bounds for the computed list. -/
theorem exact_output (n s : ℕ) (hs : 1 ≤ s) :
    (list n s).dimension ≤ 256 * (n + s + 1) ^ 10 ∧
    (encodeOutput (list n s)).length ≤ PolynomialBounds.outputConstant * (n + s + 1) ^ 104 ∧
    Hits s (list n s) := by
  rw [list_spec]
  exact ⟨Generator.list_dimension_bound n s, Generator.list_output_bound n s,
    Generator.list_hits n s hs⟩

end Rational.ExecutableGenerator

end Cslib.Circuits
