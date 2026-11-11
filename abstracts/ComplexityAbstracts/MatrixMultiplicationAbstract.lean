/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.MatrixMultiplicationBridge

/-! # Matrix multiplication: the exponent is at most 9/4

Over every field of characteristic zero, for every positive real `γ`, exact multiplication
of two `n × n` matrices has nonuniform arithmetic circuits with at most `c n^(9/4 + γ)` gates,
for one positive constant `c` independent of `n` and of the matrix entries. Consequently the
infimum of admissible exponents is at most `9/4`.

**Model.** A circuit is a finite acyclic straight-line program. Each gate reads inputs or
previous gates; outputs select available wires, and values may be reused freely. The allowed
operations are binary addition, binary multiplication, and a nullary constant from the field.
Every gate costs one, including constants and scalar multiplications. Inputs, output selection
and wires cost nothing. Subtraction can use a negative constant and multiplication; division
is not a gate. Correctness is exact for every pair of matrices, rather than probabilistic or
approximate. Different sizes may use different circuits: no uniform circuit generator is asserted.

Only the elementary arithmetic signature and its interpretation from
`Complexity.Computability.Circuit.Arithmetic` are explicitly allowed. Their three operations
and costs are described above; the circuit datatype, evaluation and total gate count are
upstream `Cslib`. Matrix multiplication, admissibility and the infimum are defined below,
without referring to the implementation's exponent definitions. A reader needs only these
statements and definitions and the stated elementary model to inspect the claim. Lean checks
the proofs through `MatrixMultiplicationBridge`; `#check_abstract` audits this boundary.

**Source and limits.** This transfers the field-circuit consequence of Rafael Pass,
*Matrix Multiplication from Polynomial Packings*, arXiv:2610.28627v2 (30 October 2026),
Theorem 1.1 (printed p. 1; PDF p. 2), via block recursion in Section 4.3. Pass attributes the
preceding exponent bound over complex scalars to OpenAI and gives a constructive integer
algorithm. Here the proved scope is every characteristic-zero field (integer interpolation
nodes require characteristic zero), exact scalar arithmetic and existential circuits.
The paper's integer algorithm and integer bit complexity are not certified. The construction
is galactic; no numerical constants, practical sizes, computable extraction of its block
parameters, or uniform algorithm follow from these statements. The mathematical implementation
is by Aviv Bar Natan; this abstract transfers its proved endpoint without adding new mathematics.

## References

* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], v2,
  Theorem 1.1 and Section 4.3
-/

namespace ComplexityAbstracts.MatrixMultiplicationAbstract

/-- The entries of a square matrix in row-major order. -/
def entries {K : Type*} {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (t : Fin (n * n)) : K :=
  A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

/-- Exact matrix multiplication: inputs are all entries of `A`, then all entries of `B`;
outputs are all entries of their product. The circuit must work for every `A` and `B`. -/
def ComputesProduct {K : Type*} [Field K] {n : ℕ}
    (C : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature K)
      (n * n + n * n) (n * n)) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) K,
    C.eval (Cslib.Circuits.arithInterpretation K) (Fin.append (entries A) (entries B)) =
      entries (A * B)

/-- An exponent is admissible if every positive slack admits a positive size constant,
shared by all positive dimensions; the circuit may depend on the dimension and slack. -/
def AdmissibleExponent (K : Type*) [Field K] (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ C : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature K)
      (n * n + n * n) (n * n),
      ComputesProduct C ∧ (C.size : ℝ) ≤ c * (n : ℝ) ^ (τ + ε)

/-- The exponent is the real infimum of the admissible exponents. The set is nonempty
(the cubic algorithm suffices) and bounded below by two in this model. -/
noncomputable def exponent (K : Type*) [Field K] : ℝ :=
  sInf {τ : ℝ | AdmissibleExponent K τ}

/-- For every positive slack, exact nonuniform matrix multiplication has total gate count
`O(n^(9/4 + γ))`, over any field of characteristic zero. -/
theorem circuits_nine_quarters (K : Type*) [Field K] [CharZero K] (γ : ℝ) (hγ : 0 < γ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ C : Cslib.Circuits.Circuit (Cslib.Circuits.arithSignature K)
        (n * n + n * n) (n * n),
        ComputesProduct C ∧ (C.size : ℝ) ≤ c * (n : ℝ) ^ ((9 : ℝ) / 4 + γ) :=
  MatrixMultiplicationBridge.circuits_nine_quarters K γ hγ

/-- The matrix multiplication exponent over every characteristic-zero field is at most 9/4. -/
theorem exponent_le_nine_quarters (K : Type*) [Field K] [CharZero K] :
    exponent K ≤ 9 / 4 :=
  MatrixMultiplicationBridge.exponent_le_nine_quarters K

end ComplexityAbstracts.MatrixMultiplicationAbstract

/--
info: abstract audit passed for `ComplexityAbstracts.MatrixMultiplicationAbstract`: 6 root
  declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.MatrixMultiplicationAbstract allowing [
  Complexity.Computability.Circuit.Arithmetic
]
