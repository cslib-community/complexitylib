/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Foundations.LinearAlgebra.Tensor.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Computability.Circuit.Synthesis
import Complexity.Computability.Circuit.Arithmetic.VP

/-!
# The exponent of matrix multiplication

A circuit `C : Circuit (arithSignature K) (n * n + n * n) (n * n)` *computes `n × n` matrix
multiplication* (`ComputesMatMul`) when, on the entries of `A` followed by those of `B`, its
outputs are the entries of `A * B`, in the row-major numbering `finProdFinEquiv`. Its size
`C.size` counts the gates: additions, multiplications and constants, each of cost one.

A real `τ` is an *admissible exponent* (`AdmissibleExponent K τ`) when for every `ε > 0` there is
a constant `c` such that, for every `n ≥ 1`, some circuit of size at most `c n ^ (τ + ε)`
computes `n × n` matrix multiplication. The *exponent of matrix multiplication* `omega K` is the
infimum of the admissible exponents. This is the definition of [Pass][Pass2026], §1, with
arithmetic circuits over `K` in place of integer arithmetic, and the formal arithmetic model of
[Bürgisser, Clausen and Shokrollahi][BurgisserClausenShokrollahi1997], Chapter 15.

**Block recursion** (`admissibleExponent_of_rank`, [Strassen][Strassen1969]; [Pass][Pass2026],
proof of Theorem 1.1): a bilinear algorithm with `r` multiplications for `v × v` matrices, that is
`Tensor.Rank r (Tensor.mm v v v)`, gives circuits of size `O(n ^ τ)` whenever `r ≤ v ^ τ` and
`τ > 2`: apply the algorithm to `v × v` arrays of blocks, recursively, with linear encoding and
decoding of the blocks costing `O(r n ^ 2)` per level.

## Main definitions

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.ComputesMatMul`
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.AdmissibleExponent`
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega`

## Main results

* `Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_of_rank`: block recursion.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.two_le_of_admissibleExponent`: every
  admissible exponent is at least `2`, so `omega` is a true infimum.
* `Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_of_admissibleExponent`.

## References

* [V. Strassen, *Gaussian elimination is not optimal*][Strassen1969]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 15
* [R. Pass, *Matrix Multiplication from Polynomial Packings*][Pass2026], §1 and §4.3
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic.MatrixMultiplication

open Cslib.Circuits Cslib.Tensor

variable (K : Type*) [CommSemiring K]

/-- The entry `t` of a matrix, numbered row-major. -/
def entry {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (t : Fin (n * n)) : K :=
  A (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2

/-- The inputs of a matrix multiplication circuit: the entries of `A` followed by those of
`B`. -/
def matrixInputs {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : Fin (n * n + n * n) → K :=
  Fin.append (entry K A) (entry K B)

/-- `C` computes `n × n` matrix multiplication: on the entries of `A` and `B` it outputs the
entries of `A * B`. -/
def ComputesMatMul {n : ℕ} (C : Circuit (arithSignature K) (n * n + n * n) (n * n)) : Prop :=
  ∀ A B : Matrix (Fin n) (Fin n) K,
    C.eval (arithInterpretation K) (matrixInputs K A B) = entry K (A * B)

/-- `τ` is an admissible exponent: for every `ε > 0`, circuits of size `O(n ^ (τ + ε))` compute
`n × n` matrix multiplication for every `n ≥ 1`. -/
def AdmissibleExponent (τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ (C.size : ℝ) ≤ c * (n : ℝ) ^ (τ + ε)

/-- **The exponent of matrix multiplication**: the infimum of the admissible exponents. -/
noncomputable def omega : ℝ :=
  sInf {τ : ℝ | AdmissibleExponent K τ}

variable {K}

/-- Admissibility is monotone. -/
theorem AdmissibleExponent.mono {τ τ' : ℝ} (h : AdmissibleExponent K τ) (hτ : τ ≤ τ') :
    AdmissibleExponent K τ' := by
  intro ε hε
  obtain ⟨c, hc, hC⟩ := h ε hε
  refine ⟨c, hc, fun n hn => ?_⟩
  obtain ⟨C, hC, hsize⟩ := hC n hn
  refine ⟨C, hC, hsize.trans (mul_le_mul_of_nonneg_left ?_ hc.le)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)

/-! ### Circuits from synthesis bounds -/

section Helpers

variable {n : ℕ}

/-- The matrix `A` encoded by an input vector. -/
private def leftMatrix (x : Fin (n * n + n * n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x (Fin.castAdd (n * n) (finProdFinEquiv (i, j)))

/-- The matrix `B` encoded by an input vector. -/
private def rightMatrix (x : Fin (n * n + n * n) → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x (Fin.natAdd (n * n) (finProdFinEquiv (i, j)))

/-- Entry `t` of the product of the two encoded matrices, as a function of the inputs. -/
private def matMulFun (n : ℕ) (t : Fin (n * n)) (x : Fin (n * n + n * n) → K) : K :=
  entry K (leftMatrix x * rightMatrix x) t

omit [CommSemiring K] in
private theorem leftMatrix_matrixInputs (A B : Matrix (Fin n) (Fin n) K) :
    leftMatrix (matrixInputs K A B) = A := by
  ext i j
  simp only [leftMatrix, Matrix.of_apply, matrixInputs, Fin.append_left, entry,
    Equiv.symm_apply_apply]

omit [CommSemiring K] in
private theorem rightMatrix_matrixInputs (A B : Matrix (Fin n) (Fin n) K) :
    rightMatrix (matrixInputs K A B) = B := by
  ext i j
  simp only [rightMatrix, Matrix.of_apply, matrixInputs, Fin.append_right, entry,
    Equiv.symm_apply_apply]

omit [CommSemiring K] in
private theorem leftMatrix_apply (x : Fin (n * n + n * n) → K) (i j : Fin n) :
    leftMatrix x i j = x (Fin.castAdd (n * n) (finProdFinEquiv (i, j))) := rfl

omit [CommSemiring K] in
private theorem rightMatrix_apply (x : Fin (n * n + n * n) → K) (i j : Fin n) :
    rightMatrix x i j = x (Fin.natAdd (n * n) (finProdFinEquiv (i, j))) := rfl

omit [CommSemiring K] in
private theorem leftMatrix_mem_inputs (i j : Fin n) :
    (fun x : Fin (n * n + n * n) → K => leftMatrix x i j) ∈ inputs (n * n + n * n) :=
  ⟨Fin.castAdd (n * n) (finProdFinEquiv (i, j)), rfl⟩

omit [CommSemiring K] in
private theorem rightMatrix_mem_inputs (i j : Fin n) :
    (fun x : Fin (n * n + n * n) → K => rightMatrix x i j) ∈ inputs (n * n + n * n) :=
  ⟨Fin.natAdd (n * n) (finProdFinEquiv (i, j)), rfl⟩

/-- A synthesis bound for the entries of the product gives a circuit computing matrix
multiplication within the bound. -/
private theorem exists_computesMatMul_of_synthesis {cost : ℕ}
    (h : Synthesis (arithInterpretation K) (inputs (n * n + n * n)) (Set.range (matMulFun n))
      cost) :
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ C.size ≤ cost := by
  obtain ⟨C, hC, hsize⟩ := h.exists_circuit_outputs
  refine ⟨C, fun A B => ?_, hsize⟩
  rw [hC]
  funext t
  simp only [matMulFun, leftMatrix_matrixInputs, rightMatrix_matrixInputs]

/-- Zero is available at the cost of one gate. -/
private theorem synthesis_zero {s : Set ((Fin n → K) → K)} :
    Synthesis (arithInterpretation K) s {fun _ => (0 : K)} 1 :=
  Synthesis.arith_const (constant := id) (0 : K)

/-- Multiplying an available function by a constant costs two gates. -/
private theorem synthesis_const_mul {s : Set ((Fin n → K) → K)} (a : K)
    {f : (Fin n → K) → K} (hf : f ∈ s) :
    Synthesis (arithInterpretation K) s {fun x => a * f x} 2 :=
  Synthesis.combine (Synthesis.arith_const (constant := id) a) (Synthesis.of_mem hf)
    (Synthesis.arith_mul (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl))

/-- The trivial algorithm: `n × n` matrix multiplication with `2 n ^ 3 + 1` gates. -/
private theorem exists_circuit_trivial (n : ℕ) :
    ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n),
      ComputesMatMul K C ∧ C.size ≤ 2 * n ^ 3 + 1 := by
  refine exists_computesMatMul_of_synthesis (n := n) ?_
  have h0 : (fun _ => (0 : K)) ∈ inputs (n * n + n * n) ∪ {fun _ => (0 : K)} :=
    Set.mem_union_right _ rfl
  have hentry (t : Fin (n * n)) :
      Synthesis (arithInterpretation K) (inputs (n * n + n * n) ∪ {fun _ => (0 : K)})
        {matMulFun n t} (n * 2) := by
    have := Synthesis.arith_sum (constant := id) (Finset.univ : Finset (Fin n))
      (fun j x => leftMatrix x (finProdFinEquiv.symm t).1 j *
        rightMatrix x j (finProdFinEquiv.symm t).2) (fun _ => 1) h0 fun j _ =>
      Synthesis.arith_mul (Set.mem_union_left _ (leftMatrix_mem_inputs _ _))
        (Set.mem_union_left _ (rightMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) (by simp)
    funext x
    simp only [matMulFun, entry, Matrix.mul_apply]
  have := synthesis_zero.trans (Synthesis.family _ _ hentry)
  refine this.mono Set.Subset.rfl Set.Subset.rfl ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith [Nat.zero_le n]

end Helpers

/-- The trivial algorithm: `3` is admissible. -/
theorem admissibleExponent_three : AdmissibleExponent K 3 := by
  intro ε hε
  refine ⟨3, by norm_num, fun n hn => ?_⟩
  obtain ⟨C, hC, hsize⟩ := exists_circuit_trivial (K := K) n
  refine ⟨C, hC, ?_⟩
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h3 : (n : ℝ) ^ (3 : ℕ) ≤ (n : ℝ) ^ (3 + ε) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn' (by push_cast; linarith)
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (3 : ℕ) := one_le_pow₀ hn'
  calc (C.size : ℝ) ≤ ((2 * n ^ 3 + 1 : ℕ) : ℝ) := by exact_mod_cast hsize
    _ = 2 * (n : ℝ) ^ (3 : ℕ) + 1 := by push_cast; ring
    _ ≤ 3 * (n : ℝ) ^ (3 : ℕ) := by linarith
    _ ≤ 3 * (n : ℝ) ^ (3 + ε) := by linarith

section LowerBound

variable [Nontrivial K] {n : ℕ} {C : Circuit (arithSignature K) (n * n + n * n) (n * n)}

/-- The output wire of an entry of the product is a gate, not an input. -/
private theorem exists_outputs_eq_gate (hC : ComputesMatMul K C) (t : Fin (n * n)) :
    ∃ j, C.outputs t = Wire.gate j := by
  rcases ht : C.outputs t with i | j
  · exfalso
    have key (A B : Matrix (Fin n) (Fin n) K) : entry K (A * B) t = matrixInputs K A B i := by
      rw [← congrFun (hC A B) t]
      change C.program.trace _ _ (C.outputs t) = _
      rw [ht, Program.trace_input]
    revert ht key
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> intro ht key
    · have := key (Matrix.of fun _ _ => 1) 0
      simp only [Matrix.mul_zero, entry, Matrix.zero_apply, matrixInputs, Fin.append_left,
        Matrix.of_apply] at this
      exact zero_ne_one this
    · have := key 0 (Matrix.of fun _ _ => 1)
      simp only [Matrix.zero_mul, entry, Matrix.zero_apply, matrixInputs, Fin.append_right,
        Matrix.of_apply] at this
      exact zero_ne_one this
  · exact ⟨j, rfl⟩

/-- Distinct entries of the product are carried by distinct wires. -/
private theorem outputs_injective (hC : ComputesMatMul K C) : Function.Injective C.outputs := by
  intro t t' htt'
  by_contra hne
  have key (A B : Matrix (Fin n) (Fin n) K) : entry K (A * B) t = entry K (A * B) t' := by
    rw [← congrFun (hC A B) t, ← congrFun (hC A B) t']
    change C.program.trace _ _ (C.outputs t) = C.program.trace _ _ (C.outputs t')
    rw [htt']
  have := key 1 (Matrix.of fun a b => if (a, b) = finProdFinEquiv.symm t then 1 else 0)
  have hne' : finProdFinEquiv.symm t' ≠ finProdFinEquiv.symm t :=
    fun h => hne (finProdFinEquiv.symm.injective h).symm
  rw [Matrix.one_mul] at this
  simp only [entry, Matrix.of_apply, Prod.mk.eta, ite_true, hne', ite_false] at this
  exact one_ne_zero this

/-- A circuit computing `n × n` matrix multiplication has at least `n ^ 2` gates. -/
private theorem mul_self_le_size (hC : ComputesMatMul K C) : n * n ≤ C.size := by
  have := Finset.card_le_card_of_injOn C.outputs (s := Finset.univ)
    (t := Finset.univ.map ⟨Wire.gate, fun _ _ h => Wire.gate.inj h⟩) ?_
    (outputs_injective hC).injOn
  · simpa using this
  · intro t _
    obtain ⟨j, hj⟩ := exists_outputs_eq_gate hC t
    rw [hj]
    exact Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)

end LowerBound

/-- Every admissible exponent is at least `2`: a circuit computing `n × n` matrix multiplication
has at least `n ^ 2` gates, one for each output, since the entries of `A * B` are pairwise
distinct functions of the inputs and none is an input. -/
theorem two_le_of_admissibleExponent [Nontrivial K] {τ : ℝ} (h : AdmissibleExponent K τ) :
    2 ≤ τ := by
  by_contra hτ
  set ε : ℝ := (2 - τ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨c, hc, hC⟩ := h ε hε0
  -- every `n ≥ 1` satisfies `n ^ ε ≤ c`
  have hle (n : ℕ) (hn : 1 ≤ n) : (n : ℝ) ^ ε ≤ c := by
    obtain ⟨C, hC, hsize⟩ := hC n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : (n : ℝ) ^ (τ + ε) * (n : ℝ) ^ ε ≤ c * (n : ℝ) ^ (τ + ε) := by
      rw [← Real.rpow_add hn']
      have h2 : τ + ε + ε = 2 := by rw [hε]; ring
      rw [h2, Real.rpow_two]
      calc (n : ℝ) ^ 2 = ((n * n : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (C.size : ℝ) := by exact_mod_cast mul_self_le_size hC
        _ ≤ c * (n : ℝ) ^ (τ + ε) := hsize
    have hpos : 0 < (n : ℝ) ^ (τ + ε) := Real.rpow_pos_of_pos hn' _
    rw [mul_comm c] at hsq
    exact le_of_mul_le_mul_left hsq hpos
  -- but `n ^ ε` exceeds `c` for `n` beyond `c ^ (1 / ε)`
  set n : ℕ := ⌈c ^ (1 / ε)⌉₊ + 1 with hn
  have hcn : c ^ (1 / ε) < n := by
    rw [hn, Nat.cast_add, Nat.cast_one]
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hlt : c < (n : ℝ) ^ ε := by
    calc c = (c ^ (1 / ε)) ^ ε := by
          rw [← Real.rpow_mul hc.le, one_div_mul_cancel hε0.ne', Real.rpow_one]
      _ < (n : ℝ) ^ ε := Real.rpow_lt_rpow (Real.rpow_nonneg hc.le _) hcn hε0
  exact absurd (hle n (by omega)) (not_le.mpr hlt)

theorem omega_le_of_admissibleExponent [Nontrivial K] {τ : ℝ} (h : AdmissibleExponent K τ) :
    omega K ≤ τ :=
  csInf_le ⟨2, fun _ hτ => two_le_of_admissibleExponent hτ⟩ h

/-! ### Block recursion -/

section BlockRecursion

variable {v r m : ℕ}

/-- The bilinear map of the unit tensor is coordinatewise multiplication. -/
private theorem bil_unit (u w : Fin r → K) (ν : Fin r) :
    (unit r : Tensor K _ _ _).bil u w ν = u ν * w ν := by
  simp [Tensor.bil, unit_apply, ite_and, ite_mul, Finset.sum_ite_eq']

/-- A bilinear algorithm with `r` multiplications for `v × v` matrices: encoders `α`, `β` and a
decoder `γ` with `(A * B) i k = ∑ ν, γ (i, k) ν * (∑ x, α ν x * A x) * (∑ y, β ν y * B y)`. -/
private theorem exists_encoders (hr : Rank r (mm v v v : Tensor K _ _ _)) :
    ∃ (α β : Matrix (Fin r) (Fin v × Fin v) K) (γ : Matrix (Fin v × Fin v) (Fin r) K),
      ∀ (A B : Fin v × Fin v → K) (c : Fin v × Fin v),
        ∑ j, A (c.1, j) * B (j, c.2) =
          ∑ ν, γ c ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y)) := by
  obtain ⟨α, β, γ, h⟩ := hr
  refine ⟨α, β, γ, fun A B c => ?_⟩
  have := congrFun (congrArg (fun T : Tensor K _ _ _ => T.bil A B) h) c
  simp only [bil_restrict, bil_mm, Matrix.mulVec, dotProduct, bil_unit] at this
  exact this.symm

/-- The `ν`-th encoded block of a `v m × v m` matrix, viewed as a `v × v` array of `m × m`
blocks: `∑ x, α ν x • A_x`. -/
private def encode (α : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (A : Matrix (Fin (v * m)) (Fin (v * m)) K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun a l => ∑ p : Fin v × Fin v,
    α ν p * A (finProdFinEquiv (p.1, a)) (finProdFinEquiv (p.2, l))

/-- The bilinear algorithm applied blockwise computes the product of `v m × v m` matrices. -/
private theorem mul_apply_eq_sum_encode {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K}
    (hid : ∀ (A B : Fin v × Fin v → K) (c : Fin v × Fin v),
      ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, γ c ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y)))
    (A B : Matrix (Fin (v * m)) (Fin (v * m)) K) (i k : Fin v) (a b : Fin m) :
    (A * B) (finProdFinEquiv (i, a)) (finProdFinEquiv (k, b)) =
      ∑ ν, γ (i, k) ν * (encode α ν A * encode β ν B) a b := by
  have h1 : (A * B) (finProdFinEquiv (i, a)) (finProdFinEquiv (k, b)) =
      ∑ l : Fin m, ∑ j : Fin v, A (finProdFinEquiv (i, a)) (finProdFinEquiv (j, l)) *
        B (finProdFinEquiv (j, l)) (finProdFinEquiv (k, b)) := by
    rw [Matrix.mul_apply, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∀ ν, (encode α ν A * encode β ν B) a b =
      ∑ l : Fin m, (∑ p, α ν p * A (finProdFinEquiv (p.1, a)) (finProdFinEquiv (p.2, l))) *
        (∑ q, β ν q * B (finProdFinEquiv (q.1, l)) (finProdFinEquiv (q.2, b))) := fun ν => by
    simp only [Matrix.mul_apply, encode, Matrix.of_apply]
  rw [h1]
  simp only [h2]
  conv_rhs => enter [2, ν]; rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => hid (fun p => A (finProdFinEquiv (p.1, a))
    (finProdFinEquiv (p.2, l))) (fun q => B (finProdFinEquiv (q.1, l)) (finProdFinEquiv (q.2, b)))
    (i, k)

/-- `n × n` matrix multiplication has a circuit of size at most `s`. -/
private def HasCircuit (n s : ℕ) : Prop :=
  ∃ C : Circuit (arithSignature K) (n * n + n * n) (n * n), ComputesMatMul K C ∧ C.size ≤ s

private theorem HasCircuit.congr {n n' s : ℕ} (h : n = n') (hC : HasCircuit (K := K) n s) :
    HasCircuit (K := K) n' s := by
  subst h
  exact hC

private theorem HasCircuit.mono {n s s' : ℕ} (hC : HasCircuit (K := K) n s) (h : s ≤ s') :
    HasCircuit (K := K) n s' :=
  let ⟨C, hC, hs⟩ := hC
  ⟨C, hC, hs.trans h⟩

/-- The inputs of the `ν`-th block product, encoded from the inputs of the `v m × v m`
multiplication: the entries of `encode α ν A` followed by those of `encode β ν B`. -/
private def encInputs (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (i : Fin (m * m + m * m)) (x : Fin (v * m * (v * m) + v * m * (v * m)) → K) : K :=
  matrixInputs K (encode α ν (leftMatrix x)) (encode β ν (rightMatrix x)) i

/-- Each encoded input is a linear combination of `v ^ 2` inputs: `3 v ^ 2` gates. -/
private theorem synthesis_encInputs (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r)
    (i : Fin (m * m + m * m)) :
    Synthesis (arithInterpretation K)
      (inputs (v * m * (v * m) + v * m * (v * m)) ∪ {fun _ => (0 : K)}) {encInputs α β ν i}
      (∑ _p : Fin v × Fin v, (2 + 1)) := by
  have h0 : (fun _ => (0 : K)) ∈
      inputs (v * m * (v * m) + v * m * (v * m)) ∪ {fun _ => (0 : K)} :=
    Set.mem_union_right _ rfl
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · have := Synthesis.arith_sum (constant := id) (Finset.univ : Finset (Fin v × Fin v))
      (fun p x => α ν p * leftMatrix x (finProdFinEquiv (p.1, (finProdFinEquiv.symm i).1))
        (finProdFinEquiv (p.2, (finProdFinEquiv.symm i).2))) (fun _ => 2) h0 fun p _ =>
        synthesis_const_mul (α ν p) (Set.mem_union_left _ (leftMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    simp only [encInputs, matrixInputs, Fin.append_left, entry, encode, Matrix.of_apply]
  · have := Synthesis.arith_sum (constant := id) (Finset.univ : Finset (Fin v × Fin v))
      (fun p x => β ν p * rightMatrix x (finProdFinEquiv (p.1, (finProdFinEquiv.symm i).1))
        (finProdFinEquiv (p.2, (finProdFinEquiv.symm i).2))) (fun _ => 2) h0 fun p _ =>
        synthesis_const_mul (β ν p) (Set.mem_union_left _ (rightMatrix_mem_inputs _ _))
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    simp only [encInputs, matrixInputs, Fin.append_right, entry, encode, Matrix.of_apply]

/-- The entries of the `ν`-th block product, as functions of the inputs. -/
private def blockProd (α β : Matrix (Fin r) (Fin v × Fin v) K) (ν : Fin r) (t : Fin (m * m))
    (x : Fin (v * m * (v * m) + v * m * (v * m)) → K) : K :=
  entry K (encode α ν (leftMatrix x) * encode β ν (rightMatrix x)) t

/-- A circuit for `m × m` multiplication, fed with the encoded inputs, computes the block
products. -/
private theorem synthesis_blockProd {α β : Matrix (Fin r) (Fin v × Fin v) K} (ν : Fin r)
    {C : Circuit (arithSignature K) (m * m + m * m) (m * m)} (hC : ComputesMatMul K C)
    {s : Set ((Fin (v * m * (v * m) + v * m * (v * m)) → K) → K)}
    (hs : ∀ i, encInputs α β ν i ∈ s) :
    Synthesis (arithInterpretation K) s (Set.range (blockProd α β ν)) C.size := by
  have := Synthesis.circuit (I := arithInterpretation K) C (encInputs α β ν) hs
  refine this.mono Set.Subset.rfl (le_of_eq ?_) le_rfl
  congr 1
  funext t x
  simp only [blockProd]
  rw [← congrFun (hC (encode α ν (leftMatrix x)) (encode β ν (rightMatrix x))) t]
  rfl

/-- The entries of the `v m × v m` product are linear combinations of the block products. -/
private theorem matMulFun_eq_sum {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K}
    (hid : ∀ (A B : Fin v × Fin v → K) (c : Fin v × Fin v),
      ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, γ c ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y)))
    (t : Fin (v * m * (v * m))) (x : Fin (v * m * (v * m) + v * m * (v * m)) → K) :
    matMulFun (v * m) t x =
      ∑ ν, γ ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).1,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1) ν *
        blockProd α β ν (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).2,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).2)) x := by
  simp only [matMulFun, blockProd, entry, Equiv.symm_apply_apply]
  conv_lhs => rw [← finProdFinEquiv.apply_symm_apply (finProdFinEquiv.symm t).1,
    ← finProdFinEquiv.apply_symm_apply (finProdFinEquiv.symm t).2]
  exact mul_apply_eq_sum_encode hid _ _ _ _ _ _

/-- **The block step**: a circuit of size `s` for `m × m` matrices gives one of size
`r s + 9 r (v m) ^ 2 + 1` for `v m × v m` matrices: encode the `2 r` block inputs
(`6 r v ^ 2 m ^ 2` gates), compute the `r` block products with the given circuit, and decode the
`(v m) ^ 2` outputs (`3 r (v m) ^ 2` gates). -/
private theorem hasCircuit_mul {α β : Matrix (Fin r) (Fin v × Fin v) K}
    {γ : Matrix (Fin v × Fin v) (Fin r) K}
    (hid : ∀ (A B : Fin v × Fin v → K) (c : Fin v × Fin v),
      ∑ j, A (c.1, j) * B (j, c.2) = ∑ ν, γ c ν * ((∑ x, α ν x * A x) * (∑ y, β ν y * B y)))
    {s : ℕ} (hm : HasCircuit (K := K) m s) :
    HasCircuit (K := K) (v * m) (r * s + 9 * r * (v * m) ^ 2 + 1) := by
  classical
  obtain ⟨C, hC, hs⟩ := hm
  refine exists_computesMatMul_of_synthesis (n := v * m) ?_
  -- the available functions after each stage
  set s₀ := inputs (v * m * (v * m) + v * m * (v * m)) (U := K) with hs₀
  set s₁ : Set ((Fin (v * m * (v * m) + v * m * (v * m)) → K) → K) := {fun _ => 0} with hs₁
  set s₂ := Set.range fun p : Fin r × Fin (m * m + m * m) => encInputs α β p.1 p.2 with hs₂
  set s₃ := ⋃ ν, Set.range (blockProd α β ν) with hs₃
  have S₀ : Synthesis (arithInterpretation K) s₀ s₁ 1 := synthesis_zero
  have S₁ : Synthesis (arithInterpretation K) (s₀ ∪ s₁) s₂
      (∑ _p : Fin r × Fin (m * m + m * m), ∑ _q : Fin v × Fin v, (2 + 1)) :=
    Synthesis.family _ _ fun p => synthesis_encInputs α β p.1 p.2
  have henc : ∀ ν i, encInputs α β ν i ∈ s₀ ∪ (s₁ ∪ s₂) := fun ν i => by
    simp only [hs₂, Set.mem_union, Set.mem_range]
    exact Or.inr (Or.inr ⟨(ν, i), rfl⟩)
  have S₂ : Synthesis (arithInterpretation K) (s₀ ∪ (s₁ ∪ s₂)) s₃ (∑ _ν : Fin r, C.size) :=
    Synthesis.iUnion _ _ fun ν => synthesis_blockProd ν hC (henc ν)
  have h0 : (fun _ => (0 : K)) ∈ s₀ ∪ (s₁ ∪ s₂ ∪ s₃) := by simp [hs₁]
  have hbp : ∀ ν t, blockProd α β ν t ∈ s₀ ∪ (s₁ ∪ s₂ ∪ s₃) := fun ν t => by
    simp only [hs₃, Set.mem_union, Set.mem_iUnion, Set.mem_range]
    exact Or.inr (Or.inr ⟨ν, t, rfl⟩)
  have S₃ : Synthesis (arithInterpretation K) (s₀ ∪ (s₁ ∪ s₂ ∪ s₃))
      (Set.range (matMulFun (v * m))) (∑ _t : Fin (v * m * (v * m)), ∑ _ν : Fin r, (2 + 1)) := by
    refine Synthesis.family _ _ fun t => ?_
    have := Synthesis.arith_sum (constant := id) (Finset.univ : Finset (Fin r))
      (fun ν x => γ ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).1,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).1) ν *
        blockProd α β ν (finProdFinEquiv ((finProdFinEquiv.symm (finProdFinEquiv.symm t).1).2,
          (finProdFinEquiv.symm (finProdFinEquiv.symm t).2).2)) x) (fun _ => 2) h0 fun ν _ =>
        synthesis_const_mul _ (hbp ν _)
    refine this.mono Set.Subset.rfl (Set.singleton_subset_iff.mpr ?_) le_rfl
    funext x
    exact matMulFun_eq_sum hid t x
  have := ((S₀.comp S₁).comp S₂).comp S₃
  refine this.mono Set.Subset.rfl Set.subset_union_right ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  have := Nat.mul_le_mul_left r hs
  nlinarith

/-- Zero padding of a matrix to a larger side. -/
private def padMatrix {n : ℕ} (N : ℕ) (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin N) (Fin N) K :=
  Matrix.of fun i j => if h : i.val < n ∧ j.val < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

private theorem padMatrix_castLE {n N : ℕ} (hnN : n ≤ N) (A : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : padMatrix N A (Fin.castLE hnN i) (Fin.castLE hnN j) = A i j := by
  rw [padMatrix, Matrix.of_apply, dite_eq_left ⟨i.isLt, j.isLt⟩]
  rfl

/-- The product of zero-padded matrices is the zero-padded product. -/
private theorem padMatrix_mul {n N : ℕ} (hnN : n ≤ N) (A B : Matrix (Fin n) (Fin n) K)
    (i k : Fin n) :
    (padMatrix N A * padMatrix N B) (Fin.castLE hnN i) (Fin.castLE hnN k) = (A * B) i k := by
  simp only [Matrix.mul_apply]
  symm
  calc ∑ j, A i j * B j k
      = ∑ j, padMatrix N A (Fin.castLE hnN i) (Fin.castLE hnN j) *
          padMatrix N B (Fin.castLE hnN j) (Fin.castLE hnN k) := by
        simp only [padMatrix_castLE]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin n)).map (Fin.castLEEmb hnN),
          padMatrix N A (Fin.castLE hnN i) j * padMatrix N B j (Fin.castLE hnN k) := by
        rw [Finset.sum_map]
        rfl
    _ = ∑ j, padMatrix N A (Fin.castLE hnN i) j * padMatrix N B j (Fin.castLE hnN k) := by
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
        have hjn : ¬ j.val < n := fun h => hj (Finset.mem_map.2 ⟨⟨j.val, h⟩, Finset.mem_univ _,
          Fin.ext rfl⟩)
        simp [padMatrix, hjn]

/-- **Padding**: a circuit for `N × N` matrices gives one for `n × n` matrices, `n ≤ N`, with one
more gate (the zero fed to the padding entries). -/
private theorem hasCircuit_of_le {n N s : ℕ} (hnN : n ≤ N) (hN : HasCircuit (K := K) N s) :
    HasCircuit (K := K) n (s + 1) := by
  classical
  obtain ⟨C, hC, hs⟩ := hN
  refine exists_computesMatMul_of_synthesis (n := n) ?_
  let g : Fin (N * N + N * N) → (Fin (n * n + n * n) → K) → K := fun i x =>
    matrixInputs K (padMatrix N (leftMatrix x)) (padMatrix N (rightMatrix x)) i
  have hg : ∀ i, g i ∈ inputs (n * n + n * n) ∪ {fun _ => (0 : K)} := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · by_cases h : (finProdFinEquiv.symm i).1.val < n ∧ (finProdFinEquiv.symm i).2.val < n
      · refine Set.mem_union_left _ ?_
        convert leftMatrix_mem_inputs (K := K) (n := n) ⟨_, h.1⟩ ⟨_, h.2⟩ using 1
        funext x
        simp only [g, matrixInputs, Fin.append_left, entry, padMatrix, Matrix.of_apply,
          dite_eq_left h]
      · refine Set.mem_union_right _ ?_
        funext x
        simp only [g, matrixInputs, Fin.append_left, entry, padMatrix, Matrix.of_apply,
          dite_eq_right h]
    · by_cases h : (finProdFinEquiv.symm i).1.val < n ∧ (finProdFinEquiv.symm i).2.val < n
      · refine Set.mem_union_left _ ?_
        convert rightMatrix_mem_inputs (K := K) (n := n) ⟨_, h.1⟩ ⟨_, h.2⟩ using 1
        funext x
        simp only [g, matrixInputs, Fin.append_right, entry, padMatrix, Matrix.of_apply,
          dite_eq_left h]
      · refine Set.mem_union_right _ ?_
        funext x
        simp only [g, matrixInputs, Fin.append_right, entry, padMatrix, Matrix.of_apply,
          dite_eq_right h]
  have := synthesis_zero.comp (Synthesis.circuit (I := arithInterpretation K) C g hg)
  refine this.mono Set.Subset.rfl ?_ (by omega)
  rintro _ ⟨t, rfl⟩
  refine Set.mem_union_right _ ⟨finProdFinEquiv (Fin.castLE hnN (finProdFinEquiv.symm t).1,
    Fin.castLE hnN (finProdFinEquiv.symm t).2), ?_⟩
  funext x
  beta_reduce
  have h1 : (fun i => g i x) =
      matrixInputs K (padMatrix N (leftMatrix x)) (padMatrix N (rightMatrix x)) := rfl
  rw [h1, hC]
  simp only [matMulFun, entry, Equiv.symm_apply_apply, padMatrix_mul]

end BlockRecursion

/-- **Block recursion** ([Strassen][Strassen1969]; [Pass][Pass2026], §4.3): a bilinear algorithm
with `r` multiplications for `v × v` matrices gives circuits of size `O(n ^ τ)` for every `n`,
when `r ≤ v ^ τ` and `2 < τ`. For every `ε > 0`, with `R = v ^ (τ + ε) > r`, the sizes `S j` of
the circuits for `v ^ j × v ^ j` matrices satisfy `S (j + 1) ≤ r S j + 9 r (v ^ (j + 1)) ^ 2 + 1`,
hence `S j ≤ C R ^ j`; a general `n` is padded to the next power of `v`, which is at most
`v n`. -/
theorem admissibleExponent_of_rank {v r : ℕ} (hv : 2 ≤ v) (hr : Rank r (mm v v v : Tensor K _ _ _))
    {τ : ℝ} (hτ : (r : ℝ) ≤ (v : ℝ) ^ τ) (h2 : 2 < τ) : AdmissibleExponent K τ := by
  classical
  obtain ⟨α, β, γ, hid⟩ := exists_encoders hr
  intro ε hε
  have hv1 : (1 : ℝ) < v := by exact_mod_cast hv
  set R : ℝ := (v : ℝ) ^ (τ + ε) with hR
  have hrR : (r : ℝ) < R :=
    hτ.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hv1 (by linarith))
  have hv2R : (v : ℝ) ^ 2 ≤ R := by
    rw [hR, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hv1.le (by push_cast; linarith)
  have hR1 : 1 ≤ R := le_trans (by nlinarith) hv2R
  have hR0 : 0 < R := by linarith
  have hRr : 0 < R - r := by linarith
  -- the constant of the recursion
  set Cc : ℝ := (9 * r + 1) * R / (R - r) + 3 with hCc
  have hCc3 : 3 ≤ Cc := le_add_of_nonneg_left (div_nonneg (by positivity) hRr.le)
  have hCc0 : 0 < Cc := by linarith
  have hCcR : (9 * r + 1) * R ≤ Cc * (R - r) := by
    have key : ((9 * r + 1) * R / (R - r) + 3) * (R - r) = (9 * r + 1) * R + 3 * (R - r) := by
      field_simp
    rw [hCc, key]
    nlinarith
  -- circuits for the powers of `v`
  have step : ∀ j : ℕ, ∃ s : ℕ, HasCircuit (K := K) (v ^ j) s ∧ (s : ℝ) ≤ Cc * R ^ j := by
    intro j
    induction j with
    | zero =>
      obtain ⟨C, hC, hCs⟩ := exists_circuit_trivial (K := K) 1
      refine ⟨3, HasCircuit.congr (pow_zero v).symm ⟨C, hC, hCs.trans (by norm_num)⟩, ?_⟩
      rw [pow_zero, mul_one]
      exact_mod_cast hCc3
    | succ j ih =>
      obtain ⟨s, hs, hsR⟩ := ih
      refine ⟨_, HasCircuit.congr (pow_succ' v j).symm (hasCircuit_mul hid hs), ?_⟩
      have h1 : ((v : ℝ) * (v : ℝ) ^ j) ^ 2 ≤ R ^ (j + 1) := by
        rw [show ((v : ℝ) * (v : ℝ) ^ j) ^ 2 = ((v : ℝ) ^ 2) ^ (j + 1) by ring]
        exact pow_le_pow_left₀ (by positivity) hv2R _
      have h2 : (1 : ℝ) ≤ R ^ (j + 1) := one_le_pow₀ hR1
      have h3 : (r : ℝ) * s ≤ r * (Cc * R ^ j) :=
        mul_le_mul_of_nonneg_left hsR (Nat.cast_nonneg r)
      have h4 : 9 * (r : ℝ) * ((v : ℝ) * (v : ℝ) ^ j) ^ 2 ≤ 9 * r * R ^ (j + 1) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      have h5 : (r : ℝ) * (Cc * R ^ j) + (9 * r + 1) * R ^ (j + 1) ≤ Cc * R ^ (j + 1) := by
        have := mul_le_mul_of_nonneg_left hCcR (pow_nonneg hR0.le j)
        rw [pow_succ]
        nlinarith
      push_cast
      nlinarith
  -- the general `n`: pad to the next power of `v`
  refine ⟨Cc * (v : ℝ) ^ (τ + ε) + 1, by positivity, fun n hn => ?_⟩
  set j := Nat.log v n + 1 with hj
  have hnj : n < v ^ j := Nat.lt_pow_succ_log_self (by omega) n
  have hjn : v ^ j ≤ v * n := by
    rw [hj, pow_succ']
    exact Nat.mul_le_mul_left v (Nat.pow_log_le_self v (by omega))
  obtain ⟨s, hs, hsR⟩ := step j
  obtain ⟨C, hC, hCs⟩ := hasCircuit_of_le hnj.le hs
  refine ⟨C, hC, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ (τ + ε) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  have hRj : R ^ j = ((v ^ j : ℕ) : ℝ) ^ (τ + ε) := by
    rw [hR, ← Real.rpow_mul_natCast (by positivity), mul_comm,
      Real.rpow_natCast_mul (by positivity)]
    push_cast
    rfl
  have hle : ((v ^ j : ℕ) : ℝ) ^ (τ + ε) ≤ ((v * n : ℕ) : ℝ) ^ (τ + ε) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hjn) (by linarith)
  calc (C.size : ℝ) ≤ s + 1 := by exact_mod_cast hCs
    _ ≤ Cc * R ^ j + 1 := by linarith
    _ ≤ Cc * ((v * n : ℕ) : ℝ) ^ (τ + ε) + 1 := by
      rw [hRj]
      exact add_le_add (mul_le_mul_of_nonneg_left hle hCc0.le) le_rfl
    _ = Cc * (v : ℝ) ^ (τ + ε) * (n : ℝ) ^ (τ + ε) + 1 := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring
    _ ≤ (Cc * (v : ℝ) ^ (τ + ε) + 1) * (n : ℝ) ^ (τ + ε) := by
      have : 0 ≤ Cc * (v : ℝ) ^ (τ + ε) := by positivity
      nlinarith

end Cslib.Circuits.Arithmetic.MatrixMultiplication
