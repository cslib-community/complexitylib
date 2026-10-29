/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Measurement
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Quantum circuits

The state of an `n`-qubit register is a vector of `ℂ^{{0,1}^n}` (`Cslib.Quantum.Qubits`), with
computational basis `|x⟩` (`Cslib.Quantum.ket`) for bit strings `x : Fin n → Bool`. A *gate* is a
unitary matrix on `k` qubits (`Cslib.Quantum.Gate`). Applied to an ordered list `A` of `k` distinct
qubits of the register, written `U[A]` in [Shi][Shi2003], it acts on those qubits and leaves the
others alone (`Cslib.Quantum.PlacedGate`):
`⟨y| U[A] |x⟩ = U(y ∘ A, x ∘ A)` when `y` and `x` agree off `A`, and `0` otherwise
(`Cslib.Quantum.PlacedGate.matrix_apply`). A *circuit* is a sequence of placed gates
(`Cslib.Quantum.Circuit`); its unitary is the product `U_m ⋯ U_1` of its gates, the first gate
acting first (`Cslib.Quantum.Circuit.matrix`), and it acts on states as a linear isometric
equivalence (`Cslib.Quantum.Circuit.eval`).

At the end of a computation the whole register is measured in the computational basis: a unit state
`ψ` gives outcome `y` with probability `|ψ_y|²` (`Cslib.Quantum.measure` and
`Cslib.Quantum.measureProb`, from `Complexity/Foundations/Quantum/Measurement.lean`). This is the
model of [Arora, Barak][AroraBarak09], Chapter 10: pure states, gates on a bounded number of qubits,
and a single final measurement in the computational basis. Mixed states and intermediate
measurements are not modelled; Arora and Barak note that they add no power. A gate set is a set of
gates of any arities (`Cslib.Quantum.Circuit.IsOver`). This file provides the Hadamard gate and the
classical reversible gates (`Cslib.Quantum.Gate.hadamard`, `Cslib.Quantum.Gate.ofPerm`,
`Cslib.Quantum.Gate.not`, `Cslib.Quantum.Gate.cnot`, `Cslib.Quantum.Gate.toffoli`); no particular
gate set is fixed here.

As in the quantum query model (`Complexity/Computability/QueryComplexity/Quantum/Search.lean`),
states are vectors of a Euclidean space over `ℂ`. Gates and circuit unitaries are elements of
Mathlib's `Matrix.unitaryGroup`, acting on states through `Matrix.toEuclideanCLM` and
`Unitary.linearIsometryEquiv` (`Cslib.Quantum.unitaryEquiv`). Placing a `k`-qubit unitary on the
qubits `A` is a monoid homomorphism (`Cslib.Quantum.place`).

## Main definitions

* `Cslib.Quantum.Qubits`: the `n`-qubit state space.
* `Cslib.Quantum.unitaryEquiv`: a unitary matrix as a linear isometric equivalence.
* `Cslib.Quantum.Gate`, `Cslib.Quantum.PlacedGate`: gates, and gates applied to chosen qubits.
* `Cslib.Quantum.splitEquiv`, `Cslib.Quantum.place`: splitting the register along chosen qubits,
  and placing a unitary on them.
* `Cslib.Quantum.Circuit`, `Cslib.Quantum.Circuit.matrix`, `Cslib.Quantum.Circuit.eval`: circuits,
  their unitaries and their action on states.
* `Cslib.Quantum.Circuit.run`, `Cslib.Quantum.Circuit.measure`: the final state of a circuit started
  in a basis state, and the distribution of its measurement.
* `Cslib.Quantum.Circuit.IsOver`: a circuit whose gates lie in a gate set.
* `Cslib.Quantum.Gate.hadamard`, `Cslib.Quantum.Gate.ofPerm`: the Hadamard gate and the classical
  reversible gates, among them `Cslib.Quantum.Gate.not`, `Cslib.Quantum.Gate.cnot` and
  `Cslib.Quantum.Gate.toffoli`.

## Main results

* `Cslib.Quantum.place_apply`, `Cslib.Quantum.PlacedGate.matrix_apply`: the entries of a placed
  unitary.
* `Cslib.Quantum.PlacedGate.eval_ket_apply`: a placed gate maps `|x⟩` to its column `x`.
* `Cslib.Quantum.Circuit.matrix_append`, `Cslib.Quantum.Circuit.eval_append`: running two circuits
  in sequence.
* `Cslib.Quantum.Circuit.norm_eval`: circuits preserve norms.
* `Cslib.Quantum.PlacedGate.eval_ofPerm_ket`: a classical reversible gate permutes basis states.
* `Cslib.Quantum.Gate.hadamard_mul_self`: the Hadamard gate is its own inverse.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [Y. Shi, *Both Toffoli and Controlled-NOT need little help to do universal quantum
  computation*][Shi2003], §2 (arXiv:quant-ph/0205115v2)
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix Finset
open scoped Kronecker

variable {n k : ℕ}

/-! ### States and measurement -/

/-- The state space `ℂ^{{0,1}^n}` of an `n`-qubit register, whose computational basis is indexed by
bit strings `Fin n → Bool`. -/
abbrev Qubits (n : ℕ) := EuclideanSpace ℂ (Fin n → Bool)

/-- A unitary matrix, as a linear isometric equivalence of Euclidean space. -/
noncomputable def unitaryEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  Unitary.linearIsometryEquiv
    ⟨toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ), Unitary.map_mem _ U.2⟩

@[simp] theorem unitaryEquiv_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitaryGroup ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    (unitaryEquiv U ψ).ofLp = (U : Matrix ι ι ℂ) *ᵥ ψ.ofLp :=
  rfl

theorem unitaryEquiv_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (U V : unitaryGroup ι ℂ)
    (ψ : EuclideanSpace ℂ ι) : unitaryEquiv (U * V) ψ = unitaryEquiv U (unitaryEquiv V ψ) := by
  ext y
  simp [mulVec_mulVec]

@[simp] theorem unitaryEquiv_one {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : EuclideanSpace ℂ ι) :
    unitaryEquiv 1 ψ = ψ := by
  ext y
  simp

/-! ### Gates -/

/-- A **quantum gate** on `k` qubits: a unitary matrix indexed by `{0,1}^k`. -/
abbrev Gate (k : ℕ) := unitaryGroup (Fin k → Bool) ℂ

/-- A gate `U[A]` applied to an ordered list `A` of distinct qubits of an `n`-qubit register
[Shi][Shi2003]. -/
structure PlacedGate (n : ℕ) where
  /-- The number of qubits the gate acts on. -/
  arity : ℕ
  /-- The gate. -/
  gate : Gate arity
  /-- The qubits it acts on, in order. -/
  wires : Fin arity ↪ Fin n

/-- Splitting a bit string into its restriction `x ∘ A` to the qubits `A` and its values on the
other qubits. -/
noncomputable def splitEquiv (A : Fin k ↪ Fin n) :
    (Fin n → Bool) ≃ (Fin k → Bool) × ({j // ¬∃ i, A i = j} → Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun j => ∃ i, A i = j) fun _ => Bool).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective A A.injective).symm (Equiv.refl _))
      (Equiv.refl _))

@[simp] theorem splitEquiv_apply_fst (A : Fin k ↪ Fin n) (x : Fin n → Bool) :
    (splitEquiv A x).1 = x ∘ A :=
  rfl

@[simp] theorem splitEquiv_apply_snd (A : Fin k ↪ Fin n) (x : Fin n → Bool) :
    (splitEquiv A x).2 = fun j => x j.1 :=
  rfl

/-- The first component of `splitEquiv A` determines the values on the qubits `A`. -/
@[simp] theorem splitEquiv_symm_apply_wire (A : Fin k ↪ Fin n) (b : Fin k → Bool)
    (r : {j // ¬∃ i, A i = j} → Bool) (i : Fin k) : (splitEquiv A).symm (b, r) (A i) = b i :=
  congrFun (congrArg Prod.fst ((splitEquiv A).apply_symm_apply (b, r))) i

/-- The second component of `splitEquiv A` determines the values off the qubits `A`. -/
theorem splitEquiv_symm_apply_of_not (A : Fin k ↪ Fin n) (b : Fin k → Bool)
    (r : {j // ¬∃ i, A i = j} → Bool) (j : Fin n) (hj : ¬∃ i, A i = j) :
    (splitEquiv A).symm (b, r) j = r ⟨j, hj⟩ :=
  congrFun (congrArg Prod.snd ((splitEquiv A).apply_symm_apply (b, r))) ⟨j, hj⟩

/-- **Placing a unitary on the qubits `A`**: the unitary `U[A] = U ⊗ I` of the whole register,
reindexed along `splitEquiv A`. Placement is multiplicative. -/
noncomputable def place (A : Fin k ↪ Fin n) :
    unitaryGroup (Fin k → Bool) ℂ →* unitaryGroup (Fin n → Bool) ℂ where
  toFun U :=
    ⟨((U : Matrix _ _ ℂ) ⊗ₖ (1 : Matrix ({j // ¬∃ i, A i = j} → Bool) _ ℂ)).submatrix
        (splitEquiv A) (splitEquiv A),
      submatrix_equiv_mem_unitary.mpr (kronecker_mem_unitary U.2 (one_mem _))⟩
  map_one' := Subtype.ext <| by simp [submatrix_one_equiv]
  map_mul' U V := Subtype.ext <| by
    simp only [Submonoid.coe_mul, submatrix_mul_equiv, ← mul_kronecker_mul, mul_one]

/-- **The entries of a placed unitary**: `⟨y| U[A] |x⟩ = U(y ∘ A, x ∘ A)` when `y` and `x` agree
off `A`, and `0` otherwise. -/
theorem place_apply (A : Fin k ↪ Fin n) (U : unitaryGroup (Fin k → Bool) ℂ) (y x : Fin n → Bool) :
    (place A U : Matrix _ _ ℂ) y x =
      if ∀ j, (¬∃ i, A i = j) → y j = x j then (U : Matrix _ _ ℂ) (y ∘ A) (x ∘ A) else 0 := by
  simp only [place, MonoidHom.coe_mk, OneHom.coe_mk, submatrix_apply, kroneckerMap_apply,
    splitEquiv_apply_fst, splitEquiv_apply_snd, Matrix.one_apply, funext_iff, Subtype.forall]
  split_ifs <;> simp

namespace PlacedGate

/-- The unitary `U[A]` of a placed gate on the whole register. -/
noncomputable def matrix (g : PlacedGate n) : unitaryGroup (Fin n → Bool) ℂ :=
  place g.wires g.gate

/-- **The entries of a placed gate**: `⟨y| U[A] |x⟩ = U(y ∘ A, x ∘ A)` when `y` and `x` agree off
`A`, and `0` otherwise. -/
theorem matrix_apply (g : PlacedGate n) (y x : Fin n → Bool) :
    (g.matrix : Matrix _ _ ℂ) y x =
      if ∀ j, (¬∃ i, g.wires i = j) → y j = x j then
        (g.gate : Matrix _ _ ℂ) (y ∘ g.wires) (x ∘ g.wires)
      else 0 :=
  place_apply _ _ _ _

/-- The action of a placed gate on states. -/
noncomputable def eval (g : PlacedGate n) : Qubits n ≃ₗᵢ[ℂ] Qubits n :=
  unitaryEquiv g.matrix

/-- A placed gate maps the basis state `|x⟩` to its column `x`. -/
theorem eval_ket_apply (g : PlacedGate n) (x y : Fin n → Bool) :
    (g.eval (ket x)).ofLp y = (g.matrix : Matrix _ _ ℂ) y x := by
  simp [eval, mulVec, dotProduct]

end PlacedGate

/-! ### Circuits -/

/-- A **quantum circuit** on `n` qubits: a sequence of placed gates, applied first to last. -/
abbrev Circuit (n : ℕ) := List (PlacedGate n)

namespace Circuit

/-- The unitary `U_m ⋯ U_1` of a circuit with gates `U_1, …, U_m`. -/
noncomputable def matrix : Circuit n → unitaryGroup (Fin n → Bool) ℂ
  | [] => 1
  | g :: C => matrix C * g.matrix

@[simp] theorem matrix_nil : matrix ([] : Circuit n) = 1 := rfl

@[simp] theorem matrix_cons (g : PlacedGate n) (C : Circuit n) :
    matrix (g :: C) = matrix C * g.matrix :=
  rfl

/-- Running `C` and then `D` applies `D`'s unitary after `C`'s. -/
@[simp] theorem matrix_append (C D : Circuit n) : matrix (C ++ D) = matrix D * matrix C := by
  induction C with
  | nil => simp
  | cons g C ih => simp [ih, mul_assoc]

/-- The action of a circuit on states. -/
noncomputable def eval (C : Circuit n) : Qubits n ≃ₗᵢ[ℂ] Qubits n :=
  unitaryEquiv (matrix C)

@[simp] theorem eval_nil (ψ : Qubits n) : eval ([] : Circuit n) ψ = ψ := by
  simp [eval]

@[simp] theorem eval_cons (g : PlacedGate n) (C : Circuit n) (ψ : Qubits n) :
    eval (g :: C) ψ = eval C (g.eval ψ) := by
  simp [eval, PlacedGate.eval, unitaryEquiv_mul]

theorem eval_append (C D : Circuit n) (ψ : Qubits n) :
    eval (C ++ D) ψ = eval D (eval C ψ) := by
  simp [eval, unitaryEquiv_mul]

/-- Circuits preserve norms. -/
theorem norm_eval (C : Circuit n) (ψ : Qubits n) : ‖eval C ψ‖ = ‖ψ‖ :=
  (eval C).norm_map ψ

/-- The final state of the circuit started in the basis state `|x⟩`. -/
noncomputable def run (C : Circuit n) (x : Fin n → Bool) : Qubits n :=
  eval C (ket x)

@[simp] theorem norm_run (C : Circuit n) (x : Fin n → Bool) : ‖run C x‖ = 1 := by
  simp [run]

/-- The distribution of the outcome of measuring the final state of `C` started in `|x⟩`. -/
noncomputable def measure (C : Circuit n) (x : Fin n → Bool) : PMF (Fin n → Bool) :=
  Quantum.measure (run C x) (norm_run C x)

@[simp] theorem measure_apply (C : Circuit n) (x y : Fin n → Bool) :
    measure C x y = ENNReal.ofReal (‖(run C x).ofLp y‖ ^ 2) :=
  rfl

/-- The circuit `C` uses only gates from the gate set `B`, a set of gates of any arities. -/
def IsOver (B : Set (Σ k, Gate k)) (C : Circuit n) : Prop :=
  ∀ g ∈ C, ⟨g.arity, g.gate⟩ ∈ B

end Circuit

/-! ### The Hadamard gate and classical reversible gates -/

namespace Gate

/-- The Hadamard matrix `H = (1/√2) [[1, 1], [1, -1]]`, indexed by one bit. -/
noncomputable def hadamardMatrix : Matrix Bool Bool ℂ :=
  fun b c => (if b && c then -1 else 1) * ((Real.sqrt 2)⁻¹ : ℝ)

theorem hadamardMatrix_mem_unitaryGroup : hadamardMatrix ∈ unitaryGroup Bool ℂ := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = 1 / 2 := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  have h1 : (2⁻¹ : ℂ) + 2⁻¹ = 1 := by norm_num
  rw [mem_unitaryGroup_iff]
  ext b c
  cases b <;> cases c <;>
    simp [hadamardMatrix, Matrix.mul_apply, star_eq_conjTranspose, Complex.conj_ofReal, h2, h1]

theorem star_hadamardMatrix : star hadamardMatrix = hadamardMatrix := by
  ext b c
  cases b <;> cases c <;> simp [hadamardMatrix, Complex.conj_ofReal]

/-- The **Hadamard gate** `|b⟩ ↦ (|0⟩ + (-1)^b |1⟩)/√2`. -/
noncomputable def hadamard : Gate 1 :=
  ⟨hadamardMatrix.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool),
    submatrix_equiv_mem_unitary.mpr hadamardMatrix_mem_unitaryGroup⟩

theorem hadamard_apply (y x : Fin 1 → Bool) :
    (hadamard : Matrix (Fin 1 → Bool) (Fin 1 → Bool) ℂ) y x =
      (if y 0 && x 0 then -1 else 1) * ((Real.sqrt 2)⁻¹ : ℝ) :=
  rfl

/-- The Hadamard gate is its own inverse. -/
theorem hadamard_mul_self : hadamard * hadamard = 1 := by
  have h := hadamardMatrix_mem_unitaryGroup.2
  rw [star_hadamardMatrix] at h
  apply Subtype.ext
  change hadamardMatrix.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool) *
    hadamardMatrix.submatrix (Equiv.funUnique (Fin 1) Bool) (Equiv.funUnique (Fin 1) Bool) = 1
  rw [submatrix_mul_equiv, h, submatrix_one_equiv]

/-- The **classical reversible gate** `|x⟩ ↦ |σ x⟩` of a permutation `σ` of `{0,1}^k`. -/
noncomputable def ofPerm (σ : Equiv.Perm (Fin k → Bool)) : Gate k :=
  ⟨σ⁻¹.permMatrix ℂ, by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, conjTranspose_permMatrix, ← permMatrix_mul,
      inv_mul_cancel, permMatrix_one]⟩

theorem ofPerm_apply (σ : Equiv.Perm (Fin k → Bool)) (y x : Fin k → Bool) :
    (ofPerm σ : Matrix (Fin k → Bool) (Fin k → Bool) ℂ) y x = if y = σ x then 1 else 0 := by
  by_cases h : y = σ x
  · simp [ofPerm, h]
  · simp [ofPerm, h, Equiv.symm_apply_eq]

/-- The classical reversible gate of an involution of `{0,1}^k`. -/
noncomputable def ofInvolutive (f : (Fin k → Bool) → Fin k → Bool) (hf : Function.Involutive f) :
    Gate k :=
  ofPerm (hf.toPerm f)

/-- The **NOT** gate `|b⟩ ↦ |¬b⟩`. -/
noncomputable def not : Gate 1 :=
  ofInvolutive (fun x _ => !x 0) fun x => by funext i; fin_cases i; simp

/-- The **controlled NOT** gate `|a, b⟩ ↦ |a, b ⊕ a⟩`. -/
noncomputable def cnot : Gate 2 :=
  ofInvolutive (fun x => Function.update x 1 (x 1 ^^ x 0)) fun x => by
    funext i; fin_cases i <;> simp [Function.update]

/-- The **Toffoli** gate `|a, b, c⟩ ↦ |a, b, c ⊕ (a ∧ b)⟩`. -/
noncomputable def toffoli : Gate 3 :=
  ofInvolutive (fun x => Function.update x 2 (x 2 ^^ (x 0 && x 1))) fun x => by
    funext i; fin_cases i <;> simp [Function.update]

end Gate

namespace PlacedGate

/-- **A classical reversible gate permutes basis states**: `σ[A]` maps `|x⟩` to the basis state
that agrees with `x` off `A` and equals `σ (x ∘ A)` on `A`. -/
theorem eval_ofPerm_ket (σ : Equiv.Perm (Fin k → Bool)) (A : Fin k ↪ Fin n)
    (x : Fin n → Bool) :
    (PlacedGate.mk k (Gate.ofPerm σ) A).eval (ket x) =
      ket ((splitEquiv A).symm (σ (x ∘ A), (splitEquiv A x).2)) := by
  ext y
  have key : y = (splitEquiv A).symm (σ (x ∘ A), (splitEquiv A x).2) ↔
      (∀ j, (¬∃ i, A i = j) → y j = x j) ∧ y ∘ A = σ (x ∘ A) := by
    rw [Equiv.eq_symm_apply, Prod.ext_iff, splitEquiv_apply_fst, splitEquiv_apply_snd,
      splitEquiv_apply_snd, funext_iff (f := fun j : {j // ¬∃ i, A i = j} => y j)]
    simp only [Subtype.forall]
    exact and_comm
  rw [eval_ket_apply, matrix_apply, ket_apply]
  simp only [key, ite_and]
  rw [Gate.ofPerm_apply]

end PlacedGate

end Cslib.Quantum
