/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Foundations.Quantum.DensityMatrix
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import CslibFrontier.Foundations.Quantum.POVM

/-!
# Pauli strings and the Pauli twirl

On `n` qubits, with computational basis the bit strings `ι → Bool`, the bit flip
`X^a |z⟩ = |z + a⟩` (`Cslib.Quantum.pauliXPow`) and the phase flip `Z^b |z⟩ = (-1)^{b · z} |z⟩`
(`Cslib.Quantum.pauliZPow`) are the tensor products of the single-qubit Pauli matrices `X` and `Z`
on the qubits where `a`, respectively `b`, is one. Their product `X^a Z^b`
(`Cslib.Quantum.pauliString`) runs over the `4ⁿ` Pauli strings up to phases.

The **Pauli twirl**, averaging `P ρ Pᴴ` over the `4ⁿ` strings `P = X^a Z^b`, is the completely
depolarizing map: `∑_{a, b} X^a Z^b ρ (X^a Z^b)ᴴ = 2ⁿ tr ρ • 1` (`Cslib.Quantum.sum_pauliTwirl`).
Summing over `b` first kills the off-diagonal entries, by orthogonality of the characters
`b ↦ (-1)^{b · z}` (`Cslib.BitString.sum_signVal_dotProduct_mul_signVal_dotProduct`), and summing
over `a` then averages the diagonal. With a reference system the twirl gives
`2ⁿ 1 ⊗ Tr_A ρ` (`Cslib.Quantum.sum_pauliTwirl_kronecker_one`), so it also erases every
correlation with the reference. For one qubit this is [de Wolf][deWolf2019], Chapter 18,
Exercise 5(a); it is the heart of the quantum one-time pad
(`CslibFrontier.Crypto.Protocols.Quantum.OneTimePad`).

## Main definitions

* `Cslib.Quantum.pauliXPow`, `Cslib.Quantum.pauliZPow`: `X^a` and `Z^b`.
* `Cslib.Quantum.pauliString`: `X^a Z^b`.

## Main results

* `Cslib.Quantum.pauliString_mem_unitaryGroup`: Pauli strings are unitary.
* `Cslib.Quantum.sum_pauliTwirl`: `∑_{a, b} X^a Z^b ρ (X^a Z^b)ᴴ = 2ⁿ tr ρ • 1`.
* `Cslib.Quantum.sum_pauliTwirl_kronecker_one`: with a reference system,
  `∑_{a, b} (X^a Z^b ⊗ 1) ρ (X^a Z^b ⊗ 1)ᴴ = 2ⁿ 1 ⊗ Tr_A ρ`.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Finset BitString
open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Pauli strings -/

/-- The **bit flip** `X^a |z⟩ = |z + a⟩`, the tensor product of `X` on the qubits where `a` is
one. -/
def pauliXPow (a : ι → Bool) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  fun y z => if z = y + a then 1 else 0

/-- The **phase flip** `Z^b |z⟩ = (-1)^{b · z} |z⟩`, the tensor product of `Z` on the qubits where
`b` is one. -/
noncomputable def pauliZPow (b : ι → Bool) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  diagonal fun z => (signVal (b ⬝ᵥ z) : ℂ)

/-- The **Pauli string** `X^a Z^b`. -/
noncomputable def pauliString (a b : ι → Bool) : Matrix (ι → Bool) (ι → Bool) ℂ :=
  pauliXPow a * pauliZPow b

omit [DecidableEq ι] in
theorem pauliXPow_apply (a y z : ι → Bool) : pauliXPow a y z = if z = y + a then 1 else 0 := by
  rfl

omit [DecidableEq ι] in
theorem pauliZPow_apply (b y z : ι → Bool) :
    pauliZPow b y z = if y = z then (signVal (b ⬝ᵥ z) : ℂ) else 0 := by
  rw [pauliZPow, diagonal_apply]
  split_ifs with h <;> simp [h]

theorem pauliString_apply (a b y z : ι → Bool) :
    pauliString a b y z = if z = y + a then (signVal (b ⬝ᵥ z) : ℂ) else 0 := by
  rw [pauliString, Matrix.mul_apply, Finset.sum_eq_single (y + a)]
  · by_cases h : z = y + a <;> simp [pauliXPow_apply, pauliZPow_apply, h, eq_comm]
  · intro w _ hw
    simp [pauliXPow_apply, hw]
  · simp

theorem conjTranspose_pauliString_apply (a b y z : ι → Bool) :
    (pauliString a b)ᴴ y z = if y = z + a then (signVal (b ⬝ᵥ y) : ℂ) else 0 := by
  rw [conjTranspose_apply, pauliString_apply]
  split_ifs <;> simp [Complex.conj_ofReal]

omit [DecidableEq ι] in
theorem pauliXPow_isHermitian (a : ι → Bool) : (pauliXPow a).IsHermitian := by
  ext y z
  have : (y = z + a) ↔ (z = y + a) := by
    constructor <;> rintro rfl <;> simp
  by_cases h : z = y + a <;> simp [conjTranspose_apply, pauliXPow_apply, h, this]

omit [DecidableEq ι] in
theorem pauliZPow_isHermitian (b : ι → Bool) : (pauliZPow b).IsHermitian :=
  isHermitian_diagonal_of_self_adjoint _ (funext fun z => by simp [Complex.conj_ofReal])

theorem pauliXPow_mul_self (a : ι → Bool) : pauliXPow a * pauliXPow a = 1 := by
  ext y z
  rw [Matrix.mul_apply, Finset.sum_eq_single (y + a)]
  · by_cases h : y = z <;> simp [pauliXPow_apply, Matrix.one_apply, h, Ne.symm]
  · intro w _ hw
    simp [pauliXPow_apply, hw]
  · simp

theorem pauliZPow_mul_self (b : ι → Bool) : pauliZPow b * pauliZPow b = 1 := by
  rw [pauliZPow, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext z
  rw [← Complex.ofReal_mul, signVal_mul_self, Complex.ofReal_one]

theorem pauliXPow_mem_unitaryGroup (a : ι → Bool) : pauliXPow a ∈ unitaryGroup (ι → Bool) ℂ :=
  mem_unitaryGroup_of_isHermitian_of_mul_self (pauliXPow_isHermitian a) (pauliXPow_mul_self a)

theorem pauliZPow_mem_unitaryGroup (b : ι → Bool) : pauliZPow b ∈ unitaryGroup (ι → Bool) ℂ :=
  mem_unitaryGroup_of_isHermitian_of_mul_self (pauliZPow_isHermitian b) (pauliZPow_mul_self b)

/-- Pauli strings are unitary. -/
theorem pauliString_mem_unitaryGroup (a b : ι → Bool) :
    pauliString a b ∈ unitaryGroup (ι → Bool) ℂ :=
  (unitaryGroup (ι → Bool) ℂ).mul_mem (pauliXPow_mem_unitaryGroup a) (pauliZPow_mem_unitaryGroup b)

/-! ### The Pauli twirl -/

/-- The entries of `X^a Z^b ρ (X^a Z^b)ᴴ`. -/
theorem pauliString_mul_mul_conjTranspose_apply (a b : ι → Bool)
    (ρ : Matrix (ι → Bool) (ι → Bool) ℂ) (y y' : ι → Bool) :
    (pauliString a b * ρ * (pauliString a b)ᴴ) y y' =
      (signVal (b ⬝ᵥ (y + a)) : ℂ) * ρ (y + a) (y' + a) * signVal (b ⬝ᵥ (y' + a)) := by
  simp only [Matrix.mul_apply, conjTranspose_pauliString_apply, pauliString_apply, ite_mul,
    zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]

/-- Summing over the phase flips `b` keeps only the entries with `u = u'`. -/
private theorem sum_signVal_mul_mul_signVal (u u' : ι → Bool) (c : ℂ) :
    ∑ b : ι → Bool, (signVal (b ⬝ᵥ u) : ℂ) * c * signVal (b ⬝ᵥ u') =
      if u = u' then 2 ^ Fintype.card ι * c else 0 := by
  have h := sum_signVal_dotProduct_mul_signVal_dotProduct u u'
  simp only [dotProduct_comm u, dotProduct_comm u'] at h
  calc ∑ b : ι → Bool, (signVal (b ⬝ᵥ u) : ℂ) * c * signVal (b ⬝ᵥ u')
      = ((∑ b : ι → Bool, signVal (b ⬝ᵥ u) * signVal (b ⬝ᵥ u') : ℝ) : ℂ) * c := by
        push_cast
        rw [sum_mul]
        exact sum_congr rfl fun b _ => by ring
    _ = _ := by
        rw [h]
        split_ifs <;> simp

/-- **The Pauli twirl** is completely depolarizing:
`∑_{a, b} X^a Z^b ρ (X^a Z^b)ᴴ = 2ⁿ tr ρ • 1` on `n = |ι|` qubits. -/
theorem sum_pauliTwirl (ρ : Matrix (ι → Bool) (ι → Bool) ℂ) :
    ∑ a : ι → Bool, ∑ b : ι → Bool, pauliString a b * ρ * (pauliString a b)ᴴ =
      (2 ^ Fintype.card ι * ρ.trace) • (1 : Matrix (ι → Bool) (ι → Bool) ℂ) := by
  ext y y'
  simp only [Matrix.sum_apply, pauliString_mul_mul_conjTranspose_apply,
    sum_signVal_mul_mul_signVal, add_left_inj, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases h : y = y'
  · subst h
    simp only [ite_true]
    rw [← mul_sum, trace]
    congr 1
    exact Fintype.sum_equiv (Equiv.addRight y) _ _ fun a => by simp [add_comm]
  · simp [h]

/-- **The Pauli twirl with a reference system**: twirling the first system of `ρ` on
`ℂ^{(ι → Bool) × κ}` gives `2ⁿ 1 ⊗ Tr_A ρ`, a product state, so every correlation with the
reference system is erased. -/
theorem sum_pauliTwirl_kronecker_one [Fintype κ] [DecidableEq κ]
    (ρ : Matrix ((ι → Bool) × κ) ((ι → Bool) × κ) ℂ) :
    ∑ a : ι → Bool, ∑ b : ι → Bool,
        (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ * (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ =
      (2 ^ Fintype.card ι : ℂ) • ((1 : Matrix (ι → Bool) (ι → Bool) ℂ) ⊗ₖ partialTraceLeft ρ) := by
  ext ⟨y, k⟩ ⟨y', k'⟩
  have hentry (a b : ι → Bool) :
      ((pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ)) * ρ *
          (pauliString a b ⊗ₖ (1 : Matrix κ κ ℂ))ᴴ) (y, k) (y', k') =
        (signVal (b ⬝ᵥ (y + a)) : ℂ) * ρ (y + a, k) (y' + a, k') *
          signVal (b ⬝ᵥ (y' + a)) := by
    simp only [Matrix.mul_apply, conjTranspose_kronecker, conjTranspose_one, kroneckerMap_apply,
      conjTranspose_pauliString_apply, pauliString_apply, Fintype.sum_prod_type, Matrix.one_apply,
      ite_mul, zero_mul, mul_ite, mul_zero, mul_one, sum_ite_eq', sum_ite_eq, mem_univ, ite_true]
  simp only [Matrix.sum_apply, hentry, sum_signVal_mul_mul_signVal, add_left_inj,
    Matrix.smul_apply, kroneckerMap_apply, Matrix.one_apply, partialTraceLeft_apply, smul_eq_mul,
    ite_mul, one_mul, zero_mul]
  by_cases h : y = y'
  · subst h
    simp only [ite_true]
    rw [← mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.addRight y) _ _ fun a => by simp [add_comm]
  · simp [h]

end Cslib.Quantum
