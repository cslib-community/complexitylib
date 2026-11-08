/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.GateMatrix
public import Complexity.Foundations.Quantum.Bell
public import Complexity.Foundations.Quantum.Bipartite
public import Complexity.Foundations.Quantum.Register

/-!
# Superdense coding

**Superdense coding** [Bennett, Wiesner][BennettWiesner1992]; [de Wolf][deWolf2019], Chapter 1,
Exercise 14. Alice and Bob share a Bell state `|Φ⁺⟩ = (|00⟩ + |11⟩)/√2`, with Alice's half first.
To send two classical bits `(a, b)`, Alice applies `X^b Z^a` to her half
(`Cslib.Quantum.superdenseEncoding`): first `Z` if `a = 1`, then `X` if `b = 1`. She sends her
qubit to Bob, who applies a CNOT (Alice's qubit the control) and then a Hadamard on Alice's qubit
(`Cslib.Quantum.superdenseDecoding`). The result is the basis state `(-1)^{a b} |a, b⟩`
(`Cslib.Quantum.superdenseState_eq`), so Bob's computational-basis measurement returns `(a, b)`
with probability `1` (`Cslib.Quantum.superdense_coding`).

De Wolf's exercise has Alice apply `X` if `a = 1` and then `Z` if `b = 1`, that is `Z^b X^a`. With
that encoding the same decoding returns `(b, a)`. The encoding here is chosen so that Bob reads
`(a, b)` in order.

## Main definitions

* `Cslib.Quantum.superdenseEncoding`: Alice's encoding `X^b Z^a`.
* `Cslib.Quantum.superdenseDecoding`: Bob's decoding, the CNOT and then the Hadamard.
* `Cslib.Quantum.superdenseState`: the state Bob measures.

## Main results

* `Cslib.Quantum.superdenseState_eq`: Bob's state is `(-1)^{a b} |a, b⟩`.
* `Cslib.Quantum.superdense_coding`: Bob measures `(a, b)` with probability `1`.

## References

* [C. H. Bennett, S. J. Wiesner, *Communication via one- and two-particle operators on
  Einstein-Podolsky-Rosen states*][BennettWiesner1992]
* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019]
-/

public section

namespace Cslib.Quantum

open Matrix Gate
open scoped Kronecker

/-- Alice's encoding `X^b Z^a` of two bits in superdense coding: first `Z` if `a = 1`, then `X`
if `b = 1`. -/
noncomputable def superdenseEncoding (a b : Bool) : unitaryGroup Bool ℂ :=
  (if b then ⟨pauliX, pauliX_mem_unitaryGroup⟩ else 1) *
    (if a then ⟨pauliZ, pauliZ_mem_unitaryGroup⟩ else 1)

/-- Alice's encoding maps `v` to `((-1)^{a (c ⊕ b)} v_{c ⊕ b})_c`. -/
theorem superdenseEncoding_mulVec (a b : Bool) (v : Bool → ℂ) (c : Bool) :
    ((superdenseEncoding a b : Matrix Bool Bool ℂ) *ᵥ v) c =
      (if a && (c ^^ b) then -1 else 1) * v (c ^^ b) := by
  cases a <;> cases b <;> cases c <;> simp [superdenseEncoding, ← mulVec_mulVec]

/-- Bob's decoding in superdense coding: a CNOT controlled by Alice's qubit, then a Hadamard on
Alice's qubit. -/
noncomputable def superdenseDecoding : unitaryGroup (Bool × Bool) ℂ :=
  onFirst ⟨hadamardMatrix, hadamardMatrix_mem_unitaryGroup⟩ *
    ⟨cnotMatrix, cnotMatrix_mem_unitaryGroup⟩

/-- The state Bob measures in superdense coding of `(a, b)`: the Bell state after Alice's encoding
on her half and Bob's decoding. -/
noncomputable def superdenseState (a b : Bool) : EuclideanSpace ℂ (Bool × Bool) :=
  unitaryEquiv superdenseDecoding (unitaryEquiv (onFirst (superdenseEncoding a b)) bell)

theorem norm_superdenseState (a b : Bool) : ‖superdenseState a b‖ = 1 := by
  rw [superdenseState, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, norm_bell]

/-- Bob's state in superdense coding of `(a, b)` is the basis state `(-1)^{a b} |a, b⟩`. -/
theorem superdenseState_eq (a b : Bool) :
    superdenseState a b = (if a && b then -1 else 1 : ℂ) • ket (a, b) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (by norm_num)]
    norm_num
  ext ⟨x, y⟩
  simp only [superdenseState, superdenseDecoding, unitaryEquiv_apply, Submonoid.coe_mul,
    coe_onFirst, ← mulVec_mulVec, kronecker_one_mulVec_apply, hadamardMatrix_mulVec,
    cnotMatrix_mulVec, superdenseEncoding_mulVec, bell_apply]
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp only [WithLp.ofLp_smul, Pi.smul_apply, ket_apply, smul_eq_mul, Bool.bne_true,
      Bool.bne_false, Bool.not_false, Bool.not_true, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, and_self, and_true, and_false,
      Bool.true_eq_false, mul_one, mul_zero, one_mul, neg_mul, mul_neg, neg_neg, add_zero,
      add_neg_cancel] <;>
    first | linear_combination 2 * hs | linear_combination (-2) * hs | ring1

/-- **Superdense coding** [Bennett, Wiesner][BennettWiesner1992]; [de Wolf][deWolf2019], Chapter 1,
Exercise 14: after Alice encodes `(a, b)` into her half of a shared Bell state and sends it,
Bob's decoding and computational-basis measurement return `(a, b)` with probability `1`. -/
theorem superdense_coding (a b : Bool) :
    measure (superdenseState a b) (norm_superdenseState a b) = PMF.pure (a, b) := by
  ext p
  rw [measure_apply, superdenseState_eq, PMF.pure_apply]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, ket_apply, smul_eq_mul]
  by_cases h : p = (a, b)
  · subst h; cases a <;> cases b <;> simp
  · simp [h]

end Cslib.Quantum
