/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.Uniform

/-!
# Uniform families of quantum verifiers

A quantum verifier reads, besides its input word, a **witness state** on some of its qubits
[Watrous][Watrous2008], Section V.1. A polynomial-time uniform family of verifiers
(`Cslib.Quantum.UniformVerifierFamily`) is a uniform family of circuits
(`Cslib.Quantum.UniformCircuitFamily`) with a witness length `witnessLength n`, computed from `n`
in unary in polynomial time. On an input word `x` of length `n` and a witness state `ψ` on
`witnessLength n` qubits, the circuit for inputs of length `n` starts in `|x⟩ ⊗ |ψ⟩ ⊗ |0 … 0⟩`:
the input on the qubits `0, …, n - 1`, the witness on the next `witnessLength n` qubits and zeros
on the rest. It accepts when the final measurement finds qubit `0` in state `1`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb`).

The initial state is the embedding of `ψ` into the larger register
(`Cslib.Quantum.embedState`): the amplitude of a basis string is that of its bits on the witness
qubits, when its other bits are those of the classical input, and zero otherwise. On a basis
witness `|z⟩` this is the input state of the word `x ++ z`
(`Cslib.Quantum.UniformVerifierFamily.acceptProb_ket`).

Witnesses are pure states, as in [Marriott, Watrous][MarriottWatrous2005], Definition 3.1. Mixed
witnesses would give the same acceptance bounds: the acceptance probability is a quadratic form in
the witness, so a mixed witness accepts with a convex combination of the acceptance probabilities of
pure witnesses. This equivalence is not formalized here.

## Main definitions

* `Cslib.Quantum.UniformVerifierFamily`: polynomial-time uniform families of quantum verifiers.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb`: the acceptance probability on an input word and
  a witness state.
* `Cslib.Quantum.UniformVerifierFamily.ofCircuitFamily`: a uniform family of circuits as a
  verifier reading no witness.

## Main results

* `Cslib.Quantum.UniformVerifierFamily.acceptProb_ket`: on a basis witness, the verifier is its
  circuit run on the input word followed by the witness bits.
* `Cslib.Quantum.UniformVerifierFamily.acceptProb_smul`: the acceptance probability is homogeneous
  of degree two in the witness.

## References

* [J. Watrous, *Quantum computational complexity*][Watrous2008]
* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

@[expose] public section

namespace Cslib.Quantum

open Finset Turing.MultiTapeTM

/-! ### Verifier families -/

/-- A **polynomial-time uniform family of quantum verifiers**: a uniform family of circuits that,
on inputs of length `n`, also reads a witness state of `witnessLength n` qubits on the qubits
`n, …, n + witnessLength n - 1`, right after the input. The witness length is computed from `n` in
unary in polynomial time. -/
structure UniformVerifierFamily extends UniformCircuitFamily where
  /-- The number of witness qubits on inputs of length `n`. -/
  witnessLength : ℕ → ℕ
  computableInPolyTime_witnessLength : ComputableInPolyTime witnessLength encUnary encUnary
  add_witnessLength_le : ∀ n, n + witnessLength n ≤ width n

namespace UniformVerifierFamily

variable (V : UniformVerifierFamily)

/-- The witness qubits `n, …, n + witnessLength n - 1` on inputs of length `n`. -/
def witnessQubits (n : ℕ) : Fin (V.witnessLength n) ↪ Fin (V.width n) :=
  blockEmb n (V.add_witnessLength_le n)

/-- The **acceptance probability** of the verifier on the input word `x` and the witness state
`ψ`: its circuit for inputs of length `|x|` runs on `x`, the witness `ψ` and zeros, and the final
measurement finds qubit `0` in state `1`. For a unit vector `ψ` this is a probability. -/
noncomputable def acceptProb (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) : ℝ :=
  measureProb (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))
    (embedState (V.witnessQubits x.length) (inputState (V.width x.length) x) ψ))
    (accepting (V.width x.length))

theorem acceptProb_nonneg (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    0 ≤ V.acceptProb x ψ :=
  measureProb_nonneg _ _

theorem acceptProb_le (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    V.acceptProb x ψ ≤ ‖ψ‖ ^ 2 := by
  refine (measureProb_le_measureProb_univ _ _).trans_eq ?_
  rw [measureProb_univ, LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]

/-- The acceptance probability is homogeneous of degree two in the witness. -/
theorem acceptProb_smul (x : List Bool) (c : ℂ) (ψ : Qubits (V.witnessLength x.length)) :
    V.acceptProb x (c • ψ) = ‖c‖ ^ 2 * V.acceptProb x ψ := by
  rw [acceptProb, map_smul, map_smul, measureProb_smul, acceptProb]

/-- On a basis witness `|z⟩`, the verifier is its circuit run on the word `x ++ z`. -/
theorem acceptProb_ket (x : List Bool) (z : Fin (V.witnessLength x.length) → Bool) :
    V.acceptProb x (ket z) =
      Quantum.acceptProb (V.width x.length) (V.gates x.length) (x ++ List.ofFn z) := by
  rw [acceptProb, embedState_ket, witnessQubits, glue_blockEmb_inputState _ _ rfl]
  rfl

/-- The verifier accepts with probability zero on every witness state if it does on every basis
witness. -/
theorem acceptProb_eq_zero_of_forall_ket (x : List Bool) (h : ∀ z, V.acceptProb x (ket z) = 0)
    (ψ : Qubits (V.witnessLength x.length)) : V.acceptProb x ψ = 0 := by
  have hz (z) (y) (hy : y ∈ accepting (V.width x.length)) :
      (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))
        (embedState (V.witnessQubits x.length) (inputState _ x) (ket z))).ofLp y = 0 :=
    ofLp_eq_zero_of_measureProb_eq_zero (h z) hy
  rw [acceptProb, measureProb]
  refine sum_eq_zero fun y hy => ?_
  rw [← sum_smul_ket ψ, map_sum, map_sum, WithLp.ofLp_sum, Finset.sum_apply]
  simp only [map_smul, WithLp.ofLp_smul, Pi.smul_apply, hz _ y hy, smul_zero, sum_const_zero,
    norm_zero]
  norm_num

/-- A verifier reading no witness qubits on inputs of length `|x|` accepts the (unique) basis
witness as its circuit family accepts `x`. -/
theorem acceptProb_ket_of_witnessLength_eq_zero (x : List Bool) (h : V.witnessLength x.length = 0)
    (z : Fin (V.witnessLength x.length) → Bool) :
    V.acceptProb x (ket z) = V.toUniformCircuitFamily.acceptProb x := by
  rw [acceptProb_ket, List.eq_nil_of_length_eq_zero (by simp [h] : (List.ofFn z).length = 0),
    List.append_nil]
  rfl

/-- A uniform family of circuits as a verifier reading no witness. -/
def ofCircuitFamily (F : UniformCircuitFamily) : UniformVerifierFamily where
  toUniformCircuitFamily := F
  witnessLength _ := 0
  computableInPolyTime_witnessLength := ComputableInPolyTime.const _
  add_witnessLength_le n := F.le_width n

/-- A family reading no witness accepts as the circuit family does, scaled by the squared norm of
the (one-dimensional) witness. -/
theorem acceptProb_ofCircuitFamily (F : UniformCircuitFamily) (x : List Bool)
    (ψ : Qubits ((ofCircuitFamily F).witnessLength x.length)) :
    (ofCircuitFamily F).acceptProb x ψ = ‖ψ‖ ^ 2 * F.acceptProb x := by
  have : Subsingleton (Fin ((ofCircuitFamily F).witnessLength x.length) → Bool) :=
    inferInstanceAs (Subsingleton (Fin 0 → Bool))
  have hψ : ψ = ψ.ofLp default • ket default := by
    ext z
    rw [Subsingleton.elim z default]
    simp
  rw [hψ, acceptProb_smul, acceptProb_ket_of_witnessLength_eq_zero _ _ rfl, norm_smul, norm_ket,
    mul_one]
  rfl

end UniformVerifierFamily

end Cslib.Quantum
