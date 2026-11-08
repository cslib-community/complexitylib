/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Quantum.Verifier
public import Complexity.Computability.Circuit.Quantum.PathSum
public import Complexity.Foundations.LinearAlgebra.TracePower
public import Complexity.Foundations.Quantum.Measurement.Restrict

/-!
# The acceptance operator of a quantum verifier

On an input word `x`, a verifier (`Cslib.Quantum.UniformVerifierFamily`) maps a witness state `ψ`
to its final state and accepts on the outcomes `accepting`. Restricting the final state to those
outcomes gives a linear map `B_x` (`Cslib.Quantum.UniformVerifierFamily.acceptMap`) with
`‖B_x ψ‖² = acceptProb x ψ`. The **acceptance operator** `Q_x = B_x† B_x`
(`Cslib.Quantum.UniformVerifierFamily.acceptOp`) is therefore positive and its quadratic form is the
acceptance probability. Its eigenvalues are the acceptance probabilities of its eigenvectors, so the
largest one is the maximum acceptance probability over unit witnesses
[Marriott, Watrous][MarriottWatrous2005], proof of Theorem 3.4.

For circuits over the Hadamard and Toffoli gates with `h` Hadamard gates, the matrix entry
`⟨u|Q_x|v⟩` in the computational basis is the projected pair gap of the registers `x ++ u` and
`x ++ v` divided by `2^h` (`Cslib.Quantum.UniformVerifierFamily.inner_ket_acceptOp_ket`). Hence
`2^{hd} tr(Q_x^d)` is the integer `traceGap x d`, a sum over closed paths of `d` steps through the
basis witnesses of products of pair gaps
(`Cslib.Quantum.UniformVerifierFamily.re_trace_acceptOp_pow`).
The trace bounds for positive operators (`LinearMap.IsPositive.pow_le_re_trace_pow`,
`LinearMap.IsPositive.re_trace_pow_le`) then separate accepting from rejecting inputs:

* if some unit witness is accepted with probability at least `c ≥ 0`, then
  `c^d 2^{hd} ≤ traceGap x d` (`Cslib.Quantum.UniformVerifierFamily.pow_mul_le_traceGap`);
* if every unit witness is accepted with probability at most `s`, then
  `traceGap x d ≤ 2^m s^d 2^{hd}` with `m` the witness length
  (`Cslib.Quantum.UniformVerifierFamily.traceGap_le`).

Marriott and Watrous bound `tr(Q_x)` for a verifier whose error has first been reduced below
`2^{-m-2}`. Here powers of `Q_x` play that role instead, which is how
`Cslib.Complexity.QMA_subset_PP` avoids strong error reduction.

## Main definitions

* `Cslib.Quantum.UniformVerifierFamily.acceptMap`: the final state restricted to the accepting
  outcomes, as a linear map of the witness.
* `Cslib.Quantum.UniformVerifierFamily.acceptOp`: the acceptance operator `B† B`.
* `Cslib.Quantum.UniformVerifierFamily.traceGap`: the closed-path sum of pair gaps.

## Main results

* `Cslib.Quantum.UniformVerifierFamily.re_inner_acceptOp`: the quadratic form of the acceptance
  operator is the acceptance probability.
* `Cslib.Quantum.UniformVerifierFamily.inner_ket_acceptOp_ket`: its entries are pair gaps over
  `2^h`.
* `Cslib.Quantum.UniformVerifierFamily.re_trace_acceptOp_pow`: `tr(Q^d) = traceGap / 2^{hd}`.
* `Cslib.Quantum.UniformVerifierFamily.pow_mul_le_traceGap`,
  `Cslib.Quantum.UniformVerifierFamily.traceGap_le`: the trace bounds.

## References

* [C. Marriott, J. Watrous, *Quantum Arthur–Merlin games*][MarriottWatrous2005]
-/

public section

namespace Cslib.Quantum

open Finset Module

namespace UniformVerifierFamily

variable (V : UniformVerifierFamily)

/-- The **acceptance map** of the verifier on the input word `x`: a witness state `ψ` goes to the
final state of the circuit run on `x`, `ψ` and zeros, restricted to the accepting outcomes. -/
noncomputable def acceptMap (x : List Bool) :
    Qubits (V.witnessLength x.length) →ₗ[ℂ] EuclideanSpace ℂ (accepting (V.width x.length)) :=
  restrictOutcomes (accepting (V.width x.length)) ∘ₗ
    (Circuit.eval (Circuit.ofCodes (V.width x.length) (V.gates x.length))).toLinearMap ∘ₗ
    (embedState (V.witnessQubits x.length) (inputState (V.width x.length) x)).toLinearMap

/-- The squared norm of the acceptance map is the acceptance probability. -/
theorem norm_acceptMap_sq (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    ‖V.acceptMap x ψ‖ ^ 2 = V.acceptProb x ψ :=
  norm_restrictOutcomes_sq _ _

/-- On a basis witness `|z⟩`, the acceptance map restricts the final state of the circuit run on
the word `x ++ z`. -/
theorem acceptMap_ket (x : List Bool) (z : Fin (V.witnessLength x.length) → Bool) :
    V.acceptMap x (ket z) = restrictOutcomes (accepting (V.width x.length))
      (Circuit.run (Circuit.ofCodes (V.width x.length) (V.gates x.length))
        (inputState (V.width x.length) (x ++ List.ofFn z))) := by
  change restrictOutcomes _ (Circuit.eval _ (embedState _ _ (ket z))) = _
  rw [embedState_ket, witnessQubits, glue_blockEmb_inputState _ _ rfl]
  rfl

/-- The **acceptance operator** `B† B` of the verifier on the input word `x`, where `B` is the
acceptance map. -/
noncomputable def acceptOp (x : List Bool) :
    Qubits (V.witnessLength x.length) →ₗ[ℂ] Qubits (V.witnessLength x.length) :=
  (V.acceptMap x).adjoint ∘ₗ V.acceptMap x

theorem isPositive_acceptOp (x : List Bool) : (V.acceptOp x).IsPositive :=
  LinearMap.isPositive_adjoint_comp_self _

/-- The quadratic form of the acceptance operator is the acceptance probability. -/
theorem re_inner_acceptOp (x : List Bool) (ψ : Qubits (V.witnessLength x.length)) :
    RCLike.re (inner ℂ ψ (V.acceptOp x ψ)) = V.acceptProb x ψ := by
  rw [acceptOp, LinearMap.re_inner_adjoint_comp_self_apply, norm_acceptMap_sq]

/-- **The entries of the acceptance operator are pair gaps**: `⟨u|Q_x|v⟩` is the projected pair gap
of qubit `0` on the registers holding `x ++ u` and `x ++ v`, divided by `2^h`. -/
theorem inner_ket_acceptOp_ket (x : List Bool) (u v : Fin (V.witnessLength x.length) → Bool) :
    inner ℂ (ket u) (V.acceptOp x (ket v)) =
      (onesPairGap [0] (V.gates x.length)
          (List.ofFn (inputState (V.width x.length) (x ++ List.ofFn u)))
          (List.ofFn (inputState (V.width x.length) (x ++ List.ofFn v))) : ℂ) /
        2 ^ hadamardCount (V.gates x.length) := by
  rw [acceptOp, LinearMap.comp_apply, LinearMap.adjoint_inner_right, acceptMap_ket, acceptMap_ket,
    inner_restrictOutcomes]
  exact sum_onesAt_star_run_mul_run _ (V.wellFormed _) _ _ _

/-- The **trace gap** of the verifier on the input word `x`: the sum, over closed paths
`p 0, …, p d = p 0` of basis witnesses, of the product of the pair gaps of consecutive steps. It is
`2^{hd} tr(Q_x^d)` (`Cslib.Quantum.UniformVerifierFamily.re_trace_acceptOp_pow`). -/
@[expose] def traceGap (x : List Bool) (d : ℕ) : ℤ :=
  ∑ p : Fin (d + 1) → Fin (V.witnessLength x.length) → Bool,
    if p 0 = p (Fin.last d) then
      ∏ i : Fin d, onesPairGap [0] (V.gates x.length)
        (List.ofFn (inputState (V.width x.length) (x ++ List.ofFn (p i.castSucc))))
        (List.ofFn (inputState (V.width x.length) (x ++ List.ofFn (p i.succ))))
    else 0

/-- `tr(Q_x^d) = traceGap x d / 2^{hd}`. -/
theorem trace_acceptOp_pow (x : List Bool) (d : ℕ) :
    LinearMap.trace ℂ _ (V.acceptOp x ^ d) =
      (V.traceGap x d : ℂ) / 2 ^ (hadamardCount (V.gates x.length) * d) := by
  rw [LinearMap.trace_pow_eq_sum (EuclideanSpace.basisFun _ ℂ), traceGap, Int.cast_sum, sum_div]
  refine sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [Int.cast_prod, pow_mul, ← Fin.prod_const d ((2 : ℂ) ^ hadamardCount (V.gates x.length)),
      ← prod_div_distrib]
    refine prod_congr rfl fun i _ => ?_
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply]
    exact V.inner_ket_acceptOp_ket x _ _
  · simp

/-- **The trace of a power of the acceptance operator is a trace gap over a power of two.** -/
theorem re_trace_acceptOp_pow (x : List Bool) (d : ℕ) :
    RCLike.re (LinearMap.trace ℂ _ (V.acceptOp x ^ d)) =
      (V.traceGap x d : ℝ) / 2 ^ (hadamardCount (V.gates x.length) * d) := by
  rw [trace_acceptOp_pow]
  have : ((V.traceGap x d : ℂ) / 2 ^ (hadamardCount (V.gates x.length) * d)) =
      (((V.traceGap x d : ℝ) / 2 ^ (hadamardCount (V.gates x.length) * d) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [this]
  exact Complex.ofReal_re _

/-- **Completeness bound**: if some unit witness is accepted with probability at least `c ≥ 0`,
then `c^d 2^{hd} ≤ traceGap x d`. -/
theorem pow_mul_le_traceGap (x : List Bool) {c : ℝ} (hc : 0 ≤ c)
    (h : ∃ ψ : Qubits (V.witnessLength x.length), ‖ψ‖ = 1 ∧ c ≤ V.acceptProb x ψ) (d : ℕ) :
    c ^ d * 2 ^ (hadamardCount (V.gates x.length) * d) ≤ V.traceGap x d := by
  obtain ⟨ψ, hψ, hcψ⟩ := h
  have := (V.isPositive_acceptOp x).pow_le_re_trace_pow hψ hc
    ((V.re_inner_acceptOp x ψ).symm ▸ hcψ) d
  rwa [re_trace_acceptOp_pow, le_div_iff₀ (by positivity)] at this

/-- **Soundness bound**: if every unit witness is accepted with probability at most `s`, then
`traceGap x d ≤ 2^m s^d 2^{hd}`, where `m` is the number of witness qubits. -/
theorem traceGap_le (x : List Bool) {s : ℝ}
    (h : ∀ ψ : Qubits (V.witnessLength x.length), ‖ψ‖ = 1 → V.acceptProb x ψ ≤ s) (d : ℕ) :
    (V.traceGap x d : ℝ) ≤
      2 ^ V.witnessLength x.length * s ^ d * 2 ^ (hadamardCount (V.gates x.length) * d) := by
  have := (V.isPositive_acceptOp x).re_trace_pow_le
    (fun ψ hψ => (V.re_inner_acceptOp x ψ).symm ▸ h ψ hψ) d
  rwa [re_trace_acceptOp_pow, div_le_iff₀ (by positivity), finrank_euclideanSpace,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at this

end UniformVerifierFamily

end Cslib.Quantum
