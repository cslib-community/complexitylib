/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature.Failure
public import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Tactic.PolyTime

/-!
# An explicit family with negligible bounded-signing failure

At security parameter `λ`, put `t = λ + 1`, use dimensions `n = m = k = t`, secret-entry
bound one, rejection margin `β = t`, radius `γ = 4t²`, sampling width `λ`, modulus `2^t`,
and `t` signing attempts. The parameter construction and the actual signer are polynomial-time
jointly in unary `λ` and the encoded matrix/message input sizes. The modulus and radii are
binary, so the exponentially large modulus has only linear bit length.

Failure is negligible uniformly over bounded secret matrices, public matrices, messages and
deterministic hashes. Efficiency additionally requires a polynomial-time word hash. This is
an availability result for the existing signer, not a SIS-hardness parameter recommendation
or a random-oracle signature security theorem. The bounds are original formalization results.

## Main definitions

* `lyubashevskySigningParams`: the concrete parameter schedule.

## Main results

* `isPPTOn_lyubashevskySigningParams`: the actual family signer is uniformly strict PPT.
* `lyubashevskySigningParams_failure_le`: explicit geometric-plus-sampling failure bound.
* `negligible_lyubashevskySigningParams_failure`: the actual failure probability is negligible.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF Turing.MultiTapeTM Interactive
open scoped ENNReal NNReal _root_.Matrix

/-- Explicit availability parameters. No hardness of the resulting SIS instances is asserted. -/
@[expose] def lyubashevskySigningParams (security : ℕ) : LyubashevskyParams :=
  let t := security + 1
  ((t, t, t, security), (2 ^ t, 4 * t ^ 2, t))

/-- The schedule is polynomial-time: the exponential modulus is produced in binary. -/
@[fun_prop]
theorem computableInPolyTime_lyubashevskySigningParams :
    ComputableInPolyTime lyubashevskySigningParams encUnary encLyubashevskyParams := by
  unfold lyubashevskySigningParams encLyubashevskyParams
  fun_prop

/-- The instantiated signer is strict PPT jointly in unary security and raw matrix/message
sizes. No polynomial-length assumption on an arbitrary message sequence is implicit here. -/
theorem isPPTOn_lyubashevskySigningParams
    {hash : List Bool × List Bool → List Bool}
    (hhash : ComputableInPolyTime hash (encPair encBits encBits) encBits) :
    IsPPTOn
      (encPair encUnary
        (encPair (encList (encList encIntBin)) (encPair (encList (encList encIntBin)) encBits)))
      (encOption (encPair encBits encBits))
      (fun input : ℕ × List (List ℤ) × List (List ℤ) × List Bool =>
        let (security, secret, matrix, msg) := input
        lyubashevskySignBoundedNative hash
          ((lyubashevskySigningParams security, secret, matrix, msg), security + 1)) := by
  apply (isPPTOn_lyubashevskySignBoundedNative hhash).preprocess
  unfold encLyubashevskySignInput
  fun_prop

/-- At the chosen radius every exact signing attempt fails with probability at most one half,
uniformly over the deterministic hash and message. -/
theorem lyubashevskySigningParams_attempt_none_le (security : ℕ)
    {S : Matrix (Fin (security + 1)) (Fin (security + 1)) ℤ}
    (hS : ∀ i j, |S i j| ≤ 1)
    (y : Matrix (Fin (security + 1)) (Fin (security + 1)) (ZMod (2 ^ (security + 1))) ×
      Matrix (Fin (security + 1)) (Fin (security + 1)) (ZMod (2 ^ (security + 1))))
    (hash : List Bool × List Bool → List Bool) (msg : List Bool) :
    let p := lyubashevskySigningParams security
    lyubashevskySignAttempt p.n p.m p.k p.q p.γ p.β
      (lyubashevskyNativeHash hash p) S y msg none ≤ (1 / 2 : ℝ≥0∞) := by
  dsimp only [lyubashevskySigningParams, LyubashevskyParams.n, LyubashevskyParams.m,
    LyubashevskyParams.k, LyubashevskyParams.q, LyubashevskyParams.γ, LyubashevskyParams.β]
  have hβ : 2 * (security + 1) ≤ 4 * (security + 1) ^ 2 := by nlinarith
  have h := lyubashevskySignAttempt_none_le hβ (by omega : (security + 1) * 1 ≤ security + 1)
    hS y (lyubashevskyNativeHash hash (lyubashevskySigningParams security)) msg
  refine h.trans ?_
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num)),
    ← ENNReal.mul_div_right_comm, ENNReal.div_le_iff (by positivity) (by finiteness)]
  norm_cast
  nlinarith

/-- Explicit native failure bound. The matrix/message lengths and deterministic hash are
unrestricted for this probability estimate; efficiency is supplied separately above. -/
theorem lyubashevskySigningParams_failure_le (security : ℕ)
    {S : Matrix (Fin (security + 1)) (Fin (security + 1)) ℤ}
    (hS : ∀ i j, |S i j| ≤ 1)
    (A : Matrix (Fin (security + 1)) (Fin (security + 1)) (ZMod (2 ^ (security + 1))))
    (hash : List Bool × List Bool → List Bool) (msg : List Bool) :
    ProbComp.eval (lyubashevskySignBoundedNative hash
      (lyubashevskySignInput (lyubashevskySigningParams security) S A msg, security + 1)) none ≤
      (1 / 2 : ℝ≥0∞) ^ (security + 1) +
        (security + 1) ^ 2 * (8 * (security + 1) ^ 2 + 1) / 2 ^ security := by
  have h := lyubashevskySignBoundedNative_none_le hash (lyubashevskySigningParams security)
    S (A, 0) msg (security + 1)
  have hp := pow_le_pow_left' (lyubashevskySigningParams_attempt_none_le security hS
    (A, 0) hash msg) (security + 1)
  refine h.trans ((add_le_add hp le_rfl).trans ?_)
  apply le_of_eq
  congr 1
  dsimp only [lyubashevskySigningParams, LyubashevskyParams.m, LyubashevskyParams.γ,
    LyubashevskyParams.width]
  push_cast
  simp only [div_eq_mul_inv]
  ring

/-- Both the geometric retry term and the polynomial fair-bit sampling loss are negligible. -/
theorem negligible_lyubashevskySigningParams_bound :
    Negligible (fun security => (1 / 2 : ℝ≥0) ^ (security + 1) +
      (security + 1) ^ 2 * (8 * (security + 1) ^ 2 + 1) / 2 ^ security) := by
  have hg := (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)).shift 1
  have hpoly : PolynomiallyBounded
      (fun security : ℕ => (security + 1) ^ 2 * (8 * (security + 1) ^ 2 + 1)) := by
    fun_prop
  have hs := (negligible_const_div_two_pow 1).polynomiallyBounded_mul hpoly
  have hs' : Negligible (fun security =>
      (security + 1 : ℝ≥0) ^ 2 * (8 * (security + 1) ^ 2 + 1) / 2 ^ security) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      mul_one_div] using hs
  exact hg.add hs'

/-- For every bounded secret-matrix sequence and arbitrary public matrices/messages, the
actual native bounded signer has negligible failure. This is uniform over deterministic hashes;
no random oracle or SIS-hardness hypothesis is asserted. -/
theorem negligible_lyubashevskySigningParams_failure
    (S : (security : ℕ) → Matrix (Fin (security + 1)) (Fin (security + 1)) ℤ)
    (hS : ∀ security i j, |S security i j| ≤ 1)
    (A : (security : ℕ) →
      Matrix (Fin (security + 1)) (Fin (security + 1)) (ZMod (2 ^ (security + 1))))
    (hash : List Bool × List Bool → List Bool) (msg : ℕ → List Bool) :
    Negligible (fun security =>
      (ProbComp.eval (lyubashevskySignBoundedNative hash
        (lyubashevskySignInput (lyubashevskySigningParams security)
          (S security) (A security) (msg security), security + 1)) none).toNNReal) := by
  apply negligible_of_le negligible_lyubashevskySigningParams_bound
  intro security
  have h := ENNReal.toNNReal_mono (by finiteness)
    (lyubashevskySigningParams_failure_le security (hS security) (A security) hash (msg security))
  have heq : ((1 / 2 : ℝ≥0∞) ^ (security + 1) +
      (security + 1) ^ 2 * (8 * (security + 1) ^ 2 + 1) / 2 ^ security) =
      (((1 / 2 : ℝ≥0) ^ (security + 1) +
        (security + 1) ^ 2 * (8 * (security + 1) ^ 2 + 1) / 2 ^ security : ℝ≥0) : ℝ≥0∞) := by
    push_cast
    rfl
  rw [heq, ENNReal.toNNReal_coe] at h
  exact h

end Cslib.Crypto.Protocols.SigmaProtocol
