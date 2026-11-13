/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CompositeResiduosity.Finite
public import CslibFrontier.Crypto.Computational.TwoStage
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.FieldTheory.Finite.Basic

/-!
# Paillier encryption at a fixed modulus

Fix a positive modulus `N`. Paillier encryption ([KatzLindell2020], Construction 15.11) encrypts
a message `m : ZMod N` as the unit `(1 + N) ^ m * r ^ N` of `ZMod (N ^ 2)`, for a uniform unit `r`
modulo `N`. This module states the scheme with typed messages, ciphertexts and randomness, so the
randomness is exactly uniform and the algebra of `Paillier.Algebra` applies directly. There are no
encodings, security parameter or key generation: the public key is `N`, and the secret key is the
totient `φ(N)`.

Decryption raises the ciphertext to the power `t = φ(N)`, reads off `m * t` with
`Paillier.logOneAdd`, and multiplies by `t⁻¹` modulo `N`. It is correct whenever
`gcd(N, φ(N)) = 1`.

The scheme is additively homomorphic in the full sense of [KatzLindell2020], Definition 15.14:
the product of ciphertexts decrypts to the sum of the messages, and multiplying a ciphertext of
`m₁` by a fresh encryption of `m₂` gives exactly a fresh encryption of `m₁ + m₂`. The word-level
scheme in `CslibFrontier.Crypto.Computational.Paillier` satisfies only the first condition,
because its randomness is dyadic.

Chosen-plaintext security at modulus `N` reduces to the decisional composite residuosity
experiments at `N` ([KatzLindell2020], Theorem 15.13). The reduction `paillierToDCR A b` runs the
CPA experiment for challenge bit `b` with the DCR challenge `y` in place of `r ^ N`. A real
challenge gives the CPA experiment, and a uniform challenge hides the message, so the CPA
advantage is at most the sum of the two DCR advantages, one for each challenge bit.

## Main definitions

* `Cslib.Crypto.paillierEncrypt`, `Cslib.Crypto.paillierDecrypt`: the scheme at modulus `N`.
* `Cslib.Crypto.paillierCPAExperiment`, `Cslib.Crypto.paillierCPAAdvantage`: the left-or-right
  chosen-plaintext experiment against a two-stage adversary, and its advantage.
* `Cslib.Crypto.paillierToDCR`: the reduction from chosen-plaintext security to DCR.

## Main results

* `Cslib.Crypto.paillierDecrypt_of_mem_support`: perfect correctness.
* `Cslib.Crypto.paillierDecrypt_mul`: the product of ciphertexts decrypts to the sum of the
  messages ([KatzLindell2020], Definition 15.14, first condition).
* `Cslib.Crypto.eval_mul_paillierEncrypt`, `Cslib.Crypto.eval_paillierEncrypt_mul_paillierEncrypt`:
  multiplying by a fresh encryption gives a fresh encryption of the sum ([KatzLindell2020],
  Definition 15.14, second condition).
* `Cslib.Crypto.paillierCPAAdvantage_le_dcrAdvantage`: the chosen-plaintext advantage is at most
  the sum of the DCR advantages of the two reductions ([KatzLindell2020], Theorem 15.13).

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Chapter 15,
  Construction 15.11, Theorem 15.13 and Definition 15.14.
-/

public section

namespace Cslib.Crypto

open Probability Paillier
open scoped NNReal

variable (N : ℕ) [NeZero N]

/-! ### The scheme -/

/-- Paillier encryption ([KatzLindell2020], Construction 15.11) at modulus `N`: draw a uniform unit
`r` modulo `N` and output `(1 + N) ^ m * r ^ N`. -/
@[expose] noncomputable def paillierEncrypt (m : ZMod N) : ProbComp (ZMod (N ^ 2))ˣ := do
  let r ← ProbComp.uniform (ZMod N)ˣ
  return oneAddPowHom N (.ofAdd m) * powSelfHom N r

/-- Paillier decryption ([KatzLindell2020], Construction 15.11) at modulus `N` with secret
exponent `t`: `L(c ^ t) * t⁻¹ mod N`, where `L = logOneAdd N`. The secret key is `t = φ(N)`. -/
@[expose] def paillierDecrypt (t : ℕ) (c : (ZMod (N ^ 2))ˣ) : ZMod N :=
  logOneAdd N ↑(c ^ t) * (t : ZMod N)⁻¹

variable {N}

/-- Decryption with `φ(N)` inverts `(a, r) ↦ (1 + N) ^ a * r ^ N` in its first argument: raising to
`φ(N)` removes `r ^ N` and multiplies the exponent by `φ(N)`, which is invertible modulo `N`. -/
theorem paillierDecrypt_oneAddPowHom_mul (hcop : N.Coprime N.totient)
    (a : Multiplicative (ZMod N)) (r : (ZMod N)ˣ) :
    paillierDecrypt N N.totient (oneAddPowHom N a * powSelfHom N r) = Multiplicative.toAdd a := by
  rcases (Nat.one_le_iff_ne_zero.2 (NeZero.ne N)).eq_or_lt with h | hN
  · subst h
    have : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.2 rfl
    exact Subsingleton.elim _ _
  have hr : powSelfHom N r ^ N.totient = 1 := by
    rw [← map_pow, ZMod.pow_totient, map_one]
  rw [paillierDecrypt, mul_pow, hr, mul_one, ← map_pow, logOneAdd_oneAddPowHom hN, toAdd_pow,
    nsmul_eq_mul, mul_right_comm, ZMod.coe_mul_inv_eq_one _ hcop.symm, one_mul]

/-- The encryptions of `m` are the units `(1 + N) ^ m * r ^ N` for units `r` modulo `N`. -/
theorem mem_support_paillierEncrypt {m : ZMod N} {c : (ZMod (N ^ 2))ˣ} :
    c ∈ (ProbComp.eval (paillierEncrypt N m)).support ↔
      ∃ r : (ZMod N)ˣ, c = oneAddPowHom N (.ofAdd m) * powSelfHom N r := by
  simp only [paillierEncrypt, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_uniformOfFintype, true_and,
    PMF.mem_support_pure_iff]

/-- **Correctness** ([KatzLindell2020], Construction 15.11): when `gcd(N, φ(N)) = 1`, every
encryption of `m` decrypts to `m` with secret key `φ(N)`. -/
theorem paillierDecrypt_of_mem_support (hcop : N.Coprime N.totient) {m : ZMod N}
    {c : (ZMod (N ^ 2))ˣ} (hc : c ∈ (ProbComp.eval (paillierEncrypt N m)).support) :
    paillierDecrypt N N.totient c = m := by
  obtain ⟨r, rfl⟩ := mem_support_paillierEncrypt.1 hc
  exact paillierDecrypt_oneAddPowHom_mul hcop _ r

/-- **Additive homomorphism, first condition** ([KatzLindell2020], Definition 15.14): when
`gcd(N, φ(N)) = 1`, the product of an encryption of `m₁` and an encryption of `m₂` decrypts to
`m₁ + m₂`. -/
theorem paillierDecrypt_mul (hcop : N.Coprime N.totient) {m₁ m₂ : ZMod N}
    {c₁ c₂ : (ZMod (N ^ 2))ˣ} (hc₁ : c₁ ∈ (ProbComp.eval (paillierEncrypt N m₁)).support)
    (hc₂ : c₂ ∈ (ProbComp.eval (paillierEncrypt N m₂)).support) :
    paillierDecrypt N N.totient (c₁ * c₂) = m₁ + m₂ := by
  obtain ⟨r₁, rfl⟩ := mem_support_paillierEncrypt.1 hc₁
  obtain ⟨r₂, rfl⟩ := mem_support_paillierEncrypt.1 hc₂
  rw [mul_mul_mul_comm, ← map_mul (oneAddPowHom N), ← map_mul (powSelfHom N),
    paillierDecrypt_oneAddPowHom_mul hcop]
  rfl

/-- **Additive homomorphism, second condition** ([KatzLindell2020], Definition 15.14): multiplying
any encryption `c₁` of `m₁` by a fresh encryption of `m₂` gives exactly a fresh encryption of
`m₁ + m₂`. If `c₁ = (1 + N) ^ m₁ * r₁ ^ N`, the product has randomness `r₁ * r`, which is again
uniform. -/
theorem eval_mul_paillierEncrypt {m₁ : ZMod N} {c₁ : (ZMod (N ^ 2))ˣ}
    (hc₁ : c₁ ∈ (ProbComp.eval (paillierEncrypt N m₁)).support) (m₂ : ZMod N) :
    (ProbComp.eval (paillierEncrypt N m₂)).map (c₁ * ·) =
      ProbComp.eval (paillierEncrypt N (m₁ + m₂)) := by
  obtain ⟨r₁, rfl⟩ := mem_support_paillierEncrypt.1 hc₁
  simp only [paillierEncrypt, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure]
  conv_rhs => rw [← PMF.uniformOfFintype_map_equiv (Equiv.mulLeft r₁), PMF.bind_map]
  rw [PMF.map_bind]
  congr 1 with r
  simp only [Function.comp_apply, PMF.pure_map, Equiv.coe_mulLeft, ofAdd_add, map_mul]
  rw [mul_mul_mul_comm]

/-- The product of two independent encryptions of `m₁` and `m₂` is distributed as an encryption of
`m₁ + m₂`. -/
theorem eval_paillierEncrypt_mul_paillierEncrypt (m₁ m₂ : ZMod N) :
    ProbComp.eval (do
        let c₁ ← paillierEncrypt N m₁
        let c₂ ← paillierEncrypt N m₂
        return c₁ * c₂) =
      ProbComp.eval (paillierEncrypt N (m₁ + m₂)) := by
  have h : ∀ c₁ ∈ (ProbComp.eval (paillierEncrypt N m₁)).support,
      ProbComp.eval (do let c₂ ← paillierEncrypt N m₂; return c₁ * c₂) =
        ProbComp.eval (paillierEncrypt N (m₁ + m₂)) := fun c₁ hc₁ => by
    rw [← eval_mul_paillierEncrypt hc₁ m₂, ProbComp.eval_bind]
    exact PMF.bind_pure_comp _ _
  rw [ProbComp.eval_bind, Cslib.Probability.PMF.bind_congr_on_support _ _ _ h, PMF.bind_const]

/-! ### Chosen-plaintext security -/

variable (N)

/-- The left-or-right chosen-plaintext experiment against Paillier encryption at modulus `N`
([KatzLindell2020], Theorem 15.13): the adversary receives the public key `N`, chooses two
messages, and guesses the challenge bit `b` from an encryption of the selected message. Every pair
of messages is admissible. -/
@[expose] noncomputable def paillierCPAExperiment {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) (b : Bool) : Experiment :=
  lrExperiment (fun _ _ _ => true) (fun _ m => paillierEncrypt N m) A b N

/-- The chosen-plaintext advantage of `A` against Paillier encryption at modulus `N`. -/
@[expose] noncomputable def paillierCPAAdvantage {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) : ℝ≥0 :=
  Experiment.advantage (paillierCPAExperiment N A false) (paillierCPAExperiment N A true)

/-- The reduction from chosen-plaintext security to DCR ([KatzLindell2020], proof of
Theorem 15.13): on challenge `y`, run the chosen-plaintext experiment for bit `b`, encrypting
`m` as `(1 + N) ^ m * y`. -/
@[expose] noncomputable def paillierToDCR {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) (b : Bool)
    (y : (ZMod (N ^ 2))ˣ) : Experiment :=
  lrExperiment (fun _ _ _ => true) (fun _ m => pure (oneAddPowHom N (.ofAdd m) * y)) A b N

variable {N}

/-- A real DCR challenge gives the reduction the chosen-plaintext experiment. -/
theorem eval_dcrRealExperiment_paillierToDCR {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) (b : Bool) :
    ProbComp.eval (dcrRealExperiment N (paillierToDCR N A b)) =
      ProbComp.eval (paillierCPAExperiment N A b) := by
  simp only [eval_dcrRealExperiment, paillierToDCR, paillierCPAExperiment,
    eval_lrExperiment, ite_true, paillierEncrypt, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind]
  rw [PMF.bind_comm]
  simp only [PMF.bind_bind, PMF.pure_bind]

/-- A uniform DCR challenge hides the message: multiplying the uniform unit by `(1 + N) ^ m`
leaves it uniform, so the reduction's experiment does not depend on `b`. -/
theorem eval_dcrRandomExperiment_paillierToDCR {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) (b b' : Bool) :
    ProbComp.eval (dcrRandomExperiment N (paillierToDCR N A b)) =
      ProbComp.eval (dcrRandomExperiment N (paillierToDCR N A b')) := by
  have key : ∀ b : Bool, ProbComp.eval (dcrRandomExperiment N (paillierToDCR N A b)) =
      (ProbComp.eval (A.choose N)).bind fun p =>
        (PMF.uniformOfFintype (ZMod (N ^ 2))ˣ).bind fun y => ProbComp.eval (A.guess p.2 y) := by
    intro b
    simp only [dcrRandomExperiment, paillierToDCR, eval_lrExperiment, ite_true,
      ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind]
    rw [PMF.bind_comm]
    congr 1
    funext p
    conv_rhs => rw [← PMF.uniformOfFintype_map_equiv
      (Equiv.mulLeft (oneAddPowHom N (.ofAdd (p.1.select b)))), PMF.bind_map]
    rfl
  rw [key, key]

/-- **Theorem 15.13** ([KatzLindell2020]) at modulus `N`: the chosen-plaintext advantage of `A`
against Paillier encryption is at most the sum of the DCR advantages of the reductions
`paillierToDCR A false` and `paillierToDCR A true`. -/
theorem paillierCPAAdvantage_le_dcrAdvantage {σ : Type}
    (A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ) :
    paillierCPAAdvantage N A ≤
      dcrAdvantage N (paillierToDCR N A false) + dcrAdvantage N (paillierToDCR N A true) := by
  simp only [paillierCPAAdvantage, dcrAdvantage, Experiment.advantage,
    ← eval_dcrRealExperiment_paillierToDCR,
    eval_dcrRandomExperiment_paillierToDCR A true false]
  refine (Game.advantage_triangle _
    (ProbComp.eval (dcrRandomExperiment N (paillierToDCR N A false))) _).trans_eq ?_
  rw [Game.advantage_comm _ (ProbComp.eval (dcrRealExperiment N (paillierToDCR N A true)))]

end Cslib.Crypto
