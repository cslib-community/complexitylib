/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.MLDSA.Basic
public import Complexity.Crypto.Game
public import Complexity.Probability.Product
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# ML-DSA forgeries, self-target MSIS and Module-LWE: the key-only reduction

The security argument for Dilithium ([DucasEtAl2018]) replaces the public key `t = A s₁ + s₂`
by a uniform vector, which costs a Module-LWE distinguishing advantage, and then turns a forgery
against a *uniform* key into a solution of the *self-target* Module-SIS problem for the matrix
`[I_k | A | -t]`. This module formalizes both steps for key-only attacks (no signing queries,
fixed hash function), with explicit reductions:

* **Self-target MSIS.** `IsSelfTargetSolution G ζ pk M u z c` says that `(u, z, c)` is a solution
  for message `M`: `‖u‖_∞, ‖z‖_∞ ≤ ζ`, `c ∈ B_τ`, and `G(u + A z - c t, M) = c` for the hash `G`.
* **From a forgery to a self-target solution.** If `(z, c)` verifies on `M`, write
  `w' = A z - c t` and `u = -LowBits(w')`. Then `u + w' = 2 γ₂ · HighBits(w')`, whose high bits
  are again `HighBits(w')` by uniqueness of the decomposition, so `(u, z, c)` is a self-target
  solution for the hash `G(v, M) = H(HighBits(v), M)` with `ζ = max γ₁ γ₂`
  (`isSelfTargetSolution_of_verify`). This step is deterministic and holds for every key.
* **Key-only unforgeability.** For honest keys (`keyLaw`), the success probability of any
  key-only forger is at most the advantage of the explicit distinguisher `forgeryDistinguisher`
  between honest and uniform keys (`uniformKeyLaw`), plus the success probability of the explicit
  solver `selfTargetReduction` against self-target MSIS for a uniform matrix `[A | t]`
  (`succProbability_koaGame_le`). The honest key `(A, A s₁ + s₂)` is a Module-LWE sample with
  short secret `s₁` and error `s₂` (`SecretKey.publicKey_t`); the uniform-secret
  `Cslib.Crypto.DecisionModuleLWE` of `SIS.Module` is a different secret distribution, so the
  distinguishing term is stated concretely rather than through that hypothesis.

Hardness of self-target MSIS for the hash `H(HighBits(·), ·)` is the assumption, as in
[DucasEtAl2018]; it is neither proved nor reduced to standard Module-SIS here.

This is the key-only core of the reduction. Chosen-message security additionally simulates the
signing oracle (zero knowledge of the aborting identification scheme, in the random-oracle
model); that step, and the asymptotic packaging, are not formalized here.

## Main definitions

* `Cslib.Crypto.MLDSA.selfTargetMap`, `Cslib.Crypto.MLDSA.IsSelfTargetSolution`,
  `Cslib.Crypto.MLDSA.selfTargetHash`: self-target MSIS for `[I_k | A | -t]`.
* `Cslib.Crypto.MLDSA.forgeryLowPart`: the low part `-LowBits(A z - c t)` of a forgery.
* `Cslib.Crypto.MLDSA.keyLaw`, `Cslib.Crypto.MLDSA.uniformKeyLaw`: honest and uniform keys.
* `Cslib.Crypto.MLDSA.koaGame`, `Cslib.Crypto.MLDSA.keyDistinguishGame`,
  `Cslib.Crypto.MLDSA.selfTargetGame`: the key-only forgery, key-distinguishing and self-target
  experiments.
* `Cslib.Crypto.MLDSA.forgeryDistinguisher`, `Cslib.Crypto.MLDSA.selfTargetReduction`: the
  explicit reductions.

## Main results

* `Cslib.Crypto.MLDSA.isSelfTargetSolution_of_verify`: a verifying forgery yields a self-target
  solution.
* `Cslib.Crypto.MLDSA.succProbability_koaGame_le_selfTargetGame`: forging is at most as likely as
  solving self-target MSIS through `selfTargetReduction`, for every key distribution.
* `Cslib.Crypto.MLDSA.succProbability_koaGame_le`: the key-only bound by Module-LWE and
  self-target MSIS.

## References

* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

@[expose] public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability
open scoped NNReal

variable (P : Params)

/-! ### Self-target MSIS -/

/-- The self-target linear map `[I_k | A | -t] · (u, z, c) = u + A z - c t`. -/
def selfTargetMap (pk : PublicKey P) (u : Fin P.k → Fin P.n → ZMod P.q)
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Fin P.n → ZMod P.q) : Fin P.k → Fin P.n → ZMod P.q :=
  u + verifierCommitment P pk z c

/-- A self-target hash, mapping a vector of `R_q^k` and a message to a challenge. -/
abbrev SelfTargetHash := (Fin P.k → Fin P.n → ZMod P.q) × List Bool → (Fin P.n → ZMod P.q)

/-- `(u, z, c)` solves self-target MSIS for `[I_k | A | -t]`, the hash `G`, the bound `ζ` and the
message `M`: `‖u‖_∞ ≤ ζ`, `‖z‖_∞ ≤ ζ`, `c ∈ B_τ` and `G(u + A z - c t, M) = c`. -/
def IsSelfTargetSolution (G : SelfTargetHash P) (ζ : ℕ) (pk : PublicKey P) (msg : List Bool)
    (u : Fin P.k → Fin P.n → ZMod P.q) (z : Fin P.ℓ → Fin P.n → ZMod P.q)
    (c : Fin P.n → ZMod P.q) : Prop :=
  ModuleSIS.inInfNormBound ζ u ∧ ModuleSIS.inInfNormBound ζ z ∧ InBall P.τ c ∧
    G (selfTargetMap P pk u z c, msg) = c

instance (G : SelfTargetHash P) (ζ : ℕ) (pk : PublicKey P) (msg : List Bool)
    (u : Fin P.k → Fin P.n → ZMod P.q) (z : Fin P.ℓ → Fin P.n → ZMod P.q)
    (c : Fin P.n → ZMod P.q) : Decidable (IsSelfTargetSolution P G ζ pk msg u z c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The self-target hash induced by an ML-DSA hash: `G(v, M) = H(HighBits(v), M)`. -/
def selfTargetHash (H : Hash P) : SelfTargetHash P :=
  fun x => H (highBitsVec P x.1, x.2)

/-- The low part `u = -LowBits(A z - c t)` of a candidate signature `(z, c)`. -/
def forgeryLowPart (pk : PublicKey P) (σ : Signature P) : Fin P.k → Fin P.n → ZMod P.q :=
  fun i j => -((lowBits P.q P.γ₂ (verifierCommitment P pk σ.1 σ.2 i j) : ℤ) : ZMod P.q)

variable {P}

/-- `u + (A z - c t) = 2 γ₂ · HighBits(A z - c t)` for the low part `u` of `(z, c)`. -/
theorem selfTargetMap_forgeryLowPart [NeZero P.q] (pk : PublicKey P) (σ : Signature P) :
    selfTargetMap P pk (forgeryLowPart P pk σ) σ.1 σ.2 = fun i j =>
      ((highBits P.q P.γ₂ (verifierCommitment P pk σ.1 σ.2 i j) * (2 * P.γ₂ : ℕ) : ℤ) :
        ZMod P.q) := by
  funext i j
  have h := intCast_highBits_mul_add_lowBits (γ₂ := P.γ₂) (verifierCommitment P pk σ.1 σ.2 i j)
  rw [Int.cast_add] at h
  simp only [selfTargetMap, forgeryLowPart, Pi.add_apply]
  linear_combination -h

/-- **A verifying forgery is a self-target solution.** If `(z, c)` verifies on `M` under `(A, t)`,
then `(-LowBits(A z - c t), z, c)` solves self-target MSIS for `[I_k | A | -t]`, the hash
`H(HighBits(·), ·)` and the bound `max γ₁ γ₂`. -/
theorem isSelfTargetSolution_of_verify (hP : P.Valid) {H : Hash P} {pk : PublicKey P}
    {msg : List Bool} {σ : Signature P} (h : verify P H pk msg σ = true) :
    IsSelfTargetSolution P (selfTargetHash P H) (max P.γ₁ P.γ₂) pk msg
      (forgeryLowPart P pk σ) σ.1 σ.2 := by
  have : NeZero P.q := ⟨by have := hP.one_lt_q; omega⟩
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz, hc⟩, hH⟩ := h
  have hγq : (2 * P.γ₂ : ℤ) < P.q := by
    have h1 := hP.one_lt_q
    have h2 := Nat.le_of_dvd (by omega) hP.two_mul_γ₂_dvd
    have : 2 * P.γ₂ < P.q := by omega
    exact_mod_cast this
  refine ⟨fun i j => ?_, fun i j => ?_, hc, ?_⟩
  · -- `‖u‖_∞ ≤ γ₂`.
    set b := lowBits P.q P.γ₂ (verifierCommitment P pk σ.1 σ.2 i j)
    have hb := abs_lowBits_le (q := P.q) hP.γ₂_pos (verifierCommitment P pk σ.1 σ.2 i j)
    change |(-((b : ℤ) : ZMod P.q)).valMinAbs| ≤ (max P.γ₁ P.γ₂ : ℕ)
    rw [← Int.cast_neg, (ZMod.valMinAbs_spec _ (-b)).mpr ⟨rfl, ?_⟩]
    · rw [abs_neg]
      exact hb.trans (by exact_mod_cast le_max_right _ _)
    · rw [abs_le] at hb
      simp only [Set.mem_Ioc]
      constructor <;> linarith [hb.1, hb.2]
  · -- `‖z‖_∞ < γ₁ - β ≤ γ₁`.
    have := hz i j
    have hγ : ((P.γ₁ : ℕ) : ℤ) ≤ (max P.γ₁ P.γ₂ : ℕ) := by exact_mod_cast le_max_left _ _
    have hβ : (0 : ℤ) ≤ P.β := Int.natCast_nonneg _
    exact le_of_lt (by linarith)
  · -- The hash of `2 γ₂ · HighBits(w')` is the hash of `HighBits(w')`, which is `c`.
    rw [selfTargetHash, selfTargetMap_forgeryLowPart]
    convert hH using 3
    funext i j
    exact highBits_intCast_mul hP.γ₂_pos hP.two_mul_γ₂_dvd (highBits_nonneg hP.γ₂_pos _)
      (highBits_lt hP.γ₂_pos hP.two_mul_γ₂_dvd hP.one_lt_q _)

/-! ### Key distributions and experiments -/

variable (P)

/-- The honest public key is a Module-LWE sample `(A, A s₁ + s₂)` with secret `s₁` and error
`s₂`. -/
theorem SecretKey.publicKey_t (sk : SecretKey P) :
    sk.publicKey.t = ModuleLWE.sample sk.A sk.s₁ sk.s₂ := rfl

/-- Honest public keys: `A` uniform, and every coefficient of `s₁` and `s₂` drawn independently
from `secret` (in ML-DSA, uniform on `[-η, η]`). The deterministic part of key generation is
`SecretKey.publicKey`; this is the semantic key distribution compared in the reduction, in the
style of `ModuleLWE.sampleLaw`, not a sampling program. -/
noncomputable def keyLaw [NeZero P.q] (secret : PMF (ZMod P.q)) : PMF (PublicKey P) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q))
  let s₁ ← PMF.pi fun _ : Fin P.ℓ => PMF.pi fun _ : Fin P.n => secret
  let s₂ ← PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n => secret
  return (SecretKey.mk A s₁ s₂).publicKey

/-- Uniform public keys: `A` and `t` independent and uniform. -/
noncomputable def uniformKeyLaw [NeZero P.q] : PMF (PublicKey P) := do
  let A ← PMF.uniformOfFintype (Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q))
  let t ← PMF.uniformOfFintype (Fin P.k → Fin P.n → ZMod P.q)
  return ⟨A, t⟩

/-- The key-only forgery experiment: sample a public key, run the forger on it, and accept when
its output `(M, σ)` verifies. -/
noncomputable def koaGame (keys : PMF (PublicKey P)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) : Game := do
  let pk ← keys
  let forgery ← ProbComp.eval (adv pk)
  return verify P H pk forgery.1 forgery.2

/-- The key-distinguishing experiment: sample a public key and output the distinguisher's bit. -/
noncomputable def keyDistinguishGame (keys : PMF (PublicKey P))
    (D : PublicKey P → ProbComp Bool) : Game := do
  let pk ← keys
  ProbComp.eval (D pk)

/-- The self-target MSIS experiment for the matrix `[I_k | A | -t]` of a sampled key: accept when
the solver's output is a self-target solution. -/
noncomputable def selfTargetGame (keys : PMF (PublicKey P)) (G : SelfTargetHash P) (ζ : ℕ)
    (B : PublicKey P → ProbComp (List Bool × (Fin P.k → Fin P.n → ZMod P.q) ×
      (Fin P.ℓ → Fin P.n → ZMod P.q) × (Fin P.n → ZMod P.q))) : Game := do
  let pk ← keys
  let out ← ProbComp.eval (B pk)
  return decide (IsSelfTargetSolution P G ζ pk out.1 out.2.1 out.2.2.1 out.2.2.2)

/-- The Module-LWE reduction: run the forger and output whether its forgery verifies. -/
def forgeryDistinguisher (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P))
    (pk : PublicKey P) : ProbComp Bool := do
  let forgery ← adv pk
  return verify P H pk forgery.1 forgery.2

/-- The self-target MSIS reduction: run the forger on `(A, t)` and output its message, the low
part of its signature, and the signature. -/
def selfTargetReduction (adv : PublicKey P → ProbComp (List Bool × Signature P))
    (pk : PublicKey P) : ProbComp (List Bool × (Fin P.k → Fin P.n → ZMod P.q) ×
      (Fin P.ℓ → Fin P.n → ZMod P.q) × (Fin P.n → ZMod P.q)) := do
  let forgery ← adv pk
  return (forgery.1, forgeryLowPart P pk forgery.2, forgery.2.1, forgery.2.2)

variable {P}

/-- The forgery experiment is the key-distinguishing experiment of `forgeryDistinguisher`. -/
theorem koaGame_eq_keyDistinguishGame (keys : PMF (PublicKey P)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    koaGame P keys H adv = keyDistinguishGame P keys (forgeryDistinguisher P H adv) := by
  simp only [koaGame, keyDistinguishGame, forgeryDistinguisher, ProbComp.eval_bind,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]

/-- **Forging reduces to self-target MSIS.** For every key distribution, a key-only forger
succeeds at most as often as `selfTargetReduction` solves self-target MSIS for the hash
`H(HighBits(·), ·)` and the bound `max γ₁ γ₂`. -/
theorem succProbability_koaGame_le_selfTargetGame (hP : P.Valid) (keys : PMF (PublicKey P))
    (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    (koaGame P keys H adv).succProbability ≤
      (selfTargetGame P keys (selfTargetHash P H) (max P.γ₁ P.γ₂)
        (selfTargetReduction P adv)).succProbability := by
  apply ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
  simp only [koaGame, selfTargetGame, selfTargetReduction, ProbComp.eval_bind,
    ProbComp.eval_pure, Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun pk _ => ?_
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun forgery _ => ?_
  by_cases hv : verify P H pk forgery.1 forgery.2 = true
  · rw [hv, decide_eq_true (isSelfTargetSolution_of_verify hP hv)]
  · rw [Bool.not_eq_true] at hv
    rw [hv]
    simp

/-- **Key-only unforgeability from Module-LWE and self-target MSIS.** Against honest keys, the
success probability of a key-only forger is at most the advantage of `forgeryDistinguisher` in
distinguishing honest from uniform keys, plus the success probability of `selfTargetReduction`
against self-target MSIS for a uniform matrix `[A | t]`. -/
theorem succProbability_koaGame_le (hP : P.Valid) [NeZero P.q] (secret : PMF (ZMod P.q))
    (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    (koaGame P (keyLaw P secret) H adv).succProbability ≤
      Game.advantage (keyDistinguishGame P (keyLaw P secret) (forgeryDistinguisher P H adv))
          (keyDistinguishGame P (uniformKeyLaw P) (forgeryDistinguisher P H adv)) +
        (selfTargetGame P (uniformKeyLaw P) (selfTargetHash P H) (max P.γ₁ P.γ₂)
          (selfTargetReduction P adv)).succProbability := by
  have hst := succProbability_koaGame_le_selfTargetGame hP (uniformKeyLaw P) H adv
  rw [koaGame_eq_keyDistinguishGame] at hst ⊢
  rw [← NNReal.coe_le_coe] at hst ⊢
  rw [NNReal.coe_add, Game.coe_advantage]
  linarith [le_abs_self
    (((keyDistinguishGame P (keyLaw P secret) (forgeryDistinguisher P H adv)).succProbability :
      ℝ) - (keyDistinguishGame P (uniformKeyLaw P) (forgeryDistinguisher P H adv)).succProbability)]

end Cslib.Crypto.MLDSA
