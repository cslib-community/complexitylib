/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.LWE.Module
public import CslibFrontier.Crypto.Computational.MLDSA.Basic
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Probability.Product
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# ML-DSA forgeries, self-target MSIS and Module-LWE: the key-only reduction

The security argument for Dilithium ([DucasEtAl2018]) replaces the public key `t = A s₁ + s₂`
by a uniform vector, which costs a Module-LWE distinguishing advantage, and then turns a forgery
against a *uniform* key into a solution of the *self-target* Module-SIS problem for the matrix
`[I_k | A | -t]`. This module formalizes both steps for key-only attacks (no signing queries,
fixed hash function), with explicit reductions:

* **Self-target MSIS.** `IsSelfTargetSolution G ζ pk s` says that the candidate
  `s = (M, u, z, c)` (a `SelfTargetCandidate`) is a solution: `‖u‖_∞, ‖z‖_∞ ≤ ζ`, `c ∈ B_τ`, and
  `G(u + A z - c t, M) = c` for the hash `G`.
* **From a forgery to a self-target solution.** If `(z, c)` verifies on `M`, write
  `w' = A z - c t` and `u = -LowBits(w')`. Then `u + w' = 2 γ₂ · HighBits(w')`, whose high bits
  are again `HighBits(w')` by uniqueness of the decomposition, so `(M, u, z, c)`
  (`SelfTargetCandidate.ofForgery`) is a self-target solution for the hash
  `G(v, M) = H(HighBits(v), M)` with `ζ = max γ₁ γ₂` (`isSelfTargetSolution_of_verify`). This step
  is deterministic and holds for every key.
* **Experiments.** For a fixed public key, `koaExperiment` and `selfTargetExperiment` are
  `ProbComp Bool` programs. The games `koaGame` and `selfTargetGame` draw the key from a key
  distribution and run the experiment on it.
* **Key-only unforgeability.** The honest key `(A, A s₁ + s₂)` is a Module-LWE sample with short
  secret `s₁` and error `s₂` (`SecretKey.publicKey_t`), so the forgery game for honest keys
  (`keyLaw`) is the real Module-LWE game of the explicit distinguisher `forgeryDistinguisher`
  (`koaGame_keyLaw`), and for uniform keys (`uniformKeyLaw`) it is the random one
  (`koaGame_uniformKeyLaw`). The success probability of any key-only forger is therefore at most
  the Module-LWE advantage `ModuleLWE.advantage` of `forgeryDistinguisher` for these short laws,
  plus the success probability of the explicit solver `selfTargetReduction` against self-target
  MSIS for a uniform matrix `[A | t]` (`succProbability_koaGame_le`). The uniform-secret
  `Cslib.Crypto.DecisionModuleLWE` does not bound that advantage.

Hardness of self-target MSIS for the hash `H(HighBits(·), ·)` is the assumption, as in
[DucasEtAl2018]; it is neither proved nor reduced to standard Module-SIS here.

This is the key-only core of the reduction. Chosen-message security additionally simulates the
signing oracle (zero knowledge of the aborting identification scheme, in the random-oracle
model); that step, and the asymptotic packaging, are not formalized here.

## Main definitions

* `Cslib.Crypto.MLDSA.selfTargetMap`, `Cslib.Crypto.MLDSA.SelfTargetCandidate`,
  `Cslib.Crypto.MLDSA.IsSelfTargetSolution`, `Cslib.Crypto.MLDSA.selfTargetHash`: self-target
  MSIS for `[I_k | A | -t]`.
* `Cslib.Crypto.MLDSA.forgeryLowPart`, `Cslib.Crypto.MLDSA.SelfTargetCandidate.ofForgery`: the
  low part `-LowBits(A z - c t)` of a forgery and the candidate it gives.
* `Cslib.Crypto.MLDSA.keyLaw`, `Cslib.Crypto.MLDSA.uniformKeyLaw`: honest and uniform keys.
* `Cslib.Crypto.MLDSA.koaExperiment`, `Cslib.Crypto.MLDSA.selfTargetExperiment`: the key-only
  forgery and self-target experiments for a fixed public key.
* `Cslib.Crypto.MLDSA.koaGame`, `Cslib.Crypto.MLDSA.selfTargetGame`: the same experiments with
  the key drawn from a key distribution.
* `Cslib.Crypto.MLDSA.forgeryDistinguisher`, `Cslib.Crypto.MLDSA.selfTargetReduction`: the
  explicit reductions.

## Main results

* `Cslib.Crypto.MLDSA.isSelfTargetSolution_of_verify`: a verifying forgery yields a self-target
  solution.
* `Cslib.Crypto.MLDSA.succProbability_koaGame_le_selfTargetGame`: forging is at most as likely as
  solving self-target MSIS through `selfTargetReduction`, for every key distribution.
* `Cslib.Crypto.MLDSA.koaGame_keyLaw`, `Cslib.Crypto.MLDSA.koaGame_uniformKeyLaw`: the forgery
  games for honest and uniform keys are the Module-LWE games of `forgeryDistinguisher`.
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

/-- A candidate solution `(M, u, z, c)` to self-target MSIS: a message, a low part
`u ∈ R_q^k`, a response `z ∈ R_q^ℓ` and a challenge `c ∈ R_q`. -/
structure SelfTargetCandidate where
  /-- The message. -/
  msg : List Bool
  /-- The low part `u`. -/
  u : Fin P.k → Fin P.n → ZMod P.q
  /-- The response `z`. -/
  z : Fin P.ℓ → Fin P.n → ZMod P.q
  /-- The challenge `c`. -/
  c : Fin P.n → ZMod P.q

/-- `s = (M, u, z, c)` solves self-target MSIS for `[I_k | A | -t]`, the hash `G` and the bound `ζ`:
`‖u‖_∞ ≤ ζ`, `‖z‖_∞ ≤ ζ`, `c ∈ B_τ` and `G(u + A z - c t, M) = c`. -/
def IsSelfTargetSolution (G : SelfTargetHash P) (ζ : ℕ) (pk : PublicKey P)
    (s : SelfTargetCandidate P) : Prop :=
  ModuleSIS.inInfNormBound ζ s.u ∧ ModuleSIS.inInfNormBound ζ s.z ∧ InBall P.τ s.c ∧
    G (selfTargetMap P pk s.u s.z s.c, s.msg) = s.c

instance (G : SelfTargetHash P) (ζ : ℕ) (pk : PublicKey P) (s : SelfTargetCandidate P) :
    Decidable (IsSelfTargetSolution P G ζ pk s) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The self-target hash induced by an ML-DSA hash: `G(v, M) = H(HighBits(v), M)`. -/
def selfTargetHash (H : Hash P) : SelfTargetHash P :=
  fun x => H (highBitsVec P x.1, x.2)

/-- The low part `u = -LowBits(A z - c t)` of a candidate signature `(z, c)`. -/
def forgeryLowPart (pk : PublicKey P) (σ : Signature P) : Fin P.k → Fin P.n → ZMod P.q :=
  fun i j => -((lowBits P.q P.γ₂ (verifierCommitment P pk σ.z σ.c i j) : ℤ) : ZMod P.q)

/-- The self-target candidate `(M, -LowBits(A z - c t), z, c)` read off a forgery `(M, (z, c))`. -/
def SelfTargetCandidate.ofForgery (pk : PublicKey P) (msg : List Bool) (σ : Signature P) :
    SelfTargetCandidate P :=
  ⟨msg, forgeryLowPart P pk σ, σ.z, σ.c⟩

variable {P}

/-- `u + (A z - c t) = 2 γ₂ · HighBits(A z - c t)` for the low part `u` of `(z, c)`. -/
theorem selfTargetMap_forgeryLowPart [NeZero P.q] (pk : PublicKey P) (σ : Signature P) :
    selfTargetMap P pk (forgeryLowPart P pk σ) σ.z σ.c = fun i j =>
      ((highBits P.q P.γ₂ (verifierCommitment P pk σ.z σ.c i j) * (2 * P.γ₂ : ℕ) : ℤ) :
        ZMod P.q) := by
  funext i j
  have h := intCast_highBits_mul_add_lowBits (γ₂ := P.γ₂) (verifierCommitment P pk σ.z σ.c i j)
  rw [Int.cast_add] at h
  simp only [selfTargetMap, forgeryLowPart, Pi.add_apply]
  linear_combination -h

/-- **A verifying forgery is a self-target solution.** If `(z, c)` verifies on `M` under `(A, t)`,
then `(-LowBits(A z - c t), z, c)` solves self-target MSIS for `[I_k | A | -t]`, the hash
`H(HighBits(·), ·)` and the bound `max γ₁ γ₂`. -/
theorem isSelfTargetSolution_of_verify (hP : P.Valid) {H : Hash P} {pk : PublicKey P}
    {msg : List Bool} {σ : Signature P} (h : verify P H pk msg σ = true) :
    IsSelfTargetSolution P (selfTargetHash P H) (max P.γ₁ P.γ₂) pk
      (SelfTargetCandidate.ofForgery P pk msg σ) := by
  have : NeZero P.q := ⟨by have := hP.one_lt_q; omega⟩
  simp only [IsSelfTargetSolution, SelfTargetCandidate.ofForgery]
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz, hc⟩, hH⟩ := h
  have hγq : (2 * P.γ₂ : ℤ) < P.q := by
    have h1 := hP.one_lt_q
    have h2 := Nat.le_of_dvd (by omega) hP.two_mul_γ₂_dvd
    have : 2 * P.γ₂ < P.q := by omega
    exact_mod_cast this
  refine ⟨fun i j => ?_, fun i j => ?_, hc, ?_⟩
  · -- `‖u‖_∞ ≤ γ₂`.
    set b := lowBits P.q P.γ₂ (verifierCommitment P pk σ.z σ.c i j)
    have hb := abs_lowBits_le (q := P.q) hP.γ₂_pos (verifierCommitment P pk σ.z σ.c i j)
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

/-- The key-only forgery experiment for a fixed public key `pk`: run the forger on `pk` and accept
when its output `(M, σ)` verifies. -/
def koaExperiment (H : Hash P) (pk : PublicKey P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) : ProbComp Bool := do
  let (msg, σ) ← adv pk
  return verify P H pk msg σ

/-- The self-target MSIS experiment for the matrix `[I_k | A | -t]` of a fixed public key `pk`:
accept when the solver's candidate is a self-target solution. -/
def selfTargetExperiment (G : SelfTargetHash P) (ζ : ℕ) (pk : PublicKey P)
    (B : PublicKey P → ProbComp (SelfTargetCandidate P)) : ProbComp Bool := do
  let s ← B pk
  return decide (IsSelfTargetSolution P G ζ pk s)

/-- The key-only forgery game: draw a public key from `keys` and run `koaExperiment`. -/
noncomputable def koaGame (keys : PMF (PublicKey P)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) : Game :=
  keys.bind fun pk => (koaExperiment P H pk adv).eval

/-- The self-target MSIS game: draw a public key from `keys` and run `selfTargetExperiment`. -/
noncomputable def selfTargetGame (keys : PMF (PublicKey P)) (G : SelfTargetHash P) (ζ : ℕ)
    (B : PublicKey P → ProbComp (SelfTargetCandidate P)) : Game :=
  keys.bind fun pk => (selfTargetExperiment P G ζ pk B).eval

/-- The Module-LWE reduction: read the sample `(A, t)` as a public key, run the forger and output
whether its forgery verifies, that is, run `koaExperiment` on `(A, t)`. -/
def forgeryDistinguisher (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P))
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)) (t : Fin P.k → Fin P.n → ZMod P.q) :
    ProbComp Bool :=
  koaExperiment P H ⟨A, t⟩ adv

/-- The self-target MSIS reduction: run the forger on `(A, t)` and read its forgery as a
self-target candidate. -/
def selfTargetReduction (adv : PublicKey P → ProbComp (List Bool × Signature P))
    (pk : PublicKey P) : ProbComp (SelfTargetCandidate P) := do
  let (msg, σ) ← adv pk
  return SelfTargetCandidate.ofForgery P pk msg σ

variable {P}

/-- The forgery game for honest keys is the real Module-LWE game of `forgeryDistinguisher`, with
secret `s₁` and error `s₂` drawn coefficientwise from `secret`. -/
theorem koaGame_keyLaw [NeZero P.q] (secret : PMF (ZMod P.q)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    koaGame P (keyLaw P secret) H adv =
      ModuleLWE.realGame (PMF.pi fun _ : Fin P.ℓ => PMF.pi fun _ : Fin P.n => secret)
        (PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n => secret)
        (forgeryDistinguisher P H adv) := by
  rw [ModuleLWE.realGame_eq_uniform_bind]
  simp only [koaGame, keyLaw, forgeryDistinguisher, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rfl

/-- The forgery game for uniform keys is the random Module-LWE game of `forgeryDistinguisher`. -/
theorem koaGame_uniformKeyLaw [NeZero P.q] (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    koaGame P (uniformKeyLaw P) H adv = ModuleLWE.randomGame (forgeryDistinguisher P H adv) := by
  simp only [koaGame, uniformKeyLaw, ModuleLWE.randomGame, ModuleLWE.eval_randomExperiment,
    forgeryDistinguisher, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind]

/-- **Forging reduces to self-target MSIS.** For every key distribution, a key-only forger
succeeds at most as often as `selfTargetReduction` solves self-target MSIS for the hash
`H(HighBits(·), ·)` and the bound `max γ₁ γ₂`. -/
theorem succProbability_koaGame_le_selfTargetGame (hP : P.Valid) (keys : PMF (PublicKey P))
    (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    (koaGame P keys H adv).succProbability ≤
      (selfTargetGame P keys (selfTargetHash P H) (max P.γ₁ P.γ₂)
        (selfTargetReduction P adv)).succProbability := by
  refine Game.succProbability_mono
    (Probability.PMF.bind_apply_mono_on_support _ _ fun pk _ => ?_)
  simp only [koaExperiment, selfTargetExperiment, selfTargetReduction, bind_assoc, pure_bind,
    ProbComp.eval_bind, ProbComp.eval_pure]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ⟨msg, σ⟩ _ => ?_
  by_cases hv : verify P H pk msg σ = true
  · rw [hv, decide_eq_true (isSelfTargetSolution_of_verify hP hv)]
  · rw [Bool.not_eq_true] at hv
    simp [hv]

/-- **Key-only unforgeability from Module-LWE and self-target MSIS.** Against honest keys, the
success probability of a key-only forger is at most the Module-LWE advantage of
`forgeryDistinguisher`, with secret and error drawn coefficientwise from `secret`, plus the success
probability of `selfTargetReduction` against self-target MSIS for a uniform matrix `[A | t]`. -/
theorem succProbability_koaGame_le (hP : P.Valid) [NeZero P.q] (secret : PMF (ZMod P.q))
    (H : Hash P) (adv : PublicKey P → ProbComp (List Bool × Signature P)) :
    (koaGame P (keyLaw P secret) H adv).succProbability ≤
      ModuleLWE.advantage (PMF.pi fun _ : Fin P.ℓ => PMF.pi fun _ : Fin P.n => secret)
          (PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n => secret)
          (forgeryDistinguisher P H adv) +
        (selfTargetGame P (uniformKeyLaw P) (selfTargetHash P H) (max P.γ₁ P.γ₂)
          (selfTargetReduction P adv)).succProbability := by
  have hst := succProbability_koaGame_le_selfTargetGame hP (uniformKeyLaw P) H adv
  rw [koaGame_uniformKeyLaw] at hst
  rw [koaGame_keyLaw, ModuleLWE.advantage, add_comm]
  exact (Game.succProbability_le_add_of_advantage_le le_rfl).trans (add_le_add hst le_rfl)

end Cslib.Crypto.MLDSA
