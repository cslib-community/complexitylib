/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.Hint
public import CslibFrontier.Crypto.Computational.MLDSA.KeyOnly
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import Mathlib.Tactic.LinearCombination

/-!
# ML-DSA compressed-verification key-only reduction

The Dilithium v3.1 verifier does not hash `HighBits(Az - ct)` directly. It uses the rounded
public-key component `t₁`, computes `r = Az - c t₁ 2ᵈ`, and recovers the hashed high part as
`UseHint(h, r, 2γ₂)`. Section 6.2.1, equations (9)--(12), rewrites every verifying key-only
forgery as a solution of self-target Module-SIS. This module formalizes that algebra and the
resulting semantic key-only reduction.

This remains the simplified proof model: the public input is the full pair `(A, t)`, from which
verification computes `t₁`; the hash is fixed; and there are no signing queries. Seed expansion,
codecs, message representatives, the hint-weight check, bounded signing failure, strong
unforgeability, and classical/QROM Fiat--Shamir transformations are not represented here.

## Main definitions

* `Cslib.Crypto.MLDSA.CompressedSignature`: a response, hint vector, and challenge.
* `Cslib.Crypto.MLDSA.publicKeyHighTerm`, `Cslib.Crypto.MLDSA.publicKeyLowPart`: the terms
  `t₁ 2ᵈ` and `t₀` from `Power2Round`.
* `Cslib.Crypto.MLDSA.compressedVerifierCommitment`,
  `Cslib.Crypto.MLDSA.compressedVerify`: the compressed-verification surface.
* `Cslib.Crypto.MLDSA.compressedForgeryLowPart`,
  `Cslib.Crypto.MLDSA.SelfTargetCandidate.ofCompressedForgery`: the explicit
  self-target candidate of equations (9)--(10).
* `Cslib.Crypto.MLDSA.compressedKoaGame`,
  `Cslib.Crypto.MLDSA.compressedForgeryDistinguisher`,
  `Cslib.Crypto.MLDSA.compressedSelfTargetReduction`: the semantic key-only games and
  reductions.

## Main results

* `Cslib.Crypto.MLDSA.isSelfTargetSolution_of_compressedVerify`: every compressed-verification
  forgery solves self-target Module-SIS at
  `max (γ₁ - β) (2γ₂ + 1 + τ 2^(d-1))`.
* `Cslib.Crypto.MLDSA.succProbability_compressedKoaGame_le`: compressed key-only success is at
  most the short-law Module-LWE advantage plus the uniform-key self-target success probability.

## References

* [S. Bai et al., *CRYSTALS-Dilithium: Algorithm Specifications and Supporting
  Documentation*, Version 3.1][BaiEtAl2021Dilithium]
* [National Institute of Standards and Technology, *Module-Lattice-Based Digital Signature
  Standard*][NISTFIPS204]
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.Probability
open scoped NNReal

variable (P : Params)

/-- A signature for the compressed-verification proof surface: response `z`, hint vector `h`,
and challenge `c`. Unlike the final FIPS 204 byte string, this semantic value has no codec or
malformed-input behavior. -/
@[ext] structure CompressedSignature where
  /-- The response `z`. -/
  z : Fin P.ℓ → Fin P.n → ZMod P.q
  /-- The coefficientwise hint vector. -/
  h : Fin P.k → Fin P.n → Bool
  /-- The challenge polynomial. -/
  c : Fin P.n → ZMod P.q

/-- The public-key high term `t₁ 2ᵈ`, computed from the full semantic `t`. -/
@[expose] def publicKeyHighTerm (d : ℕ) (pk : PublicKey P) : Fin P.k → Fin P.n → ZMod P.q :=
  fun i j => (((power2RoundVec P.q d pk.t).1 i j * (2 ^ d : ℕ) : ℤ) : ZMod P.q)

/-- The public-key low term `t₀`, computed from the full semantic `t`. -/
@[expose] def publicKeyLowPart (d : ℕ) (pk : PublicKey P) : Fin P.k → Fin P.n → ZMod P.q :=
  fun i j => (((power2RoundVec P.q d pk.t).2 i j : ℤ) : ZMod P.q)

variable {P}

/-- `Power2Round` gives `t = t₁ 2ᵈ + t₀` coefficientwise. -/
theorem publicKeyHighTerm_add_lowPart [NeZero P.q] (d : ℕ) (pk : PublicKey P) :
    publicKeyHighTerm P d pk + publicKeyLowPart P d pk = pk.t := by
  funext i j
  have h := congrFun (congrFun (power2RoundVec_reconstruct (d := d) pk.t) i) j
  simp only [publicKeyHighTerm, publicKeyLowPart, Pi.add_apply]
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using h

variable (P)

/-- The compressed verifier's commitment `r = A z - c (t₁ 2ᵈ)`. -/
@[expose] def compressedVerifierCommitment (d : ℕ) (pk : PublicKey P)
    (z : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Fin P.n → ZMod P.q) :
    Fin P.k → Fin P.n → ZMod P.q :=
  moduleSISMap pk.A z - fun i => negacyclicMul c (publicKeyHighTerm P d pk i)

/-- Compressed verification in the simplified proof model. It checks the response and challenge,
then hashes `UseHint(h, A z - c t₁ 2ᵈ, 2γ₂)`. The final FIPS hint-weight and byte-codec checks are
not part of this semantic surface. -/
@[expose] def compressedVerify (d : ℕ) (H : Hash P) (pk : PublicKey P) (msg : List Bool)
    (σ : CompressedSignature P) : Bool :=
  decide (ResponseShort P σ.z) && decide (InBall P.τ σ.c) &&
    decide (H (fun i => useHintVec P.q P.γ₂ (σ.h i)
      (compressedVerifierCommitment P d pk σ.z σ.c i), msg) = σ.c)

/-- The low component `u' = u + c t₀` from equation (10), where `u` is the arbitrary-hint
residual of equation (9). -/
def compressedForgeryLowPart (d : ℕ) (pk : PublicKey P) (σ : CompressedSignature P) :
    Fin P.k → Fin P.n → ZMod P.q :=
  fun i j =>
    hintResidual P.q P.γ₂ (σ.h i j) (compressedVerifierCommitment P d pk σ.z σ.c i j) +
      negacyclicMul σ.c (publicKeyLowPart P d pk i) j

/-- The self-target candidate read from a compressed-verification forgery. -/
def SelfTargetCandidate.ofCompressedForgery (d : ℕ) (pk : PublicKey P) (msg : List Bool)
    (σ : CompressedSignature P) : SelfTargetCandidate P :=
  ⟨msg, compressedForgeryLowPart P d pk σ, σ.z, σ.c⟩

/-- The conservative self-target radius from Dilithium v3.1 equation (7). -/
def compressedSelfTargetRadius (d : ℕ) : ℕ :=
  max (P.γ₁ - P.β) (2 * P.γ₂ + 1 + P.τ * 2 ^ (d - 1))

variable {P}

/-- Equations (9)--(10): adding the forged low component to `A z - c t` gives the hinted high
part multiplied by `2γ₂`. -/
theorem selfTargetMap_compressedForgeryLowPart [NeZero P.q] (d : ℕ) (pk : PublicKey P)
    (σ : CompressedSignature P) :
    selfTargetMap P pk (compressedForgeryLowPart P d pk σ) σ.z σ.c = fun i j =>
      ((useHint P.q P.γ₂ (σ.h i j)
        (compressedVerifierCommitment P d pk σ.z σ.c i j) * (2 * P.γ₂ : ℕ) : ℤ) :
          ZMod P.q) := by
  funext i j
  have ht := congrFun (publicKeyHighTerm_add_lowPart d pk) i
  simp only [Pi.add_apply] at ht
  rw [useHint_mul_eq_add_hintResidual]
  simp only [selfTargetMap, compressedForgeryLowPart, verifierCommitment,
    compressedVerifierCommitment, Pi.add_apply, Pi.sub_apply]
  rw [← ht, negacyclicMul_add]
  simp only [Pi.add_apply]
  ring

private theorem abs_valMinAbs_add_le {q : ℕ} (a b : ZMod q) :
    |(a + b).valMinAbs| ≤ |a.valMinAbs| + |b.valMinAbs| := by
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs, Int.abs_eq_natAbs]
  norm_cast
  exact (ZMod.natAbs_valMinAbs_add_le a b).trans (Int.natAbs_add_le _ _)

/-- **A compressed-verification forgery is a self-target solution.** This is the formal
counterpart of Dilithium v3.1 Section 6.2.1, equations (9)--(12), with the source condition
`q > 4γ₂` explicit. -/
theorem isSelfTargetSolution_of_compressedVerify (hP : P.Valid) (hγq : 4 * P.γ₂ < P.q)
    {d : ℕ} (hd : 0 < d) {H : Hash P} {pk : PublicKey P} {msg : List Bool}
    {σ : CompressedSignature P} (h : compressedVerify P d H pk msg σ = true) :
    IsSelfTargetSolution P (selfTargetHash P H) (compressedSelfTargetRadius P d) pk
      (SelfTargetCandidate.ofCompressedForgery P d pk msg σ) := by
  have : NeZero P.q := ⟨by have := hP.one_lt_q; omega⟩
  simp only [compressedVerify, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz, hc⟩, hH⟩ := h
  simp only [IsSelfTargetSolution, SelfTargetCandidate.ofCompressedForgery,
    compressedSelfTargetRadius]
  refine ⟨fun i j => ?_, fun i j => ?_, hc, ?_⟩
  · have hres := abs_hintResidual_valMinAbs_le hP.γ₂_pos hP.two_mul_γ₂_dvd hγq
      (σ.h i j) (compressedVerifierCommitment P d pk σ.z σ.c i j)
    have ht₀ : ∀ j', |(publicKeyLowPart P d pk i j').valMinAbs| ≤ 2 ^ (d - 1) :=
      fun j' => by
        unfold publicKeyLowPart
        exact (ZMod.abs_valMinAbs_intCast_le _).trans
          (abs_power2RoundVec_low_le (q := P.q) hd pk.t i j')
    have hct₀ := abs_valMinAbs_negacyclicMul_le (s := publicKeyLowPart P d pk i) hc ht₀ j
    have hmax :
        ((2 * P.γ₂ + 1 + P.τ * 2 ^ (d - 1) : ℕ) : ℤ) ≤
          ((max (P.γ₁ - P.β) (2 * P.γ₂ + 1 + P.τ * 2 ^ (d - 1)) : ℕ) : ℤ) := by
      exact_mod_cast (le_max_right (P.γ₁ - P.β)
        (2 * P.γ₂ + 1 + P.τ * 2 ^ (d - 1)))
    exact (abs_valMinAbs_add_le _ _).trans ((add_le_add hres hct₀).trans hmax)
  · have hz' := hz i j
    have hβγ : P.β ≤ P.γ₁ := by
      have hnonneg : (0 : ℤ) ≤ |(σ.z i j).valMinAbs| := abs_nonneg _
      omega
    have hle : |(σ.z i j).valMinAbs| ≤ (P.γ₁ - P.β : ℕ) := by
      exact_mod_cast le_of_lt hz'
    exact hle.trans (by
      exact_mod_cast (le_max_left (P.γ₁ - P.β)
        (2 * P.γ₂ + 1 + P.τ * 2 ^ (d - 1))))
  · rw [selfTargetHash, selfTargetMap_compressedForgeryLowPart]
    convert hH using 3
    funext i j
    exact highBits_intCast_mul hP.γ₂_pos hP.two_mul_γ₂_dvd
      (useHint_nonneg hP.γ₂_pos hγq _ _)
      (useHint_lt hP.γ₂_pos hP.two_mul_γ₂_dvd hγq _ _)

/-! ### Compressed key-only games and reductions -/

variable (P)

/-- The compressed key-only forgery experiment for a fixed public key. -/
def compressedKoaExperiment (d : ℕ) (H : Hash P) (pk : PublicKey P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) : ProbComp Bool := do
  let (msg, σ) ← adv pk
  return compressedVerify P d H pk msg σ

/-- The compressed key-only forgery game under a supplied key distribution. -/
noncomputable def compressedKoaGame (d : ℕ) (keys : PMF (PublicKey P)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) : Game :=
  keys.bind fun pk => (compressedKoaExperiment P d H pk adv).eval

/-- The Module-LWE distinguisher induced by a compressed key-only forger. -/
def compressedForgeryDistinguisher (d : ℕ) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P))
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q))
    (t : Fin P.k → Fin P.n → ZMod P.q) : ProbComp Bool :=
  compressedKoaExperiment P d H ⟨A, t⟩ adv

/-- The self-target solver induced by a compressed key-only forger. -/
def compressedSelfTargetReduction (d : ℕ)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P))
    (pk : PublicKey P) : ProbComp (SelfTargetCandidate P) := do
  let (msg, σ) ← adv pk
  return SelfTargetCandidate.ofCompressedForgery P d pk msg σ

variable {P}

/-- The honest-key compressed game is the real short-law Module-LWE game of the explicit
distinguisher. -/
theorem compressedKoaGame_keyLaw [NeZero P.q] (d : ℕ) (secret : PMF (ZMod P.q)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) :
    compressedKoaGame P d (keyLaw P secret) H adv =
      ModuleLWE.realGame (PMF.pi fun _ : Fin P.ℓ => PMF.pi fun _ : Fin P.n => secret)
        (PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n => secret)
        (compressedForgeryDistinguisher P d H adv) := by
  rw [ModuleLWE.realGame_eq_uniform_bind]
  simp only [compressedKoaGame, keyLaw, compressedForgeryDistinguisher,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  rfl

/-- The uniform-key compressed game is the random Module-LWE game of the explicit
distinguisher. -/
theorem compressedKoaGame_uniformKeyLaw [NeZero P.q] (d : ℕ) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) :
    compressedKoaGame P d (uniformKeyLaw P) H adv =
      ModuleLWE.randomGame (compressedForgeryDistinguisher P d H adv) := by
  simp only [compressedKoaGame, uniformKeyLaw, ModuleLWE.randomGame,
    ModuleLWE.eval_randomExperiment, compressedForgeryDistinguisher,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]

/-- For every key distribution, compressed forging is at most as likely as solving self-target
Module-SIS through the explicit reduction. -/
theorem succProbability_compressedKoaGame_le_selfTargetGame (hP : P.Valid)
    (hγq : 4 * P.γ₂ < P.q) {d : ℕ} (hd : 0 < d) (keys : PMF (PublicKey P)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) :
    (compressedKoaGame P d keys H adv).succProbability ≤
      (selfTargetGame P keys (selfTargetHash P H) (compressedSelfTargetRadius P d)
        (compressedSelfTargetReduction P d adv)).succProbability := by
  refine Game.succProbability_mono
    (Probability.PMF.bind_apply_mono_on_support _ _ fun pk _ => ?_)
  simp only [compressedKoaExperiment, selfTargetExperiment, compressedSelfTargetReduction,
    bind_assoc, pure_bind, ProbComp.eval_bind, ProbComp.eval_pure]
  refine Probability.PMF.bind_apply_mono_on_support _ _ fun ⟨msg, σ⟩ _ => ?_
  by_cases hv : compressedVerify P d H pk msg σ = true
  · rw [hv, decide_eq_true (isSelfTargetSolution_of_compressedVerify hP hγq hd hv)]
  · rw [Bool.not_eq_true] at hv
    simp [hv]

/-- **Compressed key-only unforgeability from Module-LWE and self-target MSIS.** Against honest
keys, success is at most the short-law Module-LWE advantage of the explicit distinguisher plus
the uniform-key success probability of the explicit self-target solver. This semantic finite-game
inequality supplies neither executable resource bounds nor an asymptotic/negligible corollary. -/
theorem succProbability_compressedKoaGame_le (hP : P.Valid) (hγq : 4 * P.γ₂ < P.q)
    [NeZero P.q] {d : ℕ} (hd : 0 < d) (secret : PMF (ZMod P.q)) (H : Hash P)
    (adv : PublicKey P → ProbComp (List Bool × CompressedSignature P)) :
    (compressedKoaGame P d (keyLaw P secret) H adv).succProbability ≤
      ModuleLWE.advantage (PMF.pi fun _ : Fin P.ℓ => PMF.pi fun _ : Fin P.n => secret)
          (PMF.pi fun _ : Fin P.k => PMF.pi fun _ : Fin P.n => secret)
          (compressedForgeryDistinguisher P d H adv) +
        (selfTargetGame P (uniformKeyLaw P) (selfTargetHash P H)
          (compressedSelfTargetRadius P d)
          (compressedSelfTargetReduction P d adv)).succProbability := by
  have hst := succProbability_compressedKoaGame_le_selfTargetGame hP hγq hd
    (uniformKeyLaw P) H adv
  rw [compressedKoaGame_uniformKeyLaw] at hst
  rw [compressedKoaGame_keyLaw, ModuleLWE.advantage, add_comm]
  exact (Game.succProbability_le_add_of_advantage_le le_rfl).trans (add_le_add hst le_rfl)

end Cslib.Crypto.MLDSA
