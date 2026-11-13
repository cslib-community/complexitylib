/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Padding
public import CslibFrontier.Crypto.Computational.DiffieHellman.EncodingBounds
public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Languages.Probabilistic.LinearHash
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Probabilistic.LinearHash
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.Collision
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT

/-!
# Unconditionally Secure Key Derivation for Hashed ElGamal via the Leftover Hash Lemma

In [BonehShoup2023], Section 8.10.4 (Theorem 8.11, p. 334) and Section 11.5.2 (p. 449), a universal
hash function whose key is placed in the public system parameter yields an unconditionally secure
key derivation function (`SecureKDF`, Attack Game 11.3, pp. 448–449, and Definition 11.5, p. 449)
via the Leftover Hash Lemma, without any computational assumptions on the hash family.

* **Paraphrase of [BonehShoup2023], Section 8.10.4, Theorem 8.11 (p. 334, Leftover Hash Lemma):**
  for a $(1 + \alpha)/N$-universal keyed hash function $H$ over $(\mathcal{K}, \mathcal{S},
  \mathcal{T})$ with $N = |\mathcal{T}|$, if $k$ is uniform on $\mathcal{K}$ and $s_1, \dots, s_m$
  are independent of $k$ and of each other with guessing/collision probability at most $\gamma$,
  the statistical distance $\delta$ between $(k, H(k, s_1), \dots, H(k, s_m))$ and the uniform
  distribution on $\mathcal{K} \times \mathcal{T}^m$ satisfies
  $\delta \le \frac{1}{2} m \sqrt{N \gamma + \alpha}$.
* **Paraphrase of [BonehShoup2023], Section 11.5.2, Attack Game 11.3 and Definition 11.5
  (pp. 448–449):** for $F : \mathcal{X} \times \mathcal{Y} \to \mathcal{Z}$, Experiment $b$ samples
  $x \leftarrow \mathcal{X}$, $y \leftarrow \mathcal{Y}$, sets $z_0 = F(x, y)$, samples uniform
  $z_1 \leftarrow \mathcal{Z}$, and passes $(x, z_b)$ to $\mathcal{A}$; $F$ is a secure KDF if
  $|\Pr[W_0] - \Pr[W_1]|$ is negligible for every efficient adversary $\mathcal{A}$. As noted on
  p. 449:
  > One may even build a secure KDF without making any assumptions at all: the construction in
  > Section 8.10.4 based on a universal hash function and the leftover hash lemma yields an
  > unconditionally secure KDF.

To formalize this over an arbitrary `PrimeOrderGroupFamily`:
1. `PrimeOrderGroupFamily.withSeed` augments the public group description `d : F.Desc` with a public
   bit-string seed `s : List Bool`, giving `F.withSeed.Desc = F.Desc × List Bool`. Under
   `PrimeOrderGroupFamily.seededSetup`, given the sampled group description `d ← setup n`, `s` is
   sampled uniformly from `{0, 1}^{seedLen n d}` conditional on `d` (and independently of the group
   exponents). When `seedLen` is polynomial-time computable in unary, `DDH.withSeed` transfers the
   `DDH` assumption from `(F, setup)` to `(F.withSeed, F.seededSetup setup seedLen)`.
2. `PrimeOrderGroupFamily.linearHashKDF` pads the encoded group element `w : List Bool` to the fixed
   self-delimiting width `2 * bound d + 1` via `Cslib.BitString.padWord (bound d) w` and hashes it
   with the public Boolean matrix seed `s` via `Cslib.BitString.LinearHash.wordHash (keyLen d) s`.
   Because `padWord` is injective on words of length at most `bound d`
   (`Cslib.BitString.word_eq_of_paddedBits_eq`) and `F.encode d` is injective on `F.Carrier d`, a
   uniform group element `γ • g` maps injectively into `BitString (2 * bound d + 1)` with collision
   probability `(F.order d)⁻¹`.
3. Applying the Leftover Hash Lemma for two-universal binary matrix hashing
   (`Cslib.BitString.LinearHash.isTwoUniversal_flat` and `IsTwoUniversal.leftover_hash`),
   `advantage_kdfGame_linearHashKDF_le` bounds the distinguishing advantage between `kdfRealGame`
   and `kdfIdealGame` for *every* (even computationally unbounded) distinguisher by
   `NNReal.sqrt ((2 : ℝ≥0) ^ (msgLen n) / (qMin : ℝ≥0)) / 2`. Consequently,
   `secureKDF_linearHashKDF`, `secureKDF_linearHashKDF_const`, `exists_secureKDF_withSeed`, and
   `DDH.negligible_hashedElGamalCPAGame_linearHashKDF` yield non-degenerate `SecureKDF` and Hashed
   ElGamal instantiations for arbitrary positive key lengths `msgLen n > 0` whenever
   `2 ^ (msgLen n) / q` is negligible.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.withSeed`: prime-order group family with a public hash seed in
  the description.
* `Cslib.Crypto.PrimeOrderGroupFamily.seededSetup`: setup distribution augmenting `setup n` with a
  bit-string seed sampled uniformly conditional on the sampled group description.
* `Cslib.Crypto.PrimeOrderGroupFamily.seededDDHDistinguisher`: DDH reduction that samples the public
  seed internally.
* `Cslib.Crypto.PrimeOrderGroupFamily.linearHashKDF`: polynomial-time key-derivation function built
  from `Cslib.BitString.padWord` and `Cslib.BitString.LinearHash.wordHash`.
* `Cslib.Crypto.PrimeOrderGroupFamily.linearHashSeedLen`: seed length
  `msgLen n * (2 * bound d + 1)` for `linearHashKDF`.
* `Cslib.Crypto.PrimeOrderGroupFamily.LinearHashKDFConditions`: the support, length, group-order
  and negligible-loss conditions under which `linearHashKDF` is a `SecureKDF`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.withSeed`: `DDH` is preserved under `seededSetup` when
  `seedLen` is polynomial-time computable in unary.
* `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_linearHashKDF`: `linearHashKDF` is
  computable in polynomial time when `keyLen` and `bound` are polynomial-time computable in unary.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_kdfGame_linearHashKDF_le`: unconditional Leftover
  Hash Lemma bound on `Game.advantage` between `kdfRealGame` and `kdfIdealGame`
  ([BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, p. 449).
* `Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_linearHashKDF`,
  `Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_linearHashKDF_const`,
  `Cslib.Crypto.PrimeOrderGroupFamily.exists_secureKDF_withSeed`,
  `Cslib.Crypto.PrimeOrderGroupFamily.DDH.negligible_hashedElGamalCPAGame_linearHashKDF`:
  non-degenerate `SecureKDF` and Hashed ElGamal IND-CPA instantiations via `linearHashKDF`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 8.10.4 (Theorem 8.11, p. 334) and Section 11.5.2
  (Attack Game 11.3, Definition 11.5, and Theorem 11.5, pp. 448–451).
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Probability.PMF Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

variable (F : PrimeOrderGroupFamily)

/-! ### Prime-order group family with a public seed in the description -/

/-- Seeded group descriptor `(d, s)` pairing a group descriptor `d : F.Desc` with a hash seed
`s : List Bool`. -/
abbrev SeededDesc (F : PrimeOrderGroupFamily) := F.Desc × List Bool

/-- Underlying group descriptor `d` of a seeded descriptor `(d, s)`. -/
abbrev SeededDesc.desc {F : PrimeOrderGroupFamily} (ds : F.SeededDesc) : F.Desc :=
  ds.1

/-- Hash seed `s` of a seeded descriptor `(d, s)`. -/
abbrev SeededDesc.seed {F : PrimeOrderGroupFamily} (ds : F.SeededDesc) : List Bool :=
  ds.2

/-- Augment a `PrimeOrderGroupFamily` with a public bit-string seed in the group description
(`Desc := F.Desc × List Bool`), as in [BonehShoup2023], Section 8.10.4 (p. 334), where the
universal-hash key is part of the public system parameter. All group operations act on the
underlying group description `d.1 : F.Desc`. -/
abbrev withSeed : PrimeOrderGroupFamily where
  Desc := F.Desc × List Bool
  encDesc := encPair F.encDesc encBits
  order d := F.order d.1
  prime_order d := F.prime_order d.1
  Carrier d := F.Carrier d.1
  addCommGroup d := F.addCommGroup d.1
  module d := F.module d.1
  generator d := F.generator d.1
  card_carrier d := F.card_carrier d.1
  generator_ne_zero d := F.generator_ne_zero d.1
  encode d := F.encode d.1
  encode_injective d := F.encode_injective d.1
  add input := F.add (SeededDesc.desc input.1, input.2)
  add_encode d x y := F.add_encode d.1 x y
  smul input := F.smul (SeededDesc.desc input.1, input.2)
  smul_encode d a x := F.smul_encode d.1 a x
  computableInPolyTime_order :=
    F.computableInPolyTime_order.comp (by fun_prop)
  computableInPolyTime_generator :=
    F.computableInPolyTime_generator.comp (by fun_prop)
  computableInPolyTime_add :=
    F.computableInPolyTime_add.comp
      (((ComputableInPolyTime.fst F.encDesc encBits).comp
        (ComputableInPolyTime.fst (encPair F.encDesc encBits)
          (encPair encBits encBits))).prod
        (by fun_prop))
  computableInPolyTime_smul :=
    F.computableInPolyTime_smul.comp
      (((ComputableInPolyTime.fst F.encDesc encBits).comp
        (ComputableInPolyTime.fst (encPair F.encDesc encBits)
          (encPair encNat encBits))).prod
        (by fun_prop))

/-- Setup distribution for `F.withSeed`: draw `d ← setup n`, then sample a uniform seed
`s ← Cslib.BitString.uniformList (seedLen n d)` conditional on `d`, and return `(d, s)`. -/
noncomputable def seededSetup (setup : ℕ → PMF F.Desc) (seedLen : ℕ → F.Desc → ℕ)
    (n : ℕ) : PMF F.withSeed.Desc := do
  let d ← setup n
  let s ← Cslib.BitString.uniformList (seedLen n d)
  return (d, s)

/-- Given a DDH distinguisher for `F.withSeed`, construct a DDH distinguisher for `F` by sampling
a fresh uniform seed `s ← Cslib.BitString.sampleList (seedLen n d)` and running `distinguisher` on
the seeded group parameters `(d, s)`. -/
noncomputable def seededDDHDistinguisher (seedLen : ℕ → F.Desc → ℕ)
    (distinguisher : F.withSeed.DDHDistinguisher) : F.DDHDistinguisher :=
  fun n d u v w => do
    let s ← Cslib.BitString.sampleList (seedLen n d)
    distinguisher n (d, s) u v w

/-- In `ddhRealGame`, `seededDDHDistinguisher` simulates `F.withSeed.ddhRealGame` under
`seededSetup`. -/
@[simp] theorem ddhRealGame_seededDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (distinguisher : F.withSeed.DDHDistinguisher) (n : ℕ) :
    F.ddhRealGame setup (F.seededDDHDistinguisher seedLen distinguisher) n =
      F.withSeed.ddhRealGame (F.seededSetup setup seedLen) distinguisher n := by
  simp only [pmf_norm, ddhRealGame, eval_ddhRealExperiment, seededDDHDistinguisher, seededSetup,
    withSeed, Cslib.BitString.eval_sampleList]
  pmf_swap

/-- In `ddhRandomGame`, `seededDDHDistinguisher` simulates `F.withSeed.ddhRandomGame` under
`seededSetup`. -/
@[simp] theorem ddhRandomGame_seededDDHDistinguisher (setup : ℕ → PMF F.Desc)
    (seedLen : ℕ → F.Desc → ℕ) (distinguisher : F.withSeed.DDHDistinguisher) (n : ℕ) :
    F.ddhRandomGame setup (F.seededDDHDistinguisher seedLen distinguisher) n =
      F.withSeed.ddhRandomGame (F.seededSetup setup seedLen) distinguisher n := by
  simp only [pmf_norm, ddhRandomGame, eval_ddhRandomExperiment, seededDDHDistinguisher,
    seededSetup, withSeed, Cslib.BitString.eval_sampleList]
  pmf_swap

/-- `seededDDHDistinguisher` is uniform strict PPT whenever `seedLen` is polynomial-time computable
in unary and `distinguisher` is uniform strict PPT. -/
theorem isPPT_seededDDHDistinguisher {seedLen : ℕ → F.Desc → ℕ}
    (hseed : ComputableInPolyTime (fun p : ℕ × F.Desc => seedLen p.1 p.2)
      (encPair encUnary F.encDesc) encUnary)
    {distinguisher : F.withSeed.DDHDistinguisher} (hD : distinguisher.IsPPT) :
    (F.seededDDHDistinguisher seedLen distinguisher).IsPPT := by
  have hsample : IsPPTOn F.encDDHInput encBits fun x : F.DDHInput =>
      Cslib.BitString.sampleList (seedLen x.secParam x.groupParameters) :=
    ComputableInPolyTime.sampleList (hseed.comp (show ComputableInPolyTime
      (fun x : F.DDHInput => (x.secParam, x.groupParameters)) F.encDDHInput
      (encPair encUnary F.encDesc) by fun_prop))
  have hprepare : ComputableInPolyTime
      (fun p : F.DDHInput × List Bool =>
        (⟨⟨p.1.secParam, (p.1.groupParameters, p.2), p.1.leftPublic, p.1.rightPublic⟩,
          p.1.candidateShared⟩ : F.withSeed.DDHInput))
      (encPair F.encDDHInput encBits) F.withSeed.encDDHInput :=
    ComputableInPolyTime.of_enc_eq
      (f := fun p : F.DDHInput × List Bool => (p.1.secParam, (p.1.groupParameters, p.2),
        F.encode _ p.1.leftPublic, F.encode _ p.1.rightPublic, F.encode _ p.1.candidateShared))
      (by fun_prop) fun _ => rfl
  simp only [DDHDistinguisher.IsPPT, seededDDHDistinguisher]
  exact hsample.bind_with (hD.preprocess hprepare)

/-- **Preservation of `DDH` under public-seed augmentation**: if `F.DDH setup` holds and
`seedLen` is polynomial-time computable in unary, then `F.withSeed.DDH (F.seededSetup setup
seedLen)` holds. -/
theorem DDH.withSeed {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    {seedLen : ℕ → F.Desc → ℕ} (hDDH : F.DDH setup)
    (hseed : ComputableInPolyTime (fun p : ℕ × F.Desc => seedLen p.1 p.2)
      (encPair encUnary F.encDesc) encUnary) :
    F.withSeed.DDH (F.seededSetup setup seedLen) := by
  intro distinguisher hD
  simpa only [F.ddhRealGame_seededDDHDistinguisher, F.ddhRandomGame_seededDDHDistinguisher] using
    hDDH (F.seededDDHDistinguisher seedLen distinguisher)
      (F.isPPT_seededDDHDistinguisher hseed hD)

/-! ### Binary Linear-Hash Key Derivation and Leftover Hash Lemma -/

/-- Binary linear-hash key derivation function ([BonehShoup2023], Section 8.10.4, Theorem 8.11,
p. 334, and Section 11.5.2, p. 449): given a seeded group description `(d, s) : F.withSeed.Desc`
and an encoded group element `w : List Bool`, pad `w` to the self-delimiting width
`2 * bound d + 1` via `Cslib.BitString.padWord (bound d) w` and hash with the public seed `s`
via `Cslib.BitString.LinearHash.wordHash (keyLen d) s`. -/
def linearHashKDF (keyLen bound : F.Desc → ℕ)
    (input : F.withSeed.Desc × List Bool) : List Bool :=
  Cslib.BitString.LinearHash.wordHash (keyLen (SeededDesc.desc input.1))
    (SeededDesc.seed input.1)
    (Cslib.BitString.padWord (bound (SeededDesc.desc input.1)) input.2)

/-- `linearHashKDF` always has the key length of its underlying group description. -/
@[simp] theorem length_linearHashKDF (keyLen bound : F.Desc → ℕ)
    (input : F.withSeed.Desc × List Bool) :
    (F.linearHashKDF keyLen bound input).length = keyLen (SeededDesc.desc input.1) := by
  simp [linearHashKDF]

/-- `linearHashKDF` is computable in polynomial time whenever `keyLen` and `bound` are computable
in polynomial time in unary from the group description `d : F.Desc`. -/
theorem computableInPolyTime_linearHashKDF {keyLen bound : F.Desc → ℕ}
    (hkey : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary) :
    ComputableInPolyTime (F.linearHashKDF keyLen bound)
      (encPair F.withSeed.encDesc encBits) encBits := by
  let EIn := encPair (encPair F.encDesc encBits) encBits
  have hd : ComputableInPolyTime
      (fun input : (F.Desc × List Bool) × List Bool => input.1.1) EIn F.encDesc := by fun_prop
  have hkeyIn : ComputableInPolyTime
      (fun input : (F.Desc × List Bool) × List Bool => keyLen input.1.1) EIn encUnary :=
    hkey.comp hd
  have hboundIn : ComputableInPolyTime
      (fun input : (F.Desc × List Bool) × List Bool => bound input.1.1) EIn encUnary :=
    hbound.comp hd
  change ComputableInPolyTime
    (fun input : (F.Desc × List Bool) × List Bool =>
      Cslib.BitString.LinearHash.wordHash (keyLen input.1.1) input.1.2
        (Cslib.BitString.padWord (bound input.1.1) input.2))
    EIn encBits
  fun_prop

/-- The matrix seed length required by `linearHashKDF` for output length `msgLen n` and encoding
length bound `bound d`: `msgLen n * (2 * bound d + 1)` bits. -/
def linearHashSeedLen (msgLen : ℕ → ℕ) (bound : F.Desc → ℕ) (n : ℕ) (d : F.Desc) : ℕ :=
  msgLen n * (2 * bound d + 1)

/-- `linearHashSeedLen` is computable in polynomial time in unary whenever `msgLen` and `bound`
are computable in polynomial time in unary. -/
theorem computableInPolyTime_linearHashSeedLen {msgLen : ℕ → ℕ} {bound : F.Desc → ℕ}
    (hmsg : ComputableInPolyTime msgLen encUnary encUnary)
    (hbound : ComputableInPolyTime bound F.encDesc encUnary) :
    ComputableInPolyTime (fun p : ℕ × F.Desc => F.linearHashSeedLen msgLen bound p.1 p.2)
      (encPair encUnary F.encDesc) encUnary := by
  have hmsgIn : ComputableInPolyTime (fun p : ℕ × F.Desc => msgLen p.1)
      (encPair encUnary F.encDesc) encUnary := hmsg.comp (by fun_prop)
  have hboundIn : ComputableInPolyTime (fun p : ℕ × F.Desc => bound p.2)
      (encPair encUnary F.encDesc) encUnary := hbound.comp (by fun_prop)
  unfold linearHashSeedLen
  fun_prop

/-- Self-delimiting padded bit-string encoding of `γ • g` in `BitString (2 * bound d + 1)`. -/
def paddedGeneratorMultiple (bound : F.Desc → ℕ) (d : F.Desc)
    (γ : ZMod (F.order d)) : BitString (2 * bound d + 1) :=
  Cslib.BitString.ofList (2 * bound d + 1)
    (Cslib.BitString.padWord (bound d) (F.encode d (γ • F.generator d)))

/-- When every encoded group element in `F.Carrier d` has bit-length at most `bound d`,
`List.ofFn (F.paddedGeneratorMultiple bound d γ)` recovers the padded word
`Cslib.BitString.padWord (bound d) (F.encode d (γ • F.generator d))`. -/
theorem ofFn_paddedGeneratorMultiple {bound : F.Desc → ℕ} {d : F.Desc}
    (hbound : ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (γ : ZMod (F.order d)) :
    List.ofFn (F.paddedGeneratorMultiple bound d γ) =
      Cslib.BitString.padWord (bound d) (F.encode d (γ • F.generator d)) :=
  Cslib.BitString.ofFn_ofList
    (Cslib.BitString.length_padWord (hbound (γ • F.generator d)))

/-- When every encoded group element in `F.Carrier d` has bit-length at most `bound d`,
`paddedGeneratorMultiple bound d` is injective on `ZMod (F.order d)`. -/
theorem paddedGeneratorMultiple_injective {bound : F.Desc → ℕ} {d : F.Desc}
    (hbound : ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d) :
    Function.Injective (F.paddedGeneratorMultiple bound d) := by
  intro γ₁ γ₂ h
  unfold paddedGeneratorMultiple at h
  have hpad : F.encode d (γ₁ • F.generator d) = F.encode d (γ₂ • F.generator d) :=
    Cslib.BitString.word_eq_of_paddedBits_eq
      (hbound (γ₁ • F.generator d)) (hbound (γ₂ • F.generator d)) h
  exact F.smul_generator_injective d (F.encode_injective d hpad)

/-- **Unconditional Leftover Hash Lemma bound for `linearHashKDF`** ([BonehShoup2023],
Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, p. 449): for every (even computationally
unbounded) distinguisher, when every `d ∈ (setup n).support` satisfies `keyLen d = msgLen n`,
`∀ x, (F.encode d x).length ≤ bound d`, and `qMin ≤ F.order d` with `0 < qMin`, the distinguishing
advantage between `kdfRealGame` and `kdfIdealGame` under `F.seededSetup` and `F.linearHashKDF` is at
most `NNReal.sqrt ((2 : ℝ≥0) ^ (msgLen n) / (qMin : ℝ≥0)) / 2`. -/
theorem advantage_kdfGame_linearHashKDF_le (setup : ℕ → PMF F.Desc)
    (keyLen bound : F.Desc → ℕ) (msgLen : ℕ → ℕ)
    (distinguisher : F.withSeed.KDFDistinguisher) (n qMin : ℕ) (hq0 : 0 < qMin)
    (hkey : ∀ d ∈ (setup n).support, keyLen d = msgLen n)
    (hbound : ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq : ∀ d ∈ (setup n).support, qMin ≤ F.order d) :
    Game.advantage
      (F.withSeed.kdfRealGame (F.seededSetup setup (F.linearHashSeedLen msgLen bound))
        (F.linearHashKDF keyLen bound) distinguisher n)
      (F.withSeed.kdfIdealGame (F.seededSetup setup (F.linearHashSeedLen msgLen bound))
        msgLen distinguisher n) ≤
      NNReal.sqrt ((2 : ℝ≥0) ^ (msgLen n) / (qMin : ℝ≥0)) / 2 := by
  simp only [pmf_norm, kdfRealGame, kdfIdealGame, seededSetup, withSeed]
  refine Game.advantage_bind_le_of_support (setup n) _ _ fun d hd => ?_
  change Game.advantage
    ((Cslib.BitString.uniformList (F.linearHashSeedLen msgLen bound n d)).bind fun a =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
            ProbComp.eval (distinguisher n
              (d, a) (α • F.generator d) (β • F.generator d)
                (F.linearHashKDF keyLen bound ((d, a), F.encode d (γ • F.generator d)))))
    ((Cslib.BitString.uniformList (F.linearHashSeedLen msgLen bound n d)).bind fun a =>
      (PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (Cslib.BitString.uniformList (msgLen n)).bind fun pad =>
            ProbComp.eval (distinguisher n (d, a) (α • F.generator d) (β • F.generator d) pad)) ≤
    _
  rw [Game.advantage_bind_comm]
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun α => ?_
  rw [Game.advantage_bind_comm]
  refine Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _ fun β => ?_
  let m := msgLen n
  let W := 2 * bound d + 1
  let source : PMF (BitString W) :=
    (PMF.uniformOfFintype (ZMod (F.order d))).map (F.paddedGeneratorMultiple bound d)
  let test : BitString (m * W) × BitString m → Game := fun pair =>
    ProbComp.eval (distinguisher n
      (d, List.ofFn pair.1) (α • F.generator d) (β • F.generator d)
        (List.ofFn pair.2))
  have hreal :
      (Cslib.BitString.uniformList (F.linearHashSeedLen msgLen bound n d)).bind (fun s =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ =>
          ProbComp.eval (distinguisher n
            (d, s) (α • F.generator d) (β • F.generator d)
              (F.linearHashKDF keyLen bound ((d, s), F.encode d (γ • F.generator d))))) =
      (seededHash (PMF.uniformOfFintype (BitString (m * W))) source
        (fun seed =>
          Cslib.BitString.LinearHash.hash
            (Cslib.BitString.blocksEquiv (m := m) (k := W) seed))).bind test := by
    simp only [pmf_norm, linearHashSeedLen, Cslib.BitString.uniformList, seededHash_eq_bind, source,
      test]
    conv_rhs => rw [PMF.bind_comm]
    congr 1 with seed : 1
    congr 1 with γ : 1
    have hpad := F.ofFn_paddedGeneratorMultiple (hbound d hd) γ
    have hhash :
        F.linearHashKDF keyLen bound ((d, List.ofFn seed), F.encode d (γ • F.generator d)) =
          List.ofFn (Cslib.BitString.LinearHash.hash
            (Cslib.BitString.blocksEquiv (m := m) (k := W) seed)
            (F.paddedGeneratorMultiple bound d γ)) := by
      simp only [linearHashKDF, SeededDesc.seed, hkey d hd, ← hpad,
        Cslib.BitString.LinearHash.wordHash_eq_ofFn,
        Cslib.BitString.ofList_ofFn, Cslib.BitString.blocksEquiv_apply]
    rw [hhash]
  have hideal :
      (Cslib.BitString.uniformList (F.linearHashSeedLen msgLen bound n d)).bind (fun s =>
        (Cslib.BitString.uniformList m).bind fun pad =>
          ProbComp.eval (distinguisher n
            (d, s) (α • F.generator d) (β • F.generator d) pad)) =
      ((PMF.uniformOfFintype (BitString (m * W))).bind fun seed =>
        (PMF.uniformOfFintype (BitString m)).map (seed, ·)).bind test := by
    simp only [pmf_norm, linearHashSeedLen, Cslib.BitString.uniformList, test]
    rfl
  rw [hreal, hideal, Game.advantage_eq_nndist, ← NNReal.coe_le_coe, coe_nndist]
  have hlhl := (Cslib.BitString.LinearHash.isTwoUniversal_flat W m).leftover_hash source
  have hcoll : collisionProbability source = (F.order d : ℝ)⁻¹ := by
    simp only [source,
      collisionProbability_map_of_injective _ _ (F.paddedGeneratorMultiple_injective (hbound d hd)),
      collisionProbability_uniform, ZMod.card]
  have hcard : (Fintype.card (BitString m) : ℝ) = (2 : ℝ) ^ m := by
    simp [BitString]
  have hord_le : (F.order d : ℝ)⁻¹ ≤ (qMin : ℝ)⁻¹ :=
    inv_anti₀ (by exact_mod_cast hq0) (by exact_mod_cast hq d hd)
  calc dist
        ((seededHash (PMF.uniformOfFintype (BitString (m * W))) source
          (fun seed =>
            Cslib.BitString.LinearHash.hash
              (Cslib.BitString.blocksEquiv (m := m) (k := W) seed))).bind test)
        (((PMF.uniformOfFintype (BitString (m * W))).bind fun seed =>
          (PMF.uniformOfFintype (BitString m)).map (seed, ·)).bind test)
      ≤ dist
          (seededHash (PMF.uniformOfFintype (BitString (m * W))) source
            (fun seed =>
              Cslib.BitString.LinearHash.hash
                (Cslib.BitString.blocksEquiv (m := m) (k := W) seed)))
          ((PMF.uniformOfFintype (BitString (m * W))).bind fun seed =>
            (PMF.uniformOfFintype (BitString m)).map (seed, ·)) :=
        dist_bind_le _ _ _
    _ ≤ Real.sqrt (Fintype.card (BitString m) * collisionProbability source) / 2 := hlhl
    _ = Real.sqrt ((2 : ℝ) ^ m * (F.order d : ℝ)⁻¹) / 2 := by rw [hcard, hcoll]
    _ ≤ Real.sqrt ((2 : ℝ) ^ m * (qMin : ℝ)⁻¹) / 2 := by
        gcongr
    _ = ↑(NNReal.sqrt ((2 : ℝ≥0) ^ m / (qMin : ℝ≥0)) / 2) := by
        push_cast
        rw [← div_eq_mul_inv]

/-- Statistical conditions under which `linearHashKDF keyLen bound` is a `SecureKDF` with output
length `msgLen` over `setup` ([BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334): on every
supported description `d` of `setup n`, the derived key has length `msgLen n`, `bound d` bounds the
encoded group elements, and the group order is at least `qMin n > 0`, while the Leftover Hash Lemma
loss `2 ^ (msgLen n) / qMin n` is negligible. -/
structure LinearHashKDFConditions (setup : ℕ → PMF F.Desc) (keyLen bound : F.Desc → ℕ)
    (msgLen qMin : ℕ → ℕ) : Prop where
  /-- The group-order lower bound is positive. -/
  qMin_pos : ∀ n, 0 < qMin n
  /-- Supported descriptions derive keys of length `msgLen n`. -/
  keyLen_eq : ∀ n, ∀ d ∈ (setup n).support, keyLen d = msgLen n
  /-- `bound d` bounds the encoded length of every group element of a supported description. -/
  length_encode_le : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d,
    (F.encode d x).length ≤ bound d
  /-- Supported descriptions have group order at least `qMin n`. -/
  qMin_le_order : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d
  /-- The Leftover Hash Lemma loss `2 ^ (msgLen n) / qMin n` is negligible. -/
  negligible : Negligible fun n => (2 : ℝ≥0) ^ (msgLen n) / (qMin n : ℝ≥0)

/-- **Unconditional `SecureKDF` instantiation via `linearHashKDF`** ([BonehShoup2023],
Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, Definition 11.5, p. 449): under
`LinearHashKDFConditions`, `linearHashKDF keyLen bound` satisfies `SecureKDF` over `F.withSeed` and
`F.seededSetup setup (F.linearHashSeedLen msgLen bound)`. -/
theorem secureKDF_linearHashKDF {setup : ℕ → PMF F.Desc} {keyLen bound : F.Desc → ℕ}
    {msgLen qMin : ℕ → ℕ} (h : F.LinearHashKDFConditions setup keyLen bound msgLen qMin) :
    F.withSeed.SecureKDF (F.seededSetup setup (F.linearHashSeedLen msgLen bound))
      (F.linearHashKDF keyLen bound) msgLen := by
  intro distinguisher _
  have hsqrt : Negligible fun n => NNReal.sqrt ((2 : ℝ≥0) ^ (msgLen n) / (qMin n : ℝ≥0)) / 2 := by
    have h1 : Negligible fun n =>
        (2⁻¹ : ℝ≥0) * NNReal.sqrt ((2 : ℝ≥0) ^ (msgLen n) / (qMin n : ℝ≥0)) :=
      (Negligible.sqrt h.negligible).const_mul (2⁻¹ : ℝ≥0)
    simpa only [div_eq_inv_mul] using h1
  exact negligible_of_le hsqrt fun n =>
    F.advantage_kdfGame_linearHashKDF_le setup keyLen bound msgLen distinguisher n (qMin n)
      (h.qMin_pos n) (h.keyLen_eq n) (h.length_encode_le n) (h.qMin_le_order n)

/-- **Unconditional `SecureKDF` instantiation for any constant key length `k : ℕ`** (including all
non-degenerate `k > 0`, e.g., `k = 128` as in [BonehShoup2023], Section 8.10.4, p. 334): when
`1 / qMin n` is negligible, `linearHashKDF (fun _ => k) bound` is a `SecureKDF` with output length
`fun _ => k`. -/
theorem secureKDF_linearHashKDF_const (setup : ℕ → PMF F.Desc)
    (bound : F.Desc → ℕ) (k : ℕ) {qMin : ℕ → ℕ}
    (hq0 : ∀ n, 0 < qMin n)
    (hbound : ∀ n, ∀ d ∈ (setup n).support, ∀ x : F.Carrier d, (F.encode d x).length ≤ bound d)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (1 / qMin n : ℝ≥0)) :
    F.withSeed.SecureKDF (F.seededSetup setup (F.linearHashSeedLen (fun _ => k) bound))
      (F.linearHashKDF (fun _ => k) bound) (fun _ => k) := by
  refine F.secureKDF_linearHashKDF ⟨hq0, fun _ _ _ => rfl, hbound, hq, ?_⟩
  have hk : Negligible fun n => (2 : ℝ≥0) ^ k * (1 / qMin n : ℝ≥0) :=
    hneg.const_mul ((2 : ℝ≥0) ^ k)
  simpa only [div_eq_mul_inv, one_mul] using hk

/-- **Existence of a polynomial-time non-degenerate `SecureKDF` for any `PrimeOrderGroupFamily`**
with super-polynomial group order: using the canonical polynomial encoding-length bound from
`F.exists_length_encode_le`, for every key length `k : ℕ` (in particular any `k > 0`) there exist a
unary polynomial-time seed-length function `seedLen` and a polynomial-time hash function
`H : F.withSeed.Desc × List Bool → List Bool` such that `F.withSeed.SecureKDF
(F.seededSetup setup seedLen) H (fun _ => k)` holds whenever `1 / qMin n` is negligible. -/
theorem exists_secureKDF_withSeed (setup : ℕ → PMF F.Desc) (k : ℕ) {qMin : ℕ → ℕ}
    (hq0 : ∀ n, 0 < qMin n)
    (hq : ∀ n, ∀ d ∈ (setup n).support, qMin n ≤ F.order d)
    (hneg : Negligible fun n => (1 / qMin n : ℝ≥0)) :
    ∃ (seedLen : ℕ → F.Desc → ℕ) (H : F.withSeed.Desc × List Bool → List Bool),
      ComputableInPolyTime (fun p : ℕ × F.Desc => seedLen p.1 p.2)
        (encPair encUnary F.encDesc) encUnary ∧
      ComputableInPolyTime H (encPair F.withSeed.encDesc encBits) encBits ∧
      (∀ ds w, (H (ds, w)).length = k) ∧
      F.withSeed.SecureKDF (F.seededSetup setup seedLen) H (fun _ => k) := by
  obtain ⟨c, e, hce⟩ := F.exists_length_encode_le
  let bound : F.Desc → ℕ := fun d => c * ((F.encDesc d).length + 1) ^ e
  have hbound_poly : ComputableInPolyTime bound F.encDesc encUnary := by
    dsimp [bound]
    fun_prop
  have hkey_poly : ComputableInPolyTime (fun _ : F.Desc => k) F.encDesc encUnary := by fun_prop
  have hmsg_poly : ComputableInPolyTime (fun _ : ℕ => k) encUnary encUnary := by fun_prop
  refine ⟨F.linearHashSeedLen (fun _ => k) bound, F.linearHashKDF (fun _ => k) bound,
    F.computableInPolyTime_linearHashSeedLen hmsg_poly hbound_poly,
    F.computableInPolyTime_linearHashKDF hkey_poly hbound_poly,
    fun ds w => F.length_linearHashKDF (fun _ => k) bound (ds, w),
    F.secureKDF_linearHashKDF_const setup bound k hq0 (fun _ d _ x => hce d x) hq hneg⟩

/-- **Hashed ElGamal with `linearHashKDF` is IND-CPA secure under `F.DDH setup` alone**
([BonehShoup2023], Section 8.10.4, Theorem 8.11, p. 334, and Section 11.5.2, Theorem 11.5,
pp. 449–451): combining `DDH.withSeed`, `secureKDF_linearHashKDF`, and
`DDH.negligible_hashedElGamalCPAGame`, no computational hypothesis on the key-derivation hash is
needed under `LinearHashKDFConditions`. -/
theorem DDH.negligible_hashedElGamalCPAGame_linearHashKDF {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc} {keyLen bound : F.Desc → ℕ} {msgLen qMin : ℕ → ℕ}
    (hDDH : F.DDH setup) (hKDF : F.LinearHashKDFConditions setup keyLen bound msgLen qMin)
    (hkey_poly : ComputableInPolyTime keyLen F.encDesc encUnary)
    (hbound_poly : ComputableInPolyTime bound F.encDesc encUnary)
    (hmsg_poly : ComputableInPolyTime msgLen encUnary encUnary)
    {adversary : Encryption.WordAdversary} (hA : adversary.IsPPT) :
    Negligible fun n =>
      Game.advantage
        (F.withSeed.hashedElGamalCPAGame
          (F.seededSetup setup (F.linearHashSeedLen msgLen bound))
          (F.linearHashKDF keyLen bound) adversary false n)
        (F.withSeed.hashedElGamalCPAGame
          (F.seededSetup setup (F.linearHashSeedLen msgLen bound))
          (F.linearHashKDF keyLen bound) adversary true n) :=
  (hDDH.withSeed (F.computableInPolyTime_linearHashSeedLen hmsg_poly hbound_poly))
    |>.negligible_hashedElGamalCPAGame (F.secureKDF_linearHashKDF hKDF)
      (F.computableInPolyTime_linearHashKDF hkey_poly hbound_poly) hA

end Cslib.Crypto.PrimeOrderGroupFamily
