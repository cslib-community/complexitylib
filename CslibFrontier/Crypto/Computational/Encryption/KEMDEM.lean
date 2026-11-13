/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Computational.Encryption.KEM
public import CslibFrontier.Crypto.Computational.Encryption.Scheme
import CslibFrontier.Tactic.PMFSwap

/-!
# KEM–DEM hybrid encryption

A key encapsulation mechanism `E : KEM PK SK CT K` and a symmetric cipher `D : Cipher K M C` on
its keys combine into the public-key encryption scheme `E.hybrid D : PKE PK SK M (CT × C)`
([BonehShoup2023], Exercise 11.9(a)): encryption encapsulates a key and encrypts the message under
it with `D`, and decryption decapsulates the key and decrypts. `KEM.hybrid_correct` states that
the hybrid is correct when both components are.

Chosen-plaintext security of the hybrid reduces to security of the KEM and one-time security of
the cipher (Exercise 11.9(b)). Fix a sampler `sampleKey` for the random KEM key, which is also the
key distribution of the one-time cipher experiment. For every two-stage adversary `A` against the
hybrid and every admissibility predicate on message pairs:

* `KEM.advantage_hybrid_le`: the hybrid advantage is at most the KEM advantages of the two
  distinguishers `hybridDistinguisher D valid A b`, one for each challenge bit `b`, plus the
  one-time advantage of `hybridCipherAdversary E A`;
* `KEM.advantage_hybrid_le_two_mul`: it is at most twice the KEM advantage of the single
  distinguisher `hybridHiddenBitDistinguisher D valid A`, which draws the challenge bit itself,
  plus the same one-time advantage.

The distinguisher for bit `b` runs `A` on the challenge public key and answers its challenge by
encrypting the selected message under the challenge key. With the encapsulated key this is the
hybrid experiment (`eval_cpaExperiment_hybridDistinguisher_false`); with a random key it is the
one-time experiment of `hybridCipherAdversary E A`, which generates the KEM keys and the
encapsulation itself (`eval_cpaExperiment_hybridDistinguisher_true`).

## Main definitions

* `Cslib.Crypto.KEM.hybrid`: the KEM–DEM hybrid public-key encryption scheme.
* `Cslib.Crypto.KEM.hybridDistinguisher`, `Cslib.Crypto.KEM.hybridHiddenBitDistinguisher`: the
  KEM distinguishers of the reduction.
* `Cslib.Crypto.KEM.hybridCipherAdversary`: the one-time cipher adversary of the reduction.

## Main results

* `Cslib.Crypto.KEM.hybrid_correct`: the hybrid of a correct KEM and a correct cipher is correct.
* `Cslib.Crypto.KEM.advantage_hybrid_le`, `Cslib.Crypto.KEM.advantage_hybrid_le_two_mul`: the
  advantage bounds of [BonehShoup2023], Exercise 11.9(b).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.9 (pp. 460–461).
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

namespace KEM

variable {PK SK CT K M C : Type}

/-- KEM–DEM hybrid encryption ([BonehShoup2023], Exercise 11.9(a)). Key generation is that of the
KEM. Encryption encapsulates a key under the public key and encrypts the message under it with the
cipher; the ciphertext is the encapsulation together with the cipher's ciphertext. Decryption
decapsulates the key and decrypts; either step may reject. -/
def hybrid (E : KEM PK SK CT K) (D : Cipher K M C) : PKE PK SK M (CT × C) where
  keyGen := E.keyGen
  encrypt pk m := do
    let encapsulated ← E.encaps pk
    let c ← D.encrypt encapsulated.2 m
    return (encapsulated.1, c)
  decrypt sk ct := (E.decaps sk ct.1).bind fun k => D.decrypt k ct.2

/-- The hybrid of a correct KEM and a correct cipher is correct. -/
theorem hybrid_correct {E : KEM PK SK CT K} {D : Cipher K M C} (hE : E.Correct)
    (hD : D.Correct) : (E.hybrid D).Correct := by
  intro keys hkeys m ct hct
  simp only [hybrid, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hct
  obtain ⟨encapsulated, hencapsulated, c, hc, rfl⟩ := hct
  simp only [hybrid, hE keys hkeys encapsulated hencapsulated, Option.bind_some, hD _ _ c hc]

/-- The KEM distinguisher of the hybrid argument for challenge bit `b` ([BonehShoup2023],
Exercise 11.9(b)): run the left-or-right experiment of `A` on the challenge public key, answering
the challenge by encrypting the selected message under the challenge key and pairing the result
with the challenge ciphertext. -/
def hybridDistinguisher (D : Cipher K M C) (valid : M → M → Bool) {σ : Type}
    (A : TwoStage PK (MessagePair M) (CT × C) Bool σ) (b : Bool) (ch : Challenge PK CT K) :
    ProbComp Bool :=
  lrExperiment (fun _ => valid) (fun _ m => do
    let c ← D.encrypt ch.key m
    return (ch.ct, c)) A b ch.pk

/-- The single KEM distinguisher of the hybrid argument ([BonehShoup2023], Exercise 11.9(b)): draw
a fair challenge bit `b`, run `hybridDistinguisher D valid A b`, and output its guess XOR `b`. -/
noncomputable def hybridHiddenBitDistinguisher (D : Cipher K M C) (valid : M → M → Bool)
    {σ : Type} (A : TwoStage PK (MessagePair M) (CT × C) Bool σ) (ch : Challenge PK CT K) :
    ProbComp Bool := do
  let b ← ProbComp.uniform Bool
  let guess ← hybridDistinguisher D valid A b ch
  return guess ^^ b

/-- The one-time cipher adversary of the hybrid argument ([BonehShoup2023], Exercise 11.9(b)). Its
first stage generates a KEM key pair, runs the first stage of `A` on the public key, and
encapsulates under it, saving the encapsulation with the state of `A`; its second stage pairs the
encapsulation with the cipher's challenge and runs the second stage of `A`. -/
def hybridCipherAdversary (E : KEM PK SK CT K) {σ : Type}
    (A : TwoStage PK (MessagePair M) (CT × C) Bool σ) :
    TwoStage Unit (MessagePair M) C Bool (CT × σ) where
  choose _ := do
    let keys ← E.keyGen
    let choice ← A.choose keys.1
    let encapsulated ← E.encaps keys.1
    return (choice.1, (encapsulated.1, choice.2))
  guess state c := A.guess state.2 (state.1, c)

variable (E : KEM PK SK CT K) (sampleKey : ProbComp K) (D : Cipher K M C) (valid : M → M → Bool)
  {σ : Type} (A : TwoStage PK (MessagePair M) (CT × C) Bool σ)

/-- With the encapsulated key, `hybridDistinguisher D valid A b` runs the chosen-plaintext
experiment of the hybrid for bit `b`. -/
theorem eval_cpaExperiment_hybridDistinguisher_false (b : Bool) :
    ProbComp.eval (E.cpaExperiment sampleKey (hybridDistinguisher D valid A b) false) =
      ProbComp.eval ((E.hybrid D).cpaExperiment (fun _ => valid) A b) := by
  simp only [cpaExperiment, PKE.cpaExperiment, hybridDistinguisher, hybrid, Bool.false_eq_true,
    ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, eval_lrExperiment,
    PMF.bind_bind]
  congr 1 with keys : 1
  rw [PMF.bind_comm]
  congr 1 with choice : 1
  split <;> simp only [PMF.bind_const]

/-- With a random key, `hybridDistinguisher D valid A b` runs the one-time experiment of
`hybridCipherAdversary E A` for bit `b`. -/
theorem eval_cpaExperiment_hybridDistinguisher_true (b : Bool) :
    ProbComp.eval (E.cpaExperiment sampleKey (hybridDistinguisher D valid A b) true) =
      ProbComp.eval (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) b) := by
  simp only [cpaExperiment, Cipher.oneTimeExperiment, hybridDistinguisher,
    hybridCipherAdversary, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    eval_lrExperiment, PMF.bind_bind]
  pmf_swap

/-- `hybridHiddenBitDistinguisher D valid A` averages the experiments of
`hybridDistinguisher D valid A b` over a fair bit `b`, complementing the guess for `b = true`. -/
theorem eval_cpaExperiment_hybridHiddenBitDistinguisher (c : Bool) :
    ProbComp.eval (E.cpaExperiment sampleKey (hybridHiddenBitDistinguisher D valid A) c) =
      (PMF.uniformOfFintype Bool).bind fun b =>
        (ProbComp.eval (E.cpaExperiment sampleKey (hybridDistinguisher D valid A b) c)).map
          fun guess => guess ^^ b := by
  cases c <;>
    simp only [cpaExperiment, hybridHiddenBitDistinguisher, Bool.false_eq_true, ↓reduceIte,
      pure_bind, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, PMF.map_bind] <;>
    pmf_swap

/-- **Hybrid encryption from two per-bit KEM distinguishers** (two-distinguisher variant of
[BonehShoup2023], Exercise 11.9(b)): the chosen-plaintext advantage of the hybrid is at most the
KEM advantages of `hybridDistinguisher D valid A false` and `hybridDistinguisher D valid A true`
plus the one-time advantage of `hybridCipherAdversary E A`. -/
theorem advantage_hybrid_le :
    Experiment.advantage ((E.hybrid D).cpaExperiment (fun _ => valid) A false)
        ((E.hybrid D).cpaExperiment (fun _ => valid) A true) ≤
      Experiment.advantage (E.cpaExperiment sampleKey (hybridDistinguisher D valid A false) false)
          (E.cpaExperiment sampleKey (hybridDistinguisher D valid A false) true) +
        Experiment.advantage (E.cpaExperiment sampleKey (hybridDistinguisher D valid A true) false)
          (E.cpaExperiment sampleKey (hybridDistinguisher D valid A true) true) +
        Experiment.advantage
          (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) false)
          (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) true) := by
  simp only [Experiment.advantage, eval_cpaExperiment_hybridDistinguisher_false,
    eval_cpaExperiment_hybridDistinguisher_true]
  refine (Game.advantage_triangle _ (ProbComp.eval
    (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) false)) _).trans ?_
  refine (add_le_add le_rfl (Game.advantage_triangle _ (ProbComp.eval
    (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) true)) _)).trans_eq ?_
  rw [Game.advantage_comm (ProbComp.eval
    (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) true))]
  ac_rfl

/-- **Hybrid encryption from one KEM distinguisher** ([BonehShoup2023], Exercise 11.9(b)): the
chosen-plaintext advantage of the hybrid is at most twice the KEM advantage of
`hybridHiddenBitDistinguisher D valid A` plus the one-time advantage of
`hybridCipherAdversary E A`. -/
theorem advantage_hybrid_le_two_mul :
    Experiment.advantage ((E.hybrid D).cpaExperiment (fun _ => valid) A false)
        ((E.hybrid D).cpaExperiment (fun _ => valid) A true) ≤
      2 * Experiment.advantage
          (E.cpaExperiment sampleKey (hybridHiddenBitDistinguisher D valid A) false)
          (E.cpaExperiment sampleKey (hybridHiddenBitDistinguisher D valid A) true) +
        Experiment.advantage
          (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) false)
          (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) true) := by
  simp only [Experiment.advantage, eval_cpaExperiment_hybridHiddenBitDistinguisher,
    eval_cpaExperiment_hybridDistinguisher_false, eval_cpaExperiment_hybridDistinguisher_true]
  exact Game.advantage_le_two_mul_uniform_bool_xor
    (fun b => ProbComp.eval ((E.hybrid D).cpaExperiment (fun _ => valid) A b))
    (fun b => ProbComp.eval (D.oneTimeExperiment sampleKey valid (hybridCipherAdversary E A) b))

end KEM

end Cslib.Crypto
