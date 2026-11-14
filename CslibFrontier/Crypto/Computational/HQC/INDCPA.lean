/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game.HiddenBit
public import CslibFrontier.Crypto.Primitives.HQC.PKE

/-!
# IND-CPA security of the ideal HQC public-key encryption core

This module formalizes the two-hop game argument of [HQC2026], Theorem 6.3, printed
pp. 61--64, for the ideal expanded-value HQC-PKE core. The adversary is a
`Cslib.Crypto.TwoStage`: after receiving the public key it chooses both challenge messages and a
saved state, then guesses from that state and the challenge ciphertext. Thus the messages may
depend on the key, unlike the fixed-message `ExplicitCoinPKE.indCpaAdvantage` experiment.

The source defines the public parity `b₁` from the sampled public word. Accordingly the DQCSD
laws below mix both fixed-parity branches rather than silently fixing one. The first reduction
replaces the public syndrome using 2-DQCSD-P. The second reads the public key and masked
ciphertext as one 3-DQCSD-PT sample; this hop assumes `ωᵣ = ωₑ`, as in the source parameter
sets. A uniform comparison sample masks the selected encoded message, so the final game wins
with probability exactly one half.

The theorem is an exact finite probability bound. [HQC2026] gives no gate, query, or runtime
loss formula for the two reductions, so this module does not invent one or claim a native-QPPT
endpoint. In particular, applying the canonical native assumptions in
`Cslib.Crypto.HQC.NativeQuantumTwoDQCSDP` and
`Cslib.Crypto.HQC.NativeQuantumThreeDQCSDPT` still requires circuit/resource certificates for
these reductions and an explicit treatment of the fair parity mixtures. As in [HQC2026],
Definition 2.4.1 (printed p. 13), `indCpaAdvantage` is the absolute bias
`|Pr[win] - 1/2|`.

The displayed Game3 pseudocode on printed p. 63 repeats the fixed-weight Game2 sampling and
formula. This conflicts with the adjacent transition text, the definition of 3-DQCSD-PT and the
proof paragraph, which identify Game3 with the uniform comparison law and use that law to conclude
independence from the hidden bit. `threeUniformGame` follows that stated comparison-law transition,
not the inconsistent displayed body. Seed/XOF expansion, the biased production sampler, QROM,
Fujisaki--Okamoto, IND-CCA2, and HQC-KEM remain separate obligations.

## Main definitions

* `Cslib.Crypto.HQC.indCpaGame`: the source hidden-bit two-stage IND-CPA experiment.
* `Cslib.Crypto.HQC.twoDQCSDDistinguisher`: the source 2-DQCSD-P reduction.
* `Cslib.Crypto.HQC.threeDQCSDDistinguisher`: the source 3-DQCSD-PT reduction.
* `Cslib.Crypto.HQC.twoDQCSDAdvantage`, `Cslib.Crypto.HQC.threeDQCSDAdvantage`: the two exact
  finite source advantage terms.

## Main results

* `Cslib.Crypto.HQC.eval_indCpaGame_eq_twoRealGame`: Game1 is the real 2-DQCSD-P reduction game.
* `Cslib.Crypto.HQC.twoUniformGame_eq_threeRealGame`: Game2 is the real 3-DQCSD-PT reduction game.
* `Cslib.Crypto.HQC.threeUniformGame_eq_uniform`: Game3 is a fair hidden-bit game.
* `Cslib.Crypto.HQC.indCpaAdvantage_le`: [HQC2026], Theorem 6.3, Equation (10).

## References

* [HQC specification, version 5.1][HQC2026], Theorem 6.3, pp. 61--64.
-/

@[expose] public section

namespace Cslib.Crypto.HQC

open Matrix BitString Probability
open scoped NNReal

variable (P : PKEParams) [NeZero P.n]

/-! ### Exact parity-mixtures of the source DQCSD laws -/

private theorem bind_uniformParity_eq_uniform (n : ℕ) [NeZero n] :
    (PMF.uniformOfFintype Bool).bind (uniformParity n) =
      PMF.uniformOfFintype (BitString n) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  ext x
  cases h : parity (j + 1) x <;>
    simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_bool,
      Nat.cast_ofNat, tsum_fintype, Fintype.univ_bool, Finset.mem_singleton,
      Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true, Finset.sum_insert,
      Finset.sum_singleton, uniformParity_apply, h, ite_false, ite_true, Fintype.card_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_succ, mul_comm]
  all_goals
    simp only [Nat.succ_sub_one, Nat.cast_mul, zero_mul, add_zero, zero_add]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by finiteness))]
    rw [Nat.cast_pow]
    norm_num [mul_comm]

/-- The real 2-DQCSD-P public-key law, mixing the parity `b₁` read from the sampled public word. -/
noncomputable def mixedTwoRealLaw : PMF (SyndromeSample P.n) :=
  (PMF.uniformOfFintype Bool).bind fun b₁ =>
    realSyndromeLaw P.n P.omega P.omega_le_n b₁

/-- The comparison 2-DQCSD-P public-key law, with the same mixed public parity. -/
noncomputable def mixedTwoUniformLaw : PMF (SyndromeSample P.n) :=
  (PMF.uniformOfFintype Bool).bind fun b₁ =>
    uniformSyndromeLaw P.n P.omega b₁

/-- The real 3-DQCSD-PT law for the encryption hop. Its second public parity is the parity of the
comparison public syndrome from the first hop. -/
noncomputable def mixedThreeRealLaw : PMF (TruncatedSyndromeSample P.n P.codeLen) :=
  (PMF.uniformOfFintype Bool).bind fun b₁ =>
    realTruncatedSyndromeLaw P.n P.codeLen P.omegaR (Nat.sub_le _ _) P.omegaR_le_n
      b₁ (syndromeParity P.omega b₁)

/-- The comparison 3-DQCSD-PT law for the encryption hop. -/
noncomputable def mixedThreeUniformLaw : PMF (TruncatedSyndromeSample P.n P.codeLen) :=
  (PMF.uniformOfFintype Bool).bind fun b₁ =>
    uniformTruncatedSyndromeLaw P.n P.codeLen P.omegaR
      b₁ (syndromeParity P.omega b₁)

/-! ### Source games and reductions -/

/-- Read a two-block syndrome sample as an expanded HQC public key. -/
def SyndromeSample.toPKEPublicKey (sample : SyndromeSample P.n) : PKEPublicKey P :=
  ⟨sample.publicBlock, sample.value⟩

/-- Read the two public blocks of a truncated three-block sample as an expanded HQC public key. -/
def TruncatedSyndromeSample.toPKEPublicKey
    (sample : TruncatedSyndromeSample P.n P.codeLen) : PKEPublicKey P :=
  ⟨sample.firstBlock, sample.secondBlock⟩

/-- Read the two output blocks of a truncated three-block sample as an HQC ciphertext, adding the
selected encoded message to the retained component as in the source reduction. -/
def TruncatedSyndromeSample.toPKECiphertext (encode : PKEMessage P → Codeword P)
    (message : PKEMessage P) (sample : TruncatedSyndromeSample P.n P.codeLen) :
    PKECiphertext P :=
  ⟨sample.firstValue, encode message + sample.secondValue⟩

/-- **HQC v5.1 Game1.** The ideal expanded-key two-stage IND-CPA experiment samples the hidden bit
after the key-dependent message pair and wins when the second-stage guess equals that bit. -/
noncomputable def indCpaGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : Experiment := do
  let (pk, _) ← pkeKeyGen P
  let (messages, state) ← adversary.choose pk
  let bit ← ProbComp.uniform Bool
  let coins ← pkeSampleCoins P
  let guess ← adversary.guess state (pkeEncrypt P encode pk (messages.select bit) coins)
  return guess == bit

/-- Absolute bias of the hidden-bit success probability from one half, matching [HQC2026],
Definition 2.4.1 (printed p. 13). -/
noncomputable def indCpaAdvantage {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : ℝ≥0 :=
  Game.guessingAdvantage (ProbComp.eval (indCpaGame P encode adversary))

/-- The 2-DQCSD-P distinguisher `B₁`: read the challenge as the public key, run the key-dependent
message stage, encrypt the selected message honestly, and report whether the guess was right. -/
noncomputable def twoDQCSDDistinguisher {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (sample : SyndromeSample P.n) : Game := do
  let pk := sample.toPKEPublicKey P
  let (messages, state) ← ProbComp.eval (adversary.choose pk)
  let bit ← PMF.uniformOfFintype Bool
  let coins ← ProbComp.eval (pkeSampleCoins P)
  let guess ← ProbComp.eval
    (adversary.guess state (pkeEncrypt P encode pk (messages.select bit) coins))
  return guess == bit

/-- Game1 as the real 2-DQCSD-P game for `twoDQCSDDistinguisher`. -/
noncomputable def twoRealGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : Game :=
  (mixedTwoRealLaw P).bind (twoDQCSDDistinguisher P encode adversary)

/-- Game2 as the comparison 2-DQCSD-P game for `twoDQCSDDistinguisher`. -/
noncomputable def twoUniformGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : Game :=
  (mixedTwoUniformLaw P).bind (twoDQCSDDistinguisher P encode adversary)

/-- The exact finite 2-DQCSD-P advantage term in Equation (10). -/
noncomputable def twoDQCSDAdvantage {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : ℝ≥0 :=
  Game.advantage (twoRealGame P encode adversary) (twoUniformGame P encode adversary)

/-- The 3-DQCSD-PT distinguisher `B₂`: read the first two blocks as the public key and the last
two as the ciphertext mask, then add the selected encoded message before the guessing stage. -/
noncomputable def threeDQCSDDistinguisher {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (sample : TruncatedSyndromeSample P.n P.codeLen) : Game := do
  let pk := sample.toPKEPublicKey P
  let (messages, state) ← ProbComp.eval (adversary.choose pk)
  let bit ← PMF.uniformOfFintype Bool
  let ciphertext := sample.toPKECiphertext P encode (messages.select bit)
  let guess ← ProbComp.eval (adversary.guess state ciphertext)
  return guess == bit

/-- Game2 as the real 3-DQCSD-PT game for `threeDQCSDDistinguisher`. -/
noncomputable def threeRealGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : Game :=
  (mixedThreeRealLaw P).bind (threeDQCSDDistinguisher P encode adversary)

/-- Game3 as the comparison 3-DQCSD-PT game for `threeDQCSDDistinguisher`. -/
noncomputable def threeUniformGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : Game :=
  (mixedThreeUniformLaw P).bind (threeDQCSDDistinguisher P encode adversary)

/-- The exact finite 3-DQCSD-PT advantage term in Equation (10). -/
noncomputable def threeDQCSDAdvantage {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) : ℝ≥0 :=
  Game.advantage (threeRealGame P encode adversary) (threeUniformGame P encode adversary)

/-! ### Exact game identities -/

omit [NeZero P.n] in
private theorem eval_pkeKeyGen_bind {Output : Type} (kernel :
    PKEPublicKey P × PKESecretKey P → PMF Output) :
    (ProbComp.eval (pkeKeyGen P)).bind kernel =
      (PMF.uniformOfFinset (weightLayer P.n P.omega)
        (weightLayer_nonempty P.omega_le_n)).bind fun y =>
      (PMF.uniformOfFinset (weightLayer P.n P.omega)
        (weightLayer_nonempty P.omega_le_n)).bind fun x =>
      (PMF.uniformOfFintype (RingWord P)).bind fun h =>
        kernel (expandedPublicKey P h x y, y) := by
  ext output
  simp only [PMF.bind_apply]
  change ProbComp.expect (pkeKeyGen P) (fun keys => kernel keys output) = _
  rw [pkeKeyGen_expect]
  simp only [ProbComp.expect]
  rw [eval_sampleFixedWeight P P.omega_le_n]
  simp only [ProbComp.eval_uniform]

omit [NeZero P.n] in
private theorem eval_pkeSampleCoins_bind {Output : Type} (kernel : PKECoins P → PMF Output) :
    (ProbComp.eval (pkeSampleCoins P)).bind kernel =
      (PMF.uniformOfFinset (weightLayer P.n P.omegaR)
        (weightLayer_nonempty P.omegaR_le_n)).bind fun r2 =>
      (PMF.uniformOfFinset (weightLayer P.n P.omegaE)
        (weightLayer_nonempty P.omegaE_le_n)).bind fun e =>
      (PMF.uniformOfFinset (weightLayer P.n P.omegaR)
        (weightLayer_nonempty P.omegaR_le_n)).bind fun r1 => kernel ⟨r2, e, r1⟩ := by
  ext output
  simp only [PMF.bind_apply]
  change ProbComp.expect (pkeSampleCoins P) (fun coins => kernel coins output) = _
  rw [pkeSampleCoins_expect]
  simp only [ProbComp.expect]
  rw [eval_sampleFixedWeight P P.omegaR_le_n,
    eval_sampleFixedWeight P P.omegaE_le_n]

private theorem bind_rotate {A B C Output : Type} (p : PMF A) (q : PMF B) (r : PMF C)
    (kernel : A → B → C → PMF Output) :
    p.bind (fun a => q.bind fun b => r.bind fun c => kernel a b c) =
      r.bind fun c => q.bind fun b => p.bind fun a => kernel a b c := by
  calc
    _ = p.bind (fun a => r.bind fun c => q.bind fun b => kernel a b c) := by
      apply congrArg (p.bind)
      funext a
      exact PMF.bind_comm q r (fun b c => kernel a b c)
    _ = r.bind (fun c => p.bind fun a => q.bind fun b => kernel a b c) :=
      PMF.bind_comm p r (fun a c => q.bind fun b => kernel a b c)
    _ = _ := by
      apply congrArg (r.bind)
      funext c
      exact PMF.bind_comm p q (fun a b => kernel a b c)

private theorem bind_last_first {A B C Output : Type} (p : PMF A) (q : PMF B) (r : PMF C)
    (kernel : A → B → C → PMF Output) :
    p.bind (fun a => q.bind fun b => r.bind fun c => kernel a b c) =
      r.bind fun c => p.bind fun a => q.bind fun b => kernel a b c := by
  calc
    _ = p.bind (fun a => r.bind fun c => q.bind fun b => kernel a b c) := by
      apply congrArg (p.bind)
      funext a
      exact PMF.bind_comm q r (fun b c => kernel a b c)
    _ = _ := PMF.bind_comm p r (fun a c => q.bind fun b => kernel a b c)

private def truncateEncryptionSample (sample : SyndromeSample P.n) (coins : PKECoins P) :
    TruncatedSyndromeSample P.n P.codeLen :=
  ⟨sample.publicBlock, sample.value, syndrome sample.publicBlock coins.r1 coins.r2,
    truncate P (syndrome sample.value coins.e coins.r2)⟩

private theorem mixedTwoUniform_bind_coins_eq_mixedThreeReal
    (hweight : P.omegaE = P.omegaR) :
    (mixedTwoUniformLaw P).bind (fun sample =>
      (ProbComp.eval (pkeSampleCoins P)).map (truncateEncryptionSample P sample)) =
      mixedThreeRealLaw P := by
  simp only [mixedTwoUniformLaw, uniformSyndromeLaw, mixedThreeRealLaw,
    realTruncatedSyndromeLaw, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind, PMF.map, eval_pkeSampleCoins_bind]
  have heLaw :
      PMF.uniformOfFinset (weightLayer P.n P.omegaE)
          (weightLayer_nonempty P.omegaE_le_n) =
        PMF.uniformOfFinset (weightLayer P.n P.omegaR)
          (weightLayer_nonempty P.omegaR_le_n) := by
    simp only [hweight]
  rw [heLaw]
  apply congrArg (PMF.uniformOfFintype Bool).bind
  funext b₁
  apply congrArg (uniformParity P.n b₁).bind
  funext h₁
  apply congrArg (uniformParity P.n (syndromeParity P.omega b₁)).bind
  funext h₂
  let sparse := PMF.uniformOfFinset (weightLayer P.n P.omegaR)
    (weightLayer_nonempty P.omegaR_le_n)
  simpa only [truncateEncryptionSample, Function.comp_apply, truncate] using
    bind_rotate sparse sparse sparse (fun r2 e r1 =>
      PMF.pure (truncateEncryptionSample P ⟨h₁, h₂⟩ ⟨r2, e, r1⟩))

/-- HQC v5.1 Game1 is exactly the real 2-DQCSD-P reduction game. -/
theorem eval_indCpaGame_eq_twoRealGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) :
    ProbComp.eval (indCpaGame P encode adversary) = twoRealGame P encode adversary := by
  simp only [indCpaGame, twoRealGame, mixedTwoRealLaw, realSyndromeLaw,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind]
  rw [eval_pkeKeyGen_bind]
  unfold twoDQCSDDistinguisher SyndromeSample.toPKEPublicKey
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, eval_pkeSampleCoins_bind]
  conv_rhs =>
    rw [← PMF.bind_bind, bind_uniformParity_eq_uniform]
  simpa only [expandedPublicKey] using bind_rotate
    (PMF.uniformOfFinset (weightLayer P.n P.omega) (weightLayer_nonempty P.omega_le_n))
    (PMF.uniformOfFinset (weightLayer P.n P.omega) (weightLayer_nonempty P.omega_le_n))
    (PMF.uniformOfFintype (RingWord P))
    (fun y x h =>
      (ProbComp.eval (adversary.choose (expandedPublicKey P h x y))).bind fun choice =>
      (PMF.uniformOfFintype Bool).bind fun bit =>
      (PMF.uniformOfFinset (weightLayer P.n P.omegaR)
        (weightLayer_nonempty P.omegaR_le_n)).bind fun r2 =>
      (PMF.uniformOfFinset (weightLayer P.n P.omegaE)
        (weightLayer_nonempty P.omegaE_le_n)).bind fun e =>
      (PMF.uniformOfFinset (weightLayer P.n P.omegaR)
        (weightLayer_nonempty P.omegaR_le_n)).bind fun r1 =>
      (ProbComp.eval (adversary.guess choice.2
        (pkeEncrypt P encode (expandedPublicKey P h x y) (choice.1.select bit) ⟨r2, e, r1⟩))).bind
          fun guess => PMF.pure (guess == bit))

/-- HQC v5.1 Game2 is exactly the real 3-DQCSD-PT reduction game. The equality of the two
encryption weights is explicit because the source 3-DQCSD-PT sample uses one weight for all three
sparse vectors. -/
theorem twoUniformGame_eq_threeRealGame {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (hweight : P.omegaE = P.omegaR) :
    twoUniformGame P encode adversary = threeRealGame P encode adversary := by
  rw [threeRealGame, ← mixedTwoUniform_bind_coins_eq_mixedThreeReal P hweight]
  simp only [twoUniformGame, PMF.bind_bind]
  apply congrArg (mixedTwoUniformLaw P).bind
  funext sample
  unfold twoDQCSDDistinguisher threeDQCSDDistinguisher
    SyndromeSample.toPKEPublicKey TruncatedSyndromeSample.toPKEPublicKey
    TruncatedSyndromeSample.toPKECiphertext
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, Function.comp_def]
  simpa only [Game, SyndromeSample.toPKEPublicKey, truncateEncryptionSample, pkeEncrypt,
    syndrome, truncate, add_comm] using
    bind_last_first (ProbComp.eval (adversary.choose (sample.toPKEPublicKey P)))
      (PMF.uniformOfFintype Bool) (ProbComp.eval (pkeSampleCoins P))
      (fun choice bit coins =>
        (ProbComp.eval (adversary.guess choice.2
          (pkeEncrypt P encode (sample.toPKEPublicKey P) (choice.1.select bit) coins))).bind
            fun guess => PMF.pure (guess == bit))

omit [NeZero P.n] in
private theorem uniformMaskGame_eq_uniform {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (pk : PKEPublicKey P) (u : RingWord P) :
    (PMF.uniformOfFintype (Codeword P)).bind (fun mask =>
      (ProbComp.eval (adversary.choose pk)).bind fun choice =>
      (PMF.uniformOfFintype Bool).bind fun bit =>
      (ProbComp.eval (adversary.guess choice.2
        ⟨u, encode (choice.1.select bit) + mask⟩)).bind fun guess =>
      PMF.pure (guess == bit)) = PMF.uniformOfFintype Bool := by
  rw [PMF.bind_comm (PMF.uniformOfFintype (Codeword P))
    (ProbComp.eval (adversary.choose pk))]
  conv_rhs =>
    rw [← PMF.bind_const (ProbComp.eval (adversary.choose pk))
      (PMF.uniformOfFintype Bool)]
  apply congrArg (ProbComp.eval (adversary.choose pk)).bind
  funext choice
  rw [PMF.bind_comm (PMF.uniformOfFintype (Codeword P))
    (PMF.uniformOfFintype Bool)]
  have hmask : ∀ bit : Bool,
      (PMF.uniformOfFintype (Codeword P)).bind (fun mask =>
        (ProbComp.eval (adversary.guess choice.2
          ⟨u, encode (choice.1.select bit) + mask⟩)).bind fun guess =>
        PMF.pure (guess == bit)) =
      ((PMF.uniformOfFintype (Codeword P)).bind fun value =>
        ProbComp.eval (adversary.guess choice.2 ⟨u, value⟩)).map
          (fun guess => guess == bit) := by
    intro bit
    simp only [PMF.map, PMF.bind_bind, Function.comp_def]
    let c := encode (choice.1.select bit)
    let kernel : Codeword P → PMF Bool := fun value =>
      (ProbComp.eval (adversary.guess choice.2 ⟨u, value⟩)).bind fun guess =>
        PMF.pure (guess == bit)
    change (PMF.uniformOfFintype (Codeword P)).bind (kernel ∘ Equiv.addLeft c) =
      (PMF.uniformOfFintype (Codeword P)).bind kernel
    rw [← PMF.bind_map]
    rw [PMF.uniformOfFintype_map_equiv
      (Equiv.addLeft c)]
  rw [congrArg (PMF.uniformOfFintype Bool).bind (funext hmask)]
  exact Game.uniform_bool_bind_map_beq_const _

/-- HQC v5.1 Game3 is a fair hidden-bit game: the uniform retained component one-time-pads the
selected encoded message, including when the message pair depends on the public key. -/
theorem threeUniformGame_eq_uniform {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) :
    threeUniformGame P encode adversary = PMF.uniformOfFintype Bool := by
  unfold threeUniformGame mixedThreeUniformLaw uniformTruncatedSyndromeLaw
    threeDQCSDDistinguisher TruncatedSyndromeSample.toPKEPublicKey
    TruncatedSyndromeSample.toPKECiphertext
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind]
  simp_rw [uniformMaskGame_eq_uniform P encode adversary]
  simp only [PMF.bind_const]

/-- **HQC v5.1, Theorem 6.3, Equation (10).** The absolute hidden-bit IND-CPA bias of the ideal
expanded-value HQC-PKE core is at most the sum of the exact finite 2-DQCSD-P and 3-DQCSD-PT
advantages of the source reductions. The source gives no quantitative circuit-resource loss for
these reductions; this theorem therefore makes no asymptotic or native-quantum claim. -/
theorem indCpaAdvantage_le {State : Type}
    (encode : PKEMessage P → Codeword P)
    (adversary : TwoStage (PKEPublicKey P) (MessagePair (PKEMessage P))
      (PKECiphertext P) Bool State) (hweight : P.omegaE = P.omegaR) :
    indCpaAdvantage P encode adversary ≤
      twoDQCSDAdvantage P encode adversary + threeDQCSDAdvantage P encode adversary := by
  rw [indCpaAdvantage, twoDQCSDAdvantage, threeDQCSDAdvantage,
    eval_indCpaGame_eq_twoRealGame, twoUniformGame_eq_threeRealGame P encode adversary hweight,
    threeUniformGame_eq_uniform]
  exact Game.advantage_triangle _ _ _

end Cslib.Crypto.HQC
