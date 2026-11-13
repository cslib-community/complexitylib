/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Expect
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal

/-!
# Public-key encryption with explicit coins

This module formalizes public-key encryption `PKE = (Gen, Enc, Dec)` with an explicit encryption
coin type `R`, following [HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604 (full version dated
2 November 2021), §2.1. Exposing deterministic encryption `encDet : PK → M → R → CT` lets
transforms such as Fujisaki--Okamoto derive coins from a message and repeat encryption exactly.

`ExplicitCoinPKE` uses a fixed type `R` and an arbitrary sampler `sampleCoins : ProbComp R`, while
HHK17 permits a public-key-dependent randomness space and draws coins uniformly. Its
`DeltaCorrect` definition preserves the source's expectation over key generation of the
worst-message decryption-failure probability, and `GammaSpread` likewise generalizes the source's
uniform coin draw to `sampleCoins`.

The provided IND-CPA experiment is deliberately narrower than HHK17 §2.1, Definition 2.2 / Figure
4. `indCpaGame` takes caller-supplied messages `m₀, m₁` fixed before key generation, uses a
single-stage adversary, and `indCpaAdvantage` is the unnormalized probability difference between
the two fixed challenge sides. HHK17 instead lets a first stage choose key-dependent messages and
state, samples a challenge bit, and normalizes guessing advantage as `|Pr[b' = b] - 1/2|`.

Unlike the standard-model bit-string KEM interfaces in `Cslib.Crypto.Encryption.KEMINDCPA` and
`Cslib.Crypto.Encryption.encryptKeyEncaps`, this interface retains encryption coins and
deterministic encryption. KEM transforms and their security reductions live in separate modules.

## Main definitions

* `Cslib.Crypto.Protocols.ExplicitCoinPKE`: public-key encryption with explicit deterministic
  encryption coins.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.DeltaCorrect`: expected worst-message `δ`-correctness.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GammaSpread`: `γ`-spreadness over sampled coins.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.indCpaGame`,
  `Cslib.Crypto.Protocols.ExplicitCoinPKE.indCpaAdvantage`: the single-stage fixed-message
  distinguishing experiment and probability-difference advantage.

## Main results

* `Cslib.Crypto.Protocols.ExplicitCoinPKE.deltaCorrect_zero_of_perfect`: perfect supported
  decryption implies zero-error correctness.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.DeltaCorrect.mono`: correctness is monotone in `δ`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki--Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), §2.1.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols

open Probability
open scoped NNReal ENNReal

/-- A public-key encryption scheme `PKE = (Gen, Enc, Dec)` with explicit encryption coins `r : R`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1): randomized encryption draws
`r ← sampleCoins` and evaluates deterministic encryption `encDet pk m r`, allowing
Fujisaki--Okamoto transforms to derandomize encryption with `G(m) : R` and perform exact
re-encryption checks. Unlike §2.1's uniform draw from a potentially `pk`-dependent coin space,
`R` is a fixed type and `sampleCoins : ProbComp R` is an arbitrary sampler. -/
structure ExplicitCoinPKE (PK SK M R CT : Type) where
  /-- Key generation `(pk, sk) ← keyGen`. -/
  keyGen : ProbComp (PK × SK)
  /-- Encryption coin sampler `r ← sampleCoins`. -/
  sampleCoins : ProbComp R
  /-- Deterministic encryption `Enc(pk, m; r)` with explicit coins `r : R`. -/
  encDet : PK → M → R → CT
  /-- Deterministic decryption `Dec(sk, c) ∈ M ∪ {⊥}`. -/
  dec : SK → CT → Option M

namespace ExplicitCoinPKE

variable {PK SK M R CT : Type}

/-- Randomized encryption `Enc(pk, m)` drawing fresh coins `r ← sampleCoins`. -/
def encrypt (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (m : M) : ProbComp CT := do
  let r ← P.sampleCoins
  return P.encDet pk m r

/-- Per-message decryption failure probability `Pr_{r ← sampleCoins}[Dec(sk, Enc(pk, m; r)) ≠ m]`
for a fixed key pair `(pk, sk)` and message `m` ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604
(2 Nov 2021), §2.1, generalized from uniform coins to `sampleCoins`). -/
noncomputable def msgFailProb
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M) : ℝ :=
  ((ProbComp.eval P.sampleCoins).toOuterMeasure
    {r | P.dec sk (P.encDet pk m r) ≠ some m}).toReal

theorem msgFailProb_nonneg
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M) :
    0 ≤ P.msgFailProb pk sk m :=
  ENNReal.toReal_nonneg

theorem msgFailProb_le_one
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M) :
    P.msgFailProb pk sk m ≤ 1 := by
  rw [msgFailProb]
  exact PMF.toOuterMeasure_toReal_le_one _ _

/-- If `Dec(sk, Enc(pk, m; r)) = some m` holds for every supported coin `r`, the message failure
probability at `(pk, sk, m)` is `0`. -/
theorem msgFailProb_eq_zero_of_support
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M)
    (hdec : ∀ r ∈ (ProbComp.eval P.sampleCoins).support, P.dec sk (P.encDet pk m r) = some m) :
    P.msgFailProb pk sk m = 0 := by
  rw [msgFailProb, ENNReal.toReal_eq_zero_iff]
  left
  rw [_root_.PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro r hr hne
  exact hne (hdec r hr)

/-- Worst-case-over-messages decryption failure probability
`max_{m ∈ M} Pr_{r ← sampleCoins}[Dec(sk, Enc(pk, m; r)) ≠ m]` for a fixed key pair `(pk, sk)`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1). -/
noncomputable def keyPairMaxFailProb [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun m => P.msgFailProb pk sk m)

theorem msgFailProb_le_keyPairMaxFailProb [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) (m : M) :
    P.msgFailProb pk sk m ≤ P.keyPairMaxFailProb pk sk :=
  Finset.le_sup' (f := fun m => P.msgFailProb pk sk m) (Finset.mem_univ m)

theorem keyPairMaxFailProb_nonneg [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) :
    0 ≤ P.keyPairMaxFailProb pk sk := by
  obtain ⟨m₀⟩ := ‹Nonempty M›
  exact le_trans (P.msgFailProb_nonneg pk sk m₀) (P.msgFailProb_le_keyPairMaxFailProb pk sk m₀)

theorem keyPairMaxFailProb_le_one [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK) :
    P.keyPairMaxFailProb pk sk ≤ 1 := by
  rw [keyPairMaxFailProb, Finset.sup'_le_iff]
  intro m _
  exact P.msgFailProb_le_one pk sk m

/-- **HHK17 `δ`-correctness** ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1,
generalized from uniform coins to `sampleCoins`): the expectation over `(pk, sk) ← keyGen` of the
worst-case message decryption failure probability is at most `δ`:
`E_{(pk, sk) ← keyGen}[max_{m ∈ M} Pr_{r ← sampleCoins}[Dec(sk, Enc(pk, m; r)) ≠ m]] ≤ δ`. -/
def DeltaCorrect [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (δ : ℝ) : Prop :=
  (P.keyGen.expect fun (pk, sk) => ENNReal.ofReal (P.keyPairMaxFailProb pk sk)).toReal ≤ δ

/-- Monotonicity of `DeltaCorrect` in the failure bound `δ`. -/
theorem DeltaCorrect.mono [Fintype M] [Nonempty M]
    {P : ExplicitCoinPKE PK SK M R CT} {δ δ' : ℝ}
    (h : P.DeltaCorrect δ) (hle : δ ≤ δ') : P.DeltaCorrect δ' :=
  le_trans h hle

/-- A public-key encryption scheme whose supported key pairs and coins never incur decryption
errors is `0`-correct (`DeltaCorrect P 0`). -/
theorem deltaCorrect_zero_of_perfect [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT)
    (hperf : ∀ pk sk, (pk, sk) ∈ (ProbComp.eval P.keyGen).support →
      ∀ m, ∀ r ∈ (ProbComp.eval P.sampleCoins).support,
        P.dec sk (P.encDet pk m r) = some m) :
    P.DeltaCorrect 0 := by
  unfold DeltaCorrect
  have hcongr : P.keyGen.expect (fun (pk, sk) => ENNReal.ofReal (P.keyPairMaxFailProb pk sk)) =
      P.keyGen.expect (fun _ => 0) := by
    refine ProbComp.expect_congr_on_support ?_
    rintro ⟨pk, sk⟩ hkeys
    rw [← ProbComp.support_eval] at hkeys
    have hmax : P.keyPairMaxFailProb pk sk = 0 := by
      apply le_antisymm _ (P.keyPairMaxFailProb_nonneg pk sk)
      rw [keyPairMaxFailProb, Finset.sup'_le_iff]
      intro m _
      exact le_of_eq (P.msgFailProb_eq_zero_of_support pk sk m (hperf pk sk hkeys m))
    simp [hmax]
  rw [hcongr, ProbComp.expect_zero, ENNReal.toReal_zero]

/-- **HHK17 `γ`-spreadness** ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1,
generalized from uniform coins to `sampleCoins`): for every supported key pair
`(pk, sk) ∈ support(keyGen)`, message `m`, and ciphertext `c`, encryption hits `c` with
probability at most `2 ^ (-γ)` over fresh coins `r ← sampleCoins`. -/
def GammaSpread (P : ExplicitCoinPKE PK SK M R CT) (γ : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ (ProbComp.eval P.keyGen).support → ∀ (m : M) (c : CT),
    ((ProbComp.eval P.sampleCoins).toOuterMeasure
      {r | P.encDet pk m r = c}).toReal ≤ (2 : ℝ) ^ (-γ)

/-- Single-challenge fixed-message IND-CPA experiment for `ExplicitCoinPKE`: on bit `false` the
challenger encrypts `m₀`, and on bit `true` it encrypts `m₁`. Unlike [HofheinzHoevelmannsKiltz2017]
(ePrint 2017/604 (2 Nov 2021), §2.1, Def. 2.2 / Fig. 4), where a first-stage adversary receives
`pk` and chooses `(m₀, m₁)` with state, `(m₀, m₁)` are fixed caller-supplied messages independent
of `pk`. -/
def indCpaGame (P : ExplicitCoinPKE PK SK M R CT) (m₀ m₁ : M) (bit : Bool)
    (adversary : PK → CT → ProbComp Bool) : ProbComp Bool := do
  let (pk, _) ← P.keyGen
  let c ← P.encrypt pk (if bit then m₁ else m₀)
  adversary pk c

/-- Single-challenge fixed-message IND-CPA probability-difference advantage
`|Pr[indCpaGame m₀ m₁ false = true] - Pr[indCpaGame m₀ m₁ true = true]|` via `Game.advantage`
(whereas [HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.1, Def. 2.2 / Fig. 4
defines `|Pr[b' = b] - 1/2|` in a two-stage key-dependent-message guessing game). -/
noncomputable def indCpaAdvantage (P : ExplicitCoinPKE PK SK M R CT) (m₀ m₁ : M)
    (adversary : PK → CT → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (P.indCpaGame m₀ m₁ false adversary))
    (ProbComp.eval (P.indCpaGame m₀ m₁ true adversary))

end ExplicitCoinPKE

end Cslib.Crypto.Protocols
