/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Languages.Probabilistic.Expect
public import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF

/-!
# HHK17 Modular Fujisaki–Okamoto KEM Transforms

Hofheinz, Hövelmanns, and Kiltz ([HofheinzHoevelmannsKiltz2017]) decompose the Fujisaki–Okamoto
transformation of a public-key encryption scheme `PKE = (Gen, Enc, Dec)` with explicit coin space
`R` into two modular steps:

1. **Derandomization with mandatory re-encryption check `T[PKE, G]`** (`encT`, `decT`): given a
   random function `G : M → R`, encrypt `m` deterministically as `Enc(pk, m; G(m))`, and on
   decryption recompute `Enc(pk, m'; G(m')) = c` after running `Dec(sk, c) = some m'`, rejecting
   any ciphertext failing the check (`encT_of_decT_eq_some`).
2. **Key encapsulation with explicit or implicit rejection**:
   * `FO^⊥ = U^⊥ ∘ T` (`Scheme.encapsBot`, `Scheme.decapsBot`): decapsulation returns `none` on
     re-encryption failure and `some (H(false, m', c))` on success.
   * `FO^⫫ = U^⫫ ∘ T` (`Scheme.keyGenNotBot`, `Scheme.encapsNotBot`, `Scheme.decapsNotBot`): the
     secret key (`ImplicitSK`) retains the public key `pk` and a secret fallback seed
     `fallback ← M`, returning a pseudorandom fallback key `H(true, fallback, c)` on
     decapsulation rejection so decapsulation never outputs failure externally.

**Scope of this module**: this file formalizes `ExplicitCoinPKE` (together with expected
worst-case-message `δ`-correctness `ExplicitCoinPKE.DeltaCorrect`, `γ`-spreadness
`ExplicitCoinPKE.GammaSpread`, and the single-challenge two-message IND-CPA experiment
`ExplicitCoinPKE.indCpaGame` / `ExplicitCoinPKE.indCpaAdvantage`) and the `T`, `FO^⊥`, and `FO^⫫`
transforms together with their deterministic recovery and re-encryption rigidity lemmas. Adaptive
random-oracle IND-CCA games and security reductions are deferred to follow-up modules.

**Modeling note on domain-separated `H`**: in [HofheinzHoevelmannsKiltz2017], `U^⫫` derives both
honest keys `H(m, c)` and implicit-rejection keys `H(s, c)` from a single untagged random oracle
`H : M × CT → K` using a secret seed `s ← M`. Here `H` has domain `Bool × M × CT → K`, with
`false` tagging valid key derivations `H(false, m, c)` and `true` tagging implicit-rejection
queries `H(true, fallback, c)`. This is a deliberate domain-separated variant (analogous to the
separate implicit-rejection hash `J(s, c)` in ML-KEM / FIPS 203) that keeps the valid-key and
rejection-key namespaces disjoint. It does not affect the deterministic correctness and
re-encryption rigidity lemmas proved below; its effect on random-oracle security bounds is not
analysed in this module.

Unlike the standard-model bit-string KEM interfaces in `Cslib.Crypto.Encryption.KEMINDCPA`
(`Complexity/Crypto/Computational/Encryption/Hybrid.lean`),
`Cslib.Crypto.Encryption.encryptKeyEncaps`
(`Complexity/Crypto/Computational/Encryption/KEMFromPKE.lean`), and
`Complexity/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean` (which encrypt a sampled key
directly without derandomization or re-encryption checks), `ExplicitCoinPKE` exposes the
encryption coin space `R` and deterministic encryption `encDet : PK → M → R → CT` needed for `T`
to recompute `Enc(pk, m'; G(m'))` during decapsulation.

## Main definitions

* `Cslib.Crypto.Protocols.ExplicitCoinPKE`: public-key encryption with explicit deterministic
  encryption coins `encDet : PK → M → R → CT`.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.DeltaCorrect`,
  `Cslib.Crypto.Protocols.ExplicitCoinPKE.GammaSpread`: HHK17 `δ`-correctness and `γ`-spreadness.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.indCpaGame`,
  `Cslib.Crypto.Protocols.ExplicitCoinPKE.indCpaAdvantage`: two-message IND-CPA game and advantage.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.encT`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.decT`: the `T[PKE, G]` derandomization and re-encryption
  check transform.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ImplicitSK`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme`: implicit-rejection secret key and FO parameter
  bundle (`FO^⊥` via `Scheme.encapsBot` / `Scheme.decapsBot` and domain-separated `FO^⫫` via
  `Scheme.keyGenNotBot` / `Scheme.encapsNotBot` / `Scheme.decapsNotBot`).

## Main results

* `Cslib.Crypto.Protocols.ExplicitCoinPKE.deltaCorrect_zero_of_perfect`,
  `Cslib.Crypto.Protocols.ExplicitCoinPKE.DeltaCorrect.mono`: zero-error correctness and
  monotonicity in `δ`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.decT_encT_eq_some`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.encT_of_decT_eq_some`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.dec_of_decT_eq_some`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.decT_eq_none_of_reencrypt_ne`: correctness and rigid
  ciphertext soundness of the `T` re-encryption check.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsBot_encT_eq_some`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsBot_eq_none_of_reencrypt_ne`: honest
  recovery and explicit rejection for `FO^⊥`.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNotBot_encT_eq`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNotBot_of_reencrypt_ne`: honest recovery
  and pseudorandom fallback rejection for `FO^⫫`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017].
-/

@[expose] public section

namespace Cslib.Crypto.Protocols

open Probability
open scoped NNReal ENNReal

/-- A public-key encryption scheme `PKE = (Gen, Enc, Dec)` with explicit encryption coins `r : R`
([HofheinzHoevelmannsKiltz2017]): randomized encryption draws `r ← sampleCoins` and evaluates
deterministic encryption `encDet pk m r`, allowing Fujisaki–Okamoto transforms to derandomize
encryption with `G(m) : R` and perform exact re-encryption checks. -/
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
for a fixed key pair `(pk, sk)` and message `m` ([HofheinzHoevelmannsKiltz2017]). -/
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
  rw [msgFailProb, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.toOuterMeasure_le_one _ _)

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
([HofheinzHoevelmannsKiltz2017]). -/
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

/-- **HHK17 `δ`-correctness** ([HofheinzHoevelmannsKiltz2017]): the expectation over
`(pk, sk) ← keyGen` of the worst-case message decryption failure probability is at most `δ`:
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

/-- **HHK17 `γ`-spreadness** ([HofheinzHoevelmannsKiltz2017]): for every supported key
pair `(pk, sk) ∈ support(keyGen)`, message `m`, and ciphertext `c`, encryption hits `c` with
probability at most `2 ^ (-γ)` over fresh coins `r ← sampleCoins`. -/
def GammaSpread (P : ExplicitCoinPKE PK SK M R CT) (γ : ℝ) : Prop :=
  ∀ pk sk, (pk, sk) ∈ (ProbComp.eval P.keyGen).support → ∀ (m : M) (c : CT),
    ((ProbComp.eval P.sampleCoins).toOuterMeasure
      {r | P.encDet pk m r = c}).toReal ≤ (2 : ℝ) ^ (-γ)

/-- Single-challenge two-message IND-CPA experiment for `ExplicitCoinPKE`: on bit `false` the
challenger encrypts `m₀`, and on bit `true` it encrypts `m₁`. -/
def indCpaGame (P : ExplicitCoinPKE PK SK M R CT) (m₀ m₁ : M) (bit : Bool)
    (adversary : PK → CT → ProbComp Bool) : ProbComp Bool := do
  let (pk, _) ← P.keyGen
  let c ← P.encrypt pk (if bit then m₁ else m₀)
  adversary pk c

/-- Single-challenge two-message IND-CPA distinguishing advantage
`|Pr[indCpaGame m₀ m₁ false = true] - Pr[indCpaGame m₀ m₁ true = true]|`. -/
noncomputable def indCpaAdvantage (P : ExplicitCoinPKE PK SK M R CT) (m₀ m₁ : M)
    (adversary : PK → CT → ProbComp Bool) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (P.indCpaGame m₀ m₁ false adversary))
    (ProbComp.eval (P.indCpaGame m₀ m₁ true adversary))

end ExplicitCoinPKE

namespace FujisakiOkamoto

/-! ### `T[PKE, G]`: Derandomization with Mandatory Re-Encryption Check -/

section TransformT

variable {PK SK M R CT : Type}

/-- Derandomized encryption `Enc_1(pk, m) := Enc(pk, m; G(m))` of `T[PKE, G]`
([HofheinzHoevelmannsKiltz2017]). -/
def encT (P : ExplicitCoinPKE PK SK M R CT) (G : M → R) (pk : PK) (m : M) : CT :=
  P.encDet pk m (G m)

/-- Derandomized decryption `Dec_1(pk, sk, c)` of `T[PKE, G]` with mandatory re-encryption check
([HofheinzHoevelmannsKiltz2017]): runs `m' ← Dec(sk, c)` and accepts `m'` only when
`Enc(pk, m'; G(m')) = c`. -/
def decT [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT) (G : M → R)
    (pk : PK) (sk : SK) (c : CT) : Option M :=
  match P.dec sk c with
  | none => none
  | some m' => if encT P G pk m' = c then some m' else none

/-- Whenever `Dec(sk, Enc_1(pk, m)) = some m`, the re-encryption check succeeds and `decT`
recovers `some m`. -/
theorem decT_encT_eq_some [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT) (G : M → R)
    (pk : PK) (sk : SK) (m : M) (hdec : P.dec sk (encT P G pk m) = some m) :
    decT P G pk sk (encT P G pk m) = some m := by
  simp [decT, hdec]

/-- **Rigidity of `T`**: any plaintext `m'` accepted by `decT` re-encrypts strictly to `c`, and
satisfies `P.dec sk c = some m'`. -/
theorem encT_of_decT_eq_some [DecidableEq CT] {P : ExplicitCoinPKE PK SK M R CT} {G : M → R}
    {pk : PK} {sk : SK} {c : CT} {m' : M} (h : decT P G pk sk c = some m') :
    encT P G pk m' = c := by
  unfold decT at h
  cases hdec : P.dec sk c with
  | none => simp [hdec] at h
  | some m₀ =>
    simp only [hdec] at h
    split_ifs at h with henc
    simp only [Option.some.injEq] at h
    exact h ▸ henc

theorem dec_of_decT_eq_some [DecidableEq CT] {P : ExplicitCoinPKE PK SK M R CT} {G : M → R}
    {pk : PK} {sk : SK} {c : CT} {m' : M} (h : decT P G pk sk c = some m') :
    P.dec sk c = some m' := by
  unfold decT at h
  cases hdec : P.dec sk c with
  | none => simp [hdec] at h
  | some m₀ =>
    simp only [hdec] at h
    split_ifs at h
    simpa only [Option.some.injEq] using h

/-- Any ciphertext failing the re-encryption check on its decrypted candidate is rejected by
`decT`. -/
theorem decT_eq_none_of_reencrypt_ne [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT)
    (G : M → R) (pk : PK) (sk : SK) (c : CT)
    (hbad : ∀ m', P.dec sk c = some m' → encT P G pk m' ≠ c) :
    decT P G pk sk c = none := by
  unfold decT
  cases hdec : P.dec sk c with
  | none => rfl
  | some m' => exact ite_eq_right (hbad m' hdec)

end TransformT

/-! ### `FO^⊥` and `FO^⫫`: Explicit- and Implicit-Rejection KEM Transforms -/

/-- Extended secret key `(sk, pk, fallback)` of the implicit-rejection KEM `FO^⫫`
([HofheinzHoevelmannsKiltz2017]), retaining the public key for the re-encryption check and a
secret fallback message seed `fallback ∈ M`. -/
structure ImplicitSK (PK SK M : Type) where
  /-- Underlying PKE secret key `sk`. -/
  sk : SK
  /-- Underlying PKE public key `pk`, stored to recompute `Enc(pk, m'; G(m'))`. -/
  pk : PK
  /-- Secret fallback seed `s ∈ M` used to derive pseudorandom keys on invalid ciphertexts. -/
  fallback : M
  deriving DecidableEq

/-- Parameter bundle for the HHK17 Fujisaki–Okamoto KEM transforms `FO^⊥` and `FO^⫫`
([HofheinzHoevelmannsKiltz2017]): an `ExplicitCoinPKE` scheme paired with its message-space
sampler `sampleMsg` and shared-key sampler `sampleKey`. -/
structure Scheme (PK SK M R CT K : Type) where
  /-- Underlying explicit-coin public-key encryption scheme `PKE`. -/
  pke : ExplicitCoinPKE PK SK M R CT
  /-- Sampler `m ← M` for encapsulated plaintexts and implicit-rejection seeds. -/
  sampleMsg : ProbComp M
  /-- Sampler `k ← K` for shared KEM keys. -/
  sampleKey : ProbComp K

namespace Scheme

section FixedOracles

variable {PK SK M R CT K : Type}

/-- Encapsulation `Encaps^⊥(pk)` for `FO^⊥ = U^⊥ ∘ T` with fixed functions `G` and
domain-separated `H` ([HofheinzHoevelmannsKiltz2017]): samples `m ← sampleMsg`, computes
`c := Enc(pk, m; G(m))`, and outputs `(c, H(false, m, c))`. -/
def encapsBot (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (pk : PK) : ProbComp (CT × K) := do
  let m ← S.sampleMsg
  let c := encT S.pke G pk m
  return (c, H (false, m, c))

/-- Explicit-rejection decapsulation `Decaps^⊥(pk, sk, c)` for `FO^⊥ = U^⊥ ∘ T`
([HofheinzHoevelmannsKiltz2017]): returns `some (H(false, m', c))` when `decT` accepts `m'`, and
`none` otherwise. -/
def decapsBot [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT) : Option K :=
  (decT S.pke G pk sk c).map fun m' => H (false, m', c)

/-- Honest recovery for `FO^⊥`: whenever `Dec(sk, Enc_1(pk, m)) = some m`, `decapsBot` returns
`some (H(false, m, Enc_1(pk, m)))`. -/
theorem decapsBot_encT_eq_some [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (m : M)
    (hdec : S.pke.dec sk (encT S.pke G pk m) = some m) :
    S.decapsBot G H pk sk (encT S.pke G pk m) = some (H (false, m, encT S.pke G pk m)) := by
  simp [decapsBot, decT_encT_eq_some S.pke G pk sk m hdec]

theorem decapsBot_eq_none_of_decT_eq_none [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT)
    (hnone : decT S.pke G pk sk c = none) :
    S.decapsBot G H pk sk c = none := by
  simp [decapsBot, hnone]

/-- Explicit rejection for `FO^⊥`: any tampered ciphertext failing the re-encryption check
decapsulates to `none`. -/
theorem decapsBot_eq_none_of_reencrypt_ne [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT)
    (hbad : ∀ m', S.pke.dec sk c = some m' → encT S.pke G pk m' ≠ c) :
    S.decapsBot G H pk sk c = none :=
  S.decapsBot_eq_none_of_decT_eq_none G H pk sk c
    (decT_eq_none_of_reencrypt_ne S.pke G pk sk c hbad)

/-- Key generation `Gen^⫫` for `FO^⫫ = U^⫫ ∘ T` ([HofheinzHoevelmannsKiltz2017]):
generates `(pk, sk) ← pke.keyGen`, samples a secret seed `s ← sampleMsg`, and outputs
`(pk, ⟨sk, pk, s⟩)`. -/
def keyGenNotBot (S : Scheme PK SK M R CT K) : ProbComp (PK × ImplicitSK PK SK M) := do
  let (pk, sk) ← S.pke.keyGen
  let s ← S.sampleMsg
  return (pk, { sk := sk, pk := pk, fallback := s })

/-- Encapsulation `Encaps^⫫(pk)` for `FO^⫫ = U^⫫ ∘ T` ([HofheinzHoevelmannsKiltz2017]),
identical to `encapsBot`. -/
def encapsNotBot (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (pk : PK) : ProbComp (CT × K) :=
  S.encapsBot G H pk

/-- Implicit-rejection decapsulation `Decaps^⫫(dk, c)` for the domain-separated variant of
`FO^⫫ = U^⫫ ∘ T` ([HofheinzHoevelmannsKiltz2017]): returns `H(false, m', c)` when `decT` accepts
`m'`, and returns the domain-separated pseudorandom fallback key `H(true, dk.fallback, c)`
otherwise (where the `Bool` tag separates valid key derivations from rejection evaluations, in
place of HHK17's untagged `H(s, c)`). -/
def decapsNotBot [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT) : K :=
  match decT S.pke G dk.pk dk.sk c with
  | some m' => H (false, m', c)
  | none => H (true, dk.fallback, c)

/-- Honest recovery for `FO^⫫`: whenever `Dec(dk.sk, Enc_1(dk.pk, m)) = some m`, the re-encryption
check passes and `decapsNotBot` outputs `H(false, m, Enc_1(dk.pk, m))`. -/
theorem decapsNotBot_encT_eq [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (m : M)
    (hdec : S.pke.dec dk.sk (encT S.pke G dk.pk m) = some m) :
    S.decapsNotBot G H dk (encT S.pke G dk.pk m) = H (false, m, encT S.pke G dk.pk m) := by
  simp [decapsNotBot, decT_encT_eq_some S.pke G dk.pk dk.sk m hdec]

theorem decapsNotBot_of_decT_eq_none [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT)
    (hnone : decT S.pke G dk.pk dk.sk c = none) :
    S.decapsNotBot G H dk c = H (true, dk.fallback, c) := by
  simp [decapsNotBot, hnone]

/-- Implicit pseudorandom rejection for `FO^⫫`: any tampered ciphertext failing the re-encryption
check decapsulates to `H(true, dk.fallback, c)`. -/
theorem decapsNotBot_of_reencrypt_ne [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT)
    (hbad : ∀ m', S.pke.dec dk.sk c = some m' → encT S.pke G dk.pk m' ≠ c) :
    S.decapsNotBot G H dk c = H (true, dk.fallback, c) :=
  S.decapsNotBot_of_decT_eq_none G H dk c
    (decT_eq_none_of_reencrypt_ne S.pke G dk.pk dk.sk c hbad)

end FixedOracles

end Scheme

end FujisakiOkamoto

end Cslib.Crypto.Protocols
