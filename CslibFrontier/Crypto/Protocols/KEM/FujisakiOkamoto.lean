/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.ToReal

/-!
# HHK17 Modular Fujisaki–Okamoto KEM Transforms

Hofheinz, Hövelmanns, and Kiltz ([HofheinzHoevelmannsKiltz2017], IACR ePrint 2017/604 full version
dated 2 November 2021) decompose the Fujisaki–Okamoto transformation of a public-key encryption
scheme `PKE = (Gen, Enc, Dec)` with explicit coin space `R` into two modular steps:

1. **Derandomization with mandatory re-encryption check `T[PKE, G]`** (`encT`, `decT`;
   §3.1, Fig. 5): given a function `G : M → R`, encrypt `m` deterministically as
   `Enc(pk, m; G(m))`, and on decryption recompute `Enc(pk, m'; G(m')) = c` after running
   `Dec(sk, c) = some m'`, rejecting any ciphertext failing the check (`encT_of_decT_eq_some`).
2. **Key encapsulation with explicit or implicit rejection**:
   * `FO^⊥ = U^⊥ ∘ T` (`Scheme.encapsBot`, `Scheme.decapsBot`; §3.2.1, Fig. 9): decapsulation
     returns `none` on re-encryption failure and `some (H(false, m', c))` on success.
   * `FO-notbot = U-notbot ∘ T` (`Scheme.keyGenNotBot`, `Scheme.encapsNotBot`,
     `Scheme.decapsNotBot`; §3.2.2, Fig. 12, written with a negated-`⊥` superscript in the paper):
     the secret key (`ImplicitSK`) retains the public key `pk` and a secret fallback seed
     `fallback ← M`, returning a pseudorandom fallback key `H(true, fallback, c)` on
     decapsulation rejection so decapsulation never outputs failure externally.

**Scope of this module**: this file formalizes the `T`, `FO^⊥`, and `FO-notbot` transforms together
with their deterministic recovery and re-encryption rigidity lemmas. The generic explicit-coin PKE
interface, correctness and spreadness live in `CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin`.
The IND-CPA notion of the FO security theorems is two-stage IND-CPA (`cpaAdvantage`, via
`PKE.cpaExperiment` on `ExplicitCoinPKE.toPKE`), not the fixed-message `indCpaGame`. Adaptive
random-oracle IND-CCA games and the security reductions live in the `FujisakiOkamoto/` submodules;
a standalone transfer of PKE `δ`-correctness to KEM correctness is not formalized (`δ` enters only
as a hop inside the IND-CCA bounds).

## Source map and model differences

All section and figure locators refer to the full version of [HofheinzHoevelmannsKiltz2017] served
by IACR ePrint 2017/604, dated **2 November 2021**:

* **§3.1, Figure 5**: derandomization and re-encryption check transform `T[PKE, G]` (`encT`,
  `decT`).
* **§3.2.1, Figure 9**: explicit-rejection KEM `FO^⊥ = U^⊥ ∘ T` (`Scheme.encapsBot`,
  `Scheme.decapsBot`).
* **§3.2.2, Figure 12**: implicit-rejection KEM `FO-notbot = U-notbot ∘ T` (`ImplicitSK`,
  `Scheme.keyGenNotBot`, `Scheme.encapsNotBot`, `Scheme.decapsNotBot`).

The PKE-level fixed-coin-type and arbitrary-sampler differences are documented in
`CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin`; the security theorems use two-stage
IND-CPA. This transform differs from the
paper's presentation in two further respects:

1. **Fixed message/key types and arbitrary samplers**: in [HofheinzHoevelmannsKiltz2017]
   (§3.2.1 Fig. 9, §3.2.2 Fig. 12), encapsulated messages, fallback seeds, and ideal keys are drawn
   uniformly. Here `Scheme` uses fixed types `M`, `K` and arbitrary `ProbComp` samplers
   `sampleMsg : ProbComp M` and `sampleKey : ProbComp K`. The deterministic transform lemmas hold
   for arbitrary samplers and fixed functions `G, H`.
2. **Domain-separated `H : Bool × M × CT → K` in `FO-notbot`**: in [HofheinzHoevelmannsKiltz2017]
   (§3.2.1 Fig. 9, §3.2.2 Fig. 12), `U^⊥` and `U-notbot` derive honest keys `H(m, c)` and
   implicit-rejection keys `H(s, c)` from a single untagged random oracle `H : M × CT → K` using a
   secret seed `s ←$ M`. Here `H` has domain `Bool × M × CT → K`, with `false` tagging valid key
   derivations `H(false, m, c)` and `true` tagging implicit-rejection queries
   `H(true, fallback, c)`. This deliberate domain-separated variant (analogous to the separate
   implicit-rejection hash `J(s, c)` in ML-KEM / FIPS 203) keeps the valid-key and rejection-key
   namespaces disjoint. It does not affect the deterministic correctness and re-encryption rigidity
   lemmas proved below; its effect on random-oracle security bounds is not analysed in this module.

The imported `ExplicitCoinPKE` interface exposes the deterministic encryption needed for `T` to
recompute `Enc(pk, m'; G(m'))` during decapsulation.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.encT`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.decT`: the `T[PKE, G]` derandomization and re-encryption
  check transform (§3.1, Fig. 5).
* `Cslib.Crypto.Protocols.FujisakiOkamoto.ImplicitSK`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme`: implicit-rejection secret key and FO parameter
  bundle (`FO^⊥` via `Scheme.encapsBot` / `Scheme.decapsBot` (§3.2.1, Fig. 9) and
  domain-separated `FO-notbot` via `Scheme.keyGenNotBot` / `Scheme.encapsNotBot` /
  `Scheme.decapsNotBot` (§3.2.2, Fig. 12)).
* `Cslib.Crypto.Protocols.FujisakiOkamoto.decTM`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsBotM`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.decapsNotBotM`: the `T` check and both
  decapsulation algorithms with oracle access to `G` and `H` in any monad, run by the random-oracle
  games. `decT`, `decapsBot` and `decapsNotBot` are these in the identity monad; with pure oracles
  in any lawful monad the decapsulations return `decapsBot` and `decapsNotBot`
  (`Scheme.decapsBotM_pure`, `Scheme.decapsNotBotM_pure`).

## Main results

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
  and pseudorandom fallback rejection for `FO-notbot`.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols

open Probability
open scoped NNReal ENNReal

namespace FujisakiOkamoto

/-! ### `T[PKE, G]`: Derandomization with Mandatory Re-Encryption Check -/

section TransformT

variable {PK SK M R CT : Type}

/-- Derandomized encryption `Enc_1(pk, m) := Enc(pk, m; G(m))` of `T[PKE, G]`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.1, Fig. 5). -/
def encT (P : ExplicitCoinPKE PK SK M R CT) (G : M → R) (pk : PK) (m : M) : CT :=
  P.encDet pk m (G m)

/-- Derandomized decryption `Dec_1(pk, sk, c)` of `T[PKE, G]` with mandatory re-encryption check
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.1, Fig. 5): runs
`m' ← Dec(sk, c)` and accepts `m'` only when `Enc(pk, m'; G(m')) = c`, with oracle access to
`G : M → m R` in a monad `m`. `G` is queried only when `Dec` succeeds. The random-oracle games run
it with lazily sampled `G`; `decT` is the case of a fixed function `G`. -/
def decTM [DecidableEq CT] {m : Type → Type} [Monad m] (P : ExplicitCoinPKE PK SK M R CT)
    (G : M → m R) (pk : PK) (sk : SK) (c : CT) : m (Option M) :=
  match P.dec sk c with
  | none => return none
  | some m' => do
    let r' ← G m'
    return if P.encDet pk m' r' = c then some m' else none

/-- Derandomized decryption `Dec_1(pk, sk, c)` of `T[PKE, G]` with mandatory re-encryption check
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.1, Fig. 5) for a fixed
function `G`: `decTM` in the identity monad. -/
def decT [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT) (G : M → R)
    (pk : PK) (sk : SK) (c : CT) : Option M :=
  decTM (m := Id) P G pk sk c

/-- `decT` runs `m' ← Dec(sk, c)` and accepts `m'` only when `Enc(pk, m'; G(m')) = c`. -/
theorem decT_eq [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT) (G : M → R)
    (pk : PK) (sk : SK) (c : CT) :
    decT P G pk sk c =
      match P.dec sk c with
      | none => none
      | some m' => if encT P G pk m' = c then some m' else none := by
  unfold decT decTM encT
  cases P.dec sk c <;> rfl

/-- With a pure oracle, `decTM` is `decT`. -/
@[simp] theorem decTM_pure [DecidableEq CT] {m : Type → Type} [Monad m] [LawfulMonad m]
    (P : ExplicitCoinPKE PK SK M R CT) (G : M → R) (pk : PK) (sk : SK) (c : CT) :
    decTM (m := m) P (pure ∘ G) pk sk c = pure (decT P G pk sk c) := by
  rw [decT_eq]
  unfold decTM encT
  cases P.dec sk c <;> simp

/-- Whenever `Dec(sk, Enc_1(pk, m)) = some m`, the re-encryption check succeeds and `decT`
recovers `some m`. -/
theorem decT_encT_eq_some [DecidableEq CT] (P : ExplicitCoinPKE PK SK M R CT) (G : M → R)
    (pk : PK) (sk : SK) (m : M) (hdec : P.dec sk (encT P G pk m) = some m) :
    decT P G pk sk (encT P G pk m) = some m := by
  simp [decT_eq, hdec]

/-- **Rigidity of `T`**: any plaintext `m'` accepted by `decT` re-encrypts strictly to `c`, and
satisfies `P.dec sk c = some m'`. -/
theorem encT_of_decT_eq_some [DecidableEq CT] {P : ExplicitCoinPKE PK SK M R CT} {G : M → R}
    {pk : PK} {sk : SK} {c : CT} {m' : M} (h : decT P G pk sk c = some m') :
    encT P G pk m' = c := by
  rw [decT_eq] at h
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
  rw [decT_eq] at h
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
  rw [decT_eq]
  cases hdec : P.dec sk c with
  | none => rfl
  | some m' => exact ite_eq_right (hbad m' hdec)

end TransformT

/-! ### `FO^⊥` and `FO-notbot`: Explicit- and Implicit-Rejection KEM Transforms -/

/-- Extended secret key `(sk, pk, fallback)` of the implicit-rejection KEM `FO-notbot`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.2, Fig. 12), retaining the
public key for the re-encryption check and a secret fallback message seed `fallback ∈ M`. -/
structure ImplicitSK (PK SK M : Type) where
  /-- Underlying PKE secret key `sk`. -/
  sk : SK
  /-- Underlying PKE public key `pk`, stored to recompute `Enc(pk, m'; G(m'))`. -/
  pk : PK
  /-- Secret fallback seed `s ∈ M` used to derive pseudorandom keys on invalid ciphertexts. -/
  fallback : M
  deriving DecidableEq

/-- Parameter bundle for the HHK17 Fujisaki–Okamoto KEM transforms `FO^⊥` and `FO-notbot`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.1 Fig. 9 and §3.2.2 Fig. 12):
an `ExplicitCoinPKE` scheme paired with its message-space sampler `sampleMsg` and shared-key
sampler `sampleKey` (generalizing the paper's uniform draws from `M` and `K`). -/
structure Scheme (PK SK M R CT K : Type) where
  /-- Underlying explicit-coin public-key encryption scheme `PKE`. -/
  pke : ExplicitCoinPKE PK SK M R CT
  /-- Sampler `m ← M` for encapsulated plaintexts and implicit-rejection seeds. -/
  sampleMsg : ProbComp M
  /-- Sampler `k ← K` for shared KEM keys. -/
  sampleKey : ProbComp K

namespace Scheme

/-! ### Decapsulation with oracle access

The random-oracle games answer `G` and `H` lazily, so their decapsulation oracles run the
decapsulation algorithms with `G : M → m R` and `H : Bool × M × CT → m K` given as oracles in a
monad `m`. Both run the `T` check `decTM` and add only their rejection policy and `H` query.
`decapsBotM_eq` and `decapsNotBotM_eq` unfold them into explicit oracle calls. The fixed-function
decapsulations `decapsBot` and `decapsNotBot` below are these algorithms in the identity monad; with
pure oracles in any lawful monad, the oracle-access versions return them (`decapsBotM_pure`,
`decapsNotBotM_pure`). -/

section OracleAccess

variable {PK SK M R CT K : Type} [DecidableEq CT] {m : Type → Type} [Monad m]

/-- Explicit-rejection decapsulation `Decaps^⊥(pk, sk, c)` of `FO^⊥` with oracle access to `G` and
`H`: returns `some (H(false, m', c))` when `decTM` accepts `m'`, and `none` otherwise. -/
def decapsBotM (S : Scheme PK SK M R CT K) (G : M → m R) (H : Bool × M × CT → m K) (pk : PK)
    (sk : SK) (c : CT) : m (Option K) := do
  match ← decTM S.pke G pk sk c with
  | some m' => some <$> H (false, m', c)
  | none => return none

/-- Implicit-rejection decapsulation `Decaps-notbot(dk, c)` of `FO-notbot` with oracle access to
`G` and `H`: returns `H(false, m', c)` when `decTM` accepts `m'`, and the fallback key
`H(true, dk.fallback, c)` otherwise. -/
def decapsNotBotM (S : Scheme PK SK M R CT K) (G : M → m R) (H : Bool × M × CT → m K)
    (dk : ImplicitSK PK SK M) (c : CT) : m K := do
  match ← decTM S.pke G dk.pk dk.sk c with
  | some m' => H (false, m', c)
  | none => H (true, dk.fallback, c)

variable [LawfulMonad m]

/-- `decapsBotM` as explicit oracle calls: no query when `Dec` fails; otherwise `G(m')`, then
`H(false, m', c)` exactly when the re-encryption check passes. -/
theorem decapsBotM_eq (S : Scheme PK SK M R CT K) (G : M → m R) (H : Bool × M × CT → m K)
    (pk : PK) (sk : SK) (c : CT) :
    S.decapsBotM G H pk sk c =
      (match S.pke.dec sk c with
      | none => return none
      | some m' => do
        let r' ← G m'
        if S.pke.encDet pk m' r' = c then do
          let k ← H (false, m', c)
          return some k
        else
          return none) := by
  unfold decapsBotM decTM
  cases S.pke.dec sk c with
  | none => simp
  | some m' =>
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun r' => ?_
    split_ifs <;> simp

/-- `decapsNotBotM` as explicit oracle calls: `H(true, dk.fallback, c)` when `Dec` fails;
otherwise `G(m')`, then `H(false, m', c)` or `H(true, dk.fallback, c)` by the re-encryption
check. -/
theorem decapsNotBotM_eq (S : Scheme PK SK M R CT K) (G : M → m R) (H : Bool × M × CT → m K)
    (dk : ImplicitSK PK SK M) (c : CT) :
    S.decapsNotBotM G H dk c =
      (match S.pke.dec dk.sk c with
      | none => H (true, dk.fallback, c)
      | some m' => do
        let r' ← G m'
        if S.pke.encDet dk.pk m' r' = c then H (false, m', c) else H (true, dk.fallback, c)) := by
  unfold decapsNotBotM decTM
  cases S.pke.dec dk.sk c with
  | none => simp
  | some m' =>
    simp only [bind_assoc, pure_bind]
    refine bind_congr fun r' => ?_
    split_ifs <;> rfl

end OracleAccess

section FixedOracles

variable {PK SK M R CT K : Type}

/-- Encapsulation `Encaps^⊥(pk)` for `FO^⊥ = U^⊥ ∘ T` with fixed functions `G` and
domain-separated `H` ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.1,
Fig. 9): samples `m ← sampleMsg`, computes `c := Enc(pk, m; G(m))`, and outputs
`(c, H(false, m, c))`. -/
def encapsBot (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (pk : PK) : ProbComp (CT × K) := do
  let m ← S.sampleMsg
  let c := encT S.pke G pk m
  return (c, H (false, m, c))

/-- Explicit-rejection decapsulation `Decaps^⊥(pk, sk, c)` for `FO^⊥ = U^⊥ ∘ T`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.1, Fig. 9) with fixed
functions `G` and `H`: `decapsBotM` in the identity monad. It returns `some (H(false, m', c))`
when `decT` accepts `m'`, and `none` otherwise (`decapsBot_eq`). -/
def decapsBot [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT) : Option K :=
  S.decapsBotM (m := Id) G H pk sk c

/-- `decapsBot` returns `some (H(false, m', c))` when `decT` accepts `m'`, and `none` otherwise. -/
theorem decapsBot_eq [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT) :
    S.decapsBot G H pk sk c = (decT S.pke G pk sk c).map fun m' => H (false, m', c) :=
  rfl

/-- Honest recovery for `FO^⊥`: whenever `Dec(sk, Enc_1(pk, m)) = some m`, `decapsBot` returns
`some (H(false, m, Enc_1(pk, m)))`. -/
theorem decapsBot_encT_eq_some [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (pk : PK) (sk : SK) (m : M)
    (hdec : S.pke.dec sk (encT S.pke G pk m) = some m) :
    S.decapsBot G H pk sk (encT S.pke G pk m) = some (H (false, m, encT S.pke G pk m)) := by
  simp [decapsBot_eq, decT_encT_eq_some S.pke G pk sk m hdec]

theorem decapsBot_eq_none_of_decT_eq_none [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT)
    (hnone : decT S.pke G pk sk c = none) :
    S.decapsBot G H pk sk c = none := by
  simp [decapsBot_eq, hnone]

/-- Explicit rejection for `FO^⊥`: any tampered ciphertext failing the re-encryption check
decapsulates to `none`. -/
theorem decapsBot_eq_none_of_reencrypt_ne [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (pk : PK) (sk : SK) (c : CT)
    (hbad : ∀ m', S.pke.dec sk c = some m' → encT S.pke G pk m' ≠ c) :
    S.decapsBot G H pk sk c = none :=
  S.decapsBot_eq_none_of_decT_eq_none G H pk sk c
    (decT_eq_none_of_reencrypt_ne S.pke G pk sk c hbad)

/-- Key generation `Gen-notbot` for `FO-notbot = U-notbot ∘ T`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.2, Fig. 12): generates
`(pk, sk) ← pke.keyGen`, samples a secret seed `s ← sampleMsg`, and outputs
`(pk, ⟨sk, pk, s⟩)`. -/
def keyGenNotBot (S : Scheme PK SK M R CT K) : ProbComp (PK × ImplicitSK PK SK M) := do
  let (pk, sk) ← S.pke.keyGen
  let s ← S.sampleMsg
  return (pk, { sk := sk, pk := pk, fallback := s })

/-- Encapsulation `Encaps-notbot(pk)` for `FO-notbot = U-notbot ∘ T`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.2, Fig. 12), identical to
`encapsBot`. -/
def encapsNotBot (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (pk : PK) : ProbComp (CT × K) :=
  S.encapsBot G H pk

/-- Implicit-rejection decapsulation `Decaps-notbot(dk, c)` for the domain-separated variant of
`FO-notbot = U-notbot ∘ T` ([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §3.2.2,
Fig. 12) with fixed functions `G` and `H`: `decapsNotBotM` in the identity monad. It returns
`H(false, m', c)` when `decT` accepts `m'`, and the domain-separated pseudorandom fallback key
`H(true, dk.fallback, c)` otherwise (`decapsNotBot_eq`), where the `Bool` tag separates valid key
derivations from rejection evaluations, in place of HHK17's untagged `H(s, c)`. -/
def decapsNotBot [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT) : K :=
  S.decapsNotBotM (m := Id) G H dk c

/-- `decapsNotBot` returns `H(false, m', c)` when `decT` accepts `m'`, and the fallback key
`H(true, dk.fallback, c)` otherwise. -/
theorem decapsNotBot_eq [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT) :
    S.decapsNotBot G H dk c =
      (match decT S.pke G dk.pk dk.sk c with
      | some m' => H (false, m', c)
      | none => H (true, dk.fallback, c)) :=
  rfl

/-- Honest recovery for `FO-notbot`: whenever `Dec(dk.sk, Enc_1(dk.pk, m)) = some m`, the
re-encryption check passes and `decapsNotBot` outputs `H(false, m, Enc_1(dk.pk, m))`. -/
theorem decapsNotBot_encT_eq [DecidableEq CT] (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (m : M)
    (hdec : S.pke.dec dk.sk (encT S.pke G dk.pk m) = some m) :
    S.decapsNotBot G H dk (encT S.pke G dk.pk m) = H (false, m, encT S.pke G dk.pk m) := by
  simp [decapsNotBot_eq, decT_encT_eq_some S.pke G dk.pk dk.sk m hdec]

theorem decapsNotBot_of_decT_eq_none [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT)
    (hnone : decT S.pke G dk.pk dk.sk c = none) :
    S.decapsNotBot G H dk c = H (true, dk.fallback, c) := by
  simp [decapsNotBot_eq, hnone]

/-- Implicit pseudorandom rejection for `FO-notbot`: any tampered ciphertext failing the
re-encryption check decapsulates to `H(true, dk.fallback, c)`. -/
theorem decapsNotBot_of_reencrypt_ne [DecidableEq CT] (S : Scheme PK SK M R CT K)
    (G : M → R) (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT)
    (hbad : ∀ m', S.pke.dec dk.sk c = some m' → encT S.pke G dk.pk m' ≠ c) :
    S.decapsNotBot G H dk c = H (true, dk.fallback, c) :=
  S.decapsNotBot_of_decT_eq_none G H dk c
    (decT_eq_none_of_reencrypt_ne S.pke G dk.pk dk.sk c hbad)

end FixedOracles

/-! ### Pure oracles

With pure oracles `pure ∘ G` and `pure ∘ H` in any lawful monad, the oracle-access decapsulations
return the fixed-function ones. -/

section PureOracles

variable {PK SK M R CT K : Type} [DecidableEq CT] {m : Type → Type} [Monad m] [LawfulMonad m]

/-- With pure oracles, `decapsBotM` is the fixed-function decapsulation `decapsBot`. -/
@[simp] theorem decapsBotM_pure (S : Scheme PK SK M R CT K) (G : M → R) (H : Bool × M × CT → K)
    (pk : PK) (sk : SK) (c : CT) :
    S.decapsBotM (m := m) (pure ∘ G) (pure ∘ H) pk sk c = pure (S.decapsBot G H pk sk c) := by
  rw [decapsBot_eq]
  unfold decapsBotM
  rw [decTM_pure, pure_bind]
  cases decT S.pke G pk sk c <;> simp

/-- With pure oracles, `decapsNotBotM` is the fixed-function decapsulation `decapsNotBot`. -/
@[simp] theorem decapsNotBotM_pure (S : Scheme PK SK M R CT K) (G : M → R)
    (H : Bool × M × CT → K) (dk : ImplicitSK PK SK M) (c : CT) :
    S.decapsNotBotM (m := m) (pure ∘ G) (pure ∘ H) dk c = pure (S.decapsNotBot G H dk c) := by
  rw [decapsNotBot_eq]
  unfold decapsNotBotM
  rw [decTM_pure, pure_bind]
  cases decT S.pke G dk.pk dk.sk c <;> rfl

end PureOracles

end Scheme

end FujisakiOkamoto

end Cslib.Crypto.Protocols
