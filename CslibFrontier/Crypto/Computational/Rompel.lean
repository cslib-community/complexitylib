/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.IndexedSignature.Counter
public import CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision
public import CslibFrontier.Crypto.Computational.TCRSignature.ManyTime

/-!
# Rompel's signature theorem: one-way functions and EUF-CMA digital signatures

Combining universal one-way hash families from inaccessible entropy with target collision-resistant
hash-and-sign and stateless PRF-seeded authentication trees establishes Rompel's equivalence between
uniform one-way functions (`OneWay`) and uniform stateless many-time EUF-CMA digital signature
schemes on both fixed `n`-bit messages (`SignatureScheme.EUFCMA`) and unrestricted `List Bool`
messages (`WordSignatureScheme.EUFCMA`):

1. **Sufficiency (`OneWay.exists_indexedEUFCMA_two`, `OneWay.exists_counterEUFCMA_two`,
   `OneWay.exists_eufCMA`, `OneWay.exists_wordEUFCMA`)**: any uniform `OneWay` function yields an
   unrestricted target collision-resistant `KeyedHashFamily` on `List Bool`
   (`OneWay.exists_targetCollisionResistant_keyedHashFamily`, following `[HHRVW2020]`, Sections
   4.2 and 5.1, Theorems 4.5 and 5.1, Lemmas 5.3–5.7, pp. 21–32). Pairing that hash family with
   Lamport's one-time signature scheme (`OneWay.exists_oneTimeSignature`, `[Lamport1979]`),
   fresh-key target collision-resistant hash-and-sign (`TCRSignature.scheme`, `[BonehShoup2023]`,
   Section 13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534), and index doubling
   (`IndexedSignatureScheme.double`, `[BonehShoup2023]`, Section 14.6.1, p. 597) gives a
   capacity-`2` `IndexedSignatureScheme` satisfying `IndexedEUFCMA` and `CounterEUFCMA` on
   arbitrary-length `List Bool` messages without assuming collision-resistant hashing. Upgrading
   via `TreeSignature` with GGM pseudorandom coins
   (`IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`, `[BonehShoup2023]`, Section
   14.6.3, Theorem 14.6, pp. 600–601; `[NaorYung1989]`, Section 4) produces a stateless many-time
   `SignatureScheme` satisfying `EUFCMA` on `n`-bit messages, and applying many-time fresh-key
   target collision-resistant hash-and-sign (`TCRSignature.wordScheme`,
   `SignatureScheme.EUFCMA.eufCMA_wordScheme`, `[BonehShoup2023]`, Section 13.2.1, Theorem 13.2,
   p. 534) lifts it to a stateless many-time `WordSignatureScheme` satisfying `EUFCMA` on all
   `List Bool` messages.
2. **Necessity and equivalence (`exists_oneWay_iff_exists_signature`,
   `exists_oneTimeSignature_iff_exists_signature`, `exists_oneWay_iff_exists_wordSignature`,
   `exists_oneTimeSignature_iff_exists_wordSignature`)**: converse reindexing of seeded key
   generation (`SignatureScheme.EUFCMA.exists_oneWay`, `WordSignatureScheme.EUFCMA.exists_oneWay`)
   closes both `(∃ f, OneWay f) ↔ ∃ S : SignatureScheme, S.EUFCMA` and
   `(∃ f, OneWay f) ↔ ∃ S : WordSignatureScheme, S.EUFCMA` (`[Rompel1990]`, pp. 387–394) and
   equates existence of one-time `SignatureScheme`s with stateless many-time `SignatureScheme`s and
   `WordSignatureScheme`s.

**Model and message-space boundary**: all algorithms and reductions are uniform strict PPT /
strict oracle-PPT multi-tape Turing machines (`IsPPTOn`, `IsOraclePPT`). `SignatureScheme` fixes
the message space at security parameter `n` to `n`-bit words (`msg.length = n`), whereas
`WordSignatureScheme` imposes no message-length restriction at any security parameter (`msg : List
Bool`), with strict oracle-PPT admissibility polynomially bounding the lengths of messages queried
and forged in each execution.

## Main results

* `Cslib.Crypto.OneWay.exists_indexedEUFCMA_two`: every uniform `OneWay` function yields a
  capacity-`2` `IndexedSignatureScheme` satisfying `IndexedEUFCMA` on arbitrary-length `List Bool`
  messages.
* `Cslib.Crypto.OneWay.exists_counterEUFCMA_two`: every uniform `OneWay` function yields a
  capacity-`2` `IndexedSignatureScheme` satisfying `CounterEUFCMA` on arbitrary-length `List Bool`
  messages.
* `Cslib.Crypto.OneWay.exists_eufCMA`: every uniform `OneWay` function yields a stateless many-time
  `SignatureScheme` satisfying `EUFCMA` on `n`-bit messages.
* `Cslib.Crypto.OneWay.exists_wordEUFCMA`: every uniform `OneWay` function yields a stateless
  many-time `WordSignatureScheme` satisfying `EUFCMA` on arbitrary-length `List Bool` messages.
* `Cslib.Crypto.exists_oneWay_iff_exists_signature`,
  `Cslib.Crypto.exists_oneTimeSignature_iff_exists_signature`: `OneWay` and `OneTimeEUFCMA`
  equivalences for `n`-bit `SignatureScheme`s.
* `Cslib.Crypto.exists_oneWay_iff_exists_wordSignature`,
  `Cslib.Crypto.exists_oneTimeSignature_iff_exists_wordSignature`: `OneWay` and `OneTimeEUFCMA`
  equivalences for unrestricted-message `WordSignatureScheme`s.

## References

* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990]
* [I. Haitner, T. Holenstein, O. Reingold, S. Vadhan, H. Wee, *Inaccessible Entropy II: IE
  Functions and Universal One-Way Hashing*, Sections 4.2 and 5.1, Theorems 4.5 and 5.1,
  pp. 21–32][HHRVW2020]
* [M. Naor, M. Yung, *Universal One-Way Hash Functions and their Cryptographic Applications*,
  Section 4][NaorYung1989]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Sections 13.2.1 and 14.6,
  pp. 533–534, 597–603][BonehShoup2023]
* [S. Goldwasser, S. Micali, R. L. Rivest, *A Digital Signature Scheme Secure Against Adaptive
  Chosen-Message Attacks*][GoldwasserMicaliRivest1988]
* [L. Lamport, *Constructing Digital Signatures from a One-Way Function*][Lamport1979]
-/

public section

namespace Cslib.Crypto

/-- **Capacity-`2` indexed signatures from any one-way function**: combining
`OneWay.exists_targetCollisionResistant_keyedHashFamily` (`[HHRVW2020]`, Theorem 5.1) with
`OneWay.exists_indexedEUFCMA_of_targetCollisionResistant` yields a capacity-`2`
`IndexedSignatureScheme` satisfying `IndexedEUFCMA` on arbitrary-length `List Bool` messages without
assuming collision-resistant hashing. -/
theorem OneWay.exists_indexedEUFCMA_two {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.IndexedEUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.exists_indexedEUFCMA_of_targetCollisionResistant hH

/-- **Capacity-`2` counter-stateful signatures from any one-way function**: every uniform `OneWay`
function yields a capacity-`2` `IndexedSignatureScheme` satisfying `CounterEUFCMA` on
arbitrary-length `List Bool` messages. -/
theorem OneWay.exists_counterEUFCMA_two {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : IndexedSignatureScheme, (∀ n, S.capacity n = 2) ∧ S.CounterEUFCMA := by
  obtain ⟨S, hcap, hS⟩ := hf.exists_indexedEUFCMA_two
  exact ⟨S, hcap, hS.counterEUFCMA⟩

/-- **Rompel sufficiency for `SignatureScheme`** (`[Rompel1990]`, pp. 387–394; proved via
`[HHRVW2020]`, Sections 4.2 and 5.1, Theorems 4.5 and 5.1, and `[BonehShoup2023]`, Sections 13.2.1
and 14.6.3): every uniform `OneWay` function implies the existence of a stateless many-time
`SignatureScheme` satisfying `EUFCMA` (on `SignatureScheme`'s `n`-bit message space at security
parameter `n`). -/
theorem OneWay.exists_eufCMA {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : SignatureScheme, S.EUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.exists_eufCMA_of_targetCollisionResistant hH

/-- **Rompel's equivalence for `SignatureScheme`** (`[Rompel1990]`, pp. 387–394): a uniform one-way
function exists if and only if a uniform stateless many-time `EUFCMA`-secure `SignatureScheme` (on
`n`-bit messages at parameter `n`) exists. -/
theorem exists_oneWay_iff_exists_signature :
    (∃ f, OneWay f) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  ⟨fun ⟨_, hf⟩ => hf.exists_eufCMA, fun ⟨_, hS⟩ => hS.exists_oneWay⟩

/-- **Equivalence between one-time and stateless many-time `SignatureScheme`s**: a one-time EUF-CMA
secure `SignatureScheme` exists if and only if a stateless many-time EUF-CMA secure
`SignatureScheme` exists. -/
theorem exists_oneTimeSignature_iff_exists_signature :
    (∃ S : SignatureScheme, S.OneTimeEUFCMA) ↔ ∃ S : SignatureScheme, S.EUFCMA :=
  exists_oneWay_iff_exists_oneTimeSignature.symm.trans exists_oneWay_iff_exists_signature

/-- **Rompel sufficiency for `WordSignatureScheme`** (`[Rompel1990]`, pp. 387–394; proved via
`[HHRVW2020]`, Sections 4.2 and 5.1, Theorems 4.5 and 5.1, and `[BonehShoup2023]`, Sections 13.2.1
and 14.6.3): every uniform `OneWay` function implies the existence of a stateless many-time
`WordSignatureScheme` satisfying `EUFCMA` on arbitrary-length `List Bool` messages. -/
theorem OneWay.exists_wordEUFCMA {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ S : WordSignatureScheme, S.EUFCMA := by
  obtain ⟨H, hH⟩ := hf.exists_targetCollisionResistant_keyedHashFamily
  exact hf.exists_wordEUFCMA_of_targetCollisionResistant hH

/-- **Rompel's equivalence for `WordSignatureScheme`** (`[Rompel1990]`, pp. 387–394): a uniform
one-way function exists if and only if a uniform stateless many-time `EUFCMA`-secure
`WordSignatureScheme` on arbitrary-length `List Bool` messages exists. -/
theorem exists_oneWay_iff_exists_wordSignature :
    (∃ f, OneWay f) ↔ ∃ S : WordSignatureScheme, S.EUFCMA :=
  ⟨fun ⟨_, hf⟩ => hf.exists_wordEUFCMA, fun ⟨_, hS⟩ => hS.exists_oneWay⟩

/-- **Equivalence between one-time `SignatureScheme`s and stateless many-time
`WordSignatureScheme`s**: a one-time EUF-CMA secure `SignatureScheme` exists if and only if a
stateless many-time EUF-CMA secure `WordSignatureScheme` on arbitrary-length `List Bool` messages
exists. -/
theorem exists_oneTimeSignature_iff_exists_wordSignature :
    (∃ S : SignatureScheme, S.OneTimeEUFCMA) ↔ ∃ S : WordSignatureScheme, S.EUFCMA :=
  exists_oneWay_iff_exists_oneTimeSignature.symm.trans exists_oneWay_iff_exists_wordSignature

end Cslib.Crypto
