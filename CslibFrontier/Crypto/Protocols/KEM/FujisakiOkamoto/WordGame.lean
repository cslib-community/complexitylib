/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordReduction

/-!
# Random-oracle IND-CCA security of the word-level `FO-notbot` family

This module states random-oracle IND-CCA security for the word-level `FO-notbot` family of
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Word`, against the uniform strict oracle PPT
adversaries of `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordReduction`. It is the
IND-CCA game of [HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
2 November 2021), §2.2, Definition 2.4 / Figure 4, with random oracles `G` and `H`:

1. generate `(pk, dk)` with the native key generation `WordPKE.keyGenNotBot`;
2. run the native encapsulation `WordPKE.encaps` against lazily sampled random oracles, giving
   the challenge ciphertext `c*` and the real key `k₀*`;
3. draw an independent uniform key `k₁*` of length `keyLen n`;
4. give the adversary the challenge word `Encryption.encKEMChallenge (pk, k_b*, c*)` and the
   oracles `G`, `H` and decapsulation (`WordPKE.ccaWordOracle`), sharing the random oracles of
   step 2.

Decapsulation runs the native `WordPKE.decapsNotBot` against the same random oracles, and refuses
`c*` with the empty word.

**Domains of the random oracles.** `G` is a random function from messages of length `msgLen n`
to uniform words of length `coinLen n`. `H` is a random function from the canonical encodings
`encHQuery (b, m, c)` with `m` of length `msgLen n` and `c` of length at most `ctLen n`
(`WordPKE.isHQuery`) to uniform words of length `keyLen n`. A request outside these domains gets
the empty word and leaves the oracle unchanged (`WordPKE.roWordOracle`). The honest algorithms only
query inside the domains, except that encapsulation queries `H` at a ciphertext longer than
`ctLen n` when the PKE family produces one.

**Advantage.** `WordPKE.ROMINDCCA` asks that the two sides `b = false` and `b = true` be
indistinguishable for every uniform strict oracle PPT adversary. The two-world advantage is twice
the source's hidden-bit advantage `|Pr[b' = b] - 1/2|`.

This notion is FO-specific and local to this module, pending the generic KEM records of the
crypto readability program (#4817, I3 #4894). `WordPKE.INDCPA.romINDCCA` in
`CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.WordSecurity` derives `ROMINDCCA` from IND-CPA
security of the PKE family.

## Main definitions

* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.roWordOracle`,
  `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.withRO`: the lazily sampled random oracles
  `G` and `H` of the game, and a word program run against them.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.ccaWordOracle`: the adversary's oracles.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.romIndCcaGameWord`: the game.
* `Cslib.Crypto.Protocols.FujisakiOkamoto.WordPKE.ROMINDCCA`: random-oracle IND-CCA security.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), §2.2, Definition 2.4 / Figure 4.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.FujisakiOkamoto

open Probability Turing.MultiTapeTM

namespace WordPKE

variable (P : WordPKE) (keyLen : ℕ → ℕ)

/-- The lazily sampled random oracles of the word ROM game at parameter `n`, on caches of words.
`G` maps a message of length `msgLen n` to a uniform word of length `coinLen n`, and `H` maps a
request satisfying `isHQuery` to a uniform word of length `keyLen n`. Any other request gets the
empty word and leaves the caches unchanged. -/
noncomputable def roWordOracle (n : ℕ) (request : RO × List Bool) :
    StateT (ROCache (List Bool) (List Bool) (List Bool) (List Bool)) ProbComp (List Bool) :=
  fun st => match request with
  | (.G, m) =>
    if m.length = P.msgLen n then
      roHashG (CT := List Bool) (K := List Bool) (BitString.sampleList (P.coinLen n)) m st
    else pure ([], st)
  | (.H, w) =>
    if P.isHQuery n w then
      roHashH (M := List Bool) (R := List Bool) (BitString.sampleList (keyLen n))
        (hQueryDecoder.decode w) st
    else pure ([], st)

/-- Run a word program over the oracles `G` and `H` against the game's random oracles, keeping
their caches. -/
noncomputable def withRO (n : ℕ) {α : Type} (program : WordOracleComp RO α) :
    StateT (ROCache (List Bool) (List Bool) (List Bool) (List Bool)) ProbComp α :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k)) (P.roWordOracle keyLen n))
    program

/-- The oracles of the adversary in the word ROM game: `G` and `H` are the game's random oracles,
and decapsulation runs the native `decapsNotBot` with secret key `dk` against them, encoding its
answer with `encOption encBits`. Decapsulation of the challenge ciphertext `cStar` is refused with
the empty word. -/
noncomputable def ccaWordOracle (n : ℕ) (dk : ImplicitSK (List Bool) (List Bool) (List Bool))
    (cStar : List Bool) (request : CCAOp × List Bool) :
    StateT (ROCache (List Bool) (List Bool) (List Bool) (List Bool)) ProbComp (List Bool) :=
  match request with
  | (.G, m) => P.roWordOracle keyLen n (.G, m)
  | (.H, w) => P.roWordOracle keyLen n (.H, w)
  | (.decaps, c) =>
    if c = cStar then pure []
    else encOption encBits <$> P.withRO keyLen n (P.decapsNotBot keyLen n dk c)

/-- **The word ROM IND-CCA game** for `FO-notbot` at parameter `n` with challenge bit `b`
([HofheinzHoevelmannsKiltz2017], ePrint 2017/604 (2 Nov 2021), §2.2, Def. 2.4 / Fig. 4, with
random oracles `G` and `H`). Key generation is `keyGenNotBot`; the challenge `(c*, k₀*)` is
`encaps` against fresh lazy random oracles; `k₁*` is uniform of length `keyLen n`; and the
adversary `A` receives `encKEMChallenge (pk, k_b*, c*)` with the oracles `ccaWordOracle`, sharing
the random oracles of the challenge. -/
noncomputable def romIndCcaGameWord (A : ℕ → List Bool → WordOracleComp CCAOp Bool) (b : Bool)
    (n : ℕ) : ProbComp Bool := do
  let (pk, dk) ← P.keyGenNotBot keyLen n
  let ((cStar, kReal), st) ← (P.withRO keyLen n (P.encaps keyLen n pk)).run {}
  let kRand ← BitString.sampleList (keyLen n)
  let (guess, _) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (P.ccaWordOracle keyLen n dk cStar))
    (A n (Encryption.encKEMChallenge (pk, if b then kRand else kReal, cStar)))).run st
  return guess

/-- **Random-oracle IND-CCA security** of the word-level `FO-notbot` family: every uniform strict
oracle PPT adversary has negligible advantage between the two sides of `romIndCcaGameWord`. The
negligible bound may depend on the adversary, which is fixed before the parameter. -/
def ROMINDCCA : Prop :=
  Game.Indistinguishable
    (fun A n => ProbComp.eval (P.romIndCcaGameWord keyLen A false n))
    (fun A n => ProbComp.eval (P.romIndCcaGameWord keyLen A true n))
    (IsOraclePPT encBool)

end WordPKE

end Cslib.Crypto.Protocols.FujisakiOkamoto
