/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Key encapsulation challenges

In the indistinguishability games for a key encapsulation mechanism (KEM), the challenger
generates a key pair, encapsulates a key under the public key, and gives the adversary the public
key, the challenge ciphertext and a challenge key: the encapsulated key or an independent random
key, depending on the hidden bit ([HofheinzHoevelmannsKiltz2017], Section 2.2, Definition 2.4).
`KEM.Challenge PK CT K` is that input, with named fields in place of a triple `PK × CT × K`.

## Main definitions

* `Cslib.Crypto.KEM.Challenge`: the public key, challenge ciphertext and challenge key given to a
  KEM adversary.

## References

* [D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*][HofheinzHoevelmannsKiltz2017] (IACR ePrint 2017/604, full version dated
  2 November 2021), Section 2.2, Definition 2.4.
-/

public section

namespace Cslib.Crypto

/-- The input of a KEM indistinguishability adversary ([HofheinzHoevelmannsKiltz2017],
Section 2.2, Definition 2.4): the public key, the challenge ciphertext and the challenge key. -/
structure KEM.Challenge (PK CT K : Type) where
  /-- The public key. -/
  pk : PK
  /-- The challenge ciphertext, an encapsulation under `pk`. -/
  ct : CT
  /-- The challenge key: the key encapsulated in `ct`, or an independent random key, depending on
  the challenge bit. -/
  key : K

end Cslib.Crypto
