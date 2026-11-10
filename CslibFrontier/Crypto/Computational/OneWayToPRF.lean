/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Computational.GGM.Security

/-!
# Pseudorandom functions from one-way functions

Combine the general OWF-to-PRG theorem with the GGM construction. The conclusion includes an
efficient deterministic evaluator and security against uniform adaptive oracle PPT adversaries.
Existence of the one-way function is the sole cryptographic assumption.

## Main results

* `Cslib.Crypto.OneWay.exists_pseudorandomFunction`: every uniform OWF implies an adaptive PRF.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Sections 4–5.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986],
  Sections 3.2–3.3.

Adapted from Crypto/Computational/OneWayToPRF.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability

/-- Every uniform one-way function implies a uniform pseudorandom function secure against
adaptive, strict polynomial-time oracle adversaries. -/
theorem OneWay.exists_pseudorandomFunction {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ family : List Bool → List Bool → List Bool, PseudorandomFunction family := by
  obtain ⟨generator, hgenerator⟩ := hf.exists_pseudorandomGenerator
  exact hgenerator.exists_pseudorandomFunction

end Cslib.Crypto
