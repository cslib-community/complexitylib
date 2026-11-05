/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Binary-size imperfect-randomness sharing

The Galois fields `GaloisField 2 b` instantiate the source-class separation for every `b ≥ 2`.
Thus the finite-field hypotheses are satisfiable at every message size, rather than an extra
assumption. The message, key, and share alphabets have respectively `2^b`, `2^(b+2)`, and
`2^(b+1)` elements. These are cardinal-size statements: a particular choice of bit-coordinate
bijections or a circuit implementation is not part of this result.

This is the information-theoretic endpoint of [Aggarwal2026], Theorem 1.1, Sections 3–3.2.

## Main results

* `binary_field_separation`: the explicit `GaloisField 2 b` source-class separation for every
  `b ≥ 2`, with exact alphabet cardinalities.

## References

* [D. Aggarwal, *Secret Sharing Despite Non-Extractable Randomness*][Aggarwal2026], Theorem 1.1.
-/

public section

open Cslib.Probability
open scoped Cslib.Probability.PMF

namespace Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness

open scoped Classical in
/-- Every binary message size at least two has a perfect source-class sharing scheme even though
no deterministic bit extractor has error below `1/6` on the whole source class. -/
theorem binary_field_separation (b : ℕ) (hb : 2 ≤ b) :
    let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
    Fintype.card (PaddedKey (GaloisField 2 b)) = 2 ^ (b + 2) ∧
      Fintype.card (Share (GaloisField 2 b)) = 2 ^ (b + 1) ∧
      ∃ α : GaloisField 2 b,
        (∀ m k, reconstruct α (paddedFirst m k) (paddedSecond α m k) = m) ∧
        (∀ T m m', (paddedSource T).map (paddedFirst m) =
          (paddedSource T).map (paddedFirst m') ∧
          (paddedSource T).map (paddedSecond α m) =
            (paddedSource T).map (paddedSecond α m')) ∧
        (∀ T : Finset (GaloisField 2 b), (b : ℝ) ≤ PMF.minEntropy (paddedSource T)) ∧
        (∀ ext : PaddedKey (GaloisField 2 b) → Bool, ∃ T, (1 : ℝ) / 6 ≤
          dist ((paddedSource T).map ext) (PMF.uniformOfFintype Bool)) := by
  classical
  let : Fintype (GaloisField 2 b) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 b) = 2 ^ b := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 b (by omega)]
  exact sharing_at_bit_size hb hcard

end Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness
