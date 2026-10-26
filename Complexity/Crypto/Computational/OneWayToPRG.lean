/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.OneWay
public import Complexity.Crypto.Computational.PseudorandomGenerator
import Complexity.Crypto.Computational.Pseudoentropy.Generator
import Complexity.Crypto.Computational.Pseudoentropy.OneWay
import Complexity.Crypto.Computational.Pseudoentropy.ThreeSource.Candidates
import Complexity.Tactic.PolyTime

/-!
# Pseudorandom generators from one-way functions

A general uniform one-way function gives a samplable pseudoentropy pair. Its inverse-polynomial
gap admits a polynomial entropy grid, and the pseudoentropy construction gives a deterministic
polynomial-time generator expanding every input by one bit. All security reductions are uniform
strict PPT, and no entropy estimate or nonuniform advice is an additional hypothesis.

## Main results

* `Cslib.Crypto.OneWay.exists_pseudorandomGenerator`: every uniform OWF implies a uniform PRG
  expanding every input by exactly one bit.

## References

* [J. Håstad, R. Impagliazzo, L. Levin, M. Luby,
  *A Pseudorandom Generator from Any One-Way Function*][HILL1999]: the original theorem.
* [T. Holenstein, *Pseudorandom Generators from One-Way Functions*][Holenstein2006], Sections 4–5:
  the construction followed here.

The matrix extractor and uniform length conversion preserve the polynomial guarantees;
we do not assert the paper's optimized seed-length exponent or practical efficiency.

Adapted from Crypto/Computational/OneWayToPRG.lean
on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed machine certificates and the
nonnegative game API.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Pseudoentropy Turing.MultiTapeTM

/-- Every uniform one-way function implies a uniform pseudorandom generator with one bit of
stretch at every seed length. The existence of a one-way function remains the sole assumption. -/
theorem OneWay.exists_pseudorandomGenerator {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ generator : List Bool → List Bool, PseudorandomGenerator generator (fun n => n + 1) := by
  obtain ⟨pair, hpair⟩ := hf.exists_pseudoentropyPair
  exact hpair.exists_pseudorandomGenerator (densityBound := fun n => 16 * (n + 7))
    (.of_tidy (by polytime)) (Filter.Eventually.of_forall EntropyGrid.four_steps_le_owf_gap)

end Cslib.Crypto
