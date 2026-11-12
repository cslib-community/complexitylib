/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.AmpGeneratorDeMorgan

/-!
# The CIKK learner from a test that rejects small circuits

Carmosino, Impagliazzo, Kabanets and Kolokolova learn a circuit class from a natural property
useful against it [Carmosino et al., Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016]. This file states the step from usefulness to the
hypothesis of the learner (`Cslib.MachineLearning.UniformLearning.learns_cikkLearner`) at one
input length `ℓ` of the test, for fan-in-two De Morgan circuits of bounded size, the class P/poly
measures.

Every function `g_z` of the generator on the amplified target has De Morgan circuit complexity at
most `cikkPPolyBound n ℓ e g s` when the target has complexity at most `s`
(`Cslib.Crypto.PRG.NisanWigderson.complexity_generator_glAmp_le`, with `k = cikkK e g`). So a test
that accepts at least a `2 ^ (ℓ + 1 - g)` fraction of the functions on `ℓ` bits, all of complexity
above that bound, rejects every `g_z`. The CIKK learner with that test then learns the functions on
`n` bits of complexity at most `s`, with error `2^{-e}` and confidence `1 - 2^{-h}`
(`Cslib.MachineLearning.UniformLearning.learns_cikkLearner_of_lt_complexity`).

The bound is named so that statements built on it, such as the choice of `ℓ` from a natural
property, do not change when it is tightened; `cikkPPolyBound_def` unfolds it. Its constants are
this library's and are not tight. The form for constant-depth bases containing AC⁰[2] is
`CslibFrontier.MachineLearning.UniformLearning.CIKK.DenseTest`.

Labels:
* **Per-length form.** The set `D` is one slice of a property, and the usefulness hypothesis is
  stated at the bound at that length. Deriving it from
  `Cslib.Circuits.Boolean.NaturalProof.IsUseful` and choosing `ℓ` and `g` is not done here.
* **Density.** `D` may have any density at least `2 ^ (ℓ + 1 - g)`, where Theorem 5.1 assumes
  largeness `1 / 5`, as for `learns_cikkLearner`.
* **Size only.** The target class is bounded by De Morgan circuit size, with no depth bound, and
  Theorem 5.1's class `Λ` is replaced by this one class.
* **Queries, not time.** The learner's query count is certified
  (`Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_two_pow`); its running time is
  not.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.cikkPPolyBound`: the De Morgan circuit size bound on the
  generator's functions.

## Main results

* `Cslib.MachineLearning.UniformLearning.learns_cikkLearner_of_lt_complexity`: the CIKK learner
  whose test accepts a dense set of functions of complexity above `cikkPPolyBound` learns the
  functions of complexity at most `s`.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*, Theorem 5.1 (p. 10:19)][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson

/-- The De Morgan circuit size `(2100 · 8)² (ℓ + k s + 6 (k n + k)² + 3 + 1) ^ 8`, with
`k = cikkK e g`, that bounds every function of the CIKK generator on `ℓ` bits for a target on `n`
bits of De Morgan circuit complexity at most `s`
(`Cslib.Crypto.PRG.NisanWigderson.complexity_generator_glAmp_le`). -/
def cikkPPolyBound (n ℓ e g s : ℕ) : ℕ :=
  (2100 * 8) ^ 2 * (ℓ + (cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3) + 1) ^ 8

/-- `cikkPPolyBound` unfolded. -/
theorem cikkPPolyBound_def (n ℓ e g s : ℕ) :
    cikkPPolyBound n ℓ e g s =
      (2100 * 8) ^ 2 * (ℓ + (cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3) + 1) ^ 8 := by
  rw [cikkPPolyBound]

/-- **Learning from a test that rejects small circuits** [Carmosino et al., Theorem 5.1,
p. 10:19][CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2` and fan-in-two De Morgan
circuits, at one input length `ℓ` of the test. Suppose `D` holds at least `2 ^ (2 ^ ℓ + ℓ + 1 - g)`
functions on `ℓ` bits, each of De Morgan circuit complexity above `cikkPPolyBound n ℓ e g s`. Then
the CIKK learner with the test `truthTableTest D` learns the functions on `n` bits of De Morgan
circuit complexity at most `s`, with error `2^{-e}` and confidence `1 - 2^{-h}`. Only queries are
certified, not running time. -/
theorem learns_cikkLearner_of_lt_complexity {n ℓ : ℕ} (s e g h : ℕ) {D : Set (BooleanFunction ℓ)}
    (hdense : 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ g * D.ncard)
    (huse : ∀ F ∈ D, cikkPPolyBound n ℓ e g s < complexity interpretation (single F)) :
    (cikkLearner n ℓ e g h (truthTableTest D)).Learns (cikkSeed n ℓ e g h)
      {f | complexity interpretation (single f) ≤ s} (1 / 2 ^ e) (1 / 2 ^ h) := by
  refine learns_cikkLearner e g h (by rwa [card_filter_truthTableTest]) ?_
  intro f hf z
  rw [Bool.eq_false_iff, ne_eq, truthTableTest_eq_true_iff]
  exact fun hmem => (huse _ hmem).not_ge (complexity_generator_glAmp_le hf (cikkK e g) ℓ z)

end Cslib.MachineLearning.UniformLearning
