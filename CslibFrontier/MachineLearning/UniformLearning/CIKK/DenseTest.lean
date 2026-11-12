/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ModGates
public import CslibFrontier.Computability.Circuit.Boolean.NaturalProof
public import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.Crypto.Primitives.PRG.NisanWigderson.AmpGeneratorCircuit

/-!
# The CIKK learner from a test that rejects small constant-depth circuits

Carmosino, Impagliazzo, Kabanets and Kolokolova learn a circuit class `Λ` containing AC⁰[p] from a
natural property useful against `Λ` [Carmosino et al., Theorem 5.1, p. 10:19]
[CarmosinoImpagliazzoKabanetsKolokolova2016]. Their proof has two halves. The black-box generator
is efficient within `Λ`: every output `g_z` on the amplified target has a small `Λ`-circuit. Hence a
dense test that accepts no function with a small `Λ`-circuit rejects every `g_z`, which is the
hypothesis of the learner (`Cslib.MachineLearning.UniformLearning.learns_cikkLearner`).

This file states that step at one input length `ℓ` of the test, for `p = 2` and for every
constant-depth basis that contains AC⁰[2]: a signature `σ` with an interpretation `I` into which
`φ` translates the unbounded fan-in basis with `MOD₂` gates. Let `D` be a set of functions on `ℓ`
bits holding at least a `2 ^ (ℓ + 1 - g)` fraction of them, none computed by a `σ`-circuit of
depth at most `d + 7` and size at most `k s + 6 (k n + k)² + 3`, with `k = cikkK e g`. Then the
CIKK learner with the test `truthTableTest D` learns the functions on `n` bits computed by
`σ`-circuits of depth at most `d` and size at most `s`, with error `2^{-e}` and confidence
`1 - 2^{-h}` (`Cslib.MachineLearning.UniformLearning.learns_cikkLearner_of_hom`). The depth
overhead `7` and the size bound are those of the library's generator circuits
(`Cslib.Crypto.PRG.NisanWigderson.exists_circuit_generator_glAmp`).

The AC⁰[2] learner with the rank property
(`Cslib.MachineLearning.UniformLearning.learns_cikkLearner_rankTest`) is the instance
`σ = Unbounded.extSignature`, `φ = Signature.Hom.id _`. The form for fan-in-two De Morgan circuits
of bounded size is `CslibFrontier.MachineLearning.UniformLearning.CIKK.PPoly`.

Labels:
* **Per-length form.** The set `D` is one slice of a property, and the usefulness hypothesis is
  stated at the generator's depth and size at that length. Deriving it from
  `Cslib.Circuits.Boolean.NaturalProof.IsUseful` and choosing `ℓ` and `g` from the parameters of
  the target class is not done here.
* **Density.** `D` may have any density at least `2 ^ (ℓ + 1 - g)`, where Theorem 5.1 assumes
  largeness `1 / 5`, as for `learns_cikkLearner`.
* **Bases containing AC⁰[2].** Theorem 5.1 allows any class containing AC⁰[p] that is closed under
  the source's oracle substitution. Here the class is given by a basis, a depth bound and a size
  bound, and `p = 2`.
* **Queries, not time.** The learner's query count is certified
  (`Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_two_pow`); its running time is
  not.

## Main results

* `Cslib.MachineLearning.UniformLearning.learns_cikkLearner_of_hom`: the CIKK learner whose test
  accepts a dense set of functions without small `σ`-circuits learns small `σ`-circuits of bounded
  depth.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets, A. Kolokolova, *Learning algorithms from natural
  proofs*, Theorem 5.1 (p. 10:19)][CarmosinoImpagliazzoKabanetsKolokolova2016]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset Cslib.Circuits Cslib.Circuits.Boolean Cslib.Crypto.PRG Cslib.Crypto.PRG.NisanWigderson

variable {σ : Signature} {I : Interpretation σ Bool}

/-- **Learning from a test that rejects small constant-depth circuits** [Carmosino et al.,
Theorem 5.1, p. 10:19][CarmosinoImpagliazzoKabanetsKolokolova2016], for `p = 2`, at one input
length `ℓ` of the test. Let `φ` translate the unbounded fan-in basis with `MOD₂` gates into the
basis `σ`. Suppose `D` holds at least `2 ^ (2 ^ ℓ + ℓ + 1 - g)` functions on `ℓ` bits, none
computed by a `σ`-circuit of depth at most `d + 7` and size at most `k s + 6 (k n + k)² + 3`, with
`k = cikkK e g`. Then the CIKK learner with the test `truthTableTest D` learns the functions on `n`
bits computed by `σ`-circuits of depth at most `d` and size at most `s`, with error `2^{-e}` and
confidence `1 - 2^{-h}`. Only queries are certified, not running time. -/
theorem learns_cikkLearner_of_hom (φ : Unbounded.extSignature.Hom σ)
    [φ.Preserves (Unbounded.extInterpretation (modGate 2)) I] {n ℓ : ℕ} (d s e g h : ℕ)
    {D : Set (BooleanFunction ℓ)} (hdense : 2 ^ 2 ^ ℓ * 2 ^ (ℓ + 1) ≤ 2 ^ g * D.ncard)
    (huse : ∀ G : Circuit σ ℓ 1, G.depth ≤ d + 7 →
      G.size ≤ cikkK e g * s + 6 * (cikkK e g * n + cikkK e g) ^ 2 + 3 →
      ∀ F ∈ D, ¬ G.Computes I (single F)) :
    (cikkLearner n ℓ e g h (truthTableTest D)).Learns (cikkSeed n ℓ e g h)
      {f | ∃ C : Circuit σ n 1, C.Computes I (single f) ∧ C.depth ≤ d ∧ C.size ≤ s}
      (1 / 2 ^ e) (1 / 2 ^ h) := by
  refine learns_cikkLearner e g h (by rwa [card_filter_truthTableTest]) ?_
  rintro f ⟨C, hC, hCd, hCs⟩ z
  obtain ⟨G, hG, hGs, hGd⟩ := exists_circuit_generator_glAmp φ hC (cikkK e g) ℓ z
  rw [Bool.eq_false_iff, ne_eq, truthTableTest_eq_true_iff]
  exact fun hmem => huse G (hGd.trans (by omega)) (hGs.trans (by gcongr)) _ hmem hG

end Cslib.MachineLearning.UniformLearning
