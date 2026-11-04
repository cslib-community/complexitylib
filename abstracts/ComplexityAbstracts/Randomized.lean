/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract foundations)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.Computation
import Cslib.Probability.PMF

/-! # Randomized polynomial time and computational indistinguishability

A randomized algorithm is a deterministic polynomial-time evaluator supplied with polynomially
many independent fair bits. Its law on each input is the image of that coin tape. The evaluator,
the polynomial and the machine are fixed before the input, so the algorithm is uniform, and the
bound holds for every execution rather than in expectation.

Two ensembles indexed by a unary security parameter are computationally indistinguishable when
every such test, which receives the parameter and one sample, has negligible advantage: its
advantage multiplied by any fixed power of the parameter tends to zero.
-/

namespace ComplexityTests.Abstracts.Randomized

/-- Exactly `n` independent fair bits, as a word of length `n`. -/
noncomputable def uniformBits (n : ℕ) : PMF (List Bool) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → Bool)).map List.ofFn

/-- A uniformly strict polynomial-time probability law: one deterministic evaluator, supplied
with polynomially many independent fair bits, realizes every input's law exactly. Its time
includes reading the coin tape and writing the encoded output. Both evaluator and polynomial
are fixed before the input. This also bounds every execution, rather than its expectation. -/
def StrictPPT {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (law : α → PMF β) : Prop :=
  ∃ (c d : ℕ) (evaluate : α → List Bool → β),
    Computation.PolyTime (fun p : α × List Bool => evaluate p.1 p.2)
      (Encoding.encPair a Encoding.encBits) b ∧
    ∀ x, law x = (uniformBits (c * ((a x).length + 1) ^ d)).map (evaluate x)

/-- A nonnegative error is negligible if multiplication by every fixed power of the security
parameter still tends to zero. The threshold and decay bound may depend on the whole adversary. -/
def Negligible (ε : ℕ → NNReal) : Prop :=
  ∀ k : ℕ, Filter.Tendsto (fun n : ℕ => (n : NNReal) ^ k * ε n)
    Filter.atTop (nhds 0)

/-- Probability that a Boolean experiment returns true. -/
noncomputable def probability (p : PMF Bool) : NNReal := (p true).toNNReal

/-- Every one uniform strict PPT test has negligible distinguishing advantage.
The test receives the unary security parameter and a sample. `bind` samples the word and then runs
the test with independent coins; `nndist` is the absolute difference of success probabilities. -/
def Indistinguishable (X Y : ℕ → PMF (List Bool)) : Prop :=
  ∀ test : ℕ → List Bool → PMF Bool,
    StrictPPT (Encoding.encPair Encoding.encUnary Encoding.encBits) Encoding.encBool
      (fun p => test p.1 p.2) →
    Negligible (fun n => nndist
      (probability (do let sample ← X n; test n sample))
      (probability (do let sample ← Y n; test n sample)))

end ComplexityTests.Abstracts.Randomized

/--
info: abstract audit passed for `ComplexityTests.Abstracts.Randomized`:
6 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.Randomized allowing [
  ComplexityAbstracts.Encoding, ComplexityAbstracts.Computation
]
