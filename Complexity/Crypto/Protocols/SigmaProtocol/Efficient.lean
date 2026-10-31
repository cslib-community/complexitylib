/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Basic
public import Complexity.Computability.Interactive.Security
public import Complexity.Computability.Probabilistic.PPT

/-!
# Efficient special soundness and special HVZK

`SigmaProtocol.SpecialSoundness` and `SigmaProtocol.SpecialHVZK` name their extractor and
simulator but accept arbitrary functions and distributions. Boneh and Shoup require an efficient
deterministic extractor (Definition 19.4) and an efficient probabilistic simulator
(Definition 19.5). Without that requirement the notions say little: a Sigma protocol has some
extractor exactly when two accepting conversations with a common commitment and distinct
challenges certify that the statement has a witness, and for a relation in which every statement
has exactly one witness, even the protocol that reveals its witness is special HVZK (test module
`ComplexityTests.UnboundedSimulators`). This module adds the efficient variants; the test module
`ComplexityTests.EfficientSimulators` shows that, under the discrete-logarithm assumption, they
rule out both examples.

Efficiency is uniform over a family `P i` of Sigma protocols indexed by `i : I`, typically a
unary security parameter together with a system parameter such as a group description
([BonehShoup2023], Definition 2.9). The types of statements, commitments, challenges and responses
may depend on the index, so the algorithms are certified on words, through the encodings
collected in a `SigmaProtocol.Encoding`.

* `EfficientSpecialSoundness P R enc encW extract`: at every index `extract i` is a witness
  extractor, and one deterministic polynomial-time function of words computes the whole family
  (`ExtractorRealizedBy`).
* `EfficientSpecialHVZK P R enc simulate δ`: at every index `simulate i` is a perfect simulator,
  and one uniform strict PPT program realizes the whole family on words up to statistical
  distance `δ i` (`SimulatorRealizedBy`). The error is needed because a strict PPT machine has a
  fixed clock and only fair coins, so it cannot sample `ZMod q` exactly when `q` is not a power
  of two; with `ProbComp.sampleModNat` the error is exponentially small. Boneh and Shoup's
  efficient algorithms (Definition 2.8) may instead exceed their time bound with negligible
  probability, which permits exact rejection sampling.

Both variants contain the exact property at every index with the same extractor or simulator, so
every theorem about `SpecialSoundness` and `SpecialHVZK` applies to them. The realizing program of
an efficient simulator is `δ i`-close to honest transcripts
(`SimulatorRealizedBy.closeTo_transcript`) and outputs an accepting conversation except with
probability `δ i` (`SimulatorRealizedBy.one_sub_le_accepts`), which relaxes Definition 19.5 (i).
Computational special HVZK ([BonehShoup2023], Definition 20.6) is a further relaxation that is not
defined here.

## Main definitions

* `SigmaProtocol.Encoding`: word encodings of an indexed family of Sigma protocols.
* `SigmaProtocol.ExtractorRealizedBy`, `SigmaProtocol.SimulatorRealizedBy`: a word function or
  program computes an extractor or simulator family on encodings.
* `SigmaProtocol.EfficientSpecialSoundness`: special soundness with a polynomial-time extractor.
* `SigmaProtocol.EfficientSpecialHVZK`: special HVZK with a strict PPT simulator, up to `δ`.

## Main results

* `SigmaProtocol.SimulatorRealizedBy.closeTo_transcript`: the realizing program is `δ i`-close to
  the honest prover's commitment and response at every challenge.
* `SigmaProtocol.SimulatorRealizedBy.one_sub_le_accepts`: the realizing program outputs an
  accepting conversation with probability at least `1 - δ i`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Definitions 2.8, 2.9, 19.4, 19.5 and 20.6.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM Interactive
open scoped ENNReal

/-- Word encodings for a family of Sigma protocols indexed by `I`, with statements in `Y i`,
commitments in `T i`, challenges in `C i` and responses in `Z i` at the index `i`. -/
structure Encoding (I : Type) (Y T C Z : I → Type) where
  /-- The index, such as a unary security parameter with a system parameter. -/
  index : I ↪ List Bool
  /-- The statements at each index. -/
  statement : ∀ i, Y i ↪ List Bool
  /-- The commitments at each index. -/
  commitment : ∀ i, T i ↪ List Bool
  /-- The challenges at each index. -/
  challenge : ∀ i, C i ↪ List Bool
  /-- The responses at each index. -/
  response : ∀ i, Z i ↪ List Bool

variable {I : Type} {X Y T C Z W : I → Type}

/-- The word function `f` computes the extractor family `extract` on encodings: from the index,
the encoded statement and the encoded conversations `(t, c, z)` and `(t, c', z')`, it returns the
encoded witness. -/
def ExtractorRealizedBy (enc : Encoding I Y T C Z) (encW : ∀ i, W i ↪ List Bool)
    (extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i)
    (f : I × List Bool × List Bool × List Bool × List Bool × List Bool × List Bool → List Bool) :
    Prop :=
  ∀ i y t c z c' z', f (i, enc.statement i y, enc.commitment i t, enc.challenge i c,
    enc.response i z, enc.challenge i c', enc.response i z') = encW i (extract i y t c z c' z')

/-- The program `program` realizes the simulator family `simulate` on encodings up to statistical
distance `δ`: on the index, the encoded statement and the encoded challenge, its output is within
`δ i` of the encoded commitment and response sampled by `simulate i`. -/
def SimulatorRealizedBy (enc : Encoding I Y T C Z) (simulate : ∀ i, Y i → C i → PMF (T i × Z i))
    (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)) (δ : I → ℝ≥0∞) :
    Prop :=
  ∀ i y c, CloseTo ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i)))
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i)

/-- **Efficient special soundness** ([BonehShoup2023], Definition 19.4). At every index,
`extract i` is a witness extractor for `P i`, and one deterministic polynomial-time function of the
index and words computes the whole family on encodings. As in `SpecialSoundness`, the extracted
witness has a type `W i` and a relation `R i` of its own. -/
structure EfficientSpecialSoundness (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, W i → Y i → Prop) (enc : Encoding I Y T C Z) (encW : ∀ i, W i ↪ List Bool)
    (extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i) : Prop where
  /-- `extract i` is a witness extractor at every index. -/
  specialSoundness : ∀ i, (P i).SpecialSoundness (R i) (extract i)
  /-- One polynomial-time word function computes the extractor family. -/
  polyTime : ∃ f, ComputableInPolyTime f (encPair enc.index (encPair encBits (encPair encBits
    (encPair encBits (encPair encBits (encPair encBits encBits)))))) encBits ∧
    ExtractorRealizedBy enc encW extract f

/-- **Efficient special HVZK** ([BonehShoup2023], Definition 19.5), up to a statistical error
`δ`. At every index, `simulate i` is a perfect special HVZK simulator for `P i`, and one uniform
strict PPT program of the index and words realizes the whole family up to `δ`, for every
statement and challenge. -/
structure EfficientSpecialHVZK (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, X i → Y i → Prop) (enc : Encoding I Y T C Z)
    (simulate : ∀ i, Y i → C i → PMF (T i × Z i)) (δ : I → ℝ≥0∞) : Prop where
  /-- `simulate i` is a perfect special HVZK simulator at every index. -/
  specialHVZK : ∀ i, (P i).SpecialHVZK (R i) (simulate i)
  /-- One uniform strict PPT program realizes the simulator family up to `δ`. -/
  realized : ∃ program, IsPPTOn (encPair enc.index (encPair encBits encBits))
    (encPair encBits encBits) program ∧ SimulatorRealizedBy enc simulate program δ

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {R : ∀ i, X i → Y i → Prop}
  {enc : Encoding I Y T C Z} {simulate : ∀ i, Y i → C i → PMF (T i × Z i)}
  {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)} {δ : I → ℝ≥0∞}

/-- A program realizing a perfect simulator is `δ i`-close to the honest prover's encoded
commitment and response, for every witness-statement pair and every challenge. -/
theorem SimulatorRealizedBy.closeTo_transcript (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy enc simulate program δ) {i : I} {x : X i} {y : Y i} (hxy : R i x y)
    (c : C i) :
    CloseTo (((P i).transcript x y c).map (Prod.map (enc.commitment i) (enc.response i)))
      (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i) := by
  rw [← (hS i).transcript_eq x y hxy c]
  exact h i y c

/-- A program realizing a perfect simulator outputs an encoded accepting conversation with
probability at least `1 - δ i`, for every statement and challenge (a relaxation of
[BonehShoup2023], Definition 19.5 (i)). -/
theorem SimulatorRealizedBy.one_sub_le_accepts (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy enc simulate program δ) (i : I) (y : Y i) (c : C i) :
    1 - δ i ≤ (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))).toOuterMeasure
      {w | ∃ t z, w = (enc.commitment i t, enc.response i z) ∧ (P i).Accepts y t c z} := by
  have hone : ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i))).toOuterMeasure
      {w | ∃ t z, w = (enc.commitment i t, enc.response i z) ∧ (P i).Accepts y t c z} = 1 := by
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_eq_one_iff]
    exact fun tz htz => ⟨tz.1, tz.2, rfl, (hS i).accepts y c tz htz⟩
  exact tsub_le_iff_right.mpr (hone ▸ h i y c _)

end Cslib.Crypto.Protocols.SigmaProtocol
