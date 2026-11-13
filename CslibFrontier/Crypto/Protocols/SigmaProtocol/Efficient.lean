/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Basic
public import CslibFrontier.Computability.Interactive.Security
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.PPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.PPT.Extension

/-!
# Efficient special soundness and special HVZK

`SigmaProtocol.SpecialSoundness` and `SigmaProtocol.SpecialHVZK` name their extractor and
simulator but accept arbitrary functions and distributions. Boneh and Shoup require an efficient
deterministic extractor (Definition 19.4) and an efficient probabilistic simulator
(Definition 19.5). Without that requirement the notions say little: a Sigma protocol has some
extractor exactly when two accepting conversations with a common commitment and distinct
challenges certify that the statement has a witness, and for a relation in which every statement
has exactly one witness, even the protocol that reveals its witness is special HVZK (test module
`CslibFrontierTests.UnboundedSimulators`). This module adds the efficient variants; the test module
`CslibFrontierTests.EfficientSimulators` shows that, under the discrete-logarithm assumption, they
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
  and one typed simulator family `sim : Simulator I Y T C Z` is uniform strict PPT
  (`Simulator.IsPPT`) and within statistical distance `δ i` of `simulate i`
  (`SimulatorRealizedBy`). The simulator takes and returns typed values; encodings appear only in
  `Simulator.IsPPT`, which reads the record `SimulatorInput` of the index, the statement and the
  challenge and writes the encoded commitment and response. The error is needed because a strict
  PPT machine has a fixed clock and only fair coins, so it cannot sample `ZMod q` exactly when `q`
  is not a power of two; with `ProbComp.sampleModNat` the error is exponentially small. Boneh and
  Shoup's efficient algorithms (Definition 2.8) may instead exceed their time bound with negligible
  probability, which permits exact rejection sampling.

Both variants contain the exact property at every index with the same extractor or simulator, so
every theorem about `SpecialSoundness` and `SpecialHVZK` applies to them. An efficient simulator is
`δ i`-close to honest transcripts (`SimulatorRealizedBy.closeTo_transcript`) and outputs an
accepting conversation except with probability `δ i` (`SimulatorRealizedBy.one_sub_le_accepts`),
which relaxes Definition 19.5 (i). A simulator certified by `Simulator.IsPPT` is computed on words
by a uniform strict PPT program that agrees with it on every encoded input
(`Simulator.IsPPT.exists_word`), and conversely a word program that agrees with a typed simulator
certifies it (`Simulator.IsPPT.of_word`). Note that `δ` in `EfficientSpecialHVZK` is an
unconstrained parameter of the predicate rather than a bundled `Negligible` condition: at `δ i ≥ 1`
(since event probabilities are at most `1`), `SimulatorRealizedBy` holds trivially for every
simulator, reducing `EfficientSpecialHVZK` to the unbounded `SpecialHVZK` field
(`not_efficientSpecialHVZK_sendWitness` in `CslibFrontierTests.EfficientSimulators` requires
`δ i ≤ 1 / 2`). Computational special HVZK ([BonehShoup2023], Definition 20.6) is defined in
`CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational`
(`SigmaProtocol.ComputationalSpecialHVZK`); when `δ` is bounded along the setup distribution by a
negligible function, `EfficientSpecialHVZK.exists_computationalSpecialHVZK` derives it.

## Main definitions

* `SigmaProtocol.Encoding`: word encodings of an indexed family of Sigma protocols.
* `SigmaProtocol.SimulatorInput`, `SigmaProtocol.encSimulatorInput`: a simulator's input
  `(index, statement, challenge)` and its encoding.
* `SigmaProtocol.encSimulatorWordInput`: the encoding of a word simulator program's input
  `(index, statement word, challenge word)`.
* `SigmaProtocol.Simulator`, `SigmaProtocol.Simulator.IsPPT`: typed simulator families and their
  uniform strict PPT admissibility.
* `SigmaProtocol.ExtractorRealizedBy`: a word function computes an extractor family on encodings.
* `SigmaProtocol.SimulatorRealizedBy`: a typed simulator family is `δ`-close to a family of
  distributions.
* `SigmaProtocol.WordSimulatorRealizedBy`: a word program is `δ`-close to the encoded output of a
  family of distributions, the word-level form provided by `SimulatorRealizedBy.exists_word`.
* `SigmaProtocol.EfficientSpecialSoundness`: special soundness with a polynomial-time extractor.
* `SigmaProtocol.EfficientSpecialHVZK`: special HVZK with a strict PPT simulator, up to `δ`.

## Main results

* `SigmaProtocol.Simulator.IsPPT.of_word`, `SigmaProtocol.Simulator.IsPPT.exists_word`: a typed
  simulator is uniform strict PPT exactly when a uniform strict PPT word program computes it on
  encodings.
* `SigmaProtocol.SimulatorRealizedBy.closeTo_transcript`: an efficient simulator is `δ i`-close to
  the honest prover's commitment and response at every challenge.
* `SigmaProtocol.SimulatorRealizedBy.one_sub_le_accepts`: an efficient simulator outputs an
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

variable (I Y C) in
/-- The input of a special HVZK simulator: an index, a statement and a challenge at that index. -/
structure SimulatorInput where
  /-- The index. -/
  index : I
  /-- The statement. -/
  statement : Y index
  /-- The challenge. -/
  challenge : C index

/-- The encoding of a simulator's input: the index, then the words of the statement and the
challenge under `enc` at that index, each framed except the last (`encSimulatorInput_apply`). -/
enc_structure encSimulatorInput (enc : Encoding I Y T C Z) : SimulatorInput I Y C where
  index : enc.index,
  statement : (enc.statement index) using (enc.statement index).injective,
  challenge : (enc.challenge index) using (enc.challenge index).injective

variable (I Y T C Z) in
/-- A family of special HVZK simulators: at index `i`, a probabilistic program from a statement and
a challenge to a commitment and a response. `Simulator.IsPPT` states its efficiency on encodings. -/
abbrev Simulator : Type :=
  ∀ i, Y i → C i → ProbComp (T i × Z i)

/-- A simulator family is uniform strict PPT: one machine reads `encSimulatorInput enc` and writes
the encoded commitment and response, framing the commitment. -/
def Simulator.IsPPT (enc : Encoding I Y T C Z) (sim : Simulator I Y T C Z) : Prop :=
  IsPPTOn (encSimulatorInput enc) (encPair encBits encBits) fun s =>
    Prod.map (enc.commitment s.index) (enc.response s.index) <$>
      sim s.index s.statement s.challenge

/-- Input `(i, y, c)` of a word program computing a special HVZK simulator: the index `i` encoded by
`encI`, then the encoded statement and the encoded challenge as bit words. The index and the
statement are framed. -/
abbrev encSimulatorWordInput (encI : I ↪ List Bool) : I × List Bool × List Bool ↪ List Bool :=
  encPair encI (encPair encBits encBits)

/-- The word program `program` realizes the simulator family `simulate` on encodings up to
statistical distance `δ`: on the index, the encoded statement and the encoded challenge, its output
is within `δ i` of the encoded commitment and response sampled by `simulate i`. This is the
word-level form of `SimulatorRealizedBy` that `SimulatorRealizedBy.exists_word` provides. -/
def WordSimulatorRealizedBy (enc : Encoding I Y T C Z)
    (simulate : ∀ i, Y i → C i → PMF (T i × Z i))
    (program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)) (δ : I → ℝ≥0∞) :
    Prop :=
  ∀ i y c, CloseTo ((simulate i y c).map (Prod.map (enc.commitment i) (enc.response i)))
    (ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) (δ i)

/-- A uniform strict PPT word program on the index and the encoded statement and challenge that
computes a typed program on encodings certifies the typed program. Its output type `β` and its
output encoding `out` are arbitrary, so this also certifies simulators with aborts. -/
theorem isPPTOn_encSimulatorInput_of_word {β : Type} {out : β ↪ List Bool}
    (enc : Encoding I Y T C Z) {typed : SimulatorInput I Y C → ProbComp β}
    {program : I × List Bool × List Bool → ProbComp β}
    (hprogram : IsPPTOn (encSimulatorWordInput enc.index) out program)
    (heq : ∀ s : SimulatorInput I Y C, ProbComp.eval (typed s) = ProbComp.eval
      (program (s.index, enc.statement s.index s.statement, enc.challenge s.index s.challenge))) :
    IsPPTOn (encSimulatorInput enc) out typed :=
  (hprogram.preprocess (prepare := fun s : SimulatorInput I Y C =>
      (s.index, enc.statement s.index s.statement, enc.challenge s.index s.challenge))
    (ComputableInPolyTime.of_eq fun _ => rfl)).congr fun s => (heq s).symm

/-- A uniform strict PPT word program that computes a typed simulator on encodings certifies it. -/
theorem Simulator.IsPPT.of_word {enc : Encoding I Y T C Z} {sim : Simulator I Y T C Z}
    {program : I × List Bool × List Bool → ProbComp (List Bool × List Bool)}
    (hprogram : IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program)
    (heq : ∀ i y c, (ProbComp.eval (sim i y c)).map (Prod.map (enc.commitment i) (enc.response i)) =
      ProbComp.eval (program (i, enc.statement i y, enc.challenge i c))) :
    Simulator.IsPPT enc sim :=
  isPPTOn_encSimulatorInput_of_word enc hprogram fun s => by
    rw [ProbComp.eval_map]
    exact heq s.index s.statement s.challenge

/-- A uniform strict PPT simulator family is computed on words by a uniform strict PPT program of
the index and arbitrary statement and challenge words, which agrees with it on every encoded
input. -/
theorem Simulator.IsPPT.exists_word {enc : Encoding I Y T C Z} {sim : Simulator I Y T C Z}
    (h : Simulator.IsPPT enc sim) :
    ∃ program : I × List Bool × List Bool → ProbComp (List Bool × List Bool),
      IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program ∧
      ∀ i y c, (ProbComp.eval (sim i y c)).map (Prod.map (enc.commitment i) (enc.response i)) =
        ProbComp.eval (program (i, enc.statement i y, enc.challenge i c)) := by
  obtain ⟨extension, hext, hagree⟩ := IsPPTOn.exists_extension h
    (decode := fun w => (unframe w, dropFrame w))
    (ComputableInPolyTime.unframe.prod ComputableInPolyTime.dropFrame)
    fun p => Prod.ext (unframe_encPair encBits encBits p.1 p.2)
      (dropFrame_encPair encBits encBits p.1 p.2)
  refine ⟨fun p => extension (encSimulatorWordInput enc.index p),
    hext.preprocess (ComputableInPolyTime.of_eq fun _ => rfl), fun i y c => ?_⟩
  rw [← ProbComp.eval_map]
  exact (hagree ⟨i, y, c⟩).symm

/-- The typed simulator family `sim` realizes the family of distributions `simulate` up to
statistical distance `δ`: on every statement and challenge at index `i`, its output law is within
`δ i` of `simulate i`. The outputs `O i` are commitment-response pairs for `EfficientSpecialHVZK`
and optional pairs for simulators with aborts. -/
def SimulatorRealizedBy {O : I → Type} (simulate : ∀ i, Y i → C i → PMF (O i))
    (sim : ∀ i, Y i → C i → ProbComp (O i)) (δ : I → ℝ≥0∞) : Prop :=
  ∀ i y c, CloseTo (simulate i y c) (ProbComp.eval (sim i y c)) (δ i)

/-- A uniform strict PPT simulator family within `δ` of `simulate` yields a uniform strict PPT word
program of the index and arbitrary statement and challenge words whose output on every encoded input
is within `δ i` of the encoded `simulate i`. -/
theorem SimulatorRealizedBy.exists_word {enc : Encoding I Y T C Z}
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}
    (h : SimulatorRealizedBy simulate sim δ) (hppt : Simulator.IsPPT enc sim) :
    ∃ program : I × List Bool × List Bool → ProbComp (List Bool × List Bool),
      IsPPTOn (encSimulatorWordInput enc.index) (encPair encBits encBits) program ∧
      WordSimulatorRealizedBy enc simulate program δ := by
  obtain ⟨program, hprogram, hword⟩ := hppt.exists_word
  refine ⟨program, hprogram, fun i y c => ?_⟩
  rw [← hword]
  exact (h i y c).map _

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
strict PPT simulator family realizes the whole family up to `δ`, for every statement and
challenge. -/
structure EfficientSpecialHVZK (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    (R : ∀ i, X i → Y i → Prop) (enc : Encoding I Y T C Z)
    (simulate : ∀ i, Y i → C i → PMF (T i × Z i)) (δ : I → ℝ≥0∞) : Prop where
  /-- `simulate i` is a perfect special HVZK simulator at every index. -/
  specialHVZK : ∀ i, (P i).SpecialHVZK (R i) (simulate i)
  /-- One uniform strict PPT simulator family realizes `simulate` up to `δ`. -/
  realized : ∃ sim : Simulator I Y T C Z, Simulator.IsPPT enc sim ∧
    SimulatorRealizedBy simulate sim δ

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {R : ∀ i, X i → Y i → Prop}
  {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}

/-- A simulator realizing a perfect simulator is `δ i`-close to the honest prover's commitment and
response, for every witness-statement pair and every challenge. -/
theorem SimulatorRealizedBy.closeTo_transcript (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ) {i : I} {x : X i} {y : Y i} (hxy : R i x y)
    (c : C i) :
    CloseTo ((P i).transcript x y c) (ProbComp.eval (sim i y c)) (δ i) := by
  rw [← (hS i).transcript_eq x y hxy c]
  exact h i y c

/-- A simulator realizing a perfect simulator outputs an accepting conversation with probability at
least `1 - δ i`, for every statement and challenge (a relaxation of [BonehShoup2023],
Definition 19.5 (i)). -/
theorem SimulatorRealizedBy.one_sub_le_accepts (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ) (i : I) (y : Y i) (c : C i) :
    1 - δ i ≤ (ProbComp.eval (sim i y c)).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2} := by
  have hone : (simulate i y c).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2} = 1 :=
    (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr fun tz htz => (hS i).accepts y c tz htz
  exact tsub_le_iff_right.mpr (hone ▸ h i y c _)

end Cslib.Crypto.Protocols.SigmaProtocol
