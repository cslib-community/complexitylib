/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Security
public import Complexity.Computability.Probabilistic.PPT

/-!
# Efficient extractors and simulators for interactive reductions

`Interactive.Verifier.KnowledgeSound` and `Interactive.Reduction.HVZK` name their extractor and
simulator but place no efficiency requirement on them. Without one, knowledge soundness says no
more than soundness, and HVZK says no more than honest-verifier witness indistinguishability
(test modules `ComplexityTests.InteractiveKnowledgeSound` and
`ComplexityTests.UnboundedSimulators`). This module adds the efficient variants.

Efficiency is uniform over a family of reductions indexed by `i : I`, typically a unary security
parameter together with a system parameter. Statements, witnesses and protocol shapes may depend
on the index, so the algorithms are certified on words, through the encodings collected in an
`Interactive.Encoding`.

* `Verifier.EfficientKnowledgeSound V relIn relOut enc encOut encIn E ε`: at every index `E i` is
  a straight-line extractor with error `ε i`, and one deterministic polynomial-time function of
  words computes the whole family (`ExtractorRealizedBy`).
* `Reduction.EfficientHVZK R rel enc Sim ε δ`: at every index `Sim i` is an `ε i`-HVZK simulator,
  and one uniform strict PPT program realizes the whole family on encoded transcripts up to
  statistical distance `δ i` (`SimulatorRealizedBy`). A typed simulator may sample from
  distributions, such as uniform field elements, that a strict PPT machine with fair coins
  samples only approximately; `δ` accounts for that.

Both variants contain the exact property at every index with the same extractor or simulator, so
every theorem about `KnowledgeSound` and `HVZK` applies to them; the realizing program of an
efficient simulator is `ε i + δ i`-close to honest transcripts
(`SimulatorRealizedBy.closeTo_run`). Extraction here is straight-line, from the transcript, as for
interactive oracle proofs; rewinding extractors in the sense of Bellare and Goldreich are a
different notion, as are malicious-verifier zero knowledge and computational zero knowledge.

## Main definitions

* `Interactive.Encoding`: word encodings of an indexed family of reductions.
* `Interactive.ExtractorRealizedBy`, `Interactive.SimulatorRealizedBy`: a word function or program
  computes an extractor or simulator family on encodings.
* `Interactive.Verifier.EfficientKnowledgeSound`: knowledge soundness with a polynomial-time
  extractor.
* `Interactive.Reduction.EfficientHVZK`: HVZK with a strict PPT simulator, up to `δ`.

## Main results

* `Interactive.SimulatorRealizedBy.closeTo_run`: the realizing program of an efficient simulator
  is `ε i + δ i`-close to the honest encoded transcript.
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec Probability Turing.MultiTapeTM

/-- Word encodings for a family of reductions indexed by `I`, with rounds `s i` and input
statements in `Stmt i` at the index `i`. -/
structure Encoding (I : Type) (s : I → Spec) (Stmt : I → Type) where
  /-- The index, such as a unary security parameter with a system parameter. -/
  index : I ↪ List Bool
  /-- The input statements at each index. -/
  statement : ∀ i, Stmt i ↪ List Bool
  /-- The transcripts at each index. -/
  transcript : ∀ i, Transcript (s i) ↪ List Bool

variable {I : Type} {s : I → Spec} {StmtIn WitIn StmtOut WitOut : I → Type}

/-- The word function `f` computes the extractor family `E` on encodings: from the index, the
encoded statement, the encoded transcript and the encoded output witness, it returns the encoded
input witness. -/
def ExtractorRealizedBy (enc : Encoding I s StmtIn) (encOut : ∀ i, WitOut i ↪ List Bool)
    (encIn : ∀ i, WitIn i ↪ List Bool) (E : ∀ i, StmtIn i → Transcript (s i) → WitOut i → WitIn i)
    (f : I × List Bool × List Bool × List Bool → List Bool) : Prop :=
  ∀ i x τ w, f (i, enc.statement i x, enc.transcript i τ, encOut i w) = encIn i (E i x τ w)

/-- The program `program` realizes the simulator family `Sim` on encodings up to statistical
distance `δ`: on the index and the encoded statement, its output is within `δ i` of the encoded
transcript sampled by `Sim i`. -/
def SimulatorRealizedBy (enc : Encoding I s StmtIn)
    (Sim : ∀ i, StmtIn i → ProbComp (Transcript (s i)))
    (program : I × List Bool → ProbComp (List Bool)) (δ : I → ℝ≥0∞) : Prop :=
  ∀ i x, CloseTo ((ProbComp.eval (Sim i x)).map (enc.transcript i))
    (ProbComp.eval (program (i, enc.statement i x))) (δ i)

/-- **Efficient straight-line knowledge soundness.** At every index, `E i` is a straight-line
extractor for `V i` with error `ε i`, in the plain model, and one deterministic polynomial-time
function of the index and words computes the whole family on encodings. -/
structure Verifier.EfficientKnowledgeSound
    (V : ∀ i, Verifier OracleSpec.empty (s i) (StmtIn i) (StmtOut i))
    (relIn : ∀ i, StmtIn i → WitIn i → Prop) (relOut : ∀ i, StmtOut i → WitOut i → Prop)
    (enc : Encoding I s StmtIn) (encOut : ∀ i, WitOut i ↪ List Bool)
    (encIn : ∀ i, WitIn i ↪ List Bool) (E : ∀ i, StmtIn i → Transcript (s i) → WitOut i → WitIn i)
    (ε : I → ℝ≥0∞) : Prop where
  /-- `E i` is a straight-line extractor with error `ε i` at every index. -/
  knowledgeSound : ∀ i, (V i).KnowledgeSound (relIn i) (relOut i) (E i) (ε i)
  /-- One polynomial-time word function computes the extractor family. -/
  polyTime : ∃ f, ComputableInPolyTime f
    (encPair enc.index (encPair encBits (encPair encBits encBits))) encBits ∧
    ExtractorRealizedBy enc encOut encIn E f

/-- **Efficient honest-verifier zero knowledge**, with simulation error `ε` and realization error
`δ`. At every index, `Sim i` is an `ε i`-HVZK simulator for `R i`, in the plain model, and one
uniform strict PPT program of the index and the encoded statement realizes the whole family on
encoded transcripts up to `δ`. -/
structure Reduction.EfficientHVZK
    (R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (s i) (StmtIn i) (WitIn i) (StmtOut i)
      (WitOut i))
    (rel : ∀ i, StmtIn i → WitIn i → Prop) (enc : Encoding I s StmtIn)
    (Sim : ∀ i, StmtIn i → ProbComp (Transcript (s i))) (ε δ : I → ℝ≥0∞) : Prop where
  /-- `Sim i` is an `ε i`-HVZK simulator at every index. -/
  hvzk : ∀ i, (R i).HVZK (rel i) (Sim i) (ε i)
  /-- One uniform strict PPT program realizes the simulator family up to `δ`. -/
  realized : ∃ program, IsPPTOn (encPair enc.index encBits) encBits program ∧
    SimulatorRealizedBy enc Sim program δ

/-- A program realizing an `ε`-HVZK simulator up to `δ` is `ε i + δ i`-close to the honest encoded
transcript, for every statement and valid witness. -/
theorem SimulatorRealizedBy.closeTo_run
    {R : ∀ i, Reduction OracleSpec.empty OracleSpec.empty (s i) (StmtIn i) (WitIn i) (StmtOut i)
      (WitOut i)}
    {rel : ∀ i, StmtIn i → WitIn i → Prop} {enc : Encoding I s StmtIn}
    {Sim : ∀ i, StmtIn i → ProbComp (Transcript (s i))}
    {program : I × List Bool → ProbComp (List Bool)} {ε δ : I → ℝ≥0∞}
    (hzk : ∀ i, (R i).HVZK (rel i) (Sim i) (ε i)) (h : SimulatorRealizedBy enc Sim program δ)
    {i : I} {x : StmtIn i} {w : WitIn i} (hxw : rel i x w) :
    CloseTo (((World.plain.eval ((R i).run x w)).map Prod.fst).map (enc.transcript i))
      (ProbComp.eval (program (i, enc.statement i x))) (ε i + δ i) :=
  ((hzk i x w hxw).map (enc.transcript i)).trans (h i x)

end Cslib.Interactive
