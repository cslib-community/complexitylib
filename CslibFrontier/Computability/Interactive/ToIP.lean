/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Interactive.Plain
public import CslibFrontier.Computability.Interactive.Efficient
public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Probability.StatisticalDistance.CloseTo
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event

/-!
# Bridge from Public-Coin Interactive Reductions to `IP`

A public-coin interactive protocol (`Cslib.Interactive.Verifier` and
`Cslib.Interactive.Reduction` in `World.plain`) exchanges typed prover messages `M` and public
verifier challenges `C` according to a round specification `s : Spec`. In contrast, the complexity
class `Cslib.Complexity.IP` runs a word-level oracle verifier (`WordOracleComp Unit Bool`)
against an arbitrary stateful, randomized bit-string prover (`Cslib.Complexity.Prover Unit`).

This module bridges the two models:

1. **Round codecs and adversarial decoding** (`ProverCodec`, `ChallengeCodec`, `RoundCodecs`):
   Each prover round specifies a bit-length cap `limit`, a partial parser
   `decode : List Bool → Option M`, and a fallback message `default : M`. Incoming prover bit
   strings are truncated to `limit` bits; any reply for which `decode` returns `none` marks the
   transcript invalid (causing the word-level verifier to reject) while substituting `default` in
   the typed transcript stub.
2. **Word-level verifier compilation** (`runWordRounds`, `Verifier.wordVerifierWith`,
   `Verifier.wordVerifier`):
   Compiles a typed `Interactive.Verifier` into a `WordOracleComp Unit Bool`.
3. **Completeness transfer** (`honestWordProver`, `Reduction.Complete.acceptProb_wordVerifier`):
   When the round codecs are lawful (`RoundCodecs.Lawful`), an honest typed prover compiles to a
   word-level prover with the exact same acceptance probability, transferring completeness error
   `ε_c` to word-level acceptance probability at least `1 - ε_c`.
4. **Soundness transfer against arbitrary stateful randomized provers**
   (`optimalTypedStrategy`, `Verifier.Sound.acceptProb_wordVerifier`):
   By backwards induction over the finite set `BitString.shortWords c.limit` of truncated bit
   replies in each prover round and public challenge conditioning in each verifier round, every
   stateful `PMF` word prover is bounded by an optimal plain-model typed `ProverStrategy`. Thus
   plain-model soundness with error `ε_s` implies word-level soundness with error `ε_s` against
   all `Cslib.Complexity.Prover Unit`.
5. **Statistical-distance stability and uniform `IP` membership**
   (`closeTo_runWordRounds`, `Verifier.isOraclePPTOn_wordVerifierWith`,
   `mem_IP_of_reduction_closeTo`, `Reduction.mem_IP`):
   Replacing ideal challenge samplers by `δ`-close distributions shifts word-level acceptance
   probabilities by at most `PerChallenge.sum s δ`, and polynomial-time round codecs plus challenge
   samplers yield `IsOraclePPTOn` and membership in `Cslib.Complexity.IP`.

## Main definitions

* `Cslib.Interactive.ProverCodec`, `Cslib.Interactive.ChallengeCodec`,
  `Cslib.Interactive.RoundCodecs`: per-round bit-word codecs with length bounds and fallback.
* `Cslib.Interactive.runWordRounds`: execute a typed round specification as a word-level
  oracle computation.
* `Cslib.Interactive.Verifier.wordVerifierWith`, `Cslib.Interactive.Verifier.wordVerifier`:
  compiled word-level `IP` verifier.
* `Cslib.Interactive.honestWordProver`: compile an honest typed prover strategy to
  `Cslib.Complexity.Prover Unit`.
* `Cslib.Interactive.optimalTypedStrategy`: optimal plain-model typed strategy bounding all
  word-level provers by backwards induction.
* `Cslib.Interactive.RoundEncodings`, `Cslib.Interactive.RoundCodecs.IsPolyTime`: uniform
  polynomial-time certificates for round codecs and challenge samplers.

## Main results

* `Cslib.Interactive.Reduction.Complete.acceptProb_wordVerifier`: completeness transfer from
  `Interactive.Reduction.Complete` to `Cslib.Complexity.acceptProb`.
* `Cslib.Interactive.Verifier.Sound.acceptProb_wordVerifier`: soundness transfer from
  `Interactive.Verifier.Sound` against arbitrary `Cslib.Complexity.Prover Unit`.
* `Cslib.Interactive.Reduction.isInteractiveProof_wordVerifier`: an interactive reduction for a
  relation induces an `IsInteractiveProof` for its language.
* `Cslib.Interactive.Verifier.isOraclePPTOn_wordVerifierWith`: uniform `IsOraclePPTOn`
  certificate for the compiled word verifier.
* `Cslib.Interactive.mem_IP_of_reduction_closeTo`, `Cslib.Interactive.Reduction.mem_IP`: a language
  admitting an efficient public-coin interactive reduction with completeness and soundness errors
  at most `1 / 3` lies in `IP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]
-/

public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec World Cslib.Complexity Probability Turing.MultiTapeTM

variable {Statement Witness OutStmt OutWit : Type}
variable {s : Spec}

/-! ### Round codecs and adversarial decoding -/

/-- A bounded bit-word codec for a prover-round message type `M`.
Honest messages are serialized by `encode`; raw prover replies are truncated to `limit` bits and
parsed by `decode`. Malformed replies (`decode w = none`) cause the word-level verifier to reject
while substituting `default` in the typed transcript stub. -/
structure ProverCodec (M : Type) where
  /-- Serialize a typed prover message as a bit word. -/
  encode : M → List Bool
  /-- Parse a truncated bit word into an optional typed message. -/
  decode : List Bool → Option M
  /-- Fallback message used in the transcript stub when `decode` returns `none`. -/
  default : M
  /-- Maximum number of bits read from a prover reply in this round. -/
  limit : ℕ

namespace ProverCodec

variable {M : Type}

/-- Total adversarial decoder obtained by falling back to `c.default` on `none`. -/
@[expose]
def decodeOrDefault (c : ProverCodec M) (w : List Bool) : M :=
  (c.decode w).getD c.default

/-- A prover codec is lawful when every honest message is recovered after truncation to `limit`
bits. -/
@[expose]
def Lawful (c : ProverCodec M) : Prop :=
  ∀ m : M, c.decode ((c.encode m).take c.limit) = some m

@[simp]
theorem decodeOrDefault_eq_of_decode_eq_some (c : ProverCodec M) {w : List Bool} {m : M}
    (h : c.decode w = some m) : c.decodeOrDefault w = m := by
  simp [decodeOrDefault, h]

@[simp]
theorem isSome_decode_take_encode {c : ProverCodec M} (h : c.Lawful) (m : M) :
    (c.decode ((c.encode m).take c.limit)).isSome = true := by
  rw [h m]; rfl

@[simp]
theorem decodeOrDefault_take_encode {c : ProverCodec M} (h : c.Lawful) (m : M) :
    c.decodeOrDefault ((c.encode m).take c.limit) = m := by
  rw [decodeOrDefault, h m]; rfl

/-- Build a prover codec from a total decoder that always succeeds. -/
@[expose]
def ofTotal (encode : M → List Bool) (decode : List Bool → M) (default : M) (limit : ℕ) :
    ProverCodec M where
  encode := encode
  decode w := some (decode w)
  default := default
  limit := limit

theorem lawful_ofTotal {encode : M → List Bool} {decode : List Bool → M} {default : M} {limit : ℕ}
    (h : ∀ m, decode ((encode m).take limit) = m) :
    (ofTotal encode decode default limit).Lawful := by
  intro m
  simp [ofTotal, h m]

/-- Build a prover codec from an injective bit-word encoding `enc` and a total `Decoder enc`. -/
@[expose]
def ofDecoder {enc : M ↪ List Bool} (D : Decoder enc) (default : M) (limit : ℕ) :
    ProverCodec M :=
  ofTotal enc D.decode default limit

theorem lawful_ofDecoder {enc : M ↪ List Bool} (D : Decoder enc) (default : M) {limit : ℕ}
    (hlen : ∀ m : M, (enc m).length ≤ limit) :
    (ofDecoder D default limit).Lawful :=
  lawful_ofTotal fun m => by rw [List.take_of_length_le (hlen m), D.decode_enc]

/-- Canonical codec for fixed-width bit strings `BitString n`. -/
@[expose]
def bitString (n : ℕ) : ProverCodec (BitString n) :=
  ofTotal List.ofFn (BitString.ofList n) (fun _ => false) n

theorem lawful_bitString (n : ℕ) : (bitString n).Lawful :=
  lawful_ofTotal fun m => by rw [List.take_of_length_le (by simp), BitString.ofList_ofFn]

/-- Canonical codec for raw bit lists of length at most `limit`. -/
@[expose]
def bits (limit : ℕ) : ProverCodec (List Bool) where
  encode := id
  decode w := if w.length ≤ limit then some w else none
  default := []
  limit := limit

theorem lawful_bits (limit : ℕ) {w : List Bool} (hw : w.length ≤ limit) :
    (bits limit).decode (((bits limit).encode w).take limit) = some w := by
  simp [bits, List.take_of_length_le hw, hw]

end ProverCodec

/-- A bit-word codec for a public verifier challenge type `C`. -/
structure ChallengeCodec (C : Type) where
  /-- Serialize a challenge so the word-level prover can read it from the query payload. -/
  encode : C → List Bool
  /-- Recover the challenge from its serialized bit word. -/
  decode : List Bool → C

namespace ChallengeCodec

variable {C : Type}

/-- A challenge codec is lawful when `decode` left-inverts `encode`. -/
@[expose]
def Lawful (c : ChallengeCodec C) : Prop :=
  ∀ ch : C, c.decode (c.encode ch) = ch

/-- Build a challenge codec from an injective bit-word encoding `enc` and a `Decoder enc`. -/
@[expose]
def ofDecoder {enc : C ↪ List Bool} (D : Decoder enc) : ChallengeCodec C where
  encode := enc
  decode := D.decode

theorem lawful_ofDecoder {enc : C ↪ List Bool} (D : Decoder enc) :
    (ofDecoder D).Lawful :=
  D.decode_enc

/-- Canonical challenge codec for fixed-width bit strings `BitString n`. -/
@[expose]
def bitString (n : ℕ) : ChallengeCodec (BitString n) where
  encode := List.ofFn
  decode := BitString.ofList n

theorem lawful_bitString (n : ℕ) : (bitString n).Lawful :=
  BitString.ofList_ofFn

/-- Canonical challenge codec for a single Boolean coin. -/
@[expose]
def bool : ChallengeCodec Bool where
  encode b := [b]
  decode w := w.headD false

theorem lawful_bool : bool.Lawful := by
  intro b; rfl

end ChallengeCodec

/-- Per-round message and challenge codecs for a protocol specification `s`. -/
@[reducible, expose]
def RoundCodecs : Spec → Type
  | [] => Unit
  | .prover M _ :: s => ProverCodec M × RoundCodecs s
  | .verifier C :: s => ChallengeCodec C × RoundCodecs s

/-- Every round codec in `s` round-trips honest messages and challenges. -/
@[reducible, expose]
def RoundCodecs.Lawful : {s : Spec} → RoundCodecs s → Prop
  | [], () => True
  | .prover _ _ :: _, (c, cs) => c.Lawful ∧ RoundCodecs.Lawful cs
  | .verifier _ :: _, (c, cs) => c.Lawful ∧ RoundCodecs.Lawful cs

/-! ### Word-level execution of a public-coin verifier -/

/-- Execute the rounds of `s` as a word-level oracle computation against an untyped bit-word
prover (`Operation = Unit`), returning whether all prover replies decoded validly together
with the resulting typed transcript. -/
@[expose]
noncomputable def runWordRounds :
    (s : Spec) → RoundCodecs s → PerChallenge ProbComp s →
      WordOracleComp Unit (Bool × Transcript s)
  | [], (), () => pure (true, ())
  | .prover _ _ :: s, (c, cs), smp => do
      let raw ← List.take c.limit <$> ProbOracleComp.query ((), [])
      (fun rest : Bool × Transcript s =>
        ((c.decode raw).isSome && rest.1, (c.decodeOrDefault raw, rest.2))) <$>
        runWordRounds s cs smp
  | .verifier _ :: s, (c, cs), (smp, smps) => do
      let ch ← ProbOracleComp.sample smp
      let _ ← List.take 0 <$> ProbOracleComp.query ((), c.encode ch)
      (fun rest : Bool × Transcript s => (rest.1, (ch, rest.2))) <$>
        runWordRounds s cs smps

/-- Compile a plain-model typed `Interactive.Verifier` into a word-level oracle verifier using the
challenge samplers `smp` and round codecs `codecs`. The verifier accepts when every prover reply
decodes validly and `V.outputOn x` returns `some _`. -/
@[expose]
noncomputable def Verifier.wordVerifierWith
    (V : Verifier OracleSpec.empty s Statement OutStmt)
    (codecs : RoundCodecs s) (smp : PerChallenge ProbComp s) (x : Statement) :
    WordOracleComp Unit Bool :=
  (fun out : Bool × Transcript s => out.1 && (V.outputOn x out.2).isSome) <$>
    runWordRounds s codecs smp

/-- Compile a plain-model typed `Interactive.Verifier` into a word-level oracle verifier using its
own challenge samplers `V.samplers`. -/
@[expose]
noncomputable def Verifier.wordVerifier
    (V : Verifier OracleSpec.empty s Statement OutStmt)
    (codecs : RoundCodecs s) (x : Statement) : WordOracleComp Unit Bool :=
  V.wordVerifierWith codecs V.samplers x

/-! ### Honest prover compilation and completeness transfer -/

/-- State of the compiled word-level prover for an honest typed prover strategy in `World.plain`,
defined by structural recursion on `s` so that `HonestWordState α s : Type`. -/
@[reducible, expose]
def HonestWordState (α : Type) : Spec → Type
  | [] => Unit
  | r :: s =>
      ProbOracleComp OracleSpec.empty
        (ProverStrategy (ProbOracleComp OracleSpec.empty) (r :: s) α) ⊕
      HonestWordState α s

/-- Initial state of the compiled honest word-level prover at the start of `s`. -/
@[reducible, expose]
def HonestWordState.init {α : Type} :
    (s : Spec) →
      ProbOracleComp OracleSpec.empty (ProverStrategy (ProbOracleComp OracleSpec.empty) s α) →
      HonestWordState α s
  | [], _ => ()
  | _ :: _, P => .inl P

/-- Single-query transition of the compiled honest word-level prover. -/
@[expose]
noncomputable def HonestWordState.respond {α : Type} :
    (s : Spec) → RoundCodecs s →
      Unit × List Bool → StateT (HonestWordState α s) PMF (List Bool)
  | [], (), _, () => pure ([], ())
  | .prover _ _ :: s, (c, cs), q, st =>
      match st with
      | .inl P =>
          (plainLaw (P >>= id)).map fun (m, next) =>
            (c.encode m, .inr (HonestWordState.init s (pure next)))
      | .inr st' =>
          (HonestWordState.respond s cs q st').map fun (w, st'') => (w, .inr st'')
  | .verifier _ :: s, (c, cs), q, st =>
      match st with
      | .inl P =>
          pure ([], .inr (HonestWordState.init s (P >>= fun k => k (c.decode q.2))))
      | .inr st' =>
          (HonestWordState.respond s cs q st').map fun (w, st'') => (w, .inr st'')

/-- Compile a plain-model typed prover computation into a word-level
`Cslib.Complexity.Prover Unit`. -/
@[expose]
noncomputable def honestWordProver {α : Type} (codecs : RoundCodecs s)
    (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s α)) :
    Complexity.Prover Unit where
  State := HonestWordState α s
  init := HonestWordState.init s P
  respond := HonestWordState.respond s codecs

/-- Generalized simulation lemma: when `respond` simulates `HonestWordState.respond s codecs`
along `embed : HonestWordState α s → State`, running `runWordRounds` produces the exact transcript
distribution of `plainLaw (P >>= runStrategy s smp)` with validity flag `true`. -/
theorem runWith_honestWordState_runWordRounds_embed {α : Type} :
    ∀ (s : Spec) (codecs : RoundCodecs s), codecs.Lawful →
      ∀ (smp : PerChallenge ProbComp s)
        (P : ProbOracleComp OracleSpec.empty
          (ProverStrategy (ProbOracleComp OracleSpec.empty) s α))
        {State : Type} (respond : Unit × List Bool → StateT State PMF (List Bool))
        (embed : HonestWordState α s → State),
        (∀ q st, respond q (embed st) =
          (HonestWordState.respond s codecs q st).map (Prod.map id embed)) →
        (ProbOracleComp.runWith respond (runWordRounds s codecs smp)
            (embed (HonestWordState.init s P))).map Prod.fst =
          (plainLaw (P >>= runStrategy s smp)).map (fun r => (true, r.1))
  | [], (), _, (), P, _, respond, embed, _ => by
      simp [runWordRounds, runStrategy, PMF.map, Function.comp_def]
  | .prover _ _ :: s, (c, cs), ⟨hc, hcs⟩, smp, P, State, respond, embed, hemb => by
      have hemb' : ∀ q st, respond q (embed (.inr st)) =
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := by
        intro q st
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]
        rfl
      rw [runWordRounds, HonestWordState.init, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hemb]
      simp only [HonestWordState.respond, PMF.bind_map, PMF.map_bind,
        ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def, Prod.map, id_eq]
      have hleft :
          ((plainLaw (P >>= id)).bind fun x : _ × _ =>
            PMF.map
              (fun a : (Bool × Transcript s) × State =>
                ((c.decode ((c.encode x.1).take c.limit)).isSome && a.1.1,
                  (c.decodeOrDefault ((c.encode x.1).take c.limit), a.1.2)))
              (ProbOracleComp.runWith respond (runWordRounds s cs smp)
                (embed (.inr (HonestWordState.init s (pure x.2)))))) =
          (plainLaw (P >>= id)).bind fun x =>
            PMF.map (fun r : Transcript s × α => (true, (x.1, r.1)))
              (plainLaw (pure x.2 >>= runStrategy s smp)) := by
        refine congrArg (PMF.bind (plainLaw (P >>= id))) (funext fun ⟨m, next⟩ => ?_)
        have ih := runWith_honestWordState_runWordRounds_embed s cs hcs smp (pure next)
          respond (embed ∘ Sum.inr) hemb'
        have hmap := congrArg (PMF.map fun p : Bool × Transcript s =>
          ((c.decode ((c.encode m).take c.limit)).isSome && p.1,
            (c.decodeOrDefault ((c.encode m).take c.limit), p.2))) ih
        simpa [PMF.map_comp, Function.comp_def, ProverCodec.isSome_decode_take_encode hc,
          ProverCodec.decodeOrDefault_take_encode hc] using hmap
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, id_eq, PMF.bind_bind,
        plainLaw_pure, PMF.pure_bind, PMF.map, Function.comp_def]
  | .verifier _ :: s, (c, cs), ⟨hc, hcs⟩, (smp, smps), P, State, respond, embed, hemb => by
      have hemb' : ∀ q st, respond q (embed (.inr st)) =
          (HonestWordState.respond s cs q st).map (Prod.map id (embed ∘ Sum.inr)) := by
        intro q st
        rw [hemb q (.inr st), HonestWordState.respond, PMF.map_comp]
        rfl
      rw [runWordRounds, HonestWordState.init, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_sample]
      simp only [PMF.bind_map, PMF.map_bind, ProbOracleComp.runWith_bind,
        ProbOracleComp.runWith_map, ProbOracleComp.runWith_query, hemb,
        HonestWordState.respond, Pure.pure, PMF.pure_map, PMF.pure_bind,
        PMF.map_comp, Function.comp_def, Prod.map, id_eq]
      have hleft :
          ((ProbComp.eval smp).bind fun ch =>
            PMF.map (fun a : (Bool × Transcript s) × State => (a.1.1, (ch, a.1.2)))
              (ProbOracleComp.runWith respond (runWordRounds s cs smps)
                (embed (.inr (HonestWordState.init s
                  (P >>= fun k => k (c.decode (c.encode ch)))))))) =
          (ProbComp.eval smp).bind fun ch =>
            PMF.map (fun r : Transcript s × α => (true, (ch, r.1)))
              (plainLaw ((P >>= fun k => k ch) >>= runStrategy s smps)) := by
        refine congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => ?_)
        rw [hc ch]
        have ih := runWith_honestWordState_runWordRounds_embed s cs hcs smps
          (P >>= fun k => k ch) respond (embed ∘ Sum.inr) hemb'
        have hmap := congrArg (PMF.map fun p : Bool × Transcript s => (p.1, (ch, p.2))) ih
        simpa [PMF.map_comp, Function.comp_def] using hmap
      rw [hleft]
      simp only [runStrategy, plainLaw_bind, plainLaw_sample, PMF.map_bind, PMF.bind_bind]
      rw [PMF.bind_comm]
      refine congrArg (PMF.bind (plainLaw P)) (funext fun k => ?_)
      refine congrArg (PMF.bind (ProbComp.eval smp)) (funext fun ch => ?_)
      simp [plainLaw_pure, PMF.map, Function.comp_def]

/-- When `codecs` is lawful, running `runWordRounds` against `HonestWordState.respond` produces the
exact transcript distribution of `plainLaw (P >>= runStrategy s smp)` with validity flag `true`. -/
theorem runWith_honestWordState_runWordRounds {α : Type}
    (s : Spec) (codecs : RoundCodecs s) (hLawful : codecs.Lawful)
    (smp : PerChallenge ProbComp s)
    (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s α)) :
    (ProbOracleComp.runWith (HonestWordState.respond s codecs) (runWordRounds s codecs smp)
        (HonestWordState.init s P)).map Prod.fst =
      (plainLaw (P >>= runStrategy s smp)).map (fun r => (true, r.1)) :=
  runWith_honestWordState_runWordRounds_embed s codecs hLawful smp P
    (HonestWordState.respond s codecs) id (fun _ _ => by simp [Prod.map_id, PMF.map_id])

/-- The word-level acceptance probability of `V.wordVerifier codecs x` with `honestWordProver`
equals the plain-model probability that `V.execute x P` outputs `some _`. -/
theorem acceptProb_wordVerifier_honestWordProver {α : Type}
    (V : Verifier OracleSpec.empty s Statement OutStmt)
    (codecs : RoundCodecs s) (hLawful : codecs.Lawful) (x : Statement)
    (P : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s α)) :
    Complexity.acceptProb (V.wordVerifier codecs x) (honestWordProver codecs P) =
      (World.plain.eval (V.execute x P)).toOuterMeasure
        (Set.ofPred fun (_, out, _) => out.isSome) := by
  have hdist :
      ((honestWordProver codecs P).run (V.wordVerifier codecs x)
        (honestWordProver codecs P).init).map Prod.fst =
      (World.plain.eval (V.execute x P)).map (fun r => r.2.1.isSome) := by
    rw [Verifier.wordVerifier, Verifier.wordVerifierWith, Complexity.Prover.run_eq_runWith,
      ProbOracleComp.runWith_map]
    dsimp [honestWordProver]
    have h1 :
        PMF.map Prod.fst
          (PMF.map
            (Prod.map (fun out : Bool × Transcript s => out.1 && (V.outputOn x out.2).isSome) id)
            (ProbOracleComp.runWith (HonestWordState.respond s codecs)
              (runWordRounds s codecs V.samplers) (HonestWordState.init s P))) =
        PMF.map (fun out : Bool × Transcript s => out.1 && (V.outputOn x out.2).isSome)
          ((ProbOracleComp.runWith (HonestWordState.respond s codecs)
            (runWordRounds s codecs V.samplers) (HonestWordState.init s P)).map Prod.fst) := by
      simp [PMF.map_comp, Function.comp_def]
    rw [h1, runWith_honestWordState_runWordRounds s codecs hLawful V.samplers P,
      World.plain_eval_execute]
    simp [PMF.map_comp, Function.comp_def]
  rw [Complexity.acceptProb, hdist, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- **Completeness transfer**: if a plain-model reduction `R` is complete with error `ε_c` and
`codecs` is lawful, then for every valid statement-witness pair `(x, w)`, the compiled honest
word-level prover makes `R.verifier.wordVerifier codecs x` accept with probability at least
`1 - ε_c`. -/
theorem Reduction.Complete.acceptProb_wordVerifier
    {R : Reduction OracleSpec.empty OracleSpec.empty s Statement Witness OutStmt OutWit}
    {relIn : Statement → Witness → Prop} {relOut : OutStmt → OutWit → Prop} {ε_c : ℝ≥0∞}
    (hComp : R.Complete World.plain relIn relOut ε_c)
    {codecs : RoundCodecs s} (hLawful : codecs.Lawful)
    {x : Statement} {w : Witness} (hrel : relIn x w) :
    1 - ε_c ≤ Complexity.acceptProb (R.verifier.wordVerifier codecs x)
      (honestWordProver codecs (R.prover x w)) := by
  rw [acceptProb_wordVerifier_honestWordProver R.verifier codecs hLawful x (R.prover x w)]
  have hfail := hComp x w hrel
  let μ := World.plain.eval (R.run x w)
  let S : Set (Transcript s × Option OutStmt × (OutStmt × OutWit)) := {r | r.2.1.isSome}
  have hcompl : Sᶜ ⊆ {r | ¬ (r.2.1 = some r.2.2.1 ∧ relOut r.2.2.1 r.2.2.2)} := by
    rintro r (hr : ¬ r.2.1.isSome) ⟨h1, _⟩
    exact hr (by simp [h1])
  have hSc : μ.toOuterMeasure Sᶜ ≤ ε_c :=
    (MeasureTheory.OuterMeasure.mono _ hcompl).trans hfail
  have hsum : μ.toOuterMeasure S + μ.toOuterMeasure Sᶜ = 1 :=
    Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal μ S
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞)
    _ = μ.toOuterMeasure S + μ.toOuterMeasure Sᶜ := hsum.symm
    _ ≤ μ.toOuterMeasure S + ε_c := add_le_add le_rfl hSc

/-! ### Adversarial decoding and soundness transfer -/

/-- Choose the decoded message `c.decodeOrDefault w` for `w ∈ BitString.shortWords c.limit`
that maximizes the continuation acceptance value `val`. -/
noncomputable def ProverCodec.bestDecodedMsg {M : Type} (c : ProverCodec M)
    (val : M → ℝ≥0∞) : M :=
  c.decodeOrDefault
    (Classical.choose
      (Finset.exists_max_image (BitString.shortWords c.limit)
        (fun w => val (c.decodeOrDefault w))
        ⟨[], BitString.nil_mem_shortWords c.limit⟩))

/-- Every truncated reply `w.take c.limit` that decodes to `some m` has continuation value at most
`val (c.bestDecodedMsg val)`. -/
theorem ProverCodec.le_bestDecodedMsg {M : Type} (c : ProverCodec M) (val : M → ℝ≥0∞)
    (w : List Bool) {m : M} (hdec : c.decode (w.take c.limit) = some m) :
    val m ≤ val (c.bestDecodedMsg val) := by
  have hspec := Classical.choose_spec
    (Finset.exists_max_image (BitString.shortWords c.limit)
      (fun u => val (c.decodeOrDefault u))
      ⟨[], BitString.nil_mem_shortWords c.limit⟩)
  have hmem : w.take c.limit ∈ BitString.shortWords c.limit :=
    BitString.mem_shortWords.mpr (List.length_take_le c.limit w)
  have hle := hspec.2 (w.take c.limit) hmem
  simpa [bestDecodedMsg, c.decodeOrDefault_eq_of_decode_eq_some hdec] using hle

/-- Optimal plain-model typed `ProverStrategy` constructed by backwards induction over the rounds
`s` to maximize the probability of satisfying `accept`. -/
noncomputable def optimalTypedStrategy :
    (s : Spec) → RoundCodecs s → PerChallenge ProbComp s → (Transcript s → Bool) →
      ProverStrategy (ProbOracleComp OracleSpec.empty) s Unit
  | [], (), (), _ => ()
  | .prover M _ :: s, (c, cs), smp, accept =>
      let cont := fun m => optimalTypedStrategy s cs smp (fun τ => accept (m, τ))
      let val := fun m =>
        (plainLaw (runStrategy s smp (cont m))).toOuterMeasure {r | accept (m, r.1) = true}
      let mStar := c.bestDecodedMsg val
      show ProbOracleComp OracleSpec.empty
          (M × ProverStrategy (ProbOracleComp OracleSpec.empty) s Unit) from
        pure (mStar, cont mStar)
  | .verifier C :: s, (_, cs), (_, smps), accept =>
      fun (ch : C) =>
        show ProbOracleComp OracleSpec.empty
            (ProverStrategy (ProbOracleComp OracleSpec.empty) s Unit) from
          pure (optimalTypedStrategy s cs smps (fun τ => accept (ch, τ)))

private theorem tsum_pmf_mul_mono {α : Type*} (p : PMF α) (f g : α → ℝ≥0∞)
    (h : ∀ a, f a ≤ g a) : ∑' a, p a * f a ≤ ∑' a, p a * g a :=
  tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le

/-- For every word-level prover `P : Cslib.Complexity.Prover Unit` and starting state `pState`,
the probability that `runWordRounds s codecs smp` produces a valid transcript accepted by `accept`
is bounded by the plain-model acceptance probability of `optimalTypedStrategy`. -/
theorem runWith_runWordRounds_le_optimalTypedStrategy :
    ∀ (s : Spec) (codecs : RoundCodecs s) (smp : PerChallenge ProbComp s)
      (accept : Transcript s → Bool) (P : Complexity.Prover Unit) (pState : P.State),
      (ProbOracleComp.runWith P.respond (runWordRounds s codecs smp) pState).toOuterMeasure
        (Set.ofPred fun ((valid, τ), _) => (valid && accept τ) = true) ≤
      (plainLaw (runStrategy s smp (optimalTypedStrategy s codecs smp accept))).toOuterMeasure
        {r | accept r.1 = true}
  | [], (), (), accept, P, pState => by
      by_cases h : accept () = true <;>
        simp [runWordRounds, optimalTypedStrategy, runStrategy, plainLaw_pure,
          PMF.toOuterMeasure_pure_apply, h]
  | .prover M _ :: s, (c, cs), smp, accept, P, pState => by
      let cont := fun m : M => optimalTypedStrategy s cs smp (fun τ => accept (m, τ))
      let val := fun m : M =>
        (plainLaw (runStrategy s smp (cont m))).toOuterMeasure {r | accept (m, r.1) = true}
      let mStar := c.bestDecodedMsg val
      have hgoal :
          (plainLaw (runStrategy (.prover M _ :: s) smp
            (optimalTypedStrategy (.prover M _ :: s) (c, cs) smp accept))).toOuterMeasure
              {r | accept r.1 = true} = val mStar := by
        simp [optimalTypedStrategy, runStrategy, PMF.toOuterMeasure_map_apply, cont, val, mStar]
      rw [hgoal]
      simp only [runWordRounds, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, PMF.bind_map, Function.comp_def,
        PMF.toOuterMeasure_bind_apply]
      refine PMF.tsum_mul_le_of_forall_le (P.respond ((), []) pState) fun ⟨w, pState'⟩ => ?_
      rw [PMF.toOuterMeasure_map_apply]
      dsimp
      rcases hdec : c.decode (w.take c.limit) with _ | m
      · simp
      · rw [c.decodeOrDefault_eq_of_decode_eq_some hdec]
        simpa only [Option.isSome_some, Bool.true_and] using
          (runWith_runWordRounds_le_optimalTypedStrategy s cs smp
            (fun τ => accept (m, τ)) P pState').trans (c.le_bestDecodedMsg val w hdec)
  | .verifier C :: s, (c, cs), (smp, smps), accept, P, pState => by
      have hgoal :
          (plainLaw (runStrategy (.verifier C :: s) (smp, smps)
            (optimalTypedStrategy (.verifier C :: s) (c, cs) (smp, smps) accept))).toOuterMeasure
              {r | accept r.1 = true} =
          ∑' ch : C, ProbComp.eval smp ch *
            (plainLaw (runStrategy s smps
              (optimalTypedStrategy s cs smps (fun τ => accept (ch, τ))))).toOuterMeasure
                {r | accept (ch, r.1) = true} := by
        rw [optimalTypedStrategy, runStrategy, plainLaw_bind, plainLaw_sample,
          PMF.toOuterMeasure_bind_apply]
        refine tsum_congr fun ch => congrArg (ProbComp.eval smp ch * ·) ?_
        simp [PMF.toOuterMeasure_map_apply]
      rw [hgoal]
      simp only [runWordRounds, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_sample, ProbOracleComp.runWith_query, PMF.bind_map,
        Function.comp_def, PMF.toOuterMeasure_bind_apply]
      refine tsum_pmf_mul_mono (ProbComp.eval smp) _ _ fun ch => ?_
      refine PMF.tsum_mul_le_of_forall_le
        (P.respond ((), c.encode ch) pState) fun ⟨_, pState'⟩ => ?_
      rw [PMF.toOuterMeasure_map_apply]
      exact runWith_runWordRounds_le_optimalTypedStrategy s cs smps
        (fun τ => accept (ch, τ)) P pState'

/-- For every word-level prover `P : Cslib.Complexity.Prover Unit`, the acceptance probability of
`V.wordVerifier codecs x` is bounded by the plain-model acceptance probability of
`optimalTypedStrategy`. -/
theorem acceptProb_wordVerifier_le_optimalTypedStrategy
    (V : Verifier OracleSpec.empty s Statement OutStmt)
    (codecs : RoundCodecs s) (x : Statement) (P : Complexity.Prover Unit) :
    Complexity.acceptProb (V.wordVerifier codecs x) P ≤
      (World.plain.eval
        (V.execute x (pure (optimalTypedStrategy s codecs V.samplers
          (fun τ => (V.outputOn x τ).isSome))))).toOuterMeasure
            (Set.ofPred fun (_, out, _) => out.isSome) := by
  rw [Complexity.acceptProb, ← PMF.toOuterMeasure_apply_singleton,
    Verifier.wordVerifier, Verifier.wordVerifierWith,
    Complexity.Prover.run_eq_runWith, ProbOracleComp.runWith_map,
    PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    World.plain_eval_execute, pure_bind, PMF.toOuterMeasure_map_apply]
  exact runWith_runWordRounds_le_optimalTypedStrategy s codecs V.samplers
    (fun τ => (V.outputOn x τ).isSome) P P.init

/-- **Soundness transfer**: if `V` is sound with error `ε_s` for reducing `langIn` to `Set.univ`
(every non-`none` output is considered acceptance), then for every `x ∉ langIn` and every
word-level prover `P : Cslib.Complexity.Prover Unit`,
`acceptProb (V.wordVerifier codecs x) P ≤ ε_s`. -/
theorem Verifier.Sound.acceptProb_wordVerifier
    {V : Verifier OracleSpec.empty s Statement OutStmt}
    {langIn : Set Statement} {ε_s : ℝ≥0∞}
    (hSound : V.Sound (oP := OracleSpec.empty) World.plain langIn Set.univ ε_s)
    (codecs : RoundCodecs s) {x : Statement} (hx : x ∉ langIn)
    (P : Complexity.Prover Unit) :
    Complexity.acceptProb (V.wordVerifier codecs x) P ≤ ε_s := by
  refine (acceptProb_wordVerifier_le_optimalTypedStrategy V codecs x P).trans ?_
  let strat := optimalTypedStrategy s codecs V.samplers (fun τ => (V.outputOn x τ).isSome)
  have h1 := hSound x hx Unit (pure strat)
  refine le_trans (MeasureTheory.OuterMeasure.mono _ fun r (hr : r.2.1.isSome = true) => ?_) h1
  rcases h : r.2.1 with _ | y
  · simp [h] at hr
  · exact ⟨y, Set.mem_univ y, h⟩

/-- If `V` is sound with error `ε_s` for reducing `langIn` to `langOut` and `V.outputOn x τ` only
outputs elements of `langOut` when `x ∉ langIn` (for instance when `langOut = language Accept`),
then `V` is sound for reducing `langIn` to `Set.univ`. -/
theorem Verifier.Sound.to_univ
    {V : Verifier OracleSpec.empty s Statement OutStmt}
    {langIn : Set Statement} {langOut : Set OutStmt} {ε_s : ℝ≥0∞}
    (hSound : V.Sound (oP := OracleSpec.empty) World.plain langIn langOut ε_s)
    (hout : ∀ x ∉ langIn, ∀ τ y, V.outputOn x τ = some y → y ∈ langOut) :
    V.Sound (oP := OracleSpec.empty) World.plain langIn Set.univ ε_s := by
  intro x hx α P
  refine le_trans ?_ (hSound x hx α P)
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.OuterMeasure.mono _ fun r ⟨y, _, hy⟩ => ?_
  exact ⟨y, hout x hx r.1 y hy, hy⟩

/-- An interactive reduction `R` that is complete with error `ε_c` and sound with error `ε_s`
(to `Set.univ`) induces a word-level `IsInteractiveProof` with completeness `1 - ε_c` and
soundness `ε_s` for `language relIn`. -/
theorem Reduction.isInteractiveProof_wordVerifier
    {R : Reduction OracleSpec.empty OracleSpec.empty s Statement Witness OutStmt OutWit}
    {relIn : Statement → Witness → Prop} {relOut : OutStmt → OutWit → Prop}
    {ε_c ε_s : ℝ≥0∞}
    (hComp : R.Complete World.plain relIn relOut ε_c)
    (hSound : R.verifier.Sound (oP := OracleSpec.empty) World.plain (language relIn) Set.univ ε_s)
    {codecs : RoundCodecs s} (hLawful : codecs.Lawful) :
    IsInteractiveProof (R.verifier.wordVerifier codecs) (language relIn) (1 - ε_c) ε_s := by
  refine ⟨fun x ⟨w, hw⟩ => ⟨honestWordProver codecs (R.prover x w),
    hComp.acceptProb_wordVerifier hLawful hw⟩,
    fun x hx P => hSound.acceptProb_wordVerifier codecs hx P⟩

/-! ### Statistical-distance stability for approximate challenge samplers -/

/-- Zero per-round error vector for a protocol specification `s`. -/
@[reducible, expose]
def PerChallenge.zero : (s : Spec) → PerChallenge (fun _ => ℝ≥0∞) s
  | [] => ()
  | .prover _ _ :: s => PerChallenge.zero s
  | .verifier _ :: s => (0, PerChallenge.zero s)

@[simp]
theorem PerChallenge.sum_zero : ∀ (s : Spec), PerChallenge.sum s (PerChallenge.zero s) = 0
  | [] => rfl
  | .prover _ _ :: s => PerChallenge.sum_zero s
  | .verifier _ :: s => by simp [PerChallenge.sum, PerChallenge.sum_zero s]

/-- Pointwise statistical closeness of per-round challenge samplers. -/
@[reducible, expose]
def PerChallenge.CloseTo :
    (s : Spec) → PerChallenge ProbComp s → PerChallenge ProbComp s →
      PerChallenge (fun _ => ℝ≥0∞) s → Prop
  | [], (), (), () => True
  | .prover _ _ :: s, smp₁, smp₂, δ => PerChallenge.CloseTo s smp₁ smp₂ δ
  | .verifier _ :: s, (d₁, smp₁), (d₂, smp₂), (ε, δ) =>
      Probability.CloseTo (ProbComp.eval d₁) (ProbComp.eval d₂) ε ∧
        PerChallenge.CloseTo s smp₁ smp₂ δ

@[simp]
theorem PerChallenge.closeTo_refl :
    ∀ (s : Spec) (smp : PerChallenge ProbComp s),
      PerChallenge.CloseTo s smp smp (PerChallenge.zero s)
  | [], () => trivial
  | .prover _ _ :: s, smp => PerChallenge.closeTo_refl s smp
  | .verifier _ :: s, (d, smp) =>
      ⟨Probability.CloseTo.refl (ProbComp.eval d), PerChallenge.closeTo_refl s smp⟩

/-- Replacing challenge samplers `smp₁` by `δ`-close challenge samplers `smp₂` changes the
word-level execution distribution of `runWordRounds` by at most `PerChallenge.sum s δ` in total
variation against any stateful word prover `P`. -/
theorem closeTo_runWordRounds :
    ∀ (s : Spec) (codecs : RoundCodecs s) {smp₁ smp₂ : PerChallenge ProbComp s}
      {δ : PerChallenge (fun _ => ℝ≥0∞) s},
      PerChallenge.CloseTo s smp₁ smp₂ δ →
      ∀ (P : Complexity.Prover Unit) (pState : P.State),
        Probability.CloseTo
          (ProbOracleComp.runWith P.respond (runWordRounds s codecs smp₁) pState)
          (ProbOracleComp.runWith P.respond (runWordRounds s codecs smp₂) pState)
          (PerChallenge.sum s δ)
  | [], (), (), (), (), _, P, pState => by
      simp [runWordRounds, PerChallenge.sum]
  | .prover _ _ :: s, (c, cs), smp₁, smp₂, δ, hClose, P, pState => by
      simp only [runWordRounds, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_query, PMF.bind_map, Function.comp_def, PerChallenge.sum]
      exact Probability.CloseTo.bind_right (P.respond ((), []) pState) fun ⟨w, pState'⟩ _ =>
        (closeTo_runWordRounds s cs hClose P pState').map _
  | .verifier _ :: s, (c, cs), (d₁, smp₁), (d₂, smp₂), (ε, δ), ⟨hd, hClose⟩, P, pState => by
      simp only [runWordRounds, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
        ProbOracleComp.runWith_sample, ProbOracleComp.runWith_query, PMF.bind_map,
        Function.comp_def, PerChallenge.sum]
      exact Probability.CloseTo.bind hd fun ch _ =>
        Probability.CloseTo.bind_right (P.respond ((), c.encode ch) pState) fun ⟨_, pState'⟩ _ =>
          (closeTo_runWordRounds s cs hClose P pState').map _

/-- If `PerChallenge.CloseTo s smp₁ smp₂ δ`, then the acceptance probabilities of
`V.wordVerifierWith codecs smp₁ x` and `V.wordVerifierWith codecs smp₂ x` against any word-level
prover `P` differ by at most `PerChallenge.sum s δ`. -/
theorem Verifier.closeTo_wordVerifierWith
    (V : Verifier OracleSpec.empty s Statement OutStmt) (codecs : RoundCodecs s)
    {smp₁ smp₂ : PerChallenge ProbComp s} {δ : PerChallenge (fun _ => ℝ≥0∞) s}
    (hClose : PerChallenge.CloseTo s smp₁ smp₂ δ) (x : Statement) (P : Complexity.Prover Unit) :
    Probability.CloseTo
      ((P.run (V.wordVerifierWith codecs smp₁ x) P.init).map Prod.fst)
      ((P.run (V.wordVerifierWith codecs smp₂ x) P.init).map Prod.fst)
      (PerChallenge.sum s δ) := by
  simp only [Verifier.wordVerifierWith, Complexity.Prover.run_eq_runWith,
    ProbOracleComp.runWith_map, PMF.map_comp, Function.comp_def]
  exact (closeTo_runWordRounds s codecs hClose P P.init).map _

theorem Verifier.acceptProb_wordVerifier_le_wordVerifierWith_add
    (V : Verifier OracleSpec.empty s Statement OutStmt) (codecs : RoundCodecs s)
    {smp : PerChallenge ProbComp s} {δ : PerChallenge (fun _ => ℝ≥0∞) s}
    (hClose : PerChallenge.CloseTo s V.samplers smp δ) (x : Statement)
    (P : Complexity.Prover Unit) :
    Complexity.acceptProb (V.wordVerifier codecs x) P ≤
      Complexity.acceptProb (V.wordVerifierWith codecs smp x) P + PerChallenge.sum s δ := by
  have h := V.closeTo_wordVerifierWith codecs hClose x P {true}
  simpa [Complexity.acceptProb, Verifier.wordVerifier, PMF.toOuterMeasure_apply_singleton] using h

theorem Verifier.acceptProb_wordVerifierWith_le_wordVerifier_add
    (V : Verifier OracleSpec.empty s Statement OutStmt) (codecs : RoundCodecs s)
    {smp : PerChallenge ProbComp s} {δ : PerChallenge (fun _ => ℝ≥0∞) s}
    (hClose : PerChallenge.CloseTo s V.samplers smp δ) (x : Statement)
    (P : Complexity.Prover Unit) :
    Complexity.acceptProb (V.wordVerifierWith codecs smp x) P ≤
      Complexity.acceptProb (V.wordVerifier codecs x) P + PerChallenge.sum s δ := by
  have h := (V.closeTo_wordVerifierWith codecs hClose x P).symm {true}
  simpa [Complexity.acceptProb, Verifier.wordVerifier, PMF.toOuterMeasure_apply_singleton] using h

/-! ### Uniform polynomial-time certificates and `IP` membership -/

/-- Per-round bit-word encodings for a protocol specification `s`, giving a canonical nested-pair
encoding `RoundEncodings.transcript : Transcript s ↪ List Bool`. -/
@[reducible, expose]
def RoundEncodings : Spec → Type
  | [] => Unit
  | .prover M _ :: s => (M ↪ List Bool) × RoundEncodings s
  | .verifier C :: s => (C ↪ List Bool) × RoundEncodings s

/-- The nested-pair encoding of `Transcript s` induced by per-round encodings. -/
@[reducible, expose]
def RoundEncodings.transcript : {s : Spec} → RoundEncodings s → Transcript s ↪ List Bool
  | [], () => encUnit
  | .prover _ _ :: _, (encM, encs) => encPair encM encs.transcript
  | .verifier _ :: _, (encC, encs) => encPair encC encs.transcript

/-- A `ProverCodec M` is polynomial-time with respect to `encM : M ↪ List Bool` when both its
validity test `(decode ·).isSome` and its total fallback decoder `decodeOrDefault` are
polynomial-time computable. -/
@[expose]
def ProverCodec.IsPolyTime {M : Type} (encM : M ↪ List Bool) (c : ProverCodec M) : Prop :=
  ComputableInPolyTime (fun w => (c.decode w).isSome) encBits encBool ∧
    ComputableInPolyTime c.decodeOrDefault encBits encM

/-- A prover codec whose partial `decode` is polynomial-time with respect to `encOption encM` is
polynomial-time. -/
theorem ProverCodec.IsPolyTime.of_decode {M : Type} {encM : M ↪ List Bool} {c : ProverCodec M}
    (hdec : ComputableInPolyTime c.decode encBits (encOption encM)) :
    c.IsPolyTime encM := by
  have htidy := hdec.tidy
  refine ⟨.of_tidy htidy.optionIsSome,
    .of_tidy (htidy.optionGetDWithInput (ComputableTidilyInPolyTime.const c.default))⟩

/-- A `ProverCodec.ofTotal` is polynomial-time whenever its total decoder is polynomial-time. -/
theorem ProverCodec.isPolyTime_ofTotal {M : Type} {encM : M ↪ List Bool}
    {encode : M → List Bool} {decode : List Bool → M} {default : M} {limit : ℕ}
    (hdec : ComputableInPolyTime decode encBits encM) :
    (ProverCodec.ofTotal encode decode default limit).IsPolyTime encM :=
  ⟨.of_tidy (ComputableTidilyInPolyTime.const true), hdec⟩

/-- A `ProverCodec.ofDecoder D default limit` is automatically polynomial-time. -/
theorem ProverCodec.isPolyTime_ofDecoder {M : Type} {encM : M ↪ List Bool}
    (D : Decoder encM) (default : M) (limit : ℕ) :
    (ProverCodec.ofDecoder D default limit).IsPolyTime encM :=
  ProverCodec.isPolyTime_ofTotal D.computableInPolyTime

/-- A `ChallengeCodec C` and challenge sampler `smp : ProbComp C` are polynomial-time with respect
to `encC : C ↪ List Bool` when `smp` is `IsPPTOn` and `c.encode` is polynomial-time. -/
@[expose]
def ChallengeCodec.IsPolyTime {C : Type} (encC : C ↪ List Bool)
    (c : ChallengeCodec C) (smp : ProbComp C) : Prop :=
  IsPPTOn encUnit encC (fun _ : Unit => smp) ∧
    ComputableInPolyTime c.encode encC encBits

/-- Per-round polynomial-time certificate for `RoundCodecs s` and challenge samplers `smp`. -/
@[reducible, expose]
def RoundCodecs.IsPolyTime :
    {s : Spec} → RoundEncodings s → RoundCodecs s → PerChallenge ProbComp s → Prop
  | [], (), (), () => True
  | .prover _ _ :: _, (encM, encs), (c, cs), smp =>
      c.IsPolyTime encM ∧ RoundCodecs.IsPolyTime encs cs smp
  | .verifier _ :: _, (encC, encs), (c, cs), (smp, smps) =>
      c.IsPolyTime encC smp ∧ RoundCodecs.IsPolyTime encs cs smps

/-- When the round codecs and challenge samplers of `s` are polynomial-time, `runWordRounds` is a
uniform polynomial-time word-oracle computation (`IsOraclePPTOn`) for any input encoding `encIn`. -/
theorem isOraclePPTOn_runWordRounds {α : Type} (encIn : α ↪ List Bool) :
    ∀ (s : Spec) (encs : RoundEncodings s) (codecs : RoundCodecs s)
      (smp : PerChallenge ProbComp s),
      codecs.IsPolyTime encs smp →
      IsOraclePPTOn encIn (encPair encBool encs.transcript)
        (fun _ : α => runWordRounds s codecs smp)
  | [], (), (), (), _ => by
      change IsOraclePPTOn encIn (encPair encBool encUnit) (fun _ : α => pure (true, ()))
      exact (ComputableInPolyTime.const (true, ())).isOraclePPTOn
  | .prover M _ :: s, (encM, encs), (c, cs), smp, ⟨⟨hValid, hDec⟩, hcs⟩ => by
      simp only [runWordRounds, RoundEncodings.transcript]
      have hq : IsOraclePPTOn encIn encBits
          (fun _ : α => List.take c.limit <$> ProbOracleComp.query ((), [])) :=
        IsOraclePPTOn.query_take' () (ComputableInPolyTime.const [])
          (ComputableInPolyTime.const c.limit)
      have hrest := isOraclePPTOn_runWordRounds (encPair encIn encBits) s encs cs smp hcs
      have hpost : ComputableInPolyTime
          (fun p : (α × List Bool) × (Bool × Transcript s) =>
            ((c.decode p.1.2).isSome && p.2.1, (c.decodeOrDefault p.1.2, p.2.2)))
          (encPair (encPair encIn encBits) (encPair encBool encs.transcript))
          (encPair encBool (encPair encM encs.transcript)) := by
        let encAll := encPair (encPair encIn encBits) (encPair encBool encs.transcript)
        have hp12 : ComputableTidilyInPolyTime
            (fun p : (α × List Bool) × (Bool × Transcript s) => p.1.2)
            encAll encBits := by fun_prop
        have hp21 : ComputableTidilyInPolyTime
            (fun p : (α × List Bool) × (Bool × Transcript s) => p.2.1)
            encAll encBool := by fun_prop
        have hp22 : ComputableTidilyInPolyTime
            (fun p : (α × List Bool) × (Bool × Transcript s) => p.2.2)
            encAll encs.transcript := by fun_prop
        exact .of_tidy
          (((hValid.tidy.comp hp12).bool_and' hp21).prod ((hDec.tidy.comp hp12).prod hp22))
      exact hq.bind_with (hrest.map_with' hpost)
  | .verifier C :: s, (encC, encs), (c, cs), (smp, smps), ⟨⟨hsmp, hEnc⟩, hcs⟩ => by
      simp only [runWordRounds, RoundEncodings.transcript]
      have hsample : IsOraclePPTOn encIn encC (fun _ : α => ProbOracleComp.sample smp) :=
        (hsmp.isOraclePPTOn (Operation := Unit)).preprocess' (ComputableInPolyTime.const ())
      have hsend : IsOraclePPTOn (encPair encIn encC) encBits
          (fun p : α × C => List.take 0 <$> ProbOracleComp.query ((), c.encode p.2)) := by
        have hpayload : ComputableInPolyTime (fun p : α × C => c.encode p.2)
            (encPair encIn encC) encBits := by
          have hp2 : ComputableTidilyInPolyTime (fun p : α × C => p.2)
              (encPair encIn encC) encC := by fun_prop
          exact .of_tidy (hEnc.tidy.comp hp2)
        exact IsOraclePPTOn.query_take' ()
          hpayload
          (.of_tidy (ComputableTidilyInPolyTime.const 0))
      have hrest := isOraclePPTOn_runWordRounds
        (encPair (encPair encIn encC) encBits) s encs cs smps hcs
      have hpost : ComputableInPolyTime
          (fun p : ((α × C) × List Bool) × (Bool × Transcript s) =>
            (p.2.1, (p.1.1.2, p.2.2)))
          (encPair (encPair (encPair encIn encC) encBits) (encPair encBool encs.transcript))
          (encPair encBool (encPair encC encs.transcript)) :=
        .of_tidy (by fun_prop)
      refine IsOraclePPTOn.bind_with hsample ?_
      refine IsOraclePPTOn.bind_with hsend ?_
      exact hrest.map_with' hpost

/-- If the round codecs and challenge samplers of `s` are polynomial-time and the verifier's
acceptance predicate `(V.outputOn x τ).isSome` is polynomial-time in `(x, τ)`, then the compiled
word-level verifier `V.wordVerifierWith codecs smp` is `IsOraclePPTOn`. -/
theorem Verifier.isOraclePPTOn_wordVerifierWith
    (V : Verifier OracleSpec.empty s Statement OutStmt) (encStmt : Statement ↪ List Bool)
    (encs : RoundEncodings s) (codecs : RoundCodecs s) (smp : PerChallenge ProbComp s)
    (hRounds : codecs.IsPolyTime encs smp)
    (hDecide : ComputableInPolyTime
      (fun p : Statement × Transcript s => (V.outputOn p.1 p.2).isSome)
      (encPair encStmt encs.transcript) encBool) :
    IsOraclePPTOn encStmt encBool (V.wordVerifierWith codecs smp) := by
  have hrun := isOraclePPTOn_runWordRounds encStmt s encs codecs smp hRounds
  have hpost : ComputableInPolyTime
      (fun p : Statement × (Bool × Transcript s) =>
        p.2.1 && (V.outputOn p.1 p.2.2).isSome)
      (encPair encStmt (encPair encBool encs.transcript)) encBool := by
    let encAll := encPair encStmt (encPair encBool encs.transcript)
    have hp21 : ComputableTidilyInPolyTime
        (fun p : Statement × (Bool × Transcript s) => p.2.1)
        encAll encBool := by fun_prop
    have hp122 : ComputableTidilyInPolyTime
        (fun p : Statement × (Bool × Transcript s) => (p.1, p.2.2))
        encAll (encPair encStmt encs.transcript) := by fun_prop
    exact .of_tidy (hp21.bool_and' (hDecide.tidy.comp hp122))
  exact hrun.map_with' hpost

/-- Special case of `Verifier.isOraclePPTOn_wordVerifierWith` when `smp = V.samplers`. -/
theorem Verifier.isOraclePPTOn_wordVerifier
    (V : Verifier OracleSpec.empty s Statement OutStmt) (encStmt : Statement ↪ List Bool)
    (encs : RoundEncodings s) (codecs : RoundCodecs s)
    (hRounds : codecs.IsPolyTime encs V.samplers)
    (hDecide : ComputableInPolyTime
      (fun p : Statement × Transcript s => (V.outputOn p.1 p.2).isSome)
      (encPair encStmt encs.transcript) encBool) :
    IsOraclePPTOn encStmt encBool (V.wordVerifier codecs) :=
  V.isOraclePPTOn_wordVerifierWith encStmt encs codecs V.samplers hRounds hDecide

/-- **Public-coin interactive reductions to `IP`**: if a relation `relIn` admits a plain-model
interactive reduction `R` with completeness error `ε_c`, soundness error `ε_s` (to `Set.univ`),
lawful round codecs `codecs`, and challenge samplers `smp` within total variation `δ` of
`R.verifier.samplers` such that `ε_c + PerChallenge.sum s δ ≤ 1 / 3` and
`ε_s + PerChallenge.sum s δ ≤ 1 / 3`, and the compiled word verifier is `IsOraclePPTOn`, then
`language relIn ∈ IP encStmt`. -/
theorem mem_IP_of_reduction_closeTo
    {R : Reduction OracleSpec.empty OracleSpec.empty s Statement Witness OutStmt OutWit}
    {relIn : Statement → Witness → Prop} {relOut : OutStmt → OutWit → Prop}
    {encStmt : Statement ↪ List Bool}
    {encs : RoundEncodings s} {codecs : RoundCodecs s} {smp : PerChallenge ProbComp s}
    {δ : PerChallenge (fun _ => ℝ≥0∞) s} {ε_c ε_s : ℝ≥0∞}
    (hLawful : codecs.Lawful)
    (hRounds : codecs.IsPolyTime encs smp)
    (hDecide : ComputableInPolyTime
      (fun p : Statement × Transcript s => (R.verifier.outputOn p.1 p.2).isSome)
      (encPair encStmt encs.transcript) encBool)
    (hClose : PerChallenge.CloseTo s R.verifier.samplers smp δ)
    (hComp : R.Complete World.plain relIn relOut ε_c)
    (hSound : R.verifier.Sound (oP := OracleSpec.empty) World.plain (language relIn) Set.univ ε_s)
    (hεc : ε_c + PerChallenge.sum s δ ≤ 1 / 3)
    (hεs : ε_s + PerChallenge.sum s δ ≤ 1 / 3) :
    language relIn ∈ IP encStmt := by
  refine ⟨R.verifier.wordVerifierWith codecs smp,
    R.verifier.isOraclePPTOn_wordVerifierWith encStmt encs codecs smp hRounds hDecide,
    fun x ⟨w, hw⟩ => ?_, fun x hx P => ?_⟩
  · refine ⟨honestWordProver codecs (R.prover x w), ?_⟩
    have h1 := hComp.acceptProb_wordVerifier hLawful hw
    have h2 := R.verifier.acceptProb_wordVerifier_le_wordVerifierWith_add codecs hClose x
      (honestWordProver codecs (R.prover x w))
    have h23 : (2 / 3 : ℝ≥0∞) + (1 / 3 : ℝ≥0∞) ≤ 1 := by
      rw [← ENNReal.add_div]
      exact ENNReal.div_le_of_le_mul (by norm_num)
    have hlt_top : ε_c + PerChallenge.sum s δ < ⊤ :=
      lt_of_le_of_lt hεc (ENNReal.div_lt_top (by norm_num) (by norm_num))
    refine WithTop.le_of_add_le_add_right hlt_top.ne ?_
    calc (2 / 3 : ℝ≥0∞) + (ε_c + PerChallenge.sum s δ)
      _ ≤ 2 / 3 + 1 / 3 := add_le_add le_rfl hεc
      _ ≤ 1 := h23
      _ ≤ (1 - ε_c) + ε_c := le_tsub_add
      _ ≤ (Complexity.acceptProb (R.verifier.wordVerifierWith codecs smp x)
            (honestWordProver codecs (R.prover x w)) + PerChallenge.sum s δ) + ε_c :=
          add_le_add (h1.trans h2) le_rfl
      _ = Complexity.acceptProb (R.verifier.wordVerifierWith codecs smp x)
            (honestWordProver codecs (R.prover x w)) + (ε_c + PerChallenge.sum s δ) := by ac_rfl
  · have h1 := hSound.acceptProb_wordVerifier codecs hx P
    have h2 := R.verifier.acceptProb_wordVerifierWith_le_wordVerifier_add codecs hClose x P
    exact h2.trans ((add_le_add h1 le_rfl).trans hεs)

/-- **Public-coin interactive reductions to `IP` (exact challenge samplers)**: if a relation
`relIn` admits a plain-model interactive reduction `R` with completeness error `ε_c ≤ 1 / 3`,
soundness error `ε_s ≤ 1 / 3` (to `Set.univ`), and lawful polynomial-time round codecs, then
`language relIn ∈ IP encStmt`. -/
theorem Reduction.mem_IP
    {R : Reduction OracleSpec.empty OracleSpec.empty s Statement Witness OutStmt OutWit}
    {relIn : Statement → Witness → Prop} {relOut : OutStmt → OutWit → Prop}
    {encStmt : Statement ↪ List Bool}
    {encs : RoundEncodings s} {codecs : RoundCodecs s} {ε_c ε_s : ℝ≥0∞}
    (hLawful : codecs.Lawful)
    (hRounds : codecs.IsPolyTime encs R.verifier.samplers)
    (hDecide : ComputableInPolyTime
      (fun p : Statement × Transcript s => (R.verifier.outputOn p.1 p.2).isSome)
      (encPair encStmt encs.transcript) encBool)
    (hComp : R.Complete World.plain relIn relOut ε_c)
    (hSound : R.verifier.Sound (oP := OracleSpec.empty) World.plain (language relIn) Set.univ ε_s)
    (hεc : ε_c ≤ 1 / 3) (hεs : ε_s ≤ 1 / 3) :
    language relIn ∈ IP encStmt :=
  mem_IP_of_reduction_closeTo hLawful hRounds hDecide
    (PerChallenge.closeTo_refl s R.verifier.samplers) hComp hSound
    (by simpa [PerChallenge.sum_zero] using hεc)
    (by simpa [PerChallenge.sum_zero] using hεs)

end Cslib.Interactive
