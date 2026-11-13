/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.ToIP
import CslibFrontier.Probability.PMF.Uniform

/-!
# Tests for the `PublicCoin → IP` bridge

Checks the public API of `CslibFrontier.Computability.Interactive.ToIP` and instantiates a concrete
two-round public-coin interactive reduction
(`[.prover Bool (OracleInterface.full Bool), .verifier Bool]`) with a partial prover message codec
that rejects malformed bit strings (`length ≠ 1`), proving:

1. Completeness transfer (`Reduction.Complete.acceptProb_wordVerifier`).
2. Soundness transfer against arbitrary stateful `PMF` word provers
   (`Verifier.Sound.acceptProb_wordVerifier`).
3. Explicit adversarial decoding rejection when a cheating word prover sends a malformed bit string
   whose length exceeds 1, even when `c.default = true`.
4. Full `IP` membership (`Reduction.mem_IP`).
-/

namespace CslibFrontierTests.PublicCoinToIP

open Cslib Cslib.Interactive Spec World Cslib.Complexity Probability Turing.MultiTapeTM
open scoped ENNReal

/-- Two-round specification: one 1-bit prover message followed by one public Boolean challenge. -/
abbrev bitCoinSpec : Spec := [.prover Bool (OracleInterface.full Bool), .verifier Bool]

/-- Relation: the statement `x : Bool` is `true` and the witness `w : Bool` equals `true`. -/
def bitRel : Bool → Bool → Prop := fun x w => x = true ∧ w = true

/-- A partial prover codec for `Bool` with `limit = 2` and `default = true` that accepts only
1-bit replies `[b]` and rejects `[]` or 2-bit replies `[b₁, b₂]`. -/
def strictBoolProverCodec : ProverCodec Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  default := true
  limit := 2

theorem strictBoolProverCodec_lawful : strictBoolProverCodec.Lawful := by
  intro b
  rfl

/-- Round codecs for `bitCoinSpec`. -/
def bitCoinCodecs : RoundCodecs bitCoinSpec :=
  (strictBoolProverCodec, (ChallengeCodec.bool, ()))

theorem bitCoinCodecs_lawful : bitCoinCodecs.Lawful :=
  ⟨strictBoolProverCodec_lawful, ⟨ChallengeCodec.lawful_bool, trivial⟩⟩

/-- Concrete 2-round reduction: the prover sends `w`, the verifier sends a fair coin `c`, queries
the prover's message `m`, and accepts (`some ()`) when `x && m` is `true`. -/
noncomputable def bitCoinReduction :
    Reduction OracleSpec.empty OracleSpec.empty bitCoinSpec Bool Bool Unit Unit where
  prover _ w :=
    pure (show ProbOracleComp OracleSpec.empty
        (Bool × (Bool → ProbOracleComp OracleSpec.empty (Unit × Unit))) from
      pure (w, fun _ => pure ((), ())))
  verifier :=
    { samplers := (ProbComp.uniform Bool, ())
      decide := fun x _ => do
        let m ← OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec bitCoinSpec)
          (Sum.inr (Sum.inl ()))
        return (if x && m then some () else none) }

theorem bitCoinReduction_complete :
    bitCoinReduction.Complete World.plain bitRel Accept 0 := by
  rintro x w ⟨rfl, rfl⟩
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hempty :
      ((fun r : Transcript bitCoinSpec × Unit × Unit =>
        (r.1, bitCoinReduction.verifier.outputOn true r.1, r.2)) ⁻¹'
          {r : Execution bitCoinSpec Unit (Unit × Unit) |
            ¬(r.output = some r.result.1 ∧ Accept r.result.1 r.result.2)}) =
      {r : Transcript bitCoinSpec × Unit × Unit | r.1.1 = false} := by
    ext ⟨⟨m, ch, ⟨⟩⟩, ⟨⟩, ⟨⟩⟩
    cases m
    · exact iff_of_true (fun ⟨h, _⟩ => by cases h) rfl
    · exact iff_of_false (fun h => h ⟨rfl, trivial⟩) Bool.noConfusion
  rw [hempty]
  simp [bitCoinReduction, runStrategy, OracleInterface.full]

theorem bitCoinReduction_sound :
    bitCoinReduction.verifier.Sound (oP := OracleSpec.empty) World.plain
      (language bitRel) Set.univ 0 := by
  intro x hx α P
  have hxf : x = false := by
    cases x with
    | false => rfl
    | true => exact False.elim (hx ⟨true, rfl, rfl⟩)
  subst hxf
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hempty :
      ((fun r : Transcript bitCoinSpec × α =>
        (r.1, bitCoinReduction.verifier.outputOn false r.1, r.2)) ⁻¹'
          {r : Execution bitCoinSpec Unit α |
            ∃ x' ∈ (Set.univ : Set Unit), r.output = some x'}) = ∅ := by
    ext r
    exact iff_of_false (fun ⟨_, _, h⟩ => by cases h) id
  rw [hempty]
  simp

/-- The compiled word verifier for `bitCoinReduction` is an interactive proof with completeness `1`
and soundness `0`. -/
theorem bitCoinReduction_isInteractiveProof :
    IsInteractiveProof (bitCoinReduction.verifier.wordVerifier bitCoinCodecs)
      (language bitRel) 1 0 := by
  simpa using bitCoinReduction.isInteractiveProof_wordVerifier
    bitCoinReduction_complete bitCoinReduction_sound bitCoinCodecs_lawful

/-- A cheating word-level prover that always replies with a malformed 2-bit message `[true, true]`
is rejected with acceptance probability `0` even on a true statement `x = true` and even though
`strictBoolProverCodec.default = true`. -/
noncomputable def malformedWordProver : Complexity.Prover Unit where
  State := Unit
  init := ()
  respond _ _ := pure ([true, true], ())

theorem acceptProb_malformedWordProver_eq_zero :
    Complexity.acceptProb
      (bitCoinReduction.verifier.wordVerifier bitCoinCodecs true)
      malformedWordProver = 0 := by
  refine Complexity.acceptProb_eq_zero malformedWordProver fun x hx => ?_
  rw [Verifier.wordVerifier, Verifier.wordVerifierWith, Complexity.Prover.run_map,
    PMF.support_map] at hx
  rcases hx with ⟨⟨⟨valid, tr⟩, _⟩, hmem, rfl⟩
  dsimp [runWordRounds, bitCoinSpec, bitCoinCodecs, strictBoolProverCodec] at hmem
  rw [Complexity.Prover.run_bind, Complexity.Prover.run_map, Complexity.Prover.run_query] at hmem
  simp only [malformedWordProver, StateT.run, Pure.pure, PMF.pure_map,
    PMF.pure_bind, Prod.map, id_eq, List.take] at hmem
  rw [Complexity.Prover.run_map, PMF.support_map] at hmem
  rcases hmem with ⟨_, _, h1⟩
  injection h1 with h2 _
  injection h2 with hvalid _
  simp [← hvalid]

/-- Concrete 0-round reduction demonstrating `Reduction.mem_IP` end-to-end. -/
noncomputable def zeroRoundReduction :
    Reduction OracleSpec.empty OracleSpec.empty [] Bool Bool Unit Unit where
  prover _ _ := pure ((), ())
  verifier :=
    { samplers := ()
      decide := fun x _ => return (if x then some () else none) }

theorem zeroRoundReduction_complete :
    zeroRoundReduction.Complete World.plain bitRel Accept 0 := by
  rintro x w ⟨rfl, rfl⟩
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hempty :
      ((fun r : Transcript [] × Unit × Unit =>
        (r.1, zeroRoundReduction.verifier.outputOn true r.1, r.2)) ⁻¹'
          {r : Execution [] Unit (Unit × Unit) |
            ¬(r.output = some r.result.1 ∧ Accept r.result.1 r.result.2)}) = ∅ := by
    ext ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    exact iff_of_false (fun h => h ⟨rfl, trivial⟩) id
  rw [hempty]
  simp

theorem zeroRoundReduction_sound :
    zeroRoundReduction.verifier.Sound (oP := OracleSpec.empty) World.plain
      (language bitRel) Set.univ 0 := by
  intro x hx α P
  have hxf : x = false := by
    cases x with
    | false => rfl
    | true => exact False.elim (hx ⟨true, rfl, rfl⟩)
  subst hxf
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  have hempty :
      ((fun r : Transcript [] × α =>
        (r.1, zeroRoundReduction.verifier.outputOn false r.1, r.2)) ⁻¹'
          {r : Execution [] Unit α | ∃ x' ∈ (Set.univ : Set Unit), r.output = some x'}) = ∅ := by
    ext r
    exact iff_of_false (fun ⟨_, _, h⟩ => by cases h) id
  rw [hempty]
  simp

theorem bitRel_mem_IP : language bitRel ∈ IP encBool := by
  have heq :
      (fun p : Bool × Transcript [] => (zeroRoundReduction.verifier.outputOn p.1 p.2).isSome) =
      Prod.fst := by
    funext ⟨b, _⟩
    cases b <;> rfl
  have hDecide : ComputableInPolyTime
      (fun p : Bool × Transcript [] => (zeroRoundReduction.verifier.outputOn p.1 p.2).isSome)
      (encPair encBool (RoundEncodings.transcript (s := []) ())) encBool := by
    rw [heq]
    exact .of_tidy (by fun_prop)
  exact zeroRoundReduction.mem_IP
    (encs := ()) (codecs := ()) trivial trivial hDecide
    zeroRoundReduction_complete zeroRoundReduction_sound (by norm_num) (by norm_num)

end CslibFrontierTests.PublicCoinToIP
