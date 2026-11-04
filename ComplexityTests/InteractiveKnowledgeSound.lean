/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Interactive.Sumcheck

/-!
# Instances of straight-line knowledge soundness

Instances of `Interactive.Verifier.KnowledgeSound` and `Interactive.Reduction.HVZK` on both sides,
and what knowledge soundness adds over soundness.

* `sendWitness`: the one-message proof system in which the prover sends its witness and the
  verifier checks it. It is perfectly complete, and knowledge sound with error `0` for the
  extractor that reads the witness off the transcript.
* `trustMe`: a verifier that accepts without interaction. It is not knowledge sound for the empty
  relation with any extractor and any error below `1`, so the notion is not trivially satisfied.
* `knowledgeSound_iff_sound`: in the plain model, some extractor makes a verifier knowledge sound
  exactly when it is sound for the languages of the relations, with the same error. The forward
  direction gives a prover that ends with a valid output witness whenever the verifier's output has
  one; the backward direction uses an extractor that returns a witness of the input statement
  whenever one exists. Without an efficiency requirement on the extractor, which
  `KnowledgeSound` leaves to a separate layer, knowledge soundness therefore says no more than
  soundness; its content is in the named extractor.
  For a relation in which every statement has a witness (such as discrete logarithms in a group of
  prime order, the relation of Schnorr's protocol), every verifier is knowledge sound with error
  `0`, even `trustMe`.
* Sumcheck rounds (with `Unit` witnesses) are knowledge sound with the trivial extractor and error
  `d / |F|`, and `Verifier.KnowledgeSound.append` composes two of them.
* A sumcheck round is perfectly honest-verifier zero knowledge, since its honest message is a
  function of the statement; sending the witness is not, with any simulator and error below `1/2`,
  for a statement with two witnesses.
-/

namespace ComplexityTests.InteractiveKnowledgeSound

open Cslib Cslib.Interactive Spec
open scoped ENNReal

variable {s : Spec} {StmtIn WitIn StmtOut WitOut : Type}

/-! ### Knowledge soundness and soundness -/

/-- Soundness gives knowledge soundness for any extractor that is correct on the statements of
the input language. -/
theorem knowledgeSound_of_sound {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop} {ε : ℝ≥0∞}
    (E : StmtIn → Transcript s → WitOut → WitIn)
    (hE : ∀ x ∈ language relIn, ∀ τ w, relIn x (E x τ w))
    (h : V.Sound (oP := OracleSpec.empty) World.plain (language relIn) (language relOut) ε) :
    V.KnowledgeSound relIn relOut E ε := by
  intro x P
  by_cases hx : x ∈ language relIn
  · have hempty : {r : Transcript s × Option StmtOut × WitOut |
        (∃ x', r.2.1 = some x' ∧ relOut x' r.2.2) ∧ ¬ relIn x (E x r.1 r.2.2)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun r hr => hr.2 (hE x hx r.1 r.2.2)
    rw [hempty, MeasureTheory.measure_empty]
    exact zero_le
  · refine le_trans (MeasureTheory.measure_mono ?_) (h x hx WitOut P)
    rintro r ⟨⟨x', hout, hrel⟩, -⟩
    exact ⟨x', ⟨r.2.2, hrel⟩, hout⟩

/-- The extractor that returns a witness of the input statement whenever one exists. -/
noncomputable def choiceExtractor [Nonempty WitIn] (relIn : StmtIn → WitIn → Prop) :
    StmtIn → Transcript s → WitOut → WitIn :=
  fun x _ _ => Classical.epsilon (relIn x)

/-- An output witness for the verifier's output, whenever it has one. -/
noncomputable def outputWitness [Nonempty WitOut] (relOut : StmtOut → WitOut → Prop) :
    Option StmtOut → WitOut
  | some x' => Classical.epsilon (relOut x')
  | none => Classical.arbitrary WitOut

/-- Knowledge soundness gives soundness: a prover that makes the verifier output a statement of
the output language can end with a witness for it. -/
theorem sound_of_knowledgeSound [Nonempty WitOut] {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop} {ε : ℝ≥0∞}
    {E : StmtIn → Transcript s → WitOut → WitIn} (h : V.KnowledgeSound relIn relOut E ε) :
    V.Sound (oP := OracleSpec.empty) World.plain (language relIn) (language relOut) ε := by
  intro x hx α P
  let P' : ProbOracleComp OracleSpec.empty
      (ProverStrategy (ProbOracleComp OracleSpec.empty) s WitOut) :=
    P >>= fun st => ProverStrategy.bindLeaf s st fun τ _ =>
      pure (outputWitness relOut (V.outputOn x τ))
  have hlaw : plainLaw (P' >>= runStrategy s V.samplers) =
      (plainLaw (P >>= runStrategy s V.samplers)).map
        fun r => (r.1, outputWitness relOut (V.outputOn x r.1)) := by
    simp only [P', bind_assoc, plainLaw_bind, PMF.map_bind]
    congr 1
    funext st
    rw [← plainLaw_bind, plainLaw_bindLeaf_run]
    simp only [plainLaw_pure, PMF.pure_map]
    exact PMF.bind_pure_comp _ _
  have hk := h x P'
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply, hlaw,
    PMF.toOuterMeasure_map_apply] at hk
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  refine le_trans (MeasureTheory.measure_mono ?_) hk
  rintro r ⟨x', ⟨w', hw'⟩, hout⟩
  change V.outputOn x r.1 = some x' at hout
  refine ⟨⟨x', hout, ?_⟩, fun hrel => hx ⟨_, hrel⟩⟩
  change relOut x' (outputWitness relOut (V.outputOn x r.1))
  rw [hout]
  exact Classical.epsilon_spec ⟨w', hw'⟩

/-- **Knowledge soundness without an efficiency requirement is soundness**: in the plain model,
some straight-line extractor makes `V` knowledge sound with error `ε` exactly when `V` is sound
for the languages of the relations with error `ε`. -/
theorem knowledgeSound_iff_sound [Nonempty WitIn] [Nonempty WitOut]
    {V : Verifier OracleSpec.empty s StmtIn StmtOut}
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop} {ε : ℝ≥0∞} :
    (∃ E, V.KnowledgeSound relIn relOut E ε) ↔
      V.Sound (oP := OracleSpec.empty) World.plain (language relIn) (language relOut) ε :=
  ⟨fun ⟨_, h⟩ => sound_of_knowledgeSound h, fun h =>
    ⟨choiceExtractor relIn, knowledgeSound_of_sound _
      (fun _ hx _ _ => Classical.epsilon_spec hx) h⟩⟩

/-! ### Sending the witness -/

/-- One prover message, read in full. -/
abbrev witnessSpec (W : Type) : Spec := [.prover W (OracleInterface.full W)]

/-- The one-message proof system for a relation: the prover sends its witness and the verifier
accepts when the message is a witness for the statement. -/
noncomputable def sendWitness {X W : Type} (rel : X → W → Prop) [∀ x w, Decidable (rel x w)] :
    Reduction OracleSpec.empty OracleSpec.empty (witnessSpec W) X W Unit Unit where
  prover _ w := pure (show ProbOracleComp OracleSpec.empty (W × (Unit × Unit)) from
    pure (w, ((), ())))
  verifier :=
    { samplers := ()
      decide := fun x _ => do
        let w : W ← OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec (witnessSpec W))
          (.inr (.inl ()))
        return if rel x w then some () else none }

section SendWitness

variable {X W : Type} (rel : X → W → Prop) [∀ x w, Decidable (rel x w)]

theorem sendWitness_outputOn (x : X) (τ : Transcript (witnessSpec W)) :
    (sendWitness rel).verifier.outputOn x τ = if rel x τ.1 then some () else none :=
  rfl

/-- Sending the witness is perfectly complete. -/
theorem sendWitness_complete : (sendWitness rel).Complete World.plain rel Accept 0 := by
  intro x w hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [sendWitness, runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind]
  refine le_of_eq ((PMF.toOuterMeasure_pure_apply _ _).trans
    (ite_eq_right fun h => h ⟨?_, trivial⟩))
  exact (sendWitness_outputOn rel x _).trans (ite_eq_left hxw)

/-- **Sending the witness is knowledge sound with error `0`**, with the extractor that reads the
witness off the transcript. -/
theorem sendWitness_knowledgeSound :
    (sendWitness rel).verifier.KnowledgeSound rel Accept (fun _ τ _ => τ.1) 0 := by
  intro x P
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  refine le_of_eq ((congrArg _ (Set.eq_empty_of_forall_notMem fun r hr => ?_)).trans
    (MeasureTheory.measure_empty))
  obtain ⟨⟨x', hout, -⟩, hnot⟩ := hr
  change (sendWitness rel).verifier.outputOn x r.1 = some x' at hout
  rw [sendWitness_outputOn] at hout
  split_ifs at hout with h
  exact hnot h

end SendWitness

/-! ### A verifier that is not knowledge sound -/

/-- The verifier that accepts without interaction. -/
def trustMe : Verifier OracleSpec.empty [] Unit Unit where
  samplers := ()
  decide _ _ := pure (some ())

/-- `trustMe` is not knowledge sound for the empty relation, with any extractor and any error
below `1`: the prover that ends with the trivial output witness always succeeds. -/
theorem not_trustMe_knowledgeSound (E : Unit → Transcript [] → Unit → Unit) {ε : ℝ≥0∞}
    (hε : ε < 1) : ¬ trustMe.KnowledgeSound (fun _ _ => False) Accept E ε := by
  intro h
  have hk := h () (pure ())
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply] at hk
  simp only [runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind] at hk
  rw [PMF.toOuterMeasure_pure_apply, ite_eq_left (show _ from ⟨⟨(), rfl, trivial⟩, not_false⟩)]
    at hk
  exact absurd hk (not_le.mpr hε)

/-- When every statement has a witness, knowledge soundness without an efficiency requirement holds
with error `0` for every verifier, here `trustMe`. -/
example : trustMe.KnowledgeSound (fun _ _ => True) Accept (fun _ _ _ => ()) 0 :=
  knowledgeSound_of_sound _ (fun _ _ _ _ => trivial) fun _ hx => absurd ⟨(), trivial⟩ hx

/-! ### Sumcheck -/

section Sumcheck

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (d : ℕ)
  (P : MvPolynomial (Fin n) F)

/-- Each sumcheck round is knowledge sound with the trivial extractor and error `d / |F|`; the
relations have no witnesses. -/
theorem sumcheck_round_knowledgeSound (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (Sumcheck.round d P i).verifier.KnowledgeSound (Sumcheck.rel P i) (Sumcheck.rel P (i + 1))
      (fun _ _ _ => ()) ((d : ℝ≥0∞) / Fintype.card F) := by
  refine knowledgeSound_of_sound _ (fun _ ⟨⟨⟩, hx⟩ _ _ => hx) ?_
  simpa [PerChallenge.sum] using (Sumcheck.round_rbrSound d P hP hi).sound

/-- Two sumcheck rounds in sequence are knowledge sound with the sum of the errors, by
`Verifier.KnowledgeSound.append`. -/
example (hP : ∀ j, P.degreeOf j ≤ d) (hn : 2 ≤ n) :
    ((Sumcheck.round d P 0).verifier.append (Sumcheck.round d P 1).verifier).KnowledgeSound
      (Sumcheck.rel P 0) (Sumcheck.rel P 2)
      ((Sumcheck.round d P 0).verifier.extractAppend (fun _ _ _ => ()) (fun _ _ _ => ())
        (fun _ => 0, 0))
      ((d : ℝ≥0∞) / Fintype.card F + (d : ℝ≥0∞) / Fintype.card F) :=
  (sumcheck_round_knowledgeSound d P hP (by omega)).append
    (sumcheck_round_knowledgeSound d P hP (by omega)) _

/-- Sumcheck with the final check is knowledge sound with the trivial extractor and error
`n * (d / |F|)`. -/
example (hP : ∀ j, P.degreeOf j ≤ d) :
    (Sumcheck.proof d P).verifier.KnowledgeSound (Sumcheck.rel P 0) Accept (fun _ _ _ => ())
      (n * ((d : ℝ≥0∞) / Fintype.card F)) :=
  knowledgeSound_of_sound _ (fun _ ⟨⟨⟩, hx⟩ _ _ => hx) <| by
    simpa [language, Accept] using Sumcheck.proof_sound d P hP

/-- The simulator for a sumcheck round: the honest round polynomial and a uniform challenge. -/
noncomputable def roundSim (i : ℕ) (x : Sumcheck.Claim F i) :
    ProbComp (Transcript (Sumcheck.roundSpec F)) := do
  let z ← ProbComp.uniform F
  return (Sumcheck.roundPoly P x.1, (z, ()))

/-- A sumcheck round is perfectly honest-verifier zero knowledge. -/
theorem sumcheck_round_hvzk (i : ℕ) :
    (Sumcheck.round d P i).HVZK (Sumcheck.rel P i) (roundSim P i) 0 := by
  intro x w _
  have hlaw : (World.plain.eval ((Sumcheck.round d P i).run x w)).map Prod.fst =
      ProbComp.eval (roundSim P i x) := by
    rw [Reduction.run, World.plain_eval_execute, PMF.map_comp]
    simp only [Sumcheck.round, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample,
      PMF.pure_bind, PMF.bind_bind, roundSim, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [← PMF.bind_pure_comp, PMF.bind_bind]
    congr 1
    funext z
    rw [PMF.pure_bind]
    rfl
  rw [hlaw]
  intro event
  rw [add_zero]

end Sumcheck

/-- Sending the witness is not honest-verifier zero knowledge with error below `1/2`, with any
simulator, for a statement with two witnesses: the transcript is the witness. -/
theorem not_sendWitness_hvzk (Sim : Unit → ProbComp (Transcript (witnessSpec Bool)))
    {ε : ℝ≥0∞} (hε : 2 * ε < 1) :
    ¬ (sendWitness fun (_ : Unit) (_ : Bool) => True).HVZK (fun _ _ => True) Sim ε := by
  intro h
  have hlaw : ∀ b, (World.plain.eval ((sendWitness fun (_ : Unit) (_ : Bool) => True).run () b)).map
      Prod.fst = PMF.pure (b, ()) := fun b => by
    rw [Reduction.run, World.plain_eval_execute, PMF.map_comp]
    simp only [sendWitness, runStrategy, plainLaw_bind, plainLaw_pure, PMF.pure_bind, PMF.pure_map]
    rfl
  set A : Set (Transcript (witnessSpec Bool)) := {τ | τ.1 = true}
  have h₁ := h () true trivial A
  have h₂ := h () false trivial Aᶜ
  rw [hlaw, PMF.toOuterMeasure_pure_apply, ite_eq_left (show (true, ()) ∈ A from rfl)] at h₁
  rw [hlaw, PMF.toOuterMeasure_pure_apply,
    ite_eq_left (show (false, ()) ∈ Aᶜ from Bool.false_ne_true)] at h₂
  have hsum : (ProbComp.eval (Sim ())).toOuterMeasure A +
      (ProbComp.eval (Sim ())).toOuterMeasure Aᶜ = 1 := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
    simp only [Set.indicator_self_add_compl_apply]
    exact PMF.tsum_coe _
  have h2 : (2 : ℝ≥0∞) ≤ 1 + 2 * ε :=
    calc (2 : ℝ≥0∞) = 1 + 1 := one_add_one_eq_two.symm
      _ ≤ ((ProbComp.eval (Sim ())).toOuterMeasure A + ε) +
          ((ProbComp.eval (Sim ())).toOuterMeasure Aᶜ + ε) := add_le_add h₁ h₂
      _ = 1 + 2 * ε := by rw [add_add_add_comm, hsum, two_mul]
  exact absurd (h2.trans_lt (ENNReal.add_lt_add_left ENNReal.one_ne_top hε))
    (by rw [one_add_one_eq_two]; exact lt_irrefl 2)

end ComplexityTests.InteractiveKnowledgeSound
