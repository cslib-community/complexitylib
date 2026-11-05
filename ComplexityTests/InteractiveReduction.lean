/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Interactive.AuxZK
import Complexity.Computability.Interactive.Sumcheck
import ComplexityTests.EfficientSimulators
import ComplexityTests.InteractiveKnowledgeSound
import ComplexityTests.UnboundedSimulators

/-!
# Tests for auxiliary-input zero knowledge and product composition of interactive reductions

This test module exercises `Complexity.Computability.Interactive.AuxZK`:

1. **Auxiliary-input zero knowledge** (`PerfectHVZK`, `AuxHVZK`, `PerfectAuxHVZK`, `Reduction.ZK`,
   `EfficientAuxHVZK`, `ComputationalHVZK`, `ComputationalAuxHVZK`):
   * Positive instances on `sendWitness (fun x w => w = x)` and `Sumcheck.round`, including
     malicious-verifier zero knowledge (`Reduction.ZK`) and its specialization to `AuxHVZK` via
     `Reduction.ZK.auxHVZK`, lifting from `HVZK` / `PerfectHVZK` / `EfficientHVZK` /
     `ComputationalHVZK`, and the statistical-to-computational bridges.
   * Negative separation for `AuxHVZK` when two witnesses produce distinct transcripts
     (`not_auxHVZK_sendWitness_twoWitness`), and negative separation for `EfficientAuxHVZK` on
     `sendWitnessDL` under the discrete-logarithm assumption (`not_efficientAuxHVZK_sendWitnessDL`).
2. **Product (AND) and disjunctive (OR) relations and product composition** (`relProd`, `relDisj`,
   `Verifier.seqProd`, `Reduction.seqProd`):
   * Completeness (`Reduction.Complete.seqProd_zero`), soundness (`Verifier.Sound.seqProd`),
     straight-line knowledge soundness (`Verifier.KnowledgeSound.seqProd`), and `HVZK` /
     `PerfectHVZK` / `AuxHVZK` / `PerfectAuxHVZK` preservation (`Reduction.HVZK.seqProd`,
     `Reduction.PerfectHVZK.seqProd`, `Reduction.AuxHVZK.seqProd`,
     `Reduction.PerfectAuxHVZK.seqProd`) on concrete product reductions (`sendWitness` products and
     two-instance `Sumcheck.round` products).
-/

namespace ComplexityTests.InteractiveReduction

open Cslib Cslib.Interactive Spec Probability Turing.MultiTapeTM Crypto
open ComplexityTests.InteractiveKnowledgeSound
open ComplexityTests.UnboundedSimulators
open ComplexityTests.EfficientSimulators
open scoped ENNReal NNReal

/-! ### Part 1: Auxiliary-input zero knowledge and malicious-verifier ZK -/

/-- The equality relation `w = x` on bit words. -/
abbrev eqRel (x w : List Bool) : Prop := w = x

/-- `sendWitness eqRel` is perfectly HVZK: on valid `(x, w)` with `w = x`, the honest transcript is
deterministically `(x, ())`. -/
theorem perfectHVZK_sendWitness_eqRel :
    (sendWitness eqRel).PerfectHVZK eqRel (fun x => pure (x, ())) := by
  intro x w hxw
  rw [Reduction.honestTranscript, sendWitness_transcript, hxw, ProbComp.eval_pure]

/-- Lifting `perfectHVZK_sendWitness_eqRel` yields `PerfectAuxHVZK` for any auxiliary input type
`Aux`. -/
example {Aux : Type} :
    (sendWitness eqRel).PerfectAuxHVZK eqRel (fun x (_ : Aux) => pure (x, ())) :=
  perfectHVZK_sendWitness_eqRel.perfectAuxHVZK

/-- Lifting `perfectHVZK_sendWitness_eqRel` yields `0`-error `AuxHVZK` for any auxiliary input type
`Aux`. -/
example {Aux : Type} :
    (sendWitness eqRel).AuxHVZK eqRel (fun x (_ : Aux) => pure (x, ())) (fun _ _ => 0) :=
  perfectHVZK_sendWitness_eqRel.hvzk.auxHVZK

/-- Malicious-verifier simulator for `sendWitness eqRel`: run `Vstar x z` in the plain model and
feed the statement `x` as the prover's message. -/
noncomputable def simMaliciousSendWitness {Aux View : Type}
    (Vstar : List Bool → Aux →
      ProbOracleComp OracleSpec.empty
        (VerifierStrategy (ProbOracleComp OracleSpec.empty) (witnessSpec (List Bool)) View))
    (x : List Bool) (z : Aux) : ProbComp View :=
  closeProgram do
    let v ← Vstar x z
    let v' ← v x
    v'

/-- `sendWitness eqRel` satisfies malicious-verifier auxiliary-input zero knowledge
(`Reduction.ZK`) with error `0`. -/
theorem zk_sendWitness_eqRel {Aux View : Type} :
    (sendWitness eqRel).ZK eqRel (simMaliciousSendWitness (Aux := Aux) (View := View))
      (fun _ _ => 0) := by
  intro Vstar x w z hxw
  rw [simMaliciousSendWitness, eval_closeProgram, Reduction.viewOf, hxw]
  have heq :
      (plainLaw do
        let p ← (sendWitness eqRel).prover x x
        let v ← Vstar x z
        let r ← runAgainst (witnessSpec (List Bool)) p v
        return r.2.2) =
      (plainLaw do
        let v ← Vstar x z
        let v' ← v x
        v') := by
    simp [sendWitness, runAgainst, plainLaw_bind]
  rw [heq]
  exact CloseTo.refl _

/-- Specializing `zk_sendWitness_eqRel` via `Reduction.ZK.auxHVZK` recovers `AuxHVZK` against the
honest verifier. -/
example {Aux : Type} :
    (sendWitness eqRel).AuxHVZK eqRel
      (simMaliciousSendWitness
        (fun _ (_ : Aux) =>
          pure (honestVerifierStrategy (witnessSpec (List Bool))
            (sendWitness eqRel).verifier.samplers)))
      (fun _ _ => 0) :=
  (zk_sendWitness_eqRel (Aux := Aux)).auxHVZK

/-- **Negative test for `AuxHVZK`**: `sendWitness (fun _ _ => True)` reveals the witness bit, so no
auxiliary-input simulator can be `ε`-close to both honest transcripts when `2 * ε () z₀ < 1`. -/
theorem not_auxHVZK_sendWitness_twoWitness {Aux : Type} (z₀ : Aux)
    (Sim : Unit → Aux → ProbComp (Transcript (witnessSpec Bool)))
    {ε : Unit → Aux → ℝ≥0∞} (hε : 2 * ε () z₀ < 1) :
    ¬ (sendWitness fun (_ : Unit) (_ : Bool) => True).AuxHVZK (fun _ _ => True) Sim ε :=
  fun h => not_sendWitness_hvzk (fun x => Sim x z₀) hε (h.hvzk z₀ fun _ => le_rfl)

/-! ### Efficient and computational auxiliary-input HVZK -/

/-- `sendWitness eqRel` is efficiently HVZK with zero simulation and realization error. -/
theorem efficientHVZK_sendWitness_eqRel :
    Reduction.EfficientHVZK (fun _ : ℕ => sendWitness eqRel)
      (fun _ => eqRel) wordEncoding (fun _ x => pure (x, ())) (fun _ => 0) (fun _ => 0) where
  hvzk _ := perfectHVZK_sendWitness_eqRel.hvzk
  realized := ⟨fun p => pure p.2, (ComputableInPolyTime.snd _ _).isPPTOn, fun _ x => by
    rw [ProbComp.eval_pure, ProbComp.eval_pure, PMF.pure_map]
    exact CloseTo.refl (PMF.pure x)⟩

/-- Lifting `efficientHVZK_sendWitness_eqRel` yields `EfficientAuxHVZK` for any encoded auxiliary
input family `encAux`. -/
theorem efficientAuxHVZK_sendWitness_eqRel {AuxI : ℕ → Type} (encAux : ∀ n, AuxI n ↪ List Bool) :
    Reduction.EfficientAuxHVZK (fun _ : ℕ => sendWitness eqRel)
      (fun _ => eqRel) wordEncoding encAux (fun _ x _ => pure (x, ()))
      (fun _ => 0) (fun _ => 0) :=
  efficientHVZK_sendWitness_eqRel.efficientAuxHVZK encAux

/-- `efficientHVZK_sendWitness_eqRel` implies `ComputationalHVZK`. -/
theorem exists_computationalHVZK_sendWitness_eqRel :
    ∃ program, Reduction.ComputationalHVZK (fun _ : ℕ => sendWitness eqRel)
      (fun _ => eqRel) wordEncoding program :=
  efficientHVZK_sendWitness_eqRel.exists_computationalHVZK_zero

/-- Lifting `ComputationalHVZK` yields `ComputationalAuxHVZK` for any encoded auxiliary input
family `encAux`. -/
theorem exists_computationalAuxHVZK_sendWitness_eqRel
    {AuxI : ℕ → Type} (encAux : ∀ n, AuxI n ↪ List Bool) :
    ∃ program, Reduction.ComputationalAuxHVZK (fun _ : ℕ => sendWitness eqRel)
      (fun _ => eqRel) wordEncoding encAux program := by
  obtain ⟨program, hcomp⟩ := exists_computationalHVZK_sendWitness_eqRel
  exact ⟨_, hcomp.computationalAuxHVZK encAux⟩

/-- **Negative test for `EfficientAuxHVZK` under the discrete-logarithm assumption**: sending the
discrete-logarithm witness is not `EfficientAuxHVZK` with `ε i + δ i ≤ 1 / 2`, even for trivial
(`Unit`) auxiliary inputs. -/
theorem not_efficientAuxHVZK_sendWitnessDL {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDL : F.DiscreteLog setup)
    (Sim : ∀ i : ℕ × F.Desc, F.Carrier i.2 → Unit →
      ProbComp (Transcript (witnessSpec (ZMod (F.order i.2)))))
    {ε δ : ℕ × F.Desc → ℝ≥0∞} (hεδ : ∀ i, ε i + δ i ≤ 1 / 2) :
    ¬ Reduction.EfficientAuxHVZK (sendWitnessDL F) (dlStmtRel F) (sendWitnessDLEncoding F)
      (fun _ => encUnit) Sim ε δ := by
  intro h
  refine not_efficientHVZK_sendWitnessDL hDL (fun i x => Sim i x ()) hεδ ?_
  refine ⟨fun i => (h.auxHVZK i).hvzk () fun _ => le_rfl, ?_⟩
  obtain ⟨program, hppt, hreal⟩ := h.realized
  refine ⟨fun p => program (p.1, p.2, encUnit ()), ?_, fun i x => hreal i x ()⟩
  exact hppt.preprocess
    (prepare := fun p : (ℕ × F.Desc) × List Bool => (p.1, p.2, encUnit ())) (by fun_prop)

/-! ### Part 2: Product (AND) and disjunctive (OR) relations and `seqProd` -/

/-- Product of two `sendWitness` reductions over `s₁ ++ s₂`. -/
noncomputable abbrev sendWitnessProd {X₁ W₁ X₂ W₂ : Type}
    (rel₁ : X₁ → W₁ → Prop) (rel₂ : X₂ → W₂ → Prop)
    [∀ x₁ w₁, Decidable (rel₁ x₁ w₁)] [∀ x₂ w₂, Decidable (rel₂ x₂ w₂)] :
    Reduction OracleSpec.empty OracleSpec.empty
      (witnessSpec W₁ ++ witnessSpec W₂) (X₁ × X₂) (W₁ × W₂) (Unit × Unit) (Unit × Unit) :=
  (sendWitness rel₁).seqProd (sendWitness rel₂)

section ProductTests

variable {X₁ W₁ X₂ W₂ : Type}
  (rel₁ : X₁ → W₁ → Prop) (rel₂ : X₂ → W₂ → Prop)
  [∀ x₁ w₁, Decidable (rel₁ x₁ w₁)] [∀ x₂ w₂, Decidable (rel₂ x₂ w₂)]

/-- `sendWitnessProd` is perfectly complete for `relProd rel₁ rel₂`. -/
theorem sendWitnessProd_complete :
    (sendWitnessProd rel₁ rel₂).Complete World.plain
      (relProd rel₁ rel₂) (relProd Accept Accept) 0 :=
  (sendWitness_complete rel₁).seqProd_zero (sendWitness_complete rel₂)

/-- The verifier of `sendWitnessProd` is straight-line knowledge sound with error `0` using the
product extractor `Verifier.extractSeqProd`. -/
theorem sendWitnessProd_knowledgeSound :
    (sendWitnessProd rel₁ rel₂).verifier.KnowledgeSound
      (relProd rel₁ rel₂) (relProd Accept Accept)
      (Verifier.extractSeqProd (fun _ (τ₁ : Transcript (witnessSpec W₁)) _ => τ₁.1)
        (fun _ (τ₂ : Transcript (witnessSpec W₂)) _ => τ₂.1)) 0 := by
  simpa using (sendWitness_knowledgeSound rel₁).seqProd (sendWitness_knowledgeSound rel₂)

/-- The verifier of `sendWitnessProd` has soundness error `0` for `language (relProd rel₁ rel₂)`. -/
theorem sendWitnessProd_sound :
    (sendWitnessProd rel₁ rel₂).verifier.Sound (oP := OracleSpec.empty) World.plain
      (language (relProd rel₁ rel₂)) (language (relProd Accept Accept)) 0 := by
  rw [language_relProd, language_relProd]
  simpa using (sound_of_knowledgeSound (sendWitness_knowledgeSound rel₁)).seqProd
    (sound_of_knowledgeSound (sendWitness_knowledgeSound rel₂))

end ProductTests

/-- Product of two `sendWitness eqRel` reductions is perfectly HVZK
(`Reduction.PerfectHVZK.seqProd`). -/
theorem perfectHVZK_sendWitnessProd_eqRel :
    (sendWitnessProd eqRel eqRel).PerfectHVZK (relProd eqRel eqRel)
      (simSeqProd (fun x => pure (x, ())) (fun x => pure (x, ()))) :=
  perfectHVZK_sendWitness_eqRel.seqProd perfectHVZK_sendWitness_eqRel

/-- Product of two `sendWitness eqRel` reductions is `0`-error HVZK (`Reduction.HVZK.seqProd`). -/
example :
    (sendWitnessProd eqRel eqRel).HVZK (relProd eqRel eqRel)
      (simSeqProd (fun x => pure (x, ())) (fun x => pure (x, ()))) 0 := by
  simpa using perfectHVZK_sendWitness_eqRel.hvzk.seqProd perfectHVZK_sendWitness_eqRel.hvzk

/-- Product of two `sendWitness eqRel` reductions is `PerfectAuxHVZK`
(`Reduction.PerfectAuxHVZK.seqProd`). -/
example {Aux : Type} :
    (sendWitnessProd eqRel eqRel).PerfectAuxHVZK (relProd eqRel eqRel)
      (auxSimSeqProd (fun x (_ : Aux) => pure (x, ())) (fun x (_ : Aux) => pure (x, ()))) :=
  perfectHVZK_sendWitness_eqRel.perfectAuxHVZK.seqProd
    perfectHVZK_sendWitness_eqRel.perfectAuxHVZK

/-- Product of two `sendWitness eqRel` reductions is `0`-error `AuxHVZK`
(`Reduction.AuxHVZK.seqProd`). -/
example {Aux : Type} :
    (sendWitnessProd eqRel eqRel).AuxHVZK (relProd eqRel eqRel)
      (auxSimSeqProd (fun x (_ : Aux) => pure (x, ())) (fun x (_ : Aux) => pure (x, ())))
      (fun _ _ => 0) := by
  simpa using
    (perfectHVZK_sendWitness_eqRel.hvzk.auxHVZK (Aux := Aux)).seqProd
      (perfectHVZK_sendWitness_eqRel.hvzk.auxHVZK (Aux := Aux))

/-! ### Product of two sumcheck rounds -/

section SumcheckProduct

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
  (d₁ d₂ : ℕ) (P₁ P₂ : MvPolynomial (Fin n) F)

/-- Perfect completeness of the product of two sumcheck rounds. -/
example (hP₁ : ∀ j, P₁.degreeOf j ≤ d₁) (hP₂ : ∀ j, P₂.degreeOf j ≤ d₂)
    {i : ℕ} (hi : i < n) :
    ((Sumcheck.round d₁ P₁ i).seqProd (Sumcheck.round d₂ P₂ i)).Complete World.plain
      (relProd (Sumcheck.rel P₁ i) (Sumcheck.rel P₂ i))
      (relProd (Sumcheck.rel P₁ (i + 1)) (Sumcheck.rel P₂ (i + 1))) 0 :=
  (Sumcheck.round_complete d₁ P₁ hP₁ hi).seqProd_zero (Sumcheck.round_complete d₂ P₂ hP₂ hi)

/-- Soundness of the product of two sumcheck rounds with degree bounds `d₁` and `d₂`, achieving
error `max (d₁ / |F|) (d₂ / |F|)`. -/
example (hP₁ : ∀ j, P₁.degreeOf j ≤ d₁) (hP₂ : ∀ j, P₂.degreeOf j ≤ d₂)
    {i : ℕ} (hi : i < n) :
    ((Sumcheck.round d₁ P₁ i).verifier.seqProd (Sumcheck.round d₂ P₂ i).verifier).Sound
      (oP := OracleSpec.empty) World.plain
      (language (relProd (Sumcheck.rel P₁ i) (Sumcheck.rel P₂ i)))
      (language (relProd (Sumcheck.rel P₁ (i + 1)) (Sumcheck.rel P₂ (i + 1))))
      (max ((d₁ : ℝ≥0∞) / Fintype.card F) ((d₂ : ℝ≥0∞) / Fintype.card F)) := by
  rw [language_relProd, language_relProd]
  have hs₁ : (Sumcheck.round d₁ P₁ i).verifier.Sound (oP := OracleSpec.empty) World.plain
      (language (Sumcheck.rel P₁ i)) (language (Sumcheck.rel P₁ (i + 1)))
      ((d₁ : ℝ≥0∞) / Fintype.card F) := by
    simpa [PerChallenge.sum] using (Sumcheck.round_rbrSound d₁ P₁ hP₁ hi).sound
  have hs₂ : (Sumcheck.round d₂ P₂ i).verifier.Sound (oP := OracleSpec.empty) World.plain
      (language (Sumcheck.rel P₂ i)) (language (Sumcheck.rel P₂ (i + 1)))
      ((d₂ : ℝ≥0∞) / Fintype.card F) := by
    simpa [PerChallenge.sum] using (Sumcheck.round_rbrSound d₂ P₂ hP₂ hi).sound
  exact hs₁.seqProd hs₂

/-- Auxiliary-input HVZK of the product of two sumcheck rounds. -/
example {Aux : Type} (i : ℕ) :
    ((Sumcheck.round d₁ P₁ i).seqProd (Sumcheck.round d₂ P₂ i)).AuxHVZK
      (relProd (Sumcheck.rel P₁ i) (Sumcheck.rel P₂ i))
      (auxSimSeqProd (fun x (_ : Aux) => roundSim P₁ i x) (fun x (_ : Aux) => roundSim P₂ i x))
      (fun _ _ => 0) := by
  simpa using
    ((sumcheck_round_hvzk d₁ P₁ i).auxHVZK (Aux := Aux)).seqProd
      ((sumcheck_round_hvzk d₂ P₂ i).auxHVZK (Aux := Aux))

end SumcheckProduct

end ComplexityTests.InteractiveReduction
