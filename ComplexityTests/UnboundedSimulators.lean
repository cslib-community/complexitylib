/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Interactive.Plain
import Complexity.Computability.Interactive.Security
import Complexity.Crypto.Protocols.SigmaProtocol.Basic

/-!
# Zero knowledge and special soundness with unbounded simulators and extractors

`Interactive.Reduction.HVZK`, `SigmaProtocol.SpecialHVZK` and `SigmaProtocol.SpecialSoundness`
take their simulator or extractor as an argument and do not require it to be efficient; their
docstrings say so, and efficiency is a separate layer. This file records what the notions say
without that layer, so that the scope is checked rather than only documented.

* **Interactive HVZK is honest-verifier witness indistinguishability.** In the plain model, the
  simulator that runs the honest prover on a chosen witness (`choiceSim`) makes a reduction
  `ε`-HVZK as soon as the honest transcript laws of any two witnesses of a statement are
  `ε`-close (`hvzk_choiceSim`); conversely, `ε`-HVZK with any simulator makes them `2ε`-close
  (`closeTo_of_hvzk`). For a relation with at most one witness per statement, every plain
  reduction is perfectly HVZK (`hvzk_of_unique`), including one whose prover sends its witness.
* **Special soundness is soundness of the language.** Some extractor makes a Sigma protocol
  special sound exactly when every statement with two accepting conversations on a common
  commitment and distinct challenges has a witness (`exists_specialSoundness_iff`). For a
  relation in which every statement has a witness, every Sigma protocol is special sound, even one
  whose verifier accepts everything (`trustMeSigma`).
* **Special HVZK holds for every complete protocol for a total relation with unique witnesses**
  (`specialHVZK_choice`), such as discrete logarithms to a generator of a group of prime order.
  The protocol `sendWitnessSigma`, whose commitment and response are the witness itself, is
  complete, special sound with the extractor that reads the witness off the commitment, and
  special HVZK for such a relation (`sendWitnessSigma_specialHVZK`), although every honest
  conversation reveals the witness (`sendWitnessSigma_conversation_fst`).

A meaningful instance of any of these notions needs an efficient simulator or extractor.
-/

namespace ComplexityTests.UnboundedSimulators

open Cslib Cslib.Interactive Spec
open scoped ENNReal

/-! ### Statistical closeness -/

theorem toOuterMeasure_add_compl {α : Type} (μ : PMF α) (E : Set α) :
    μ.toOuterMeasure E + μ.toOuterMeasure Eᶜ = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  simp only [Set.indicator_self_add_compl_apply]
  exact PMF.tsum_coe _

/-- Statistical closeness is symmetric. -/
theorem closeTo_symm {α : Type} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) :
    CloseTo ν μ ε := fun E => by
  have hc := h Eᶜ
  have hne : ν.toOuterMeasure Eᶜ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq (toOuterMeasure_add_compl ν E))
  refine WithTop.le_of_add_le_add_right hne ?_
  calc ν.toOuterMeasure E + ν.toOuterMeasure Eᶜ = 1 := toOuterMeasure_add_compl ν E
    _ = μ.toOuterMeasure E + μ.toOuterMeasure Eᶜ := (toOuterMeasure_add_compl μ E).symm
    _ ≤ μ.toOuterMeasure E + (ν.toOuterMeasure Eᶜ + ε) := add_le_add le_rfl hc
    _ = μ.toOuterMeasure E + ε + ν.toOuterMeasure Eᶜ := by rw [add_comm _ ε, add_assoc]

theorem closeTo_refl {α : Type} (μ : PMF α) : CloseTo μ μ 0 := fun _ => by rw [add_zero]

/-! ### Interactive HVZK -/

/-- A prover-side program without oracles, as a closed probabilistic program. -/
noncomputable def closeProgram {α : Type} (p : ProbOracleComp OracleSpec.empty α) : ProbComp α :=
  OracleComp.interpret (ProbOracleComp.handler ProbComp.unifFin fun e => e.elim) p

theorem eval_closeProgram {α : Type} (p : ProbOracleComp OracleSpec.empty α) :
    ProbComp.eval (closeProgram p) = plainLaw p := by
  rw [ProbComp.eval, closeProgram, OracleComp.interpret_interpret, plainLaw]
  congr 1
  funext q
  rcases q with n | e
  · exact ProbComp.eval_unifFin n
  · exact e.elim

variable {s : Spec} {StmtIn WitIn StmtOut WitOut : Type}

/-- The law of the honest transcript on `(x, w)`. -/
noncomputable def honestLaw
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (x : StmtIn) (w : WitIn) : PMF (Transcript s) :=
  (plainLaw (R.prover x w >>= runStrategy s R.verifier.samplers)).map Prod.fst

theorem map_fst_eval_run
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (x : StmtIn) (w : WitIn) :
    (World.plain.eval (R.run x w)).map Prod.fst = honestLaw R x w := by
  rw [Reduction.run, World.plain_eval_execute, PMF.map_comp]
  rfl

/-- The simulator that runs the honest prover on a witness of the statement, whenever one exists.
It is not efficient: it chooses the witness. -/
noncomputable def choiceSim [Nonempty WitIn]
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (x : StmtIn) : ProbComp (Transcript s) :=
  Prod.fst <$> closeProgram
    (R.prover x (Classical.epsilon (relIn x)) >>= runStrategy s R.verifier.samplers)

theorem eval_choiceSim [Nonempty WitIn]
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    (relIn : StmtIn → WitIn → Prop) (x : StmtIn) :
    ProbComp.eval (choiceSim R relIn x) = honestLaw R x (Classical.epsilon (relIn x)) := by
  rw [choiceSim, ProbComp.eval_map, eval_closeProgram, honestLaw]

/-- **Honest-verifier witness indistinguishability gives HVZK** with the choice simulator: if the
honest transcript laws of any two witnesses of a statement are `ε`-close, the reduction is
`ε`-HVZK. -/
theorem hvzk_choiceSim [Nonempty WitIn]
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {ε : ℝ≥0∞}
    (h : ∀ x w w', relIn x w → relIn x w' → CloseTo (honestLaw R x w) (honestLaw R x w') ε) :
    R.HVZK relIn (choiceSim R relIn) ε := by
  intro x w hw
  rw [map_fst_eval_run, eval_choiceSim]
  exact h x w _ hw (Classical.epsilon_spec ⟨w, hw⟩)

/-- **HVZK gives honest-verifier witness indistinguishability**: with any simulator, `ε`-HVZK
makes the honest transcript laws of any two witnesses `2ε`-close. -/
theorem closeTo_of_hvzk
    {R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut}
    {relIn : StmtIn → WitIn → Prop} {Sim : StmtIn → ProbComp (Transcript s)} {ε : ℝ≥0∞}
    (h : R.HVZK relIn Sim ε) {x : StmtIn} {w w' : WitIn} (hw : relIn x w) (hw' : relIn x w') :
    CloseTo (honestLaw R x w) (honestLaw R x w') (ε + ε) := by
  have h₁ := h x w hw
  have h₂ := h x w' hw'
  rw [map_fst_eval_run] at h₁ h₂
  exact CloseTo.trans h₁ (closeTo_symm h₂)

/-- **With unique witnesses, every plain reduction is perfectly HVZK**, for the choice
simulator; for instance one whose prover sends its witness. -/
theorem hvzk_of_unique [Nonempty WitIn]
    (R : Reduction OracleSpec.empty OracleSpec.empty s StmtIn WitIn StmtOut WitOut)
    {relIn : StmtIn → WitIn → Prop} (huniq : ∀ x w w', relIn x w → relIn x w' → w = w') :
    R.HVZK relIn (choiceSim R relIn) 0 :=
  hvzk_choiceSim fun x w w' hw hw' => huniq x w w' hw hw' ▸ closeTo_refl _

/-! ### Sigma protocols -/

namespace Sigma

open Probability Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SigmaProtocol

variable {X Y T C Z : Type}

/-- **Special soundness without an efficiency requirement is soundness of the language**: some
extractor exists exactly when two accepting conversations on a common commitment with distinct
challenges certify that the statement has a witness. -/
theorem exists_specialSoundness_iff {W : Type} [Nonempty W] (P : SigmaProtocol X Y T C Z)
    (R : W → Y → Prop) :
    (∃ extract, P.SpecialSoundness R extract) ↔
      ∀ y t c z c' z', c ≠ c' → P.Accepts y t c z → P.Accepts y t c' z' → ∃ x, R x y :=
  ⟨fun ⟨_, h⟩ _ _ _ _ _ _ hc hz hz' => h.exists_witness hc hz hz',
    fun h => ⟨fun y _ _ _ _ _ => Classical.epsilon (R · y),
      fun y t c z c' z' hc hz hz' => Classical.epsilon_spec (h y t c z c' z' hc hz hz')⟩⟩

/-- The Sigma protocol whose verifier accepts every conversation. -/
noncomputable def trustMeSigma (X Y : Type) : SigmaProtocol X Y Unit Bool Unit where
  State := Unit
  commit _ _ := PMF.pure ((), ())
  respond _ _ _ _ := ()
  verify _ _ _ _ := true

/-- For a relation in which every statement has a witness, even `trustMeSigma` is special
sound. -/
example {X Y : Type} [Nonempty X] (R : X → Y → Prop) (htotal : ∀ y, ∃ x, R x y) :
    ∃ extract, (trustMeSigma X Y).SpecialSoundness R extract :=
  (exists_specialSoundness_iff _ R).2 fun y _ _ _ _ _ _ _ _ => htotal y

/-- The simulator that runs the honest prover on a chosen witness. -/
noncomputable def choiceSimulate [Nonempty X] (P : SigmaProtocol X Y T C Z) (R : X → Y → Prop)
    (y : Y) (c : C) : PMF (T × Z) :=
  P.transcript (Classical.epsilon (R · y)) y c

/-- **Special HVZK for a total relation with unique witnesses**: every complete Sigma protocol is
special HVZK, with the simulator that runs the honest prover on the unique witness. -/
theorem specialHVZK_choice [Nonempty X] {P : SigmaProtocol X Y T C Z} {R : X → Y → Prop}
    (hP : P.Complete R) (htotal : ∀ y, ∃ x, R x y) (huniq : ∀ x x' y, R x y → R x' y → x = x') :
    P.SpecialHVZK R (choiceSimulate P R) where
  accepts y c tz htz := hP _ y (Classical.epsilon_spec (htotal y)) c tz htz
  transcript_eq x y hxy c := by
    rw [choiceSimulate, huniq (Classical.epsilon (R · y)) x y
      (Classical.epsilon_spec (p := (R · y)) ⟨x, hxy⟩) hxy]

/-- The Sigma protocol that sends the witness: the commitment and the response are the witness,
and the verifier checks the commitment. -/
noncomputable def sendWitnessSigma (R : X → Y → Prop) [∀ x y, Decidable (R x y)] :
    SigmaProtocol X Y X Bool X where
  State := Unit
  commit x _ := PMF.pure (x, ())
  respond x _ _ _ := x
  verify y t _ _ := decide (R t y)

section SendWitness

variable (R : X → Y → Prop) [∀ x y, Decidable (R x y)]

theorem sendWitnessSigma_transcript (x : X) (y : Y) (c : Bool) :
    (sendWitnessSigma R).transcript x y c = PMF.pure (x, x) := by
  simp only [SigmaProtocol.transcript, sendWitnessSigma, PMF.pure_map]

theorem sendWitnessSigma_complete : (sendWitnessSigma R).Complete R := by
  intro x y hxy c tz htz
  rw [sendWitnessSigma_transcript, PMF.mem_support_pure_iff] at htz
  subst htz
  exact decide_eq_true hxy

/-- Sending the witness is special sound, with the extractor that reads the commitment. -/
theorem sendWitnessSigma_specialSoundness :
    (sendWitnessSigma R).SpecialSoundness R fun _ t _ _ _ _ => t :=
  fun _ _ _ _ _ _ _ hz _ => of_decide_eq_true hz

/-- **Sending the witness is special HVZK** for a total relation with unique witnesses, with the
simulator that runs the honest prover on the unique witness. -/
theorem sendWitnessSigma_specialHVZK [Nonempty X] (htotal : ∀ y, ∃ x, R x y)
    (huniq : ∀ x x' y, R x y → R x' y → x = x') :
    (sendWitnessSigma R).SpecialHVZK R (choiceSimulate (sendWitnessSigma R) R) :=
  specialHVZK_choice (sendWitnessSigma_complete R) htotal huniq

/-- Every honest conversation of `sendWitnessSigma` reveals the witness as its commitment. -/
theorem sendWitnessSigma_conversation_fst (x : X) (y : Y) {tcz : X × Bool × X}
    (h : tcz ∈ ((sendWitnessSigma R).conversation x y).support) : tcz.1 = x := by
  rw [conversation_eq_bind_transcript] at h
  simp only [sendWitnessSigma_transcript, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, PMF.pure_bind] at h
  obtain ⟨_, -, rfl⟩ := h
  rfl

end SendWitness

/-- A concrete instance: on `ZMod 5`, the relation `x = 2 * y` has exactly one witness per
statement, so the protocol that sends the witness is special HVZK in the library's sense. -/
example : (sendWitnessSigma fun (x y : ZMod 5) => x = 2 * y).SpecialHVZK
    (fun (x y : ZMod 5) => x = 2 * y)
    (choiceSimulate (sendWitnessSigma fun (x y : ZMod 5) => x = 2 * y)
      (fun (x y : ZMod 5) => x = 2 * y)) :=
  sendWitnessSigma_specialHVZK _ (fun y => ⟨2 * y, rfl⟩) fun _ _ _ h h' => h.trans h'.symm

end Sigma

end ComplexityTests.UnboundedSimulators
