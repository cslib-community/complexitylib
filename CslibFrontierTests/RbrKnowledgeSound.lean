/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Interactive.RbrKnowledge
import CslibFrontier.Computability.Interactive.Sumcheck
import CslibFrontierTests.EfficientSimulators
import CslibFrontierTests.InteractiveKnowledgeSound

/-!
# Tests for round-by-round knowledge soundness

Concrete instances, composition checks, and nonvacuity separations for
`Interactive.Verifier.RbrKnowledgeSound`:

* `sendWitness_rbrKnowledgeSound`: the one-message witness-sending protocol is round-by-round
  knowledge sound with error `()`, yielding both `KnowledgeSound` with error `0`, `RbrSound`, and
  `EfficientKnowledgeSound` on word encodings.
* `not_trustMe_rbrKnowledgeSound` and `not_sendWitness_rbrKnowledgeSound_neg`: `trustMe` is not
  round-by-round knowledge sound for the empty relation, and on the total equality relation
  `fun x w : Bool => w = x` (where `RbrSound` holds vacuously because every statement has a
  witness), `sendWitness` is not `RbrKnowledgeSound` for the flipped extractor `fun x _ _ => !x`.
* `pairCheck`: a two-round prover-message / random-bit-challenge reduction for a pair of Booleans,
  proved perfectly complete and round-by-round knowledge sound with challenge error `1 / 2`, then
  composed with itself via `Verifier.RbrKnowledgeSound.seqProd`.
* `sumcheck_round_rbrKnowledgeSound`: sumcheck rounds upgrade from `RbrSound` to
  `RbrKnowledgeSound` and compose via `Verifier.RbrKnowledgeSound.seq` and
  `Verifier.RbrKnowledgeSound.iterate`.
-/

namespace ComplexityTests.RbrKnowledgeSound

open Cslib Cslib.Interactive Spec Probability Turing.MultiTapeTM
open ComplexityTests.InteractiveKnowledgeSound
open ComplexityTests.EfficientSimulators
open scoped ENNReal

/-! ### Witness-sending reduction -/

section SendWitness

variable {X W : Type} (rel : X → W → Prop) [∀ x w, Decidable (rel x w)]

/-- **Sending the witness is round-by-round knowledge sound** with no challenge rounds and the
extractor that reads the witness from the first message. -/
theorem sendWitness_rbrKnowledgeSound :
    (sendWitness rel).verifier.RbrKnowledgeSound rel Accept (fun _ τ _ => τ.1) () := by
  refine ⟨fun _ _ => False, fun _ => not_false,
    fun x => ⟨fun _ _ => not_false, fun w _ ⟨x', _, hout, _, hnot⟩ => ?_⟩⟩
  rw [sendWitness_outputOn] at hout
  split_ifs at hout with h
  exact hnot h

/-- Round-by-round knowledge soundness of `sendWitness` yields straight-line knowledge soundness
with error `0`. -/
theorem sendWitness_knowledgeSound_of_rbr :
    (sendWitness rel).verifier.KnowledgeSound rel Accept (fun _ τ _ => τ.1) 0 :=
  (sendWitness_rbrKnowledgeSound rel).toKnowledgeSound

/-- Round-by-round knowledge soundness of `sendWitness` yields round-by-round soundness for
`language rel`. -/
theorem sendWitness_rbrSound_of_rbr :
    (sendWitness rel).verifier.RbrSound (language rel) (language Accept) () :=
  (sendWitness_rbrKnowledgeSound rel).toRbrSound

end SendWitness

/-- **Round-by-round knowledge soundness with a polynomial-time extractor gives
`EfficientKnowledgeSound`** for sending a word witness. -/
theorem sendWitness_efficientKnowledgeSound
    (rel : List Bool → List Bool → Prop) [∀ x w, Decidable (rel x w)] :
    Verifier.EfficientKnowledgeSound (fun _ => (sendWitness rel).verifier) (fun _ => rel)
      (fun _ => Accept) wordEncoding (fun _ => encUnit) (fun _ => encBits)
      (fun _ _ τ _ => τ.1) (fun _ => 0) :=
  Verifier.RbrKnowledgeSound.efficientKnowledgeSound
    (f := fun p => p.2.2.1)
    (fun _ => sendWitness_rbrKnowledgeSound rel)
    (by fun_prop)
    (fun _ _ _ _ => rfl)

/-! ### Nonvacuity and separation from `RbrSound` on total relations -/

/-- `trustMe` is not round-by-round knowledge sound for the empty relation with any extractor. -/
theorem not_trustMe_rbrKnowledgeSound (E : Unit → Transcript [] → Unit → Unit) :
    ¬ trustMe.RbrKnowledgeSound (fun _ _ => False) Accept E () := by
  intro h
  exact not_trustMe_knowledgeSound E (by norm_num : (0 : ℝ≥0∞) < 1) h.toKnowledgeSound

/-- The equality relation on `Bool`: every statement has a witness (`w = x`). -/
abbrev boolEqRel (x w : Bool) : Prop := w = x

/-- Because every `x : Bool` has a witness in `boolEqRel`, `RbrSound` holds with state `True` on
every statement. -/
theorem sendWitness_boolEqRel_rbrSound :
    (sendWitness boolEqRel).verifier.RbrSound (language boolEqRel) (language Accept) () := by
  refine ⟨fun _ _ => True, fun x hx => False.elim (hx ⟨x, rfl⟩),
    fun _ => rbrFrom_true (witnessSpec Bool) () () _⟩

/-- By contrast, `RbrKnowledgeSound` requires the initial prefix to be doomed on **all** statements
(even when `x ∈ language boolEqRel`), so the wrong extractor `fun x _ _ => !x` is rejected. -/
theorem not_sendWitness_boolEqRel_rbrKnowledgeSound_neg :
    ¬ (sendWitness boolEqRel).verifier.RbrKnowledgeSound boolEqRel Accept
      (fun x _ _ => !x) () := by
  rintro ⟨S, hinit, hround⟩
  have h0 := hinit true
  have h1 := (hround true).1 h0 true
  have h2 := (hround true).2 true h1
  exact h2 ⟨(), (), rfl, trivial, by decide⟩

/-! ### Concrete two-round challenge-checking reduction (`pairCheck`) -/

/-- Two rounds: the prover sends `Bool × Bool`, then the verifier sends a uniform bit `Bool`. -/
abbrev pairSpec : Spec :=
  [.prover (Bool × Bool) (OracleInterface.full (Bool × Bool)), .verifier Bool]

/-- Relation where the witness equals the statement pair of Booleans. -/
abbrev pairRel (x w : Bool × Bool) : Prop := w = x

/-- Acceptance test for `pairCheck` on statement `x`, message `m`, and challenge bit `b`. -/
abbrev pairAccepts (x m : Bool × Bool) (b : Bool) : Prop :=
  cond b m.2 m.1 = cond b x.2 x.1

/-- A two-round reduction for `pairRel`: the prover sends a pair `m : Bool × Bool`, and the
verifier samples a uniform challenge bit `b` and checks coordinate `b` of `m` against `x`. -/
noncomputable def pairCheck :
    Reduction OracleSpec.empty OracleSpec.empty pairSpec (Bool × Bool) (Bool × Bool) Unit Unit where
  prover _ w :=
    pure (show ProbOracleComp OracleSpec.empty
        ((Bool × Bool) × (Bool → ProbOracleComp OracleSpec.empty (Unit × Unit))) from
      pure (w, fun _ => pure ((), ())))
  verifier :=
    { samplers := (ProbComp.uniform Bool, ())
      decide := fun x c => do
        let m : Bool × Bool ←
          OracleComp.query (spec := OracleSpec.empty ⊕ₒ msgSpec pairSpec) (.inr (.inl ()))
        return if pairAccepts x m c.1 then some () else none }

/-- Straight-line extractor for `pairCheck`: reads the prover's pair from the transcript. -/
def pairExtract : (Bool × Bool) → Transcript pairSpec → Unit → Bool × Bool :=
  fun _ τ _ => τ.1

theorem pairCheck_outputOn (x : Bool × Bool) (τ : Transcript pairSpec) :
    pairCheck.verifier.outputOn x τ =
      if pairAccepts x τ.1 τ.2.1 then some () else none :=
  rfl

/-- `pairCheck` is perfectly complete. -/
theorem pairCheck_complete : pairCheck.Complete World.plain pairRel Accept 0 := by
  intro x w hxw
  subst hxw
  rw [Reduction.run, World.plain_eval_execute, PMF.toOuterMeasure_map_apply]
  simp only [pairCheck, runStrategy, plainLaw_bind, plainLaw_pure, plainLaw_sample, PMF.pure_bind,
    PMF.bind_bind]
  rw [PMF.toOuterMeasure_bind_apply]
  refine Probability.PMF.tsum_mul_le_of_forall_le _ fun b => le_of_eq ?_
  refine (PMF.toOuterMeasure_pure_apply _ _).trans
    (ite_eq_right fun h => h ⟨(pairCheck_outputOn w _).trans (ite_eq_left rfl), trivial⟩)

/-- When `m ≠ x`, at most one challenge bit `b : Bool` agrees on the selected coordinate, so a
uniform challenge bit catches a cheating pair with probability at least `1 / 2`. -/
private theorem uniform_bool_pairCheck_le (x m : Bool × Bool) (hne : m ≠ x) :
    (ProbComp.eval (ProbComp.uniform Bool)).toOuterMeasure
      {b : Bool | m ≠ x ∧ pairAccepts x m b} ≤ 1 / 2 := by
  rw [ProbComp.eval_uniform, Probability.PMF.toOuterMeasure_uniformOfFintype]
  have hcard : (Finset.univ.filter
      (fun b : Bool => b ∈ {b : Bool | m ≠ x ∧ pairAccepts x m b})).card ≤ 1 := by
    revert hne
    rcases x with ⟨x₁, x₂⟩
    rcases m with ⟨m₁, m₂⟩
    decide +revert
  have hcard_le : ((Finset.univ.filter
      (fun b : Bool => b ∈ {b : Bool | m ≠ x ∧ pairAccepts x m b})).card :
      ℝ≥0∞) ≤ 1 := by
    exact_mod_cast hcard
  simp only [Fintype.card_bool, Nat.cast_ofNat, one_div]
  calc
    ((Finset.univ.filter
        (fun b : Bool => b ∈ {b : Bool | m ≠ x ∧ pairAccepts x m b})).card :
        ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹
      ≤ 1 * (2 : ℝ≥0∞)⁻¹ := mul_le_mul_of_nonneg_right hcard_le (by positivity)
    _ = (2 : ℝ≥0∞)⁻¹ := one_mul _

/-- **`pairCheck` is round-by-round knowledge sound with challenge error `1 / 2`.** -/
theorem pairCheck_rbrKnowledgeSound :
    pairCheck.verifier.RbrKnowledgeSound pairRel Accept pairExtract (1 / 2, ()) := by
  refine ⟨fun x p => match p with
    | none => False
    | some (_, none) => False
    | some (m, some (b, _)) => m ≠ x ∧ pairAccepts x m b,
    fun _ => not_false, fun x => ⟨fun _ _ => not_false, fun m => ⟨?_, fun b => ?_⟩⟩⟩
  · intro _
    by_cases hne : m = x
    · subst hne
      simp
    · exact uniform_bool_pairCheck_le x m hne
  · rintro hS ⟨_, _, hout, -, hnot⟩
    rw [pairCheck_outputOn] at hout
    split_ifs at hout with hb
    exact hS ⟨hnot, hb⟩

/-- Straight-line knowledge soundness of `pairCheck` with error `1 / 2`, derived from
`pairCheck_rbrKnowledgeSound`. -/
theorem pairCheck_knowledgeSound :
    pairCheck.verifier.KnowledgeSound pairRel Accept pairExtract (1 / 2) := by
  simpa [PerChallenge.sum] using pairCheck_rbrKnowledgeSound.toKnowledgeSound

/-- Sequential product of two `pairCheck` verifiers is round-by-round knowledge sound with
per-round errors `(1 / 2, (1 / 2, ()))`. -/
theorem pairCheck_seqProd_rbrKnowledgeSound :
    (pairCheck.verifier.seqProd pairCheck.verifier).RbrKnowledgeSound
      (relProd pairRel pairRel) (relProd Accept Accept)
      (Verifier.extractSeqProd pairExtract pairExtract) (1 / 2, (1 / 2, ())) :=
  pairCheck_rbrKnowledgeSound.seqProd pairCheck_rbrKnowledgeSound

/-- Sequential product of two `pairCheck` reductions is perfectly complete. -/
theorem pairCheck_seqProd_complete :
    (pairCheck.seqProd pairCheck).Complete World.plain
      (relProd pairRel pairRel) (relProd Accept Accept) 0 := by
  simpa using pairCheck_complete.seqProd pairCheck_complete

/-- Concrete extraction check for `Verifier.extractSeqProd` on a two-stage `pairCheck` transcript:
both witness pairs are recovered. -/
theorem extractSeqProd_pairCheck_apply :
    Verifier.extractSeqProd pairExtract pairExtract
      ((true, false), (false, true))
      ((true, false), (false, ((false, true), (true, ()))))
      ((), ()) = ((true, false), (false, true)) :=
  rfl

/-! ### Sumcheck round-by-round knowledge soundness and composition -/

section Sumcheck

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (d : ℕ)
  (P : MvPolynomial (Fin n) F)

/-- Each sumcheck round is round-by-round knowledge sound with error `d / |F|` and the unit
extractor. -/
theorem sumcheck_round_rbrKnowledgeSound (hP : ∀ j, P.degreeOf j ≤ d) {i : ℕ} (hi : i < n) :
    (Sumcheck.round d P i).verifier.RbrKnowledgeSound (Sumcheck.rel P i) (Sumcheck.rel P (i + 1))
      (fun _ _ _ => ()) ((d : ℝ≥0∞) / Fintype.card F, ()) :=
  (Sumcheck.round_rbrSound d P hP hi).rbrKnowledgeSound
    (fun _ _ _ => ()) (fun _ ⟨⟨⟩, hx⟩ _ _ => hx)

/-- Two sumcheck rounds composed with `Verifier.RbrKnowledgeSound.seq` are round-by-round knowledge
sound with concatenated errors. -/
theorem sumcheck_twoRounds_rbrKnowledgeSound (hP : ∀ j, P.degreeOf j ≤ d) (hn : 2 ≤ n) :
    ((Sumcheck.round d P 0).verifier.append (Sumcheck.round d P 1).verifier).RbrKnowledgeSound
      (Sumcheck.rel P 0) (Sumcheck.rel P 2)
      ((Sumcheck.round d P 0).verifier.extractAppend (fun _ _ _ => ()) (fun _ _ _ => ())
        (fun _ => 0, 0))
      ((d : ℝ≥0∞) / Fintype.card F, ((d : ℝ≥0∞) / Fintype.card F, ())) :=
  (sumcheck_round_rbrKnowledgeSound d P hP (by omega)).seq
    (sumcheck_round_rbrKnowledgeSound d P hP (by omega)) (fun _ => 0, 0)

/-- Iterating `n` sumcheck rounds preserves round-by-round knowledge soundness. -/
theorem sumcheck_iterate_rbrKnowledgeSound (hP : ∀ j, P.degreeOf j ≤ d) :
    (Reduction.iterate (s := fun _ => Sumcheck.roundSpec F) (S := Sumcheck.Claim F)
      (W := fun _ => Unit) (Sumcheck.round d P) n).verifier.RbrKnowledgeSound
      (Sumcheck.rel P 0) (Sumcheck.rel P n)
      (Verifier.extractIterate (Sumcheck.round d P) (fun _ _ _ _ => ())
        (fun _ => (fun _ => 0, 0)) n)
      (PerChallenge.iterate (s := fun _ => Sumcheck.roundSpec F)
        (fun _ => ((d : ℝ≥0∞) / Fintype.card F, ())) n) :=
  Verifier.RbrKnowledgeSound.iterate (fun _ => (fun _ => 0, 0)) n
    fun _ hi => sumcheck_round_rbrKnowledgeSound d P hP hi

end Sumcheck

end ComplexityTests.RbrKnowledgeSound
