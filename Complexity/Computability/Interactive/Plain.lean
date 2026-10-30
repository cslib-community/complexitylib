/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Interactive.Security
import Complexity.Probability.PMF
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Event

/-!
# Interactive reductions in the plain model

In the plain model neither party has oracles, and a run is an ordinary probabilistic program.
`Interactive.plainLaw` is the law of a prover-side program, and
`Interactive.World.plain_eval_execute` computes the law of a whole execution from the law of the
prover's run. The main result is that round-by-round soundness implies soundness with the sum of
the per-round errors (`Interactive.Verifier.RbrSound.sound`), against arbitrary prover strategies.

## Main definitions

* `Interactive.plainLaw`: the law of a program without oracles.

## Main results

* `Interactive.World.plain_eval_execute`: the law of an execution in the plain model.
* `Interactive.Verifier.RbrSound.sound`: round-by-round soundness implies soundness.

## References

* [R. Canetti, Y. Chen, J. Holmgren, A. Lombardi, G. N. Rothblum, R. D. Rothblum, D. Wichs,
  *Fiat–Shamir: from practice to theory*][CanettiCHLRRW2019]
-/

@[expose] public section

namespace Cslib.Interactive

open scoped ENNReal
open Spec

/-- The law of a program without external oracles: its private coins are fair. -/
noncomputable def plainLaw {α : Type} (p : ProbOracleComp OracleSpec.empty α) : PMF α :=
  OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle fun e => e.elim) p

/-- The law of a joint program in the plain model. -/
private noncomputable def runLaw {α : Type}
    (p : ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) α) : PMF α :=
  OracleComp.interpret (ProbOracleComp.handler ProbComp.unifOracle
    (OracleComp.sumHandler (fun e => e.elim) fun e => e.elim)) p

private theorem plain_eval {α : Type}
    (p : ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) α) :
    World.plain.eval p = runLaw p := by
  have h := OracleComp.run_interpret_stateless (m := PMF) (State := Unit)
    (ProbOracleComp.handler ProbComp.unifOracle
      (OracleComp.sumHandler (fun e => e.elim) fun e => e.elim)) p ()
  have hh : (ProbOracleComp.handler (fun n => StateT.lift (ProbComp.unifOracle n))
      World.plain.impl) =
      fun q s => (fun a => (a, s)) <$> ProbOracleComp.handler ProbComp.unifOracle
        (OracleComp.sumHandler (fun e => e.elim) fun e => e.elim) q := by
    funext q s
    rcases q with n | e | e
    · rfl
    · exact e.elim
    · exact e.elim
  unfold World.eval ProbOracleComp.runWith
  erw [hh, h]
  exact (PMF.map_comp _ _ _).trans (PMF.map_id _)

private theorem runLaw_liftProver {α : Type} (p : ProbOracleComp OracleSpec.empty α) :
    runLaw (liftProver (oV := OracleSpec.empty) p) = plainLaw p := by
  rw [runLaw, liftProver, OracleComp.interpret_interpret, plainLaw]
  congr 1
  funext q
  rcases q with n | e
  · simp [ProbOracleComp.handler]
  · exact e.elim


/-- A returned value has a point law. -/
@[simp] theorem plainLaw_pure {α : Type} (a : α) :
    plainLaw (pure a : ProbOracleComp OracleSpec.empty α) = PMF.pure a := rfl

/-- Sequencing is `PMF.bind`. -/
@[simp] theorem plainLaw_bind {α β : Type} (p : ProbOracleComp OracleSpec.empty α)
    (f : α → ProbOracleComp OracleSpec.empty β) :
    plainLaw (p >>= f) = (plainLaw p).bind fun a => plainLaw (f a) :=
  OracleComp.interpret_bind _ _ _

/-- Postprocessing is `PMF.map`. -/
@[simp] theorem plainLaw_map {α β : Type} (f : α → β) (p : ProbOracleComp OracleSpec.empty α) :
    plainLaw (f <$> p) = (plainLaw p).map f :=
  OracleComp.interpret_map _ _ _

/-- Embedded sampling has the law of the sampled program. -/
@[simp] theorem plainLaw_sample {α : Type} (p : ProbComp α) :
    plainLaw (ProbOracleComp.sample (spec := OracleSpec.empty) p) = ProbComp.eval p :=
  ProbOracleComp.interpret_sample _ _ _

private theorem runLaw_pure {α : Type} (a : α) :
    runLaw (pure a : ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) α) = PMF.pure a := rfl

private theorem runLaw_bind {α β : Type}
    (p : ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) α)
    (f : α → ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) β) :
    runLaw (p >>= f) = (runLaw p).bind fun a => runLaw (f a) :=
  OracleComp.interpret_bind _ _ _

private theorem runLaw_map {α β : Type} (f : α → β)
    (p : ProbOracleComp (OracleSpec.empty ⊕ₒ OracleSpec.empty) α) :
    runLaw (f <$> p) = (runLaw p).map f :=
  OracleComp.interpret_map _ _ _

/-- A program whose queries are answered deterministically has a point law. -/
private theorem interpret_pure_handler {ι : Type} {spec : OracleSpec ι} {α : Type}
    (f : (q : ι) → spec q) (p : OracleComp spec α) :
    OracleComp.interpret (m := PMF) (fun q => PMF.pure (f q)) p =
      PMF.pure (OracleComp.interpret (m := Id) f p) := by
  induction p using PFunctor.FreeM.induction with
  | pure a => rfl
  | lift_bind q cont ih =>
    rw [show (PFunctor.FreeM.lift q).bind cont = OracleComp.query q >>= cont from rfl,
      OracleComp.interpret_bind, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_query]
    simp only [Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]
    exact ih (f q)

private theorem runLaw_output {s : Spec} {StmtIn StmtOut : Type}
    (V : Verifier OracleSpec.empty s StmtIn StmtOut)
    (x : StmtIn) (τ : Transcript s) :
    runLaw (V.output (oP := OracleSpec.empty) x τ) = PMF.pure (V.outputOn x τ) := by
  rw [runLaw, Verifier.output, OracleComp.interpret_interpret, Verifier.outputOn]
  rw [← interpret_pure_handler]
  congr 1
  funext q
  rcases q with e | q
  · exact e.elim
  · rfl

private theorem toOuterMeasure_bind_pure {α β : Type} (p : PMF α) (g : α → β) (t : Set β) :
    (p.bind fun a => PMF.pure (g a)).toOuterMeasure t = p.toOuterMeasure (g ⁻¹' t) := by
  rw [← PMF.toOuterMeasure_map_apply]
  rfl

/-- **The law of an execution in the plain model**: run the prover's strategy against the
challenge samplers, then apply the verifier's decision to the transcript. -/
theorem World.plain_eval_execute {s : Spec} {StmtIn StmtOut α : Type}
    (V : Verifier OracleSpec.empty s StmtIn StmtOut) (x : StmtIn)
    (P : ProbOracleComp OracleSpec.empty (ProverStrategy (ProbOracleComp OracleSpec.empty) s α)) :
    World.plain.eval (V.execute (oP := OracleSpec.empty) x P) =
      (plainLaw (P >>= runStrategy s V.samplers)).map fun r => (r.1, V.outputOn x r.1, r.2) := by
  rw [plain_eval]
  simp only [Verifier.execute, runLaw_bind, runLaw_liftProver, runLaw_output, runLaw_pure,
    PMF.pure_bind, plainLaw_bind, PMF.map_bind]
  rfl

/-- From a doomed prefix, the rest of a run wins with probability at most the remaining errors. -/
private theorem rbrFrom_le : ∀ (s : Spec) (smp : PerChallenge ProbComp s)
    (ε : PerChallenge (fun _ => ℝ≥0∞) s) (S : Prefix s → Prop) (wins : Transcript s → Prop),
    RbrFrom s smp ε S wins → ¬ S (Prefix.empty s) →
    ∀ {α : Type} (st : ProverStrategy (ProbOracleComp OracleSpec.empty) s α),
      (plainLaw (runStrategy s smp st)).toOuterMeasure {r | wins r.1} ≤ PerChallenge.sum s ε
  | [], _, _, _, wins, h, hS, _, st => by
    have hw : ¬ wins () := h hS
    simp [runStrategy, hw]
  | .prover M I :: s, smp, ε, S, wins, h, hS, _, st => by
    simp only [runStrategy, plainLaw_bind]
    refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun p => ?_
    rcases p with ⟨msg, st'⟩
    simp only [plainLaw_pure]
    rw [toOuterMeasure_bind_pure]
    exact rbrFrom_le s smp ε (fun p => S (some (msg, p))) (fun τ => wins (msg, τ)) (h.2 msg)
      (h.1 hS msg) st'
  | .verifier C :: s, smp, ε, S, wins, h, hS, _, st => by
    simp only [runStrategy, plainLaw_bind, plainLaw_sample]
    rw [PMF.toOuterMeasure_bind_apply]
    set A : Set C := {c | S (some (c, Prefix.empty s))}
    have hinner : ∀ c, ((plainLaw (st c)).bind fun st' => (plainLaw (runStrategy s smp.2 st')).bind
        fun r => plainLaw (pure ((c, r.1), r.2))).toOuterMeasure {r | wins r.1} ≤
        A.indicator 1 c + PerChallenge.sum s ε.2 := by
      intro c
      by_cases hc : c ∈ A
      · refine le_trans ?_ le_self_add
        rw [Set.indicator_of_mem hc]
        exact Probability.PMF.toOuterMeasure_le_one _ _
      · rw [Set.indicator_of_notMem hc, zero_add]
        refine Probability.PMF.toOuterMeasure_bind_le _ _ _ fun st' => ?_
        simp only [plainLaw_pure]
        rw [toOuterMeasure_bind_pure]
        exact rbrFrom_le s smp.2 ε.2 (fun p => S (some (c, p))) (fun τ => wins (c, τ)) (h.2 c) hc
          st'
    calc ∑' c, ProbComp.eval smp.1 c * _ ≤
          ∑' c, ProbComp.eval smp.1 c * (A.indicator 1 c + PerChallenge.sum s ε.2) :=
          tsum_le_tsum fun c => by gcongr; exact hinner c
      _ = (ProbComp.eval smp.1).toOuterMeasure A + PerChallenge.sum s ε.2 := by
          simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun c => ?_
          by_cases hc : c ∈ A <;> simp [hc]
      _ ≤ ε.1 + PerChallenge.sum s ε.2 := by gcongr; exact h.1 hS

/-- **Round-by-round soundness implies soundness**, with the sum of the per-round errors. -/
theorem Verifier.RbrSound.sound {s : Spec} {StmtIn StmtOut : Type}
    {V : Verifier OracleSpec.empty s StmtIn StmtOut} {langIn : Set StmtIn}
    {langOut : Set StmtOut} {ε : PerChallenge (fun _ => ℝ≥0∞) s}
    (h : V.RbrSound langIn langOut ε) :
    V.Sound (oP := OracleSpec.empty) World.plain langIn langOut (PerChallenge.sum s ε) := by
  obtain ⟨S, hinit, hround⟩ := h
  intro x hx α P
  rw [World.plain_eval_execute, PMF.toOuterMeasure_map_apply, plainLaw_bind]
  exact Probability.PMF.toOuterMeasure_bind_le _ _ _ fun st =>
    rbrFrom_le s V.samplers ε (S x) _ (hround x) (hinit x hx) st

end Cslib.Interactive
