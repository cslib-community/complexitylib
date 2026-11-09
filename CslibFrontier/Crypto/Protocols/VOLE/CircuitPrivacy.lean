/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Circuit
public import CslibFrontier.Crypto.Protocols.VOLE.AdaptiveMulCheck
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind

/-!
# Full receiver views for the circuit-bound VOLE session

For an honest satisfying circuit trace, every linear opening is determined by the public statement,
corrections and receiver share. An adapter supplies these openings to an arbitrary circuit receiver
and reuses the existing adaptive masked-batch simulation without revealing sender vectors.

## Main definitions

* `circuitPublicFirst`: recover honest linear openings from the receiver's own view.
* `circuitReceiverAdapter`: deliver those openings through the existing receiver strategy API.
* `circuitReceiverView`, `circuitReceiverSimulate`: actual and simulated full receiver views.

## Main results

* `circuitPublicFirst_correct`: recovered openings agree with honest sender openings.
* `circuitReceiverView_eq_simulate`: perfect full-view simulation for the public circuit relation.
* `circuitReceiverSimulate_linear`: every simulated view meets the public linear equations.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.VOLE

open Circuits Interactive Interactive.Spec Probability
open scoped Matrix

variable {F : Type} [CommRing F] {p k m : ℕ}

/-- Recover the honest first message using only the public statement, corrections and receiver
share. Its linear openings are correct precisely when the committed assignment meets those rows. -/
def circuitPublicFirst (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (share : F × (Fin (((p + k) + C.size) + 1) → F))
    (d : Fin ((p + k) + C.size) → F) :
    (Fin ((p + k) + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F) :=
  (d, fun row =>
    (circuitLinearCoeffs C *ᵥ voleAdjustReceiver (Fin.init share.2) d share.1) row -
      circuitLinearTargets C statement.1 statement.2 row * share.1)

/-- For a true circuit statement, the receiver-side reconstruction is exactly the sender's
linear opening. The actual sender computes its opening directly from its private mask vector. -/
theorem circuitPublicFirst_correct (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (w : Fin k → F) (y : Fin m → F)
    (hy : C.eval (arithInterpretation F) (Fin.append x w) = y)
    (c : VOLECorrelation F (((p + k) + C.size) + 1)) (hc : c.Valid) :
    circuitPublicFirst C (x, y) c.receiverView
        (voleCommitWitness (circuitTrace C x w) (Fin.init c.u)) =
      (voleCommitWitness (circuitTrace C x w) (Fin.init c.u),
        circuitLinearCoeffs C *ᵥ Fin.init c.v) := by
  apply Prod.ext
  · rfl
  funext row
  change (circuitLinearCoeffs C *ᵥ
    voleAdjustReceiver (Fin.init c.w) (voleCommitWitness (circuitTrace C x w) (Fin.init c.u))
      c.delta) row - circuitLinearTargets C x y row * c.delta = _
  rw [circuitLinear_adjusted C c hc]
  have hadd : Fin.init c.u + voleCommitWitness (circuitTrace C x w) (Fin.init c.u) =
      circuitTrace C x w := by simp [voleCommitWitness]
  rw [hadd, circuitTrace_linear C x w y hy]
  exact add_sub_cancel_left _ _

variable [Fintype F] [DecidableEq F] {Aux View : Type}

/-- Adapt a circuit receiver to the existing masked batch. Initialization and every selected
continuation are retained. The extra receiver-local setup read uses the same cached share. -/
noncomputable def circuitReceiverAdapter (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (z : Aux) :
    ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (maskedMulCheckSpec F (CircuitMulGate C) ((p + k) + C.size)) View) := do
  let verifier ← V z
  return fun d => do
    let share ← ProbOracleComp.query ()
    verifier (circuitPublicFirst C statement share d)

/-- Extend a masked-batch view with its receiver-reconstructible linear openings. -/
def circuitExpandView (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (view : (F × (Fin (((p + k) + C.size) + 1) → F)) ×
      Transcript (maskedMulCheckSpec F (CircuitMulGate C) ((p + k) + C.size)) × View) :
    (F × (Fin (((p + k) + C.size) + 1) → F)) × Transcript (circuitCheckSpec C) × View :=
  let (share, (d, r, reply, ()), result) := view
  (share, (circuitPublicFirst C statement share d, r, reply, ()), result)

/-- The circuit receiver's actual role-local view: private share, entire transcript and terminal
result. Initialization precedes the honest sender. Each run uses one fresh cached correlation. -/
noncomputable def circuitReceiverView (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (w : Fin k → F) (z : Aux) :
    PMF ((F × (Fin (((p + k) + C.size) + 1) → F)) × Transcript (circuitCheckSpec C) × View) :=
  (voleWorld F (((p + k) + C.size) + 1)).eval do
    let share ← ProbOracleComp.query (.inr ())
    let v ← liftVerifier (V z)
    let p ← liftProver ((circuitCheck C).prover statement w)
    let (transcript, _, result) ← runAgainst (circuitCheckSpec C)
      (ProverStrategy.hoist liftProver _ p) (VerifierStrategy.hoist liftVerifier _ v)
    return (share, transcript, result)

/-- Witness-free simulation, using the existing adaptive masked-batch simulator and extending its
full transcript. The adapter accesses only the receiver share, without sender masks. -/
noncomputable def circuitReceiverSimulate (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (z : Aux) :
    ProbComp ((F × (Fin (((p + k) + C.size) + 1) → F)) × Transcript (circuitCheckSpec C) × View) :=
  circuitExpandView C statement <$>
    maskedMulCheckReceiverSimulate (fun i => circuitMulInput C i 0)
      (fun i => circuitMulInput C i 1) (circuitMulOutput C)
      (circuitReceiverAdapter C statement V) z


omit [CommRing F] [Fintype F] [DecidableEq F] in
private theorem interpret_liftVerifier {n : ℕ} {α : Type} (c : VOLECorrelation F n)
    (program : ProbOracleComp (voleReceiverSpec F n) α) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (OracleComp.sumHandler (fun _ => PMF.pure (c.u, c.v))
        (fun _ => PMF.pure c.receiverView)))
      (liftVerifier (oP := voleSenderSpec F n) program) =
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (fun _ => PMF.pure c.receiverView)) program := by
  rw [liftVerifier, OracleComp.interpret_interpret]
  congr 1
  funext q
  cases q <;> simp [OracleComp.sumHandler, ProbOracleComp.query]

/-- The circuit interaction is the existing masked-batch interaction with reconstructed linear
openings, including the entire receiver state and transcript. The prover remains role-local. -/
theorem circuitReceiverView_eq_expand (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (w : Fin k → F) (z : Aux)
    (hy : C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2) :
    circuitReceiverView C statement V w z =
      (maskedMulCheckReceiverView (fun i => circuitMulInput C i 0)
        (fun i => circuitMulInput C i 1) (circuitMulOutput C)
        (circuitReceiverAdapter C statement V) (circuitTrace C statement.1 w) z).map
          (circuitExpandView C statement) := by
  unfold circuitReceiverView maskedMulCheckReceiverView
  rw [voleWorld_eval, voleWorld_eval]
  simp only [PMF.monad_bind_eq_bind, PMF.map_bind]
  apply PMF.bind_congr_on_support
  intro c hc
  have hfirst := circuitPublicFirst_correct C statement.1 w statement.2 hy c
    (valid_of_mem_support_voleIdealDist hc)
  simp only [pmf_norm, OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbOracleComp.interpret_query, OracleComp.sumHandler, VOLECorrelation.senderView,
    interpret_liftVerifier]
  simp only [pmf_norm, circuitReceiverAdapter, OracleComp.interpret_bind, OracleComp.interpret_pure]
  congr 1
  funext verifier
  simp [circuitCheck, maskedMulCheck, liftProver, ProbOracleComp.query,
    OracleComp.sumHandler, runAgainst, ProverStrategy.hoist, VerifierStrategy.hoist,
    circuitCheckSpec, maskedMulCheckSpec, SigmaProtocol.sigmaSpec,
    interpret_liftVerifier, PMF.map, Function.comp_def, circuitExpandView,
    hfirst]

/-- Exact full-view simulation against every role-local receiver for a satisfying public circuit
statement. Auxiliary input is fixed before the trusted fresh setup; arbitrary captured private
coins and repeated receiver-share queries are preserved. This is one fixed session, without a
runtime, reset, concurrent composition or plain-model ZK claim. -/
theorem circuitReceiverView_eq_simulate (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (w : Fin k → F) (z : Aux)
    (hy : C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2) :
    circuitReceiverView C statement V w z =
      ProbComp.eval (circuitReceiverSimulate C statement V z) := by
  rw [circuitReceiverView_eq_expand C statement V w z hy,
    maskedMulCheckReceiverView_eq_simulate _ _ _ _ _ z (circuitTrace_mul C statement.1 w)]
  exact (ProbComp.eval_map _ _).symm


omit [DecidableEq F] in
/-- Every simulated view satisfies the public linear openings. This concerns the transcript
rather than the decision of an arbitrary receiver, and requires no witness. -/
theorem circuitReceiverSimulate_linear (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (V : Aux → ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1))
      (VerifierStrategy (ProbOracleComp (voleReceiverSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) View)) (z : Aux)
    {view : (F × (Fin (((p + k) + C.size) + 1) → F)) × Transcript (circuitCheckSpec C) × View}
    (hview : view ∈ (ProbComp.eval (circuitReceiverSimulate C statement V z)).support)
    (row : Fin p ⊕ Fin C.size ⊕ Fin m) :
    (circuitLinearCoeffs C *ᵥ
      voleAdjustReceiver (Fin.init view.1.2) view.2.1.1.1 view.1.1) row =
        circuitLinearTargets C statement.1 statement.2 row * view.1.1 + view.2.1.1.2 row := by
  rw [circuitReceiverSimulate, ProbComp.eval_map, PMF.mem_support_map_iff] at hview
  obtain ⟨source, _, rfl⟩ := hview
  simp only [circuitExpandView, circuitPublicFirst]
  ring

end Cslib.Crypto.Protocols.VOLE
