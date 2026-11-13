/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.AdaptiveMulCheck
import CslibFrontierTests.Crypto.VOLEMaskedMulCheck

/-!
# Adaptive receiver clients

The receiver's weights depend on its private key/tags and the correction. A second receiver
retains a private coin, branches between zero and adaptive weights, and reads the setup again
both after the reply and during its terminal computation. Earlier false-witness and unmasked
full-view separation tests remain imported above.
-/

namespace CslibFrontierTests.Crypto.VOLEAdaptiveMulCheck

open Cslib Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
  Cslib.Crypto.Protocols.VOLE

private def wire : Fin 1 → Fin 1 := fun _ => 0

abbrev Share (F : Type) := F × (Fin 2 → F)
abbrev Protocol (F : Type) := maskedMulCheckSpec F (Fin 1) 1
abbrev ReceiverM (F : Type) := ProbOracleComp (voleReceiverSpec F 2)

def adaptiveWeight {F : Type} [Add F] (share : Share F) (d : Fin 1 → F) (z : F) : F :=
  share.1 + share.2 0 + d 0 + z

def adaptiveReceiver {F : Type} [Add F] (z : F) :
    ReceiverM F (VerifierStrategy (ReceiverM F) (Protocol F) (Share F × F × (F × F))) := do
  let share ← ProbOracleComp.query ()
  return fun d => do
    let r : Fin 1 → F := fun _ => adaptiveWeight share d z
    return (show ReceiverM F ((Fin 1 → F) ×
      VerifierStrategy (ReceiverM F) [.prover (F × F) (OracleInterface.full (F × F))]
        (Share F × F × (F × F))) from pure (r, fun reply => do
          let again ← ProbOracleComp.query ()
          return (show ReceiverM F (Share F × F × (F × F)) from
            pure (again, r 0, reply))))

-- Key, raw tags and corrections each genuinely affect the chosen challenge.
example : adaptiveWeight ((1 : ZMod 3), 0) 0 0 ≠ adaptiveWeight (0, 0) 0 0 ∧
    adaptiveWeight (0, ![1, 0]) 0 0 ≠ adaptiveWeight (0, 0) 0 0 ∧
    adaptiveWeight (0, 0) ![1] 0 ≠ adaptiveWeight (0, 0) 0 0 := by decide

example (z : ZMod 3) :
    maskedMulCheckReceiverView wire wire wire adaptiveReceiver (fun _ => 0) z =
      maskedMulCheckReceiverView wire wire wire adaptiveReceiver (fun _ => 1) z := by
  rw [maskedMulCheckReceiverView_eq_simulate wire wire wire _ _ _ (by decide),
    maskedMulCheckReceiverView_eq_simulate wire wire wire _ _ _ (by decide)]

abbrev CoinView (F : Type) := Bool × Share F × Share F × F × F

noncomputable def coinReceiver {F : Type} [CommRing F] (z : F) :
    ReceiverM F (VerifierStrategy (ReceiverM F) (Protocol F) (CoinView F)) := do
  let share ← ProbOracleComp.query ()
  return fun d => do
    let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
    let r : Fin 1 → F := fun _ => if coin then adaptiveWeight share d z else 0
    return (show ReceiverM F ((Fin 1 → F) ×
      VerifierStrategy (ReceiverM F) [.prover (F × F) (OracleInterface.full (F × F))]
        (CoinView F)) from pure (r, fun reply => do
          let afterReply ← ProbOracleComp.query ()
          return (show ReceiverM F (CoinView F) from do
            let terminal ← ProbOracleComp.query ()
            return (coin, afterReply, terminal, r 0, reply.1 + reply.2))))

example (z : ZMod 2) :
    maskedMulCheckReceiverView wire wire wire coinReceiver (fun _ => 1) z =
      ProbComp.eval (maskedMulCheckReceiverSimulate wire wire wire coinReceiver z) :=
  maskedMulCheckReceiverView_eq_simulate _ _ _ _ _ _ (by decide)

-- Privacy also covers rings with zero divisors.
example (z : ZMod 4) :
    maskedMulCheckReceiverView wire wire wire coinReceiver (fun _ => 1) z =
      ProbComp.eval (maskedMulCheckReceiverSimulate wire wire wire coinReceiver z) :=
  maskedMulCheckReceiverView_eq_simulate _ _ _ _ _ _ (by decide)

-- The empty wire/gate boundary still permits a receiver to retain and reread its mask share.
def emptyReceiver (z : Unit) : ProbOracleComp (voleReceiverSpec (ZMod 2) 1)
    (VerifierStrategy (ProbOracleComp (voleReceiverSpec (ZMod 2) 1))
      (maskedMulCheckSpec (ZMod 2) (Fin 0) 0) (ZMod 2)) := do
  let share ← ProbOracleComp.query z
  return fun _ => pure (show ProbOracleComp (voleReceiverSpec (ZMod 2) 1)
    ((Fin 0 → ZMod 2) × VerifierStrategy (ProbOracleComp (voleReceiverSpec (ZMod 2) 1))
      [.prover (ZMod 2 × ZMod 2) (OracleInterface.full (ZMod 2 × ZMod 2))] (ZMod 2)) from
    pure (Fin.elim0, fun reply => do
      let again ← ProbOracleComp.query ()
      return (show ProbOracleComp (voleReceiverSpec (ZMod 2) 1) (ZMod 2) from
        pure (share.1 + again.2 0 + reply.1))))

example : maskedMulCheckReceiverView (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0 Fin.elim0
    emptyReceiver Fin.elim0 () =
      ProbComp.eval
        (maskedMulCheckReceiverSimulate Fin.elim0 Fin.elim0 Fin.elim0 emptyReceiver ()) :=
  maskedMulCheckReceiverView_eq_simulate _ _ _ _ _ _ (fun i => Fin.elim0 i)

def constantReceiver (_ : Unit) : ReceiverM (ZMod 3)
    (VerifierStrategy (ReceiverM (ZMod 3)) (Protocol (ZMod 3)) Unit) :=
  pure fun _ => pure (show ReceiverM (ZMod 3) ((Fin 1 → ZMod 3) ×
    VerifierStrategy (ReceiverM (ZMod 3))
      [.prover (ZMod 3 × ZMod 3) (OracleInterface.full (ZMod 3 × ZMod 3))] Unit) from
    pure ((fun _ => 1), fun _ => pure (show ReceiverM (ZMod 3) Unit from pure ())))

private def falseView : Share (ZMod 3) × Transcript (Protocol (ZMod 3)) × Unit :=
  ((1, fun _ => 0), ((fun _ => 2), (fun _ => 1), (0, 0), ()), ())

private theorem falseView_real : falseView ∈
    (maskedMulCheckReceiverView wire wire wire constantReceiver
      (fun _ => (2 : ZMod 3)) ()).support := by
  have hrun : maskedMulCheckReceiverView wire wire wire constantReceiver
      (fun _ => (2 : ZMod 3)) () = (voleIdealDist (ZMod 3) 2).map (fun c =>
        (c.receiverView, (voleCommitWitness (fun _ => 2) (Fin.init c.u), (fun _ => 1),
          maskedMulCheckReply wire wire wire (fun _ => 2) c.u c.v (fun _ => 1), ()), ())) := by
    simp [maskedMulCheckReceiverView, constantReceiver, World.eval, voleWorld,
      maskedMulCheck, liftProver, liftVerifier, runAgainst, ProverStrategy.hoist,
      VerifierStrategy.hoist, maskedMulCheckSpec, threeMoveSpec,
      ProbOracleComp.query, ProbOracleComp.runWith, OracleComp.sumHandler,
      VOLECorrelation.senderView,
      PMF.map, Function.comp_def, PMF.bind_bind]
  rw [hrun]
  simp only [PMF.mem_support_map_iff]
  refine ⟨voleSample (fun _ => 0) (fun _ => 0) 1,
    (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _), ?_⟩
  decide

-- A false witness has an actual rejecting transcript, excluded from every simulator output.
example : maskedMulCheckReceiverView wire wire wire constantReceiver
    (fun _ => (2 : ZMod 3)) () ≠
      ProbComp.eval (maskedMulCheckReceiverSimulate wire wire wire constantReceiver ()) := by
  intro heq
  have hv := falseView_real
  rw [heq] at hv
  have hcheck := maskedMulCheckReceiverSimulate_accepts wire wire wire constantReceiver () hv
  have hfalse : ¬ MaskedMulCheckAccepts wire wire wire falseView.1 falseView.2.1 := by decide
  exact hfalse hcheck

end CslibFrontierTests.Crypto.VOLEAdaptiveMulCheck
