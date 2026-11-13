/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.VOLE.CircuitSound
import CslibFrontier.Crypto.Protocols.VOLE.CircuitPrivacy
import CslibFrontier.Computability.Circuit.Pi
import CslibFrontier.Computability.Probabilistic.Sampling.F4
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Public output binding, linear-only rejection, repeated wires and role-local stateful clients. -/

namespace CslibFrontierTests.Crypto.VOLECircuit

open Cslib Cslib.Circuits Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
  Cslib.Crypto.Protocols.VOLE
open scoped ENNReal Matrix

private abbrev F := QuadraticAlgebra (ZMod 2) 1 1
private def theta : F := ⟨0, 1⟩
private def square (K : Type) : Circuit (arithSignature K) (1 + 0) 1 :=
  Circuit.oneGate .mul (fun _ => 0)
private def double (K : Type) : Circuit (arithSignature K) (1 + 0) 1 :=
  Circuit.oneGate .add (fun _ => 0)
private def constant (K : Type) (a : K) : Circuit (arithSignature K) (0 + 0) 1 :=
  Circuit.oneGate (.const a) Fin.elim0

private theorem f4_error : (Fintype.card F : ℝ≥0∞)⁻¹ +
    (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞)) = 5 / 8 := by
  rw [F4.card]
  norm_num only [Nat.cast_ofNat]
  apply (ENNReal.toReal_eq_toReal_iff _ _).mp ?_ |>.resolve_right ?_
  · rw [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_sub_of_le]
    all_goals try norm_num [ENNReal.inv_le_one, ENNReal.toReal_inv, ENNReal.toReal_div]
    exact ENNReal.mul_ne_top (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · simp

-- A concrete field with exact two-bit sampling has a strictly subunit soundness error.
private theorem f4_sound {p k m : ℕ} (C : Circuit (arithSignature F) (p + k) m) :
    (circuitCheck C).verifier.Sound (voleWorld F (((p + k) + C.size) + 1))
      {statement | ∃ w, C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2}
      Set.univ (5 / 8) := by
  simpa only [f4_error] using circuitCheck_sound C

private theorem square_false : ¬ ∃ w : Fin 0 → F,
    (square F).eval (arithInterpretation F) (Fin.append (fun _ => 1) w) = fun _ => 0 := by
  rintro ⟨w, h⟩
  have h0 := congrFun h 0
  change (1 : F) * 1 = 0 at h0
  simp at h0

-- Internally honest multiplication does not authorize a false public output.
example : (∀ i : CircuitMulGate (square F),
    circuitTrace (square F) (fun _ => 1) Fin.elim0 (circuitMulInput (square F) i 0) *
      circuitTrace (square F) (fun _ => 1) Fin.elim0 (circuitMulInput (square F) i 1) =
        circuitTrace (square F) (fun _ => 1) Fin.elim0 (circuitMulOutput (square F) i)) ∧
    ¬ ∃ w : Fin 0 → F,
      (square F).eval (arithInterpretation F) (Fin.append (fun _ => 1) w) = fun _ => 0 :=
  ⟨circuitTrace_mul _ _ _, square_false⟩

-- Repeated inputs add their coefficients; in characteristic two the double circuit is zero.
private theorem double_false : ¬ ∃ w : Fin 0 → F,
    (double F).eval (arithInterpretation F) (Fin.append (fun _ => theta) w) = fun _ => 1 := by
  rintro ⟨w, h⟩
  have h0 := congrFun h 0
  change theta + theta = 1 at h0
  exact (by decide : theta + theta ≠ 1) h0

example : IsEmpty (CircuitMulGate (double F)) := by
  refine ⟨fun i => ?_⟩
  rcases i with ⟨i, hi⟩
  fin_cases i
  contradiction

example : ¬ ∃ w : Fin 0 → F,
    (constant F theta).eval (arithInterpretation F) (Fin.append Fin.elim0 w) = fun _ => 0 := by
  rintro ⟨w, h⟩
  have h0 := congrFun h 0
  change theta = 0 at h0
  exact (by decide : theta ≠ 0) h0

-- Non-prime-subfield arithmetic and shared input wire exercise honest completeness.
example : (square F).eval (arithInterpretation F)
    (Fin.append (fun _ => theta) Fin.elim0) = fun _ => theta + 1 := by
  funext i
  fin_cases i
  change theta * theta = theta + 1
  decide


private abbrev SenderM := ProbOracleComp (voleSenderSpec F 3)
private abbrev ReceiverM (K : Type) :=
  ProbOracleComp (voleReceiverSpec K (1 + 0 + (square K).size + 1))
private abbrev Share (K : Type) := K × (Fin 3 → K)
private abbrev First (K : Type) := (Fin 2 → K) × ((Fin 1 ⊕ Fin 1 ⊕ Fin 1) → K)
private abbrev ReceiverView (K : Type) :=
  Bool × Share K × Share K × Share K × First K × K × (K × K)

-- The sender's retained private coin changes its commitment and later weight-dependent reply.
private noncomputable def cheatingSender :
    SenderM (ProverStrategy SenderM (circuitCheckSpec (square F)) Bool) := do
  let share ← ProbOracleComp.query ()
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  return (show SenderM (_ × ((CircuitMulGate (square F) → F) → SenderM
    (SenderM ((F × F) × Bool)))) from pure
    (((fun _ => if coin then theta else 1), (fun _ => share.2 0)), fun r => do
      let again ← ProbOracleComp.query ()
      return (show SenderM ((F × F) × Bool) from do
        let last ← ProbOracleComp.query ()
        return ((r ⟨⟨0, by simp [square]⟩, rfl⟩ + again.1 0, last.2 1), coin))))

example : ((voleWorld F 3).eval
    ((circuitCheck (square F)).verifier.execute
      ((fun _ => 1), (fun _ => 0)) cheatingSender)).toOuterMeasure
       {result | result.2.1 = some ()} ≤ 5 / 8 := by
  have h := f4_sound (square F) ((fun _ => 1), (fun _ => 0)) square_false Bool cheatingSender
  have event (x : Option Unit) : (∃ x' : Unit, x = some x') ↔ x = some () := by
    constructor
    · rintro ⟨⟨⟩, hx⟩
      exact hx
    · exact fun hx => ⟨(), hx⟩
  simpa only [Set.mem_univ, true_and, event, square, Circuit.size_oneGate, Nat.reduceAdd] using h

-- Linear-only false statements are covered even when the multiplication challenge is empty.
example {α : Type} (P : SenderM (ProverStrategy SenderM (circuitCheckSpec (double F)) α)) :
    ((voleWorld F 3).eval
      ((circuitCheck (double F)).verifier.execute
        ((fun _ => theta), (fun _ => 1)) P)).toOuterMeasure
       {result | result.2.1 = some ()} ≤ 5 / 8 := by
  have h := f4_sound (double F) ((fun _ => theta), (fun _ => 1)) double_false α P
  have event (x : Option Unit) : (∃ x' : Unit, x = some x') ↔ x = some () := by
    constructor
    · rintro ⟨⟨⟩, hx⟩
      exact hx
    · exact fun hx => ⟨(), hx⟩
  simpa only [Set.mem_univ, true_and, event, double, Circuit.size_oneGate, Nat.reduceAdd] using h

private noncomputable def coinReceiver {K : Type} [CommRing K] (z : K) :
    ReceiverM K (VerifierStrategy (ReceiverM K) (circuitCheckSpec (square K))
      (ReceiverView K)) := do
  let share ← ProbOracleComp.query ()
  let coin ← ProbOracleComp.sample (ProbComp.uniform Bool)
  return fun first => do
    let weight := if coin then share.1 + share.2 0 + first.1 0 + first.2 (.inl 0) + z
      else first.2 (.inr (.inr 0))
    return (show ReceiverM K ((CircuitMulGate (square K) → K) ×
      VerifierStrategy (ReceiverM K) [.prover (K × K) (OracleInterface.full (K × K))]
        (ReceiverView K)) from pure ((fun _ => weight), fun reply => do
          let after ← ProbOracleComp.query ()
          return (show ReceiverM K (ReceiverView K) from do
            let terminal ← ProbOracleComp.query ()
            return (coin, share, after, terminal, first, weight, reply))))

-- The complete stateful transcript law over F4 uses nontrivial multiplication θ²=θ+1.
example (z : F) :
    circuitReceiverView (square F) ((fun _ => theta), (fun _ => theta + 1))
      coinReceiver Fin.elim0 z =
    ProbComp.eval (circuitReceiverSimulate (square F)
      ((fun _ => theta), (fun _ => theta + 1)) coinReceiver z) := by
  apply circuitReceiverView_eq_simulate
  funext i
  fin_cases i
  change theta * theta = theta + 1
  decide

-- Privacy and completeness retain their ring scope, including zero divisors.
example (z : ZMod 4) :
    circuitReceiverView (square (ZMod 4)) ((fun _ => 2), (fun _ => 0))
      coinReceiver Fin.elim0 z =
    ProbComp.eval (circuitReceiverSimulate (square (ZMod 4))
      ((fun _ => 2), (fun _ => 0)) coinReceiver z) := by
  apply circuitReceiverView_eq_simulate
  funext i
  fin_cases i
  change (2 : ZMod 4) * 2 = 0
  decide

example : (circuitCheck (square (ZMod 4))).Complete (voleWorld (ZMod 4) 3)
    (fun statement w => (square (ZMod 4)).eval (arithInterpretation (ZMod 4))
      (Fin.append statement.1 w) = statement.2) Accept 0 := circuitCheck_complete _

-- A circuit with no gates and no outputs has a true relation and an empty multiplication set.
example {K : Type} [CommRing K] [Fintype K] [DecidableEq K] :
    (circuitCheck (Circuit.wiring (arithSignature K) (Fin.elim0 : Fin 0 → Fin (0 + 0)))).Complete
      (voleWorld K 1)
      (fun statement w =>
        (Circuit.wiring (arithSignature K) (Fin.elim0 : Fin 0 → Fin (0 + 0))).eval
          (arithInterpretation K) (Fin.append statement.1 w) = statement.2) Accept 0 :=
  circuitCheck_complete _


-- Two designated outputs must both agree, even when they share a single input wire.
example : ¬ ∃ w : Fin 0 → F,
    (Circuit.wiring (arithSignature F) (fun _ : Fin 2 => (0 : Fin (1 + 0)))).eval
      (arithInterpretation F) (Fin.append (fun _ => 1) w) = ![1, 0] := by
  rintro ⟨w, h⟩
  have h1 := congrFun h 1
  change (1 : F) = 0 at h1
  exact one_ne_zero h1

private def zeroReceiver (_ : Unit) :
    ReceiverM F (VerifierStrategy (ReceiverM F) (circuitCheckSpec (square F)) Unit) :=
  pure (fun _ => pure (show ReceiverM F ((CircuitMulGate (square F) → F) ×
    VerifierStrategy (ReceiverM F) [.prover (F × F) (OracleInterface.full (F × F))] Unit) from
      pure ((fun _ => 0), fun _ => pure (show ReceiverM F Unit from pure ()))))

private def falseView : (F × (Fin (1 + 0 + (square F).size + 1) → F)) ×
    Transcript (circuitCheckSpec (square F)) × Unit :=
  ((1, fun _ => 0), (((fun _ => 1), (fun _ => 0)), (fun _ => 0), (0, 0), ()), ())

private theorem falseView_real : falseView ∈
    (circuitReceiverView (square F) ((fun _ => 1), (fun _ => 0))
      zeroReceiver Fin.elim0 ()).support := by
  have hrun : circuitReceiverView (square F) ((fun _ => 1), (fun _ => 0))
      zeroReceiver Fin.elim0 () = (voleIdealDist F (1 + 0 + (square F).size + 1)).map (fun c =>
        (c.receiverView, ((voleCommitWitness (circuitTrace (square F) (fun _ => 1) Fin.elim0)
          (Fin.init c.u), circuitLinearCoeffs (square F) *ᵥ Fin.init c.v), (fun _ => 0),
          maskedMulCheckReply (fun i => circuitMulInput (square F) i 0)
            (fun i => circuitMulInput (square F) i 1) (circuitMulOutput (square F))
            (circuitTrace (square F) (fun _ => 1) Fin.elim0) c.u c.v (fun _ => 0), ()), ())) := by
    unfold circuitReceiverView
    rw [voleWorld_eval]
    simp [zeroReceiver, circuitCheck, liftProver, liftVerifier, runAgainst,
      ProverStrategy.hoist, VerifierStrategy.hoist, circuitCheckSpec,
      threeMoveSpec, ProbOracleComp.query,
      OracleComp.sumHandler, VOLECorrelation.senderView, PMF.map, Function.comp_def,
      OracleComp.interpret_pure, OracleComp.interpret_bind]
  rw [hrun, PMF.mem_support_map_iff]
  refine ⟨voleSample (fun _ => 0) (fun _ => 0) 1,
    (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _), ?_⟩
  have htrace : circuitTrace (square F) (fun _ => 1) Fin.elim0 = fun _ => 1 := by
    funext i
    change Fin 2 at i
    fin_cases i <;> decide
  have hzero : Fin.init (fun _ : Fin (1 + 0 + (square F).size + 1) => (0 : F)) = 0 := rfl
  simp only [Nat.add_zero, VOLECorrelation.receiverView, voleSample, mul_one, add_zero,
    voleCommitWitness, htrace, hzero, sub_zero, Matrix.mulVec_zero, maskedMulCheckReply,
    Fin.isValue, zero_mul, Finset.sum_const_zero, falseView, Prod.mk.injEq, true_and, and_true]
  rfl

-- The simulation equality fails for a false public output, despite internally correct gates.
example : circuitReceiverView (square F) ((fun _ => 1), (fun _ => 0))
    zeroReceiver Fin.elim0 () ≠
      ProbComp.eval (circuitReceiverSimulate (square F)
        ((fun _ => 1), (fun _ => 0)) zeroReceiver ()) := by
  intro heq
  have hv := falseView_real
  rw [heq] at hv
  have hlinear := circuitReceiverSimulate_linear (square F)
    ((fun _ => 1), (fun _ => 0)) zeroReceiver () hv (.inr (.inr 0))
  have hfalse : ¬ (circuitLinearCoeffs (square F) *ᵥ
      voleAdjustReceiver (Fin.init falseView.1.2) falseView.2.1.1.1 falseView.1.1)
        (.inr (.inr 0)) =
      circuitLinearTargets (square F) (fun _ => 1) (fun _ => 0) (.inr (.inr 0)) *
        falseView.1.1 + falseView.2.1.1.2 (.inr (.inr 0)) := by decide
  exact hfalse hlinear

end CslibFrontierTests.Crypto.VOLECircuit
