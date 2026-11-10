/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.Circuit
public import CslibFrontier.Crypto.Protocols.VOLE.BatchMulCheck
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Tactic.PMFSwap

/-!
# Soundness of the circuit-bound ideal VOLE session

The sender's actual role-local execution fixes its correction and linear openings without access
to the receiver key. The hidden key can therefore be sampled after the sender's adaptive reply.

## Main results

* `circuitCheck_eval_execute`: the delayed-key law for arbitrary randomized sender strategies.
* `circuitVerify_sample_iff`: the linear and multiplication equations of the actual verifier.
* `toOuterMeasure_circuitVerify_le`: the conditional case-split bound for a fixed first message.
* `circuitCheck_sound`: soundness for false public circuit statements against every sender.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Circuits Interactive Interactive.Spec Probability
open scoped Matrix ENNReal

variable {F : Type} {p k m : ℕ}

section Ring

variable [CommRing F] [Fintype F] [DecidableEq F]

omit [CommRing F] [Fintype F] [DecidableEq F] in
private theorem interpret_liftProver {n : ℕ} {α : Type}
    (c : VOLECorrelation F n) (program : ProbOracleComp (voleSenderSpec F n) α) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (OracleComp.sumHandler (fun _ => PMF.pure c.senderView)
        (fun _ => PMF.pure c.receiverView)))
      (liftProver (oV := voleReceiverSpec F n) program) =
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (fun _ => PMF.pure c.senderView)) program := by
  rw [liftProver, OracleComp.interpret_interpret]
  congr 1 with q : 1
  rcases q with q | q <;>
    simp [OracleComp.sumHandler, ProbOracleComp.query]

/-- The actual malicious sender, including initialization, private coins and repeated setup reads,
uses only its two vectors. Its first message is fixed before weights, and its complete adaptive
reply is independent of the hidden key sampled last in this equal output law. -/
theorem circuitCheck_eval_execute (C : Circuit (arithSignature F) (p + k) m)
    {α : Type} (statement : (Fin p → F) × (Fin m → F))
    (P : ProbOracleComp (voleSenderSpec F (((p + k) + C.size) + 1))
      (ProverStrategy (ProbOracleComp (voleSenderSpec F (((p + k) + C.size) + 1)))
        (circuitCheckSpec C) α)) :
    (voleWorld F (((p + k) + C.size) + 1)).eval
      ((circuitCheck C).verifier.execute statement P) = (do
        let u ← PMF.uniformOfFintype (Fin (((p + k) + C.size) + 1) → F)
        let v ← PMF.uniformOfFintype (Fin (((p + k) + C.size) + 1) → F)
        let senderLaw {β : Type} := OracleComp.interpret (m := PMF) (α := β)
          (OracleComp.sumHandler ProbComp.unifOracle (fun _ : Unit => PMF.pure (u, v)))
        let st ← senderLaw P
        let (first, next) ← senderLaw st
        let r ← PMF.uniformOfFintype (CircuitMulGate C → F)
        let response ← senderLaw (next r)
        let (reply, result) ← senderLaw response
        let delta ← PMF.uniformOfFintype F
        return ((first, (r, (reply, ()))),
          (if circuitVerify C statement (voleSample u v delta).receiverView first r reply
            then some () else none), result)) := by
  rw [voleWorld_eval]
  simp only [voleIdealDist, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_bind, PMF.pure_bind]
  congr 1 with u : 1
  congr 1 with v : 1
  simp only [Verifier.execute, OracleComp.interpret_bind, interpret_liftProver,
    circuitCheck_output, OracleComp.interpret_pure]
  simp only [runStrategy, circuitCheck, circuitCheckSpec, SigmaProtocol.sigmaSpec,
    OracleComp.interpret_bind, OracleComp.interpret_pure,
    ProbOracleComp.interpret_sample,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    VOLECorrelation.senderView, voleSample]
  have huniform : OracleComp.interpret ProbComp.unifOracle
      (ProbComp.uniform (CircuitMulGate C → F)) =
      PMF.uniformOfFintype (CircuitMulGate C → F) := ProbComp.eval_uniform _
  simp only [huniform, ProbOracleComp.interpret_query, OracleComp.sumHandler, PMF.pure_bind]
  pmf_swap
  rfl


omit [Fintype F] in
/-- With a valid sampled correlation, the verifier checks the extracted linear assignment and
one weighted multiplication polynomial. The fresh affine mask is subtracted from the reply. -/
theorem circuitVerify_sample_iff (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (u v : Fin (((p + k) + C.size) + 1) → F)
    (first : (Fin ((p + k) + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F))
    (r : CircuitMulGate C → F) (reply : F × F) (delta : F) :
    let a := Fin.init u + first.1
    circuitVerify C statement (voleSample u v delta).receiverView first r reply = true ↔
      (∀ row, (circuitLinearCoeffs C *ᵥ a) row * delta +
          (circuitLinearCoeffs C *ᵥ Fin.init v) row =
        circuitLinearTargets C statement.1 statement.2 row * delta + first.2 row) ∧
      (∑ i, r i * ((a (circuitMulInput C i 0) * delta + v (circuitMulInput C i 0).castSucc) *
          (a (circuitMulInput C i 1) * delta + v (circuitMulInput C i 1).castSucc) -
          (a (circuitMulOutput C i) * delta + v (circuitMulOutput C i).castSucc) * delta)) =
        (reply.1 - u (Fin.last ((p + k) + C.size))) * delta +
          (reply.2 - v (Fin.last ((p + k) + C.size))) := by
  dsimp only
  rw [circuitVerify, decide_eq_true_eq]
  apply and_congr
  · let rows : (Fin p ⊕ Fin C.size ⊕ Fin m) ≃ Fin (p + (C.size + m)) :=
      (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
    change (∀ i, (circuitLinearCoeffs C *ᵥ
      voleAdjustReceiver (Fin.init (voleSample u v delta).w) first.1 delta) (rows.symm i) =
      circuitLinearTargets C statement.1 statement.2 (rows.symm i) * delta +
        first.2 (rows.symm i)) ↔ _
    have hlinear (row : Fin p ⊕ Fin C.size ⊕ Fin m) :
        (circuitLinearCoeffs C *ᵥ
          voleAdjustReceiver (Fin.init (voleSample u v delta).w) first.1 delta) row =
        (circuitLinearCoeffs C *ᵥ (Fin.init u + first.1)) row * delta +
          (circuitLinearCoeffs C *ᵥ Fin.init v) row :=
      circuitLinear_adjusted C _ (valid_voleSample u v delta) first.1 row
    simp only [hlinear]
    constructor
    · intro h row
      simpa only [Equiv.symm_apply_apply] using h (rows row)
    · intro h i
      exact h (rows.symm i)
  · have hadjust : voleAdjustReceiver (Fin.init (voleSample u v delta).w) first.1 delta =
        fun j => (Fin.init u + first.1) j * delta + v j.castSucc := by
      funext j
      simp only [voleAdjustReceiver, Fin.init, voleSample, Pi.add_apply]
      ring
    rw [maskedMulCheckValue]
    simp only [VOLECorrelation.receiverView]
    simp only [voleSample] at hadjust ⊢
    rw [hadjust]
    change _ + (u (Fin.last _) * delta + v (Fin.last _)) = _ ↔ _
    constructor <;> intro h <;> linear_combination h


end Ring

section Field

variable [Field F] [Fintype F] [DecidableEq F]

/-- A false public statement passes the circuit verifier with at most the batch mixture bound.
The correction and linear openings are fixed before the weights; the reply may depend arbitrarily
and randomly on those weights. This is the conditional bound used by the actual sender execution. -/
theorem toOuterMeasure_circuitVerify_le (C : Circuit (arithSignature F) (p + k) m)
    (statement : (Fin p → F) × (Fin m → F))
    (hfalse : ¬ ∃ w, C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2)
    (u v : Fin (((p + k) + C.size) + 1) → F)
    (first : (Fin ((p + k) + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F))
    (reply : (CircuitMulGate C → F) → PMF (F × F)) :
    (do
      let r ← PMF.uniformOfFintype (CircuitMulGate C → F)
      let ab ← reply r
      let delta ← PMF.uniformOfFintype F
      return circuitVerify C statement (voleSample u v delta).receiverView first r ab
    ).toOuterMeasure {true} ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞)) := by
  let a := Fin.init u + first.1
  by_cases hlinear : circuitLinearCoeffs C *ᵥ a =
      circuitLinearTargets C statement.1 statement.2
  · have hmul : ∃ i : CircuitMulGate C,
        a (circuitMulInput C i 0) * a (circuitMulInput C i 1) ≠ a (circuitMulOutput C i) := by
      by_contra h
      push Not at h
      exact hfalse (exists_witness_of_circuitChecks C statement.1 statement.2 a hlinear h)
    have hbound := toOuterMeasure_voleMulCheck_batch_le
      (fun i => a (circuitMulInput C i 0)) (fun i => a (circuitMulInput C i 1))
      (fun i => a (circuitMulOutput C i)) (fun i => v (circuitMulInput C i 0).castSucc)
      (fun i => v (circuitMulInput C i 1).castSucc) (fun i => v (circuitMulOutput C i).castSucc)
      (fun r => (reply r).map fun ab =>
        (ab.1 - u (Fin.last _), ab.2 - v (Fin.last _))) hmul
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
      PMF.bind_map, Function.comp_def] at hbound ⊢
    refine le_trans ?_ hbound
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun r => mul_le_mul_of_nonneg_left ?_ zero_le
    rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine tsum_le_tsum fun ab => mul_le_mul_of_nonneg_left ?_ zero_le
    change ((PMF.uniformOfFintype F).map _).toOuterMeasure {true} ≤
      ((PMF.uniformOfFintype F).map _).toOuterMeasure {true}
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply MeasureTheory.measure_mono
    intro delta hdelta
    exact decide_eq_true ((circuitVerify_sample_iff C statement u v first r ab delta).mp hdelta).2
  · have hsmall : (do
        let r ← PMF.uniformOfFintype (CircuitMulGate C → F)
        let ab ← reply r
        let delta ← PMF.uniformOfFintype F
        return circuitVerify C statement (voleSample u v delta).receiverView first r ab
      ).toOuterMeasure {true} ≤ (Fintype.card F : ℝ≥0∞)⁻¹ := by
      simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
      apply PMF.toOuterMeasure_bind_le
      intro r
      apply PMF.toOuterMeasure_bind_le
      intro ab
      let rows : (Fin p ⊕ Fin C.size ⊕ Fin m) ≃ Fin (p + (C.size + m)) :=
        (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
      have hne : circuitLinearTargets C statement.1 statement.2 ∘ rows.symm ≠
          (circuitLinearCoeffs C *ᵥ a) ∘ rows.symm := by
        intro h
        apply hlinear
        funext row
        simpa using (congrFun h (rows row)).symm
      refine le_trans ?_ (toOuterMeasure_voleVerifyOpening_le
        (v := (circuitLinearCoeffs C *ᵥ Fin.init v) ∘ rows.symm)
        (v' := first.2 ∘ rows.symm) hne)
      change ((PMF.uniformOfFintype F).map _).toOuterMeasure {true} ≤ _
      rw [PMF.toOuterMeasure_map_apply]
      apply MeasureTheory.measure_mono
      intro delta hdelta i
      exact ((circuitVerify_sample_iff C statement u v first r ab delta).mp hdelta).1
        (rows.symm i)
    exact hsmall.trans (le_add_right le_rfl)


/-- Information-theoretic soundness for the public circuit language in the actual cached VOLE
world, against every role-local sender strategy. A false linear row has error at most `1 / |F|`;
otherwise a false public statement forces a false multiplication gate and the batch mixture bound
applies. These are disjoint assignment cases, so their bounds are not added. -/
theorem circuitCheck_sound (C : Circuit (arithSignature F) (p + k) m) :
    (circuitCheck C).verifier.Sound (voleWorld F (((p + k) + C.size) + 1))
      {statement | ∃ w, C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2}
      Set.univ ((Fintype.card F : ℝ≥0∞)⁻¹ +
        (1 - (Fintype.card F : ℝ≥0∞)⁻¹) * (2 / (Fintype.card F : ℝ≥0∞))) := by
  intro statement hfalse α P
  rw [circuitCheck_eval_execute]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply PMF.toOuterMeasure_bind_le
  intro u
  apply PMF.toOuterMeasure_bind_le
  intro v
  apply PMF.toOuterMeasure_bind_le
  intro st
  apply PMF.toOuterMeasure_bind_le
  intro first
  let senderLaw {β : Type} := OracleComp.interpret (m := PMF) (α := β)
    (OracleComp.sumHandler ProbComp.unifOracle (fun _ : Unit => PMF.pure (u, v)))
  have hbound := toOuterMeasure_circuitVerify_le C statement hfalse u v first.1
    (fun r => do
      let response ← senderLaw (first.2 r)
      let answer ← senderLaw response
      return answer.1)
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind,
    PMF.pure_bind, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply] at hbound ⊢
  convert hbound using 1
  simp [senderLaw]

end Field

end Cslib.Crypto.Protocols.VOLE
