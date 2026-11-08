/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.VOLE.MaskedMulCheck
public import CslibFrontier.Computability.Circuit.Arithmetic
public import CslibFrontier.Computability.Circuit.Program
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Probability.PMF.Bind

/-!
# Binding VOLE checks to a public arithmetic circuit

The circuit is the existing straight-line arithmetic circuit, with public inputs followed by
private inputs. Linear MAC openings enforce the public inputs, addition and constant gates,
and the designated public outputs. Multiplication gates use the existing masked batch check.
Repeated wires accumulate coefficients in the linear rows, including in characteristic two.

## Main definitions

* `CircuitMulGate`: indices of multiplication gates in the existing circuit.
* `circuitMulInput`, `circuitMulOutput`: wire indices for the multiplication batch.
* `circuitLinearCoeffs`, `circuitLinearTargets`: the public linear equations.
* `circuitTrace`: the honest wire assignment in the existing VOLE vector layout.
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Circuits
open Interactive Interactive.Spec Probability
open scoped Matrix

variable {F : Type} {p k m : ℕ}

/-- Multiplication-gate indices of the existing arithmetic circuit. -/
abbrev CircuitMulGate (C : Circuit (arithSignature F) (p + k) m) :=
  {i : Fin C.size // (C.program.lines i).op = .mul}

noncomputable instance instFintypeCircuitMulGate
    (C : Circuit (arithSignature F) (p + k) m) : Fintype (CircuitMulGate C) :=
  Fintype.ofFinite _

/-- A multiplication input wire in the flat input-then-gate layout. -/
@[expose] def circuitMulInput (C : Circuit (arithSignature F) (p + k) m)
    (i : CircuitMulGate C) (side : Fin 2) : Fin ((p + k) + C.size) :=
  ((Wire.equiv (p + k) C.size).trans finSumFinEquiv)
    ((C.program.lines i.val).wires (Fin.cast (by rw [i.property]) side))

/-- The multiplication gate's output in the same layout. -/
@[expose] def circuitMulOutput (C : Circuit (arithSignature F) (p + k) m)
    (i : CircuitMulGate C) : Fin ((p + k) + C.size) :=
  Fin.natAdd (p + k) i.val

/-- The public linear equations: public inputs, nonmultiplication gates, then outputs.
Multiplication rows are zero, so the row index is independent of filtering gate operations. -/
@[expose] def circuitLinearCoeffs [CommRing F]
    (C : Circuit (arithSignature F) (p + k) m) :
    Matrix (Fin p ⊕ Fin C.size ⊕ Fin m) (Fin ((p + k) + C.size)) F :=
  let index := (Wire.equiv (p + k) C.size).trans finSumFinEquiv
  fun row => match row with
    | .inl i => Pi.single (index (.input (i.castAdd k))) 1
    | .inr (.inl i) =>
      match C.program.lines i with
      | ⟨.add, wires⟩ =>
        Pi.single (index (wires 0)) 1 + Pi.single (index (wires 1)) 1 -
          Pi.single (index (.gate i)) 1
      | ⟨.mul, _⟩ => 0
      | ⟨.const _, _⟩ => Pi.single (index (.gate i)) 1
    | .inr (.inr j) => Pi.single (index (C.outputs j)) 1

/-- Targets for the public input, gate and output rows. -/
@[expose] def circuitLinearTargets [Zero F]
    (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (y : Fin m → F) : (Fin p ⊕ Fin C.size ⊕ Fin m) → F
  | .inl i => x i
  | .inr (.inl i) => match (C.program.lines i).op with
    | .const c => c
    | _ => 0
  | .inr (.inr j) => y j

/-- The existing circuit trace, flattened into the VOLE input-then-gate vector. -/
@[expose] def circuitTrace [CommRing F]
    (C : Circuit (arithSignature F) (p + k) m)
    (x : Fin p → F) (w : Fin k → F) : Fin ((p + k) + C.size) → F :=
  C.program.trace (arithInterpretation F) (Fin.append x w) ∘
    ((Wire.equiv (p + k) C.size).trans finSumFinEquiv).symm

variable [CommRing F] (C : Circuit (arithSignature F) (p + k) m)

private theorem linear_input (a : Fin ((p + k) + C.size) → F) (i : Fin p) :
    (circuitLinearCoeffs C *ᵥ a) (.inl i) = a ((i.castAdd k).castAdd C.size) := by
  simp [circuitLinearCoeffs, Matrix.mulVec, Wire.equiv, Wire.elim]

private theorem linear_output (a : Fin ((p + k) + C.size) → F) (j : Fin m) :
    (circuitLinearCoeffs C *ᵥ a) (.inr (.inr j)) =
      a (((Wire.equiv (p + k) C.size).trans finSumFinEquiv) (C.outputs j)) := by
  simp [circuitLinearCoeffs, Matrix.mulVec]

/-- The honest trace satisfies all public linear equations when its designated output is `y`. -/
theorem circuitTrace_linear (x : Fin p → F) (w : Fin k → F) (y : Fin m → F)
    (hy : C.eval (arithInterpretation F) (Fin.append x w) = y) :
    circuitLinearCoeffs C *ᵥ circuitTrace C x w = circuitLinearTargets C x y := by
  funext row
  rcases row with i | (i | j)
  · rw [linear_input]
    simp [circuitTrace, circuitLinearTargets, Wire.equiv]
  · have h := C.program.trace_gate (arithInterpretation F) (Fin.append x w) i
    cases he : C.program.lines i with
    | mk op wires =>
      rw [he] at h
      cases op with
      | add =>
        change C.program.trace (arithInterpretation F) (Fin.append x w) (.gate i) =
          C.program.trace (arithInterpretation F) (Fin.append x w) (wires 0) +
            C.program.trace (arithInterpretation F) (Fin.append x w) (wires 1) at h
        simpa [circuitLinearCoeffs, circuitLinearTargets, he, Matrix.mulVec, circuitTrace,
          dotProduct, Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul,
          Pi.single_apply] using sub_eq_zero.mpr h.symm
      | mul => simp [circuitLinearCoeffs, circuitLinearTargets, he, Matrix.mulVec]
      | const c =>
        change C.program.trace (arithInterpretation F) (Fin.append x w) (.gate i) = c at h
        simpa [circuitLinearCoeffs, circuitLinearTargets, he, Matrix.mulVec, circuitTrace]
          using h
  · rw [linear_output]
    simpa [circuitTrace, circuitLinearTargets, Circuit.eval] using congrFun hy j

/-- The honest trace satisfies every multiplication gate, including shared input wires. -/
theorem circuitTrace_mul (x : Fin p → F) (w : Fin k → F) (i : CircuitMulGate C) :
    circuitTrace C x w (circuitMulInput C i 0) *
      circuitTrace C x w (circuitMulInput C i 1) =
        circuitTrace C x w (circuitMulOutput C i) := by
  have h := C.program.trace_gate (arithInterpretation F) (Fin.append x w) i.val
  have ho : circuitMulOutput C i =
      ((Wire.equiv (p + k) C.size).trans finSumFinEquiv) (.gate i.val) := rfl
  simp only [ho, circuitTrace, circuitMulInput, Function.comp_apply, Equiv.symm_apply_apply]
  have evalMul (line : Line (arithSignature F) (p + k) C.size) (hm : line.op = .mul) :
      arithInterpretation F line.op (fun j =>
        C.program.trace (arithInterpretation F) (Fin.append x w) (line.wires j)) =
      C.program.trace (arithInterpretation F) (Fin.append x w)
          (line.wires (Fin.cast (by rw [hm]) 0)) *
        C.program.trace (arithInterpretation F) (Fin.append x w)
          (line.wires (Fin.cast (by rw [hm]) 1)) := by
    rcases line with ⟨op, wires⟩
    cases hm
    rfl
  exact (evalMul _ i.property).symm.trans h.symm

/-- A wire assignment satisfying all public linear equations and multiplication gates gives
an actual private input witness for the public circuit output. -/
theorem exists_witness_of_circuitChecks (x : Fin p → F) (y : Fin m → F)
    (a : Fin ((p + k) + C.size) → F)
    (hlinear : circuitLinearCoeffs C *ᵥ a = circuitLinearTargets C x y)
    (hmul : ∀ i : CircuitMulGate C,
      a (circuitMulInput C i 0) * a (circuitMulInput C i 1) = a (circuitMulOutput C i)) :
    ∃ w : Fin k → F, C.eval (arithInterpretation F) (Fin.append x w) = y := by
  let index := (Wire.equiv (p + k) C.size).trans finSumFinEquiv
  let v : Wire (p + k) C.size → F := a ∘ index
  let w : Fin k → F := fun i => v (.input (i.natAdd p))
  have hinput (i : Fin (p + k)) : v (.input i) = Fin.append x w i := by
    induction i using Fin.addCases with
    | left i =>
      have hi := congrFun hlinear (.inl i)
      simpa [linear_input, circuitLinearTargets, v, index, Wire.equiv, Wire.elim] using hi
    | right i => simp [w]
  have hgate (i : Fin C.size) :
      v (.gate i) = arithInterpretation F (C.program.lines i).op
        (fun j => v ((C.program.lines i).wires j)) := by
    have hi := congrFun hlinear (.inr (.inl i))
    cases he : C.program.lines i with
    | mk op wires =>
      cases op with
      | add =>
        change v (.gate i) = v (wires 0) + v (wires 1)
        have hz : v (wires 0) + v (wires 1) - v (.gate i) = 0 := by
          simpa [circuitLinearCoeffs, circuitLinearTargets, he, Matrix.mulVec, dotProduct,
            Finset.sum_add_distrib, Finset.sum_sub_distrib, add_mul, sub_mul, Pi.single_apply,
            v, index] using hi
        exact (sub_eq_zero.mp hz).symm
      | mul =>
        change v (.gate i) = v (wires 0) * v (wires 1)
        have h := hmul ⟨i, by rw [he]⟩
        simp only [circuitMulInput, circuitMulOutput] at h
        have wireEq (line : Line (arithSignature F) (p + k) C.size)
            (ws : Fin 2 → Wire (p + k) C.size) (hl : line = ⟨.mul, ws⟩)
            (hop : line.op = .mul) (side : Fin 2) :
            line.wires (Fin.cast (by rw [hop]) side) = ws side := by
          subst line
          rfl
        rw [wireEq _ wires he (by rw [he]) 0, wireEq _ wires he (by rw [he]) 1] at h
        simpa [v, index, Wire.equiv, Wire.elim] using h.symm
      | const c =>
        change v (.gate i) = c
        simpa [circuitLinearCoeffs, circuitLinearTargets, he, Matrix.mulVec, v, index] using hi
  have htrace := Program.eq_trace_of_forall_gate hinput hgate
  refine ⟨w, funext fun j => ?_⟩
  change C.program.trace (arithInterpretation F) (Fin.append x w) (C.outputs j) = y j
  rw [← htrace]
  have hj := congrFun hlinear (.inr (.inr j))
  simpa only [linear_output, circuitLinearTargets, v, index, Function.comp_apply] using hj

/-- The circuit messages use the existing three-move shape: corrections and linear MAC masks,
public multiplication weights, then the masked affine reply. -/
abbrev circuitCheckSpec (C : Circuit (arithSignature F) (p + k) m) : Spec :=
  SigmaProtocol.sigmaSpec
    ((Fin ((p + k) + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F))
    (CircuitMulGate C → F) (F × F)

variable [Fintype F] [DecidableEq F]

/-- The actual circuit verifier: homomorphic linear openings and the existing masked batch.
The row equivalence merely presents the public matrix rows to `voleVerifyOpening`. -/
@[expose] noncomputable def circuitVerify
    (statement : (Fin p → F) × (Fin m → F))
    (share : F × (Fin (((p + k) + C.size) + 1) → F))
    (first : (Fin ((p + k) + C.size) → F) × ((Fin p ⊕ Fin C.size ⊕ Fin m) → F))
    (r : CircuitMulGate C → F) (reply : F × F) : Bool :=
  let rows : (Fin p ⊕ Fin C.size ⊕ Fin m) ≃ Fin (p + (C.size + m)) :=
    (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv
  let adjusted := voleAdjustReceiver (Fin.init share.2) first.1 share.1
  decide (voleVerifyOpening ((circuitLinearCoeffs C *ᵥ adjusted) ∘ rows.symm) share.1
      (circuitLinearTargets C statement.1 statement.2 ∘ rows.symm) (first.2 ∘ rows.symm) ∧
    maskedMulCheckValue (fun i => circuitMulInput C i 0) (fun i => circuitMulInput C i 1)
      (circuitMulOutput C) share.1 share.2 first.1 r = reply.1 * share.1 + reply.2)

/-- A public-circuit reduction in the same role-local cached VOLE world. The honest prover
receives only sender vectors; linear openings are fixed together with corrections before weights. -/
@[expose] noncomputable def circuitCheck :
    Reduction (voleSenderSpec F (((p + k) + C.size) + 1))
      (voleReceiverSpec F (((p + k) + C.size) + 1)) (circuitCheckSpec C)
      ((Fin p → F) × (Fin m → F)) (Fin k → F) Unit Unit where
  prover statement w := do
    let (u, v) ← ProbOracleComp.query ()
    let a := circuitTrace C statement.1 w
    return (show ProbOracleComp (voleSenderSpec F (((p + k) + C.size) + 1))
      (_ × ((CircuitMulGate C → F) →
        ProbOracleComp (voleSenderSpec F (((p + k) + C.size) + 1))
          (ProbOracleComp (voleSenderSpec F (((p + k) + C.size) + 1))
            ((F × F) × (Unit × Unit))))) from
      pure ((voleCommitWitness a (Fin.init u), circuitLinearCoeffs C *ᵥ Fin.init v),
        fun r => pure (pure (maskedMulCheckReply (fun i => circuitMulInput C i 0)
          (fun i => circuitMulInput C i 1) (circuitMulOutput C) a u v r, ((), ())))))
  verifier := {
    samplers := (ProbComp.uniform (CircuitMulGate C → F), ())
    decide := fun statement challenges => do
      let share ← OracleComp.query
        (spec := voleReceiverSpec F (((p + k) + C.size) + 1) ⊕ₒ
          msgSpec (circuitCheckSpec C)) (.inl ())
      let first ← OracleComp.query
        (spec := voleReceiverSpec F (((p + k) + C.size) + 1) ⊕ₒ
          msgSpec (circuitCheckSpec C)) (.inr (.inl ()))
      let reply ← OracleComp.query
        (spec := voleReceiverSpec F (((p + k) + C.size) + 1) ⊕ₒ
          msgSpec (circuitCheckSpec C)) (.inr (.inr (.inl ())))
      return if circuitVerify C statement share first challenges.1 reply then some () else none }

/-- The actual verifier reads only its own cached share and the public transcript. -/
theorem circuitCheck_output (statement : (Fin p → F) × (Fin m → F))
    (t : Transcript (circuitCheckSpec C)) :
    (circuitCheck C).verifier.output
      (oP := voleSenderSpec F (((p + k) + C.size) + 1)) statement t = (do
      let share ← ProbOracleComp.query
        (spec := voleSenderSpec F (((p + k) + C.size) + 1) ⊕ₒ
          voleReceiverSpec F (((p + k) + C.size) + 1)) (.inr ())
      return if circuitVerify C statement share t.1 t.2.1 t.2.2.1 then some () else none) := by
  unfold Verifier.output circuitCheck
  rw [OracleComp.interpret_bind, OracleComp.interpret_query]
  simp only [OracleComp.sumHandler]
  congr 1

omit [Fintype F] [DecidableEq F] in
/-- Linear MACs authenticate the assignment fixed by the sender's correction message. -/
theorem circuitLinear_adjusted
    (c : VOLECorrelation F (((p + k) + C.size) + 1)) (hc : c.Valid)
    (d : Fin ((p + k) + C.size) → F) (row : Fin p ⊕ Fin C.size ⊕ Fin m) :
    (circuitLinearCoeffs C *ᵥ voleAdjustReceiver (Fin.init c.w) d c.delta) row =
      (circuitLinearCoeffs C *ᵥ (Fin.init c.u + d)) row * c.delta +
        (circuitLinearCoeffs C *ᵥ Fin.init c.v) row := by
  let base : VOLECorrelation F ((p + k) + C.size) :=
    ⟨Fin.init c.u, Fin.init c.v, c.delta, Fin.init c.w⟩
  have hbase : base.Valid := fun i => hc i.castSucc
  exact (hbase.addConst d).linearComb (circuitLinearCoeffs C row)

omit [Fintype F] in
/-- Honest circuit replies pass both linear openings and multiplication verification. -/
theorem circuitVerify_correct (x : Fin p → F) (w : Fin k → F) (y : Fin m → F)
    (hy : C.eval (arithInterpretation F) (Fin.append x w) = y)
    (c : VOLECorrelation F (((p + k) + C.size) + 1)) (hc : c.Valid)
    (r : CircuitMulGate C → F) :
    circuitVerify C (x, y) c.receiverView
      (voleCommitWitness (circuitTrace C x w) (Fin.init c.u),
        circuitLinearCoeffs C *ᵥ Fin.init c.v) r
      (maskedMulCheckReply (fun i => circuitMulInput C i 0) (fun i => circuitMulInput C i 1)
        (circuitMulOutput C) (circuitTrace C x w) c.u c.v r) = true := by
  rw [circuitVerify, decide_eq_true_eq]
  refine ⟨?_, maskedMulCheckReply_correct _ _ _ _ c hc r (circuitTrace_mul C x w)⟩
  intro i
  change (circuitLinearCoeffs C *ᵥ
    voleAdjustReceiver (Fin.init c.w) (voleCommitWitness (circuitTrace C x w) (Fin.init c.u))
      c.delta) _ = _
  rw [circuitLinear_adjusted C c hc]
  have hadd : Fin.init c.u + voleCommitWitness (circuitTrace C x w) (Fin.init c.u) =
      circuitTrace C x w := by
    simp [voleCommitWitness]
  rw [hadd, circuitTrace_linear C x w y hy]
  rfl

/-- The actual role-local reduction has perfect completeness for the public circuit relation. -/
theorem circuitCheck_complete :
    (circuitCheck C).Complete (voleWorld F (((p + k) + C.size) + 1))
      (fun statement w => C.eval (arithInterpretation F) (Fin.append statement.1 w) = statement.2)
      Interactive.Accept 0 := by
  rintro ⟨x, y⟩ w hy
  have hrun : (voleWorld F (((p + k) + C.size) + 1)).eval ((circuitCheck C).run (x, y) w) =
      (do
        let c ← voleIdealDist F (((p + k) + C.size) + 1)
        let r ← PMF.uniformOfFintype (CircuitMulGate C → F)
        return (((voleCommitWitness (circuitTrace C x w) (Fin.init c.u),
          circuitLinearCoeffs C *ᵥ Fin.init c.v),
          (r, (maskedMulCheckReply (fun i => circuitMulInput C i 0)
            (fun i => circuitMulInput C i 1) (circuitMulOutput C)
            (circuitTrace C x w) c.u c.v r, ()))), some (), ((), ()))) := by
    simp only [World.eval, Reduction.run, Verifier.execute, circuitCheck_output]
    simp only [circuitCheck, liftProver, runStrategy, circuitCheckSpec, SigmaProtocol.sigmaSpec,
      ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query,
      OracleComp.interpret_bind, OracleComp.interpret_pure, voleWorld,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query, ProbOracleComp.runWith_pure,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.map_bind, PMF.pure_map, pure_bind, VOLECorrelation.senderView]
    apply PMF.bind_congr_on_support
    intro c hc
    rw [← ProbOracleComp.sample]
    simp only [ProbOracleComp.runWith_sample, ProbComp.eval_uniform, PMF.bind_map,
      Function.comp_def, PMF.pure_bind]
    congr 1
    funext r
    simp only [circuitVerify_correct C x w y hy c (valid_of_mem_support_voleIdealDist hc) r,
      ite_true]
  rw [hrun]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq,
    Interactive.Accept]
  simp

end Cslib.Crypto.Protocols.VOLE
