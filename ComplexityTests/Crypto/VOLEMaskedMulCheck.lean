/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Protocols.VOLE.MaskedMulCheck

/-!
# Full-view simulation clients and negative examples

The single wire is reused in every gate position: `w * w = w`. Zero and one are different
satisfying witnesses. Over F3, two is a false witness and its real view can fail verification.
Without the extra masking correlation, even the two true witnesses give different full views.
-/

namespace ComplexityTests.Crypto.VOLEMaskedMulCheck

open Cslib Cslib.Probability Cslib.Interactive Cslib.Interactive.Spec
  Cslib.Crypto.Protocols.VOLE

private def wire : Fin 1 → Fin 1 := fun _ => 0

-- Distinct true witnesses, with all three gate positions sharing the same wire.
example : maskedMulCheckView (F := ZMod 3) wire wire wire (fun _ => 0) =
    maskedMulCheckView wire wire wire (fun _ => 1) := by
  rw [maskedMulCheckView_eq_simulate wire wire wire _ (by decide),
    maskedMulCheckView_eq_simulate wire wire wire _ (by decide)]

example : (maskedMulCheck (F := ZMod 2) wire wire wire).Complete
    (voleWorld (ZMod 2) 2) (fun _ w => ∀ i, w (wire i) * w (wire i) = w (wire i))
    Accept 0 := maskedMulCheck_complete wire wire wire

example : maskedMulCheckView (F := ZMod 2) wire wire wire (fun _ => 1) =
    ProbComp.eval (maskedMulCheckSimulate wire wire wire) :=
  maskedMulCheckView_eq_simulate wire wire wire _ (by decide)

-- Honest privacy needs no field hypothesis; ZMod4 has zero divisors.
example : maskedMulCheckView (F := ZMod 4) wire wire wire (fun _ => 1) =
    ProbComp.eval (maskedMulCheckSimulate wire wire wire) :=
  maskedMulCheckView_eq_simulate wire wire wire _ (by decide)

-- No wires and no gates still consume exactly one fresh masking coordinate.
example : maskedMulCheckView (F := ZMod 3) (Fin.elim0 : Fin 0 → Fin 0) Fin.elim0 Fin.elim0
    Fin.elim0 = ProbComp.eval (maskedMulCheckSimulate Fin.elim0 Fin.elim0 Fin.elim0) :=
  maskedMulCheckView_eq_simulate _ _ _ _ (fun i => Fin.elim0 i)

-- Zero key is permitted. No inversion of the receiver key appears in the simulator.
example (r : Fin 1 → ZMod 3) :
    maskedMulCheckValue wire wire wire 0 ![1, 2]
        (voleCommitWitness (fun _ => 1) (Fin.init ![2, 1])) r =
      (maskedMulCheckReply wire wire wire (fun _ => 1) ![2, 1] ![1, 2] r).1 * 0 +
        (maskedMulCheckReply wire wire wire (fun _ => 1) ![2, 1] ![1, 2] r).2 := by
  exact maskedMulCheckReply_correct wire wire wire (fun _ => 1)
    (voleSample ![2, 1] ![1, 2] 0) (valid_voleSample _ _ _) r (by decide)

-- The receiver share is stable even when a sender query occurs between receiver reads.
example : (voleWorld (ZMod 2) 2).eval (do
    let first ← ProbOracleComp.query (.inr ())
    let _ ← ProbOracleComp.query (.inl ())
    let second ← ProbOracleComp.query (.inr ())
    return decide (first = second)) = PMF.pure true := by
  simp [World.eval, voleWorld, PMF.map_bind, PMF.bind_bind, PMF.bind_const]

private def falseView :
    ((ZMod 3) × (Fin 2 → ZMod 3)) × Transcript (maskedMulCheckSpec (ZMod 3) (Fin 1) 1) :=
  ((1, fun _ => 0), ((fun _ => 2), ((fun _ => 1), ((0, 0), ()))))

private theorem falseView_real : falseView ∈
    (maskedMulCheckView wire wire wire (fun _ => (2 : ZMod 3))).support := by
  rw [maskedMulCheckView_eq]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
    PMF.mem_support_pure_iff]
  refine ⟨voleSample (fun _ => 0) (fun _ => 0) 1,
    (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _),
    (fun _ => 1), PMF.mem_support_uniformOfFintype _, ?_⟩
  decide

-- The satisfying-witness hypothesis cannot be dropped from the distribution equality.
example : maskedMulCheckView wire wire wire (fun _ => (2 : ZMod 3)) ≠
    ProbComp.eval (maskedMulCheckSimulate wire wire wire) := by
  intro heq
  have hv := falseView_real
  rw [heq] at hv
  have hcheck := maskedMulCheckSimulate_accepts wire wire wire hv
  have hfalse : ¬ (maskedMulCheckValue wire wire wire falseView.1.1 falseView.1.2
      falseView.2.1 falseView.2.2.1 =
        falseView.2.2.2.1.1 * falseView.1.1 + falseView.2.2.2.1.2) := by decide
  exact hfalse hcheck

/-- An intentionally unblinded one-gate view, retaining the private share and public correction. -/
private noncomputable def unblinded (w : ZMod 3) : PMF
    (((ZMod 3) × (Fin 1 → ZMod 3)) × (Fin 1 → ZMod 3) × (ZMod 3 × ZMod 3)) :=
  (voleIdealDist (ZMod 3) 1).map fun c =>
    (c.receiverView, voleCommitWitness (fun _ => w) c.u,
      (voleMulCrossTerm w (c.v 0) w (c.v 0) (c.v 0), voleMulConstTerm (c.v 0) (c.v 0)))

private def leakedView :
    (((ZMod 3) × (Fin 1 → ZMod 3)) × (Fin 1 → ZMod 3) × (ZMod 3 × ZMod 3)) :=
  ((1, fun _ => 0), (fun _ => 0), (0, 0))

-- A concrete full-view event separates two valid witnesses when masking is omitted.
example : leakedView ∈ (unblinded 0).support ∧ leakedView ∉ (unblinded 1).support := by
  constructor
  · simp only [unblinded, PMF.mem_support_map_iff]
    refine ⟨voleSample (fun _ => 0) (fun _ => 0) 1,
      (mem_support_voleIdealDist_iff _).mpr (valid_voleSample _ _ _), ?_⟩
    decide
  · simp only [unblinded, PMF.mem_support_map_iff, mem_support_voleIdealDist_iff]
    decide

end ComplexityTests.Crypto.VOLEMaskedMulCheck
