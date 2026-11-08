/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.SourceComplexity
import CslibFrontier.Computability.Circuit.Arithmetic

/-!
# Supplied-source complexity contracts

These clients distinguish source-only computation from raw-input/helper computation, zero
weighted cost from wiring, and vacuous correctness from existence of a syntactic circuit.
They also exercise a proper support, composition and independent source/carrier universes.
-/

namespace ComplexityTests.SourceComplexity

open Cslib.Circuits

private def I : Interpretation (arithSignature ℚ) ℚ := arithInterpretationWith ℚ id

-- Constant supplied values cannot reveal raw inputs, even with every rational constant gate.
example : ecomplexityFrom I ArithOp.mulCost (id : (Fin 1 → ℚ) → Fin 1 → ℚ)
    (fun _ (_ : Fin 1) => 0) = ⊤ := by
  apply ecomplexityFrom_eq_top_of_fiber_collision (x := fun _ => 0) (y := fun _ => 1) rfl
  intro h
  have hzero := congrFun h 0
  norm_num at hzero

-- The native helper convention supplies the raw inputs, making the same target free.
example : ecomplexityGiven I (id : (Fin 1 → ℚ) → Fin 1 → ℚ)
    (fun _ (_ : Fin 1) => 0) = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact (ecomplexityGiven_le_ecomplexity _ _).trans_eq (ecomplexity_wiring id)

private def addInputs (x : Fin 2 → ℚ) : Fin 1 → ℚ := fun _ => x 0 + x 1

private theorem addInputs_free : ecomplexityFrom I ArithOp.mulCost addInputs id = 0 := by
  apply nonpos_iff_eq_zero.mp
  exact ecomplexityFrom_le_of_computesFrom
    (Circuit.oneGate (σ := arithSignature ℚ) .add id) (fun _ => rfl)

-- A finite zero budget still produces a witness even when gates have zero weight.
example : ∃ c : Circuit (arithSignature ℚ) 2 1,
    c.ComputesFrom I addInputs id ∧ c.program.cost ArithOp.mulCost ≤ 0 :=
  ecomplexityFrom_le_iff.mp addInputs_free.le

-- Free addition produces a value that no wiring can return on every input.
example : ¬ ∃ select : Fin 1 → Fin 2, ∀ x, addInputs x = x ∘ select := by
  rintro ⟨select, h⟩
  have htwo := congrFun (h (fun _ => 1)) 0
  norm_num [addInputs] at htwo

private abbrev noOps : Signature where
  Op := Empty
  Arity := Empty.elim

private def noOpsI : Interpretation noOps Unit := fun op => op.elim

-- Correctness is vacuous on Empty, but no zero-input, one-output circuit can be built.
example : ecomplexityFrom noOpsI Empty.elim
    (fun x : Empty => x.elim : Empty → Fin 1 → Unit)
    (fun x : Empty => x.elim : Empty → Fin 0 → Unit) = ⊤ := by
  rw [ecomplexityFrom_eq_top_iff]
  rintro ⟨⟨p, outputs⟩, _⟩
  cases p with
  | empty => cases outputs 0 with
    | input i => exact i.elim0
    | gate i => exact i.elim0
  | gate p line => exact line.op.elim

-- With no requested outputs, the empty wiring does exist and costs zero.
example : ecomplexityFrom noOpsI Empty.elim
    (fun x : Empty => (x.elim : Fin 0 → Unit) ∘ id)
    (fun x : Empty => (x.elim : Fin 0 → Unit)) = 0 :=
  ecomplexityFrom_wiring _ id

-- Addition becomes wiring on the proper support where the first input is zero.
example : ecomplexityOn I {x : Fin 2 → ℚ | x 0 = 0} addInputs = 0 := by
  rw [← ecomplexityFrom_unit_subtype]
  apply nonpos_iff_eq_zero.mp
  apply ecomplexityFrom_le_of_computesFrom
    (Circuit.wiring (arithSignature ℚ) (fun _ : Fin 1 => (1 : Fin 2)))
  intro x
  funext j
  change x.val 1 = x.val 0 + x.val 1
  rw [x.property, zero_add]

-- Two source-only computations compose without charging for supplied intermediate values twice.
example : ecomplexityFrom I ArithOp.mulCost
    (fun x : Fin 1 → ℚ => fun _ : Fin 1 => (x 0 * x 0) * (x 0 * x 0)) id ≤ 2 := by
  let square := fun x : Fin 1 → ℚ => fun _ : Fin 1 => x 0 * x 0
  let fourth := fun x : Fin 1 → ℚ => fun _ : Fin 1 => (x 0 * x 0) * (x 0 * x 0)
  have hs : ecomplexityFrom I ArithOp.mulCost square id ≤ 1 :=
    ecomplexityFrom_le_of_computesFrom
      (Circuit.oneGate (σ := arithSignature ℚ) (n := 1) .mul (fun _ => 0)) (fun _ => rfl)
  have hf : ecomplexityFrom I ArithOp.mulCost fourth square ≤ 1 :=
    ecomplexityFrom_le_of_computesFrom
      (Circuit.oneGate (σ := arithSignature ℚ) (n := 1) .mul (fun _ => 0)) (fun _ => rfl)
  exact (ecomplexityFrom_comp_le square fourth id).trans (add_le_add hs hf)

-- The source domain need not share the carrier or operation universe.
universe u v w
example {σ : Signature.{v}} {U : Type u} {X : Type w} (J : Interpretation σ U)
    (cost : σ.Op → ℕ) (sources : X → Fin 2 → U) :
    ecomplexityFrom J cost (fun x => sources x ∘ ![1, 0, 1]) sources = 0 :=
  ecomplexityFrom_wiring sources _

end ComplexityTests.SourceComplexity
