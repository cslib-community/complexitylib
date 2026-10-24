/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.CapacityCircuit

/-!
# Gates with arbitrary scalar activations and mixed capacity costs

Every gate of a real-weight program with arbitrary scalar activations `ℝ → Bool` forms its own
scalar block. Given the values of earlier gates, an input-reading gate `j` applies its activation
`(p.lines j).op.activate` to `t + c` in its aggregated weighted input sum `t`, for a constant `c`
collecting the contributions of earlier gates. When its activation changes at most `T j` times,
the gate's block has capacity cost `max 1 (4 * T j)`, while gates with zero aggregated input
weights are constant in the input sum and have cost `1`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.ActivationOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.activationSignature`,
  `Cslib.Circuits.Boolean.WeightedThreshold.activationInterpretation`: real-weight gates with
  arbitrary scalar activations `ℝ → Bool`.
* `Cslib.Circuits.Boolean.WeightedThreshold.ofWeightedThresholdOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.ofWeightedThreshold`: embedding of the weighted
  threshold signature into the activation signature.
* `Cslib.Circuits.Boolean.WeightedThreshold.activationLineWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.activationInputWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.activationGateWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.activationInputGates`: aggregated wire coefficients
  and input-reading gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.activationBlockDecomposition`: gate-by-gate scalar
  block decomposition.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.cost_activationBlockDecomposition`: exact cost
  `∏ j ∈ activationInputGates p, max 1 (4 * T j)`.
* `Cslib.Circuits.Boolean.WeightedThreshold.two_pow_lt_of_activations`,
  `Cslib.Circuits.Boolean.WeightedThreshold.circuit_two_pow_lt_of_activations`: the C4 mixed
  activation capacity bound.

## References

* [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*,
  Threshold/Internal/Activation][Schlesinger2026Algebraic]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

variable {n g : ℕ}

/-- Post-composition preserves a change bound. -/
theorem _root_.Cslib.ChangesAtMost.map {α β γ : Type*} [Preorder α] {Ψ : α → β} {T : ℕ}
    (h : ChangesAtMost Ψ T) (G : β → γ) :
    ChangesAtMost (fun t => G (Ψ t)) T :=
  fun z hz S hS => h z hz S fun i hi heq => hS i hi (by simp only [heq])

/-- A real-weight linear-combination operation with an arbitrary scalar activation. -/
structure ActivationOp where
  /-- The number of argument slots. -/
  arity : ℕ
  /-- The coefficient of each argument slot. -/
  weight : Fin arity → ℝ
  /-- The scalar activation applied to the weighted sum. -/
  activate : ℝ → Bool

/-- The signature of real-weight gates with arbitrary scalar activations. -/
abbrev activationSignature : Signature := ⟨ActivationOp, ActivationOp.arity⟩

/-- A gate applies its scalar activation to its weighted sum. -/
def activationInterpretation : Interpretation activationSignature Bool :=
  fun op x => op.activate (∑ a, op.weight a * (x a).toNat)

/-- A threshold gate is the activation `t ↦ decide (threshold ≤ t)`. -/
noncomputable def ofWeightedThresholdOp (op : Op) : ActivationOp :=
  ⟨op.arity, op.weight, fun t => decide (op.threshold ≤ t)⟩

/-- The weighted threshold basis embeds gate for gate into the activation basis. -/
noncomputable def ofWeightedThreshold : signature.Hom activationSignature :=
  ⟨ofWeightedThresholdOp, fun _ => rfl⟩

/-- Embedding a weighted threshold gate into the activation basis preserves its semantics. -/
instance preserves_ofWeightedThreshold :
    ofWeightedThreshold.Preserves interpretation activationInterpretation :=
  ⟨fun _ _ => rfl⟩

/-- The combined coefficient of an actual wire in an activation line, summing all slots that
read it. -/
def activationLineWeight (line : Line activationSignature n g) (wire : Wire n g) : ℝ :=
  ∑ a with line.wires a = wire, line.op.weight a

/-- Regrouping argument slots by actual wire preserves their weighted sum. -/
private theorem sum_activationLineWeight_mul (line : Line activationSignature n g)
    (values : Wire n g → ℝ) :
    ∑ a, line.op.weight a * values (line.wires a) =
      ∑ wire, activationLineWeight line wire * values wire := by
  rw [← sum_fiberwise univ line.wires (fun a => line.op.weight a * values (line.wires a))]
  apply sum_congr rfl
  intro wire _
  rw [activationLineWeight, sum_mul]
  apply sum_congr rfl
  intro a ha
  rw [(mem_filter.mp ha).2]

/-- An activation line's value splits into its aggregated input and gate contributions. -/
theorem activationLine_eval_eq (line : Line activationSignature n g)
    (x : Fin n → Bool) (z : Fin g → Bool) :
    line.eval activationInterpretation x z = line.op.activate
      ((∑ i, activationLineWeight line (.input i) * (x i).toNat) +
      ∑ j, activationLineWeight line (.gate j) * (z j).toNat) := by
  unfold Line.eval activationInterpretation
  dsimp only [Function.comp_apply]
  congr 1
  rw [sum_activationLineWeight_mul line (fun wire => (Wire.elim x z wire).toNat)]
  rw [← (Wire.equiv n g).symm.sum_comp (fun wire =>
    activationLineWeight line wire * ((Wire.elim x z wire).toNat : ℝ)), Fintype.sum_sum_type]
  rfl

/-- The direct coefficient of an original input in an activation-program gate. -/
def activationInputWeight (p : Program activationSignature n g)
    (gate : Fin g) (input : Fin n) : ℝ :=
  activationLineWeight (p.lines gate) (.input input)

/-- The coefficient of an internal gate in another gate of an activation program. -/
def activationGateWeight (p : Program activationSignature n g) (gate prior : Fin g) : ℝ :=
  activationLineWeight (p.lines gate) (.gate prior)

/-- A native activation-program gate applies its activation to the sum of its aggregated
input and gate contributions. -/
theorem eval_activationGate_eq (p : Program activationSignature n g)
    (x : Fin n → Bool) (gate : Fin g) :
    p.eval activationInterpretation x gate = (p.lines gate).op.activate
      ((∑ i, activationInputWeight p gate i * (x i).toNat) +
      ∑ j, activationGateWeight p gate j * (p.eval activationInterpretation x j).toNat) := by
  rw [← p.lines_eval activationInterpretation x gate, activationLine_eval_eq]
  rfl

/-- A gate has zero coefficient on its own output and on later gate outputs. -/
private theorem activationGateWeight_eq_zero_of_le (p : Program activationSignature n g)
    (gate prior : Fin g) (h : gate ≤ prior) : activationGateWeight p gate prior = 0 := by
  unfold activationGateWeight activationLineWeight
  apply sum_eq_zero
  intro a ha
  exact (not_lt_of_ge h (p.lt_of_lines_wires_eq_gate gate a prior (mem_filter.mp ha).2)).elim

/-- The gates of an activation program with a nonzero aggregated direct-input coefficient. -/
noncomputable def activationInputGates (p : Program activationSignature n g) : Finset (Fin g) :=
  univ.filter fun gate => ∃ i, activationInputWeight p gate i ≠ 0

/-- A gate belongs to `activationInputGates p` if and only if it has a nonzero direct-input
weight. -/
@[simp]
theorem mem_activationInputGates (p : Program activationSignature n g) (gate : Fin g) :
    gate ∈ activationInputGates p ↔ ∃ i, activationInputWeight p gate i ≠ 0 := by
  classical
  simp [activationInputGates]

/-- Every input coefficient vanishes at a gate outside `activationInputGates p`. -/
theorem activationInputWeight_eq_zero_of_not_mem (p : Program activationSignature n g)
    {gate : Fin g} (h : gate ∉ activationInputGates p) (i : Fin n) :
    activationInputWeight p gate i = 0 := by
  by_contra hi
  exact h ((mem_activationInputGates p gate).mpr ⟨i, hi⟩)

private theorem masked_activation_succ (p : Program activationSignature n g)
    (gate : Fin g) (x : Fin n → Bool) :
    (fun j : Fin g => if j.val < gate.val + 1 then
        p.eval activationInterpretation x j else false) =
      Function.update
        (fun j => if j.val < gate.val then p.eval activationInterpretation x j else false)
        gate ((p.lines gate).op.activate
          ((∑ i, activationInputWeight p gate i * (x i).toNat) +
          ∑ j, activationGateWeight p gate j *
            (if j.val < gate.val then
              p.eval activationInterpretation x j else false).toNat)) := by
  have heval := eval_activationGate_eq p x gate
  have hsum : (∑ j, activationGateWeight p gate j *
      (p.eval activationInterpretation x j).toNat) =
      ∑ j, activationGateWeight p gate j *
        (if j.val < gate.val then p.eval activationInterpretation x j else false).toNat := by
    apply sum_congr rfl
    intro j _
    by_cases hj : j < gate
    · simp [hj]
    · simp [hj, activationGateWeight_eq_zero_of_le p gate j (le_of_not_gt hj)]
  rw [hsum] at heval
  funext j
  by_cases hj : j = gate
  · subst j
    simpa using heval
  · rw [Function.update_of_ne hj]
    have hv : j.val ≠ gate.val := fun h => hj (Fin.ext h)
    have heq : (j.val < gate.val + 1) ↔ j.val < gate.val := by omega
    simp only [heq]

private theorem masked_activation_step (p : Program activationSignature n g)
    (T : Fin g → ℕ)
    (hT : ∀ j ∈ activationInputGates p, ChangesAtMost (p.lines j).op.activate (T j))
    (gate : Fin g) :
    (BlockKind.oneDim (if gate ∈ activationInputGates p then T gate else 0)).Step
      (fun x j => if j.val < gate.val then p.eval activationInterpretation x j else false)
      (fun x j => if j.val < gate.val + 1 then
        p.eval activationInterpretation x j else false) := by
  classical
  by_cases hgate : gate ∈ activationInputGates p
  · simp only [hgate, ite_true, BlockKind.Step]
    refine ⟨activationInputWeight p gate,
      fun z t => Function.update z gate ((p.lines gate).op.activate
        (t + ∑ j, activationGateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact ChangesAtMost.map ((hT gate hgate).comp_monotone (monotone_id.add_const _))
        (Function.update z gate)
    · exact masked_activation_succ p gate
  · simp only [hgate, ite_false, BlockKind.Step]
    refine ⟨fun _ => 0,
      fun z _ => Function.update z gate ((p.lines gate).op.activate
        (∑ j, activationGateWeight p gate j * (z j).toNat)), ?_, ?_⟩
    · intro z
      exact ChangesAtMost.const _
    · intro x
      simpa only [activationInputWeight_eq_zero_of_not_mem p hgate, zero_mul, sum_const_zero,
        zero_add] using masked_activation_succ p gate x

/-- Revealing the gate evaluation of an activation program one gate at a time gives a scalar
block decomposition with per-gate change bounds `T`. -/
noncomputable def activationBlockDecomposition (p : Program activationSignature n g)
    (readout : (Fin g → Bool) → Bool) (T : Fin g → ℕ)
    (hT : ∀ j ∈ activationInputGates p, ChangesAtMost (p.lines j).op.activate (T j)) :
    BlockDecomposition
      (fun x => readout (p.eval activationInterpretation x)) (Fin g → Bool) where
  length := g
  kind := fun i => .oneDim
    (if h : i < g then if ⟨i, h⟩ ∈ activationInputGates p then T ⟨i, h⟩ else 0 else 0)
  history := fun i x j => if j.val < i then p.eval activationInterpretation x j else false
  output := readout
  history_zero := by simp
  step := fun i hi => by
    simpa only [dite_eq_left hi] using masked_activation_step p T hT ⟨i, hi⟩
  output_history := fun x => by simp

/-- Each input-reading gate `j` costs `max 1 (4 * T j)`, and every other gate costs `1`. -/
theorem cost_activationBlockDecomposition (p : Program activationSignature n g)
    (readout : (Fin g → Bool) → Bool) (T : Fin g → ℕ)
    (hT : ∀ j ∈ activationInputGates p, ChangesAtMost (p.lines j).op.activate (T j)) :
    (activationBlockDecomposition p readout T hT).cost =
      ∏ j ∈ activationInputGates p, max 1 (4 * T j) := by
  classical
  simp only [BlockDecomposition.cost, activationBlockDecomposition]
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [dite_eq_left, Fin.isLt]
  have hcost (j : Fin g) :
      (BlockKind.oneDim (if j ∈ activationInputGates p then T j else 0)).cost =
        if j ∈ activationInputGates p then max 1 (4 * T j) else 1 := by
    rw [cost_oneDim_eq_max]
    by_cases h : j ∈ activationInputGates p <;> simp [h]
  simp only [hcost]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **C4: mixed activation gate costs.** If an activation program computes `f` through a Boolean
readout of its gate values, and each input-reading gate `j` has activation changing at most `T j`
times, then `2 ^ n < 4 * K ^ 2 * ∏ j ∈ activationInputGates p, max 1 (4 * T j)`. -/
theorem two_pow_lt_of_activations (p : Program activationSignature n g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction n} {K : ℕ}
    (T : Fin g → ℕ)
    (hT : ∀ j ∈ activationInputGates p, ChangesAtMost (p.lines j).op.activate (T j))
    (hreadout : ∀ x, readout (p.eval activationInterpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ j ∈ activationInputGates p, max 1 (4 * T j) := by
  have h := (activationBlockDecomposition p readout T hT).two_pow_lt_mul_cost
    (fun b => by simpa only [hreadout] using hf b)
  simpa only [cost_activationBlockDecomposition] using h

/-- The C4 mixed-activation bound for a single-output circuit whose output selects a gate. -/
theorem circuit_two_pow_lt_of_activations (c : Circuit activationSignature n 1)
    (houtput : ∃ gate, c.outputs 0 = .gate gate) {f : Cslib.BooleanFunction n} {K : ℕ}
    (T : Fin c.size → ℕ)
    (hT : ∀ j ∈ activationInputGates c.program,
      ChangesAtMost (c.program.lines j).op.activate (T j))
    (hcomputes : ∀ x, c.eval activationInterpretation x 0 = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} K) :
    2 ^ n < 4 * K ^ 2 * ∏ j ∈ activationInputGates c.program, max 1 (4 * T j) := by
  obtain ⟨gate, hgate⟩ := houtput
  apply two_pow_lt_of_activations c.program (fun z => z gate) T hT ?_ hf
  simpa only [Circuit.eval_of_output_eq_gate hgate] using hcomputes

end Cslib.Circuits.Boolean.WeightedThreshold
