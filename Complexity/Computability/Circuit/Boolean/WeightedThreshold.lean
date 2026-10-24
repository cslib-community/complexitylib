/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Basic
public import Complexity.Computability.Circuit.Boolean.Threshold
public import Complexity.Computability.Circuit.Program
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Weighted threshold circuits and their input-reading transcripts

Real-weight threshold gates form a signature for CSLib's existing `Program` and `Circuit`.
A gate returns `true` exactly when its weighted sum is at least its threshold. The model allows
arbitrary real coefficients, repeated argument wires, and nullary gates.

Coefficients are aggregated by actual wire before determining which gates read original inputs.
In particular, repeated weights may cancel. The values of these input-reading gates determine
all internal gate values. Circuit outputs are therefore determined when they select gate wires;
an output selecting an original input is not covered by that conclusion.

These are semantic results. Comparing arbitrary real numbers is noncomputable, and this module
does not assert an algorithm for evaluating rationally encoded circuits.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.Op`,
  `Cslib.Circuits.Boolean.WeightedThreshold.signature`,
  `Cslib.Circuits.Boolean.WeightedThreshold.interpretation`: the weighted threshold basis and its
  Boolean evaluation.
* `Cslib.Circuits.Boolean.WeightedThreshold.ofThresholdOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.ofThreshold`: embedding of the unweighted threshold
  basis.
* `Cslib.Circuits.Boolean.WeightedThreshold.lineWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.inputWeight`,
  `Cslib.Circuits.Boolean.WeightedThreshold.gateWeight`: aggregated wire coefficients of a gate.
* `Cslib.Circuits.Boolean.WeightedThreshold.inputGates`: gates with a nonzero aggregated
  coefficient on an original input.
* `Cslib.Circuits.Boolean.WeightedThreshold.transcript`: the values of these gates.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.eval_gate_eq`: the dense gate equation, with repeated
  wire coefficients aggregated.
* `Cslib.Circuits.Boolean.WeightedThreshold.eval_eq_of_transcript_eq`: the restricted transcript
  determines every internal gate value.
* `Cslib.Circuits.Boolean.WeightedThreshold.circuit_eval_eq_of_transcript_eq`: the corresponding
  statement for circuits whose designated outputs are gates.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Section 3]
  [ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

/-- A real-weight threshold operation with arbitrary finite arity. -/
structure Op where
  /-- The number of argument slots. -/
  arity : ℕ
  /-- The coefficient of each argument slot. -/
  weight : Fin arity → ℝ
  /-- Equality at the threshold returns `true`. -/
  threshold : ℝ

/-- The signature of real-weight threshold gates. -/
abbrev signature : Signature := ⟨Op, Op.arity⟩

/-- A gate is true exactly when its weighted sum is at least its threshold. -/
noncomputable def interpretation : Interpretation signature Bool :=
  fun op x => decide (op.threshold ≤ ∑ a, op.weight a * (x a).toNat)

/-- Unweighted thresholds have unit coefficients, and negation has coefficient `-1` and
threshold zero. -/
def ofThresholdOp : Threshold.Op → Op
  | .not => ⟨1, fun _ => -1, 0⟩
  | .threshold m j => ⟨m, fun _ => 1, j⟩

/-- The existing unweighted threshold basis embeds gate for gate. -/
def ofThreshold : Threshold.signature.Hom signature :=
  ⟨ofThresholdOp, fun op => by cases op <;> rfl⟩

/-- Translating the existing threshold basis preserves its Boolean interpretation. -/
instance preserves_ofThreshold :
    ofThreshold.Preserves Threshold.interpretation interpretation :=
  ⟨fun op x => by
    cases op with
    | not =>
      change decide ((0 : ℝ) ≤ ∑ a : Fin 1, (-1 : ℝ) * (x a).toNat) = !x 0
      cases hx : x 0 <;> simp [hx]
    | threshold m j =>
      change decide ((j : ℝ) ≤ ∑ a, (1 : ℝ) * (x a).toNat) = Cslib.threshold m j x
      rw [Bool.eq_iff_iff, decide_eq_true_iff, Cslib.threshold_eq_true_iff,
        BitString.weight_eq_sum_toNat]
      simp only [one_mul, ← Nat.cast_sum, Nat.cast_le]⟩

variable {n g : ℕ}

/-- The combined coefficient of an actual wire, summing all slots that read it. -/
def lineWeight (line : Line signature n g) (wire : Wire n g) : ℝ :=
  ∑ a with line.wires a = wire, line.op.weight a

/-- Regrouping argument slots by actual wire preserves their weighted sum. -/
private theorem sum_lineWeight_mul (line : Line signature n g) (values : Wire n g → ℝ) :
    ∑ a, line.op.weight a * values (line.wires a) =
      ∑ wire, lineWeight line wire * values wire := by
  rw [← sum_fiberwise univ line.wires (fun a => line.op.weight a * values (line.wires a))]
  apply sum_congr rfl
  intro wire _
  rw [lineWeight, sum_mul]
  apply sum_congr rfl
  intro a ha
  rw [(mem_filter.mp ha).2]

/-- A line's value splits into its aggregated input and gate contributions. -/
theorem line_eval_eq (line : Line signature n g) (x : Fin n → Bool) (z : Fin g → Bool) :
    line.eval interpretation x z = decide (line.op.threshold ≤
      (∑ i, lineWeight line (.input i) * (x i).toNat) +
      ∑ j, lineWeight line (.gate j) * (z j).toNat) := by
  unfold Line.eval interpretation
  dsimp only [Function.comp_apply]
  congr 2
  rw [sum_lineWeight_mul line (fun wire => (Wire.elim x z wire).toNat)]
  rw [← (Wire.equiv n g).symm.sum_comp (fun wire =>
    lineWeight line wire * ((Wire.elim x z wire).toNat : ℝ)), Fintype.sum_sum_type]
  rfl

/-- The direct coefficient of an original input in a program gate. -/
def inputWeight (p : Program signature n g) (gate : Fin g) (input : Fin n) : ℝ :=
  lineWeight (p.lines gate) (.input input)

/-- The coefficient of an internal gate in another gate. -/
def gateWeight (p : Program signature n g) (gate prior : Fin g) : ℝ :=
  lineWeight (p.lines gate) (.gate prior)

/-- A native program gate satisfies the usual dense threshold equation. Coefficients of the
current gate and of later gates are zero by the program's topological order. -/
theorem eval_gate_eq (p : Program signature n g) (x : Fin n → Bool) (gate : Fin g) :
    p.eval interpretation x gate = decide ((p.lines gate).op.threshold ≤
      (∑ i, inputWeight p gate i * (x i).toNat) +
      ∑ j, gateWeight p gate j * (p.eval interpretation x j).toNat) := by
  rw [← p.lines_eval interpretation x gate, line_eval_eq]
  rfl

/-- A gate has zero coefficient on its own output and on later gate outputs. -/
theorem gateWeight_eq_zero_of_le (p : Program signature n g) (gate prior : Fin g)
    (h : gate ≤ prior) : gateWeight p gate prior = 0 := by
  unfold gateWeight lineWeight
  apply sum_eq_zero
  intro a ha
  exact (not_lt_of_ge h (p.lt_of_lines_wires_eq_gate gate a prior (mem_filter.mp ha).2)).elim

/-- The gates with a nonzero aggregated direct-input coefficient. Gates that depend on inputs
only through earlier gates are not counted. -/
noncomputable def inputGates (p : Program signature n g) : Finset (Fin g) :=
  univ.filter fun gate => ∃ i, inputWeight p gate i ≠ 0

/-- A gate belongs to `inputGates p` if and only if it has a nonzero aggregated coefficient on some
original input. -/
@[simp]
theorem mem_inputGates (p : Program signature n g) (gate : Fin g) :
    gate ∈ inputGates p ↔ ∃ i, inputWeight p gate i ≠ 0 := by
  classical
  simp [inputGates]

/-- Every input coefficient vanishes at a gate outside the input-reading set. -/
theorem inputWeight_eq_zero_of_not_mem (p : Program signature n g) {gate : Fin g}
    (h : gate ∉ inputGates p) (i : Fin n) : inputWeight p gate i = 0 := by
  by_contra hi
  exact h ((mem_inputGates p gate).mpr ⟨i, hi⟩)

/-- The restricted activation transcript, indexed by the input-reading gates. -/
noncomputable def transcript (p : Program signature n g) (x : Fin n → Bool) :
    inputGates p → Bool :=
  fun gate => p.eval interpretation x gate

/-- Agreement on input-reading gates before a given bound forces agreement on every gate
before that bound. -/
theorem eval_eq_of_forall_mem_inputGates_lt (p : Program signature n g)
    {x y : Fin n → Bool} (bound : ℕ)
    (h : ∀ gate ∈ inputGates p, (gate : ℕ) < bound →
      p.eval interpretation x gate = p.eval interpretation y gate) :
    ∀ gate : Fin g, (gate : ℕ) < bound →
      p.eval interpretation x gate = p.eval interpretation y gate := by
  intro gate
  induction gate using Fin.strong_induction_on with
  | h gate ih =>
    intro hbound
    by_cases hgate : gate ∈ inputGates p
    · exact h gate hgate hbound
    · rw [eval_gate_eq p x gate, eval_gate_eq p y gate]
      simp only [inputWeight_eq_zero_of_not_mem p hgate, zero_mul,
        sum_const_zero, zero_add]
      congr 2
      apply sum_congr rfl
      intro prior _
      by_cases hprior : prior < gate
      · rw [ih prior hprior (lt_trans hprior hbound)]
      · rw [gateWeight_eq_zero_of_le p gate prior (le_of_not_gt hprior)]
        simp

/-- Agreement on all input-reading gates forces agreement on every gate. -/
theorem eval_eq_of_forall_mem_inputGates (p : Program signature n g) {x y : Fin n → Bool}
    (h : ∀ gate ∈ inputGates p, p.eval interpretation x gate = p.eval interpretation y gate) :
    p.eval interpretation x = p.eval interpretation y :=
  funext fun gate => eval_eq_of_forall_mem_inputGates_lt p g
    (fun gate hgate _ => h gate hgate) gate gate.isLt

/-- The restricted transcript determines the complete gate valuation. -/
theorem eval_eq_of_transcript_eq (p : Program signature n g) {x y : Fin n → Bool}
    (h : transcript p x = transcript p y) : p.eval interpretation x = p.eval interpretation y :=
  eval_eq_of_forall_mem_inputGates p fun gate hgate => congrFun h ⟨gate, hgate⟩

/-- Gate-valued designated outputs are determined by the restricted transcript. The output
hypothesis is necessary: native circuits may select original inputs without any gates. -/
theorem circuit_eval_eq_of_transcript_eq {m : ℕ} (c : Circuit signature n m)
    (houtputs : ∀ output, ∃ gate, c.outputs output = .gate gate) {x y : Fin n → Bool}
    (h : transcript c.program x = transcript c.program y) :
    c.eval interpretation x = c.eval interpretation y := by
  funext output
  obtain ⟨gate, hgate⟩ := houtputs output
  simpa only [Circuit.eval_of_output_eq_gate hgate] using
    congrFun (eval_eq_of_transcript_eq c.program h) gate

end Cslib.Circuits.Boolean.WeightedThreshold
