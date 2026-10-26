/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Majority
public import Complexity.Computability.Circuit.Boolean.Threshold.Parity

/-!
# TC⁰

**TC⁰** is the class of languages decided, at every input length, by circuits of polynomial size
and constant depth whose gates are negations, conjunctions and disjunctions of unbounded fan-in,
and majority gates of unbounded fan-in [Vollmer, Chapter 4][Vollmer1999]: the unbounded fan-in
basis extended by majority (`Unbounded.extInterpretation majority`). Every AC⁰ circuit is a TC⁰
circuit (`AC0_subset_TC0`), and majority is a single gate, so majority is in TC⁰
(`majority_mem_TC0`) but not in AC⁰: **AC⁰ is strictly contained in TC⁰** (`AC0_ssubset_TC0`).

TC⁰ is also the class of the threshold circuits of polynomial size and constant depth
(`TC0_eq_constDepth_threshold`) [Hajnal et al., Section 2][HMPST1993]. A majority gate is a
threshold gate (`Threshold.ofMajority`). Conversely, a threshold gate `Th^m_j` is a majority gate
on its `m` arguments padded with `m + 2` constants, `m + 1 - j` of them `true`, read from two
constant gates (`thresholdCircuitOfMajority`): three gates in depth two, whatever the fan-in. So
parity, which has threshold circuits of depth three and linear size
(`Threshold.parity_mem_constDepth`), is in TC⁰ (`parity_mem_TC0`).

## Main definitions

* `Cslib.Circuits.Boolean.TC0`: the class TC⁰.
* `Cslib.Circuits.Boolean.Threshold.majorityCircuit`: a gate of the threshold basis as a circuit
  with a majority gate.

## Main results

* `Cslib.Circuits.Boolean.AC0_ssubset_TC0`: `AC⁰ ⊊ TC⁰`.
* `Cslib.Circuits.Boolean.TC0_eq_constDepth_threshold`: TC⁰ is the class of threshold circuits of
  polynomial size and constant depth.
* `Cslib.Circuits.Boolean.parity_mem_TC0`: parity is in TC⁰.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [A. Hajnal, W. Maass, P. Pudlák, M. Szegedy, G. Turán, *Threshold circuits of bounded
  depth*][HMPST1993]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- **TC⁰**: the languages over `Bool` decided, at every input length, by circuits with majority
gates of polynomially bounded size and constant depth. -/
def TC0 : Set (Language Bool) :=
  ConstDepth (Unbounded.extInterpretation majority)

/-- **AC⁰ ⊆ TC⁰**: every AC⁰ circuit is a circuit with majority gates. -/
theorem AC0_subset_TC0 : AC0 ⊆ TC0 :=
  ConstDepth.mono Unbounded.toExt

/-- **Majority is in TC⁰**: it is a single gate. -/
theorem majority_mem_TC0 : Language.ofSlices majority ∈ TC0 := by
  refine ConstDepth.mem_iff.2 ⟨1, fun _ => 1, by fun_prop, fun n =>
    ⟨Circuit.oneGate (σ := Unbounded.extSignature) (.gate n) id, fun x => ?_,
      (Circuit.depth_oneGate _ _).le, le_rfl⟩⟩
  funext j
  rw [Language.slice_ofSlices]
  rfl

/-- **AC⁰ is strictly contained in TC⁰.** -/
theorem AC0_ssubset_TC0 : AC0 ⊂ TC0 :=
  Set.ssubset_iff_of_subset AC0_subset_TC0 |>.2 ⟨_, majority_mem_TC0, majority_notMem_AC0⟩

namespace Threshold

/-- A gate of the threshold basis as a circuit over the basis of TC⁰: a negation is a negation, and
the threshold gate `Th^m_j` is a majority gate of `2 m + 2` arguments, its `m` arguments padded with
`m + 1 - j` copies of `true` and the rest copies of `false`. -/
def majorityCircuit : (op : Op) → Circuit Unbounded.extSignature (signature.Arity op) 1
  | .not => Circuit.oneGate (σ := Unbounded.extSignature) (.ac .not) id
  | .threshold m j => thresholdCircuitOfMajority Unbounded.toExt
      (Circuit.oneGate (σ := Unbounded.extSignature) (.gate (m + (m + 2))) id) (min j (m + 1))

/-- The circuit of a gate computes the gate. -/
theorem computes_majorityCircuit (op : Op) :
    (majorityCircuit op).Computes (Unbounded.extInterpretation majority)
      (single (interpretation op)) := by
  intro x
  funext o
  rw [Subsingleton.elim o 0]
  cases op with
  | not => rfl
  | threshold m j =>
    rw [majorityCircuit, eval_thresholdCircuitOfMajority (fun y => funext fun _ => rfl)
      (min_le_right _ _)]
    simp only [single_apply, interpretation_threshold]
    rcases le_total j (m + 1) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, threshold_eq_false_of_lt (show m < m + 1 by omega),
        threshold_eq_false_of_lt (show m < j by omega)]

/-- The circuit of a gate has at most three gates. -/
theorem size_majorityCircuit_le (op : Op) : (majorityCircuit op).size ≤ 3 := by
  cases op with
  | not => simp [majorityCircuit]
  | threshold m j => simp [majorityCircuit, size_thresholdCircuitOfMajority]

/-- The circuit of a gate has depth at most two. -/
theorem depth_majorityCircuit_le (op : Op) : (majorityCircuit op).depth ≤ 2 := by
  cases op with
  | not => simp [majorityCircuit]
  | threshold m j =>
    exact (depth_thresholdCircuitOfMajority_le _).trans (by simp)

end Threshold

/-- **TC⁰ is the class of threshold circuits of polynomial size and constant depth**: majority
gates are threshold gates, and a threshold gate is a majority gate with constants. -/
theorem TC0_eq_constDepth_threshold : TC0 = ConstDepth Threshold.interpretation :=
  (ConstDepth.mono Threshold.ofMajority).antisymm (ConstDepth.subset_of_simulation fun op =>
    ⟨_, Threshold.computes_majorityCircuit op, Threshold.size_majorityCircuit_le op,
      Threshold.depth_majorityCircuit_le op⟩)

/-- **Parity is in TC⁰**: it has threshold circuits of depth three and linear size. -/
theorem parity_mem_TC0 : Language.ofSlices parity ∈ TC0 :=
  TC0_eq_constDepth_threshold ▸ Threshold.parity_mem_constDepth

end Cslib.Circuits.Boolean
