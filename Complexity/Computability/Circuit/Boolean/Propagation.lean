/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Propagation
public import Cslib.Computability.Circuit.Boolean.Basic
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Linear-size segmented propagation circuits

Source bits occupy the first input block and links the second. The circuit outputs every
prefix value of `BitString.propagate`: one false constant initializes the computation, and
each record adds an AND gate and an OR gate. Earlier values are shared wires, so the gate
count is linear even when links connect a long run.

## Main definitions

* `Cslib.Circuits.Boolean.propagateCircuit`: all prefix values in input order.

## Main results

* `Cslib.Circuits.Boolean.eval_propagateCircuit`: agreement with the functional recurrence.
* `Cslib.Circuits.Boolean.eval_propagateCircuit_eq_true_iff`: a connected true source exists.
* `Cslib.Circuits.Boolean.cost_program_propagateCircuit`: exact arbitrary weighted cost.
* `Cslib.Circuits.Boolean.size_propagateCircuit`: one constant and two gates per record.

Weighted cost distinguishes conventions that charge the initial constant from those that
make constants free. The zero-record circuit still contains its unused initial constant.
The constructor is executable; these gate counts do not certify its running time.

## References

* Adapted from MassProduction/Nonuniform/Propagation.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

/-- All propagated prefix values, sharing earlier values as circuit wires. -/
def propagateCircuit (count : ℕ) : Circuit signature (count + count) count where
  program := program count count le_rfl
  outputs := fun index => .gate ⟨2 * (index.val + 1), by lia⟩
where
  /-- Two gates per processed record, after a single false constant. -/
  program (count : ℕ) : (processed : ℕ) → processed ≤ count →
      Program signature (count + count) (1 + 2 * processed)
    | 0, _ => .gate .empty ⟨.const false, Fin.elim0⟩
    | processed + 1, fits =>
      let previous := program count processed (by lia)
      let linked := previous.gate ⟨.and,
        ![.input (Fin.natAdd count ⟨processed, by lia⟩), .gate ⟨2 * processed, by lia⟩]⟩
      linked.gate ⟨.or,
        ![.input (Fin.castAdd count ⟨processed, by lia⟩), .gate (Fin.last (1 + 2 * processed))]⟩
  /-- Extend a finite input block by false beyond its endpoint. -/
  inputBlock {count : ℕ} (x : BitString count) (i : ℕ) : Bool :=
    if h : i < count then x ⟨i, h⟩ else false

open propagateCircuit

/-- Every earlier prefix value is retained at the corresponding even-numbered gate. -/
theorem eval_propagateCircuit_program {count : ℕ} (x : BitString (count + count))
    (processed : ℕ) (fits : processed ≤ count) (prefixCount : ℕ) (hle : prefixCount ≤ processed) :
    (program count processed fits).eval interpretation x ⟨2 * prefixCount, by lia⟩ =
      BitString.propagate (inputBlock (x ∘ Fin.castAdd count))
        (inputBlock (x ∘ Fin.natAdd count)) prefixCount := by
  induction processed generalizing prefixCount with
  | zero =>
    have : prefixCount = 0 := by lia
    subst prefixCount
    rfl
  | succ processed ih =>
    by_cases last : prefixCount = processed + 1
    · subst prefixCount
      have lastIndex : (⟨2 * (processed + 1), by lia⟩ : Fin (1 + 2 * (processed + 1))) =
          Fin.last (1 + 2 * processed + 1) := by apply Fin.ext; simp only [Fin.val_last]; lia
      rw [lastIndex, program, Program.eval_gate_last]
      simp only [Line.eval, interpretation, Function.comp_apply, Matrix.cons_val_zero,
        Matrix.cons_val_one, Wire.elim_input, Wire.elim_gate, Program.eval_gate_last]
      rw [ih (by lia) processed le_rfl]
      simp [BitString.propagate, inputBlock, show processed < count by lia]
    · have oldIndex : (⟨2 * prefixCount, by lia⟩ : Fin (1 + 2 * (processed + 1))) =
          (⟨2 * prefixCount, by lia⟩ : Fin (1 + 2 * processed)).castSucc.castSucc := rfl
      rw [oldIndex, program, Program.eval_gate_castSucc, Program.eval_gate_castSucc]
      exact ih (by lia) prefixCount (by lia)

/-- Every output is the recurrence value after processing its record. -/
theorem eval_propagateCircuit {count : ℕ} (x : BitString (count + count)) (j : Fin count) :
    (propagateCircuit count).eval interpretation x j =
      BitString.propagate (inputBlock (x ∘ Fin.castAdd count))
        (inputBlock (x ∘ Fin.natAdd count)) (j.val + 1) := by
  exact eval_propagateCircuit_program x count le_rfl (j.val + 1) j.isLt

/-- A finite-array interface: a true output has an earlier true source connected by links.
The link at the source itself need not be true. -/
theorem eval_propagateCircuit_eq_true_iff {count : ℕ} (source link : BitString count)
    (j : Fin count) :
    (propagateCircuit count).eval interpretation (Fin.append source link) j = true ↔
      ∃ start : Fin count, start ≤ j ∧ source start = true ∧
        ∀ index : Fin count, start < index → index ≤ j → link index = true := by
  rw [eval_propagateCircuit, BitString.propagate_eq_true_iff]
  simp only [Function.comp_def, Fin.append_left, Fin.append_right]
  constructor
  · rintro ⟨start, before, starts, links⟩
    have hstart : start < count := by lia
    refine ⟨⟨start, hstart⟩, Nat.le_of_lt_succ before, ?_, ?_⟩
    · simpa only [inputBlock, dite_eq_left hstart] using starts
    · intro index after before
      simpa only [inputBlock, dite_eq_left index.isLt] using
        links index.val after (Nat.lt_succ_of_le before)
  · rintro ⟨start, before, starts, links⟩
    refine ⟨start.val, Nat.lt_succ_of_le before, ?_, ?_⟩
    · simpa only [inputBlock, dite_eq_left start.isLt] using starts
    · intro index after before
      have hindex : index < count := by lia
      simpa only [inputBlock, dite_eq_left hindex] using
        links ⟨index, hindex⟩ after (Nat.le_of_lt_succ before)

/-- Each prefix contributes one AND and one OR, independently of the input links. -/
private theorem cost_propagateCircuit_program (count processed : ℕ) (fits : processed ≤ count)
    (cost : signature.Op → ℕ) :
    (program count processed fits).cost cost =
      cost (.const false) + processed * (cost .and + cost .or) := by
  induction processed with
  | zero => simp [program]
  | succ processed ih =>
    simp only [program, Program.cost_gate, ih]
    ring

/-- The exact weighted cost includes the initial constant, even for zero records. -/
theorem cost_program_propagateCircuit (count : ℕ) (cost : signature.Op → ℕ) :
    (propagateCircuit count).program.cost cost =
      cost (.const false) + count * (cost .and + cost .or) :=
  cost_propagateCircuit_program count count le_rfl cost

/-- The circuit contains one false constant and two gates per record. -/
@[simp] theorem size_propagateCircuit (count : ℕ) :
    (propagateCircuit count).size = 1 + 2 * count := rfl

end Cslib.Circuits.Boolean
