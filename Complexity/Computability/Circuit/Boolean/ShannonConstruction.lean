/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Minterms
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Shannon synthesis with a shared column library

Split the inputs into a short address block and a data block. Build both tables of minterms,
then every Boolean function of the address block. For each data assignment, select its column
of the supplied truth table, conjoin it with that assignment's minterm, and disjoin the rows.

The construction uses native CSLib circuits and the existing balanced Boolean formulas. Its
finite gate bound counts constants and negations, as well as binary gates. The companion
`ShannonSynthesis` module chooses the address width to obtain a uniform `27 * 2 ^ n / n` bound.

## Main definitions

* `Cslib.Circuits.Boolean.ShannonSynthesis.columnFormula`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.columnLibrary`: disjunction formula for a bit pattern and
  circuit computing all disjunctions of an address minterm table.
* `Cslib.Circuits.Boolean.ShannonSynthesis.column`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.rowFormula`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.outputFormula`: truth-table column index, single-row
  conjunction formula, and final disjunction of rows.
* `Cslib.Circuits.Boolean.ShannonSynthesis.splitMinterms`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.libraryAndData`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.circuit`: block minterm tables, address library paired
  with data minterms, and synthesized circuit on split inputs.
* `Cslib.Circuits.Boolean.ShannonSynthesis.bound`: the finite construction budget.

## Main results

* `Cslib.Circuits.Boolean.ShannonSynthesis.eval_circuit`: correctness of the synthesized circuit.
* `Cslib.Circuits.Boolean.ShannonSynthesis.size_circuit_le`: the complete finite gate ledger.

## References

* [C. E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949].
* Adapted from MassProduction/ShannonCircuit.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShannonSynthesis

variable {k d n : ℕ}

/-- Disjoin exactly the input coordinates selected by a bit vector. -/
def columnFormula (pattern : BitString n) : Formula signature n :=
  Formula.orList (((List.finRange n).filter pattern).map Formula.input)

/-- `columnFormula pattern` evaluates to `true` on `x` if and only if some coordinate `i` has both
`pattern i = true` and `x i = true`. -/
@[simp] theorem eval_columnFormula (pattern x : BitString n) :
    (columnFormula pattern).eval interpretation x =
      decide (∃ i, pattern i = true ∧ x i = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [columnFormula]

/-- A nonempty ambient table bounds even the empty disjunction's constant gate. -/
theorem size_columnFormula_le (hn : 0 < n) (pattern : BitString n) :
    (columnFormula pattern).size ≤ n := by
  let indices := (List.finRange n).filter pattern
  have hlen : indices.length ≤ n := by
    simpa only [List.length_finRange] using List.length_filter_le pattern (List.finRange n)
  change (Formula.orList (indices.map Formula.input)).size ≤ n
  by_cases hnil : indices = []
  · simpa only [hnil, List.map_nil, Formula.orList_nil, Formula.size_const] using
      (show 1 ≤ n by lia)
  · have h := Formula.size_orList_add_one (l := indices.map (Formula.input (σ := signature)))
      (by simpa using hnil)
    simp only [List.map_map, Function.comp_def, Formula.size_input, List.map_const',
      List.sum_replicate, smul_eq_mul, mul_zero, List.length_map, Nat.zero_add] at h
    lia

/-- Every pattern of a table of address minterms is computed once and shared by all data rows. -/
def columnLibrary (k : ℕ) : Circuit signature (2 ^ k) (2 ^ (2 ^ k)) :=
  Circuit.pi fun p => (columnFormula ((BitString.equivFin (2 ^ k)).symm p)).toCircuit

/-- Evaluating `columnLibrary k` on the minterm indicators of `x` yields at output `p` the value of
the `p`th Boolean function at the index of `x`. -/
@[simp] theorem eval_columnLibrary_minterms (x : BitString k) (p : Fin (2 ^ (2 ^ k))) :
    (columnLibrary k).eval interpretation ((mintermCircuit k).eval interpretation x) p =
      (BitString.equivFin (2 ^ k)).symm p (BitString.equivFin k x) := by
  simp only [columnLibrary, Circuit.eval_pi, Formula.eval_toCircuit, eval_columnFormula,
    eval_mintermCircuit]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, exists_eq_right']

/-- `columnLibrary k` has size at most `2 ^ (2 ^ k) * 2 ^ k`. -/
theorem size_columnLibrary_le (k : ℕ) :
    (columnLibrary k).size ≤ 2 ^ (2 ^ k) * 2 ^ k := by
  simp only [columnLibrary, Circuit.size_pi, Formula.size_toCircuit]
  simpa using Finset.sum_le_sum
    (s := Finset.univ) (f := fun p => (columnFormula ((BitString.equivFin (2 ^ k)).symm p)).size)
    (g := fun _ => 2 ^ k) (fun p _ => size_columnFormula_le (pow_pos (by decide) _) _)

/-- The truth-table column at one data assignment, indexed as an address-value bit string. -/
def column (f : BooleanFunction (k + d)) (y : Fin (2 ^ d)) : Fin (2 ^ (2 ^ k)) :=
  BitString.equivFin (2 ^ k) fun a =>
    f (Fin.append ((BitString.equivFin k).symm a) ((BitString.equivFin d).symm y))

/-- One row uses the selected column and the corresponding data minterm. -/
def rowFormula (f : BooleanFunction (k + d)) (y : Fin (2 ^ d)) :
    Formula signature (2 ^ (2 ^ k) + 2 ^ d) :=
  (Formula.input (Fin.natAdd (2 ^ (2 ^ k)) y)).and
    (Formula.input (Fin.castAdd (2 ^ d) (column f y)))

/-- The final disjunction of rows. -/
def outputFormula (f : BooleanFunction (k + d)) : Formula signature (2 ^ (2 ^ k) + 2 ^ d) :=
  Formula.orList (List.ofFn (rowFormula f))

/-- `outputFormula f` has size at most `2 * 2 ^ d`. -/
theorem size_outputFormula_le (f : BooleanFunction (k + d)) :
    (outputFormula f).size ≤ 2 * 2 ^ d := by
  have h := Formula.size_orList_add_one (l := List.ofFn (rowFormula f))
    (by simp [List.ofFn_eq_nil_iff])
  simp only [List.map_ofFn, Function.comp_def, rowFormula, Formula.size_and, Formula.size_input,
    Nat.zero_add, List.ofFn_const, List.sum_replicate, smul_eq_mul, mul_one,
    List.length_ofFn] at h
  change (Formula.orList (List.ofFn (rowFormula f))).size ≤ _
  lia

/-- The two minterm tables read disjoint coordinate blocks. -/
def splitMinterms (k d : ℕ) : Circuit signature (k + d) (2 ^ k + 2 ^ d) :=
  ((mintermCircuit k).comp (Circuit.wiring signature (Fin.castAdd d))).append
    ((mintermCircuit d).comp (Circuit.wiring signature (Fin.natAdd k)))

/-- Compute the address library while retaining the data minterms as free wires. -/
def libraryAndData (k d : ℕ) : Circuit signature (2 ^ k + 2 ^ d) (2 ^ (2 ^ k) + 2 ^ d) :=
  ((columnLibrary k).comp (Circuit.wiring signature (Fin.castAdd (2 ^ d)))).append
    (Circuit.wiring signature (Fin.natAdd (2 ^ k)))

/-- Synthesize a Boolean function from shared minterms, address columns and row selection. -/
def circuit (f : BooleanFunction (k + d)) : Circuit signature (k + d) 1 :=
  (outputFormula f).toCircuit.comp ((libraryAndData k d).comp (splitMinterms k d))

private theorem eval_rowFormula (f : BooleanFunction (k + d)) (x : BitString (k + d))
    (y : Fin (2 ^ d)) :
    (rowFormula f y).eval interpretation
        ((libraryAndData k d).eval interpretation ((splitMinterms k d).eval interpretation x)) =
      (decide (BitString.equivFin d (x ∘ Fin.natAdd k) = y) &&
        f (Fin.append (x ∘ Fin.castAdd d) ((BitString.equivFin d).symm y))) := by
  simp only [rowFormula, Formula.eval_and, Formula.eval_input, libraryAndData, splitMinterms,
    Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring, Fin.append_left,
    Fin.append_right, Function.comp_def]
  rw [eval_columnLibrary_minterms]
  simp only [column, Equiv.symm_apply_apply, eval_mintermCircuit]

/-- The selected row and address column reconstruct the original input. -/
@[simp] theorem eval_circuit (f : BooleanFunction (k + d)) (x : BitString (k + d)) (i : Fin 1) :
    (circuit f).eval interpretation x i = f x := by
  simp only [circuit, Circuit.eval_comp, Formula.eval_toCircuit, outputFormula,
    Formula.eval_orList]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_ofFn]
  simp only [exists_exists_eq_and, eval_rowFormula, Bool.and_eq_true, decide_eq_true_eq]
  simp only [exists_eq_left', Equiv.symm_apply_apply, Function.comp_def,
    Fin.append_castAdd_natAdd]

/-- The complete gate budget, before choosing the split. -/
def bound (k d : ℕ) : ℕ :=
  4 * 2 ^ k + 4 * 2 ^ d + 2 ^ (2 ^ k) * 2 ^ k + 2 * 2 ^ d

/-- Shared minterms, shared columns and the final row disjunction account for every gate. -/
theorem size_circuit_le (f : BooleanFunction (k + d)) : (circuit f).size ≤ bound k d := by
  have hk := size_mintermCircuit_add_three_le k
  have hd := size_mintermCircuit_add_three_le d
  have hlib := size_columnLibrary_le k
  have hout := size_outputFormula_le f
  simp only [circuit, libraryAndData, splitMinterms, Circuit.size_comp, Circuit.size_append,
    Circuit.size_wiring, Formula.size_toCircuit, Nat.zero_add, Nat.add_zero, bound]
  lia

end Cslib.Circuits.Boolean.ShannonSynthesis
