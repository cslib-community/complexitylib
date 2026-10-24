/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Sorting
import Mathlib.Tactic.Ring

/-!
# Sorting records by a computed key

Compute each record's key once, sort the enriched records, and discard the temporary
keys. The same record layout can therefore support successive sorts with different keys.
Keys are ordered lexicographically, with coordinate zero most significant. Complete records,
including duplicates and payload, are preserved; sorting need not be stable.

## Main definitions

* `Cslib.Circuits.Boolean.keyedSortCircuit`: Batcher sorting by a supplied key circuit.

## Main results

* `Cslib.Circuits.Boolean.keyedSortCircuit_perm`: preservation of complete records.
* `Cslib.Circuits.Boolean.monotone_keyedSortCircuit` and
  `Cslib.Circuits.Boolean.antitone_keyedSortCircuit`: recomputed output keys are sorted.
* `Cslib.Circuits.Boolean.four_mul_cost_program_keyedSortCircuit`: exact weighted cost,
  charging key computation once per record. This does not certify constructor runtime.

## References

* Adapted from MassProduction/Nonuniform/KeyedSort.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
* [K. E. Batcher, *Sorting Networks and Their Applications*][Batcher1968].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

variable {k r : ℕ}

/-- Compute keys, sort the enriched records, and retain the original record bodies. -/
def keyedSortCircuit (key : Circuit signature r k) (depth : ℕ) (ascending : Bool) :
    Circuit signature (BitonicSort.arity depth * r) (BitonicSort.arity depth * r) :=
  (Circuit.wiring signature fun i =>
    let jb := finProdFinEquiv.symm i
    finProdFinEquiv (jb.1, Fin.natAdd k jb.2)).comp
      ((bitonicSortCircuit (Fin.castAdd r) depth ascending).comp (pack key depth))
where
  /-- Prepend the computed key to each complete record. -/
  pack (key : Circuit signature r k) (depth : ℕ) :
      Circuit signature (BitonicSort.arity depth * r) (BitonicSort.arity depth * (k + r)) :=
    (key.append (Circuit.id signature r)).replicate (BitonicSort.arity depth)

/-- Packing retains each record after its computed key. -/
theorem eval_keyedSortCircuit_pack (key : Circuit signature r k) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) (j : Fin (BitonicSort.arity depth)) :
    directProductInput ((keyedSortCircuit.pack key depth).eval interpretation x) j =
      Fin.append (key.eval interpretation (directProductInput x j)) (directProductInput x j) := by
  funext b
  simp [keyedSortCircuit.pack, directProductInput, Circuit.eval_replicate_apply]

/-- Each output record is the body of the corresponding sorted enriched record. -/
theorem eval_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ) (ascending : Bool)
    (x : BitString (BitonicSort.arity depth * r)) (j : Fin (BitonicSort.arity depth)) :
    directProductInput ((keyedSortCircuit key depth ascending).eval interpretation x) j =
      directProductInput ((bitonicSortCircuit (Fin.castAdd r) depth ascending).eval interpretation
        ((keyedSortCircuit.pack key depth).eval interpretation x)) j ∘ Fin.natAdd k := by
  funext b
  simp only [keyedSortCircuit, Circuit.eval_comp, Circuit.eval_wiring,
    directProductInput, Function.comp_apply, Equiv.symm_apply_apply]

/-- Sorting by computed keys preserves the multiset of complete records. -/
theorem keyedSortCircuit_perm (key : Circuit signature r k) (depth : ℕ) (ascending : Bool)
    (x : BitString (BitonicSort.arity depth * r)) :
    (List.ofFn (directProductInput
      ((keyedSortCircuit key depth ascending).eval interpretation x))).Perm
        (List.ofFn (directProductInput x)) := by
  have h := (bitonicSortCircuit_perm (Fin.castAdd r) depth ascending
    ((keyedSortCircuit.pack key depth).eval interpretation x)).map
      (fun record : BitString (k + r) => record ∘ Fin.natAdd k)
  rw [funext (eval_keyedSortCircuit key depth ascending x)]
  simpa only [List.map_ofFn, Function.comp_def,
    eval_keyedSortCircuit_pack, Fin.append_right] using h

private theorem output_key (key : Circuit signature r k) (depth : ℕ) (ascending : Bool)
    (x : BitString (BitonicSort.arity depth * r)) (j : Fin (BitonicSort.arity depth)) :
    directProductInput ((bitonicSortCircuit (Fin.castAdd r) depth ascending).eval interpretation
      ((keyedSortCircuit.pack key depth).eval interpretation x)) j ∘ Fin.castAdd r =
        key.eval interpretation
          (directProductInput
            ((keyedSortCircuit key depth ascending).eval interpretation x) j) := by
  rw [eval_keyedSortCircuit]
  have h := bitonicSortCircuit_perm (Fin.castAdd r) depth ascending
    ((keyedSortCircuit.pack key depth).eval interpretation x)
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp (h.mem_iff.mp (List.mem_ofFn.mpr ⟨j, rfl⟩))
  rw [← hi, eval_keyedSortCircuit_pack]
  simp [Function.comp_def, -Fin.natAdd_eq_addNat]

/-- Recomputing the keys of ascending output records gives a nondecreasing sequence. -/
theorem monotone_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Monotone (fun j => toLex (key.eval interpretation
      (directProductInput ((keyedSortCircuit key depth true).eval interpretation x) j))) := by
  simpa only [output_key] using monotone_bitonicSortCircuit (Fin.castAdd r) depth
    ((keyedSortCircuit.pack key depth).eval interpretation x)

/-- Recomputing the keys of descending output records gives a nonincreasing sequence. -/
theorem antitone_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ)
    (x : BitString (BitonicSort.arity depth * r)) :
    Antitone (fun j => toLex (key.eval interpretation
      (directProductInput ((keyedSortCircuit key depth false).eval interpretation x) j))) := by
  simpa only [output_key] using antitone_bitonicSortCircuit (Fin.castAdd r) depth
    ((keyedSortCircuit.pack key depth).eval interpretation x)

/-- Key computation is charged once per record; packing and dropping keys are free wirings. -/
private theorem cost_program_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    (keyedSortCircuit key depth ascending).program.cost cost =
      BitonicSort.arity depth * key.program.cost cost +
        (bitonicSortCircuit (Fin.castAdd r : Fin k → Fin (k + r)) depth ascending).program.cost
          cost := by
  simp only [keyedSortCircuit, keyedSortCircuit.pack, Circuit.cost_program_comp,
    Circuit.cost_program_replicate, Circuit.cost_program_append, Circuit.id,
    Circuit.cost_program_wiring, Nat.add_zero]

/-- Exact weighted cost, including all temporary key gates and comparisons. The factor four
avoids natural division and includes depth zero, empty keys, and empty records. -/
theorem four_mul_cost_program_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ)
    (ascending : Bool) (cost : signature.Op → ℕ) :
    4 * (keyedSortCircuit key depth ascending).program.cost cost =
      4 * 2 ^ depth * key.program.cost cost + depth * (depth + 1) * 2 ^ depth *
        (compareSwapCircuit (Fin.castAdd r : Fin k → Fin (k + r))).program.cost cost := by
  rw [cost_program_keyedSortCircuit, Nat.mul_add, four_mul_cost_program_bitonicSortCircuit,
    BitonicSort.arity_eq_two_pow]
  ring

/-- Exact total gate count, including constants and negations. -/
theorem four_mul_size_keyedSortCircuit (key : Circuit signature r k) (depth : ℕ)
    (ascending : Bool) :
    4 * (keyedSortCircuit key depth ascending).size =
      4 * 2 ^ depth * key.size + depth * (depth + 1) * 2 ^ depth *
        (if k + r = 0 then 0 else 6 * k + 6 * (k + r) + 2) := by
  simpa only [Program.cost_const, one_mul, size_compareSwapCircuit] using
    four_mul_cost_program_keyedSortCircuit key depth ascending (fun _ => 1)

end Cslib.Circuits.Boolean
