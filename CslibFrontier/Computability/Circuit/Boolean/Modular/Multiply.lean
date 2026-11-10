/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.PartialProduct
import Mathlib.Tactic.Ring

/-!
# Logarithmic-depth modular multiplication

All shifted partial products are generated in parallel, reduced along the existing half-split
carry-save tree, and finished by carry lookahead. The result is the product modulo `2 ^ w` on
every pair of words. Width zero uses the actual empty carry-save fallback and finishing circuit.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.multiply`: the complete unsigned modular multiplier.

## Main results

* `Cslib.Circuits.Boolean.Modular.val_eval_multiply`: exact multiplication modulo `2 ^ w`.
* `Cslib.Circuits.Boolean.Modular.depth_multiply_le`: depth at most `9 + 14 * clog 2 (w + 1)`.
* `Cslib.Circuits.Boolean.Modular.size_multiply_le`: at most `63 * (w + 1)^2` gates.

## References

Binary partial products and carry-save reduction follow [Vollmer, Chapter 1][Vollmer1999];
parallel-prefix finishing follows [Ladner and Fischer][LadnerFischer1980].
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open BitString
open scoped BigOperators

variable {w : ℕ}

/-- Reduce all shifted partial products and finish their sum with carry lookahead. -/
@[expose] def multiply (w : ℕ) : Circuit signature (w + w) w :=
  sumPairs (w + w) w (List.ofFn fun i : Fin w => pairWithZero (partialProduct w i))

/-- The circuit computes the modular product of arbitrary input words. -/
theorem val_eval_multiply (a b : BitString w) :
    (BitString.equivFin w ((multiply w).eval interpretation (Fin.append a b)) : ℕ) =
      ((BitString.equivFin w a : ℕ) * (BitString.equivFin w b : ℕ)) % 2 ^ w := by
  rw [multiply, val_eval_sumPairs]
  simp only [List.map_ofFn, Function.comp_def, pairVal_eval_pairWithZero,
    val_eval_partialProduct, List.sum_ofFn]
  have ht (i : Fin w) :
      (if b i then ((BitString.equivFin w a : ℕ) * 2 ^ i.val) % 2 ^ w else 0) % 2 ^ w =
        ((BitString.equivFin w a : ℕ) * ((b i).toNat * 2 ^ i.val)) % 2 ^ w := by
    cases b i <;> simp
  simp_rw [ht]
  rw [← Finset.sum_nat_mod, ← Finset.mul_sum, ← BitString.val_equivFin_eq_sum]

/-- The balanced pair tree uses one-level leaves and logarithmic-depth finishing. -/
theorem depth_multiply_le (w : ℕ) :
    (multiply w).depth ≤ 9 + 14 * Nat.clog 2 (w + 1) := by
  have h := depth_sumPairs_le
    (List.ofFn fun i : Fin w => pairWithZero (partialProduct w i)) (D := 1) (by
      intro C hC
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hC
      exact (depth_pairWithZero_le _).trans (max_le (depth_partialProduct_le i) le_rfl))
  simp only [List.length_ofFn, max_self] at h
  have hm : Nat.clog 2 w ≤ Nat.clog 2 (w + 1) := Nat.clog_mono_right 2 (Nat.le_succ w)
  exact h.trans (by omega)

/-- Every partial product and every carry-save gate is charged. -/
theorem size_multiply_le (w : ℕ) : (multiply w).size ≤ 63 * (w + 1) ^ 2 := by
  have h := size_sumPairs_le (List.ofFn fun i : Fin w => pairWithZero (partialProduct w i))
  simp only [List.map_ofFn, Function.comp_def, size_pairWithZero, size_partialProduct,
    List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    List.length_ofFn] at h
  exact h.trans (by nlinarith)

end Cslib.Circuits.Boolean.Modular
