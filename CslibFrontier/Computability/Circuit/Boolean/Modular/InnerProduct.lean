/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply
public import CslibFrontier.Foundations.Data.BitString.Block

/-!
# Modular inner products of unsigned word arrays

Inputs are the complete first array followed by the complete second array, each in consecutive
least-significant-first word blocks. Products run in parallel, then a balanced carry-save tree
and one carry-lookahead addition compute the sum. The theorem applies to arbitrary raw words.

## Main definitions

* `Cslib.Circuits.Boolean.Modular.innerProduct`: the complete modular inner-product circuit.

## Main results

* `Cslib.Circuits.Boolean.Modular.val_eval_innerProduct`: exact modular inner-product semantics.
* `Cslib.Circuits.Boolean.Modular.depth_innerProduct_le`: logarithmic depth in count and width.

## References

This is the selected-row arithmetic used by [Gentry, Sahai and Waters][GentrySahaiWaters2013],
Sections 3.1 and 3.4, with the modular multiplier and carry-save bounds proved in companion files.
-/

public section

namespace Cslib.Circuits.Boolean.Modular

open BitString
open scoped BigOperators

variable {k w : ℕ}

/-- Read the same word position from each of the two input arrays. -/
private def innerProductInputs (k w : ℕ) (j : Fin k) : Fin (w + w) → Fin (k * w + k * w) :=
  Fin.addCases (fun i => Fin.castAdd (k * w) (finProdFinEquiv (j, i)))
    (fun i => Fin.natAdd (k * w) (finProdFinEquiv (j, i)))

private theorem append_comp_innerProductInputs (j : Fin k) (a b : BitString (k * w)) :
    Fin.append a b ∘ innerProductInputs k w j = Fin.append (block a j) (block b j) := by
  funext i
  refine Fin.addCases (fun h => ?_) (fun h => ?_) i <;>
    simp only [Function.comp_apply, innerProductInputs, Fin.addCases_left, Fin.addCases_right,
      Fin.append_left, Fin.append_right, block_apply]

/-- One modular product of corresponding word blocks. -/
private def innerProductTerm (k w : ℕ) (j : Fin k) : Circuit signature (k * w + k * w) w :=
  (multiply w).comp (Circuit.wiring signature (innerProductInputs k w j))

private theorem val_eval_innerProductTerm (j : Fin k) (a b : BitString (k * w)) :
    (BitString.equivFin w ((innerProductTerm k w j).eval interpretation (Fin.append a b)) : ℕ) =
      ((BitString.equivFin w (block a j) : ℕ) * (BitString.equivFin w (block b j) : ℕ)) %
        2 ^ w := by
  rw [innerProductTerm, Circuit.eval_comp, Circuit.eval_wiring, append_comp_innerProductInputs,
    val_eval_multiply]

/-- Compute all word products in parallel, then sum their carry-save representations. -/
def innerProduct (k w : ℕ) : Circuit signature (k * w + k * w) w :=
  sumPairs (k * w + k * w) w
    (List.ofFn fun j : Fin k => pairWithZero (innerProductTerm k w j))

/-- Exact inner-product value, including empty arrays and zero-width words. -/
theorem val_eval_innerProduct (a b : BitString (k * w)) :
    (BitString.equivFin w ((innerProduct k w).eval interpretation (Fin.append a b)) : ℕ) =
      (∑ j : Fin k, (BitString.equivFin w (block a j) : ℕ) *
        (BitString.equivFin w (block b j) : ℕ)) % 2 ^ w := by
  rw [innerProduct, val_eval_sumPairs]
  simp only [List.map_ofFn, Function.comp_def, pairVal_eval_pairWithZero,
    val_eval_innerProductTerm, Nat.mod_mod, List.sum_ofFn]
  rw [← Finset.sum_nat_mod]

/-- Both multiplication and the sum tree have logarithmic depth in their respective widths. -/
theorem depth_innerProduct_le (k w : ℕ) :
    (innerProduct k w).depth ≤
      17 + 16 * Nat.clog 2 (w + 1) + 12 * Nat.clog 2 k := by
  have h := depth_sumPairs_le
    (List.ofFn fun j : Fin k => pairWithZero (innerProductTerm k w j))
    (D := 9 + 14 * Nat.clog 2 (w + 1)) (by
      intro C hC
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hC
      apply (depth_pairWithZero_le _).trans
      apply max_le _ (by omega)
      exact (Circuit.depth_comp_le _ _).trans (by
        simp only [Circuit.depth_wiring, add_zero]
        exact depth_multiply_le w))
  simp only [List.length_ofFn] at h
  have he : max (9 + 14 * Nat.clog 2 (w + 1)) 1 =
      9 + 14 * Nat.clog 2 (w + 1) := max_eq_left (by omega)
  rw [he] at h
  exact h.trans (by omega)

/-- Every product, fallback, pair-reduction gate and final addition is charged. -/
theorem size_innerProduct_le (k w : ℕ) :
    (innerProduct k w).size ≤ 105 * (k + 1) * (w + 1) ^ 2 := by
  have h := size_sumPairs_le
    (List.ofFn fun j : Fin k => pairWithZero (innerProductTerm k w j))
  simp only [List.map_ofFn, Function.comp_def, size_pairWithZero, innerProductTerm,
    Circuit.size_comp, Circuit.size_wiring, zero_add, List.sum_ofFn, List.length_ofFn] at h
  have hs : (∑ _j : Fin k, ((multiply w).size + 1)) ≤ k * (63 * (w + 1) ^ 2 + 1) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    exact Nat.mul_le_mul_left k (Nat.add_le_add_right (size_multiply_le w) 1)
  apply h.trans
  nlinarith [Nat.zero_le (k * w), Nat.zero_le (k * w ^ 2)]

end Cslib.Circuits.Boolean.Modular
