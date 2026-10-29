/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Stage
public import Complexity.Algorithms.MatrixMultiplication.Schonhage.CoordinateTransform

/-!
# Agreement of the flat tensor transform with the public encodings

The digit numbering is supplied by Mathlib's `finFunctionFinEquiv`. The explicit alphabet
numberings contain exactly the original seven variables and ten terms. The final mixed-radix
transform is `encodingL` or `encodingR` for every depth, including zero.

## Main results

* `Encoding.value_final_left`, `Encoding.value_final_right`: unchanged public encoding semantics.

## References

The original encodings and coefficients are from [AlmanWilliams2026, Section 2.4.1], selectively
adapted from Anthropic, PBC's formal source; see `Encoding` for the exact pin and paths.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding

open Cslib.Algorithms.MatrixMultiplication.Schonhage
open CoordinateTransform

/-- The numbered output position of a term string. -/
def leafIndex {L : ℕ} (τ : Leaf L) : Fin (10 ^ L) :=
  finFunctionFinEquiv fun i => termDigits.symm (τ i)

private theorem value_final_alphabet {α : Type} [Fintype α] (e : Fin 7 ≃ α)
    (c : Term → α → ℤ) {L : ℕ} (a : (Fin L → α) → ℤ) (arr : ℕ → ℤ)
    (harr : ∀ u : Fin L → Fin 7, arr (finFunctionFinEquiv u) = a (fun i => e (u i)))
    (τ : Leaf L) :
    value (table (fun t s => c (termAt t) (e s))) L 0 arr (leafIndex τ) 0 =
      encodeWith c τ a := by
  have h := value_final (fun t s => c (termAt t) (e s)) L
    (fun u => a (fun i => e (u i))) arr harr (fun i => termDigits.symm (τ i))
  change value (table (fun t s => c (termAt t) (e s))) L 0 arr
    (finFunctionFinEquiv fun i => termDigits.symm (τ i)) 0 = _
  rw [h]
  unfold encodeWith
  refine Fintype.sum_equiv (Equiv.piCongrRight fun _ : Fin L => e) _ _ ?_
  intro u
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change c (termDigits (termDigits.symm (τ i))) (e (u i)) = c (τ i) (e (u i))
  rw [Equiv.apply_symm_apply]

/-- The flat shared left transform equals the existing `encodingL` on every leaf. -/
theorem value_final_left {L : ℕ} (a : LeftStr L → ℤ) (arr : ℕ → ℤ)
    (harr : ∀ u : Fin L → Fin 7, arr (finFunctionFinEquiv u) = a (fun i => leftAt (u i)))
    (τ : Leaf L) :
    value (table (coefficients false)) L 0 arr (leafIndex τ) 0 = encodingL a τ :=
  value_final_alphabet leftDigits phi a arr harr τ

/-- The flat shared right transform equals the existing `encodingR` on every leaf. -/
theorem value_final_right {L : ℕ} (a : RightStr L → ℤ) (arr : ℕ → ℤ)
    (harr : ∀ u : Fin L → Fin 7, arr (finFunctionFinEquiv u) = a (fun i => rightAt (u i)))
    (τ : Leaf L) :
    value (table (coefficients true)) L 0 arr (leafIndex τ) 0 = encodingR a τ :=
  value_final_alphabet rightDigits psi a arr harr τ

/-- The native stage's row-wise specification is the next shared-prefix value. This includes
the quotient/remainder decomposition of its actual flat loop counter. -/
theorem stageResult_value (side : Bool) (j k i : ℕ) (arr : ℕ → ℤ) :
    stageResult side (7 ^ k)
      (fun i a => value (table (coefficients side)) j (k + 1) arr
        (i / (10 * 7 ^ k)) (a.val * 7 ^ k + i % 7 ^ k)) i =
      value (table (coefficients side)) (j + 1) k arr (i / 7 ^ k) (i % 7 ^ k) := by
  have hdiv : i / 7 ^ k / 10 = i / (10 * 7 ^ k) := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (7 ^ k) 10]
  have hprefix : i / (10 * 7 ^ k) * 10 + i / 7 ^ k % 10 = i / 7 ^ k := by
    simpa only [hdiv, Nat.mul_comm] using Nat.div_add_mod (i / 7 ^ k) 10
  have he := value_step (table (coefficients side)) j k arr (i / (10 * 7 ^ k))
    (i % 7 ^ k) (Nat.mod_lt (i / 7 ^ k) (by decide : 0 < 10))
  rw [hprefix] at he
  unfold stageResult
  rw [he, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  simp only [table, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding
