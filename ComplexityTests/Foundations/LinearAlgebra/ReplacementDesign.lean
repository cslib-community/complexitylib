/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.LinearAlgebra.ReplacementDesign
import Mathlib.Tactic.NormNum

/-!
# Tests for `Complexity.Foundations.LinearAlgebra.ReplacementDesign`

Concrete smoke tests and nonvacuous witnesses for Lemma 4.1's binomial fiber counts,
equation (4.8)'s tail bound, equation (4.16)'s total measurement row bound, `ReplacementDesign`,
and Lemma 4.7 (`exists_replacementDesign`).
-/

@[expose] public noncomputable section

namespace Cslib.LinearAlgebra.ReplacementDesignTests

open Finset Matrix Polynomial
open scoped BigOperators
open Cslib.BalancedSchedules

/-- Slot-level antisymmetric and symmetric pair counts for `r = 2, 3, 4`:
`#(antisymPairs 2) = 1`, `#(symPairs 2) = 3`,
`#(antisymPairs 3) = 3`, `#(symPairs 3) = 6`,
`#(antisymPairs 4) = 6`, `#(symPairs 4) = 10`. -/
example :
    #(antisymPairs 2) = 1 ∧ #(symPairs 2) = 3 ∧
      #(antisymPairs 3) = 3 ∧ #(symPairs 3) = 6 ∧
      #(antisymPairs 4) = 6 ∧ #(symPairs 4) = 10 := by
  simp only [card_antisymPairs, card_symPairs]
  decide

/-- For `Q = 2, r = 2`, the `D = 2 ^ 4 = 16` auxiliary basis vectors split by `antisymCount` into
fibers of size `9` (`j = 0`), `6` (`j = 1`), and `1` (`j = 2`). -/
example :
    #(univ.filter (fun β : AuxLabel 2 2 => antisymCount β = 0)) = 9 ∧
      #(univ.filter (fun β : AuxLabel 2 2 => antisymCount β = 1)) = 6 ∧
      #(univ.filter (fun β : AuxLabel 2 2 => antisymCount β = 2)) = 1 := by
  simp only [card_filter_antisymCount_eq]
  decide

/-- Remark 4.4 / Lemma 4.1 (`Q = 2, r = 2, A₀ = 0, R = 2`):
only `j = 2` lies outside `[0, 2)`, so `#(measurementIndices 2 2 0 2) = 1` and
`binomTailProb 2 2 0 2 = 1 / 16`. -/
example :
    #(measurementIndices 2 2 0 2) = 1 ∧
      binomTailProb 2 2 0 2 = 1 / 16 ∧
      (#(measurementIndices 2 2 0 2) : ℚ) ≤ (1 / 16 : ℚ) * ((2 ^ (2 * 2) : ℕ) : ℚ) := by
  have hcard : #(measurementIndices 2 2 0 2) = 1 := by
    rw [card_measurementIndices_eq]
    decide
  have hprob : binomTailProb 2 2 0 2 = 1 / 16 := by
    rw [binomTailProb_eq_div 2 2 0 2 (by decide), hcard]
    norm_num
  refine ⟨hcard, hprob, ?_⟩
  exact card_measurementIndices_le_of_binomTailProb_le (by decide : 0 < 2) hprob.le

/-- Full binomial distribution sum (`R = 0`) equals `1`, and every tail probability lies in
`[0, 1]`. -/
example (Q A₀ R : ℕ) :
    binomTailProb Q 2 A₀ 0 = 1 ∧
      0 ≤ binomTailProb Q 2 A₀ R ∧
      binomTailProb Q 2 A₀ R ≤ 1 :=
  ⟨binomTailProb_zero_right Q 2 A₀ (by decide),
    binomTailProb_nonneg (by decide),
    binomTailProb_le_one Q 2 A₀ R (by decide)⟩

/-- Nonvacuous witness of **Lemma 4.7 (`exists_replacementDesign`)** on `n = 16384` variables with
singleton scopes (`b = 1, w = 1, M = 16384`) and parameters `Q = 3, r = 2, A₀ = 0, R = 2,
τ = 1 / 2`:
- `D = 2 ^ 6 = 64`,
- `2 * (b + w) * D ^ 2 = 4 * 4096 = 16384 ≤ M`,
- `2 * Q * r ^ 2 = 24 ≤ 16384 = n`,
- `binomTailProb 3 2 0 2 = 10 / 64 ≤ (1 / 2) / (2 * 1) = 1 / 4`. -/
def singletonScope16384 : Fin 16384 → Finset (Fin 16384) :=
  fun f => {f}

theorem sum_card_singletonScope16384 :
    (∑ f : Fin 16384, #(singletonScope16384 f)) = 16384 := by
  simp [singletonScope16384]

theorem var_deg_singletonScope16384 (v : Fin 16384) :
    #{f : Fin 16384 | v ∈ singletonScope16384 f} ≤ 1 := by
  have hEq : univ.filter (fun f : Fin 16384 => v ∈ singletonScope16384 f) = {v} := by
    ext f
    simp [singletonScope16384, eq_comm]
  rw [hEq, card_singleton]

theorem nonempty_replacementDesign_singletonScope16384 :
    Nonempty (ReplacementDesign singletonScope16384 3 2 0 2 (1 / 2)) := by
  have hcard : #(measurementIndices 3 2 0 2) = 10 := by
    rw [card_measurementIndices_eq]
    decide
  refine exists_replacementDesign singletonScope16384
    (b := 1) (w := 1)
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by norm_num)
    (by omega)
    var_deg_singletonScope16384
    (fun f => by simp [singletonScope16384])
    (by rw [sum_card_singletonScope16384])
    (by rw [sum_card_singletonScope16384]; decide)
    (by decide)
    ?_
  rw [binomTailProb_eq_div 3 2 0 2 (by decide), hcard]
  norm_num

/-- Unpacking the Lemma 4.7 design verifies `T = 0` variable recovery, group size bounds,
total measurement row bounds, and cleared polynomial coefficient `ℓ₁`-norm bounds. -/
example (e : ScopeIncidence singletonScope16384) (x : Fin 16384 → ℚ) :
    ∃ D : ReplacementDesign singletonScope16384 3 2 0 2 (1 / 2),
      evalVarReplacementRow 3 2 0 2 D.place (scopeVarOf singletonScope16384) e 0 x =
        x (scopeVarOf singletonScope16384 e) ∧
      (∀ t g, #(varGroup D.varAssign t g) ≤ 16384) ∧
      ((2 * (D.h * #(measurementIndices 3 2 0 2)) : ℕ) : ℚ) ≤ 16384 := by
  obtain ⟨D⟩ := nonempty_replacementDesign_singletonScope16384
  refine ⟨D, D.evalReplacementRow_zero e x, fun t g => D.card_varGroup_le t g, ?_⟩
  simpa using D.total_measurement_rows_le

end Cslib.LinearAlgebra.ReplacementDesignTests
