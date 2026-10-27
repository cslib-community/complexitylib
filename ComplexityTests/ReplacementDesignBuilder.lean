/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.PolyTime.LinearAlgebra.ReplacementDesignBuilder
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Concrete tests for polynomial-time replacement design builder (Lemma 4.7)

Computational (`rfl` / `decide`), specification-bridge, and `fun_prop` synthesis tests for
`withNeutralScopesList` and `buildReplacementDesignData` ([OpenAI2026ETH], §4.6, Lemma 4.7).
-/

@[expose] public section

namespace ComplexityTests.ReplacementDesignBuilder

open Finset Polynomial Cslib.BitString Cslib.LinearAlgebra Turing.MultiTapeTM

/-- Sample raw 2-scope family on 4 variables (`b₀ = 1`). -/
abbrev rawScopes : List (List ℕ) := [[0, 2], [1, 3]]
/-- Neutral-augmented 6-scope family (`b = 2`, `M = 8`). -/
abbrev augScopes : List (List ℕ) := withNeutralScopesList rawScopes 4
/-- Balanced variable schedule on `n_free = 4, Q = 2, r = 2`. -/
abbrev sampleVarSched : List (List ℕ) := [[0, 0], [0, 1], [1, 0], [1, 1]]
/-- Balanced factor schedule on `augScopes` mapping the 8 incidences to distinct labels. -/
abbrev sampleScopeSched : List (List ℕ) := [[0, 1], [0, 0], [1, 1], [1, 0], [1, 1], [1, 0]]
/-- Design output with relaxed parameters `(n_free = 4, D = 16, Q = 2, r = 2, A₀ = 1, R = 2)`. -/
abbrev sampleData : ReplacementDesignData :=
  buildReplacementDesignData 4 16 2 2 1 2 augScopes sampleVarSched sampleScopeSched

private def dotRow (row vals : List ℤ) : ℤ :=
  ((List.range row.length).map fun j => row.getD j 0 * vals.getD j 0).sum
private def evalReplRow (table : List (List ℤ)) (t : ℤ) (ξ : List ℤ) : ℤ :=
  ((List.range ξ.length).map fun i => evalCoeffList t (table.getD i []) * ξ.getD i 0).sum

/-! ### 1. Neutral-singleton scope augmentation and `withNeutralScope` agreement -/
example : augScopes = [[0, 2], [1, 3], [0], [1], [2], [3]] ∧
    scopeIncidencesList 4 augScopes =
      [(0, 0), (0, 2), (1, 1), (1, 3), (2, 0), (3, 1), (4, 2), (5, 3)] ∧
    normalizeScopeSchedules 4 2 2 [[0, 2], [9]] [[1, 1], [1, 1]] = [[1, 1], [0, 0]] :=
  ⟨rfl, rfl, rfl⟩

example : (∀ v : Fin 4, varIncidence univ (listScopeFamily 4 augScopes) v = 2) ∧
    totalIncidence univ (listScopeFamily 4 augScopes) = 8 :=
  ⟨fun v => by rw [varIncidence_listScopeFamily_withNeutralScopesList]; revert v; decide,
   by rw [totalIncidence_listScopeFamily_withNeutralScopesList]; decide⟩

/-! ### 2. Concrete construction: groups, truncation, `T = 0` identity, restricted kernel -/
example : incidenceLabelsList 4 2 2 augScopes sampleVarSched sampleScopeSched =
      [8, 9, 2, 3, 12, 6, 13, 7] ∧
    sampleData.varGroups = [[[0, 1], [2, 3]], [[0, 2], [1, 3]]] ∧
    sampleData.factorGroups = sampleScopeSched ∧ sampleData.copyCount = 1 ∧
    sampleData.denom = 2 ∧ sampleData.placements.Nodup ∧
    sampleData.measurementMatrix.length = 9 ∧
    decide ((buildReplacementDesignData 4 5 2 2 1 2 augScopes sampleVarSched sampleScopeSched) ≠
      sampleData) = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl⟩

example :
    (sampleData.incidences.all fun (f, v) =>
      let tbl := sampleData.lookupReplacementRow f v
      decide (tbl.length = 4) && tbl.all (fun row => decide (row.length = 2)) &&
        (List.range 4).all fun i =>
          decide (evalCoeffList 0 (tbl.getD i []) = if i = v then sampleData.denom else 0)) = true ∧
    (((sampleData.groupMeasurementMatrices.getD 0 []).getD 0 []).all fun r_row =>
      decide (dotRow r_row [1, -1] = 0)) = true ∧
    evalReplRow (sampleData.lookupReplacementRow 2 0) 0 [1, -1, 0, 0] = 2 ∧
    evalReplRow (sampleData.lookupReplacementRow 2 0) 1 [1, -1, 0, 0] = 0 ∧
    (buildReplacementDesignData 4 1 0 2 0 1 [[0]] [[]] [[]]).measurementMatrix = [] ∧
    (buildReplacementDesignData 4 4 2 0 1 2 [[0]] [[]] [[]]).copyCount = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 3. Nonvacuous semantic bridge with relaxed parameters (`b₀ = 1`, `τ = 9 / 4`)

This exercises the constructor's relaxed hypotheses, not the full numerical regime of Lemma 4.7:
here `R = Q`, `τ > 1 / 2`, and the lemma's size hypotheses do not hold. -/
example : ∃ D : ReplacementDesign (listScopeFamily 4 augScopes) 2 2 1 2 (9 / 4),
    sampleData.Refines augScopes D := by
  have hbal : BalancedSchedule (by decide : 1 ≤ 2) 4 2 augScopes sampleVarSched sampleScopeSched :=
    (balancedSchedule_iff_exec (by decide) 4 2 augScopes sampleVarSched sampleScopeSched).mpr
      (by decide)
  have hb₀ : ∀ v : Fin 4, varIncidence univ (listScopeFamily 4 rawScopes) v ≤ 1 := by decide
  have htail : binomTailProb 2 2 1 2 ≤ (9 / 4 : ℚ) / ((2 : ℚ) * ((1 + 1 : ℕ) : ℚ)) := by
    have hcard : (#(measurementIndices 2 2 1 2) : ℚ) =
        ((2 ^ (2 * 2) : ℕ) : ℚ) * binomTailProb 2 2 1 2 := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        card_measurementIndices_cast_eq 2 2 1 2 (by decide)
    have h9 : #(measurementIndices 2 2 1 2) = 9 := by rw [card_measurementIndices_eq]; rfl
    rw [h9] at hcard; push_cast at hcard ⊢; linarith
  exact exists_replacementDesign_withNeutralScopesList (D_cap := 16) rawScopes sampleVarSched
    sampleScopeSched (by decide) (by decide) (by decide) (by decide) (by norm_num) (by omega)
    hb₀ htail hbal

/-! ### 4. Compositional `fun_prop` synthesis and unary-encoding guards -/
example : ComputableInPolyTime
    (fun p : (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ) × (List (List ℕ) × List (List ℕ) × List (List ℕ)) =>
      let d := buildReplacementDesignData p.1.1 p.1.2.1 p.1.2.2 p.2.1.1 p.2.1.2.1 p.2.1.2.2
        (withNeutralScopesList p.2.2.1 p.1.1) p.2.2.2.1 p.2.2.2.2
      (d.varGroups, d.groupMeasurementMatrices, d.denom, d.lookupReplacementRow 0 0))
    (encPair (encPair encUnary (encPair encUnary encUnary))
      (encPair (encPair encUnary (encPair encUnary encUnary))
        (encPair (encList (encList encNat))
          (encPair (encList (encList encNat)) (encList (encList encNat))))))
    (encPair (encList (encList (encList encNat)))
      (encPair (encList (encList (encList (encList encIntBin))))
        (encPair encIntBin (encList (encList encIntBin))))) := by fun_prop

example : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n : ℕ => withNeutralScopesList [] n)
      encNat (encList (encList encNat)) := by fun_prop (config := { maxSteps := 32 })
  fail_if_success
    have : ComputableInPolyTime (fun D : ℕ => buildReplacementDesignData 1 D 1 2 0 1 [] [] [])
      encNat encReplacementDesignData := by fun_prop (config := { maxSteps := 32 })
  trivial

end ComplexityTests.ReplacementDesignBuilder
