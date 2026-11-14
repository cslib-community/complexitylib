/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BallsToSlots.KickTree
public import CslibFrontier.Foundations.Data.Finset.Density
public import CslibFrontier.Probability.KWiseIndependent.Trinomial

/-!
# Execution and API-Applicability Tests for `BallsToSlots` and the STOC 2022 `k`-Kick Tree

Exercises concrete execution and hypothesis satisfiability of `Cslib.DataStructure.BallsToSlots`:
1. Multi-step `insert → query → delete → insert` execution on a `2`-kick tree over `8` slots that
   deterministically triggers a priority kick (`1 < switchingCost`), checking `switchingCost ≤
   depth + 1`, kick-depth invariance (`assignedDepth_insert_of_mem`), removal-only deletion
   (`ValidState.delete`, `assignedDepth_delete_of_ne`), and `step_schemeSpec` refinement;
2. Tight comparison between `max (Nat.iterLog 2 n) 1` and `Dictionary.Dynamic.logLogFactor n`;
3. Hypothesis-satisfiability and API-applicability checks instantiating
   `expect_ballProbeComplexity_standardInsert_le`, `expect_totalProbeComplexity_standardRun_le`
   (at `m₀ = 32, k = 2`, where `effectiveDepth 32 2 = 2`), and
   `dens_sum_totalProbeComplexity_standardRun_gt_le` (at `m = 1, m₀ = 2, k = 1`) with unconditional
   `trinomialPolyHash` families.

**Quantitative regime note:** Every present ball deterministically satisfies
`ballProbeComplexity ≤ 1 + m₀`. Consequently, the proved per-ball expectation bound
`96 * max (Nat.iterLog (k + 1) (2 ^ m₀)) 1` improves on the deterministic ceiling `1 + m₀` once
`96 * max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 < 1 + m₀` — starting at `m₀ ≥ 96` for `k ≥ 3` (where
`effectiveDepth 96 3 = 3` and `Nat.iterLog 4 (2 ^ 96) = 1`, giving `96 < 97`), and for all
`m₀ ≥ 288` for `k = 2` (`96 * 3 = 288 < 289`; holding also on `192 ≤ m₀ ≤ 255` where
`iterLog 3 = 2`, failing on `256 ≤ m₀ ≤ 287`, and holding for all `m₀ ≥ 288`). Likewise, the tail
event `{μ + Δ ≤ ∑ b ∈ R, ...}` in `dens_sum_totalProbeComplexity_standardRun_gt_le` is empty
whenever `m₀ < 96`, and its Markov bound is `< 1` when `#R` is large relative to
`2 ^ m₀ * (1 + m₀)`. At `m₀ = 32, k = 2` the expectation bound `192` exceeds `33`, and at
`m₀ = 2, k = 1` (`effectiveDepth 2 1 = 0`) the tail event is empty; Section 3 below therefore
checks hypothesis satisfiability and API applicability rather than numerical tightness at those
small sizes.
-/

public section

namespace CslibFrontierTests.DataStructure.KickTree

open Cslib Cslib.Probability Finset
open Cslib.DataStructure.BallsToSlots
open Cslib.DataStructure.BallsToSlots.KickTree
open scoped BigOperators

/-! ## 1. Concrete `2`-kick tree execution with priority kicks and deletion -/

/-- Concrete `2`-kick tree over `8` slots with bin sizes `8, 4, 2` and cap exponents `2, 1`. -/
@[expose] def testParams : Params where
  slotBits := 3
  depth := 2
  capBits := 2
  binExp
    | ⟨0, _⟩ => 3
    | ⟨1, _⟩ => 2
    | ⟨_, _⟩ => 1
  capExp
    | ⟨0, _⟩ => 2
    | ⟨_, _⟩ => 1
  binExp_zero := rfl
  binExp_antitone i j hij := by revert hij; fin_cases i <;> fin_cases j <;> decide
  capExp_antitone i j hij := by revert hij; fin_cases i <;> fin_cases j <;> decide
  capExp_le_capBits i := by fin_cases i <;> decide

/-- Deterministic test hash `Fin 4 → Fin 32`:
* ball `0`: `preferredSlot = 0`, `capHash = 0` (`depthCap = 0`);
* ball `1`: `preferredSlot = 1`, `capHash = 2` (`depthCap = 1`);
* balls `2, 3`: `preferredSlot = 0`, `capHash = 3` (`depthCap = 2`). -/
@[expose] def testHash : Fin 4 → Fin (2 ^ testParams.hashBits)
  | 0 => 0
  | 1 => 17
  | _ => 24

/-- Kernel-checked multi-step trace witnessing an actual priority kick (`switchingCost = 2`),
kick-depth invariance for kicked ball `0`, removal-only deletion of ball `1`, and reuse of the
vacated slot by ball `3`. -/
theorem concrete_kick_and_delete_trace :
    let st₀ := State.empty testParams (Fin 4)
    let st₁ := testParams.insert testHash st₀ 0
    let st₂ := testParams.insert testHash st₁ 1
    let st₃ := testParams.insert testHash st₂ 2
    let st₄ := st₃.delete 1
    let st₅ := testParams.insert testHash st₄ 3
    st₂.query 0 = some 0 ∧ st₂.assignedDepth 0 = some 0 ∧
    st₂.query 1 = some 1 ∧ st₂.assignedDepth 1 = some 1 ∧
    -- Inserting ball `2` kicks ball `0` from slot `0` to slot `2` while keeping `0` at depth `0`:
    st₃.query 2 = some 0 ∧ st₃.assignedDepth 2 = some 2 ∧
    st₃.query 0 = some 2 ∧ st₃.assignedDepth 0 = some 0 ∧
    switchingCost st₂.assignment st₃.assignment = 2 ∧
    displacedBalls st₂.assignment st₃.assignment = 1 ∧
    -- Deleting ball `1` vacates slot `1` without moving or re-depthing balls `0` or `2`:
    st₄.query 1 = none ∧ st₄.query 0 = some 2 ∧ st₄.assignedDepth 0 = some 0 ∧
    st₄.query 2 = some 0 ∧ st₄.assignedDepth 2 = some 2 ∧
    -- Inserting ball `3` places it into the vacated slot `1` at depth `2`:
    st₅.query 3 = some 1 ∧ st₅.assignedDepth 3 = some 2 ∧
    testParams.ValidState testHash st₅ := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, ?_⟩
  exact (((((Params.ValidState.empty testParams testHash).insert 0).insert 1).insert 2).delete
    1).insert 3

/-- Concrete `step_schemeSpec` refinement check across an insertion step. -/
theorem concrete_step_schemeSpec :
    let st₀ := State.empty testParams (Fin 4)
    (schemeSpec (Fin 4) 8 8 3 (testParams.probeSeq testHash)).step
      st₀.assignment (.insert 0) (testParams.step testHash st₀ (.insert 0)).1.assignment () ∧
    switchingCost st₀.assignment (testParams.insert testHash st₀ 0).assignment ≤ 3 :=
  ⟨testParams.step_schemeSpec testHash (Params.ValidState.empty testParams testHash)
    (Or.inl (by rw [State.empty, SlotAssignment.present_empty]; decide)),
   testParams.switchingCost_insert_le testHash (Params.ValidState.empty testParams testHash) 0⟩

/-! ## 2. Iterated-logarithm bridge tightness (`n = 5`) -/

/-- At `n = 5`, `max (Nat.iterLog 2 5) 1 = 1` whereas `Dictionary.Dynamic.logLogFactor 5 = 2`,
witnessing both `max_iterLog_two_le_logLogFactor` and `logLogFactor_le_two_mul_max_iterLog_two`. -/
theorem iterLog_bridge_at_five :
    max (Nat.iterLog 2 5) 1 = 1 ∧
    max (Nat.iterLog 2 5) 1 ≤ Cslib.DataStructure.Dictionary.Dynamic.logLogFactor 5 ∧
    Cslib.DataStructure.Dictionary.Dynamic.logLogFactor 5 ≤ 2 * max (Nat.iterLog 2 5) 1 :=
  ⟨by decide, max_iterLog_two_le_logLogFactor 5, logLogFactor_le_two_mul_max_iterLog_two 5⟩

/-! ## 3. Hypothesis-satisfiability and API-applicability checks via `trinomialPolyHash` -/

/-- Admissible `insert → insert → delete → insert → query` operation history on `Fin 16`. -/
@[expose] def sampleOps : List (Op (Fin 16)) :=
  [.insert 1, .insert 2, .delete 1, .insert 3, .query 2]

theorem validOpSeq_sampleOps_32 : ValidOpSeq (2 ^ 32) sampleOps ∧ #(activeSet sampleOps) = 2 := by
  refine ⟨?_, by decide⟩
  simp [sampleOps, ValidOpSeq, ValidOpSeqFrom, ValidOp, stepSet]

/-- Hypothesis-satisfiability and API-applicability check instantiating
`expect_ballProbeComplexity_standardInsert_le` and `expect_totalProbeComplexity_standardRun_le` at
`m₀ = 32, k = 2` (`effectiveDepth 32 2 = 2`) with unconditional 3-wise independent
`trinomialPolyHash` (at `m₀ = 32` the per-ball bound `192` exceeds deterministic `33`; see the
module docstring for the `m₀ ≥ 96` / `m₀ ≥ 288` regimes where it improves on `1 + m₀`). -/
theorem expect_probeComplexity_trinomialPolyHash :
    let H := (standardParams 32 2).hashBits
    let t := trinomialStep 16 H
    let h := trinomialPolyHash t 3 16 H
    effectiveDepth 32 2 = 2 ∧
    IsKWiseIndependentHash 3 h ∧
    𝔼 θ, (ballProbeComplexity ((standardParams 32 2).probeSeq (h θ))
      (standardInsert 32 2 (h θ) (State.empty (standardParams 32 2) (Fin 16)) 0).assignment 0 :
        ℝ) ≤ 96 * (max (Nat.iterLog 3 (2 ^ 32)) 1 : ℝ) ∧
    𝔼 θ, (totalProbeComplexity ((standardParams 32 2).probeSeq (h θ))
      (standardRun 32 2 (h θ) sampleOps).assignment : ℝ) ≤
      96 * 2 * (max (Nat.iterLog 3 (2 ^ 32)) 1 : ℝ) := by
  intro H t h
  have hh : IsKWiseIndependentHash 3 h :=
    isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg 16 H) (le_trinomialDeg 16 H)
  have hD : effectiveDepth 32 2 = 2 := by decide
  have hL1 := expect_ballProbeComplexity_standardInsert_le 32 2 hh le_rfl
    (st := fun _ => State.empty (standardParams 32 2) (Fin 16))
    (fun θ => Params.ValidState.empty (standardParams 32 2) (h θ))
    (S := ∅) (fun _ => SlotAssignment.present_empty (Fin 16) _) (x := (0 : Fin 16))
    (Finset.notMem_empty 0) (by simp)
  have hT2 := expect_totalProbeComplexity_standardRun_le 32 2 hh le_rfl validOpSeq_sampleOps_32.1
  rw [validOpSeq_sampleOps_32.2] at hT2
  exact ⟨hD, hh, hL1, by simpa using hT2⟩

/-- Two disjoint-footprint operation sequences over `Fin 8` (one with deletion) for checking
multi-tree `2m`-th moment concentration premises at `m = 1, m₀ = 2, k = 1`. -/
@[expose] def twoTreeOps : Bool → List (Op (Fin 8))
  | false => [.insert 0, .insert 1, .delete 0, .insert 2]
  | true => [.insert 4, .insert 5]

/-- Hypothesis-satisfiability and API-applicability check instantiating
`dens_sum_totalProbeComplexity_standardRun_gt_le` across two disjoint-footprint histories using
unconditional `32`-wise independent `trinomialPolyHash` (at `m₀ = 2`, `effectiveDepth 2 1 = 0` and
the tail event is empty; nonempty tail events require `m₀ ≥ 96`). -/
theorem dens_sum_totalProbeComplexity_trinomialPolyHash :
    let H := (standardParams 2 1).hashBits
    let t := trinomialStep 8 H
    let h := trinomialPolyHash t 32 8 H
    let R : Finset Bool := {false, true}
    (dens {θ | (400 : ℝ) + 100 ≤ ∑ b ∈ R,
      (totalProbeComplexity ((standardParams 2 1).probeSeq (h θ))
        (standardRun 2 1 (h θ) (twoTreeOps b)).assignment : ℝ)} : ℝ) ≤
      2 * (3 * (1 : ℝ) * (2 ^ 2 : ℝ) * (1 + 2) * 400 / 100 ^ 2) ^ 1 := by
  intro H t h R
  have hh : IsKWiseIndependentHash 32 h :=
    isKWiseIndependentHash_trinomialPolyHash (le_two_pow_trinomialDeg 8 H) (le_trinomialDeg 8 H)
  have hval : ∀ b ∈ R, ValidOpSeq (2 ^ 2) (twoTreeOps b) := by
    intro b _; cases b <;> simp [twoTreeOps, ValidOpSeq, ValidOpSeqFrom, ValidOp, stepSet]
  have hdisj : (R : Set Bool).Pairwise fun b₁ b₂ =>
      Disjoint (opsBalls (twoTreeOps b₁)) (opsBalls (twoTreeOps b₂)) := by
    intro b₁ _ b₂ _ hne; cases b₁ <;> cases b₂ <;> first | contradiction | decide
  have hcard : (∑ b ∈ R, (#(activeSet (twoTreeOps b)) : ℝ)) = 4 := by
    have : ∑ b ∈ R, #(activeSet (twoTreeOps b)) = 4 := by decide
    exact_mod_cast this
  have hiter : Nat.iterLog 2 (2 ^ 2) = 1 := by decide
  exact (dens_sum_totalProbeComplexity_standardRun_gt_le (m := 1) le_rfl 2 1 hh (by decide)
    R twoTreeOps hval hdisj (μ := 400) (Δ := 100)
    (by rw [hcard, hiter]; norm_num) (by norm_num) (by norm_num)).trans_eq (by norm_num)

end CslibFrontierTests.DataStructure.KickTree
