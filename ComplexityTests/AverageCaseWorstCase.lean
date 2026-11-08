/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import Complexity.Computability.Complexity.Classes.AverageCase.WorstCase
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PolyTime

/-!
# Tests for the worst-case consequences of easy-on-average `NP`

Checked instances for `Complexity.Computability.Complexity.Classes.AverageCase.WorstCase`:

* the padded ensemble on concrete words: `frame [true] ++ 1^2` has probability `2^{-3}`, and which
  words begin with a framed word;
* the padded ensemble paired with a problem in `NP` is in `DistNP`;
* heavy instances: the threshold `1/(k+1)` of
  `Cslib.Complexity.DistProblem.IsHeuristicScheme.correct_of_lt` is sharp. A heuristic scheme
  under the uniform ensemble errs on `[true]`, which has probability exactly `1/(1+1)`;
* a point-mass ensemble, on whose support a heuristic scheme gives an exact polynomial-time
  decider;
* `(L, U) ∈ AvgP` for `L ∈ P` gives `L ∈ E`; the hypothesis `ExpPaddedNPEasy` follows from
  `NP ⊆ P`; and the `NE = E` conclusions.
-/

@[expose] public section

namespace Cslib.Complexity.AverageCaseWorstCaseTests

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped ENNReal

/-! ### The padded ensemble -/

/-- The padded word `frame [true] ++ 1^2 = 11011` has probability `2^{-3}`. -/
example : PaddedFrame.ensemble.dist 5 [true, true, false, true, true] = (2 ^ 3 : ℝ≥0∞)⁻¹ := by
  simpa using PaddedFrame.ensemble_dist_frame_append [true] 2

/-- `011` begins with the framed empty word `0`. -/
example : PaddedFrame.valid [false, true, true] = true :=
  PaddedFrame.valid_frame_append [] [true, true]

/-- `1` does not begin with a framed word. -/
example : PaddedFrame.valid [true] = false := by
  rw [← Bool.not_eq_true, PaddedFrame.valid_iff_exists]
  rintro ⟨u, s, h⟩
  cases u <;> simp at h

/-- `110` begins with the framed word `frame [true] = 110`. -/
example : PaddedFrame.valid [true, true, false] = true :=
  PaddedFrame.valid_frame_append [true] []

/-- A problem in `NP` paired with the padded ensemble is in `DistNP`. -/
example {B : Set (List Bool)} (hB : B ∈ NP encBits) :
    (⟨B, PaddedFrame.ensemble⟩ : DistProblem) ∈ DistNP :=
  mem_DistNP.mpr ⟨hB, PaddedFrame.ensemble_pComp⟩

/-! ### The threshold is sharp -/

/-- A scheme that answers `true` exactly on `[true]` with confidence parameter `1`. -/
def errOnce (p : List Bool × ℕ) : Bool := decide (p.1 = [true]) && decide (p.2 = 1)

/-- `errOnce` is a heuristic scheme for the empty problem under the uniform ensemble. Its only
error is `[true]` at confidence `1`, of probability `1/2 = 1/(1+1)`. -/
theorem errOnce_isHeuristicScheme :
    (⟨∅, Ensemble.uniform⟩ : DistProblem).IsHeuristicScheme errOnce where
  polyTime := by
    unfold errOnce
    polytime
  error_le n k := by
    by_cases hk : k = 1
    · subst hk
      have hset : {x : List Bool | ¬(errOnce (x, 1) = true ↔ x ∈ (∅ : Set (List Bool)))} =
          {[true]} := by
        ext x
        simp [errOnce]
      change (Ensemble.uniform.dist n).toOuterMeasure _ ≤ _
      rw [hset, PMF.toOuterMeasure_apply_singleton]
      by_cases hn : n = 1
      · subst hn
        have h := Ensemble.uniform_apply [true]
        simp only [List.length_cons, List.length_nil, zero_add, pow_one] at h
        rw [h]
        norm_num
      · have hns : [true] ∉ (Ensemble.uniform.dist n).support := fun h =>
          hn (by simpa using (Ensemble.uniform.length_eq n _ h).symm)
        rw [PMF.apply_eq_zero_iff _ _ |>.mpr hns]
        exact zero_le
    · have hset : {x : List Bool | ¬(errOnce (x, k) = true ↔ x ∈ (∅ : Set (List Bool)))} = ∅ := by
        ext x
        simp [errOnce, hk]
      change (Ensemble.uniform.dist n).toOuterMeasure _ ≤ _
      rw [hset]
      simp

/-- At probability exactly `1/(k+1)` a heuristic scheme may err: `correct_of_lt` needs the strict
inequality. -/
example : Ensemble.uniform.dist [true].length [true] = ((1 + 1 : ℕ) : ℝ≥0∞)⁻¹ ∧
    ¬(errOnce ([true], 1) = true ↔ [true] ∈ (∅ : Set (List Bool))) := by
  refine ⟨?_, by simp [errOnce]⟩
  rw [Ensemble.uniform_apply]
  norm_num

/-! ### Exact decision on the support -/

/-- The ensemble concentrated on the all-ones word of each length. -/
noncomputable def ones : Ensemble where
  dist n := PMF.pure (List.replicate n true)
  length_eq n x hx := by
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx, List.length_replicate]

/-- Under the all-ones ensemble every instance in the support has probability `1`, so a heuristic
scheme yields a polynomial-time decider of the all-ones words of `L`. -/
example {L : Set (List Bool)} (hL : (⟨L, ones⟩ : DistProblem) ∈ HeurP) :
    ∃ f : List Bool → Bool, ComputableInPolyTime f encBits encBool ∧
      ∀ n, (f (List.replicate n true) = true ↔ List.replicate n true ∈ L) := by
  obtain ⟨f, hf, hagree⟩ := exists_agree_on_support_of_mem_HeurP (q := 1) hL fun n x hx => by
    change x ∈ (PMF.pure _).support at hx
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    change _ ≤ (PMF.pure (List.replicate n true)) (List.replicate n true)
    simp
  exact ⟨f, hf, fun n => hagree n _ (by simp [ones])⟩

/-! ### Worst-case consequences -/

/-- A problem in `P` is in `AvgP` under the uniform ensemble, hence in `E`. -/
example {L : Set (List Bool)} (hL : L ∈ P encBits) : L ∈ E encBits :=
  mem_E_of_mem_AvgP_uniform (mem_AvgP_of_mem_P (L := ⟨L, Ensemble.uniform⟩) hL)

/-- `NP ⊆ P` implies the padding hypothesis. -/
example (h : NP encBits ⊆ P encBits) : ExpPaddedNPEasy := expPaddedNPEasy_of_NP_subset_P h

/-- The hypothesis `DistNP ⊆ AvgP` is not vacuous: it follows from `NP ⊆ P`. -/
example (h : NP encBits ⊆ P encBits) : DistNP ⊆ AvgP :=
  fun _ hL => mem_AvgP_of_mem_P (h (mem_DistNP.mp hL).1)

/-- Hence `NP ⊆ P` also gives `DistNP ⊆ HeurP`. -/
example (h : NP encBits ⊆ P encBits) : DistNP ⊆ HeurP :=
  fun _ hL => AvgP_subset_HeurP (mem_AvgP_of_mem_P (h (mem_DistNP.mp hL).1))

/-- If `DistNP ⊆ HeurP`, then `E = NE` and `EXP = NEXP` for problems on bit words. -/
example (h : DistNP ⊆ HeurP) : E encBits = NE encBits ∧ EXP encBits = NEXP encBits :=
  ⟨E_eq_NE_of_DistNP_subset_HeurP h, EXP_eq_NEXP_of_DistNP_subset_HeurP h⟩

/-- If `DistNP ⊆ AvgP`, then `E = NE`. -/
example (h : DistNP ⊆ AvgP) : E encBits = NE encBits := E_eq_NE_of_DistNP_subset_AvgP h

end Cslib.Complexity.AverageCaseWorstCaseTests
