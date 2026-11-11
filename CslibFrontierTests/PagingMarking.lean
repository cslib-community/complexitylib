/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Paging.LRU
public import CslibFrontier.DataStructure.Paging.Marking
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.NormNum

/-!
# Tests for Behavioural Online Strategies and Randomized Marking

Kernel-checked rational expected costs (`decide` + `norm_num`, zero `native_decide`), warmup and
phase-reset boundary checks, comparison against deterministic LRU on the cyclic nemesis sequence,
non-lazy offline schedule admissibility, deterministic strategy embedding (`ofDetStrategy`), and
concrete `BehavioralStrategy.IsCompetitive` instantiations for
`CslibFrontier.DataStructure.Online.Behavioral` and `CslibFrontier.DataStructure.Paging.Marking`.
-/

public section

namespace CslibFrontierTests.PagingMarking

open Cslib.DataStructure.Online Cslib.DataStructure.Paging
open scoped ENNReal

private theorem ofReal_div_nat (a b : ℕ) (hb : 0 < b) :
    ENNReal.ofReal ((a : ℝ) / (b : ℝ)) = (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr hb
  rw [ENNReal.ofReal_div_of_pos hb', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-! ### Exact rational expected costs on small instances -/

/-- Capacity `2`, full initial cache `{0, 1}`, requests `[2, 0]`:
`2` triggers a phase reset (cost `1`, evicting `0` or `1` each w.p. `1/2`), and stale request `0`
faults w.p. `1/2`, for total expected cost `3 / 2`. -/
example : trackerExpectedCost 2 (initTracker [0, 1].toFinset) [2, 0] = 3 / 2 := by
  simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
  norm_num

example :
    (markingStrategy 2 (by omega)).expectedCost ({0, 1} : Finset ℕ) [2, 0] = 3 / 2 := by
  have hvalid : ValidCache 2 ({0, 1} : Finset ℕ) := by simp [ValidCache]
  have htr : trackerExpectedCost 2 (initTracker ({0, 1} : Finset ℕ)) [2, 0] = 3 / 2 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
  simpa using ofReal_div_nat 3 2 (by omega)

/-- Capacity `3`, full initial cache `{0, 1, 2}`, requests `[3, 0, 1]`:
one clean miss (`3`, cost `1`) followed by two stale requests (`0` w.p. `1/3`, `1` w.p. `1/2`)
attains `1 + 1/3 + 1/2 = 11 / 6 = harmonic 3` (`H_3 · #clean` with equality). -/
example :
    trackerExpectedCost 3 (initTracker ({0, 1, 2} : Finset ℕ)) [3, 0, 1] = 11 / 6 ∧
      harmonic 3 = 11 / 6 ∧
      cleanCount 3 (initTracker ({0, 1, 2} : Finset ℕ)) [3, 0, 1] = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  · simp only [harmonic_succ, harmonic_zero]
    norm_num
  · simp only [cleanCount, isCleanReq, stepTracker, initTracker]
    decide

example :
    (markingStrategy 3 (by omega)).expectedCost ({0, 1, 2} : Finset ℕ) [3, 0, 1] = 11 / 6 := by
  have hvalid : ValidCache 3 ({0, 1, 2} : Finset ℕ) := by simp [ValidCache]
  have htr : trackerExpectedCost 3 (initTracker ({0, 1, 2} : Finset ℕ)) [3, 0, 1] = 11 / 6 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
  simpa using ofReal_div_nat 11 6 (by omega)

/-- Two clean misses before a stale request (`k = 3`, `{0, 1, 2}`, `[3, 4, 0]`):
`3` (cost `1`), `4` (cost `1`), and stale `0` (faults w.p. `2/3`), giving `8 / 3`. -/
example :
    (markingStrategy 3 (by omega)).expectedCost ({0, 1, 2} : Finset ℕ) [3, 4, 0] = 8 / 3 := by
  have hvalid : ValidCache 3 ({0, 1, 2} : Finset ℕ) := by simp [ValidCache]
  have htr : trackerExpectedCost 3 (initTracker ({0, 1, 2} : Finset ℕ)) [3, 4, 0] = 8 / 3 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
  simpa using ofReal_div_nat 8 3 (by omega)

/-! ### Non-full initial caches and multi-phase reset boundaries -/

/-- Empty initial cache (`|s₀| = 0 < 2`): `[0, 1]` insert without eviction (cost `2`), `0` hits
(cost `0`), `2` resets the phase (cost `1`), and stale `1` faults w.p. `1/2`, totaling `7 / 2`. -/
example :
    (markingStrategy 2 (by omega)).expectedCost (∅ : Finset ℕ) [0, 1, 0, 2, 1] = 7 / 2 := by
  have htr : trackerExpectedCost 2 (initTracker (∅ : Finset ℕ)) [0, 1, 0, 2, 1] = 7 / 2 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) (validCache_empty 2), htr]
  simpa using ofReal_div_nat 7 2 (by omega)

/-- Partially filled initial cache (`s₀ = {0}`, `|s₀| = 1 < 2`): `0` hits, `1` inserts without
eviction (cost `1`), `2` triggers the first phase reset (cost `1`), and stale `0` faults w.p.
`1/2`, totaling `5 / 2`. -/
example :
    (markingStrategy 2 (by omega)).expectedCost ({0} : Finset ℕ) [0, 1, 2, 0] = 5 / 2 := by
  have hvalid : ValidCache 2 ({0} : Finset ℕ) := by simp [ValidCache]
  have htr : trackerExpectedCost 2 (initTracker ({0} : Finset ℕ)) [0, 1, 2, 0] = 5 / 2 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
  simpa using ofReal_div_nat 5 2 (by omega)

/-- On the cyclic nemesis sequence `[2, 0, 1, 2, 0, 1]` from `{0, 1}` (`k = 2`), randomized marking
incurs expected cost `9 / 2` across three phase resets, whereas computable `lruFaults` incurs `5`
faults from initial recency list `[0, 1]` and `6` faults from `[1, 0]` (`9 / 2 < 5 < 6`;
`lruStrategy.init` uses noncomputable `Finset.toList`). -/
example :
    (markingStrategy 2 (by omega)).expectedCost ({0, 1} : Finset ℕ) [2, 0, 1, 2, 0, 1] =
      9 / 2 := by
  have hvalid : ValidCache 2 ({0, 1} : Finset ℕ) := by simp [ValidCache]
  have htr :
      trackerExpectedCost 2 (initTracker ({0, 1} : Finset ℕ)) [2, 0, 1, 2, 0, 1] = 9 / 2 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
  simpa using ofReal_div_nat 9 2 (by omega)

example :
    lruFaults 2 [0, 1] [2, 0, 1, 2, 0, 1] = 5 ∧
      lruFaults 2 [1, 0] [2, 0, 1, 2, 0, 1] = 6 ∧
      (markingStrategy 2 (by omega)).expectedCost ({0, 1} : Finset ℕ) [2, 0, 1, 2, 0, 1] <
        (lruFaults 2 [0, 1] [2, 0, 1, 2, 0, 1] : ℝ≥0∞) ∧
      (markingStrategy 2 (by omega)).expectedCost ({0, 1} : Finset ℕ) [2, 0, 1, 2, 0, 1] <
        (lruFaults 2 [1, 0] [2, 0, 1, 2, 0, 1] : ℝ≥0∞) := by
  have hlru01 : lruFaults 2 [0, 1] [2, 0, 1, 2, 0, 1] = 5 := by decide
  have hlru10 : lruFaults 2 [1, 0] [2, 0, 1, 2, 0, 1] = 6 := by decide
  have hvalid : ValidCache 2 ({0, 1} : Finset ℕ) := by simp [ValidCache]
  have htr :
      trackerExpectedCost 2 (initTracker ({0, 1} : Finset ℕ)) [2, 0, 1, 2, 0, 1] = 9 / 2 := by
    simp only [trackerExpectedCost, stepTrackerCost, stepTracker, initTracker]
    norm_num
  have hmark :
      (markingStrategy 2 (by omega)).expectedCost ({0, 1} : Finset ℕ) [2, 0, 1, 2, 0, 1] =
        ENNReal.ofReal ((9 : ℝ) / 2) := by
    rw [expectedCost_markingStrategy_eq (by omega) hvalid, htr]
    norm_num
  refine ⟨hlru01, hlru10, ?_, ?_⟩
  · rw [hlru01, hmark, ← ENNReal.ofReal_natCast 5]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  · rw [hlru10, hmark, ← ENNReal.ofReal_natCast 6]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)

/-! ### Non-lazy offline schedules -/

/-- A non-lazy valid offline schedule from `{0, 1}` (`k = 2`) on `[2, 0]` that drops *both* `{0, 1}`
on the first miss (`{0, 1} ↦ {2} ↦ {2, 0}`, incurring `2` faults): `markingStrategy_expectedCost_le`
applies directly without any lazy-schedule assumption. -/
example :
    let s₀ : Finset ℕ := {0, 1}
    let reqs : List ℕ := [2, 0]
    let offStates : List (Finset ℕ) := [{2}, {2, 0}]
    (problem ℕ 2).ValidSchedule s₀ reqs offStates ∧
      (markingStrategy 2 (by omega)).expectedCost s₀ reqs ≤
        2 * ENNReal.ofReal (harmonic 2) * (problem ℕ 2).scheduleCost s₀ reqs offStates := by
  dsimp only
  have hs₀ : ValidCache 2 ({0, 1} : Finset ℕ) := by simp [ValidCache]
  have hv : (problem ℕ 2).ValidSchedule ({0, 1} : Finset ℕ) [2, 0] [{2}, {2, 0}] := by
    refine ⟨?_, ?_, trivial⟩
    · simp [ValidStep]
    · refine ⟨by simp, by simp, by simp, ?_⟩
      intro x hx
      simp at hx ⊢
      tauto
  exact ⟨hv, markingStrategy_expectedCost_le (by omega) hs₀ hv⟩

/-! ### Deterministic strategy embedding (`BehavioralStrategy.ofDetStrategy`) -/

/-- Embedding `lruStrategy` into `BehavioralStrategy` preserves both exact cost on admissible
initial caches and `(k, 0)`-competitiveness. -/
example :
    (BehavioralStrategy.ofDetStrategy (lruStrategy (α := ℕ) 2 (by omega))).expectedCost
      ({0, 1} : Finset ℕ) [2, 0, 1] =
      (lruStrategy (α := ℕ) 2 (by omega)).cost ({0, 1} : Finset ℕ) [2, 0, 1] := by
  have hs₀ : (problem ℕ 2).ValidInit ({0, 1} : Finset ℕ) := by simp [ValidCache]
  exact BehavioralStrategy.expectedCost_ofDetStrategy (lruStrategy (α := ℕ) 2 (by omega)) hs₀
    [2, 0, 1]

example (k : ℕ) (hk : 0 < k) :
    (BehavioralStrategy.ofDetStrategy (lruStrategy (α := ℕ) k hk)).IsCompetitive k (0 : ℕ) :=
  (BehavioralStrategy.isCompetitive_ofDetStrategy_iff _ k 0).mpr (lruStrategy_isCompetitive k hk)

/-! ### Concrete `BehavioralStrategy.IsCompetitive` instances for `markingStrategy` -/

/-- For `k = 2`, `2 * H_2 = 2 * (3 / 2) = 3`, so `markingStrategy 2` is `(3, 0)`-competitive. -/
theorem markingStrategy_two_isCompetitive :
    (markingStrategy (α := ℕ) 2 (by omega)).IsCompetitive 3 0 := by
  have h := markingStrategy_isCompetitive (α := ℕ) (k := 2) (by omega)
  have hH2 : (2 : ℝ≥0∞) * ENNReal.ofReal (harmonic 2) = 3 := by
    have hq : (2 : ℝ) * (harmonic 2 : ℝ) = ((3 : ℕ) : ℝ) := by
      simp only [harmonic_succ, harmonic_zero]
      norm_num
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), hq, ENNReal.ofReal_natCast]
    norm_cast
  rwa [hH2] at h

/-- For `k = 3`, `2 * H_3 = 2 * (11 / 6) = 11 / 3`, so `markingStrategy 3` is
`(11 / 3, 0)`-competitive. -/
theorem markingStrategy_three_isCompetitive :
    (markingStrategy (α := ℕ) 3 (by omega)).IsCompetitive (11 / 3) 0 := by
  have h := markingStrategy_isCompetitive (α := ℕ) (k := 3) (by omega)
  have hH3 : (2 : ℝ≥0∞) * ENNReal.ofReal (harmonic 3) = 11 / 3 := by
    have hq : (2 : ℝ) * (harmonic 3 : ℝ) = ((11 : ℕ) : ℝ) / ((3 : ℕ) : ℝ) := by
      simp only [harmonic_succ, harmonic_zero]
      norm_num
    rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num), hq,
      ofReal_div_nat 11 3 (by omega)]
    norm_cast
  rwa [hH3] at h

end CslibFrontierTests.PagingMarking
