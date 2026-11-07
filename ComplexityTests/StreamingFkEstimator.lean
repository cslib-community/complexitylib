/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Streaming.FkEstimator

/-!
# Unit tests for the AMS `F_k` estimator

Verifies non-vacuity and concrete behavior of:
1. `Cslib.Streaming.suffixCount` and `Cslib.Streaming.fkBasicEstimate` on the stream `0, 1, 0`,
   where the basic estimator for `F₂ = 5` takes the values `9, 3, 3`, with mean `5`
   (`Cslib.Streaming.expect_fkBasicEstimate`);
2. the hypothesis `k ≠ 0`: for `k = 0` the basic estimator is identically zero while `F₀ ≠ 0`;
3. the sketch `Cslib.Streaming.fkSketch` on a concrete stream and concrete positions;
4. the hypotheses of `Cslib.Streaming.solves_fkEstimator` (`F₂` over a universe of size `4`, group
   size `12`, accuracy `η = 1`), of `Cslib.Streaming.solves_fkEstimator_of_rpow`, of
   `Cslib.Streaming.spaceLE_fkEstimator` (positions not charged) and of
   `Cslib.Streaming.exists_injOn_iUnion_reachable_fkSketch` (positions stored) hold with explicit
   parameters.
-/

public section

namespace ComplexityTests.StreamingFkEstimator

open Cslib Cslib.Probability Cslib.Streaming
open scoped BigOperators

/-! ## 1. The basic estimator on `0, 1, 0` -/

example : suffixCount [(0 : Fin 2), 1, 0] 0 = 2 := by decide
example : suffixCount [(0 : Fin 2), 1, 0] 1 = 1 := by decide
example : suffixCount [(0 : Fin 2), 1, 0] 2 = 1 := by decide
example : suffixCount [(0 : Fin 2), 1, 0] 3 = 0 := by decide
example : freqMoment 2 [(0 : Fin 2), 1, 0] = 5 := by decide

example : fkBasicEstimate 2 [(0 : Fin 2), 1, 0] 0 = 9 := by
  have h : suffixCount [(0 : Fin 2), 1, 0] 0 = 2 := by decide
  simp only [fkBasicEstimate, h]
  norm_num

example : fkBasicEstimate 2 [(0 : Fin 2), 1, 0] 1 = 3 := by
  have h : suffixCount [(0 : Fin 2), 1, 0] 1 = 1 := by decide
  simp only [fkBasicEstimate, h]
  norm_num

/-- The mean of the basic estimator `9, 3, 3` is `F₂ = 5`. -/
example : 𝔼 p : Fin 3, fkBasicEstimate 2 [(0 : Fin 2), 1, 0] p = 5 := by
  have h := expect_fkBasicEstimate (k := 2) two_ne_zero [(0 : Fin 2), 1, 0]
  have hF : freqMoment 2 [(0 : Fin 2), 1, 0] = 5 := by decide
  rw [hF] at h
  exact_mod_cast h

/-! ## 2. The hypothesis `k ≠ 0` is needed -/

/-- For `k = 0` the basic estimator `m (r ^ 0 - (r - 1) ^ 0)` vanishes, but `F₀` of a nonempty
stream does not. -/
example : 𝔼 p : Fin 1, fkBasicEstimate 0 [(0 : Fin 2)] p ≠ freqMoment 0 [(0 : Fin 2)] := by
  have hF : freqMoment 0 [(0 : Fin 2)] = 1 := by decide
  simp [fkBasicEstimate, hF]

/-! ## 3. The sketch on a concrete stream -/

/-- With every copy at position `0`, the sketch reports `3 (2 ^ 2 - 1 ^ 2) = 9` on `0, 1, 0`. -/
example : (fkSketch (α := Fin 2) 2 3 1 1 fun _ _ => 0).run [0, 1, 0] = 9 := by
  have h : suffixCount [(0 : Fin 2), 1, 0] 0 = 2 := by decide
  rw [run_fkSketch]
  simp only [Fin.val_zero, h]
  norm_num

/-! ## 4. Explicit parameters for the error and memory bounds -/

/-- `F₂` over `Fin 4` within `F₂` (`η = 1`) with error `8 / 9`, from one pair of groups of `12`
copies: `(3 · 2) ^ 2 · 4 = 144 = (12 · 1²) ^ 2`. -/
example : (fkEstimator (Fin 4) 2 5 1 12).Solves (8 / 9)
    (fun s Y => s.length = 5 → |Y - freqMoment 2 s| ≤ 1 * freqMoment 2 s) 5 :=
  solves_fkEstimator two_ne_zero one_pos (by norm_num) (by norm_num)

/-- The `rpow` form of the group size condition, for `F₁`: `3 · 1 · 4 ^ 0 ≤ 3 · 1²`. -/
example : (fkEstimator (Fin 4) 1 5 1 3).Solves (8 / 9)
    (fun s Y => s.length = 5 → |Y - freqMoment 1 s| ≤ 1 * freqMoment 1 s) 5 :=
  solves_fkEstimator_of_rpow one_ne_zero one_pos (by norm_num) (by norm_num)

/-- Every sketch drawn uses `123` bits on streams of at most `5` items:
`6 · 30 ^ 24 ≤ 2 ^ 123`. -/
example : (fkEstimator (Fin 4) 2 5 1 12).SpaceLE 5 123 :=
  spaceLE_fkEstimator (by norm_num)

/-- With the positions stored, `180` bits suffice: `5 ^ 24 · 6 · 30 ^ 24 ≤ 2 ^ 180`. -/
example : ∃ enc : FkState (Fin 4) 5 1 12 → BitString 180,
    Set.InjOn enc (⋃ ω, (fkSketch 2 5 1 12 ω).reachable 5) :=
  exists_injOn_iUnion_reachable_fkSketch (by norm_num)

end ComplexityTests.StreamingFkEstimator
