/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Completeness
public import CslibFrontier.Foundations.Data.BitString.List.BinaryOrder
public import CslibFrontier.Foundations.Data.Nat.Bitwise.CommonPrefix

/-!
# Tests for Levin's completeness theorem

Checked instances for `CslibFrontier.Computability.Complexity.Classes.AverageCase.Completeness` and
its supporting modules:

* the binary-order and common-prefix facts on concrete words and numbers;
* the compression of Claim 20 instantiated with the uniform ensemble's cumulative distribution;
* a concrete instance of the bounded halting problem: its header length and its exact probability
  `2^{-9}` under `U^BH`, and words outside `BH`;
* `(BH, U^BH) ∈ DistNP`, completeness, and the `AvgP`/`HeurP` corollaries.
-/

@[expose] public section

namespace Cslib.Complexity.AverageCaseCompletenessTests

open Cslib Cslib.Complexity Turing.MultiTapeTM
open scoped ENNReal

/-! ### Binary order and common prefixes -/

/-- `10` is a prefix of `101`: the values of the words of length `3` beginning with `10` are
`4` and `5`. -/
example : [true, false] <+: [true, false, true] :=
  (BitString.isPrefix_iff_binaryValue (by decide)).mpr (by decide)

/-- `11` is not a prefix of `101`. -/
example : ¬ [true, true] <+: [true, false, true] := fun h =>
  absurd ((BitString.isPrefix_iff_binaryValue (by decide)).mp h) (by decide)

/-- The predecessor of `100` represents `3`. -/
example : BitString.binaryValue (BitString.predWord [true, false, false]) = 3 := by
  rw [BitString.binaryValue_predWord]
  decide

/-- `5 = 101` and `6 = 110` agree above their two low bits, and the dyadic point `(2·1+1)·2 = 6`
of their common prefix `1` lies in `(5, 6]`. -/
example : (5 ^^^ 6 : ℕ).size = 2 ∧ (2 * (5 / 2 ^ 2) + 1) * 2 ^ (2 - 1) = 6 := by
  decide

example : 5 < (2 * (5 / 2 ^ (5 ^^^ 6 : ℕ).size) + 1) * 2 ^ ((5 ^^^ 6 : ℕ).size - 1) :=
  (Nat.lt_commonPrefix_mid_le (by decide : 5 < 6)).2.2.1

/-! ### Compression under the uniform ensemble -/

section Uniform

/-- The numerator of the uniform cumulative distribution. -/
def uNum (x : List Bool) : ℕ := BitString.binaryValue x + 1

/-- The denominator of the uniform cumulative distribution. -/
def uDen (x : List Bool) : ℕ := 2 ^ x.length

theorem uniform_cdf_eq (x : List Bool) :
    Ensemble.uniform.cdf x = (uNum x : ℝ≥0∞) / uDen x :=
  Ensemble.cdf_uniform x

theorem uDen_ne_zero (x : List Bool) : uDen x ≠ 0 := by
  unfold uDen
  positivity

/-- The code of Claim 20 for the uniform ensemble has at most one extra bit. -/
example (x : List Bool) : (Compression.compress uNum uDen x).length ≤ x.length + 1 :=
  Compression.length_compress_le uniform_cdf_eq uDen_ne_zero x

/-- It is injective on each length. -/
example (x x' : List Bool) (hlen : x.length = x'.length)
    (h : Compression.compress uNum uDen x = Compression.compress uNum uDen x') : x = x' :=
  Compression.compress_injective uniform_cdf_eq uDen_ne_zero hlen h

/-- No word is heavy under the uniform ensemble: `D_n(x) = 2^{-n}` exactly. -/
example (x : List Bool) : Compression.heavy uNum uDen x = false := by
  rw [Bool.eq_false_iff, ne_eq, Compression.heavy_iff uDen_ne_zero]
  intro h
  have hd := Compression.dist_eq uniform_cdf_eq uDen_ne_zero x
  rw [Ensemble.uniform_apply] at hd
  have hab := Compression.aR_le_bR uniform_cdf_eq uDen_ne_zero x
  have h2 : (0 : ℝ) < 2 ^ x.length := by positivity
  have hval : Compression.bR uNum uDen x - Compression.aR uNum uDen x = (2 ^ x.length)⁻¹ := by
    have := congrArg ENNReal.toReal hd
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat] at this
    exact this.symm
  have : (Compression.bR uNum uDen x - Compression.aR uNum uDen x) * 2 ^ x.length = 1 := by
    rw [hval, inv_mul_cancel₀ h2.ne']
  linarith

end Uniform

/-! ### The bounded halting problem -/

/-- The header of the instance with program `[]` and input `[true]`: `frame [] = 0`,
`frame (lenWord 1) = 110`, then the input `1`. -/
example : (BoundedHalting.header [] [true]).length = 5 := by
  simp

/-- An instance `(c, z, 1^t)` with a header of length `9` has probability exactly `2^{-9}` under
`U^BH`, whatever the clock `t`. -/
example (t : ℕ) :
    BoundedHalting.uniformBH.dist (BoundedHalting.encode [] [true, false, true] t).length
        (BoundedHalting.encode [] [true, false, true] t) = (2 ^ 9 : ℝ≥0∞)⁻¹ := by
  rw [BoundedHalting.uniformBH_dist_encode]
  congr 2
  simp [show Nat.size 3 = 2 by decide]

/-- Every word beginning with a header is valid; the empty word is not an instance. -/
example (s : List Bool) : BoundedHalting.valid (BoundedHalting.header [true] [] ++ s) = true :=
  BoundedHalting.valid_header_append _ _ _

/-- Words too short to hold a header are not in `BH`. -/
example : [] ∉ BoundedHalting.BH := by
  rw [BoundedHalting.mem_BH_iff]
  rintro ⟨c, z, t, h, -⟩
  have := congrArg List.length h
  simp only [List.length_nil, BoundedHalting.length_encode, BoundedHalting.length_header] at this
  omega

/-- Instances are fixed by the collapse that defines `U^BH`. -/
example (t : ℕ) : BoundedHalting.parser.collapse (BoundedHalting.encode [true] [false] t) =
    BoundedHalting.encode [true] [false] t :=
  BoundedHalting.collapse_encode _ _ _

/-! ### Completeness -/

example : BoundedHalting.problem ∈ DistNP := BoundedHalting.problem_mem_DistNP

example : DistComplete DistNP BoundedHalting.problem := BoundedHalting.distComplete_problem

/-- If `(BH, U^BH)` has an errorless heuristic scheme, so does every problem of `DistNP`. -/
example (h : BoundedHalting.problem ∈ AvgP) (L : DistProblem) (hL : L ∈ DistNP) : L ∈ AvgP :=
  BoundedHalting.problem_mem_AvgP_iff.mp h hL

/-- For example, an errorless heuristic scheme for `(BH, U^BH)` gives one for `BH` under the
uniform ensemble, which is also in `DistNP`. -/
example (h : BoundedHalting.problem ∈ AvgP) : ⟨BoundedHalting.BH, Ensemble.uniform⟩ ∈ AvgP :=
  BoundedHalting.problem_mem_AvgP_iff.mp h
    (mem_DistNP.mpr ⟨BoundedHalting.BH_mem_NP, Ensemble.uniform_pComp⟩)

example (h : BoundedHalting.problem ∈ HeurP) (L : DistProblem) (hL : L ∈ DistNP) : L ∈ HeurP :=
  BoundedHalting.problem_mem_HeurP_iff.mp h hL

end Cslib.Complexity.AverageCaseCompletenessTests
