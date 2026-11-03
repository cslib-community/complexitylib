/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold

/-!
# Linear threshold functions on finite domains

Evaluation, nonzero coordinate support and magnitude ranks for real-weight threshold
functions on arbitrary finite input types. Restriction and counting arguments can import
this module without the depth-two circuit constructor.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.ltfEval`: evaluation with threshold ties accepted.
* `Cslib.Circuits.Boolean.WeightedThreshold.ltfSupport`: nonzero input coefficients.
* `Cslib.Circuits.Boolean.WeightedThreshold.ltfWeightRank`: number of nonzero coefficients
  with magnitude at least that of the selected coordinate, including ties.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open Finset

/-- Linear threshold function `decide (θ ≤ ∑ i : ι, a i * (w i).toNat)` on `ι → Bool`. -/
noncomputable def ltfEval {ι : Type*} [Fintype ι] (a : ι → ℝ) (θ : ℝ) (w : ι → Bool) : Bool :=
  decide (θ ≤ ∑ i : ι, a i * (w i).toNat)

/-- Evaluating `op : WeightedThreshold.Op` under `WeightedThreshold.interpretation` is `ltfEval`. -/
theorem interpretation_eq_ltfEval (op : Op) (w : Fin op.arity → Bool) :
    interpretation op w = ltfEval op.weight op.threshold w :=
  rfl

/-- The active coordinate support `{i : ι | a i ≠ 0}` of a weight vector `a : ι → ℝ`. -/
noncomputable def ltfSupport {ι : Type*} [Fintype ι] (a : ι → ℝ) : Finset ι :=
  univ.filter fun i : ι => a i ≠ 0

@[simp]
theorem mem_ltfSupport {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) :
    i ∈ ltfSupport a ↔ a i ≠ 0 := by
  simp [ltfSupport]

/-- The weight rank `k_i = #{j ∈ ltfSupport a | |a i| ≤ |a j|}` of coordinate `i` in `ltfSupport a`
(counting nonzero weights of magnitude at least `|a i|`). -/
noncomputable def ltfWeightRank {ι : Type*} [Fintype ι] (a : ι → ℝ) (i : ι) : ℕ :=
  #{j ∈ ltfSupport a | |a i| ≤ |a j|}

/-- For every `i ∈ ltfSupport a`, `1 ≤ ltfWeightRank a i`. -/
theorem one_le_ltfWeightRank {ι : Type*} [Fintype ι] {a : ι → ℝ} {i : ι}
    (hi : i ∈ ltfSupport a) : 1 ≤ ltfWeightRank a i :=
  card_pos.mpr ⟨i, mem_filter.mpr ⟨hi, le_rfl⟩⟩

/-- If `|a i| ≤ |a j|`, then `ltfWeightRank a j ≤ ltfWeightRank a i`. -/
theorem ltfWeightRank_le_of_abs_le {ι : Type*} [Fintype ι] (a : ι → ℝ) {i j : ι}
    (hij : |a i| ≤ |a j|) : ltfWeightRank a j ≤ ltfWeightRank a i :=
  card_le_card fun _ hl => mem_filter.mpr ⟨(mem_filter.mp hl).1, hij.trans (mem_filter.mp hl).2⟩

end Cslib.Circuits.Boolean.WeightedThreshold
