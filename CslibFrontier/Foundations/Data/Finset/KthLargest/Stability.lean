/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate
public import CslibFrontier.Foundations.Data.Finset.KthLargest
public import Mathlib.Basic.Real.Basic

/-!
# Full-slice error bounds for padded ranks

Both ranks use the same finite set. Signed, unbounded values and empty sets are
allowed. Division retains its actual positive normalization rate.
-/
public section
namespace Finset

/-- Rank perturbations are bounded by the padded maximum absolute input error. -/
theorem abs_kthLargest_sub_le_kthLargest_one {V : Type*} {k : ℕ} (hk : 0 < k)
    (S : Finset V) (a b : V → ℝ) :
    |kthLargest k S a - kthLargest k S b| ≤
      kthLargest 1 S (fun x => |a x - b x|) :=
  abs_kthLargest_sub_kthLargest_le hk kthLargest_nonneg
    (fun x hx => abs_le_kthLargest_one S (fun x => a x - b x) x hx)

/-- Dividing both signed inputs by the same positive rate divides the full-slice
error maximum by that rate. No scalar clipping is applied before ranking. -/
theorem abs_kthLargest_div_sub_div_le {V : Type*} {k : ℕ} (hk : 0 < k)
    {r : ℝ} (hr : 0 < r) (S : Finset V) (a b : V → ℝ) :
    |kthLargest k S (fun x => a x / r) - kthLargest k S (fun x => b x / r)| ≤
      kthLargest 1 S (fun x => |a x - b x|) / r := by
  apply abs_kthLargest_sub_kthLargest_le hk (div_nonneg kthLargest_nonneg hr.le)
  intro x hx
  rw [← sub_div, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right
    (abs_le_kthLargest_one S (fun x => a x - b x) x hx) hr.le

/-- A padded rank above the size of its actual set is zero, including for signed inputs. -/
theorem kthLargest_eq_zero_of_card_lt {V R : Type*} [LinearOrder R] [Zero R]
    {k : ℕ} {S : Finset V} (hk : S.card < k) (a : V → R) : kthLargest k S a = 0 := by
  classical
  have he : S.filter (fun x => k ≤ #{w ∈ S | a x ≤ a w}) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro x _ hx
    exact (not_le_of_gt ((card_filter_le _ _).trans_lt hk)) hx
  simp [kthLargest, he]

end Finset
