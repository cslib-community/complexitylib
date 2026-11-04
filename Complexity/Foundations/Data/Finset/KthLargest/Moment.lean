/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate
public import Complexity.Foundations.Data.Finset.KthLargest
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Moments of a zero-padded maximum

The maximum power is bounded by the sum of powers, including the empty set.
Extracted from Samuel Schlesinger's heavy-count rarity proof for reuse with random rows.
-/
public section
namespace Finset
open scoped BigOperators

/-- A full-slice maximum costs at most the sum of absolute entry powers. -/
theorem abs_kthLargest_pow_le_sum {V : Type*} {s : ℕ} (S : Finset V) (b : V → ℝ)
    (hs : s ≠ 0) : |kthLargest 1 S (fun y => |b y|)| ^ s ≤ ∑ y ∈ S, |b y| ^ s := by
  classical
  have hmem : kthLargest 1 S (fun y => |b y|) ∈
      insert 0 ((S.filter fun y => 1 ≤ #{w ∈ S | |b y| ≤ |b w|}).image fun y => |b y|) :=
    max'_mem _ _
  rcases mem_insert.mp hmem with hz | hmem
  · rw [hz, abs_zero, zero_pow hs]
    positivity
  · obtain ⟨y, hy, heq⟩ := mem_image.mp hmem
    rw [← heq, abs_abs]
    exact single_le_sum (f := fun y => |b y| ^ s)
      (fun _ _ => by positivity) (mem_filter.mp hy).1

end Finset
