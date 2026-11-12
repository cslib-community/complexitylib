/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Complexity.AverageCase

/-!
# Tests for `CslibFrontier.Computability.Complexity.AverageCase`

Concrete nonvacuity, rounded-logarithm, monotonicity, and uniform-PPT shift bridge tests for
`MildlyHardOnAverage`, `MildlyHardOnAverageToApprox`, and `MildlyHardOnAverageToOneSidedApprox`.
-/

public section

namespace Cslib.Complexity.AverageCaseTests

open Cslib Cslib.Complexity Filter Turing.MultiTapeTM
open scoped Polynomial ENNReal

/-- `fun _ => 0` is not `MildlyHardOnAverage`, `MildlyHardOnAverageDet`, `MildlyHardOnAverageIO`,
`MildlyHardOnAverageToApproxIO g`, `MildlyHardOnAverageToApproxDet g`,
`MildlyHardOnAverageToApprox g`, or `MildlyHardOnAverageToOneSidedApprox g` for any error
function `g`. -/
example (g : ℕ → ℕ) :
    ¬ MildlyHardOnAverage (fun _ => 0) ∧
    ¬ MildlyHardOnAverageDet (fun _ => 0) ∧
    ¬ MildlyHardOnAverageIO (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApproxIO g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApproxDet g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToApprox g (fun _ => 0) ∧
    ¬ MildlyHardOnAverageToOneSidedApprox g (fun _ => 0) :=
  ⟨not_mildlyHardOnAverage_zero,
   not_mildlyHardOnAverageDet_zero,
   not_mildlyHardOnAverageIO_zero,
   not_mildlyHardOnAverageToApproxIO_zero g,
   not_mildlyHardOnAverageToApproxDet_zero g,
   not_mildlyHardOnAverageToApprox_zero g,
   not_mildlyHardOnAverageToOneSidedApprox_zero g⟩

/-- Concrete instantiation of the rounded-logarithm comparison lemmas at $n = 6, d = 2$:
$\lceil \log_2 6 \rceil = 3 \le \lfloor \log_2 6 \rfloor + 1 = 3$, and any $v, w \in \mathbb{N}$
with $|(v : \mathbb{R}) - (w : \mathbb{R})| \le 2 \log_2 6$ satisfies `Nat.dist v w ≤ 6`. -/
example (v w : ℕ) (h : |(v : ℝ) - (w : ℝ)| ≤ (2 : ℝ) * Real.logb 2 (6 : ℝ)) :
    Nat.clog 2 6 ≤ Nat.log 2 6 + 1 ∧
    Real.logb 2 (6 : ℝ) ≤ (Nat.log 2 6 + 1 : ℕ) ∧
    Nat.dist v w ≤ 2 * (Nat.log 2 6 + 1) :=
  ⟨nat_clog_two_le_log_two_succ 6,
   real_logb_two_le_nat_log_two_succ (by omega : 1 ≤ 6),
   nat_dist_le_mul_log_two_succ_of_abs_sub_le_mul_logb (by omega : 1 ≤ 6) h⟩

/-- Concrete instantiation of `MildlyHardOnAverageToOneSidedApprox.mildlyHardOnAverageToApprox`
for a constant gap $g(n) = c$: one-sided $(2c)$-approximation hardness implies symmetric
$c$-approximation hardness, exact PPT hardness, deterministic hardness, and IO hardness. -/
example (c : ℕ) (f : List Bool → ℕ)
    (h : MildlyHardOnAverageToOneSidedApprox (fun _ => 2 * c) f) :
    MildlyHardOnAverageToApprox (fun _ => c) f ∧
    MildlyHardOnAverage f ∧
    MildlyHardOnAverageDet f ∧
    MildlyHardOnAverageIO f := by
  have hsymm : MildlyHardOnAverageToApprox (fun _ => c) f :=
    h.mildlyHardOnAverageToApprox (ComputableInPolyTime.const c)
  have hexact := hsymm.mildlyHardOnAverage
  exact ⟨hsymm, hexact, hexact.mildlyHardOnAverageDet, hexact.mildlyHardOnAverageIO⟩

end Cslib.Complexity.AverageCaseTests
