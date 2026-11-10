/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.AffineDisperser

/-!
# Explicit `4N - O(N / log N)` circuit lower bound and weight optimality

This module packages two consequences of Theorem 4.1 (`four_mul_le_size_add`):

* **Explicit lower bound in `P`**: applying `four_mul_le_size_add` to `explicitDisperser` and
  `explicitDisperserLanguage` yields a language in `P` requiring Boolean circuits of size at
  least `4 * N - 60 * N / (Nat.log 2 N + 1) - 10` for all sufficiently large `N`
  (`exists_mem_P_eventually_four_mul_sub_le_size`, and in natural numbers
  `eventually_four_mul_le_size_add_explicitDisperser`). Achieving `4n - O(log n)` (Theorem 1.1 of
  [Mishra and Santhanam][MishraSanthanam2027]) remains open pending the `O(log n)`-dimension
  affine disperser (`#4323`).
* **Remark 4.3 (Optimality of weights `α = 6, β = 4`)**: for any choice of non-negative weights
  `α` (per used unpaired parameter) and `β` (per pair) satisfying the linear constraints of
  Lemma 4.2, the leading coefficient `c - α` is at most `4` (`remark_4_3_bound`), and equality
  forces `4 ≤ β`, `6 ≤ α`, `10 ≤ c`, and `α = β + 2` (`remark_4_3_optimal`).

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.remark_4_3_bound`: the leading coefficient `c - α`
  cannot exceed `4`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.remark_4_3_optimal`: achieving `c - α = 4` forces
  `4 ≤ β`, `6 ≤ α`, `10 ≤ c`, and `α = β + 2`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.four_mul_le_size_add_explicitThreshold`: the
  `4n - 10d` bound instantiated at `explicitDisperser`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.eventually_four_mul_le_size_add_explicitDisperser`:
  asymptotic natural-number lower bound `4 * N ≤ C.size + 60 * N / (Nat.log 2 N + 1) + 10`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_four_mul_sub_le_size`:
  explicit language in `P` requiring `4 * N - O(N / log N)` circuit size.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2027]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Filter Cslib.Circuits Cslib.Complexity Cslib.AffineDisperser

/-! ### Remark 4.3: Optimality of the potential weights -/

/-- **Remark 4.3 (upper bound on the coefficient of `n`).** Under the linear constraints from
degenerate pairs / equations (`α ≤ β + 2`) and pair creation (`c ≤ 2 α - β + 2`), the leading
coefficient `c - α` cannot exceed `4`. -/
theorem remark_4_3_bound {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * α - β + 2) :
    c - α ≤ 4 := by
  linarith

/-- **Remark 4.3 (optimality of `α = 6, β = 4, c = 10`).** Any weight triple `(α, β, c)`
satisfying the constraints of Lemma 4.2 and achieving `c - α = 4` satisfies `4 ≤ β`, `6 ≤ α`,
`10 ≤ c`, and `α = β + 2`. -/
theorem remark_4_3_optimal {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * β + 2)
    (h₃ : c ≤ 2 * α - β + 2) (h₄ : c - α = 4) :
    4 ≤ β ∧ 6 ≤ α ∧ 10 ≤ c ∧ α = β + 2 :=
  ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Explicit `4N - O(N / log N)` lower bound for `explicitDisperser` -/

/-- Theorem 4.1 instantiated at `explicitDisperser N`. -/
theorem four_mul_le_size_add_explicitThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser N))) :
    4 * N ≤ C.size + 10 * (explicitThreshold N + 1) :=
  four_mul_le_size_add (isAffineDisperser_explicitDisperser N) C hC

/-- Asymptotic natural-number lower bound for `explicitDisperser N`:
eventually `4 * N ≤ C.size + 60 * N / (Nat.log 2 N + 1) + 10`. -/
theorem eventually_four_mul_le_size_add_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * N ≤ C.size + 60 * N / (Nat.log 2 N + 1) + 10 := by
  filter_upwards [eventually_explicitThreshold_le] with N hth C hC
  have hlb := four_mul_le_size_add_explicitThreshold C hC
  have hdiv : explicitThreshold N ≤ 6 * N / (Nat.log 2 N + 1) :=
    Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2 (by linarith)
  have hmul : 10 * (6 * N / (Nat.log 2 N + 1)) ≤ 60 * N / (Nat.log 2 N + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos _)]
    have := Nat.div_mul_le_self (6 * N) (Nat.log 2 N + 1)
    calc
      10 * (6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)
        = 10 * ((6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)) := by ring
      _ ≤ 10 * (6 * N) := Nat.mul_le_mul_left 10 this
      _ = 60 * N := by ring
  omega

/-- Asymptotic real lower bound for `explicitDisperser N`:
eventually `4 * N - 60 * N / (Nat.log 2 N + 1) - 10 ≤ C.size`. -/
theorem eventually_four_mul_sub_le_size_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * (N : ℝ) - 60 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 10 ≤ (C.size : ℝ) := by
  filter_upwards [eventually_explicitThreshold_le] with N hth C hC
  have hlb : (4 * N : ℝ) ≤ (C.size : ℝ) + 10 * ((explicitThreshold N : ℝ) + 1) := by
    exact_mod_cast four_mul_le_size_add_explicitThreshold C hC
  have hlog : (0 : ℝ) < (Nat.log 2 N : ℝ) + 1 := by positivity
  have hthR : ((Nat.log 2 N : ℝ) + 1) * (explicitThreshold N : ℝ) ≤ 6 * (N : ℝ) := by
    exact_mod_cast hth
  have hdiv : (explicitThreshold N : ℝ) ≤ 6 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) :=
    (le_div_iff₀ hlog).2 (by linarith)
  have hmul : 10 * (6 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1)) =
      60 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) := by ring
  linarith

/-- There exists an explicit language in `P` whose `N`-bit slices require Boolean circuits of
size at least `4 * N - O(N / log N)`. -/
theorem exists_mem_P_eventually_four_mul_sub_le_size :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 60 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 10 ≤ (C.size : ℝ) := by
  refine ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, ?_⟩
  filter_upwards [eventually_four_mul_sub_le_size_of_computes_explicitDisperser] with N hN C hC
  rw [slice_explicitDisperserLanguage] at hC
  exact hN C hC

end Cslib.Circuits.Boolean.AffineDisperser4n
