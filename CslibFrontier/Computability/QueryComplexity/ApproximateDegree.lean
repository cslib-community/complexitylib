/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Mathlib.Basic.NNReal.Basic

public import CslibFrontier.Computability.QueryComplexity.Degree

/-!
# Approximate degree

The `ε`-approximate degree `adeg_ε(f)` of a Boolean function `f` is the least degree of a real
function on the cube that is within `ε` of `f`, read with values `0` and `1`, at every input
(`QueryComplexity.approxDegree`) [NisanSzegedy1994], [BuhrmanDeWolf2002]. The approximate degree
`adeg(f)` of the literature is `adeg_{1/3}(f)`; any constant `ε < 1/2` changes it by at most a
constant factor.

Exact representation is the case `ε = 0` (`QueryComplexity.approxDegree_zero`), so
`adeg_ε(f) ≤ deg(f) ≤ D(f)` (`QueryComplexity.approxDegree_le_degree`,
`DecisionTree.approxDegree_le_complexity`). Approximate degree decreases as `ε` grows and vanishes
from `ε = 1/2` on, where the constant `1/2` is within `ε` of every Boolean function
(`QueryComplexity.approxDegree_eq_zero_of_le`). Its error budget is a nonnegative real, so the
feasible set always contains the exact representation. Negating the output does not change it.

## Main definitions

* `Cslib.QueryComplexity.approxDegree`: the `ε`-approximate degree `adeg_ε(f)`.

## Main results

* `Cslib.QueryComplexity.exists_mem_lowDegree_approxDegree`: for `ε ≥ 0` the approximate degree
  is attained.
* `Cslib.QueryComplexity.approxDegree_zero`: `adeg_0(f) = deg(f)`.
* `Cslib.QueryComplexity.approxDegree_le_degree`, `Cslib.DecisionTree.approxDegree_le_complexity`:
  `adeg_ε(f) ≤ deg(f) ≤ D(f)`.
* `Cslib.QueryComplexity.approxDegree_antitone`: `adeg_ε(f)` decreases as `ε` grows.
* `Cslib.QueryComplexity.approxDegree_eq_zero_of_le`: `adeg_ε(f) = 0` for `ε ≥ 1/2`.

## References

* [N. Nisan, M. Szegedy, *On the degree of Boolean functions as real polynomials*][NisanSzegedy1994]
* [H. Buhrman, R. de Wolf, *Complexity measures and decision tree complexity:
  a survey*][BuhrmanDeWolf2002]
-/

@[expose] public section

open scoped NNReal

namespace Cslib

namespace QueryComplexity

open BitString

variable {n : ℕ} {f : BooleanFunction n} {ε δ : ℝ≥0}

/-- The `ε`-approximate degree `adeg_ε(f)` of a Boolean function: the least degree of a real
function on the cube that is within the nonnegative error budget `ε` of `f`, read with values
`0` and `1`, at every input. The exact representation witnesses feasibility. -/
noncomputable def approxDegree (ε : ℝ≥0) (f : BooleanFunction n) : ℕ :=
  sInf {D | ∃ p ∈ lowDegree ℝ (Fin n) D, ∀ x, |p x - bitVal ℝ (f x)| ≤ ε}

/-- A real function of degree at most `D` within `ε` of `f` bounds `adeg_ε(f)` by `D`. -/
theorem approxDegree_le_of_mem_lowDegree {p : BitString n → ℝ} {D : ℕ}
    (hp : p ∈ lowDegree ℝ (Fin n) D) (h : ∀ x, |p x - bitVal ℝ (f x)| ≤ ε) :
    approxDegree ε f ≤ D :=
  Nat.sInf_le ⟨p, hp, h⟩

/-- For `ε ≥ 0` the approximate degree is attained: some real function of degree `adeg_ε(f)` is
within `ε` of `f`. -/
theorem exists_mem_lowDegree_approxDegree :
    ∃ p ∈ lowDegree ℝ (Fin n) (approxDegree ε f), ∀ x, |p x - bitVal ℝ (f x)| ≤ ε :=
  Nat.sInf_mem (s := {D | ∃ p ∈ lowDegree ℝ (Fin n) D, ∀ x, |p x - bitVal ℝ (f x)| ≤ ε})
    ⟨degree f, _, mem_lowDegree_totalDegree _, fun x => by simp⟩

/-- `adeg_ε(f) ≤ deg(f)` for `ε ≥ 0`. -/
theorem approxDegree_le_degree : approxDegree ε f ≤ degree f :=
  approxDegree_le_of_mem_lowDegree (mem_lowDegree_totalDegree _) fun x => by simp

/-- `adeg_ε(f) ≤ n` for `ε ≥ 0`. -/
theorem approxDegree_le_card : approxDegree ε f ≤ n :=
  approxDegree_le_degree.trans (degree_le_card f)

/-- Exact representation: `adeg_0(f) = deg(f)`. -/
theorem approxDegree_zero : approxDegree 0 f = degree f := by
  refine le_antisymm approxDegree_le_degree ?_
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_approxDegree (ε := 0) (f := f)
  have h : p = fun x => bitVal ℝ (f x) :=
    funext fun x => sub_eq_zero.1 (abs_nonpos_iff.1 (hpf x))
  exact degree_le_iff_mem_lowDegree.2 (h ▸ hp)

/-- `adeg_ε(f)` decreases as `ε` grows. -/
theorem approxDegree_antitone (hεδ : ε ≤ δ) : approxDegree δ f ≤ approxDegree ε f := by
  obtain ⟨p, hp, hpf⟩ := exists_mem_lowDegree_approxDegree (ε := ε) (f := f)
  exact approxDegree_le_of_mem_lowDegree hp fun x => (hpf x).trans hεδ

/-- From `ε = 1/2` on, the constant `1/2` is within `ε` of every Boolean function. -/
theorem approxDegree_eq_zero_of_le (hε : (1 / 2 : ℝ) ≤ ε) : approxDegree ε f = 0 :=
  Nat.le_zero.1 (approxDegree_le_of_mem_lowDegree (const_mem_lowDegree 0 (1 / 2)) fun x => by
    cases f x <;> norm_num [abs_of_pos, hε])

/-- Negating a Boolean function preserves its approximate degree: `1 - p` approximates `!f` as
well as `p` approximates `f`. -/
theorem approxDegree_not (ε : ℝ≥0) (f : BooleanFunction n) :
    approxDegree ε (fun x => !f x) = approxDegree ε f := by
  have key (g : BooleanFunction n) : approxDegree ε g ≤ approxDegree ε (fun x => !g x) := by
    obtain ⟨p, hp, hpg⟩ := exists_mem_lowDegree_approxDegree (ε := ε) (f := fun x => !g x)
    refine approxDegree_le_of_mem_lowDegree (one_sub_mem_lowDegree hp) fun x => ?_
    have := hpg x
    rw [bitVal_not, ← abs_neg] at this
    convert this using 2
    simp only [Pi.sub_apply, Pi.one_apply]
    ring
  refine le_antisymm ?_ (key f)
  simpa only [Bool.not_not] using key fun x => !f x

end QueryComplexity

namespace DecisionTree

/-- `adeg_ε(f) ≤ D(f)` for `ε ≥ 0`. -/
theorem approxDegree_le_complexity {n : ℕ} (f : BooleanFunction n) {ε : ℝ≥0} :
    QueryComplexity.approxDegree ε f ≤ complexity f :=
  QueryComplexity.approxDegree_le_degree.trans (degree_le_complexity f)

end DecisionTree

end Cslib
