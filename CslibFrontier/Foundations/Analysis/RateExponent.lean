/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Rate exponents

Fine-grained complexity measures a task by the least rate at which it can be done within a family
of resource bounds indexed by a rate `δ`: the exponent `s_k` of `k`-SAT is the infimum of the
`δ ≥ 0` for which `k`-SAT is decidable within time `2 ^ (δ * n)` times a polynomial
[ImpagliazzoPaturi2001]. `Cslib.rateExponent P` is this infimum `sInf {δ | 0 ≤ δ ∧ P δ}` for a
predicate `P : ℝ → Prop`. The characterizations below need only that `P` is monotone (a larger
rate allows more) and holds at `1` (exhaustive search, in the applications), so every exponent
defined through `rateExponent` inherits them.

## Main definitions

* `Cslib.rateExponent`: the infimum of the nonnegative rates satisfying a predicate.

## Main results

* `Cslib.rateExponent_def`: the defining infimum, for clients that do not see the body.
* `Cslib.rateExponent_le`, `Cslib.le_rateExponent`: upper bounds from attained rates and lower
  bounds from unattained ones.
* `Cslib.rateExponent_le_rateExponent`: a weaker requirement has a smaller exponent.
* `Cslib.rateExponent_pos_iff`, `Cslib.rateExponent_eq_zero_iff`: the exponent is positive iff some
  positive rate is not attained, and zero iff every positive rate is attained.
* `Cslib.rateExponent_eq_sInf_pos`: the infimum may equally range over the rates `δ > 0`.
* `Cslib.tendsto_rateExponent_iff`: exponents of a family, monotone in the index, tend to `1` iff
  for every `ε > 0` some member of the family is not attained at rate `1 - ε`.

## References

* [R. Impagliazzo, R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]
-/

public section

namespace Cslib

open Filter Topology

/-- The rate exponent of `P`: the infimum of the rates `δ ≥ 0` satisfying `P`. In the
applications `P δ` says that a task can be done within a resource bound at rate `δ`. -/
noncomputable def rateExponent (P : ℝ → Prop) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ P δ}

/-- The defining infimum of `rateExponent`, for clients that do not see its body. -/
theorem rateExponent_def (P : ℝ → Prop) : rateExponent P = sInf {δ | 0 ≤ δ ∧ P δ} := by
  rw [rateExponent]

variable {P Q : ℝ → Prop} {δ : ℝ}

theorem rateExponent_nonneg (P : ℝ → Prop) : 0 ≤ rateExponent P :=
  Real.sInf_nonneg fun _ h => h.1

/-- The exponent is at most every attained rate. -/
theorem rateExponent_le (hδ : 0 ≤ δ) (h : P δ) : rateExponent P ≤ δ :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hδ, h⟩

theorem rateExponent_le_one (h1 : P 1) : rateExponent P ≤ 1 :=
  rateExponent_le zero_le_one h1

/-- Below the exponent no rate is attained. -/
theorem not_of_lt_rateExponent (hδ : 0 ≤ δ) (h : δ < rateExponent P) : ¬P δ := fun h' =>
  (rateExponent_le hδ h').not_gt h

/-- An unattained rate bounds the exponent from below. -/
theorem le_rateExponent (hP : Monotone P) (h1 : P 1) (h : ¬P δ) : δ ≤ rateExponent P :=
  le_csInf ⟨1, zero_le_one, h1⟩ fun _ h' => le_of_not_gt fun hlt => h (hP hlt.le h'.2)

/-- Above the exponent every rate is attained. -/
theorem of_rateExponent_lt (hP : Monotone P) (h1 : P 1) (h : rateExponent P < δ) : P δ :=
  not_not.mp fun h' => (le_rateExponent hP h1 h').not_gt h

/-- A weaker requirement has a smaller exponent. -/
theorem rateExponent_le_rateExponent (h1 : Q 1) (h : ∀ δ, 0 ≤ δ → Q δ → P δ) :
    rateExponent P ≤ rateExponent Q :=
  le_csInf ⟨1, zero_le_one, h1⟩ fun δ hδ => rateExponent_le hδ.1 (h δ hδ.1 hδ.2)

/-- The exponent is positive iff some positive rate is not attained. -/
theorem rateExponent_pos_iff (hP : Monotone P) (h1 : P 1) :
    0 < rateExponent P ↔ ∃ δ, 0 < δ ∧ ¬P δ :=
  ⟨fun h => ⟨rateExponent P / 2, half_pos h,
      not_of_lt_rateExponent (half_pos h).le (half_lt_self h)⟩,
    fun ⟨_, hδ, h⟩ => hδ.trans_le (le_rateExponent hP h1 h)⟩

/-- The exponent is zero iff every positive rate is attained. -/
theorem rateExponent_eq_zero_iff (hP : Monotone P) (h1 : P 1) :
    rateExponent P = 0 ↔ ∀ δ, 0 < δ → P δ :=
  ⟨fun h _ hδ => of_rateExponent_lt hP h1 (h.trans_lt hδ), fun h =>
    le_antisymm (le_of_not_gt fun hpos =>
      let ⟨δ, hδ, hn⟩ := (rateExponent_pos_iff hP h1).1 hpos; hn (h δ hδ))
      (rateExponent_nonneg P)⟩

/-- The infimum defining the exponent may equally range over the rates `δ > 0`. -/
theorem rateExponent_eq_sInf_pos (hP : Monotone P) (h1 : P 1) :
    rateExponent P = sInf {δ | 0 < δ ∧ P δ} :=
  le_antisymm (le_csInf ⟨1, one_pos, h1⟩ fun _ hδ => rateExponent_le hδ.1.le hδ.2)
    (le_of_forall_gt_imp_ge_of_dense fun _ hδ => csInf_le ⟨0, fun _ h => h.1.le⟩
      ⟨(rateExponent_nonneg P).trans_lt hδ, of_rateExponent_lt hP h1 hδ⟩)

/-- **Exponents tending to `1`.** For a family of monotone predicates holding at `1` whose
exponents are monotone in the index, the exponents tend to `1` iff for every `ε > 0` some member
of the family is not attained at rate `1 - ε`. -/
theorem tendsto_rateExponent_iff {P : ℕ → ℝ → Prop} (hP : ∀ k, Monotone (P k))
    (h1 : ∀ k, P k 1) (hmono : Monotone fun k => rateExponent (P k)) :
    Tendsto (fun k => rateExponent (P k)) atTop (𝓝 1) ↔ ∀ ε, 0 < ε → ∃ k, ¬P k (1 - ε) := by
  constructor
  · intro h ε hε
    obtain ⟨k, hk⟩ :=
      (h.eventually (lt_mem_nhds (max_lt (by linarith : 1 - ε < 1) one_pos))).exists
    exact ⟨k, fun h' => not_of_lt_rateExponent (le_max_right _ _) hk (hP k (le_max_left _ _) h')⟩
  · intro h
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha =>
      .of_forall fun k => (rateExponent_le_one (h1 k)).trans_lt ha⟩
    obtain ⟨b, hab, hb1⟩ := exists_between ha
    obtain ⟨k₀, hk₀⟩ := h (1 - b) (sub_pos.2 hb1)
    rw [sub_sub_cancel] at hk₀
    exact eventually_atTop.2 ⟨k₀, fun k hk =>
      hab.trans_le ((le_rateExponent (hP k₀) (h1 k₀) hk₀).trans (hmono hk))⟩

end Cslib
