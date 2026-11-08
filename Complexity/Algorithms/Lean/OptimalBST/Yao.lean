/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.OptimalBST.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Tactic.Abel

/-!
# The quadrangle inequality and monotone optimal roots

An interval weight `f : ℕ → ℕ → β` satisfies the *quadrangle inequality* (`QuadrangleIneq`) if
`f i j + f i' j' ≤ f i j' + f i' j` whenever `i ≤ i' ≤ j ≤ j'`, and is *monotone on intervals*
(`MonotoneOnIntervals`) if `f i' j ≤ f i j'` whenever `[i', j] ⊆ [i, j']`. Yao proved that if the
weight `w` has both properties, then the optimal cost `c = optCost w` of the interval recurrence
satisfies the quadrangle inequality (`quadrangleIneq_optCost`), and that the quadrangle
inequality for `c` makes the largest optimal root `K = optRoot w` monotone:
`K(i, j - 1) ≤ K(i, j) ≤ K(i + 1, j)` (`optRoot_mono`). For optimal binary search trees this
monotonicity is Knuth's theorem; Knuth's weight `knuthWeight p q` satisfies the quadrangle
inequality with equality (`knuthWeight_add_knuthWeight`), and is monotone on intervals when the
weights are nonnegative (`monotoneOnIntervals_knuthWeight`).

The monotonicity of roots is stated for the *largest* optimal root. It uses cancellation in `β`
(`IsOrderedCancelAddMonoid`), which holds for `ℕ`, `ℤ`, `ℚ` and `ℝ`.

## Main definitions

* `Cslib.Algorithms.Lean.OptimalBST.QuadrangleIneq`: the quadrangle inequality.
* `Cslib.Algorithms.Lean.OptimalBST.MonotoneOnIntervals`: monotonicity on the lattice of
  intervals.

## Main results

* `Cslib.Algorithms.Lean.OptimalBST.quadrangleIneq_optCost`: Yao's lemma, the optimal cost
  inherits the quadrangle inequality.
* `Cslib.Algorithms.Lean.OptimalBST.optRoot_mono`: monotonicity of the largest optimal roots.
* `Cslib.Algorithms.Lean.OptimalBST.quadrangleIneq_knuthWeight`,
  `Cslib.Algorithms.Lean.OptimalBST.monotoneOnIntervals_knuthWeight`: Knuth's weight satisfies
  both hypotheses.

## References

* [D. E. Knuth, *Optimum binary search trees*][Knuth1971]
* [F. F. Yao, *Efficient dynamic programming using quadrangle inequalities*][Yao1980]
-/

public section

namespace Cslib.Algorithms.Lean.OptimalBST

open Finset

variable {β : Type*}

section Defs

variable [Add β] [LE β]

/-- The quadrangle inequality: `f i j + f i' j' ≤ f i j' + f i' j` for `i ≤ i' ≤ j ≤ j'`. -/
@[expose] def QuadrangleIneq (f : ℕ → ℕ → β) : Prop :=
  ∀ ⦃i i' j j' : ℕ⦄, i ≤ i' → i' ≤ j → j ≤ j' → f i j + f i' j' ≤ f i j' + f i' j

/-- Monotonicity on the lattice of intervals: `f i' j ≤ f i j'` whenever `[i', j] ⊆ [i, j']`. -/
@[expose] def MonotoneOnIntervals (f : ℕ → ℕ → β) : Prop :=
  ∀ ⦃i i' j j' : ℕ⦄, i ≤ i' → i' ≤ j → j ≤ j' → f i' j ≤ f i j'

end Defs

section Yao

variable [AddCommMonoid β] [LinearOrder β]

section Ordered

variable [IsOrderedAddMonoid β]

private theorem add4_le {a b e f g h c₁ c₂ d₁ d₂ : β} (h₁ : a ≤ e + f) (h₂ : b ≤ g + h)
    (h₃ : e + g ≤ c₁ + c₂) (h₄ : f + h ≤ d₁ + d₂) : a + b ≤ (c₁ + d₁) + (c₂ + d₂) :=
  calc a + b ≤ (e + f) + (g + h) := add_le_add h₁ h₂
    _ = (e + g) + (f + h) := by abel
    _ ≤ (c₁ + c₂) + (d₁ + d₂) := add_le_add h₃ h₄
    _ = (c₁ + d₁) + (c₂ + d₂) := by abel

/-- **Yao's lemma**: if `w` satisfies the quadrangle inequality and is monotone on intervals, then
the optimal cost `c = optCost w` of the interval recurrence satisfies the quadrangle inequality. -/
theorem quadrangleIneq_optCost {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w)
    (hmono : MonotoneOnIntervals w) : QuadrangleIneq (optCost w) := by
  suffices H : ∀ n i i' j j', j' - i = n → i ≤ i' → i' ≤ j → j ≤ j' →
      optCost w i j + optCost w i' j' ≤ optCost w i j' + optCost w i' j from
    fun i i' j j' h₁ h₂ h₃ => H _ i i' j j' rfl h₁ h₂ h₃
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i i' j j' hn h₁ h₂ h₃
  have IH : ∀ a a' b b', b' - a < n → a ≤ a' → a' ≤ b → b ≤ b' →
      optCost w a b + optCost w a' b' ≤ optCost w a b' + optCost w a' b :=
    fun a a' b b' hlt => ih _ (hn ▸ hlt) a a' b b' rfl
  rcases h₁.eq_or_lt with rfl | hii'
  · exact le_of_eq (add_comm _ _)
  rcases h₃.eq_or_lt with rfl | hjj'
  · exact le_rfl
  rcases h₂.eq_or_lt with rfl | hi'j
  · -- `i' = j`: show `c(i, i') + c(i', j') ≤ c(i, j')`
    rw [optCost_of_le w (le_refl i'), add_zero]
    have hz := mem_Ioc.1 (optRoot_mem w (show i < j' by omega))
    rw [optCost_eq_optRoot w (show i < j' by omega), splitCost]
    generalize optRoot w i j' = z at hz ⊢
    rcases le_or_gt z i' with hzi' | hzi'
    · -- the root lies in `(i, i']`
      have h₁ : optCost w i i' ≤ w i i' + (optCost w i (z - 1) + optCost w z i') :=
        optCost_le w (mem_Ioc.2 ⟨hz.1, hzi'⟩)
      have h₂ := IH z i' i' j' (by omega) hzi' le_rfl hjj'.le
      rw [optCost_of_le w (le_refl i'), add_zero] at h₂
      calc optCost w i i' + optCost w i' j'
          ≤ w i i' + (optCost w i (z - 1) + optCost w z i') + optCost w i' j' :=
            add_le_add h₁ le_rfl
        _ = w i i' + (optCost w i (z - 1) + (optCost w z i' + optCost w i' j')) := by abel
        _ ≤ w i j' + (optCost w i (z - 1) + optCost w z j') :=
            add_le_add (hmono le_rfl hii'.le hjj'.le) (add_le_add le_rfl h₂)
    · -- the root lies in `(i', j']`
      have h₁ : optCost w i' j' ≤ w i' j' + (optCost w i' (z - 1) + optCost w z j') :=
        optCost_le w (mem_Ioc.2 ⟨hzi', hz.2⟩)
      have h₂ := IH i i' i' (z - 1) (by omega) hii'.le le_rfl (by omega)
      rw [optCost_of_le w (le_refl i'), add_zero] at h₂
      calc optCost w i i' + optCost w i' j'
          ≤ optCost w i i' + (w i' j' + (optCost w i' (z - 1) + optCost w z j')) :=
            add_le_add le_rfl h₁
        _ = w i' j' + ((optCost w i i' + optCost w i' (z - 1)) + optCost w z j') := by abel
        _ ≤ w i j' + (optCost w i (z - 1) + optCost w z j') :=
            add_le_add (hmono hii'.le (by omega) le_rfl) (add_le_add h₂ le_rfl)
  · -- `i < i' < j < j'`
    have hy := mem_Ioc.1 (optRoot_mem w (show i' < j by omega))
    have hz := mem_Ioc.1 (optRoot_mem w (show i < j' by omega))
    rw [optCost_eq_optRoot w (show i' < j by omega), optCost_eq_optRoot w (show i < j' by omega),
      splitCost, splitCost]
    generalize optRoot w i' j = y at hy ⊢
    generalize optRoot w i j' = z at hz ⊢
    rcases le_or_gt z y with hzy | hyz
    · have h₁ : optCost w i j ≤ w i j + (optCost w i (z - 1) + optCost w z j) :=
        optCost_le w (mem_Ioc.2 ⟨hz.1, by omega⟩)
      have h₂ : optCost w i' j' ≤ w i' j' + (optCost w i' (y - 1) + optCost w y j') :=
        optCost_le w (mem_Ioc.2 ⟨hy.1, by omega⟩)
      have h₃ := IH z y j j' (by omega) hzy hy.2 hjj'.le
      refine add4_le h₁ h₂ (hqi hii'.le hi'j.le hjj'.le) ?_
      calc optCost w i (z - 1) + optCost w z j + (optCost w i' (y - 1) + optCost w y j')
          = optCost w i (z - 1) + optCost w i' (y - 1) + (optCost w z j + optCost w y j') := by
            abel
        _ ≤ optCost w i (z - 1) + optCost w i' (y - 1) + (optCost w z j' + optCost w y j) :=
            add_le_add le_rfl h₃
        _ = optCost w i (z - 1) + optCost w z j' + (optCost w i' (y - 1) + optCost w y j) := by
            abel
    · have h₁ : optCost w i j ≤ w i j + (optCost w i (y - 1) + optCost w y j) :=
        optCost_le w (mem_Ioc.2 ⟨by omega, hy.2⟩)
      have h₂ : optCost w i' j' ≤ w i' j' + (optCost w i' (z - 1) + optCost w z j') :=
        optCost_le w (mem_Ioc.2 ⟨by omega, hz.2⟩)
      have h₃ := IH i i' (y - 1) (z - 1) (by omega) hii'.le (by omega) (by omega)
      refine add4_le h₁ h₂ (hqi hii'.le hi'j.le hjj'.le) ?_
      calc optCost w i (y - 1) + optCost w y j + (optCost w i' (z - 1) + optCost w z j')
          = optCost w i (y - 1) + optCost w i' (z - 1) + (optCost w y j + optCost w z j') := by
            abel
        _ ≤ optCost w i (z - 1) + optCost w i' (y - 1) + (optCost w y j + optCost w z j') :=
            add_le_add h₃ le_rfl
        _ = optCost w i (z - 1) + optCost w z j' + (optCost w i' (y - 1) + optCost w y j) := by
            abel

end Ordered

section Cancel

variable [IsOrderedCancelAddMonoid β]

private theorem cancel_aux {P Q V X Y Z : β} (h₁ : P + X ≤ Q + Y) (h₂ : Y + Z ≤ V + X) :
    P + Z ≤ Q + V := by
  have : (P + Z) + (X + Y) ≤ (Q + V) + (X + Y) :=
    calc (P + Z) + (X + Y) = (P + X) + (Y + Z) := by abel
      _ ≤ (Q + Y) + (V + X) := add_le_add h₁ h₂
      _ = (Q + V) + (X + Y) := by abel
  exact le_of_add_le_add_right this

/-- Root monotonicity in the right endpoint, `K(i, j) ≤ K(i, j + 1)`, for the largest optimal root
whenever the optimal cost satisfies the quadrangle inequality. -/
theorem optRoot_le_optRoot_add_one_right {w : ℕ → ℕ → β} (hc : QuadrangleIneq (optCost w))
    (i j : ℕ) : optRoot w i j ≤ optRoot w i (j + 1) := by
  rcases le_or_gt j i with hji | hij
  · rw [optRoot_of_le w hji]
    exact Nat.zero_le _
  have ha := mem_Ioc.1 (optRoot_mem w hij)
  have hb := mem_Ioc.1 (optRoot_mem w (show i < j + 1 by omega))
  refine not_lt.1 fun hlt => ?_
  -- `K(i, j)` would also be optimal for `(i, j + 1)`, contradicting maximality of `K(i, j + 1)`.
  have key : splitCost w i (j + 1) (optRoot w i j) ≤
      splitCost w i (j + 1) (optRoot w i (j + 1)) := by
    have h₁ := splitCost_optRoot_le w (i := i) (j := j) (k := optRoot w i (j + 1))
      (mem_Ioc.2 ⟨hb.1, by omega⟩)
    have h₂ := hc (i := optRoot w i (j + 1)) (i' := optRoot w i j) (j := j) (j' := j + 1)
      hlt.le ha.2 (Nat.le_succ j)
    simp only [splitCost] at h₁ ⊢
    exact cancel_aux h₁ h₂
  have := le_optRoot w (mem_Ioc.2 ⟨ha.1, by omega⟩)
    fun k hk => key.trans (splitCost_optRoot_le w hk)
  omega

/-- Root monotonicity in the left endpoint, `K(i, j + 1) ≤ K(i + 1, j + 1)` for `i < j`, for the
largest optimal root whenever the optimal cost satisfies the quadrangle inequality. -/
theorem optRoot_le_optRoot_add_one_left {w : ℕ → ℕ → β} (hc : QuadrangleIneq (optCost w))
    {i j : ℕ} (hij : i < j) : optRoot w i (j + 1) ≤ optRoot w (i + 1) (j + 1) := by
  have hb := mem_Ioc.1 (optRoot_mem w (show i < j + 1 by omega))
  have hb' := mem_Ioc.1 (optRoot_mem w (show i + 1 < j + 1 by omega))
  refine not_lt.1 fun hlt => ?_
  -- `K(i, j + 1)` would also be optimal for `(i + 1, j + 1)`, contradicting maximality of
  -- `K(i + 1, j + 1)`.
  have key : splitCost w (i + 1) (j + 1) (optRoot w i (j + 1)) ≤
      splitCost w (i + 1) (j + 1) (optRoot w (i + 1) (j + 1)) := by
    have h₁ := splitCost_optRoot_le w (i := i) (j := j + 1) (k := optRoot w (i + 1) (j + 1))
      (mem_Ioc.2 ⟨by omega, hb'.2⟩)
    have h₂ := hc (i := i) (i' := i + 1) (j := optRoot w (i + 1) (j + 1) - 1)
      (j' := optRoot w i (j + 1) - 1) (Nat.le_succ i) (by omega) (by omega)
    simp only [splitCost] at h₁ ⊢
    exact cancel_aux ((add_comm _ _).trans_le (h₂.trans_eq (add_comm _ _)))
      (h₁.trans_eq (add_comm _ _))
  have := le_optRoot w (mem_Ioc.2 ⟨by omega, hb.2⟩)
    fun k hk => key.trans (splitCost_optRoot_le w hk)
  omega

/-- **Monotonicity of optimal roots** (Knuth for binary search trees, Yao in general): under the
quadrangle inequality and interval monotonicity of `w`, the largest optimal roots satisfy
`K(i, j - 1) ≤ K(i, j) ≤ K(i + 1, j)` for `i + 1 < j`. -/
theorem optRoot_mono {w : ℕ → ℕ → β} (hqi : QuadrangleIneq w) (hmono : MonotoneOnIntervals w)
    {i j : ℕ} (hij : i + 1 < j) :
    optRoot w i (j - 1) ≤ optRoot w i j ∧ optRoot w i j ≤ optRoot w (i + 1) j := by
  have hc := quadrangleIneq_optCost hqi hmono
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact ⟨optRoot_le_optRoot_add_one_right hc i j, optRoot_le_optRoot_add_one_left hc (by omega)⟩

end Cancel

end Yao

section KnuthWeight

variable [AddCommMonoid β]

/-- Knuth's weight satisfies the quadrangle inequality with equality. -/
theorem knuthWeight_add_knuthWeight (p q : ℕ → β) {i i' j j' : ℕ} (h₁ : i ≤ i') (h₂ : i' ≤ j)
    (h₃ : j ≤ j') :
    knuthWeight p q i j + knuthWeight p q i' j' = knuthWeight p q i j' + knuthWeight p q i' j := by
  have hp : ∑ k ∈ Ioc i j, p k + ∑ k ∈ Ioc i' j', p k =
      ∑ k ∈ Ioc i j', p k + ∑ k ∈ Ioc i' j, p k := by
    rw [← sum_Ioc_consecutive p h₁ (h₂.trans h₃), ← sum_Ioc_consecutive p h₂ h₃,
      ← sum_Ioc_consecutive p h₁ h₂]
    abel
  have hq : ∑ g ∈ Icc i j, q g + ∑ g ∈ Icc i' j', q g =
      ∑ g ∈ Icc i j', q g + ∑ g ∈ Icc i' j, q g := by
    simp only [← Ico_add_one_right_eq_Icc]
    rw [← sum_Ico_consecutive q h₁ (by omega : i' ≤ j' + 1),
      ← sum_Ico_consecutive q (by omega : i' ≤ j + 1) (by omega : j + 1 ≤ j' + 1),
      ← sum_Ico_consecutive q h₁ (by omega : i' ≤ j + 1)]
    abel
  simp only [knuthWeight]
  calc ∑ k ∈ Ioc i j, p k + ∑ g ∈ Icc i j, q g + (∑ k ∈ Ioc i' j', p k + ∑ g ∈ Icc i' j', q g)
      = (∑ k ∈ Ioc i j, p k + ∑ k ∈ Ioc i' j', p k) +
          (∑ g ∈ Icc i j, q g + ∑ g ∈ Icc i' j', q g) := by abel
    _ = (∑ k ∈ Ioc i j', p k + ∑ k ∈ Ioc i' j, p k) +
          (∑ g ∈ Icc i j', q g + ∑ g ∈ Icc i' j, q g) := by rw [hp, hq]
    _ = _ := by abel

variable [PartialOrder β]

theorem quadrangleIneq_knuthWeight (p q : ℕ → β) : QuadrangleIneq (knuthWeight p q) :=
  fun _ _ _ _ h₁ h₂ h₃ => (knuthWeight_add_knuthWeight p q h₁ h₂ h₃).le

variable [IsOrderedAddMonoid β]

/-- With nonnegative access and failure weights, Knuth's weight is monotone on intervals. -/
theorem monotoneOnIntervals_knuthWeight {p q : ℕ → β} (hp : ∀ k, 0 ≤ p k) (hq : ∀ g, 0 ≤ q g) :
    MonotoneOnIntervals (knuthWeight p q) := by
  intro i i' j j' h₁ _ h₃
  exact add_le_add (sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc h₁ h₃) fun k _ _ => hp k)
    (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc h₁ h₃) fun g _ _ => hq g)

end KnuthWeight

end Cslib.Algorithms.Lean.OptimalBST
