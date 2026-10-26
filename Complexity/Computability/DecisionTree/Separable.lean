/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Leaves
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Data.Finset.Quantile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Large rectangles in separable and bi-monotone comparison trees

A separable comparison tests whether the sum of one score from each side meets a threshold.
More generally, a bi-monotone comparison combines one real score from each side using a Boolean
kernel that is monotone in each score separately. The scores may be arbitrary real-valued
functions; neither distinct scores nor linearity is required. Every nonempty finite product domain
contains a rectangle routed to one leaf whose sides lose at most the structural leaf count of the
tree.

## Main definitions

* `Cslib.BiMonotoneComparison`: a comparison whose Boolean kernel is monotone in each real score
  separately.
* `Cslib.BiMonotoneComparison.ofMax`, `Cslib.BiMonotoneComparison.ofMin`: threshold comparisons of
  the maximum and minimum of two scores.
* `Cslib.SeparableComparison`: a threshold comparison of the sum of two separate scores.

## Main results

* `Cslib.BiMonotoneComparison.exists_rectangle`, `Cslib.SeparableComparison.exists_rectangle`:
  the finite quantile alternative.
* `Cslib.DecisionTree.exists_leaf_rectangle_biMonotone`,
  `Cslib.DecisionTree.exists_leaf_rectangle`: a rectangle reaches one leaf, with side losses
  bounded by the number of leaves.
* `Cslib.DecisionTree.card_mul_le_mul_leafCount_sq_biMonotone`,
  `Cslib.DecisionTree.card_mul_le_mul_leafCount_sq`: a monochromatic-area bound forces many leaves.

## References

* [*Threshold Circuits as Decision Trees and Finite-State Programs*, Lemma 2.1, Theorem 2.2, and
  Theorem 2.6][ThresholdCircuitRepresentations2026]
-/

@[expose] public section

namespace Cslib

/-- A bi-monotone comparison applies a Boolean combiner that is monotone in each real score
separately. Queries with a nonincreasing score direction are represented by negating that
score. -/
structure BiMonotoneComparison (X Y : Type*) where
  /-- The left score. -/
  left : X → ℝ
  /-- The right score. -/
  right : Y → ℝ
  /-- The Boolean combiner of the two scores. -/
  kernel : ℝ → ℝ → Bool
  /-- The combiner is monotone in the left score for each fixed right score. -/
  monotone_left : ∀ b, Monotone (fun a => kernel a b)
  /-- The combiner is monotone in the right score for each fixed left score. -/
  monotone_right : ∀ a, Monotone (fun b => kernel a b)

namespace BiMonotoneComparison

variable {X Y : Type*}

/-- The answer to a bi-monotone comparison. -/
def eval (q : BiMonotoneComparison X Y) (x : X) (y : Y) : Bool :=
  q.kernel (q.left x) (q.right y)

/-- Compare the maximum of two scores against a threshold: the disjunction of one left-only and
one right-only threshold. -/
noncomputable def ofMax (left : X → ℝ) (right : Y → ℝ) (threshold : ℝ) :
    BiMonotoneComparison X Y where
  left := left
  right := right
  kernel a b := decide (threshold ≤ max a b)
  monotone_left b a₁ a₂ ha := by
    by_cases h : threshold ≤ max a₁ b <;>
      simp [h, fun h : threshold ≤ max a₁ b => h.trans (max_le_max_right b ha)]
  monotone_right a b₁ b₂ hb := by
    by_cases h : threshold ≤ max a b₁ <;>
      simp [h, fun h : threshold ≤ max a b₁ => h.trans (max_le_max_left a hb)]

@[simp]
theorem eval_ofMax (left : X → ℝ) (right : Y → ℝ) (threshold : ℝ) (x : X) (y : Y) :
    (ofMax left right threshold).eval x y = decide (threshold ≤ max (left x) (right y)) :=
  rfl

/-- Compare the minimum of two scores against a threshold: the conjunction of one left-only and
one right-only threshold. -/
noncomputable def ofMin (left : X → ℝ) (right : Y → ℝ) (threshold : ℝ) :
    BiMonotoneComparison X Y where
  left := left
  right := right
  kernel a b := decide (threshold ≤ min a b)
  monotone_left b a₁ a₂ ha := by
    by_cases h : threshold ≤ min a₁ b <;>
      simp [h, fun h : threshold ≤ min a₁ b => h.trans (min_le_min_right b ha)]
  monotone_right a b₁ b₂ hb := by
    by_cases h : threshold ≤ min a b₁ <;>
      simp [h, fun h : threshold ≤ min a b₁ => h.trans (min_le_min_left a hb)]

@[simp]
theorem eval_ofMin (left : X → ℝ) (right : Y → ℝ) (threshold : ℝ) (x : X) (y : Y) :
    (ofMin left right threshold).eval x y = decide (threshold ≤ min (left x) (right y)) :=
  rfl

/-- Either the false branch retains proportion `a` on both sides, or the true branch retains
proportion `1 - a` on both sides. The selected sides are nonempty, including when scores tie. -/
theorem exists_rectangle (q : BiMonotoneComparison X Y) (A : Finset X) (B : Finset Y)
    (hA : A.Nonempty) (hB : B.Nonempty) {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ (b : Bool) (A' : Finset X) (B' : Finset Y), A' ⊆ A ∧ B' ⊆ B ∧
      A'.Nonempty ∧ B'.Nonempty ∧
      (if b then 1 - a else a) * A.card ≤ (A'.card : ℝ) ∧
      (if b then 1 - a else a) * B.card ≤ (B'.card : ℝ) ∧
      ∀ x ∈ A', ∀ y ∈ B', q.eval x y = b := by
  classical
  obtain ⟨x₀, hx₀, hxlo, hxhi⟩ := A.exists_quantile hA q.left ha ha₁
  obtain ⟨y₀, hy₀, hylo, hyhi⟩ := B.exists_quantile hB q.right ha ha₁
  cases hq : q.eval x₀ y₀
  · refine ⟨false, A.filter (fun x => q.left x ≤ q.left x₀),
      B.filter (fun y => q.right y ≤ q.right y₀), Finset.filter_subset _ _,
      Finset.filter_subset _ _, ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, le_rfl⟩⟩,
      ⟨y₀, Finset.mem_filter.mpr ⟨hy₀, le_rfl⟩⟩, hxlo, hylo, ?_⟩
    intro x hx y hy
    have hle : q.eval x y ≤ q.eval x₀ y₀ :=
      (q.monotone_left (q.right y) (Finset.mem_filter.mp hx).2).trans
        (q.monotone_right (q.left x₀) (Finset.mem_filter.mp hy).2)
    exact le_antisymm (hq ▸ hle) (Bool.false_le _)
  · refine ⟨true, A.filter (fun x => q.left x₀ ≤ q.left x),
      B.filter (fun y => q.right y₀ ≤ q.right y), Finset.filter_subset _ _,
      Finset.filter_subset _ _, ⟨x₀, Finset.mem_filter.mpr ⟨hx₀, le_rfl⟩⟩,
      ⟨y₀, Finset.mem_filter.mpr ⟨hy₀, le_rfl⟩⟩, hxhi, hyhi, ?_⟩
    intro x hx y hy
    have hge : q.eval x₀ y₀ ≤ q.eval x y :=
      (q.monotone_left (q.right y₀) (Finset.mem_filter.mp hx).2).trans
        (q.monotone_right (q.left x) (Finset.mem_filter.mp hy).2)
    exact le_antisymm (Bool.le_true _) (hq ▸ hge)

end BiMonotoneComparison

/-- A comparison of the sum of two independent scores against a threshold. -/
structure SeparableComparison (X Y : Type*) where
  /-- The left score. -/
  left : X → ℝ
  /-- The right score. -/
  right : Y → ℝ
  /-- Equality at this threshold takes the `true` branch. -/
  threshold : ℝ

namespace SeparableComparison

variable {X Y : Type*}

/-- The answer to a separable comparison. -/
noncomputable def eval (q : SeparableComparison X Y) (x : X) (y : Y) : Bool :=
  decide (q.threshold ≤ q.left x + q.right y)

/-- Every separable comparison is a bi-monotone comparison with additive threshold kernel. -/
noncomputable def toBiMonotone (q : SeparableComparison X Y) : BiMonotoneComparison X Y where
  left := q.left
  right := q.right
  kernel a b := decide (q.threshold ≤ a + b)
  monotone_left b a₁ a₂ ha := by
    by_cases h : q.threshold ≤ a₁ + b <;>
      simp [h, fun h : q.threshold ≤ a₁ + b => h.trans (add_le_add_left ha b)]
  monotone_right a b₁ b₂ hb := by
    by_cases h : q.threshold ≤ a + b₁ <;>
      simp [h, fun h : q.threshold ≤ a + b₁ => h.trans (add_le_add_right hb a)]

@[simp]
theorem eval_toBiMonotone (q : SeparableComparison X Y) (x : X) (y : Y) :
    q.toBiMonotone.eval x y = q.eval x y :=
  rfl

/-- Either the false branch retains proportion `a` on both sides, or the true branch retains
proportion `1 - a` on both sides. The selected sides are nonempty, including when scores tie. -/
theorem exists_rectangle (q : SeparableComparison X Y) (A : Finset X) (B : Finset Y)
    (hA : A.Nonempty) (hB : B.Nonempty) {a : ℝ} (ha : 0 ≤ a) (ha₁ : a ≤ 1) :
    ∃ (b : Bool) (A' : Finset X) (B' : Finset Y), A' ⊆ A ∧ B' ⊆ B ∧
      A'.Nonempty ∧ B'.Nonempty ∧
      (if b then 1 - a else a) * A.card ≤ (A'.card : ℝ) ∧
      (if b then 1 - a else a) * B.card ≤ (B'.card : ℝ) ∧
      ∀ x ∈ A', ∀ y ∈ B', q.eval x y = b :=
  q.toBiMonotone.exists_rectangle A B hA hB ha ha₁

end SeparableComparison

namespace DecisionTree

variable {X Y β : Type*}

/-- Clearing denominators: if `(c / d) * n ≤ m` and `m ≤ k * c` for positive `c, d`, then
`n ≤ k * d`. -/
private theorem le_mul_of_div_mul_le {n m k c d : ℕ} (hc : 0 < c) (hd : 0 < d)
    (h : (c : ℝ) / d * n ≤ m) (hk : m ≤ k * c) : n ≤ k * d := by
  have hcR : (0 : ℝ) < c := Nat.cast_pos.mpr hc
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  rw [div_mul_eq_mul_div, div_le_iff₀ hdR] at h
  have hkR : (m : ℝ) ≤ k * c := by exact_mod_cast hk
  have : (n : ℝ) ≤ k * d := by nlinarith
  exact_mod_cast this

/-- A nonempty product domain contains a rectangle reaching one leaf of a bi-monotone comparison
tree, with at most the leaf count lost from each side. The natural-number inequalities are the
division-free form of `|A'| ≥ |A| / L` and `|B'| ≥ |B| / L`. -/
theorem exists_leaf_rectangle_biMonotone (t : DecisionTree (BiMonotoneComparison X Y) β)
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (A' : Finset X) (B' : Finset Y) (p : List Bool), A' ⊆ A ∧ B' ⊆ B ∧
      A'.Nonempty ∧ B'.Nonempty ∧ A.card ≤ A'.card * t.leafCount ∧ B.card ≤ B'.card * t.leafCount ∧
      ∀ x ∈ A', ∀ y ∈ B', t.path (fun q => q.eval x y) = p := by
  classical
  induction t generalizing A B with
  | leaf b => exact ⟨A, B, [], fun _ h => h, fun _ h => h, hA, hB,
      by simp [leafCount], by simp [leafCount], fun _ _ _ _ => rfl⟩
  | node q left right ihl ihr =>
    have hl : (0 : ℝ) < left.leafCount := Nat.cast_pos.mpr left.leafCount_pos
    have hr : (0 : ℝ) < right.leafCount := Nat.cast_pos.mpr right.leafCount_pos
    have ht : (0 : ℝ) < left.leafCount + right.leafCount := add_pos hl hr
    let a : ℝ := left.leafCount / (left.leafCount + right.leafCount)
    have ha : 0 < a := div_pos hl ht
    have ha₁ : a < 1 := (div_lt_one ht).mpr (by linarith)
    obtain ⟨b, A₀, B₀, hA₀, hB₀, hA₀ne, hB₀ne, hAc, hBc, hquery⟩ :=
      q.exists_rectangle A B hA hB ha.le ha₁.le
    cases b with
    | false =>
      obtain ⟨A', B', p, hA', hB', hA'ne, hB'ne, hAl, hBl, hp⟩ := ihl A₀ B₀ hA₀ne hB₀ne
      refine ⟨A', B', false :: p, hA'.trans hA₀, hB'.trans hB₀, hA'ne, hB'ne,
        le_mul_of_div_mul_le left.leafCount_pos (Nat.add_pos_left left.leafCount_pos _) ?_ hAl,
        le_mul_of_div_mul_le left.leafCount_pos (Nat.add_pos_left left.leafCount_pos _) ?_ hBl, ?_⟩
      · simpa only [Bool.false_eq_true, ↓reduceIte, a, leafCount, Nat.cast_add] using hAc
      · simpa only [Bool.false_eq_true, ↓reduceIte, a, leafCount, Nat.cast_add] using hBc
      · intro x hx y hy
        simp only [path, hquery x (hA' hx) y (hB' hy), Bool.cond_false, hp x hx y hy]
    | true =>
      have heq : 1 - a = right.leafCount / (left.leafCount + right.leafCount : ℝ) := by
        dsimp only [a]
        field_simp
        ring
      obtain ⟨A', B', p, hA', hB', hA'ne, hB'ne, hAr, hBr, hp⟩ := ihr A₀ B₀ hA₀ne hB₀ne
      refine ⟨A', B', true :: p, hA'.trans hA₀, hB'.trans hB₀, hA'ne, hB'ne,
        le_mul_of_div_mul_le right.leafCount_pos (Nat.add_pos_left left.leafCount_pos _) ?_ hAr,
        le_mul_of_div_mul_le right.leafCount_pos (Nat.add_pos_left left.leafCount_pos _) ?_ hBr, ?_⟩
      · simpa only [↓reduceIte, heq, leafCount, Nat.cast_add] using hAc
      · simpa only [↓reduceIte, heq, leafCount, Nat.cast_add] using hBc
      · intro x hx y hy
        simp only [path, hquery x (hA' hx) y (hB' hy), Bool.cond_true, hp x hx y hy]

/-- A bound on monochromatic rectangle area forces a squared lower bound on the leaf count of a
bi-monotone comparison tree. This is the division-free form of `L ≥ √(|A| |B| / R)`. -/
theorem card_mul_le_mul_leafCount_sq_biMonotone (t : DecisionTree (BiMonotoneComparison X Y) β)
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (hB : B.Nonempty) {R : ℕ}
    (hR : ∀ (A' : Finset X), A' ⊆ A → ∀ (B' : Finset Y), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B', t.eval (fun q => q.eval x y) = z) → A'.card * B'.card ≤ R) :
    A.card * B.card ≤ R * t.leafCount ^ 2 := by
  obtain ⟨A', B', p, hA', hB', ⟨x₀, hx₀⟩, ⟨y₀, hy₀⟩, hAc, hBc, hp⟩ :=
    t.exists_leaf_rectangle_biMonotone A B hA hB
  have harea := hR A' hA' B' hB' (t.eval fun q => q.eval x₀ y₀) fun x hx y hy =>
    t.eval_eq_of_path_eq ((hp x hx y hy).trans (hp x₀ hx₀ y₀ hy₀).symm)
  calc A.card * B.card ≤ (A'.card * t.leafCount) * (B'.card * t.leafCount) :=
      Nat.mul_le_mul hAc hBc
    _ = (A'.card * B'.card) * t.leafCount ^ 2 := by ring
    _ ≤ R * t.leafCount ^ 2 := Nat.mul_le_mul_right _ harea

/-- A nonempty product domain contains a rectangle reaching one leaf, with at most the leaf
count lost from each side. The natural-number inequalities are the division-free form of
`|A'| ≥ |A| / L` and `|B'| ≥ |B| / L`. -/
theorem exists_leaf_rectangle (t : DecisionTree (SeparableComparison X Y) β)
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ (A' : Finset X) (B' : Finset Y) (p : List Bool), A' ⊆ A ∧ B' ⊆ B ∧
      A'.Nonempty ∧ B'.Nonempty ∧ A.card ≤ A'.card * t.leafCount ∧ B.card ≤ B'.card * t.leafCount ∧
      ∀ x ∈ A', ∀ y ∈ B', t.path (fun q => q.eval x y) = p := by
  simpa [Function.comp_def] using
    (t.mapQueries SeparableComparison.toBiMonotone).exists_leaf_rectangle_biMonotone A B hA hB

/-- A bound on monochromatic rectangle area forces a squared lower bound on the leaf count.
This is the division-free form of `L ≥ √(|A| |B| / R)`. -/
theorem card_mul_le_mul_leafCount_sq (t : DecisionTree (SeparableComparison X Y) β)
    (A : Finset X) (B : Finset Y) (hA : A.Nonempty) (hB : B.Nonempty) {R : ℕ}
    (hR : ∀ (A' : Finset X), A' ⊆ A → ∀ (B' : Finset Y), B' ⊆ B → ∀ z,
      (∀ x ∈ A', ∀ y ∈ B', t.eval (fun q => q.eval x y) = z) → A'.card * B'.card ≤ R) :
    A.card * B.card ≤ R * t.leafCount ^ 2 := by
  have h := (t.mapQueries SeparableComparison.toBiMonotone).card_mul_le_mul_leafCount_sq_biMonotone
    A B hA hB fun A' hA' B' hB' z hz => hR A' hA' B' hB' z fun x hx y hy => by
      simpa [Function.comp_def] using hz x hx y hy
  simpa using h

end DecisionTree

end Cslib
