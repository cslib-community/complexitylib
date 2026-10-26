/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Languages.Probabilistic.Semantics

/-!
# Extended-nonnegative-real expectation on `ProbComp`

Expected value `Cslib.ProbComp.expect m f = ∑' a, (eval m) a * f a` for a closed probabilistic
program `m : ProbComp α` and cost function `f : α → ℝ≥0∞`.

Working in `ℝ≥0∞` makes expectation total without `[Fintype α]`, `[MeasurableSpace α]`, or
summability hypotheses. Every `PMF` has countable support, while program state spaces such as
machine configurations with infinite memory `ℕ → ℕ` need not be finite or carry a measurable space.
Unbounded or faulting branches naturally evaluate to `⊤`.

## Main definitions

* `Cslib.ProbComp.expect`: `ℝ≥0∞`-valued expectation `∑' a, (eval m) a * f a` over `ProbComp`.

## Main results

* `Cslib.ProbComp.expect_pure`, `Cslib.ProbComp.expect_bind`, `Cslib.ProbComp.expect_map`:
  monadic laws for `expect` (return, tower/law of total expectation, and postprocessing).
* `Cslib.ProbComp.expect_const`, `Cslib.ProbComp.expect_add`, `Cslib.ProbComp.expect_mul_left`,
  `Cslib.ProbComp.expect_mul_right`: linearity over `ℝ≥0∞`.
* `Cslib.ProbComp.expect_congr_on_support`, `Cslib.ProbComp.expect_mono_on_support`,
  `Cslib.ProbComp.expect_eq_top_of_mem_support`: support-localized congruence, monotonicity, and
  divergence propagation.
* `Cslib.ProbComp.expect_unifFin`, `Cslib.ProbComp.expect_uniform`: uniform finite averages.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

open scoped ENNReal

namespace Cslib.ProbComp

variable {α β : Type}

/-- Expected value of `f : α → ℝ≥0∞` under a closed `ProbComp` computation. -/
noncomputable def expect (m : ProbComp α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, (eval m) a * f a

@[simp]
theorem expect_pure (a : α) (f : α → ℝ≥0∞) : expect (pure a) f = f a := by
  classical
  rw [expect, eval_pure, tsum_eq_single a]
  · simp
  · intro b hb
    simp [hb]

@[simp]
theorem expect_const (m : ProbComp α) (c : ℝ≥0∞) : expect m (fun _ => c) = c := by
  rw [expect, ENNReal.tsum_mul_right, (eval m).tsum_coe, one_mul]

theorem expect_zero (m : ProbComp α) : expect m (fun _ => 0) = 0 :=
  expect_const m 0

theorem expect_add (m : ProbComp α) (f g : α → ℝ≥0∞) :
    expect m (fun a => f a + g a) = expect m f + expect m g := by
  simp only [expect, mul_add, ENNReal.tsum_add]

theorem expect_mul_left (m : ProbComp α) (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
    expect m (fun a => c * f a) = c * expect m f := by
  rw [expect, expect, ← ENNReal.tsum_mul_left]
  congr 1
  funext a
  exact mul_left_comm ((eval m) a) c (f a)

theorem expect_mul_right (m : ProbComp α) (f : α → ℝ≥0∞) (c : ℝ≥0∞) :
    expect m (fun a => f a * c) = expect m f * c := by
  simp only [expect, ← mul_assoc, ENNReal.tsum_mul_right]

theorem expect_bind (m : ProbComp α) (k : α → ProbComp β) (f : β → ℝ≥0∞) :
    expect (m >>= k) f = expect m (fun a => expect (k a) f) := by
  simp only [expect, eval_bind, PMF.bind_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  congr 1
  funext a
  simp only [mul_assoc, ENNReal.tsum_mul_left]

theorem expect_map (g : α → β) (m : ProbComp α) (f : β → ℝ≥0∞) :
    expect (g <$> m) f = expect m (fun a => f (g a)) := by
  rw [← bind_pure_comp, expect_bind]
  simp only [expect_pure]

theorem expect_congr_on_support {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a = g a) : expect m f = expect m g := by
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ m.support
  · rw [h a ha]
  · have hzero : (eval m) a = 0 := (PMF.apply_eq_zero_iff (eval m) a).mpr (by
      rwa [support_eval])
    simp [hzero]

theorem expect_mono_on_support {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a ≤ g a) : expect m f ≤ expect m g := by
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ m.support
  · exact mul_le_mul_right (h a ha) _
  · have hzero : (eval m) a = 0 := (PMF.apply_eq_zero_iff (eval m) a).mpr (by
      rwa [support_eval])
    simp [hzero]

theorem expect_mono {m : ProbComp α} {f g : α → ℝ≥0∞}
    (h : ∀ a, f a ≤ g a) : expect m f ≤ expect m g :=
  expect_mono_on_support fun a _ => h a

theorem expect_le_of_forall_support {m : ProbComp α} {f : α → ℝ≥0∞} {B : ℝ≥0∞}
    (h : ∀ a ∈ m.support, f a ≤ B) : expect m f ≤ B :=
  (expect_mono_on_support h).trans_eq (expect_const m B)

theorem expect_eq_top_of_mem_support {m : ProbComp α} {f : α → ℝ≥0∞} {a : α}
    (ha : a ∈ m.support) (hf : f a = ⊤) : expect m f = ⊤ := by
  have hpos : (eval m) a ≠ 0 :=
    (PMF.mem_support_iff (eval m) a).mp (by rwa [support_eval])
  refine top_unique ?_
  calc
    (⊤ : ℝ≥0∞) = (eval m) a * f a := by rw [hf, ENNReal.mul_top hpos]
    _ ≤ expect m f := ENNReal.le_tsum (f := fun b => (eval m) b * f b) a

theorem expect_unifFin (n : ℕ) (f : Fin (n + 1) → ℝ≥0∞) :
    expect (unifFin n) f = (∑ k : Fin (n + 1), f k) / (n + 1 : ℝ≥0∞) := by
  rw [expect, eval_unifFin, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]
  simp

theorem expect_uniform [Fintype α] [Nonempty α] (f : α → ℝ≥0∞) :
    expect (uniform α) f = (∑ a : α, f a) / (Fintype.card α : ℝ≥0∞) := by
  rw [expect, eval_uniform, tsum_fintype]
  simp only [Probability.PMF.uniformOfFintype_apply]
  rw [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

end Cslib.ProbComp
