/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyEndpointNoise
public import Complexity.Foundations.Probability.RootMetric.Minkowski

/-!
# Removing bin counts from literal endpoint noise payments

The endpoint allowances below remain indexed by their actual positive budgets.
Minkowski sums their fourth roots before centering, retaining fine-bin decay and
charging exhausted endpoints zero. This replaces the bin-count cube in the finite
transport bound; it does not assert the missing uniform recursive salary.

The zero-numerator comparison isolates a failure of that particular count-based
sufficient envelope. Adding exhausted zero bins leaves the production magnitude
unchanged while its artificial count factor grows. It is not an estimator lower
bound or an obstruction to scalar own-request accuracy. The zero-bin extension
need not have a common horizon for every listed bin: only the actual positive
endpoints are used. Comparisons imposing that stronger horizon remain open.

## Main results

* `residualTransportedGroupInput_centered_minkowski_le`: count-free endpoint payment.
* `magnitude_eq_of_zero_binCap`: zero numerators cost no production magnitude.
* `exists_count_envelope_gt_allocator`: the count envelope can exceed the allocator.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Sum actual positive endpoint fourth-root allowances before taking the fourth
power. Both endpoints and the once-negative ray stay literal; there is no bin count.
An allowance is needed only at a positive endpoint, independently of execution. -/
theorem residualTransportedGroupInput_centered_minkowski_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (X Y : Environment P 3 → ZMod P → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] (hNu : 0 ≤ (P : ℝ) * r.source.rate)
    (den : Matrix (ZMod P) (ZMod P) ℝ) (e : ℕ → Option ℕ → ℝ)
    (he0 : ∀ m bin, 0 ≤ e m bin)
    (he : ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => (B.sample history m .residual r bin).getD 0 σ x y -
          B.residualCanonicalRay r bin σ x y) ≤ e m bin ^ 4) :
    rowNormPow 4 P r.source.rate X Y (fun σ x y =>
      (B.residualTransportedGroupInput history M d r σ x y -
        rowSliceMean X Y (B.residualTransportedGroupInput history M d r) x y) / den x y) ≤
      16 * ‖fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹‖ ^ 4 *
        (∑ bin ∈ insert none (B.bins.image some),
          ((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) = 0 then 0
            else e (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) bin) +
          (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) = 0
            then 0 else e (LogSpaceEstimation.lastBudget M (2 * d) B.slack
              (B.sampleScale r bin)) bin))) ^ 4 := by
  let S := insert none (B.bins.image some)
  let E := fun m bin σ x y => (B.sample history m .residual r bin).getD 0 σ x y -
    (if m = 0 then 0 else B.residualCanonicalRay r bin σ x y)
  let a := fun m bin => if m = 0 then 0 else e m bin
  let f := fun bin => LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
  let c := fun bin => LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  have hS (bin : Option ℕ) : bin ∈ S ↔ bin ∈ B.rays .residual := by
    simp only [S, rays, mem_insert, mem_image, List.mem_append, List.mem_map,
      mem_toList, List.mem_singleton]
    exact or_comm
  have ha (m : ℕ) (bin : Option ℕ) : 0 ≤ a m bin := by
    dsimp only [a]; split_ifs <;> first | positivity | exact he0 _ _
  have hE (m : ℕ) (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y (E m bin) ≤ a m bin ^ 4 := by
    by_cases hm : m = 0
    · subst m; simp [E, a, B.sample_zero, rowNormPow]
    · simpa only [E, a, hm, ↓reduceIte] using he bin ((hS bin).mp hb) m (by omega)
  have hpair (bin : Option ℕ) (hb : bin ∈ S) :
      rowNormPow 4 P r.source.rate X Y
        (fun σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y) ≤
          (a (f bin) bin + a (c bin) bin) ^ 4 := by
    have h := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y
      (univ : Finset Bool)
      (fun b => if b then E (f bin) bin else -E (c bin) bin)
      (fun _ => 1) (fun b => if b then a (f bin) bin else a (c bin) bin)
      (by intros; norm_num) (by intro b _; cases b <;> exact ha _ _)
      (by
        intro b _; cases b
        · simpa only [Bool.false_eq_true, ↓reduceIte, rowNormPow, Pi.neg_apply, abs_neg]
            using hE (c bin) bin hb
        · exact hE (f bin) bin hb)
    simpa only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte, one_mul, Pi.neg_apply,
      sub_eq_add_neg, add_comm] using h
  have hsum (v : Option ℕ → ℝ) :
      ((B.rays .residual).map v).sum = ∑ bin ∈ S, v bin := by
    rw [show S = _ from rfl, sum_insert (by simp),
      sum_image (fun _ _ _ _ h => Option.some.inj h)]
    simp only [rays, List.map_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero, Function.comp_def]
    rw [sum_map_toList]; ring
  have hin : B.residualTransportedGroupInput history M d r =
      fun σ x y => ∑ bin ∈ S, (E (f bin) bin σ x y - E (c bin) bin σ x y) := by
    funext σ x y; exact hsum _
  have hi := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0) hNu Y S
    (fun bin σ x y => E (f bin) bin σ x y - E (c bin) bin σ x y)
    (fun _ => 1) (fun bin => a (f bin) bin + a (c bin) bin)
    (by intros; norm_num) (by intro bin _; exact add_nonneg (ha _ _) (ha _ _)) hpair
  simp only [one_mul] at hi
  rw [← hin] at hi
  have hc := rowNormPow_centered_sub_fourth_le hNu X Y
    (B.residualTransportedGroupInput history M d r) 0
  simp only [rowSliceMean, Pi.zero_apply, expect_const_zero, sub_zero] at hc
  have hw := rowNormPow_mul_le_pi_norm hNu X Y
    (fun σ x y => B.residualTransportedGroupInput history M d r σ x y -
      rowSliceMean X Y (B.residualTransportedGroupInput history M d r) x y)
    (fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹)
  simp only [div_eq_mul_inv]
  apply hw.trans
  have hh := mul_le_mul_of_nonneg_left (hc.trans
    (mul_le_mul_of_nonneg_left hi (by norm_num)))
    (show 0 ≤ ‖fun xy : ZMod P × ZMod P => (den xy.1 xy.2)⁻¹‖ ^ 4 by positivity)
  simpa only [rowSliceMean, a, f, c, S, mul_assoc, mul_comm, mul_left_comm] using hh

/-- With zero bin cap every positive charge vanishes, independently of how many
zero bins are listed. The negative ray and primitive correction cap are retained. -/
theorem magnitude_eq_of_zero_binCap
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hcap : B.binCap = 0) :
    B.magnitude r = 1 + B.atomCap + 2 * B.negativeMagnitude r := by
  simp [magnitude, positiveMagnitude, positiveCharge, hcap]

/-- The numerical count envelope is not bounded by the production coefficient over
arbitrary zero-bin extensions. This concerns the sufficient envelope only. Geometry,
positive endpoint availability, horizons and own-request IH must be checked separately
when applying it; it asserts no lower bound on actual transported noise. -/
theorem exists_count_envelope_gt_allocator
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (hcap : B.binCap = 0)
    (offset : ℕ) (v : ℝ) (hv : 0 < v) :
    ∃ n : ℕ, 32 * ((P : ℝ) ^ 2 / (P * r.source.rate) *
        ({B with bins := (range n).image (fun i => i + offset)}).magnitude r ^ 4) <
      128 * ((n : ℝ) + 1) ^ 3 * v := by
  have hm (n : ℕ) :
      ({B with bins := (range n).image (fun i => i + offset)}).magnitude r =
        B.magnitude r := by
    rw [B.magnitude_eq_of_zero_binCap r hcap,
      magnitude_eq_of_zero_binCap {B with bins := (range n).image (fun i => i + offset)} r hcap]
    rfl
  obtain ⟨n, hn⟩ := exists_nat_gt
    (32 * ((P : ℝ) ^ 2 / (P * r.source.rate) * B.magnitude r ^ 4) / (128 * v))
  refine ⟨n, ?_⟩
  rw [hm]
  have hn' := (div_lt_iff₀ (by positivity : 0 < 128 * v)).mp hn
  have hh : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by
    have h : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (n : ℝ), mul_nonneg h (sq_nonneg (n : ℝ))]
  nlinarith [mul_le_mul_of_nonneg_right hh hv.le]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
