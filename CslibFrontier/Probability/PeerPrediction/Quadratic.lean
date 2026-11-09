/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Four-sample quadratic mutual information payments

[Kong2027], Section 7, Proposition 7.1, Lemma 7.2 and Theorem 7.3
(PDF pp. 18–19). Matrices are finite joint probability tables, with rows for
Alice and columns for Bob. Conditional reporting channels act on column vectors,
so Bob's channel acts by right multiplication with its transpose. Independent
samples are represented by nested finite expectations with the same joint table.
This is the source's finite probability-table convention, without conditionalizing
on possibly null signals. Own deviations are mixtures of a doubly stochastic
channel and a signal-independent report. General stochastic-channel DPI and the
paper's rigidity results are outside this module.

## Main results

* `payment_unbiased`: the four independent samples estimate QMI exactly.
* `centered_mixed`, `qmi_mixed_le`: the centered-table identity and contraction.
* `truthful_alice`, `truthful_bob`: dominance against the restricted own deviations.
* `truthful_reward`: zero expected reward exactly at independence.
-/

public section
noncomputable section
open Finset Matrix
namespace Cslib.Probability.PeerPrediction.Quadratic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

/-- Row marginal of a finite joint table. -/
@[expose] def rowMarginal (U : Matrix α β ℝ) (i : α) : ℝ := ∑ j, U i j
/-- Column marginal of a finite joint table. -/
@[expose] def colMarginal (U : Matrix α β ℝ) (j : β) : ℝ := ∑ i, U i j
/-- A probability table: nonnegative entries of total mass one. -/
@[expose] def IsJoint (U : Matrix α β ℝ) : Prop :=
  (∀ i j, 0 ≤ U i j) ∧ (∑ i, rowMarginal U i) = 1
/-- The centered joint table vanishes exactly when the table factors into its marginals. -/
@[expose] def centered (U : Matrix α β ℝ) (i : α) (j : β) : ℝ :=
  U i j - rowMarginal U i * colMarginal U j
/-- Quadratic mutual information, equation (7). -/
@[expose] def qmi (U : Matrix α β ℝ) : ℝ := ∑ i, ∑ j, centered U i j ^ 2
/-- Independence in the finite joint-table model. -/
@[expose] def Independent (U : Matrix α β ℝ) : Prop :=
  ∀ i j, U i j = rowMarginal U i * colMarginal U j

omit [DecidableEq α] [DecidableEq β] in
theorem qmi_nonneg (U : Matrix α β ℝ) : 0 ≤ qmi U :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq α] [DecidableEq β] in
theorem qmi_eq_zero_iff (U : Matrix α β ℝ) : qmi U = 0 ↔ Independent U := by
  unfold qmi
  constructor
  · intro h i j
    have hi := (sum_eq_zero_iff_of_nonneg (fun i _ =>
      sum_nonneg (fun j _ => sq_nonneg (centered U i j)))).mp h i (mem_univ i)
    have hij := (sum_eq_zero_iff_of_nonneg (fun j _ =>
      sq_nonneg (centered U i j))).mp hi j (mem_univ j)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hij)
  · intro h
    exact sum_eq_zero fun i _ => sum_eq_zero fun j _ => by
      rw [centered, h i j, sub_self, zero_pow (by decide : 2 ≠ 0)]

/-- Expectation of a function of one pair under the joint table. -/
def expect (U : Matrix α β ℝ) (f : α × β → ℝ) : ℝ := ∑ i, ∑ j, U i j * f (i, j)
/-- Four independent tasks with the same report distribution. -/
def expectFour (U : Matrix α β ℝ) (f : (α × β) → (α × β) → (α × β) → (α × β) → ℝ) : ℝ :=
  expect U fun z₁ => expect U fun z₂ => expect U fun z₃ => expect U fun z₄ => f z₁ z₂ z₃ z₄
/-- The common equality-only payment, equation (8). -/
@[expose] def payment (z₁ z₂ z₃ z₄ : α × β) : ℝ :=
  (if z₁ = z₂ then 1 else 0) -
    2 * (if z₁.1 = z₂.1 ∧ z₁.2 = z₃.2 then 1 else 0) +
    (if z₁.1 = z₂.1 ∧ z₃.2 = z₄.2 then 1 else 0)

omit [DecidableEq α] [DecidableEq β] in
private theorem expect_const {U : Matrix α β ℝ} (hU : IsJoint U) (a : ℝ) :
    expect U (fun _ => a) = a := by
  simp only [expect, ← sum_mul]
  change (∑ i, rowMarginal U i) * a = a
  rw [hU.2, one_mul]

omit [DecidableEq α] [DecidableEq β] in
private theorem expect_add (U : Matrix α β ℝ) (f g : α × β → ℝ) :
    expect U (fun z => f z + g z) = expect U f + expect U g := by
  simp [expect, mul_add, sum_add_distrib]

omit [DecidableEq α] [DecidableEq β] in
private theorem expect_sub (U : Matrix α β ℝ) (f g : α × β → ℝ) :
    expect U (fun z => f z - g z) = expect U f - expect U g := by
  simp [expect, mul_sub, sum_sub_distrib]

omit [DecidableEq α] [DecidableEq β] in
private theorem expect_smul (U : Matrix α β ℝ) (a : ℝ) (f : α × β → ℝ) :
    expect U (fun z => a * f z) = a * expect U f := by
  simp only [expect, mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  ring

private theorem expect_eq (U : Matrix α β ℝ) (z : α × β) :
    expect U (fun w => if z = w then 1 else 0) = U z.1 z.2 := by
  rcases z with ⟨x, y⟩
  simp [expect, Prod.mk.injEq, ite_and, mul_ite]

omit [DecidableEq β] in
private theorem expect_fst (U : Matrix α β ℝ) (x : α) :
    expect U (fun w => if x = w.1 then 1 else 0) = rowMarginal U x := by
  simp [expect, mul_ite, rowMarginal]

omit [DecidableEq α] in
private theorem expect_snd (U : Matrix α β ℝ) (y : β) :
    expect U (fun w => if y = w.2 then 1 else 0) = colMarginal U y := by
  simp [expect, mul_ite, colMarginal]

/-- The three equality events have the collision moments given in Lemma 7.2. -/
theorem collision_moments {U : Matrix α β ℝ} (hU : IsJoint U) :
    expectFour U (fun a b _ _ => if a = b then 1 else 0) = (∑ i, ∑ j, U i j ^ 2) ∧
    expectFour U (fun a b c _ => if a.1 = b.1 ∧ a.2 = c.2 then 1 else 0) =
      (∑ i, ∑ j, U i j * rowMarginal U i * colMarginal U j) ∧
    expectFour U (fun a b c d => if a.1 = b.1 ∧ c.2 = d.2 then 1 else 0) =
      (∑ i, ∑ j, rowMarginal U i ^ 2 * colMarginal U j ^ 2) := by
  constructor
  · simp only [expectFour, expect_const hU, expect_eq]
    simp only [expect, sq]
  constructor
  · simp only [expectFour, expect_const hU]
    have h (a b : α × β) :
        expect U (fun c => if a.1 = b.1 ∧ a.2 = c.2 then 1 else 0) =
          (if a.1 = b.1 then colMarginal U a.2 else 0) := by
      by_cases hab : a.1 = b.1 <;>
        simp only [hab, true_and, ite_true, false_and, ite_false, expect_snd]
      all_goals simp [expect]
    simp only [h]
    have h' (a : α × β) :
        expect U (fun b => if a.1 = b.1 then colMarginal U a.2 else 0) =
          colMarginal U a.2 * rowMarginal U a.1 := by
      rw [show (fun b : α × β => if a.1 = b.1 then colMarginal U a.2 else 0) =
        (fun b => colMarginal U a.2 * (if a.1 = b.1 then 1 else 0)) by ext b; split <;> simp_all]
      rw [expect_smul, expect_fst]
    simp only [h']
    unfold expect
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    ring
  · have h (a b c : α × β) :
        expect U (fun d => if a.1 = b.1 ∧ c.2 = d.2 then 1 else 0) =
          (if a.1 = b.1 then colMarginal U c.2 else 0) := by
      by_cases hab : a.1 = b.1 <;>
        simp only [hab, true_and, ite_true, false_and, ite_false, expect_snd]
      all_goals simp [expect]
    simp only [expectFour, h]
    have h' (a b : α × β) :
        expect U (fun c => if a.1 = b.1 then colMarginal U c.2 else 0) =
          (if a.1 = b.1 then expect U (fun c => colMarginal U c.2) else 0) := by
      by_cases hab : a.1 = b.1 <;> simp [hab, expect]
    simp only [h']
    have h'' (a : α × β) (v : ℝ) :
        expect U (fun b => if a.1 = b.1 then v else 0) = v * rowMarginal U a.1 := by
      rw [show (fun b : α × β => if a.1 = b.1 then v else 0) =
        (fun b => v * (if a.1 = b.1 then 1 else 0)) by ext b; split <;> simp_all]
      rw [expect_smul, expect_fst]
    simp only [h'', expect_smul]
    have hr : expect U (fun a => rowMarginal U a.1) = ∑ i, rowMarginal U i ^ 2 := by
      simp only [expect, ← sum_mul, rowMarginal, sq]
    have hc : expect U (fun a => colMarginal U a.2) = ∑ j, colMarginal U j ^ 2 := by
      unfold expect
      rw [sum_comm]
      simp only [← sum_mul, colMarginal, sq]
    rw [hr, hc]
    simp only [mul_sum, sum_mul]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro j _
    ring

/-- The actual four-task equality-only payment is unbiased for QMI. -/
theorem payment_unbiased {U : Matrix α β ℝ} (hU : IsJoint U) :
    expectFour U payment = qmi U := by
  obtain ⟨h₁, h₂, h₃⟩ := collision_moments hU
  have hlin : expectFour U payment =
      expectFour U (fun a b _ _ => if a = b then 1 else 0) -
      2 * expectFour U (fun a b c _ => if a.1 = b.1 ∧ a.2 = c.2 then 1 else 0) +
      expectFour U (fun a b c d => if a.1 = b.1 ∧ c.2 = d.2 then 1 else 0) := by
    simp only [expectFour, payment, expect_add, expect_sub, expect_smul]
  rw [hlin, h₁, h₂, h₃]
  simp only [qmi, centered, mul_sum]
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  rw [← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  ring


omit [Fintype β] [DecidableEq β] in
/-- Left processing preserves the column marginal. -/
theorem col_processed (T : Matrix α α ℝ) (hT : T ∈ colStochastic ℝ α)
    (U : Matrix α β ℝ) (j : β) : colMarginal (T * U) j = colMarginal U j := by
  simp only [colMarginal, Matrix.mul_apply]
  rw [sum_comm]
  simp only [← sum_mul, sum_col_of_mem_colStochastic hT, one_mul]

omit [DecidableEq α] [DecidableEq β] in
/-- Left processing applies the conditional channel to the row marginal. -/
theorem row_processed (T : Matrix α α ℝ) (U : Matrix α β ℝ) (i : α) :
    rowMarginal (T * U) i = ∑ k, T i k * rowMarginal U k := by
  simp only [rowMarginal, Matrix.mul_apply]
  rw [sum_comm]
  simp only [mul_sum]

omit [DecidableEq β] in
/-- Processing by a memoryless conditional channel produces a probability table. -/
theorem IsJoint.process {U : Matrix α β ℝ} (hU : IsJoint U)
    (T : Matrix α α ℝ) (hT : T ∈ colStochastic ℝ α) : IsJoint (T * U) := by
  constructor
  · intro i j
    exact sum_nonneg fun k _ => mul_nonneg (nonneg_of_mem_colStochastic hT) (hU.1 k j)
  · simp only [row_processed]
    rw [sum_comm]
    simp only [← sum_mul, sum_col_of_mem_colStochastic hT, one_mul]
    exact hU.2

omit [DecidableEq α] [DecidableEq β] in
/-- Transposition swaps the two agents and preserves total mass. -/
theorem IsJoint.transpose {U : Matrix α β ℝ} (hU : IsJoint U) : IsJoint Uᵀ := by
  refine ⟨fun i j => hU.1 j i, ?_⟩
  simpa only [rowMarginal, Matrix.transpose_apply, sum_comm] using hU.2

omit [DecidableEq β] in
/-- The centered joint table transforms linearly under a conditional channel. -/
theorem centered_processed (T : Matrix α α ℝ) (hT : T ∈ colStochastic ℝ α)
    (U : Matrix α β ℝ) (i : α) (j : β) :
    centered (T * U) i j = ∑ k, T i k * centered U k j := by
  simp only [centered, col_processed T hT, row_processed, Matrix.mul_apply,
    mul_sub, sum_sub_distrib, sum_mul, mul_assoc]

omit [DecidableEq α] [DecidableEq β] in
/-- QMI is invariant under swapping the agents. -/
theorem qmi_transpose (U : Matrix α β ℝ) : qmi Uᵀ = qmi U := by
  simp only [qmi, centered, rowMarginal, colMarginal, Matrix.transpose_apply]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  rw [mul_comm]

/-- A signal-independent channel mixed with a doubly stochastic relabeling channel. -/
@[expose] def mixed (lam : ℝ) (D : Matrix α α ℝ) (q : α → ℝ) : Matrix α α ℝ :=
  fun i k => lam * D i k + (1 - lam) * q i

/-- The mixture is a valid memoryless conditional reporting channel. -/
theorem mixed_stochastic {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    {D : Matrix α α ℝ} (hD : D ∈ doublyStochastic ℝ α)
    {q : α → ℝ} (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∑ i, q i = 1) :
    mixed lam D q ∈ colStochastic ℝ α := by
  apply mem_colStochastic_iff_sum.mpr
  constructor
  · intro i k
    exact add_nonneg (mul_nonneg hl₀ (nonneg_of_mem_doublyStochastic hD))
      (mul_nonneg (sub_nonneg.mpr hl₁) (hq₀ i))
  · intro k
    simp only [mixed, sum_add_distrib, ← mul_sum, sum_col_of_mem_doublyStochastic hD,
      hq₁, mul_one]
    ring

omit [DecidableEq β] in
/-- The rank-one component annihilates the centered table: Proposition 7.1's identity. -/
theorem centered_mixed {U : Matrix α β ℝ} (hU : IsJoint U)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    {D : Matrix α α ℝ} (hD : D ∈ doublyStochastic ℝ α)
    {q : α → ℝ} (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∑ i, q i = 1) (i : α) (j : β) :
    centered (mixed lam D q * U) i j = lam * ∑ k, D i k * centered U k j := by
  rw [centered_processed _ (mixed_stochastic hl₀ hl₁ hD hq₀ hq₁)]
  have hz : ∑ k, centered U k j = 0 := by
    simp only [centered, sum_sub_distrib, ← sum_mul]
    change colMarginal U j - (∑ k, rowMarginal U k) * colMarginal U j = 0
    rw [hU.2, one_mul, sub_self]
  simp only [mixed, add_mul, sum_add_distrib, mul_assoc, ← mul_sum, hz, mul_zero, add_zero]

omit [DecidableEq β] in
/-- Frobenius contraction for the restricted channel, including its quantitative factor. -/
theorem qmi_mixed_le {U : Matrix α β ℝ} (hU : IsJoint U)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    {D : Matrix α α ℝ} (hD : D ∈ doublyStochastic ℝ α)
    {q : α → ℝ} (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∑ i, q i = 1) :
    qmi (mixed lam D q * U) ≤ lam ^ 2 * qmi U ∧ lam ^ 2 * qmi U ≤ qmi U := by
  have hj (i : α) (j : β) :
      (∑ k, D i k * centered U k j) ^ 2 ≤ ∑ k, D i k * centered U k j ^ 2 := by
    have h := sum_sq_le_sum_mul_sum_of_sq_le_mul univ
      (fun k _ => nonneg_of_mem_doublyStochastic hD (i := i) (j := k))
      (fun k _ => mul_nonneg (nonneg_of_mem_doublyStochastic hD (i := i) (j := k))
        (sq_nonneg (centered U k j)))
      (fun k _ => (by ring_nf; exact le_rfl : (D i k * centered U k j) ^ 2 ≤
        D i k * (D i k * centered U k j ^ 2)))
    simpa only [sum_row_of_mem_doublyStochastic hD, one_mul] using h
  constructor
  · calc
      qmi (mixed lam D q * U) = lam ^ 2 *
          ∑ i, ∑ j, (∑ k, D i k * centered U k j) ^ 2 := by
        simp only [qmi, centered_mixed hU hl₀ hl₁ hD hq₀ hq₁]
        simp only [mul_pow]
        simp only [mul_sum]
      _ ≤ lam ^ 2 * ∑ i, ∑ j, ∑ k, D i k * centered U k j ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => sum_le_sum fun j _ => hj i j)
          (sq_nonneg lam)
      _ = lam ^ 2 * qmi U := by
        congr 1
        rw [sum_comm]
        simp only [sum_comm (f := fun i k => D i k * centered U k _ ^ 2), ← sum_mul,
          sum_col_of_mem_doublyStochastic hD, one_mul]
        exact sum_comm
  · exact mul_le_of_le_one_left (qmi_nonneg U) (by nlinarith)

/-- Truthfulness against every fixed peer channel, relative to the specified own deviations.
The peer's channel is unrestricted within all memoryless column-stochastic channels. -/
theorem truthful_alice {P : Matrix α β ℝ} (hP : IsJoint P)
    (S : Matrix β β ℝ) (hS : S ∈ colStochastic ℝ β)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    {D : Matrix α α ℝ} (hD : D ∈ doublyStochastic ℝ α)
    {q : α → ℝ} (hq₀ : ∀ i, 0 ≤ q i) (hq₁ : ∑ i, q i = 1) :
    expectFour (mixed lam D q * (P * Sᵀ)) payment ≤ expectFour (P * Sᵀ) payment := by
  have hV : IsJoint (P * Sᵀ) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      ((hP.transpose.process S hS).transpose)
  rw [payment_unbiased (hV.process _ (mixed_stochastic hl₀ hl₁ hD hq₀ hq₁)),
    payment_unbiased hV]
  exact (qmi_mixed_le hV hl₀ hl₁ hD hq₀ hq₁).1.trans
    (qmi_mixed_le hV hl₀ hl₁ hD hq₀ hq₁).2

/-- The common truthful reward vanishes exactly at independence and is positive otherwise. -/
theorem truthful_reward {P : Matrix α β ℝ} (hP : IsJoint P) :
    (expectFour P payment = 0 ↔ Independent P) ∧
    (0 < expectFour P payment ↔ ¬ Independent P) := by
  rw [payment_unbiased hP]
  refine ⟨qmi_eq_zero_iff P, ?_⟩
  rw [lt_iff_le_and_ne]
  simp only [qmi_nonneg P, true_and, ne_eq, eq_comm (a := (0 : ℝ)), qmi_eq_zero_iff]

/-- Bob's symmetric guarantee, against every fixed Alice channel. -/
theorem truthful_bob {P : Matrix α β ℝ} (hP : IsJoint P)
    (T : Matrix α α ℝ) (hT : T ∈ colStochastic ℝ α)
    {lam : ℝ} (hl₀ : 0 ≤ lam) (hl₁ : lam ≤ 1)
    {D : Matrix β β ℝ} (hD : D ∈ doublyStochastic ℝ β)
    {q : β → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∑ j, q j = 1) :
    expectFour ((T * P) * (mixed lam D q)ᵀ) payment ≤ expectFour (T * P) payment := by
  have hV := hP.process T hT
  have hW : IsJoint ((T * P) * (mixed lam D q)ᵀ) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      (hV.transpose.process _ (mixed_stochastic hl₀ hl₁ hD hq₀ hq₁)).transpose
  rw [payment_unbiased hW, payment_unbiased hV]
  have h := qmi_mixed_le hV.transpose hl₀ hl₁ hD hq₀ hq₁
  have ht := h.1.trans h.2
  rw [← qmi_transpose ((T * P) * (mixed lam D q)ᵀ),
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simpa only [qmi_transpose] using ht

/-- Conditional reporting probabilities, summed over both latent signals. The two channels
use independent private randomness conditional on the signals. -/
def reportedLaw (P : Matrix α β ℝ) (T : Matrix α α ℝ) (S : Matrix β β ℝ) :
    Matrix α β ℝ := fun a b => ∑ i, ∑ j, P i j * T a i * S b j

omit [DecidableEq α] [DecidableEq β] in
/-- The experiment's conditional-channel semantics agrees with matrix processing. -/
theorem reportedLaw_eq (P : Matrix α β ℝ) (T : Matrix α α ℝ) (S : Matrix β β ℝ) :
    reportedLaw P T S = T * (P * Sᵀ) := by
  ext a b
  simp only [reportedLaw, Matrix.mul_apply, Matrix.transpose_apply, mul_sum]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  ring

/-- The conditional-report experiment is a genuine probability distribution. -/
theorem reportedLaw_isJoint {P : Matrix α β ℝ} (hP : IsJoint P)
    {T : Matrix α α ℝ} (hT : T ∈ colStochastic ℝ α)
    {S : Matrix β β ℝ} (hS : S ∈ colStochastic ℝ β) : IsJoint (reportedLaw P T S) := by
  rw [reportedLaw_eq]
  have hV : IsJoint (P * Sᵀ) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
      (hP.transpose.process S hS).transpose
  exact hV.process T hT

end Cslib.Probability.PeerPrediction.Quadratic
