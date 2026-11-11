/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.AdaptivePolicy.Covariance
public import CslibFrontier.Probability.Divergence
import Mathlib.Tactic

/-!
# Information used by a Markov policy

[Aldridge2027], Definition 4.1 and Theorem 4.2 (PDF p. 4). Information is the
finite joint-versus-product KL sum in nats. The action span only uses states
and actions with positive marginal probability, and ignores state-only offsets.
The probability tables and backward values are those of `FiniteMDP`.

## Main results

* `FiniteMDP.information_bound`: the information bound with the per-state action span.
-/

public section
noncomputable section
open Finset
open scoped Cslib.Probability.PMF
namespace Cslib.Probability.AdaptivePolicy.FiniteMDP
variable {S A : Type*} [Fintype S] [Fintype A]
variable (M : FiniteMDP S A) (π : MarkovPolicy S A)

private def tablePMF {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) : _root_.PMF α :=
  _root_.PMF.ofFintype (fun x => ENNReal.ofReal (p x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x), hs, ENNReal.ofReal_one])

private theorem tablePMF_real {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x = 1) (x : α) :
    (tablePMF p hp hs x).toReal = p x := ENNReal.toReal_ofReal (hp x)

/-- Joint law of the state and action at a time, under the evaluated policy. -/
def jointLaw (t : ℕ) : _root_.PMF (S × A) :=
  tablePMF (fun z => M.stateLaw π t z.1 * π.prob t z.1 z.2)
    (fun z => mul_nonneg (M.stateLaw_nonneg π t z.1) (π.nonneg t z.1 z.2)) (by
      simp only [Fintype.sum_prod_type, ← mul_sum, π.sum_prob, mul_one, M.stateLaw_sum])

/-- Product of the original policy's state and action marginals. -/
def productLaw (t : ℕ) : _root_.PMF (S × A) :=
  tablePMF (fun z => M.stateLaw π t z.1 * (M.openLoop π).prob t z.1 z.2)
    (fun z => mul_nonneg (M.stateLaw_nonneg π t z.1) ((M.openLoop π).nonneg t z.1 z.2)) (by
      simp only [Fintype.sum_prod_type, ← mul_sum, MarkovPolicy.sum_prob, mul_one,
        M.stateLaw_sum])

/-- Real probability of a state/action pair under the policy. -/
theorem jointLaw_real (t : ℕ) (z : S × A) :
    (M.jointLaw π t z).toReal = M.stateLaw π t z.1 * π.prob t z.1 z.2 :=
  tablePMF_real _ _ _ _

/-- Real product-marginal probability of a state/action pair. -/
theorem productLaw_real (t : ℕ) (z : S × A) :
    (M.productLaw π t z).toReal =
      M.stateLaw π t z.1 * (∑ x, M.stateLaw π t x * π.prob t x z.2) :=
  tablePMF_real _ _ _ _

/-- Every policy-supported pair has positive product-marginal probability. -/
theorem jointLaw_support_subset_productLaw (t : ℕ) :
    (M.jointLaw π t).support ⊆ (M.productLaw π t).support := by
  intro z hz
  have hj : 0 < (M.jointLaw π t z).toReal :=
    ENNReal.toReal_pos (by simpa using hz) (_root_.PMF.apply_ne_top _ _)
  rw [M.jointLaw_real] at hj
  have hs : 0 < M.stateLaw π t z.1 :=
    lt_of_le_of_ne (M.stateLaw_nonneg π t _) (by
      intro h; rw [← h, zero_mul] at hj; exact (lt_irrefl 0 hj))
  have hm : 0 < ∑ x, M.stateLaw π t x * π.prob t x z.2 :=
    lt_of_lt_of_le hj (single_le_sum (fun x _ =>
      mul_nonneg (M.stateLaw_nonneg π t x) (π.nonneg t x z.2)) (mem_univ _))
  have hp : 0 < (M.productLaw π t z).toReal := by
    rw [M.productLaw_real]; exact mul_pos hs hm
  exact _root_.PMF.mem_support_iff _ _ |>.mpr (fun h => by simp [h] at hp)

/-- Mutual information between state and action, in nats. Zero-mass terms are zero. -/
@[expose] def mutualInformation (t : ℕ) : ℝ :=
  ∑ z, (M.jointLaw π t z).toReal *
    Real.log ((M.jointLaw π t z).toReal / (M.productLaw π t z).toReal)

/-- Mutual information is nonnegative, including degenerate laws. -/
theorem mutualInformation_nonneg (t : ℕ) : 0 ≤ M.mutualInformation π t :=
  PMF.sum_mul_log_div_nonneg (M.jointLaw_support_subset_productLaw π t)

private def supportedValues (t : ℕ) (q : S → A → ℝ) (s : S) : Finset ℝ :=
  (univ.filter fun a => 0 < ∑ x, M.stateLaw π t x * π.prob t x a).image (q s)

private theorem supportedValues_nonempty (t : ℕ) (q : S → A → ℝ) (s : S) :
    (M.supportedValues π t q s).Nonempty := by
  classical
  have hsum := (M.openLoop π).sum_prob t s
  have hex : ∃ a, 0 < (M.openLoop π).prob t s a := by
    by_contra h
    push Not at h
    have := sum_nonpos (fun a (_ : a ∈ (univ : Finset A)) => h a)
    linarith
  obtain ⟨a, ha⟩ := hex
  exact ⟨q s a, mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩⟩

/-- Largest supported per-state action range, as in Definition 4.1.
The inserted zero handles empty types and makes the definition total. -/
def actionSpan (t : ℕ) (q : S → A → ℝ) : ℝ :=
  (insert 0 ((univ.filter fun s => 0 < M.stateLaw π t s).image fun s =>
    (M.supportedValues π t q s).max' (M.supportedValues_nonempty π t q s) -
    (M.supportedValues π t q s).min' (M.supportedValues_nonempty π t q s))).max'
      (by simp)

/-- Action spans are nonnegative, including degenerate supported action sets. -/
theorem actionSpan_nonneg (t : ℕ) (q : S → A → ℝ) :
    0 ≤ M.actionSpan π t q := le_max' _ _ (mem_insert_self _ _)

private def midpoint (t : ℕ) (q : S → A → ℝ) (s : S) : ℝ :=
  ((M.supportedValues π t q s).max' (M.supportedValues_nonempty π t q s) +
    (M.supportedValues π t q s).min' (M.supportedValues_nonempty π t q s)) / 2

private theorem centered_bound (t : ℕ) (q : S → A → ℝ) (s : S) (a : A)
    (hs : 0 < M.stateLaw π t s)
    (ha : 0 < ∑ x, M.stateLaw π t x * π.prob t x a) :
    |q s a - M.midpoint π t q s| ≤ M.actionSpan π t q / 2 := by
  classical
  have hm : q s a ∈ M.supportedValues π t q s :=
    mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩
  have hlo := min'_le _ _ hm
  have hhi := le_max' _ _ hm
  have hr : (M.supportedValues π t q s).max' (M.supportedValues_nonempty π t q s) -
      (M.supportedValues π t q s).min' (M.supportedValues_nonempty π t q s) ≤
      M.actionSpan π t q := by
    apply le_max'
    exact mem_insert_of_mem (mem_image.mpr ⟨s, mem_filter.mpr ⟨mem_univ _, hs⟩, rfl⟩)
  rw [abs_le]
  unfold midpoint
  constructor <;> linarith

/-- Any score's covariance is bounded using its supported per-state action range.
This is the one-time change-of-measure step of Theorem 4.2. -/
theorem abs_traceCovariance_le_information (t : ℕ) (q : S → A → ℝ) :
    |M.traceCovariance π t q| ≤
      M.actionSpan π t q * Real.sqrt (M.mutualInformation π t / 2) := by
  classical
  let p := M.jointLaw π t
  let r := M.productLaw π t
  let f : S × A → ℝ := fun z =>
    if 0 < (r z).toReal then q z.1 z.2 - M.midpoint π t q z.1 else 0
  have hf : ∀ z, |f z| ≤ M.actionSpan π t q / 2 := by
    intro z
    dsimp only [f]
    split_ifs with hz
    · have hp := hz
      change 0 < (M.productLaw π t z).toReal at hp
      rw [M.productLaw_real] at hp
      have hs : 0 < M.stateLaw π t z.1 := by
        apply lt_of_le_of_ne (M.stateLaw_nonneg π t _)
        intro h
        rw [← h, zero_mul] at hp
        exact lt_irrefl 0 hp
      have ha : 0 < ∑ x, M.stateLaw π t x * π.prob t x z.2 := by
        apply lt_of_le_of_ne (sum_nonneg fun x _ =>
          mul_nonneg (M.stateLaw_nonneg π t _) (π.nonneg t _ _))
        intro h
        rw [← h, mul_zero] at hp
        exact lt_irrefl 0 hp
      exact M.centered_bound π t q _ _ hs ha
    · simpa only [abs_zero] using div_nonneg (M.actionSpan_nonneg π t q) (by norm_num : (0:ℝ) ≤ 2)
  have hpzero : ∀ z, ¬0 < (r z).toReal → (p z).toReal = 0 := by
    intro z hz
    have hr : r z = 0 := by
      exact ((ENNReal.toReal_eq_zero_iff (r z)).mp
        (le_antisymm (not_lt.mp hz) ENNReal.toReal_nonneg)).resolve_right
          (_root_.PMF.apply_ne_top _ _)
    have hp : p z = 0 := by
      by_contra hp
      exact M.jointLaw_support_subset_productLaw π t
        (by simpa only [_root_.PMF.mem_support_iff] using hp) hr
    simp [hp]
  have heq : M.traceCovariance π t q =
      (∑ z, (p z).toReal * f z) - ∑ z, (r z).toReal * f z := by
    rw [← M.traceCovariance_sub_state π t q (M.midpoint π t q),
      M.traceCovariance_eq_joint_sub_product]
    simp only [Fintype.sum_prod_type]
    congr 1
    · apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro a _
      let z : S × A := (s, a)
      rw [← M.jointLaw_real π t z]
      change (p z).toReal * (q z.1 z.2 - M.midpoint π t q z.1) = (p z).toReal * f z
      by_cases hz : 0 < (r z).toReal
      · simp only [f, hz, ite_true]
      · simp only [f, hz, ite_false, hpzero z hz, zero_mul]
    · apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro a _
      let z : S × A := (s, a)
      rw [← M.productLaw_real π t z]
      change (r z).toReal * (q z.1 z.2 - M.midpoint π t q z.1) = (r z).toReal * f z
      by_cases hz : 0 < (r z).toReal
      · simp only [f, hz, ite_true]
      · have hr : (r z).toReal = 0 :=
          le_antisymm (not_lt.mp hz) ENNReal.toReal_nonneg
        simp only [hr, zero_mul]
  have hpin : dist p r ≤ Real.sqrt (M.mutualInformation π t / 2) := by
    apply Real.le_sqrt_of_sq_le
    have h := PMF.two_mul_dist_sq_le_sum_mul_log_div (M.jointLaw_support_subset_productLaw π t)
    change 2 * dist p r ^ 2 ≤ M.mutualInformation π t at h
    linarith
  rw [heq]
  calc
    _ ≤ 2 * (M.actionSpan π t q / 2) * dist p r := PMF.abs_sum_mul_sub_le p r f hf
    _ = M.actionSpan π t q * dist p r := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpin (M.actionSpan_nonneg π t q)

/-- [Aldridge2027], Theorem 4.2: the exact finite-horizon information bound,
with support-sensitive per-state action spans and information in nats. -/
theorem information_bound (H : ℕ) :
    |M.totalCost π H - M.totalCost (M.openLoop π) H| ≤
      ∑ t ∈ range H, M.actionSpan π t (M.actionValue (M.openLoop π) H t) *
        Real.sqrt (M.mutualInformation π t / 2) := by
  rw [M.covariance_characterization]
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum fun t _ => M.abs_traceCovariance_le_information π t _)

/-- A supported range bound controls the exact action span. -/
theorem actionSpan_le {t : ℕ} {q : S → A → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hq : ∀ s a, 0 < M.stateLaw π t s →
      0 < ∑ x, M.stateLaw π t x * π.prob t x a → 0 ≤ q s a ∧ q s a ≤ B) :
    M.actionSpan π t q ≤ B := by
  classical
  apply max'_le
  intro y hy
  rcases mem_insert.mp hy with rfl | hy
  · exact hB
  obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
  have hstate := (mem_filter.mp hs).2
  have hmax := max'_mem (M.supportedValues π t q s) (M.supportedValues_nonempty π t q s)
  have hmin := min'_mem (M.supportedValues π t q s) (M.supportedValues_nonempty π t q s)
  obtain ⟨a, ha, hea⟩ := mem_image.mp hmax
  obtain ⟨b, hb, heb⟩ := mem_image.mp hmin
  have hqa := (hq s a hstate (mem_filter.mp ha).2).2
  have hqb := (hq s b hstate (mem_filter.mp hb).2).1
  linarith

/-- Every supported within-state action difference is bounded by the span. -/
theorem sub_le_actionSpan (t : ℕ) (q : S → A → ℝ) (s : S) (a b : A)
    (hs : 0 < M.stateLaw π t s)
    (ha : 0 < ∑ x, M.stateLaw π t x * π.prob t x a)
    (hb : 0 < ∑ x, M.stateLaw π t x * π.prob t x b) :
    q s a - q s b ≤ M.actionSpan π t q := by
  classical
  have ma : q s a ∈ M.supportedValues π t q s :=
    mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_univ _, ha⟩, rfl⟩
  have mb : q s b ∈ M.supportedValues π t q s :=
    mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hb⟩, rfl⟩
  have hi := le_max' _ _ ma
  have lo := min'_le _ _ mb
  have hr : (M.supportedValues π t q s).max' (M.supportedValues_nonempty π t q s) -
      (M.supportedValues π t q s).min' (M.supportedValues_nonempty π t q s) ≤
      M.actionSpan π t q := by
    apply le_max'
    exact mem_insert_of_mem (mem_image.mpr ⟨s, mem_filter.mpr ⟨mem_univ _, hs⟩, rfl⟩)
  linarith

/-- Unit immediate costs give the conventional remaining-horizon value bounds. -/
theorem value_unit_bounds (μ : MarkovPolicy S A)
    (hc : ∀ t s a, 0 ≤ M.cost t s a ∧ M.cost t s a ≤ 1)
    (n t : ℕ) (s : S) : 0 ≤ M.value μ n t s ∧ M.value μ n t s ≤ n := by
  induction n generalizing t s with
  | zero => simp [value]
  | succ n ih =>
    have hfuture (a : A) : 0 ≤ ∑ s', M.transition t s a s' * M.value μ n (t+1) s' :=
      sum_nonneg fun s' _ => mul_nonneg (M.transition_nonneg t s a s') (ih _ _).1
    have hupper (a : A) : (∑ s', M.transition t s a s' * M.value μ n (t+1) s') ≤ n := by
      calc
        _ ≤ ∑ s', M.transition t s a s' * n :=
          sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (ih _ _).2 (M.transition_nonneg t s a s')
        _ = n := by rw [← sum_mul, M.transition_sum, one_mul]
    constructor
    · exact sum_nonneg fun a _ => mul_nonneg (μ.nonneg t s a)
        (add_nonneg (hc t s a).1 (hfuture a))
    · calc
        _ ≤ ∑ a, μ.prob t s a * (1 + (n:ℝ)) := by
          apply sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (add_le_add (hc t s a).2 (hupper a)) (μ.nonneg t s a)
        _ = ↑(n+1) := by rw [← sum_mul, μ.sum_prob, one_mul]; push_cast; ring

/-- Unit costs bound action values by the remaining horizon. -/
theorem actionValue_unit_bounds (μ : MarkovPolicy S A)
    (hc : ∀ t s a, 0 ≤ M.cost t s a ∧ M.cost t s a ≤ 1)
    {H t : ℕ} (ht : t < H) (s : S) (a : A) :
    0 ≤ M.actionValue μ H t s a ∧ M.actionValue μ H t s a ≤ (H-t : ℕ) := by
  have hi := M.value_unit_bounds μ hc (H-(t+1)) (t+1)
  have hn : H-t = H-(t+1)+1 := by omega
  constructor
  · exact add_nonneg (hc t s a).1 (sum_nonneg fun s' _ =>
      mul_nonneg (M.transition_nonneg t s a s') (hi s').1)
  · calc
      _ ≤ 1 + ∑ s', M.transition t s a s' * (H-(t+1) : ℕ) :=
        add_le_add (hc t s a).2 (sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (hi s').2 (M.transition_nonneg t s a s'))
      _ = (H-t : ℕ) := by rw [← sum_mul, M.transition_sum, one_mul, hn]; push_cast; ring

end Cslib.Probability.AdaptivePolicy.FiniteMDP
