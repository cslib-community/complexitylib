/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.UnsafeWitness
public import CslibFrontier.Computability.Communication.Lifting.DangerousParameters
import CslibFrontier.Foundations.Combinatorics.Subsets.Geometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Intrinsic ratio eligibility for unsafe parity witnesses

Choosing the integer order from a conditioning-slice ratio eliminates the order function from
the unsafe-witness theorem. Supported nonempty slices must have ratio at least `16 n²`; the
resulting witness satisfies the intrinsic upper bound by `n^(2|S|)`. The actual slice cardinality
is retained, so unusually rare conditioning assignments remain correctly accounted for.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {n m : ℕ}

/-- A large conditioning ratio chooses an admissible parity order and yields an intrinsic
eligible witness, without a supplied integer-order function. -/
theorem exists_ratio_parityTest_of_not_isSafe [NeZero m]
    (g : Fin m → Fin m → Bool) (σ : ℝ) (F : Finset (Fin n))
    (Y : Finset (Fin n → Fin m)) (hY : Y.Nonempty) (hn : 2 ≤ n) (hσ : 0 < σ)
    (hratio : ∀ J ⊆ F, J.Nonempty → ∀ α : Fin n → Fin m,
      (agreeOn Y J α).Nonempty →
        16 * (n : ℝ) ^ 2 ≤ (#Y : ℝ) / (σ ^ #J * #(agreeOn Y J α)))
    (x : Fin n → Fin m) (hunsafe : ¬ IsSafe g σ F Y x) :
    ∃ w : ParityTest F Y, w.IsCanonical ∧ w.parity.Nonempty ∧
      (w.conditioned = ∅ ∨ (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) *
        σ ^ w.conditioned.card * #(agreeOn Y w.conditioned w.assignment)) ∧
      (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card < w.bias g x := by
  classical
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let ratio (J : Finset (Fin n)) (a : J → Fin m) : ℝ :=
    (#Y : ℝ) / (σ ^ #J * #(agreeOn Y J (ParityTest.extendAssignment J a)))
  have hex : ∀ (J : Finset (Fin n)) (a : J → Fin m), ∃ t : ℕ,
      16 * (n : ℝ) ^ 2 ≤ ratio J a →
        1 ≤ t ∧ (n : ℝ) ^ t ≤ ratio J a / 4 ∧ ratio J a ≤ (n : ℝ) ^ (2 * t) := by
    intro J a
    by_cases hR : 16 * (n : ℝ) ^ 2 ≤ ratio J a
    · obtain ⟨t, ht⟩ := exists_power_threshold_of_ratio hnR hR
      exact ⟨t, fun _ => ht⟩
    · exact ⟨1, fun h => False.elim (hR h)⟩
  choose order hord using hex
  have hbudget : ∀ I ⊆ F, ∀ J ⊆ F \ I, J.Nonempty → ∀ a : J → Fin m,
      ∀ _hA : (agreeOn Y J (ParityTest.extendAssignment J a)).Nonempty,
      1 ≤ order J a ∧
        2 * (#{S : Finset I | S.card < order J a} + 1 : ℝ) * σ ^ #J *
          #(agreeOn Y J (ParityTest.extendAssignment J a)) ≤ #Y := by
    intro I hI J hJ hJne a hA
    have hJF : J ⊆ F := fun j hj => (mem_sdiff.mp (hJ hj)).1
    have hR := hratio J hJF hJne (ParityTest.extendAssignment J a) hA
    obtain ⟨ht, hupper, _⟩ := hord J a hR
    refine ⟨ht, ?_⟩
    have hcount : (#{S : Finset I | S.card < order J a} + 1 : ℝ) ≤ (n : ℝ) ^ order J a := by
      exact_mod_cast card_filter_card_lt_add_one_le_pow_of_card_le (α := I) hn
        (by simpa only [Fintype.card_coe, Fintype.card_fin] using card_le_univ I) (order J a)
    have hApos : (0 : ℝ) < #(agreeOn Y J (ParityTest.extendAssignment J a)) := by
      exact_mod_cast card_pos.mpr hA
    have hd : 0 < σ ^ #J * #(agreeOn Y J (ParityTest.extendAssignment J a)) := by positivity
    have hRnonneg : 0 ≤ ratio J a := by dsimp [ratio]; positivity
    have htwo : 2 * (#{S : Finset I | S.card < order J a} + 1 : ℝ) ≤ ratio J a := by
      linarith
    have hmul := (le_div_iff₀ hd).mp htwo
    simpa only [mul_assoc] using hmul
  obtain ⟨I, w, _, hcan, _, hPne, helig, hbias⟩ :=
    exists_parityTest_of_not_isSafe g σ F Y hY hσ.le (fun _ J a => order J a)
      hbudget x hunsafe
  refine ⟨w, hcan, hPne, ?_, hbias⟩
  rcases helig with he | ⟨hJne, _, horder⟩
  · exact Or.inl he
  · right
    let a := w.conditioned.restrict w.assignment
    have hA : (agreeOn Y w.conditioned (ParityTest.extendAssignment w.conditioned a)).Nonempty := by
      simpa only [a, ParityTest.agreeOn_extend_restrict] using w.supported
    have hR := hratio w.conditioned w.conditioned_subset hJne
      (ParityTest.extendAssignment w.conditioned a) hA
    have hpow := (hord w.conditioned a hR).2.2
    have hmono : (n : ℝ) ^ (2 * order w.conditioned a) ≤ (n : ℝ) ^ (2 * w.parity.card) :=
      pow_le_pow_right₀ (by linarith) (by dsimp [a]; omega)
    have hupper := hpow.trans hmono
    have hApos : (0 : ℝ) < #(agreeOn Y w.conditioned w.assignment) := by
      exact_mod_cast card_pos.mpr w.supported
    have hd : 0 < σ ^ w.conditioned.card * #(agreeOn Y w.conditioned w.assignment) := by positivity
    simp only [ratio, a, ParityTest.agreeOn_extend_restrict] at hupper
    have hmul := (div_le_iff₀ hd).mp hupper
    simpa only [mul_assoc] using hmul

/-- Joint density lower-bounds the true conditioning ratio. The cardinality of the supported
slice is not replaced by an average-case estimate. -/
theorem IsDense.le_conditioning_ratio {τ σ : ℝ} {F J : Finset (Fin n)}
    {Y : Finset (Fin n → Fin m)} (hY : IsDense τ F Y) (hσ : 0 < σ)
    (hJ : J ⊆ F) (hJne : J.Nonempty) (α : Fin n → Fin m)
    (hA : (agreeOn Y J α).Nonempty) :
    (τ / σ) ^ #J ≤ (#Y : ℝ) / (σ ^ #J * #(agreeOn Y J α)) := by
  have hApos : (0 : ℝ) < #(agreeOn Y J α) := by exact_mod_cast card_pos.mpr hA
  apply (le_div_iff₀ (by positivity : 0 < σ ^ #J * #(agreeOn Y J α))).mpr
  calc
    _ = (#(agreeOn Y J α) : ℝ) * τ ^ #J := by rw [div_pow]; field_simp
    _ ≤ #Y := hY J hJ hJne α

/-- Blockwise density and a multiplicative density gap supply the slice-ratio hypothesis.
Thus every unsafe value has an intrinsically eligible canonical parity witness. -/
theorem exists_ratio_parityTest_of_isDense_not_isSafe [NeZero m]
    (g : Fin m → Fin m → Bool) (τ σ : ℝ) (F : Finset (Fin n))
    (Y : Finset (Fin n → Fin m)) (hYne : Y.Nonempty) (hn : 2 ≤ n) (hσ : 0 < σ)
    (hY : IsDense τ F Y) (hgap : 16 * (n : ℝ) ^ 2 ≤ τ / σ)
    (x : Fin n → Fin m) (hunsafe : ¬ IsSafe g σ F Y x) :
    ∃ w : ParityTest F Y, w.IsCanonical ∧ w.parity.Nonempty ∧
      (w.conditioned = ∅ ∨ (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) *
        σ ^ w.conditioned.card * #(agreeOn Y w.conditioned w.assignment)) ∧
      (1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card < w.bias g x := by
  apply exists_ratio_parityTest_of_not_isSafe g σ F Y hYne hn hσ _ x hunsafe
  intro J hJ hJne α hA
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : 1 ≤ τ / σ := by nlinarith [sq_nonneg (n : ℝ)]
  exact hgap.trans ((le_self_pow₀ hbase (card_ne_zero.mpr hJne)).trans
    (hY.le_conditioning_ratio hσ hJ hJne α hA))

end Cslib.Communication.Lifting
