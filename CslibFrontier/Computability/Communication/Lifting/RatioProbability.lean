/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DangerousProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Tail estimates for ratio-eligible parity witnesses

The intrinsic slice-ratio bound removes the conditioning assignment's excess entropy from the
sampling estimate. Density then restricts the size of the conditioning set relative to the parity
set. These are explicit algebraic inputs to the counting part of the dangerous-values argument.
-/

public section

namespace Cslib.Communication.Lifting.ParityTest

open Finset Probability

variable {n m : ℕ} {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)}

/-- Under the slice-ratio bound, conditioning has at most a quadratic ambient-cardinality
factor per parity coordinate. The actual slice probability has been eliminated. -/
theorem conditional_atomCap_le_of_ratio (w : ParityTest F Y) {τY σ : ℝ}
    (hτY : 0 < τY) (hσ : 0 ≤ σ) (hστ : σ ≤ τY)
    (hratio : (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment)) :
    (#Y : ℝ) / (#(agreeOn Y w.conditioned w.assignment) *
      τY ^ (w.parity.card + w.conditioned.card)) ≤
      (n : ℝ) ^ (2 * w.parity.card) / τY ^ w.parity.card := by
  have hA : (0 : ℝ) < #(agreeOn Y w.conditioned w.assignment) := by
    exact_mod_cast w.supported.card_pos
  have hp := pow_le_pow_left₀ hσ hστ w.conditioned.card
  apply (div_le_iff₀ (mul_pos hA (pow_pos hτY _))).mpr
  calc
    _ ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
        #(agreeOn Y w.conditioned w.assignment) := hratio
    _ ≤ (n : ℝ) ^ (2 * w.parity.card) * τY ^ w.conditioned.card *
        #(agreeOn Y w.conditioned w.assignment) := by gcongr
    _ = _ := by rw [pow_add]; field_simp

/-- Ratio eligibility bounds the parity-test sampling cost by the XOR discrepancy with an
explicit per-coordinate amplification. -/
theorem tailCost_le_of_ratio [NeZero m] (w : ParityTest F Y)
    (g : Fin m → Fin m → Bool) {τX τY σ : ℝ}
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 ≤ σ) (hστ : σ ≤ τY)
    (hratio : (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment)) :
    w.tailCost g τX τY ≤
      2 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ w.parity.card *
        discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
          (fun x y => ∑ i, g (x i) (y i)) := by
  have hcap := w.conditional_atomCap_le_of_ratio hτY hσ hστ hratio
  calc
    _ ≤ 2 * ((τX ^ w.parity.card)⁻¹ *
        ((n : ℝ) ^ (2 * w.parity.card) / τY ^ w.parity.card) *
        ((m : ℝ) ^ w.parity.card * (m : ℝ) ^ w.parity.card) *
        discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
          (fun x y => ∑ i, g (x i) (y i))) := by
      unfold tailCost
      gcongr
      exact discrepancy_nonneg
    _ = _ := by
      simp only [mul_pow, pow_mul, div_eq_mul_inv]
      ring

/-- The intrinsic ratio estimate combined with the elementary XOR bound uses only the
single-block gadget discrepancy. -/
theorem tailCost_fourth_pow_le_of_ratio [NeZero m] (w : ParityTest F Y)
    (g : Fin m → Fin m → Bool) {τX τY σ : ℝ}
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 ≤ σ) (hστ : σ ≤ τY)
    (hratio : (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment)) :
    w.tailCost g τX τY ^ 4 ≤
      16 * ((((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4) *
        (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g)) ^ w.parity.card := by
  let A := (m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)
  have hd : 0 ≤ discrepancy
      (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
      (fun x y => ∑ i, g (x i) (y i)) := discrepancy_nonneg
  have hnonneg : 0 ≤ w.tailCost g τX τY := by unfold tailCost; positivity
  have h := pow_le_pow_left₀ hnonneg
    (w.tailCost_le_of_ratio g hτX hτY hσ hστ hratio) 4
  have hx := discrepancy_xor_fourth_pow_le (κ := w.parity) g
  calc
    _ ≤ (2 * A ^ w.parity.card *
        discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
          (fun x y => ∑ i, g (x i) (y i))) ^ 4 := h
    _ = 16 * (A ^ 4) ^ w.parity.card *
        discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
          (fun x y => ∑ i, g (x i) (y i)) ^ 4 := by
      simp only [mul_pow, ← pow_mul, Nat.mul_comm w.parity.card 4]
      norm_num
    _ ≤ 16 * (A ^ 4) ^ w.parity.card *
        (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g) ^ w.parity.card :=
      mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_coe] using hx) (by positivity)
    _ = _ := by simp only [A, mul_pow]; ring

/-- A single explicit gadget-discrepancy inequality supplies a geometric tail budget of
`q^|S|/2` at the ambient witness threshold. The factor `16384` includes the fourth-power XOR
loss and the two one-half factors in the threshold and budget. -/
theorem tailCost_le_geometric_budget_of_ratio [NeZero m] (w : ParityTest F Y)
    (g : Fin m → Fin m → Bool) {τX τY σ q : ℝ}
    (hτX : 0 < τX) (hτY : 0 < τY) (hσ : 0 ≤ σ) (hστ : σ ≤ τY)
    (hq : 0 < q) (hn : 1 ≤ n) (hS : w.parity.Nonempty)
    (hratio : (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment))
    (hdisc : 16384 * ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4 *
      discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g ≤ (q / (2 * n)) ^ 4) :
    w.tailCost g τX τY ≤
      ((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card) *
        ((1 / 2 : ℝ) * q ^ w.parity.card) := by
  let D := ((m : ℝ) ^ 2 * (n : ℝ) ^ 2 / (τX * τY)) ^ 4 *
    (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g)
  have hd : 0 ≤ discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g := discrepancy_nonneg
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound : 4096 * D ≤ (q / (2 * n)) ^ 4 := by dsimp [D]; nlinarith [hdisc]
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 4096 * D) hbound w.parity.card
  rw [mul_pow] at hp
  have hs : (4096 : ℝ) ≤ 4096 ^ w.parity.card :=
    le_self_pow₀ (by norm_num) (card_ne_zero.mpr hS)
  have hscale := mul_le_mul_of_nonneg_right hs (pow_nonneg hD w.parity.card)
  have hfour := w.tailCost_fourth_pow_le_of_ratio g hτX hτY hσ hστ hratio
  have hfinal : w.tailCost g τX τY ^ 4 ≤
      (((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card) *
        ((1 / 2 : ℝ) * q ^ w.parity.card)) ^ 4 := by
    calc
      _ ≤ 16 * D ^ w.parity.card := hfour
      _ ≤ (1 / 256 : ℝ) * (4096 ^ w.parity.card * D ^ w.parity.card) := by nlinarith
      _ ≤ (1 / 256 : ℝ) * ((q / (2 * n)) ^ 4) ^ w.parity.card := by linarith
      _ = _ := by
        simp only [div_eq_mul_inv, mul_pow, ← pow_mul, Nat.mul_comm w.parity.card 4]
        ring
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hright : 0 ≤ ((1 / 2 : ℝ) * (1 / (2 * n) : ℝ) ^ w.parity.card) *
      ((1 / 2 : ℝ) * q ^ w.parity.card) := by positivity
  exact le_of_pow_le_pow_left₀ (by norm_num) hright hfinal

/-- Unconditional tests automatically satisfy the intrinsic slice-ratio condition. -/
theorem ratio_card_le_of_conditioned_eq_empty (w : ParityTest F Y)
    (hn : 1 ≤ n) (σ : ℝ) (hJ : w.conditioned = ∅) :
    (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (1 : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) := one_le_pow₀ hnR
  simp only [hJ, card_empty, pow_zero, mul_one]
  have heq : agreeOn Y ∅ w.assignment = Y := by simp [agreeOn]
  rw [heq]
  nlinarith [(Nat.cast_nonneg Y.card : (0 : ℝ) ≤ Y.card)]

/-- Density and ratio eligibility force the conditioning set to be small compared with the
parity set. This inequality is ready for the canonical-assignment counting bound. -/
theorem density_ratio_pow_le (w : ParityTest F Y) {τY σ : ℝ}
    (hY : IsDense τY F Y) (hσ : 0 < σ)
    (hratio : (#Y : ℝ) ≤ (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card *
      #(agreeOn Y w.conditioned w.assignment)) :
    (τY / σ) ^ w.conditioned.card ≤ (n : ℝ) ^ (2 * w.parity.card) := by
  have hA : (0 : ℝ) < #(agreeOn Y w.conditioned w.assignment) := by
    exact_mod_cast w.supported.card_pos
  have hd : (#(agreeOn Y w.conditioned w.assignment) : ℝ) *
      τY ^ w.conditioned.card ≤ #Y := by
    rcases w.conditioned.eq_empty_or_nonempty with he | he
    · simp [he, agreeOn]
    · exact hY w.conditioned w.conditioned_subset he w.assignment
  have hp : τY ^ w.conditioned.card ≤
      (n : ℝ) ^ (2 * w.parity.card) * σ ^ w.conditioned.card := by
    apply le_of_mul_le_mul_right (a := (#(agreeOn Y w.conditioned w.assignment) : ℝ)) _ hA
    nlinarith
  rw [div_pow]
  exact (div_le_iff₀ (pow_pos hσ _)).mpr hp

end Cslib.Communication.Lifting.ParityTest
