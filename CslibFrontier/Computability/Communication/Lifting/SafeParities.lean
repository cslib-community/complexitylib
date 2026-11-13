/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.Dangerous
public import CslibFrontier.Probability.SmallBias.Pointwise
public import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Parity criteria for safe values

The output law on a coordinate set makes the pointwise Vazirani estimates applicable to gadget
fibers. Conditional estimates retain the size of the conditioning slice, including rare slices.
The integer threshold is explicit: this avoids rounding and sign ambiguities when specializing
the high-order parity criterion in CFKMP Claim 3.14. No rare-dangerous-values estimate is assumed
or proved here.

## Main results

* `gadgetOutputLaw_apply`: exact output probabilities as fiber-cardinality ratios.
* `nonleaking_of_parity_bias_le`: pointwise parity bounds prevent leaking.
* `gadgetFiber_card_le_of_high_order_bias_le`: high-order parity bounds control conditional fibers.
* `isSafe_of_parity_bias_le`: explicit integer-threshold parity criterion for safety.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {n m : ℕ}

/-- The gadget outputs on `I` when Bob's input is uniform on a nonempty finite set. -/
noncomputable def gadgetOutputLaw (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (hY : Y.Nonempty) (I : Finset (Fin n)) (x : Fin n → Fin m) : PMF (I → Bool) :=
  (PMF.uniformOfFinset Y hY).map fun y i => g (x i) (y i)

/-- Output parity tests are ambient-coordinate parity tests; their description does not depend
on the larger output set containing the tested coordinates. -/
theorem bias_gadgetOutputLaw (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (hY : Y.Nonempty) (I : Finset (Fin n)) (x : Fin n → Fin m) (S : Finset I) :
    bias (gadgetOutputLaw g Y hY I x) S =
      ∑ y, ((PMF.uniformOfFinset Y hY) y).toReal *
        chi ℝ (S.map (Function.Embedding.subtype (· ∈ I))) (fun i => g (x i) (y i)) := by
  unfold gadgetOutputLaw
  rw [bias_map]
  apply sum_congr rfl
  intro y _
  congr 1
  exact chi_restrict I S (fun i => g (x i) (y i))

/-- An output atom is the cardinality ratio of its gadget fiber. -/
theorem gadgetOutputLaw_apply (g : Fin m → Fin m → Bool) (Y : Finset (Fin n → Fin m))
    (hY : Y.Nonempty) (I : Finset (Fin n)) (x : Fin n → Fin m) (β : Fin n → Bool) :
    ((gadgetOutputLaw g Y hY I x) (I.restrict β)).toReal =
      #(gadgetFiber g Y I x β) / (#Y : ℝ) := by
  classical
  unfold gadgetOutputLaw
  rw [← _root_.PMF.toOuterMeasure_apply_singleton, _root_.PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_uniformOfFinset_toReal]
  congr 2
  congr 1
  ext y
  simp only [mem_filter, Set.mem_preimage, Set.mem_singleton_iff, mem_gadgetFiber]
  apply and_congr_right
  intro _
  exact ⟨fun h i hi => congrFun h ⟨i, hi⟩, fun h => funext fun i => h i i.property⟩

/-- Pointwise parity bounds prevent leaking, including empty output sets. -/
theorem nonleaking_of_parity_bias_le (g : Fin m → Fin m → Bool)
    (Y : Finset (Fin n → Fin m)) (hY : Y.Nonempty) (I : Finset (Fin n))
    (x : Fin n → Fin m)
    (hbias : ∀ S : Finset I, S.Nonempty →
      |bias (gadgetOutputLaw g Y hY I x) S| ≤
        (1 / 2 : ℝ) * (1 / (2 * I.card) : ℝ) ^ S.card)
    (β : Fin n → Bool) : (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(gadgetFiber g Y I x β) := by
  have h := abs_mul_mass_sub_one_le_of_bias_le (gadgetOutputLaw g Y hY I x)
    (ε := 1 / 2) (by norm_num) (by simpa only [Fintype.card_coe] using hbias) (I.restrict β)
  rw [gadgetOutputLaw_apply] at h
  simp only [Fintype.card_coe] at h
  have hy : (0 : ℝ) < #Y := by exact_mod_cast card_pos.mpr hY
  have hl := (abs_le.mp h).1
  have hmul := mul_le_mul_of_nonneg_right hl hy.le
  rw [pow_succ]
  field_simp at hmul
  nlinarith

/-- High-order parity estimates bound a fiber, with the exact low-order subset count retained.
This applies even when `I` has zero or one coordinate. -/
theorem gadgetFiber_card_le_of_high_order_bias_le (g : Fin m → Fin m → Bool)
    (Y : Finset (Fin n → Fin m)) (hY : Y.Nonempty) (I : Finset (Fin n))
    (x : Fin n → Fin m) {t : ℕ} (ht : 1 ≤ t)
    (hbias : ∀ S : Finset I, t ≤ S.card →
      |bias (gadgetOutputLaw g Y hY I x) S| ≤ (1 / (2 * I.card) : ℝ) ^ S.card)
    (β : Fin n → Bool) :
    2 ^ #I * (#(gadgetFiber g Y I x β) : ℝ) ≤
      (#{S : Finset I | S.card < t} + 1 : ℝ) * #Y := by
  classical
  let q : ℝ := 1 / (2 * I.card)
  have hq : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 := by
    by_cases hi : I.card = 0
    · simp [q, hi]
    · have hi1 : (1 : ℝ) ≤ I.card := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi
      dsimp [q]
      exact (div_le_one (by positivity)).mpr (by linarith)
  have hiq : (I.card : ℝ) * q ≤ 1 / 2 := by
    by_cases hi : I.card = 0
    · simp [hi]
    · have hi0 : (0 : ℝ) < I.card := by exact_mod_cast Nat.pos_of_ne_zero hi
      dsimp [q]
      apply le_of_eq
      field_simp
  have hm := mul_mass_le_card_add_one_of_high_order_bias_le (gadgetOutputLaw g Y hY I x)
    ht hq hq1 (by simpa only [Fintype.card_coe] using hiq) hbias (I.restrict β)
  rw [gadgetOutputLaw_apply] at hm
  simp only [Fintype.card_coe] at hm
  have hbound : 2 ^ #I * (#(gadgetFiber g Y I x β) / (#Y : ℝ)) ≤
      (#{S : Finset I | S.card < t} + 1 : ℝ) := hm
  have hy : (0 : ℝ) < #Y := by exact_mod_cast card_pos.mpr hY
  have hmul := mul_le_mul_of_nonneg_right hbound hy.le
  simpa only [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hy)] using hmul

/-- A sufficient parity criterion for safety. Conditional high-order estimates are required only
above an explicit positive integer threshold; the exact number of lower-order parities is paid
for by the slice-size inequality. This is the finite-threshold form of the mechanism in CFKMP
Claim 3.14, keeping its numerical specialization separate. -/
theorem isSafe_of_parity_bias_le (g : Fin m → Fin m → Bool) (σ : ℝ)
    (F : Finset (Fin n)) (Y : Finset (Fin n → Fin m)) (hY : Y.Nonempty)
    (x : Fin n → Fin m) (hσ : 0 ≤ σ)
    (hunconditional : ∀ I ⊆ F, ∀ S : Finset I, S.Nonempty →
      |bias (gadgetOutputLaw g Y hY I x) S| ≤
        (1 / 2 : ℝ) * (1 / (2 * I.card) : ℝ) ^ S.card)
    (hconditional : ∀ I ⊆ F, ∀ J ⊆ F \ I, J.Nonempty → ∀ α : Fin n → Fin m,
      ∀ hA : (agreeOn Y J α).Nonempty, ∃ t : ℕ, 1 ≤ t ∧
        (∀ S : Finset I, t ≤ S.card →
          |bias (gadgetOutputLaw g (agreeOn Y J α) hA I x) S| ≤
            (1 / (2 * I.card) : ℝ) ^ S.card) ∧
        2 * (#{S : Finset I | S.card < t} + 1 : ℝ) * σ ^ #J * #(agreeOn Y J α) ≤ #Y) :
    IsSafe g σ F Y x := by
  classical
  have hleak (I : Finset (Fin n)) (hI : I ⊆ F) (β : Fin n → Bool) :
      (#Y : ℝ) ≤ 2 ^ (#I + 1) * #(gadgetFiber g Y I x β) :=
    nonleaking_of_parity_bias_le g Y hY I x (hunconditional I hI) β
  refine ⟨hleak, ?_⟩
  intro I hI β
  by_contra hfail
  obtain ⟨J, α, hJ, hJne, _, hB, hcard⟩ := exists_bayes_card_certificate (hleak I hI β) hfail
  have hA : (agreeOn Y J α).Nonempty := hB.mono (gadgetFiber_subset g _ I x β)
  obtain ⟨t, ht, hbias, hcap⟩ := hconditional I hI J hJ hJne α hA
  have hupper := gadgetFiber_card_le_of_high_order_bias_le g _ hA I x ht hbias β
  have hmul := mul_le_mul_of_nonneg_left hupper (by positivity : (0 : ℝ) ≤ 2 * σ ^ #J)
  have hcontr : (#Y : ℝ) < #Y := calc
    _ < 2 ^ (#I + 1) * #(gadgetFiber g (agreeOn Y J α) I x β) * σ ^ #J := hcard
    _ = (2 * σ ^ #J) * (2 ^ #I * #(gadgetFiber g (agreeOn Y J α) I x β)) := by
      rw [pow_succ]; ring
    _ ≤ (2 * σ ^ #J) * ((#{S : Finset I | S.card < t} + 1 : ℝ) * #(agreeOn Y J α)) := hmul
    _ = 2 * (#{S : Finset I | S.card < t} + 1 : ℝ) * σ ^ #J * #(agreeOn Y J α) := by ring
    _ ≤ #Y := hcap
  exact (lt_irrefl _) hcontr

end Cslib.Communication.Lifting
