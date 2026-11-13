/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.DenseDiscrepancy
import CslibFrontier.Probability.PMF.Event
import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Probabilities of conditional parity witnesses

A `ParityTest` specifies disjoint parity and conditioning coordinates and a supported value
of the conditioning coordinates. Density on their union controls every atom of the conditional
source. The row-sampling bound then bounds the probability that the conditional parity is biased.
A finite family of tests is handled by the existing outer-measure union bound.

The actual conditioning-slice size remains in every estimate. This is the finite-witness step
of CFKMP Proposition 3.15, before counting eligible witnesses and choosing exponential parameters.
Neither the eligibility argument nor the asymptotic rare-dangerous-values theorem is asserted.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {n m : ℕ}

/-- A supported conditional parity test on disjoint coordinate sets. -/
structure ParityTest (F : Finset (Fin n)) (Y : Finset (Fin n → Fin m)) where
  /-- Coordinates whose gadget outputs are XORed. -/
  parity : Finset (Fin n)
  /-- Coordinates fixed before the parity is evaluated. -/
  conditioned : Finset (Fin n)
  /-- Values fixed on the conditioning coordinates. -/
  assignment : Fin n → Fin m
  /-- Parity coordinates are free. -/
  parity_subset : parity ⊆ F
  /-- Conditioning coordinates are free. -/
  conditioned_subset : conditioned ⊆ F
  /-- No coordinate is both conditioned and tested. -/
  disjoint : Disjoint conditioned parity
  /-- The conditioning event has positive probability. -/
  supported : (agreeOn Y conditioned assignment).Nonempty

/-- There are finitely many conditional parity tests; their proof fields carry no data. -/
noncomputable instance {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m)} :
    Fintype (ParityTest F Y) := by
  classical
  exact Fintype.ofInjective
    (fun w : ParityTest F Y => (w.parity, w.conditioned, w.assignment)) (by
      intro a b h
      cases a
      cases b
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl)

namespace ParityTest

variable {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}

/-- Absolute bias of the conditional gadget parity for the supplied speaker input. -/
@[expose] noncomputable def bias (w : ParityTest F Y) (g : Fin m → Fin m → Bool)
    (x : Fin n → Fin m) : ℝ :=
  |∑ y : w.parity → Fin m,
    (((PMF.uniformOfFinset (agreeOn Y w.conditioned w.assignment) w.supported).map
      (fun z (i : w.parity) => z i)) y).toReal * signVal (∑ i : w.parity, g (x i) (y i))|

/-- The explicit first-moment cost of a conditional parity test. The slice denominator records
its true probability, including any excess entropy of the conditioning value. -/
@[expose] noncomputable def tailCost [NeZero m] (w : ParityTest F Y) (g : Fin m → Fin m → Bool)
    (τX τY : ℝ) : ℝ :=
  2 * ((τX ^ w.parity.card)⁻¹ *
    ((Y.card : ℝ) / ((agreeOn Y w.conditioned w.assignment).card *
      τY ^ (w.parity.card + w.conditioned.card))) *
    ((m : ℝ) ^ w.parity.card * (m : ℝ) ^ w.parity.card) *
    discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
      (fun x y => ∑ i, g (x i) (y i)))

/-- The single-block discrepancy controls the fourth power of the tail cost. This is the
place where the weaker elementary XOR estimate enters the dangerous-values calculation. -/
theorem tailCost_fourth_pow_le [NeZero m] (w : ParityTest F Y)
    (g : Fin m → Fin m → Bool) (τX τY : ℝ) :
    w.tailCost g τX τY ^ 4 ≤
      16 * ((τX ^ w.parity.card)⁻¹ *
        ((Y.card : ℝ) / ((agreeOn Y w.conditioned w.assignment).card *
          τY ^ (w.parity.card + w.conditioned.card))) *
        ((m : ℝ) ^ w.parity.card * (m : ℝ) ^ w.parity.card)) ^ 4 *
        (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g) ^ w.parity.card := by
  have h := discrepancy_xor_fourth_pow_le (κ := w.parity) g
  calc
    _ = 16 * ((τX ^ w.parity.card)⁻¹ *
        ((Y.card : ℝ) / ((agreeOn Y w.conditioned w.assignment).card *
          τY ^ (w.parity.card + w.conditioned.card))) *
        ((m : ℝ) ^ w.parity.card * (m : ℝ) ^ w.parity.card)) ^ 4 *
        discrepancy (PMF.uniformOfFintype ((w.parity → Fin m) × (w.parity → Fin m)))
          (fun x y => ∑ i, g (x i) (y i)) ^ 4 := by
      simp only [tailCost, mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by simpa only [Fintype.card_coe] using h) (by positivity)

/-- A fixed conditional parity test has a strict sampling tail. Density is used jointly on
parity and conditioning coordinates, so conditioning costs its probability only once. -/
theorem probability_bias_lt [NeZero m] (w : ParityTest F Y)
    (g : Fin m → Fin m → Bool) {τX τY t β : ℝ}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty)
    (ht : 0 < t) (hβ : 0 < β) (hbound : w.tailCost g τX τY ≤ t * β) :
    ((PMF.uniformOfFinset X hXne).toOuterMeasure {x | t < w.bias g x}).toReal < β := by
  classical
  let p := (PMF.uniformOfFinset X hXne).map (fun z (i : w.parity) => z i)
  let q := (PMF.uniformOfFinset (agreeOn Y w.conditioned w.assignment) w.supported).map
    (fun z (i : w.parity) => z i)
  have hq (y : w.parity → Fin m) : (q y).toReal ≤
      (Y.card : ℝ) / ((agreeOn Y w.conditioned w.assignment).card *
        τY ^ (w.parity.card + w.conditioned.card)) := by
    let a : Fin n → Fin m := fun i => if hi : i ∈ w.parity then y ⟨i, hi⟩ else 0
    have ha : (fun i : w.parity => a i) = y := by funext i; simp [a, i.property]
    have h := hY.map_restrict_agreeOn_toReal_le hτY w.parity_subset
      w.conditioned_subset w.disjoint w.assignment a w.supported
    rw [ha] at h
    exact h
  have h := sum_mass_filter_rowBias_lt p q (fun x y => ∑ i, g (x i) (y i))
    (by positivity : 0 ≤ (τX ^ w.parity.card)⁻¹)
    (by positivity : 0 ≤ (Y.card : ℝ) /
      ((agreeOn Y w.conditioned w.assignment).card *
        τY ^ (w.parity.card + w.conditioned.card)))
    (hX.map_restrict_toReal_le hτX hXne w.parity_subset) hq ht hβ
    (by simpa only [tailCost, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
      Nat.cast_pow] using hbound)
  have heq : (PMF.uniformOfFinset X hXne).toOuterMeasure {x | t < w.bias g x} =
      p.toOuterMeasure {x | t < |∑ y, (q y).toReal * signVal (∑ i, g (x i) (y i))|} := by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [heq, PMF.toOuterMeasure_apply_toReal]
  simpa only [sum_filter, Set.mem_ofPred_eq] using h

end ParityTest

/-- The probability that any test in a finite family is biased is bounded by the sum of the
individual tail budgets. The family can be restricted to eligible witnesses before applying
this theorem; no count of impossible or zero-probability conditioning values is needed. -/
theorem probability_exists_parityTest_le {κ : Type*} [Fintype κ] [NeZero m]
    {F : Finset (Fin n)} {X Y : Finset (Fin n → Fin m)}
    (w : κ → ParityTest F Y) (g : Fin m → Fin m → Bool)
    {τX τY : ℝ} (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty)
    (t β : κ → ℝ) (ht : ∀ k, 0 < t k) (hβ : ∀ k, 0 < β k)
    (hbound : ∀ k, (w k).tailCost g τX τY ≤ t k * β k) :
    ((PMF.uniformOfFinset X hXne).toOuterMeasure
      {x | ∃ k, t k < (w k).bias g x}).toReal ≤ ∑ k, β k := by
  classical
  let p := PMF.uniformOfFinset X hXne
  let E := fun k => {x | t k < (w k).bias g x}
  have hu := MeasureTheory.measure_iUnion_fintype_le p.toOuterMeasure E
  have heq : {x | ∃ k, t k < (w k).bias g x} = ⋃ k, E k := by ext x; simp [E]
  rw [heq]
  calc
    _ ≤ (∑ k, p.toOuterMeasure (E k)).toReal :=
      ENNReal.toReal_mono
        (ENNReal.sum_ne_top.mpr (fun k _ => PMF.toOuterMeasure_ne_top p (E k))) hu
    _ = ∑ k, (p.toOuterMeasure (E k)).toReal :=
      ENNReal.toReal_sum (fun k _ => PMF.toOuterMeasure_ne_top p (E k))
    _ ≤ ∑ k, β k := sum_le_sum fun k _ =>
      ((w k).probability_bias_lt g hX hY hτX hτY hXne (ht k) (hβ k) (hbound k)).le

end Cslib.Communication.Lifting
