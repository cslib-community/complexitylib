/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.Partition
public import CslibFrontier.Computability.Communication.Discrepancy.Extractor
public import CslibFrontier.Computability.Communication.Discrepancy.Xor
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Discrepancy bounds for projections of dense finite sets

Blockwise density bounds each atom of a projected uniform source. Combining this fact with the
independent-source extractor estimate bounds the parity bias of a block gadget on two dense
sets. The fourth-power discrepancy XOR estimate then reduces this to the single-block gadget.
-/

public section

namespace Cslib.Communication.Lifting

open Finset BitString Probability

variable {n m : ℕ} {τ : ℝ} {F I : Finset (Fin n)} {X : Finset (Fin n → Fin m)}

/-- Every projected atom of a uniform dense set has mass at most the inverse density power. -/
theorem IsDense.map_restrict_toReal_le (hX : IsDense τ F X) (hτ : 0 < τ)
    (hne : X.Nonempty) (hIF : I ⊆ F) (a : I → Fin m) :
    (((PMF.uniformOfFinset X hne).map (fun x (i : I) => x i)) a).toReal ≤
      (τ ^ I.card)⁻¹ := by
  classical
  let x₀ := hne.choose
  let α : Fin n → Fin m := fun i => if hi : i ∈ I then a ⟨i, hi⟩ else x₀ i
  have heq : (fun x : Fin n → Fin m => (fun i : I => x i) = a) =
      (fun x => ∀ i ∈ I, x i = α i) := by
    funext x
    apply propext
    constructor
    · intro h i hi
      simpa [α, hi] using congrFun h ⟨i, hi⟩
    · intro h
      funext i
      simpa [α, i.property] using h i i.property
  rw [← _root_.PMF.toOuterMeasure_apply_singleton,
    _root_.PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFinset_toReal]
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  simp only [heq]
  have hcard : (0 : ℝ) < X.card := by exact_mod_cast hne.card_pos
  have hp : 0 < τ ^ I.card := pow_pos hτ _
  apply (div_le_iff₀ hcard).2
  rw [mul_comm, ← div_eq_mul_inv]
  apply (le_div_iff₀ hp).2
  change ((X.filter fun x => ∀ i ∈ I, x i = α i).card : ℝ) * τ ^ I.card ≤ _
  rcases I.eq_empty_or_nonempty with hI | hI
  · subst I
    simp
  · simpa [div_eq_mul_inv, mul_comm] using hX I hIF hI α

/-- Independent uniform sources from dense sets have small projected parity bias whenever the
corresponding XOR gadget has small uniform discrepancy. -/
theorem abs_projected_parity_bias_le [NeZero m]
    {τX τY : ℝ} {Y : Finset (Fin n → Fin m)}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hIF : I ⊆ F) (g : Fin m → Fin m → Bool) :
    |∑ x : I → Fin m, ∑ y : I → Fin m,
      (((PMF.uniformOfFinset X hXne).map (fun z (i : I) => z i)) x).toReal *
      (((PMF.uniformOfFinset Y hYne).map (fun z (i : I) => z i)) y).toReal *
      signVal (∑ i, g (x i) (y i))| ≤
        ((m : ℝ) ^ 2 / (τX * τY)) ^ I.card *
          discrepancy (PMF.uniformOfFintype ((I → Fin m) × (I → Fin m)))
            (fun x y => ∑ i, g (x i) (y i)) := by
  classical
  have h := abs_sum_mul_signVal_le_discrepancy_of_mass_le
    ((PMF.uniformOfFinset X hXne).map (fun z (i : I) => z i))
    ((PMF.uniformOfFinset Y hYne).map (fun z (i : I) => z i))
    (fun x y => ∑ i, g (x i) (y i))
    (inv_nonneg.mpr (pow_nonneg hτX.le _)) (inv_nonneg.mpr (pow_nonneg hτY.le _))
    (hX.map_restrict_toReal_le hτX hXne hIF)
    (hY.map_restrict_toReal_le hτY hYne hIF)
  convert h using 1;
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow]
  congr 1
  simp only [div_pow, mul_pow, inv_mul_eq_div]
  ring

/-- A single-block discrepancy bound controls every projected parity of two independent
uniform dense sets. This uses the fourth-power XOR estimate. -/
theorem projected_parity_bias_fourth_pow_le [NeZero m]
    {τX τY : ℝ} {Y : Finset (Fin n → Fin m)}
    (hX : IsDense τX F X) (hY : IsDense τY F Y)
    (hτX : 0 < τX) (hτY : 0 < τY) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hIF : I ⊆ F) (g : Fin m → Fin m → Bool) :
    |∑ x : I → Fin m, ∑ y : I → Fin m,
      (((PMF.uniformOfFinset X hXne).map (fun z (i : I) => z i)) x).toReal *
      (((PMF.uniformOfFinset Y hYne).map (fun z (i : I) => z i)) y).toReal *
      signVal (∑ i, g (x i) (y i))| ^ 4 ≤
        (((m : ℝ) ^ 2 / (τX * τY)) ^ 4 *
          (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g)) ^ I.card := by
  classical
  have hb := abs_projected_parity_bias_le hX hY hτX hτY hXne hYne hIF g
  have hx := discrepancy_xor_fourth_pow_le (κ := I) g
  have hp := pow_le_pow_left₀ (abs_nonneg _) hb 4
  rw [mul_pow] at hp
  calc
    _ ≤ (((m : ℝ) ^ 2 / (τX * τY)) ^ I.card) ^ 4 *
        discrepancy (PMF.uniformOfFintype ((I → Fin m) × (I → Fin m)))
          (fun x y => ∑ i, g (x i) (y i)) ^ 4 := hp
    _ ≤ (((m : ℝ) ^ 2 / (τX * τY)) ^ I.card) ^ 4 *
        (4 * discrepancy (PMF.uniformOfFintype (Fin m × Fin m)) g) ^ I.card :=
      mul_le_mul_of_nonneg_left (by simpa only [Fintype.card_coe] using hx)
        (by positivity)
    _ = _ := by simp only [mul_pow, ← pow_mul, Nat.mul_comm I.card 4]

/-- Conditioning on one block assignment costs its probability only once, rather than once
per remaining coordinate. This is the joint counting inequality before division. -/
theorem IsDense.card_agreeOn_agreeOn_mul_pow_le (hX : IsDense τ F X)
    {J : Finset (Fin n)} (hIF : I ⊆ F) (hJF : J ⊆ F) (hdisj : Disjoint J I)
    (α β : Fin n → Fin m) :
    ((agreeOn (agreeOn X J α) I β).card : ℝ) * τ ^ (I.card + J.card) ≤ X.card := by
  classical
  have heq : agreeOn (agreeOn X J α) I β =
      agreeOn X (J ∪ I) (fun i => if i ∈ J then α i else β i) := by
    simpa only [agreeOn] using (agreeOn_union_ite (W := X) hdisj α β).symm
  rw [heq]
  rcases (J ∪ I).eq_empty_or_nonempty with h | h
  · have hJ : J = ∅ := (union_eq_empty.mp h).1
    have hI : I = ∅ := (union_eq_empty.mp h).2
    subst J
    subst I
    simp [agreeOn]
  · have hcard : (J ∪ I).card = I.card + J.card := by
      rw [card_union_of_disjoint hdisj, Nat.add_comm]
    simpa [hcard, agreeOn] using hX (J ∪ I) (union_subset hJF hIF) h
      (fun i => if i ∈ J then α i else β i)

/-- The conditional atom cap expressed as a ratio of finite fiber sizes. The denominator is
the conditioning event's probability times the density power for both sets of coordinates. -/
theorem IsDense.card_agreeOn_agreeOn_div_le (hX : IsDense τ F X) (hτ : 0 < τ)
    {J : Finset (Fin n)} (hIF : I ⊆ F) (hJF : J ⊆ F) (hdisj : Disjoint J I)
    (α β : Fin n → Fin m) (hne : (agreeOn X J α).Nonempty) :
    ((agreeOn (agreeOn X J α) I β).card : ℝ) / (agreeOn X J α).card ≤
      (X.card : ℝ) / ((agreeOn X J α).card * τ ^ (I.card + J.card)) := by
  have hc : (0 : ℝ) < (agreeOn X J α).card := by exact_mod_cast hne.card_pos
  have hp : 0 < τ ^ (I.card + J.card) := pow_pos hτ _
  apply (div_le_iff₀ hc).2
  rw [div_mul_eq_div_mul_one_div]
  have heq : (X.card : ℝ) / (agreeOn X J α).card * (1 / τ ^ (I.card + J.card)) *
      (agreeOn X J α).card = X.card / τ ^ (I.card + J.card) := by
    field_simp
  rw [heq]
  exact (le_div_iff₀ hp).2 (hX.card_agreeOn_agreeOn_mul_pow_le hIF hJF hdisj α β)

/-- The projected atom bound after conditioning on a disjoint block assignment. -/
theorem IsDense.map_restrict_agreeOn_toReal_le (hX : IsDense τ F X) (hτ : 0 < τ)
    {J : Finset (Fin n)} (hIF : I ⊆ F) (hJF : J ⊆ F) (hdisj : Disjoint J I)
    (α β : Fin n → Fin m) (hne : (agreeOn X J α).Nonempty) :
    (((PMF.uniformOfFinset (agreeOn X J α) hne).map (fun x (i : I) => x i))
      (fun i => β i)).toReal ≤
      (X.card : ℝ) / ((agreeOn X J α).card * τ ^ (I.card + J.card)) := by
  classical
  rw [← _root_.PMF.toOuterMeasure_apply_singleton,
    _root_.PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_uniformOfFinset_toReal]
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff,
    Subtype.forall, agreeOn] using
    hX.card_agreeOn_agreeOn_div_le hτ hIF hJF hdisj α β hne

end Cslib.Communication.Lifting
