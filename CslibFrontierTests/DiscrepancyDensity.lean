/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

public import CslibFrontier.Computability.Communication.Lifting.DensitySimulation
public import CslibFrontier.Computability.Communication.Lifting.DenseDiscrepancy
public import CslibFrontier.Computability.Communication.Lifting.DangerousProbability
public import CslibFrontier.Computability.Communication.Lifting.SafeParities
public import CslibFrontier.Computability.Communication.Lifting.Volume

/-! Boundary cases and clients of the dangerous-value and simulation ingredients. -/

public section

open Cslib.Communication.Lifting Finset

namespace DiscrepancyDensityTests

/-- With no free coordinates, every value is safe, even for a constant gadget. -/
theorem safe_empty {n m : ℕ} (g : Fin m → Fin m → Bool) (σ : ℝ)
    (Y : Finset (Fin n → Fin m)) (x : Fin n → Fin m) : IsSafe g σ ∅ Y x := by
  constructor
  · intro I hI β
    have hI' : I = ∅ := subset_empty.mp hI
    subst I
    simp only [gadgetFiber_empty, card_empty, zero_add, pow_one]
    linarith [Nat.cast_nonneg (α := ℝ) Y.card]
  · intro I hI β J hJ hne
    have : J = ∅ := subset_empty.mp (hJ.trans (sdiff_subset : ∅ \ I ⊆ ∅))
    exact False.elim (hne.ne_empty this)

/-- A simulation with no free coordinates selects its step before the answer assignment. -/
example (g : Fin 1 → Fin 1 → Bool) (σ : ℝ) :
    ∃ st : DensityStep 0 1,
      st.Valid g 2 σ ∅ univ univ (fun _ => false) ∧ st.queried = ∅ := by
  classical
  have hsafe : ((univ : Finset (Fin 0 → Fin 1)).card : ℝ) ≤
      2 * #(univ.filter (IsSafe (n := 0) g σ ∅ univ)) := by
    simp [safe_empty]
  obtain ⟨st, hst⟩ := exists_densityStep (n := 0) g 2 σ ∅ univ univ (fun _ => false)
    (by norm_num) univ_nonempty univ_nonempty hsafe
  exact ⟨st, hst, subset_empty.mp hst.queried_subset⟩

/-- A constant gadget fails the safety condition as soon as a coordinate is free. -/
example : ¬ IsSafe (fun _ _ : Fin 1 => false) 1 univ
    ({fun _ : Fin 1 => (0 : Fin 1)} : Finset (Fin 1 → Fin 1)) (fun _ => 0) := by
  intro h
  have hbad := h.nonleaking univ (Subset.refl _) (fun _ => true)
  norm_num [gadgetFiber] at hbad

/-- Restoration can select a nonempty concentrated coordinate even from a singleton source. -/
example : ∃ I : Finset (Fin 1), ∃ α : Fin 1 → Fin 1,
    (agreeOn {fun _ : Fin 1 => (0 : Fin 1)} I α).Nonempty ∧
      IsDense 2 (univ \ I) (agreeOn {fun _ : Fin 1 => (0 : Fin 1)} I α) := by
  obtain ⟨I, α, _, hn, _, _, hd, _⟩ :=
    exists_dense_agreeOn (τ := 2) (by norm_num) univ
      (singleton_nonempty (fun _ : Fin 1 => (0 : Fin 1)))
  exact ⟨I, α, hn, hd⟩

/-- The query accounting specializes to the per-bit loss used by DensityStep.Valid.volume. -/
example (volume : ℕ → ℝ) (cost : ℕ → ℕ) (c : ℕ) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : ∀ i < c, volume i ≤ 8 * (2 * τ) ^ cost i * volume (i + 1)) :
    volume 0 ≤ 8 ^ c * (2 * τ) ^ (∑ i ∈ range c, cost i) * volume c := by
  exact volume_le_pow_mul_of_steps (by norm_num) (by positivity) volume cost c h

end DiscrepancyDensityTests
