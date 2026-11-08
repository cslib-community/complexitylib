/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTaskMeans
public import Complexity.Foundations.Probability.FourthRootHierarchyParams
public import Complexity.Probability.PairwiseIndependentHash.AtomChannels

/-!
# Deriving correction sampling data from hierarchy channels

`CorrectionSampling.ofChannels` builds the existing actual-correction sampler from retention
channels in both orders. The detector lemma supplies its incoming column count, the hierarchy
row-gate rank supplies its normalization rank, and channel pair probabilities supply both pair
counts. No desired mean or aggregate error bound is assumed. Affine channels satisfy both ordered
channel interfaces; the construction therefore applies to their independent source/midpoint seeds.

This discharges primitive sampling obligations for the actual correction input in
[OpenAI2026LogSpace, Sections 5.3 and 7.2, Lemma 7.1], revision `7ef5c0cc`. The preparatory
support and incoming cutoff functions remain explicit: their later access/regularity contracts
are not proved here. This is not full task assembly or a scheduled mean-prefix theorem.

## Main definitions

* `Matrix.HierarchyParams.CorrectionSampling.ofChannels`: channel-derived sampling data.

## Main results

* `Matrix.HierarchyParams.correctionInput_count_le`: the hierarchy detector bounds incoming counts.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f π : ℝ} {C : Matrix V V ℝ}

/-- The existing detector count bound specialized to the actual hierarchy input. -/
theorem correctionInput_count_le
    (hch : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) {i : ℕ} (hi : i < P.k)
    {z : V} (hg : P.γ (P.pilot X Y f C z) ≠ 0) :
    (#({w | P.δ₁ * f ≤ P.correctionInput X Y f C i w z} : Finset V) : ℝ) ≤
      P.R / f := by
  have hct (t : ℝ) (ht : 0 ≤ t) : P.cutoff f t ≤ t :=
    (P.cutoff_le hf t).trans (max_le (by
      have := mul_nonneg P.θ_pos.le hf.le
      linarith) ht)
  have hpos : 0 < P.γ (P.pilot X Y f C z) := lt_of_le_of_ne (P.γ_nonneg _) hg.symm
  rw [P.pilot_eq] at hpos
  simp only [correctionInput, correctionIter, P.pilot_eq]
  exact card_le_of_multiplier_pos (c := P.cutoff f) (γ := P.γ) (k := P.k)
    hch hf hcπ hpair P.ϕ_one P.ρ_le_one P.η_pos P.ρ_one
    hC hC1 (P.cutoff_nonneg hf) hct (P.cutoff_mono hf) P.γ_nonneg P.γ_le_one
    P.γ_antitone P.γ_zero P.gate P.J_pos P.R_rank P.R_var hpos hi

/-- The pilot's incoming-count certificate uses the current step's maximum, before the final
pilot is known. This is the pilot case of [OpenAI2026LogSpace, Lemma 4.3 (3)]. -/
theorem pilotInput_count_le
    (hch : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) {i : ℕ} (hi : i < P.k)
    {z : V} (hg : P.γ (pilotMax (P.cutoff f) P.γ
      (columnDetector X Y P.ϕ P.ρ P.J P.K f) C (i + 1) z) ≠ 0) :
    (#({w | P.δ₁ * f ≤ pilotInput (P.cutoff f) P.γ
      (columnDetector X Y P.ϕ P.ρ P.J P.K f) C i w z} : Finset V) : ℝ) ≤ P.R / f := by
  have hct (t : ℝ) (ht : 0 ≤ t) : P.cutoff f t ≤ t :=
    (P.cutoff_le hf t).trans (max_le (by
      have := mul_nonneg P.θ_pos.le hf.le
      linarith) ht)
  exact card_le_of_pilot_pos hch hf hcπ hpair P.ϕ_one P.ρ_le_one P.η_pos P.ρ_one
    hC hC1 (P.cutoff_nonneg hf) hct P.γ_nonneg P.γ_le_one P.γ_zero
    P.gate P.J_pos P.R_rank P.R_var hi (lt_of_le_of_ne (P.γ_nonneg _) hg.symm)

end Matrix.HierarchyParams

namespace Matrix.CorrectionSamplingLaws

variable {q cπ Cπ Cpair Cvar : ℝ}
  (P : Matrix.FourthRootHierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f π : ℝ} {G : Matrix V V ℝ} {g : V → ℝ} {i : ℕ}

/-- Common channel-to-gate construction. Clients derive the incoming count for their own true
input and deterministic multiplier; the shared code derives ranks and both pair-count laws. -/
noncomputable def ofHierarchyChannels
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hpair : 0 ≤ Cpair) (hi : i < P.k)
    (hcount : ∀ z, g z ≠ 0 →
      (#({w | P.δ₁ * f ≤ G w z} : Finset V) : ℝ) ≤ P.R / f)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0) :
    CorrectionSamplingLaws P.Q G g X Y Y f ((i : ℝ) + 1) where
  I := I
  τ := τ
  h := h
  ρ := P.ρ
  K := P.K
  Kc := ⌈4 * (1 + Cpair * P.R)⌉₊
  η := P.η
  τ₀ := τ₀
  e := P.δ₁
  c := Cpair
  p := Cpair * f
  R := Cpair * P.R
  π := π
  π_pos := hπ
  density := hXY.dens_Y
  Q_support := hQ
  ρ_nonneg := P.ρ_nonneg
  ρ_le_one := P.ρ_le_one
  η_pos := P.η_pos
  ρ_one := P.ρ_one
  τ_nonneg := hτ0
  τ_le_one := hτ1
  τ₀_nonneg := hτ₀
  τ_one := hτ
  I_zero := hI
  c_nonneg := hpair
  row_rank := by
    have hik : (i : ℝ) + 1 ≤ P.k := by exact_mod_cast hi
    have hmass : 1 + Cpair * ((i : ℝ) + 1) / P.η ≤ 1 + Cpair * P.k / P.η := by
      linarith [div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hik hpair) P.η_pos.le]
    calc
      4 * (1 + Cpair * ((i : ℝ) + 1) / P.η) ≤
          160 * (1 + Cpair * ((i : ℝ) + 1) / P.η) := by
            have := P.η_pos
            nlinarith [div_nonneg (mul_nonneg hpair (by positivity : (0 : ℝ) ≤ i + 1))
              (le_of_lt P.η_pos)]
      _ ≤ 160 * (1 + Cpair * P.k / P.η) := mul_le_mul_of_nonneg_left hmass (by norm_num)
      _ ≤ P.K := P.gate
  terminal_pair z w hw := by
    apply Cslib.Probability.card_filter_and_le_of_dens_le
    simpa only [and_comm] using hXY.pair w z hw
  p_nonneg := mul_nonneg hpair hf.le
  source_pair x w hw := by
    exact Cslib.Probability.card_filter_and_le_of_dens_le (by
      simpa only [and_comm] using hYX.pair w x hw)
  incoming_count z hg := by
    have hc := hcount z hg
    have hsub : ({w | P.δ₁ < G w z / f} : Finset V)
        ⊆ ({w | P.δ₁ * f ≤ G w z} : Finset V) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      exact ((lt_div_iff₀ hf).mp hw).le
    have hcount := (show
      (#({w | P.δ₁ < G w z / f} : Finset V) : ℝ) ≤
        #({w | P.δ₁ * f ≤ G w z} : Finset V) by
          exact_mod_cast card_le_card hsub).trans hc
    have hscaled := mul_le_mul_of_nonneg_left ((le_div_iff₀ hf).mp hcount) hpair
    nlinarith
  incoming_rank := Nat.le_ceil _

variable
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hpair : 0 ≤ Cpair) (hi : i < P.k)
    (hcount : ∀ z, g z ≠ 0 →
      (#({w | P.δ₁ * f ≤ G w z} : Finset V) : ℝ) ≤ P.R / f)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0)

/-- The hierarchy-channel laws preserve their `I` parameter. -/
theorem ofHierarchyChannels_I :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).I = I := by
  rfl

/-- The hierarchy-channel laws preserve their `τ` parameter. -/
theorem ofHierarchyChannels_τ :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).τ = τ := by
  rfl

/-- The hierarchy-channel laws preserve their `ρ` parameter. -/
theorem ofHierarchyChannels_ρ :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).ρ = P.ρ := by
  rfl

/-- The hierarchy-channel laws preserve their `Kc` parameter. -/
theorem ofHierarchyChannels_Kc :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).Kc = ⌈4
        * (1 + Cpair * P.R)⌉₊ := by
  rfl

/-- The hierarchy-channel laws retain the supplied preparation cutoff. -/
theorem ofHierarchyChannels_h :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).h = h := by
  rfl

/-- The hierarchy-channel laws retain the hierarchy row rank. -/
theorem ofHierarchyChannels_K :
    (ofHierarchyChannels P X Y hXY hYX hf hπ hpair hi hcount
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).K = P.K := by
  rfl

end Matrix.CorrectionSamplingLaws

namespace Matrix.HierarchyParams.CorrectionSampling

variable {q cπ Cπ Cpair Cvar : ℝ} (P : FourthRootHierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f π : ℝ} {C : Matrix V V ℝ} {i : ℕ}

/-- Build actual correction sampling data from two ordered channel laws and primitive cutoffs.
The incoming count follows from the hierarchy detector, rather than being a supplied field. -/
noncomputable def ofChannels
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0) :
    P.toHierarchyParams.CorrectionSampling X Y X Y Y f C i where
  toCorrectionSamplingLaws := CorrectionSamplingLaws.ofHierarchyChannels P X Y
    hXY hYX hf hπ hpair hi
    (fun z hg => P.toHierarchyParams.correctionInput_count_le X Y
      hXY hf hcπ hpair hC hC1 hi (z := z) hg)
    I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

variable
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0)

/-- The channel constructor uses the true stage rate for its source budget. -/
theorem ofChannels_p :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).p = Cpair * f := by
  rfl

/-- The channel constructor preserves its `I` parameter. -/
theorem ofChannels_I :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).I = I := by
  rfl

/-- The channel constructor preserves its `τ` parameter. -/
theorem ofChannels_τ :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).τ = τ := by
  rfl

/-- The channel constructor preserves its `h` parameter. -/
theorem ofChannels_h :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).h = h := by
  rfl

/-- The channel constructor preserves its `ρ` parameter. -/
theorem ofChannels_ρ :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).ρ = P.ρ := by
  rfl

/-- The channel constructor preserves its `K` parameter. -/
theorem ofChannels_K :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).K = P.K := by
  rfl

/-- The channel constructor preserves its `Kc` parameter. -/
theorem ofChannels_Kc :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).Kc = ⌈4 * (1
        + Cpair * P.R)⌉₊ := by
  rfl

/-- The channel constructor uses the actual terminal pair constant. -/
theorem ofChannels_c :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).c = Cpair := by
  rfl

/-- The channel constructor preserves its `π` parameter. -/
theorem ofChannels_π :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).π = π := by
  rfl

end Matrix.HierarchyParams.CorrectionSampling
