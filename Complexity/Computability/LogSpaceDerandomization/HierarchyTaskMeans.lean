/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchyTaskData
public import Complexity.Computability.LogSpaceDerandomization.DetectedHierarchy
public import Complexity.Computability.LogSpaceDerandomization.TrueSampleMeans
public import Complexity.Computability.LogSpaceDerandomization.CorrectionRowRecipe

/-!
# Actual correction tasks and reward sample means

`CorrectionSampling` records gates and pair-count bounds for sampling a particular actual
correction input. It contains no mean identity or estimator error certificate. The correction
input's nonnegativity and row mass come from `HierarchyParams.correctionInput_bounds`.
`CorrectionSampling.withUsage` replaces the usage slice using its actual marginal and
cross-rate pair count while preserving the true channels and gates.
The sample uses two independent seed coordinates; its midpoint mask is part of the actual
correction atom. Uniform midpoint density cancels its sampling probability.

The resulting reward sample has the exact mean of the deterministic correction-and-copy
reward update, including a nonprimary copy's weight. This is the correction/reward part of
[OpenAI2026LogSpace, Lemma 7.1, (7.5), printed pp. 34–35], revision `7ef5c0cc`. It is an exact
finite identity, independent of the choice of fourth or eighth moments. Estimates may later
share coordinates, but that does not replace this product-seed true-mean argument.

The local pilot preparation/normalization family is in
`Complexity/Computability/LogSpaceDerandomization/PilotRowTasks.lean`. Routed direct bins, the
common global task order, complete scheduled mean bound, raw differences, conditional noise,
compression and strong recursion remain separate work.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ} (P : Matrix.HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ Γ Ζ : Type*} [Fintype V] [Fintype ι] [Fintype κ] [Fintype Γ] [Fintype Ζ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  (f : ℝ) (C : Matrix V V ℝ) (i : ℕ)

/-- Primitive sampling/gate conditions for an actual correction task. The row bound used in
normalization is `i + 1`, derived from the concrete iteration rather than supplied here. -/
structure CorrectionSampling extends
    CorrectionSamplingLaws P.Q (P.correctionInput X Y f C i)
      (fun z => P.γ (P.pilot X Y f C z)) Xs Z Zt f ((i : ℝ) + 1)

variable {P X Y Xs Z Zt f C i}

namespace CorrectionSampling

variable (A : P.CorrectionSampling X Y Xs Z Zt f C i)

/-- Change only the usage channel of an actual correction sampler. Its measured density
and cross-rate pair bound suffice; true hierarchy channels and all gates stay fixed. -/
noncomputable def withUsage (U : Ζ → V → Prop) [∀ t v, Decidable (U t v)]
    (π : ℝ) (hπ : 0 < π) (hd : ∀ z, (dens {t | U t z} : ℝ) = π)
    (hp : ∀ z w, w ≠ z →
      (#{t | U t z ∧ Z t w} : ℝ) ≤ A.c * f * #{t | U t z}) :
    P.CorrectionSampling X Y Xs Z U f C i where
  toCorrectionSamplingLaws :=
    { A.toCorrectionSamplingLaws with
      π := π, π_pos := hπ, density := hd, terminal_pair := hp }

section UsageProjections
variable (U : Ζ → V → Prop) [∀ t v, Decidable (U t v)]
    (π : ℝ) (hπ : 0 < π) (hd : ∀ z, (dens {t | U t z} : ℝ) = π)
    (hp : ∀ z w, w ≠ z →
      (#{t | U t z ∧ Z t w} : ℝ) ≤ A.c * f * #{t | U t z})

/-- Usage replacement preserves the I parameter. -/
theorem withUsage_I : (A.withUsage U π hπ hd hp).I = A.I := by
  rfl

/-- Usage replacement preserves the τ parameter. -/
theorem withUsage_τ : (A.withUsage U π hπ hd hp).τ = A.τ := by
  rfl

/-- Usage replacement preserves the h parameter. -/
theorem withUsage_h : (A.withUsage U π hπ hd hp).h = A.h := by
  rfl

/-- Usage replacement preserves the ρ parameter. -/
theorem withUsage_ρ : (A.withUsage U π hπ hd hp).ρ = A.ρ := by
  rfl

/-- Usage replacement preserves the K parameter. -/
theorem withUsage_K : (A.withUsage U π hπ hd hp).K = A.K := by
  rfl

/-- Usage replacement preserves the Kc parameter. -/
theorem withUsage_Kc : (A.withUsage U π hπ hd hp).Kc = A.Kc := by
  rfl

/-- Usage replacement uses the supplied measured density. -/
theorem withUsage_π : (A.withUsage U π hπ hd hp).π = π := by
  rfl

end UsageProjections

/-- Replace the conditioning source while keeping the true channels, ranks and incoming
budget. Only its conditional pair count must fit the existing source constant. The exposed
record update lets concrete recipe clients reduce its unchanged gate projections. -/
@[expose] def withSource (S : Γ → V → Prop) [∀ s v, Decidable (S s v)]
    (hp : ∀ x w, w ≠ x →
      (#{s | S s x ∧ S s w} : ℝ) ≤ A.p * #{s | S s x}) :
    P.CorrectionSampling X Y S Z Zt f C i where
  toCorrectionSamplingLaws := { A.toCorrectionSamplingLaws with source_pair := hp }


/-- The normalized stochastic correction, built from this actual hierarchy input and its
final pilot multiplier. The usage mask is the midpoint channel. -/
@[expose] noncomputable def atom (σ : Γ × Ζ) (x z : V) : ℝ :=
  correctionAtom A.I A.τ A.K A.Kc f (P.correctionInput X Y f C i) Xs Z Zt
    P.Q A.h A.ρ (fun z => P.γ (P.pilot X Y f C z)) σ x z

/-- The two terms in the reward formula, before a conditional average. The direct child
retains the old source; the correction child is evaluated at its sampled midpoint. -/
@[expose] noncomputable def rewardSample (r : ℝ) (W : V → ℝ) (σ : Γ × Ζ) (x : V) : ℝ :=
  r * W x + r * (f / A.π) * ∑ z, A.atom σ x z * W z

include A in
/-- Positive actual density supplies every midpoint conditioning slice. -/
theorem usage_nonempty (z : V) : ({t | Zt t z} : Finset Ζ).Nonempty := by
  exact A.toCorrectionSamplingLaws.usage_nonempty z

/-- Normalization is proved from the gates on the actual correction input. -/
theorem expect_atom (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (z : V) :
    𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
      (f / A.π) * A.atom σ x z = P.correctionIter X Y f C (i + 1) x z := by
  have hseq := P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC
  have hm := A.toCorrectionSamplingLaws.expect_atom_unconditioned hf
    (hseq.input_nonneg hC i) (fun x => (hseq.sum_input_le hC1 i x).1) hx z
  rw [P.correctionIter_succ_apply]
  exact hm

/-- The reward sample's true conditional mean is the actual correction update.
No conditional mean is assumed as a field of `CorrectionSampling`. -/
theorem expect_rewardSample (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (r : ℝ) (W : V → ℝ) :
    𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ), A.rewardSample r W σ x =
      r * (W x + (P.correctionIter X Y f C (i + 1) *ᵥ W) x) := by
  have hΖ : Nonempty Ζ := ⟨(A.usage_nonempty x).choose⟩
  have hs : (({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ)).Nonempty :=
    hx.product univ_nonempty
  have hm (z : V) : (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
      (f / A.π) * A.atom σ x z * W z) = P.correctionIter X Y f C (i + 1) x z * W z := by
    rw [← expect_mul, A.expect_atom hf hC hC1 hx]
  calc
    _ = r * W x + r * ∑ z, (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
        (f / A.π) * A.atom σ x z * W z) := by
      simp only [rewardSample, expect_add_distrib, expect_const hs, ← mul_expect,
        mul_sum, expect_sum_comm, mul_assoc]
    _ = r * W x + r * ∑ z, P.correctionIter X Y f C (i + 1) x z * W z := by
      simp_rw [hm]
    _ = _ := by rw [mul_add]; rfl

/-- On a fixed copy-symbol part this is exactly the deterministic correction-and-copy
reward update, including nonprimary weights. -/
theorem expect_projected_rewardSample [DecidableEq V]
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hi : i + 1 = P.k) (a : Lex (V × Fin (P.m + 1)))
    (hx : ({s | Xs s (ofLex a).1} : Finset Γ).Nonempty) (W : V → ℝ) :
    (𝔼 σ ∈ ({s | Xs s (ofLex a).1} : Finset Γ) ×ˢ (univ : Finset Ζ),
      A.rewardSample (P.weight X Y f C (ofLex a).2 (ofLex a).1) W σ (ofLex a).1) =
      (P.proj X Y f C *ᵥ (W + P.correction X Y f C *ᵥ W)) a := by
  rw [A.expect_rewardSample hf hC hC1 hx, hi, P.correctionIter_last, P.proj_mulVec]
  rfl

end CorrectionSampling

end Matrix.HierarchyParams

namespace Matrix

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V : ℕ → Type*} [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)]
  (e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1)))
  {ι κ : ℕ → Type*} [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
  (X : ∀ l, ι l → V l → Prop) (Y : ∀ l, κ l → V l → Prop)
  [∀ l s v, Decidable (X l s v)] [∀ l t v, Decidable (Y l t v)]
  (S : Matrix (V 0) (V 0) ℝ)

/-- The product-seed sample realizes the reward of the next *actual hierarchy stage*.
The old reward is deterministic here; replacing it and the correction by estimates requires
the separate induction comparisons. No unbiasedness of such estimates is asserted. -/
theorem expect_hierarchyRewardSample {Γ Ζ : Type*} [Fintype Γ] [Fintype Ζ]
    (l i : ℕ) (Xs : Γ → V l → Prop) (Z Zt : Ζ → V l → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    (A : P.CorrectionSampling (X l) (Y l) Xs Z Zt (q⁻¹ ^ l) (hierarchy P e X Y S l) i)
    (hi : i + 1 = P.k) (he : ∀ j a b, e j a < e j b → a < b)
    (hq : 0 < q) (hCπ : 0 < Cπ) (hS : S.IsStrictUpperTriangular)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1) {π : ℕ → ℝ}
    (hch : ∀ j < l, Cslib.Probability.RetentionChannels
      (X j) (Y j) (q⁻¹ ^ j) (π j) cπ Cπ Cpair Cvar)
    (e₀ : V 0 → ℝ) (a : V (l + 1))
    (hx : ({s | Xs s (ofLex (e l a)).1} : Finset Γ).Nonempty) :
    (𝔼 σ ∈ ({s | Xs s (ofLex (e l a)).1} : Finset Γ) ×ˢ (univ : Finset Ζ),
      A.rewardSample
        (P.weight (X l) (Y l) (q⁻¹ ^ l) (hierarchy P e X Y S l)
          (ofLex (e l a)).2 (ofLex (e l a)).1)
        (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) l *ᵥ e₀)
        σ (ofLex (e l a)).1) =
      (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) (l + 1) *ᵥ
        e₀) a := by
  have hinv := hierarchy_invariant (P := P) (e := e) (X := X) (Y := Y)
    he hq hCπ hS hS0 hS1 l hch
  have hf : 0 < q⁻¹ ^ l := by positivity
  rw [A.expect_rewardSample hf hinv.2.1 hinv.2.2.1 hx, hi, P.correctionIter_last,
    rewardTransport_succ_mulVec, hierarchyProj_mulVec, hierarchyCorrection_eq]
  rfl

end Matrix
