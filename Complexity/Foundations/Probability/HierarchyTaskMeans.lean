/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyTaskData
public import Complexity.Foundations.Probability.DetectedHierarchy
public import Complexity.Foundations.Probability.TrueSampleMeans

/-!
# Actual correction tasks and reward sample means

`CorrectionSampling` records gates and pair-count bounds for sampling a particular actual
correction input. It contains no mean identity or estimator error certificate. The correction
input's nonnegativity and row mass come from `HierarchyParams.correctionInput_bounds`.
The sample uses two independent seed coordinates; its midpoint mask is part of the actual
correction atom. Uniform midpoint density cancels its sampling probability.

The resulting reward sample has the exact mean of the deterministic correction-and-copy
reward update, including a nonprimary copy's weight. This is the correction/reward part of
[OpenAI2026LogSpace, Lemma 7.1, (7.5), printed pp. 34–35], revision `7ef5c0cc`. It is an exact
finite identity, independent of the choice of fourth or eighth moments. Estimates may later
share coordinates, but that does not replace this product-seed true-mean argument.

Preparatory and normalized pilot tasks, routed direct bins, the complete scheduled mean bound,
raw differences, conditional noise, compression and strong recursion remain separate work.
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
structure CorrectionSampling where
  /-- Auxiliary incoming score. -/
  I : ℝ → ℝ → ℝ
  /-- Incoming gate. -/
  τ : ℝ → ℝ
  /-- Preparatory support cutoff. -/
  h : ℝ → ℝ
  /-- Row gate. -/
  ρ : ℝ → ℝ
  /-- Row rank used by the row gate. -/
  K : ℕ
  /-- Incoming rank used by the incoming gate. -/
  Kc : ℕ
  /-- Safe threshold for the row gate. -/
  η : ℝ
  /-- Safe threshold for the incoming gate. -/
  τ₀ : ℝ
  /-- Auxiliary-score support threshold. -/
  e : ℝ
  /-- Terminal pair-count constant. -/
  c : ℝ
  /-- Source pair-count constant. -/
  p : ℝ
  /-- Incoming-count bound on the support of the pilot multiplier. -/
  R : ℝ
  /-- Actual uniform midpoint density, not a nominal rate. -/
  π : ℝ
  π_pos : 0 < π
  density : ∀ z, (dens {t | Zt t z} : ℝ) = π
  Q_support : ∀ v, P.Q v ≠ 0 → h v = 1
  ρ_nonneg : ∀ r, 0 ≤ ρ r
  ρ_le_one : ∀ r, ρ r ≤ 1
  η_pos : 0 < η
  ρ_one : ∀ r, r ≤ η → ρ r = 1
  τ_nonneg : ∀ r, 0 ≤ τ r
  τ_le_one : ∀ r, τ r ≤ 1
  τ₀_nonneg : 0 ≤ τ₀
  τ_one : ∀ r, r ≤ τ₀ → τ r = 1
  I_zero : ∀ v r, v ≤ e → I v r = 0
  c_nonneg : 0 ≤ c
  row_rank : 4 * (1 + c * ((i : ℝ) + 1) / η) ≤ K
  terminal_pair : ∀ z w, w ≠ z →
    (#{t | Zt t z ∧ Z t w} : ℝ) ≤ c * f * #{t | Zt t z}
  p_nonneg : 0 ≤ p
  source_pair : ∀ x w, w ≠ x →
    (#{s | Xs s x ∧ Xs s w} : ℝ) ≤ p * #{s | Xs s x}
  incoming_count : ∀ z, P.γ (P.pilot X Y f C z) ≠ 0 →
    p * #({w | e < P.correctionInput X Y f C i w z / f} : Finset V) ≤ R
  incoming_rank : 4 * (1 + R) ≤ Kc

variable {P X Y Xs Z Zt f C i}

namespace CorrectionSampling

variable (A : P.CorrectionSampling X Y Xs Z Zt f C i)

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
  apply dens_ne_zero.mp
  intro he
  have hπ := A.density z
  rw [he] at hπ
  exact A.π_pos.ne' (by simpa using hπ.symm)

/-- Normalization is proved from the gates on the actual correction input. -/
theorem expect_atom (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (z : V) :
    𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
      (f / A.π) * A.atom σ x z = P.correctionIter X Y f C (i + 1) x z := by
  have hz := A.usage_nonempty z
  have hseq := P.isCorrectionSeq_correctionIter (X := X) (Y := Y) hf hC
  have hm := expect_correctionAtom_unconditioned
    (G := P.correctionInput X Y f C i) (g₀ := fun z => P.γ (P.pilot X Y f C z)) hx hz
    A.Q_support A.ρ_nonneg A.ρ_le_one
    A.η_pos A.ρ_one A.τ_nonneg A.τ_le_one A.τ₀_nonneg A.τ_one A.I_zero hf
    (hseq.input_nonneg hC i x) (hseq.sum_input_le hC1 i x).1 A.c_nonneg A.row_rank
    (A.terminal_pair z) A.p_nonneg (A.source_pair x) (A.incoming_count z) A.incoming_rank
  simp only [atom]
  rw [← mul_expect, hm, A.density, P.correctionIter_succ_apply]
  field_simp [A.π_pos.ne']

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
