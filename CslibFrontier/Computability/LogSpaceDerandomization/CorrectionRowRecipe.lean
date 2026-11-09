/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.CorrectionAtom
import CslibFrontier.Computability.LogSpaceDerandomization.TrueSampleMeans
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Shared correction sampling laws and child-function recipes

Primitive channel and gate laws for the incoming-gated correction atom of
[OpenAI2026LogSpace, Section 5.3, (5.12)–(5.14)], revision `7ef5c0cc`.
The input matrix, row-mass bound and deterministic column multiplier are parameters.
Pilot and actual correction clients supply their own inputs and multipliers; no mean or error
certificate is a field. `CorrectionRowRecipe` computes ranks on the full substituted child table,
and averages the preparatory child on the inherited source and narrower usage slice.
The second channel of Section 7.2 has no broad/narrow importance ratio.

The existing atom law budgets one quarter of the draws to each gate failure, giving the
`1/2` lower bound sufficient for exact clipped normalization. This does not assert the source
Lemma 5.3 stronger `3/4` margin, its canonical smooth cutoffs or their root regularity.
-/

public section

open Finset
open scoped BigOperators

namespace Matrix

variable {V Γ Ζ : Type*} [Fintype V] [Fintype Γ] [Fintype Ζ]
  (Q : ℝ → ℝ) (G : Matrix V V ℝ) (g : V → ℝ)
  (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  (f M : ℝ)

/-- Primitive hypotheses shared by pilot and actual atoms, with an explicit true input and
multiplier. Row mass is checked by the client, not assumed as an aggregate mean. -/
structure CorrectionSamplingLaws where
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
  /-- Positive actual usage density. -/
  π_pos : 0 < π
  /-- Uniform usage density on every terminal vertex. -/
  density : ∀ z, (dens {t | Zt t z} : ℝ) = π
  /-- Preparation equals the gate product on the support of the exact cutoff. -/
  Q_support : ∀ v, Q v ≠ 0 → h v = 1
  /-- Nonnegative row gate on arbitrary ranks. -/
  ρ_nonneg : ∀ r, 0 ≤ ρ r
  /-- Row gate is at most one. -/
  ρ_le_one : ∀ r, ρ r ≤ 1
  /-- Positive safe row threshold. -/
  η_pos : 0 < η
  /-- The row gate is full through its safe threshold. -/
  ρ_one : ∀ r, r ≤ η → ρ r = 1
  /-- Nonnegative incoming gate on arbitrary ranks. -/
  τ_nonneg : ∀ r, 0 ≤ τ r
  /-- Incoming gate is at most one. -/
  τ_le_one : ∀ r, τ r ≤ 1
  /-- The safe incoming threshold is nonnegative. -/
  τ₀_nonneg : 0 ≤ τ₀
  /-- The incoming gate is full through its safe threshold. -/
  τ_one : ∀ r, r ≤ τ₀ → τ r = 1
  /-- Auxiliary scores vanish below the input threshold, independently of the row rank. -/
  I_zero : ∀ v r, v ≤ e → I v r = 0
  /-- Nonnegative terminal pair constant. -/
  c_nonneg : 0 ≤ c
  /-- Row rank makes failure cost at most one quarter on the true input. -/
  row_rank : 4 * (1 + c * M / η) ≤ K
  /-- Cross-rate terminal pair count, conditional on the usage hit. -/
  terminal_pair : ∀ z w, w ≠ z →
    (#{t | Zt t z ∧ Z t w} : ℝ) ≤ c * f * #{t | Zt t z}
  /-- Nonnegative source pair constant. -/
  p_nonneg : 0 ≤ p
  /-- Source pair count conditional on the inherited source hit. -/
  source_pair : ∀ x w, w ≠ x →
    (#{s | Xs s x ∧ Xs s w} : ℝ) ≤ p * #{s | Xs s x}
  /-- True input support bound only where the deterministic multiplier is nonzero. -/
  incoming_count : ∀ z, g z ≠ 0 →
    p * #({w | e < G w z / f} : Finset V) ≤ R
  /-- Incoming rank makes failure cost at most one quarter. -/
  incoming_rank : 4 * (1 + R) ≤ Kc

namespace CorrectionSamplingLaws

variable {Q G g Xs Z Zt f M}
  (A : CorrectionSamplingLaws Q G g Xs Z Zt f M)

include A in
/-- Positive usage density makes every terminal conditioning slice nonempty. -/
theorem usage_nonempty (y : V) : ({t | Zt t y} : Finset Ζ).Nonempty := by
  apply dens_ne_zero.mp
  intro he
  have hπ := A.density y
  rw [he] at hπ
  exact A.π_pos.ne' (by simpa using hπ.symm)

/-- The true conditional mean follows from primitive gate and pair-count laws. -/
theorem expect_atom (hf : 0 < f) (hG : ∀ x y, 0 ≤ G x y)
    (hGM : ∀ x, ∑ y, G x y ≤ M) {x : V}
    (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ),
      correctionAtom A.I A.τ A.K A.Kc f G Xs Z Zt Q A.h A.ρ g σ x y) =
      Q (G x y / f) * g y :=
  expect_correctionAtom hx (A.usage_nonempty y) A.Q_support A.ρ_nonneg A.ρ_le_one
    A.η_pos A.ρ_one A.τ_nonneg A.τ_le_one A.τ₀_nonneg A.τ_one A.I_zero hf
    (hG x) (hGM x) A.c_nonneg A.row_rank (A.terminal_pair y) A.p_nonneg
    (A.source_pair x) (A.incoming_count y) A.incoming_rank

/-- Integrating usage membership cancels its actual density, rather than a nominal rate. -/
theorem expect_atom_unconditioned (hf : 0 < f) (hG : ∀ x y, 0 ≤ G x y)
    (hGM : ∀ x, ∑ y, G x y ≤ M) {x : V}
    (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
      (f / A.π) * correctionAtom A.I A.τ A.K A.Kc f G Xs Z Zt Q A.h A.ρ g σ x y) =
      f * Q (G x y / f) * g y := by
  have hm := expect_correctionAtom_unconditioned hx (A.usage_nonempty y)
    A.Q_support A.ρ_nonneg A.ρ_le_one A.η_pos A.ρ_one A.τ_nonneg A.τ_le_one
    A.τ₀_nonneg A.τ_one A.I_zero hf (hG x) (hGM x) A.c_nonneg A.row_rank
    (A.terminal_pair y) A.p_nonneg (A.source_pair x) (A.incoming_count y) A.incoming_rank
  rw [← mul_expect, hm, A.density]
  field_simp [A.π_pos.ne']

end CorrectionSamplingLaws

namespace CorrectionRowRecipe

variable {V Γ Ζ : Type*} [Fintype V] [Fintype Γ] [Fintype Ζ]

/-- Direct plus product input. The right row is evaluated at the midpoint, releasing the
parent source; no old source or selected endpoint is a child parameter. -/
@[expose] def input (direct left right : Matrix V V ℝ) : Matrix V V ℝ :=
  fun x y => direct x y + ∑ z, left x z * right z y

/-- Conditional normalizer of an arbitrary preparatory child; all channel suffixes are inherited. -/
@[expose] noncomputable def normalizer (Xs : Γ → V → Prop) (Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Zt t v)]
    (prep : Γ × Ζ → Matrix V V ℝ) (x y : V) : ℝ :=
  𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ), prep σ x y

/-- The narrower second signal, with external scale and zero extension, has no importance ratio. -/
@[expose] noncomputable def secondChannel (Xs : Γ → V → Prop) (Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Zt t v)] (ζ : ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (σ : Γ × Ζ) (x y : V) : ℝ :=
  if Zt σ.2 y then ζ * normalizer Xs Zt prep x y else 0

/-- Incoming-gate preparation on the completed raw child, before any port filtering. -/
@[expose] noncomputable def preparation (I : ℝ → ℝ → ℝ) (τ h ρ : ℝ → ℝ)
    (K Kc : ℕ) (f : ℝ) (Xs : Γ → V → Prop) (Z : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)]
    (input : Matrix V V ℝ) (σ : Γ × Ζ) : Matrix V V ℝ :=
  correctionPrep I τ K Kc f input h ρ {w | Xs σ.1 w} {w | Z σ.2 w}

/-- Normalization on arbitrary child functions. The scalar cutoff is supplied already bounded;
the incoming scores and ranks still inspect every original raw entry. -/
@[expose] noncomputable def normalized (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ)
    (K Kc : ℕ) (f : ℝ) (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    (input : Matrix V V ℝ) (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) : ℝ :=
  if Zt σ.2 y then
    Q (input x y / f) * (rowGate ρ K f input {w | Z σ.2 w} x *
      incomingGate I τ K Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y) /
      max (1 / 2) (min 1 (normalizer Xs Zt prep x y)) * γ (maximum y)
  else 0

/-- Uniform range for arbitrary raw, preparation and vector children. The clipped denominator
stays positive even for negative preparatory estimates; no mean or error premise is used. -/
theorem normalized_mem_Icc (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ)
    (K Kc : ℕ) (f : ℝ) (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    {B : ℝ} (hB : 0 ≤ B) (hQ0all : ∀ d, 0 ≤ Q d) (hQ1all : ∀ d, Q d ≤ B)
    (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1)
    (hγ0 : ∀ r, 0 ≤ γ r) (hγ1 : ∀ r, γ r ≤ 1)
    (input : Matrix V V ℝ) (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) :
    normalized I τ ρ Q γ K Kc f Xs Z Zt input prep maximum σ x y ∈ Set.Icc 0 (2 * B) := by
  have hQ0 := hQ0all (input x y / f)
  have hQ1 := hQ1all (input x y / f)
  have hg0 : 0 ≤ rowGate ρ K f input {w | Z σ.2 w} x *
      incomingGate I τ K Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y :=
    mul_nonneg (hρ0 _) (hτ0 _)
  have hg1 : rowGate ρ K f input {w | Z σ.2 w} x *
      incomingGate I τ K Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y ≤ 1 :=
    (mul_le_mul_of_nonneg_right (hρ1 _) (hτ0 _)).trans
      (by simpa only [one_mul] using hτ1 _)
  have hc : (1 / 2 : ℝ) ≤ max (1 / 2)
      (min 1 (normalizer Xs Zt prep x y)) := le_max_left _ _
  have hc0 : 0 < max (1 / 2) (min 1 (normalizer Xs Zt prep x y)) := by linarith
  unfold normalized
  split_ifs
  · have hn0 := div_nonneg (mul_nonneg hQ0 hg0) hc0.le
    have hn1 : Q (input x y / f) *
        (rowGate ρ K f input {w | Z σ.2 w} x *
          incomingGate I τ K Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y) /
        max (1 / 2) (min 1 (normalizer Xs Zt prep x y)) ≤ 2 * B := by
      apply (div_le_iff₀ hc0).mpr
      calc
        _ ≤ Q (input x y / f) := mul_le_of_le_one_right hQ0 hg1
        _ ≤ B := hQ1
        _ ≤ _ := by nlinarith [hB]
    exact ⟨mul_nonneg hn0 (hγ0 _),
      (mul_le_of_le_one_right hn0 (hγ1 _)).trans hn1⟩
  · exact ⟨le_rfl, mul_nonneg (by norm_num) hB⟩

omit [Fintype Γ] [Fintype Ζ] in
/-- Preparatory estimates also stay in the gate range when the support cutoff does. -/
theorem preparation_mem_Icc (I : ℝ → ℝ → ℝ) (τ h ρ : ℝ → ℝ)
    (K Kc : ℕ) (f : ℝ) (Xs : Γ → V → Prop) (Z : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)]
    (hh : ∀ d, h d ∈ Set.Icc 0 1) (hρ : ∀ r, ρ r ∈ Set.Icc 0 1)
    (hτ : ∀ r, τ r ∈ Set.Icc 0 1)
    (input : Matrix V V ℝ) (σ : Γ × Ζ) (x y : V) :
    preparation I τ h ρ K Kc f Xs Z input σ x y ∈ Set.Icc 0 1 := by
  exact ⟨mul_nonneg (mul_nonneg (hh _).1 (hρ _).1) (hτ _).1,
    (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right (hh _).2 (hρ _).1).trans
        (by simpa only [one_mul] using (hρ _).2)) (hτ _).1).trans
          (by simpa only [one_mul] using (hτ _).2)⟩

section Support

variable (I : ℝ → ℝ → ℝ) (τ ρ Q γ : ℝ → ℝ) (K Kc : ℕ) (f : ℝ)
  (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  (input : Matrix V V ℝ) (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
  (σ : Γ × Ζ)

/-- Arbitrary preparatory/vector children cannot enlarge the row support of the first gate. -/
theorem card_filter_normalized_row_ne_zero_lt (x : V) (hK : 0 < K) {e g : ℝ}
    (he : 0 ≤ e) (hQ : ∀ d, d ≤ e → Q d = 0) (hg : g ≤ e)
    (hρ : ∀ r, g ≤ r → ρ r = 0) :
    #{y ∈ ({w | Z σ.2 w} : Finset V) |
      normalized I τ ρ Q γ K Kc f Xs Z Zt input prep maximum σ x y ≠ 0} < K := by
  refine lt_of_le_of_lt (card_le_card fun y hy => ?_)
    (card_filter_mul_rowGate_ne_zero_lt (G := input) (a := f)
      {w | Z σ.2 w} x hK he hQ hg hρ)
  rw [mem_filter] at hy ⊢
  refine ⟨hy.1, fun h0 => hy.2 ?_⟩
  unfold normalized
  split_ifs
  · rw [← mul_assoc, h0, zero_mul, zero_div, zero_mul]
  · rfl

/-- The incoming rank on the completed raw table bounds column support after any substitutions. -/
theorem card_filter_normalized_col_ne_zero_lt (y : V) (hKc : 0 < Kc)
    (hIQ : ∀ v r, Q v ≠ 0 → ρ r ≠ 0 → I v r = 1)
    {g : ℝ} (hg : g ≤ 1) (hτ : ∀ r, g ≤ r → τ r = 0) :
    #{x ∈ ({w | Xs σ.1 w} : Finset V) |
      normalized I τ ρ Q γ K Kc f Xs Z Zt input prep maximum σ x y ≠ 0} < Kc := by
  by_contra hle
  rw [not_lt] at hle
  have hgate : incomingGate I τ K Kc f input
      {w | Xs σ.1 w} {w | Z σ.2 w} y = 0 := by
    refine incomingGate_eq_zero hKc hg hτ (hle.trans (card_le_card fun x hx => ?_))
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, le_of_eq (hIQ _ _ (fun hQ => hx.2 ?_) (fun hρ => hx.2 ?_)).symm⟩
    · simp [normalized, hQ]
    · simp [normalized, rowGate, hρ]
  obtain ⟨x, hx⟩ := card_pos.mp (hKc.trans_le hle)
  rw [mem_filter] at hx
  exact hx.2 (by simp [normalized, hgate])

end Support

end CorrectionRowRecipe
end Matrix
