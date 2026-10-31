/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.CopyStage
public import Complexity.Foundations.LinearAlgebra.Matrix.PilotCorrection
public import Complexity.Foundations.Probability.ColumnDetector
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# One stage of the hierarchy with detector-chosen multipliers

This file closes the detector interface of `Matrix.copyStage_rates`
[OpenAI2026LogSpace, Section 4.2, Proposition 4.5]. One stage of the correction-and-copy hierarchy
runs the pilot (`Matrix.pilotMax`) with the column detector
`Matrix.columnDetector X Y ϕ ρ J K f` as its column number, for retention channels `X`, `Y`
satisfying `Cslib.Probability.RetentionChannels`. Let `M = M_k` be the final running maximum of the
detector numbers. Then

* the column multiplier of the actual correction is `γ (M y)`, so the cutoffs are
  `φ y t = c t * γ (M y)` for the base cutoff `c t = f Q (t / f)`;
* the copy weights are `r 0 x = 1` and `r j x = κ (M x)` for `j ≠ 0`
  (`Matrix.detectorWeight`) [OpenAI2026LogSpace, (4.22)];
* the overloaded vertices are `O = {x | 1 / 4 < M x}` (`Matrix.overloaded`).

Since `γ` is one through `1 / 2` and `κ` is zero through `1 / 4` and one from `1 / 2`, every
column is either fully corrected or overloaded with all copies active, and only overloaded vertices
have active extra copies. The detector lemma (`Matrix.lt_card_of_lt_columnDetector`) gives each
overloaded column more than `J / (4 C_π f)` entries above `δ₀ f` in some pilot input, and
incidence counting over the pilot inputs, whose rows sum to at most `1, …, k`, gives
`m |O| ≤ |A|` once `2 C_π m k (k + 1) ≤ δ₀ J` [OpenAI2026LogSpace, (4.24)]. So the stage has the
density, intertwining and active-count conclusions of `Matrix.copyStage_rates`
(`Matrix.detectedStage_rates`), with only the channel properties and deterministic constant
conditions as hypotheses.

The pilot also bounds the column counts of the corrected columns
[OpenAI2026LogSpace, Lemma 4.3 (3)]: if the pilot multiplier of a column is positive, its pilot
inputs have at most `R / f` entries at least `δ₁ f` (`Matrix.card_le_of_pilot_pos`), and so do
the inputs of the actual correction when the final multiplier is positive
(`Matrix.card_le_of_multiplier_pos`).

## Main definitions

* `Matrix.detectorWeight`: the copy weights `r` from the running maximum.
* `Matrix.overloaded`: the overloaded vertices.

## Main results

* `Matrix.card_overloaded_le`: the incidence bound `m |O| ≤ |A|`.
* `Matrix.detectedStage_rates`: one stage with detector-chosen multipliers and copies.
* `Matrix.card_le_of_pilot_pos`, `Matrix.card_le_of_multiplier_pos`: column counts of corrected
  columns.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.2, Lemma 4.3 and Proposition 4.5 (preprint, not peer reviewed)
-/

public section

open Finset Cslib.Probability

namespace Matrix

section Definitions

variable {V : Type*}

/-- The **copy weights** from the running maximum `M` of the detector numbers: the primary copy
has weight one, every other copy of `x` weight `κ (M x)` [OpenAI2026LogSpace, (4.22)]. -/
@[expose] noncomputable def detectorWeight {m : ℕ} (κ : ℝ → ℝ) (M : V → ℝ) (j : Fin (m + 1))
    (x : V) : ℝ :=
  if j = 0 then 1 else κ (M x)

/-- The **overloaded** vertices: those whose running maximum of detector numbers exceeds `1 / 4`
[OpenAI2026LogSpace, Proposition 4.5]. -/
@[expose] noncomputable def overloaded [Fintype V] (M : V → ℝ) : Finset V :=
  {x | 1 / 4 < M x}

end Definitions

variable {V ι ι' : Type*} [Fintype V] [Fintype ι] [Fintype ι'] {X : ι → V → Prop}
  {Y : ι' → V → Prop} [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] {ϕ ρ : ℝ → ℝ}
  {J K : ℕ} {f π cπ Cπ Cpair Cvar : ℝ} {c γ : ℝ → ℝ} {C : Matrix V V ℝ}

private theorem sum_fin_succ_cast (k : ℕ) : ∑ i : Fin k, ((i : ℝ) + 1) = k * (k + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) + 1)]
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- **Few overloaded vertices** [OpenAI2026LogSpace, Proposition 4.5]: after `k` pilot steps with
the column detector, if `A` covers the support of `C` and `2 C_π m k (k + 1) ≤ δ₀ J`, then
`m |O| ≤ |A|`. Each overloaded column has more than `J / (4 C_π f)` entries above `δ₀ f` in some
pilot input, and the pilot inputs have row sums at most `1, …, k`. -/
theorem card_overloaded_le (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar) (hf : 0 < f)
    (hCπ : 0 < Cπ) (hϕ0 : ∀ t, 0 ≤ ϕ t) (hϕ1 : ∀ t, ϕ t ≤ 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hϕδ : ∀ t, t ≤ δ₀ → ϕ t = 0) (hρ1 : ∀ t, ρ t ≤ 1) (hJ : 0 < J) (hC0 : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) {A : Finset V} (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A)
    (hc0 : ∀ t, 0 ≤ c t) (hct : ∀ t, 0 ≤ t → c t ≤ t) (hγ0 : ∀ t, 0 ≤ γ t)
    (hγ1 : ∀ t, γ t ≤ 1) {k m : ℕ} (hJm : 2 * Cπ * m * k * (k + 1) ≤ δ₀ * J) :
    m * #(overloaded (pilotMax c γ (columnDetector X Y ϕ ρ J K f) C k)) ≤ #A := by
  set U := columnDetector X Y ϕ ρ J K f
  set O := overloaded (pilotMax c γ U C k)
  have hseq := isCorrectionSeq_pilotCorrection (U := U) hC0 hc0 hct hγ0 hγ1
  -- every overloaded column has many substantial entries in some pilot input
  have hinc : ∀ y ∈ O, ∃ i : Fin k, J / (4 * Cπ * f) <
      #({x | δ₀ * f < pilotInput c γ U C i x y} : Finset V) := by
    intro y hy
    simp only [O, overloaded, mem_filter, mem_univ, true_and] at hy
    obtain ⟨i, hi, hU⟩ := exists_lt_pilotInput_of_lt_pilotMax (by norm_num) hy
    exact ⟨⟨i, hi⟩, lt_card_of_lt_columnDetector hch hf hϕ0 hϕ1 hϕδ hρ1 hJ hU⟩
  rcases O.eq_empty_or_nonempty with hO | hO
  · rw [hO, card_empty, mul_zero]; exact Nat.zero_le _
  have hk : 0 < k := by
    obtain ⟨y, hy⟩ := hO
    obtain ⟨⟨i, hi⟩, -⟩ := hinc y hy
    omega
  set N := ⌊J / (4 * Cπ * f)⌋₊ + 1
  have hN : ∀ y ∈ O, ∃ i : Fin k, N ≤ #({x | δ₀ * f < pilotInput c γ U C i x y} : Finset V) := by
    intro y hy
    obtain ⟨i, hi⟩ := hinc y hy
    exact ⟨i, Nat.succ_le_of_lt ((Nat.floor_lt (by positivity)).mpr hi)⟩
  have hcount := card_mul_le_of_incidences (fun i : Fin k => pilotInput c γ U C i)
    (fun i x y => hseq.input_nonneg hC0 i x y) (fun i => (i : ℝ) + 1)
    (fun i x => (hseq.sum_input_le hC1 i x).1) A
    (fun i x y h => (hseq.input_mem hA i x y h).1) (mul_pos hδ₀ hf) O hN
  rw [sum_fin_succ_cast] at hcount
  have hNJ : J / (4 * Cπ * f) < N := by
    simp only [N]; push_cast; exact Nat.lt_floor_add_one _
  have hJN : (J : ℝ) * δ₀ < 4 * Cπ * N * δ₀ * f := by
    rw [div_lt_iff₀ (by positivity)] at hNJ
    nlinarith
  have hkpos : (0 : ℝ) < k * (k + 1) := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  -- `#O N δ₀ f ≤ #A k (k + 1) / 2` and `2 C_π m k (k + 1) ≤ δ₀ J < 4 C_π N δ₀ f`
  have key : (m : ℝ) * #O * (2 * Cπ * k * (k + 1)) ≤ #A * (2 * Cπ * k * (k + 1)) := by
    have h1 : (m : ℝ) * #O * (2 * Cπ * k * (k + 1)) ≤ #O * (δ₀ * J) := by
      have := mul_le_mul_of_nonneg_left hJm (Nat.cast_nonneg (α := ℝ) #O)
      nlinarith
    have h2 : (#O : ℝ) * (δ₀ * J) ≤ #O * (4 * Cπ * N * δ₀ * f) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (Nat.cast_nonneg _)
    have h3 : (#O : ℝ) * (4 * Cπ * N * δ₀ * f) ≤ #A * (2 * Cπ * k * (k + 1)) := by
      have := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ 4 * Cπ)
      nlinarith
    linarith
  have : (m : ℝ) * #O ≤ #A := le_of_mul_le_mul_right key (by positivity)
  exact_mod_cast this

/-- **Corrected pilot columns have few large entries** [OpenAI2026LogSpace, Lemma 4.3 (3)]. Under
the hypotheses of `Matrix.le_columnDetector` with row-sum bound `k`, if `γ` vanishes from `4 / 5`
on and the pilot multiplier `γ (M_(i+1) y)` of step `i + 1 ≤ k` is positive, then the pilot input
of that step has at most `R / f` entries at least `δ₁ f` in column `y`. -/
theorem card_le_of_pilot_pos (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar) (hf : 0 < f)
    (hcπ : 0 < cπ) (hCpair : 0 ≤ Cpair) {δ₁ : ℝ} (hϕδ : ∀ t, δ₁ ≤ t → ϕ t = 1)
    (hρ1 : ∀ t, ρ t ≤ 1) {η : ℝ} (hη : 0 < η) (hρη : ∀ t, t ≤ η → ρ t = 1)
    (hC0 : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hc0 : ∀ t, 0 ≤ c t)
    (hct : ∀ t, 0 ≤ t → c t ≤ t) (hγ0 : ∀ t, 0 ≤ γ t) (hγ1 : ∀ t, γ t ≤ 1)
    (hγ45 : ∀ t, 4 / 5 ≤ t → γ t = 0) {k : ℕ} (hK : 160 * (1 + Cpair * k / η) ≤ K)
    (hJ : 0 < J) {R : ℝ} (hRJ : 4 * J ≤ cπ * R) (hRvar : 40 * Cvar ≤ cπ * R) {i : ℕ}
    (hi : i < k) {y : V}
    (hpos : 0 < γ (pilotMax c γ (columnDetector X Y ϕ ρ J K f) C (i + 1) y)) :
    (#({x | δ₁ * f ≤ pilotInput c γ (columnDetector X Y ϕ ρ J K f) C i x y} : Finset V) : ℝ) ≤
      R / f := by
  set U := columnDetector X Y ϕ ρ J K f
  have hseq := isCorrectionSeq_pilotCorrection (U := U) hC0 hc0 hct hγ0 hγ1
  by_contra hlt
  have hrow : ∀ x, ∑ w, pilotInput c γ U C i x w ≤ (k : ℝ) := fun x => by
    have := (hseq.sum_input_le hC1 i x).1
    have hik : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
    exact this.trans hik
  have hU : 19 / 20 ≤ U (pilotInput c γ U C i) y :=
    le_columnDetector hch hf hcπ hCpair hϕδ hρ1 hη hρη (hseq.input_nonneg hC0 i) hrow hK hJ hRJ
      hRvar (not_le.mp hlt)
  have hM : 4 / 5 ≤ pilotMax c γ U C (i + 1) y := by
    rw [pilotMax_succ, Pi.sup_apply]
    exact le_sup_of_le_right (by linarith)
  rw [hγ45 _ hM] at hpos
  exact lt_irrefl _ hpos

/-- **Corrected columns have few large entries** [OpenAI2026LogSpace, Lemma 4.3 (3)]: if the
final multiplier `γ (M_k y)` is positive, then for every `i < k` the input of step `i + 1` of the
actual correction, with cutoffs `c t * γ (M_k y)`, has at most `R / f` entries at least `δ₁ f` in
column `y`. -/
theorem card_le_of_multiplier_pos (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hcπ : 0 < cπ) (hCpair : 0 ≤ Cpair) {δ₁ : ℝ} (hϕδ : ∀ t, δ₁ ≤ t → ϕ t = 1)
    (hρ1 : ∀ t, ρ t ≤ 1) {η : ℝ} (hη : 0 < η) (hρη : ∀ t, t ≤ η → ρ t = 1)
    (hC0 : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hc0 : ∀ t, 0 ≤ c t)
    (hct : ∀ t, 0 ≤ t → c t ≤ t) (hcm : Monotone c) (hγ0 : ∀ t, 0 ≤ γ t) (hγ1 : ∀ t, γ t ≤ 1)
    (hγm : Antitone γ) (hγ45 : ∀ t, 4 / 5 ≤ t → γ t = 0) {k : ℕ}
    (hK : 160 * (1 + Cpair * k / η) ≤ K) (hJ : 0 < J) {R : ℝ} (hRJ : 4 * J ≤ cπ * R)
    (hRvar : 40 * Cvar ≤ cπ * R) {y : V}
    (hpos : 0 < γ (pilotMax c γ (columnDetector X Y ϕ ρ J K f) C k y)) {i : ℕ} (hi : i < k) :
    let M := pilotMax c γ (columnDetector X Y ϕ ρ J K f) C k
    (#({x | δ₁ * f ≤ (C + cutoffCorrectionIter (fun y t => c t * γ (M y)) C i * C) x y} :
      Finset V) : ℝ) ≤ R / f := by
  intro M
  set U := columnDetector X Y ϕ ρ J K f
  have hstep : 0 < γ (pilotMax c γ U C (i + 1) y) :=
    hpos.trans_le (hγm (pilotMax_mono (by omega) y))
  refine le_trans ?_ (card_le_of_pilot_pos hch hf hcπ hCpair hϕδ hρ1 hη hρη hC0 hC1 hc0 hct
    hγ0 hγ1 hγ45 hK hJ hRJ hRvar hi hstep)
  refine Nat.cast_le.mpr (card_le_card fun x hx => ?_)
  simp only [mem_filter, mem_univ, true_and] at hx ⊢
  exact hx.trans (cutoffCorrectionIter_le_pilotCorrection hC0 hc0 hct hcm hγ0 hγ1 hγm
    hi.le x y).2

variable [DecidableEq V] [LinearOrder V] {θ L θ₂ : ℝ} {κ χ : ℝ → ℝ} {τ₀ τ₁ q : ℝ}

/-- **One stage with detector-chosen multipliers and copies**
[OpenAI2026LogSpace, Proposition 4.5]. Run `k` pilot steps with the column detector, let `M` be
the final running maximum, correct `C` by `k` steps of the cutoffs `φ y t = c t * γ (M y)`, and
split the residual `D` with the copy weights `Matrix.detectorWeight κ M` and the overloaded set
`Matrix.overloaded M`. If the base cutoff satisfies the hypotheses of the factorial truncation
together with `t - θ₂ f ≤ c t`, `γ` is nonincreasing and one through `1 / 2`, `κ` is zero through
`1 / 4` and one from `1 / 2`, `2 C_π m k (k + 1) ≤ δ₀ J`, and the copy constants are chosen as in
`Matrix.copyStage_rates`, then the copy step has entries at most `f / q`, intertwines with its
projection, and is supported in at most `2 |A|` copies. -/
theorem detectedStage_rates (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hC : C.IsStrictUpperTriangular) (hC0 : ∀ x y, 0 ≤ C x y) (hCf : ∀ x y, C x y ≤ f)
    (hC1 : C *ᵥ 1 ≤ 1) {A : Finset V} (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) (hf : 0 < f)
    (hc0 : ∀ t, 0 ≤ c t) (hcθ : ∀ t, c t ≤ max (t - θ * f) 0) (hcm : Monotone c)
    (hcL : ∀ s t, s ≤ t → c t - c s ≤ L * (t - s)) (hcθ₂ : ∀ t, t - θ₂ * f ≤ c t) (hθ : 0 < θ)
    (hL : 0 ≤ L) (hγ0 : ∀ t, 0 ≤ γ t) (hγ1 : ∀ t, γ t ≤ 1) (hγhalf : ∀ t, t ≤ 1 / 2 → γ t = 1)
    (hκ0 : ∀ t, 0 ≤ κ t) (hκ1 : ∀ t, κ t ≤ 1) (hκq : ∀ t, t ≤ 1 / 4 → κ t = 0)
    (hκhalf : ∀ t, 1 / 2 < t → κ t = 1) (hCπ : 0 < Cπ) (hϕ0 : ∀ t, 0 ≤ ϕ t)
    (hϕ1 : ∀ t, ϕ t ≤ 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hϕδ : ∀ t, t ≤ δ₀ → ϕ t = 0)
    (hρ1 : ∀ t, ρ t ≤ 1) (hJ : 0 < J) {k m : ℕ} (hJm : 2 * Cπ * m * k * (k + 1) ≤ δ₀ * J)
    (hτ₀ : θ₂ * f + f * Real.exp (1 / θ) * (L / θ) ^ k / k.factorial ≤ τ₀)
    (hχ0 : ∀ t, 0 ≤ χ t) (hχ1 : ∀ t, χ t ≤ 1) (hχ₀ : ∀ t, t ≤ τ₀ → χ t = 0)
    (hχ₁ : ∀ t, τ₁ ≤ t → χ t = 1) (hτ₁ : τ₁ ≤ f / q) (hcopies : (k + 1) * f / (m + 1) ≤ f / q) :
    let M := pilotMax c γ (columnDetector X Y ϕ ρ J K f) C k
    let E := cutoffCorrectionIter (fun y t => c t * γ (M y)) C k
    let D := C - E + E * C
    (∀ a b, copyStage χ m (detectorWeight κ M) D a b ≤ f / q) ∧
      copyStage χ m (detectorWeight κ M) D * copyWeight (detectorWeight κ M) =
        copyWeight (detectorWeight κ M) * D ∧
      (∀ a b, copyStage χ m (detectorWeight κ M) D a b ≠ 0 →
        a ∈ copyCover A (overloaded M) ∧ b ∈ copyCover A (overloaded M)) ∧
      #(copyCover (m := m) A (overloaded M)) ≤ 2 * #A := by
  intro M E D
  have hct : ∀ t, 0 ≤ t → c t ≤ t := fun t ht =>
    (hcθ t).trans (max_le (by nlinarith [mul_pos hθ hf]) ht)
  have hO := card_overloaded_le (K := K) (k := k) (m := m) hch hf hCπ hϕ0 hϕ1 hδ₀ hϕδ hρ1 hJ hC0
    hC1 hA hc0 hct hγ0 hγ1 hJm
  refine copyStage_rates (φ := fun y t => c t * γ (M y)) (θ := θ) (L := L) (m := m) (χ := χ)
    (τ₀ := τ₀) (τ₁ := τ₁) (r := detectorWeight κ M) (A := A) (O := overloaded M) (θ₂ := θ₂)
    (q := q) hC hC0 hCf hC1
    (fun y t => mul_nonneg (hc0 t) (hγ0 _))
    (fun y t => (mul_le_of_le_one_right (hc0 t) (hγ1 _)).trans (hcθ t))
    (fun y => hcm.mul_const (hγ0 _))
    (fun y s t hst => ?_) hf hθ hL k hA (fun x => by simp [detectorWeight])
    (fun j x => ?_) (fun j x hj hr => ?_) (fun y => ?_) hτ₀ hχ0 hχ1 hχ₀ hχ₁ hτ₁ hcopies hO
  · -- the cutoffs are `L`-Lipschitz
    have hmono : 0 ≤ c t - c s := sub_nonneg.mpr (hcm hst)
    calc c t * γ (M y) - c s * γ (M y) = γ (M y) * (c t - c s) := by ring
      _ ≤ 1 * (c t - c s) := mul_le_mul_of_nonneg_right (hγ1 _) hmono
      _ ≤ L * (t - s) := by rw [one_mul]; exact hcL s t hst
  · -- the weights lie in `[0, 1]`
    unfold detectorWeight
    split_ifs
    · exact ⟨zero_le_one, le_rfl⟩
    · exact ⟨hκ0 _, hκ1 _⟩
  · -- only overloaded vertices have active extra copies
    simp only [detectorWeight, hj, ↓reduceIte] at hr
    simp only [overloaded, mem_filter, mem_univ, true_and]
    by_contra hle
    exact hr (hκq _ (not_lt.mp hle))
  · -- every column is fully corrected or overloaded with all copies active
    by_cases hg : γ (M y) = 1
    · left
      intro t
      simp only [hg, mul_one]
      exact hcθ₂ t
    · right
      have hhalf : 1 / 2 < M y := by
        by_contra hle
        exact hg (hγhalf _ (not_lt.mp hle))
      refine ⟨fun j => ?_, ?_⟩
      · unfold detectorWeight
        split_ifs
        · rfl
        · exact hκhalf _ hhalf
      · simp only [overloaded, mem_filter, mem_univ, true_and]
        linarith

end Matrix
