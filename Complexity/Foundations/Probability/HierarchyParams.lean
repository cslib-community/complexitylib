/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.DetectedStage
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Algebraic-stage parameters for the correction-and-copy hierarchy

One stage of the hierarchy of the OpenAI preprint (2026-09-23), Section 4 [OpenAI2026LogSpace],
is driven by finitely many constants and cutoff functions: the correction ramp `Q` with its
thresholds `θ ≤ θ₂` and Lipschitz constant `L`, the iteration count `k*`, the number of copies
`D₀ = m + 1`, the copy thresholds `τ₀ < τ₁`, the detector thresholds `δ₀ < δ₁` and `η`, the
detector ranks `J` and `K`, the count threshold `R*`, and the cutoffs `ϕ`, `ρ`, `γ`, `κ`, `χ`.
`Matrix.HierarchyParams q cπ Cπ Cpair Cvar` bundles the reduced algebraic conditions used by the
stage lemmas, together with additional detector-cutoff data, for the density divisor `q` and the
channel constants of
`Cslib.Probability.RetentionChannels`. All of them are fixed before the stage: the thresholds are
relative to the rate `f`, so the same parameters serve every stage.

**Reduced algebraic-stage existence** (`Matrix.HierarchyParams.nonempty`). For every `q > 0`
and channel constants with `c_π > 0`, there are parameters satisfying this bundle. Following
[OpenAI2026LogSpace, Remark 4.6], the
choice follows the order of the preprint: first `θ = θ₂ = 1 / (4q)` and the hard ramp
`Q t = max (t - θ) 0`, then `k*` from the factorial bound (`Matrix.exists_factorial_bound_le`),
then `m = ⌈q⌉₊ (k* + 1)` and `D₀ = m + 1`, then `J` from (4.24), and finally `K` and `R*`
from Lemma 4.3.

This witness establishes only the reduced algebraic-stage package encoded here. It does not
satisfy the preprint's full threshold ladder or the regularity package needed for later
estimation. Besides the hard ramp `Q`, the cutoffs `χ`, `ϕ`, `ρ`, `γ` and `κ` are discontinuous
steps. The additional threshold conditions and root/complement regularity for `Q` and these
cutoffs remain open; replacing `Q` alone does not supply them.

**One stage** (`Matrix.HierarchyParams.stage_rates`). At rate `f > 0`, the stage uses the cutoffs
`c t = f Q (t / f)` and `χ (t / f)` (`Matrix.HierarchyParams.cutoff`,
`Matrix.HierarchyParams.copyCutoff`), the detector-driven pilot
(`Matrix.HierarchyParams.pilot`), the corrected residual `D`
(`Matrix.HierarchyParams.residual`) and the copy weights (`Matrix.HierarchyParams.weight`). The
next transition matrix `Matrix.HierarchyParams.next`, indexed by `Lex (V × Fin (m + 1))`, has
entries at most `f / q`, is supported in at most twice as many vertices, intertwines with the
weighted projection, and is again strictly upper triangular and substochastic. The only
hypotheses are those on the input matrix and the channel interface.

## Main definitions

* `Matrix.HierarchyParams`: the reduced algebraic-stage parameters and cutoff data.
* `Matrix.HierarchyParams.pilot`, `Matrix.HierarchyParams.residual`,
  `Matrix.HierarchyParams.weight`, `Matrix.HierarchyParams.next`: one stage.

## Main results

* `Matrix.HierarchyParams.nonempty`: reduced algebraic-stage parameters exist for every `q > 0`.
* `Matrix.HierarchyParams.stage_rates`: one stage satisfies the per-stage rates.
* `Matrix.HierarchyParams.next_isStrictUpperTriangular`, `Matrix.HierarchyParams.next_nonneg`,
  `Matrix.HierarchyParams.next_mulVec_one_le`: the next stage is again a valid input.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Lemma 4.1, Lemma 4.3, Proposition 4.5 and Remark 4.6 (preprint, not peer reviewed)
-/

public section

open Finset Cslib.Probability

namespace Matrix

/-- **The reduced algebraic-stage parameters** of the hierarchy, for the density divisor `q` and
the channel constants `cπ, Cπ, Cpair, Cvar`, together with additional detector-cutoff data
[OpenAI2026LogSpace, Sections 4.1–4.4 and Remark 4.6]. Thresholds of the ramp `Q` and of the
copy cutoff `χ` are relative to the rate `f`. The preprint's full threshold ladder and later
root/complement regularity for `Q` and all the step cutoffs are not part of this bundle. -/
structure HierarchyParams (q cπ Cπ Cpair Cvar : ℝ) where
  /-- The correction ramp: the cutoff at rate `f` is `t ↦ f Q (t / f)`. -/
  Q : ℝ → ℝ
  /-- The threshold below which `Q` vanishes. -/
  θ : ℝ
  /-- The threshold that `Q` leaves behind at most. -/
  θ₂ : ℝ
  /-- A Lipschitz constant of `Q`. -/
  L : ℝ
  /-- The number of correction iterations `k*`. -/
  k : ℕ
  /-- The number of extra copies, `D₀ - 1`. -/
  m : ℕ
  /-- The copy threshold up to which entries stay with the primary copy, relative to the rate. -/
  τ₀ : ℝ
  /-- The copy threshold from which entries are split evenly, relative to the rate. -/
  τ₁ : ℝ
  /-- The copy cutoff. -/
  χ : ℝ → ℝ
  /-- The detector score threshold through which the score vanishes. -/
  δ₀ : ℝ
  /-- The detector score threshold from which the score is one. -/
  δ₁ : ℝ
  /-- The detector score cutoff. -/
  ϕ : ℝ → ℝ
  /-- The row-gate threshold. -/
  η : ℝ
  /-- The row-gate cutoff. -/
  ρ : ℝ → ℝ
  /-- The column-multiplier cutoff, applied to the running maximum of detector numbers. -/
  γ : ℝ → ℝ
  /-- The copy-weight cutoff, applied to the running maximum of detector numbers. -/
  κ : ℝ → ℝ
  /-- The detector rank `J` of the column trials. -/
  J : ℕ
  /-- The rank `K` of the row gates. -/
  K : ℕ
  /-- The column-count threshold `R*` of Lemma 4.3. -/
  R : ℝ
  Q_nonneg : ∀ t, 0 ≤ Q t
  Q_le : ∀ t, Q t ≤ max (t - θ) 0
  le_Q : ∀ t, t - θ₂ ≤ Q t
  Q_mono : Monotone Q
  Q_lipschitz : ∀ s t, s ≤ t → Q t - Q s ≤ L * (t - s)
  θ_pos : 0 < θ
  L_nonneg : 0 ≤ L
  truncation : θ₂ + Real.exp (1 / θ) * (L / θ) ^ k / k.factorial ≤ τ₀
  χ_nonneg : ∀ t, 0 ≤ χ t
  χ_le_one : ∀ t, χ t ≤ 1
  χ_zero : ∀ t, t ≤ τ₀ → χ t = 0
  χ_one : ∀ t, τ₁ ≤ t → χ t = 1
  τ₁_le : τ₁ ≤ 1 / q
  copies : ((k : ℝ) + 1) / (m + 1) ≤ 1 / q
  δ₀_pos : 0 < δ₀
  ϕ_nonneg : ∀ t, 0 ≤ ϕ t
  ϕ_le_one : ∀ t, ϕ t ≤ 1
  ϕ_zero : ∀ t, t ≤ δ₀ → ϕ t = 0
  ϕ_one : ∀ t, δ₁ ≤ t → ϕ t = 1
  η_pos : 0 < η
  ρ_le_one : ∀ t, ρ t ≤ 1
  ρ_one : ∀ t, t ≤ η → ρ t = 1
  γ_nonneg : ∀ t, 0 ≤ γ t
  γ_le_one : ∀ t, γ t ≤ 1
  γ_antitone : Antitone γ
  γ_one : ∀ t, t ≤ 1 / 2 → γ t = 1
  γ_zero : ∀ t, 4 / 5 ≤ t → γ t = 0
  κ_nonneg : ∀ t, 0 ≤ κ t
  κ_le_one : ∀ t, κ t ≤ 1
  κ_zero : ∀ t, t ≤ 1 / 4 → κ t = 0
  κ_one : ∀ t, 1 / 2 < t → κ t = 1
  J_pos : 0 < J
  rank : 2 * Cπ * m * k * (k + 1) ≤ δ₀ * J
  gate : 160 * (1 + Cpair * k / η) ≤ K
  R_rank : 4 * J ≤ cπ * R
  R_var : 40 * Cvar ≤ cπ * R

namespace HierarchyParams

variable {q cπ Cπ Cpair Cvar : ℝ}

/-- The step `0` through `a`, `1` above. -/
private noncomputable def up (a t : ℝ) : ℝ := if t ≤ a then 0 else 1

/-- The step `1` through `a`, `0` above. -/
private noncomputable def down (a t : ℝ) : ℝ := if t ≤ a then 1 else 0

private theorem up_nonneg (a t : ℝ) : 0 ≤ up a t := by unfold up; split_ifs <;> norm_num
private theorem up_le_one (a t : ℝ) : up a t ≤ 1 := by unfold up; split_ifs <;> norm_num
private theorem up_of_le {a t : ℝ} (h : t ≤ a) : up a t = 0 := by simp only [up, h, ↓reduceIte]
private theorem up_of_lt {a t : ℝ} (h : a < t) : up a t = 1 := by
  simp only [up, not_le.mpr h, ↓reduceIte]
private theorem down_nonneg (a t : ℝ) : 0 ≤ down a t := by unfold down; split_ifs <;> norm_num
private theorem down_le_one (a t : ℝ) : down a t ≤ 1 := by unfold down; split_ifs <;> norm_num
private theorem down_of_le {a t : ℝ} (h : t ≤ a) : down a t = 1 := by
  simp only [down, h, ↓reduceIte]
private theorem down_of_lt {a t : ℝ} (h : a < t) : down a t = 0 := by
  simp only [down, not_le.mpr h, ↓reduceIte]
private theorem down_antitone (a : ℝ) : Antitone (down a) := fun s t hst => by
  unfold down; split_ifs with h1 h2 <;> first | exact absurd (hst.trans h1) h2 | norm_num

/-- **Reduced algebraic-stage parameters exist**: for every density divisor `q > 0` and channel
constants with `c_π > 0`, there are parameters satisfying this bundle. Following
[OpenAI2026LogSpace, Remark 4.6], they are chosen
in the order of the preprint: the ramp, then `k*` by factorial truncation, then the copies, then
the detector ranks `J` and `K`, then `R*`. The witness uses a hard ramp and step cutoffs;
the full threshold ladder and later-estimation regularity for all cutoffs and their relevant
complements remain open. -/
theorem nonempty (hq : 0 < q) (hcπ : 0 < cπ) :
    Nonempty (HierarchyParams q cπ Cπ Cpair Cvar) := by
  have hq0 : 0 < q := hq
  set θ : ℝ := 1 / (4 * q)
  have hθ : 0 < θ := by positivity
  obtain ⟨k, hk⟩ := exists_factorial_bound_le θ 1 (δ := 1 / (4 * q)) (by positivity)
  set m : ℕ := ⌈q⌉₊ * (k + 1)
  set J : ℕ := ⌈4 * Cπ * m * k * (k + 1)⌉₊ + 1
  set K : ℕ := ⌈160 * (1 + Cpair * k / (1 / 2))⌉₊
  set R : ℝ := (4 * J + 40 * |Cvar|) / cπ
  have hR : 4 * (J : ℝ) + 40 * |Cvar| ≤ cπ * R := by
    simp only [R]; rw [mul_div_cancel₀ _ hcπ.ne']
  refine ⟨{
    Q := fun t => max (t - θ) 0
    θ := θ
    θ₂ := θ
    L := 1
    k := k
    m := m
    τ₀ := 1 / (2 * q)
    τ₁ := 1 / q
    χ := up (1 / (2 * q))
    δ₀ := 1 / 2
    δ₁ := 1
    ϕ := up (1 / 2)
    η := 1 / 2
    ρ := down (1 / 2)
    γ := down (1 / 2)
    κ := up (1 / 4)
    J := J
    K := K
    R := R
    Q_nonneg := fun _ => le_max_right _ _
    Q_le := fun _ => le_rfl
    le_Q := fun _ => le_max_left _ _
    Q_mono := fun _ _ h => max_le_max (by linarith) le_rfl
    Q_lipschitz := fun s t _ => ?_
    θ_pos := hθ
    L_nonneg := zero_le_one
    truncation := ?_
    χ_nonneg := up_nonneg _
    χ_le_one := up_le_one _
    χ_zero := fun _ h => up_of_le h
    χ_one := fun t h => up_of_lt (lt_of_lt_of_le (by
      rw [div_lt_div_iff_of_pos_left one_pos (by positivity) hq0]; linarith) h)
    τ₁_le := le_rfl
    copies := ?_
    δ₀_pos := by norm_num
    ϕ_nonneg := up_nonneg _
    ϕ_le_one := up_le_one _
    ϕ_zero := fun _ h => up_of_le h
    ϕ_one := fun t h => up_of_lt (by linarith)
    η_pos := by norm_num
    ρ_le_one := down_le_one _
    ρ_one := fun _ h => down_of_le h
    γ_nonneg := down_nonneg _
    γ_le_one := down_le_one _
    γ_antitone := down_antitone _
    γ_one := fun _ h => down_of_le h
    γ_zero := fun t h => down_of_lt (by linarith)
    κ_nonneg := up_nonneg _
    κ_le_one := up_le_one _
    κ_zero := fun _ h => up_of_le h
    κ_one := fun t h => up_of_lt (by linarith)
    J_pos := Nat.succ_pos _
    rank := ?_
    gate := Nat.le_ceil _
    R_rank := by linarith [abs_nonneg Cvar]
    R_var := by linarith [le_abs_self Cvar] }⟩
  · have := le_max_left (s - θ) 0
    have := le_max_right (s - θ) 0
    have : max (t - θ) 0 ≤ max (s - θ) 0 + (t - s) := max_le (by linarith) (by linarith)
    linarith
  · have h2 : (1 : ℝ) / (2 * q) = 1 / (4 * q) + 1 / (4 * q) := by field_simp; norm_num
    rw [h2]
    exact add_le_add le_rfl hk
  · rw [div_le_div_iff₀ (by positivity) hq0, one_mul]
    have hqc : q ≤ ⌈q⌉₊ := Nat.le_ceil q
    have : (m : ℝ) = ⌈q⌉₊ * (k + 1) := by simp only [m]; push_cast; ring
    rw [this]
    nlinarith [(Nat.cast_nonneg (α := ℝ) k)]
  · have h1 : 4 * Cπ * m * k * (k + 1) ≤ (J : ℝ) := by
      simp only [J]; push_cast
      exact (Nat.le_ceil _).trans (by linarith)
    linarith

variable (P : HierarchyParams q cπ Cπ Cpair Cvar)

section Stage

variable {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop) [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (f : ℝ) (C : Matrix V V ℝ)

/-- The correction cutoff `t ↦ f Q (t / f)` at rate `f`. -/
noncomputable def cutoff (t : ℝ) : ℝ := f * P.Q (t / f)

/-- The copy cutoff `t ↦ χ (t / f)` at rate `f`. -/
noncomputable def copyCutoff (t : ℝ) : ℝ := P.χ (t / f)

/-- The final running maximum of the detector numbers after the `k*` pilot steps at rate `f`. -/
noncomputable def pilot : V → ℝ :=
  pilotMax (P.cutoff f) P.γ (columnDetector X Y P.ϕ P.ρ P.J P.K f) C P.k

/-- The actual correction `E = E_(k*)` with the column multipliers `γ (M y)`. -/
noncomputable def correction : Matrix V V ℝ :=
  cutoffCorrectionIter (fun y t => P.cutoff f t * P.γ (P.pilot X Y f C y)) C P.k

/-- The corrected residual `D = C - E + E C`. -/
noncomputable def residual : Matrix V V ℝ :=
  C - P.correction X Y f C + P.correction X Y f C * C

theorem residual_eq : P.residual X Y f C =
    C - P.correction X Y f C + P.correction X Y f C * C := by rfl

/-- The copy weights `r` of the stage (4.22). -/
noncomputable def weight : Fin (P.m + 1) → V → ℝ :=
  detectorWeight P.κ (P.pilot X Y f C)

/-- **The next transition matrix** `C⁺`, indexed by the lexicographically ordered copies. -/
noncomputable def next : Matrix (Lex (V × Fin (P.m + 1))) (Lex (V × Fin (P.m + 1))) ℝ :=
  (copyStage (P.copyCutoff f) P.m (P.weight X Y f C) (P.residual X Y f C)).submatrix ofLex ofLex

/-- **The projection** `P_r` from the copies to their parents, weighted by the copy weights. -/
noncomputable def proj [DecidableEq V] : Matrix (Lex (V × Fin (P.m + 1))) V ℝ :=
  (copyWeight (P.weight X Y f C)).submatrix ofLex id

variable {X Y f C}

theorem cutoff_nonneg (hf : 0 < f) (t : ℝ) : 0 ≤ P.cutoff f t :=
  mul_nonneg hf.le (P.Q_nonneg _)

theorem cutoff_le (hf : 0 < f) (t : ℝ) : P.cutoff f t ≤ max (t - P.θ * f) 0 := by
  have h := P.Q_le (t / f)
  calc P.cutoff f t = f * P.Q (t / f) := rfl
    _ ≤ f * max (t / f - P.θ) 0 := mul_le_mul_of_nonneg_left h hf.le
    _ = max (t - P.θ * f) 0 := by
        rw [mul_max_of_nonneg _ _ hf.le, mul_zero, mul_sub, mul_div_cancel₀ _ hf.ne', mul_comm]

theorem le_cutoff (hf : 0 < f) (t : ℝ) : t - P.θ₂ * f ≤ P.cutoff f t := by
  have h := mul_le_mul_of_nonneg_left (P.le_Q (t / f)) hf.le
  rw [mul_sub, mul_div_cancel₀ _ hf.ne'] at h
  simp only [cutoff]; linarith

theorem cutoff_mono (hf : 0 < f) : Monotone (P.cutoff f) := fun _ _ h =>
  mul_le_mul_of_nonneg_left (P.Q_mono (div_le_div_of_nonneg_right h hf.le)) hf.le

theorem cutoff_lipschitz (hf : 0 < f) (s t : ℝ) (h : s ≤ t) :
    P.cutoff f t - P.cutoff f s ≤ P.L * (t - s) := by
  have hl := P.Q_lipschitz (s / f) (t / f) (div_le_div_of_nonneg_right h hf.le)
  calc P.cutoff f t - P.cutoff f s = f * (P.Q (t / f) - P.Q (s / f)) := by
        simp only [cutoff]; ring
    _ ≤ f * (P.L * (t / f - s / f)) := mul_le_mul_of_nonneg_left hl hf.le
    _ = P.L * (t - s) := by field_simp

private theorem phi_nonneg (hf : 0 < f) (y : V) (t : ℝ) :
    0 ≤ P.cutoff f t * P.γ (P.pilot X Y f C y) :=
  mul_nonneg (P.cutoff_nonneg hf t) (P.γ_nonneg _)

private theorem phi_le (hf : 0 < f) (y : V) (t : ℝ) :
    P.cutoff f t * P.γ (P.pilot X Y f C y) ≤ max (t - P.θ * f) 0 :=
  (mul_le_of_le_one_right (P.cutoff_nonneg hf t) (P.γ_le_one _)).trans (P.cutoff_le hf t)

private theorem phi_mono (hf : 0 < f) (y : V) :
    Monotone fun t => P.cutoff f t * P.γ (P.pilot X Y f C y) :=
  (P.cutoff_mono hf).mul_const (P.γ_nonneg _)

private theorem θf_nonneg (hf : 0 < f) : 0 ≤ P.θ * f := by have := P.θ_pos; positivity

/-- **One stage with the bundled constants** [OpenAI2026LogSpace, Proposition 4.5]: at rate
`f > 0`, for retention channels with the bundled constants and an input `C` that is strictly
upper triangular, nonnegative, substochastic and has entries at most `f`, the next matrix has
entries at most `f / q`, intertwines with the projection, is supported within the copies of a
cover `A` of `C` and the overloaded vertices, and that cover has at most `2 |A|` copies. -/
theorem stage_rates [LinearOrder V] {π : ℝ} (hch : RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hCπ : 0 < Cπ) (hf : 0 < f) (hC : C.IsStrictUpperTriangular) (hC0 : ∀ x y, 0 ≤ C x y)
    (hCf : ∀ x y, C x y ≤ f) (hC1 : C *ᵥ 1 ≤ 1) {A : Finset V}
    (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) :
    (∀ a b, P.next X Y f C a b ≤ f / q) ∧
      P.next X Y f C * P.proj X Y f C = P.proj X Y f C * P.residual X Y f C ∧
      (∀ a b, P.next X Y f C a b ≠ 0 →
        ofLex a ∈ copyCover A (overloaded (P.pilot X Y f C)) ∧
          ofLex b ∈ copyCover A (overloaded (P.pilot X Y f C))) ∧
      #(copyCover (m := P.m) A (overloaded (P.pilot X Y f C))) ≤ 2 * #A := by
  have hτ₀ : P.θ₂ * f + f * Real.exp (1 / P.θ) * (P.L / P.θ) ^ P.k / P.k.factorial ≤
      P.τ₀ * f := by
    have := mul_le_mul_of_nonneg_right P.truncation hf.le
    calc P.θ₂ * f + f * Real.exp (1 / P.θ) * (P.L / P.θ) ^ P.k / P.k.factorial
        = (P.θ₂ + Real.exp (1 / P.θ) * (P.L / P.θ) ^ P.k / P.k.factorial) * f := by ring
      _ ≤ P.τ₀ * f := this
  have hτ₁ : P.τ₁ * f ≤ f / q :=
    calc P.τ₁ * f ≤ 1 / q * f := mul_le_mul_of_nonneg_right P.τ₁_le hf.le
      _ = f / q := by ring
  have hcopies : (P.k + 1) * f / (P.m + 1) ≤ f / q :=
    calc (P.k + 1) * f / (P.m + 1) = (P.k + 1) / (P.m + 1) * f := by ring
      _ ≤ 1 / q * f := mul_le_mul_of_nonneg_right P.copies hf.le
      _ = f / q := by ring
  obtain ⟨h1, h2, h3, h4⟩ := detectedStage_rates (c := P.cutoff f) (γ := P.γ) (κ := P.κ)
    (χ := P.copyCutoff f) (θ := P.θ) (L := P.L) (θ₂ := P.θ₂) (τ₀ := P.τ₀ * f) (τ₁ := P.τ₁ * f)
    (q := q) (k := P.k) (m := P.m) (K := P.K) (δ₀ := P.δ₀) hch hC hC0 hCf hC1 hA hf
    (P.cutoff_nonneg hf) (P.cutoff_le hf) (P.cutoff_mono hf) (P.cutoff_lipschitz hf)
    (P.le_cutoff hf) P.θ_pos P.L_nonneg P.γ_nonneg P.γ_le_one P.γ_one P.κ_nonneg P.κ_le_one
    P.κ_zero P.κ_one hCπ P.ϕ_nonneg P.ϕ_le_one P.δ₀_pos P.ϕ_zero P.ρ_le_one P.J_pos P.rank
    hτ₀ (fun t => P.χ_nonneg _) (fun t => P.χ_le_one _)
    (fun t ht => P.χ_zero _ (by rwa [div_le_iff₀ hf])) (fun t ht => P.χ_one _ (by
      rwa [le_div_iff₀ hf])) hτ₁ hcopies
  refine ⟨fun a b => h1 (ofLex a) (ofLex b), ?_, fun a b h => h3 _ _ h, h4⟩
  have hl : P.next X Y f C * P.proj X Y f C =
      (copyStage (P.copyCutoff f) P.m (P.weight X Y f C) (P.residual X Y f C) *
        copyWeight (P.weight X Y f C)).submatrix ofLex id :=
    submatrix_mul _ _ _ _ _ ofLex.bijective
  have hr : P.proj X Y f C * P.residual X Y f C =
      (copyWeight (P.weight X Y f C) * P.residual X Y f C).submatrix ofLex id := by
    ext a z
    rfl
  rw [hl, hr]
  exact congrArg (fun M => M.submatrix ofLex id) h2

/-- The next matrix is strictly upper triangular for the lexicographic order on the copies. -/
theorem next_isStrictUpperTriangular [LinearOrder V] (hf : 0 < f)
    (hC : C.IsStrictUpperTriangular) : (P.next X Y f C).IsStrictUpperTriangular := by
  unfold next residual correction
  exact copyStage_isStrictUpperTriangular <|
    cutoffCorrection_residual_isStrictUpperTriangular
      (φ := fun y t => P.cutoff f t * P.γ (P.pilot X Y f C y)) (P.phi_nonneg hf) (P.phi_le hf)
      (P.θf_nonneg hf) hC P.k

theorem residual_nonneg (hf : 0 < f) (hC0 : ∀ x y, 0 ≤ C x y) (x y : V) :
    0 ≤ P.residual X Y f C x y := by
  unfold residual correction
  exact cutoffCorrection_residual_nonneg (φ := fun y t => P.cutoff f t * P.γ (P.pilot X Y f C y))
    hC0 (P.phi_nonneg hf) (P.phi_le hf) (P.phi_mono hf) (P.θf_nonneg hf) P.k x y

theorem weight_nonneg (j : Fin (P.m + 1)) (x : V) : 0 ≤ P.weight X Y f C j x := by
  unfold weight detectorWeight; split_ifs
  · exact zero_le_one
  · exact P.κ_nonneg _

theorem weight_le_one (j : Fin (P.m + 1)) (x : V) : P.weight X Y f C j x ≤ 1 := by
  unfold weight detectorWeight; split_ifs
  · exact le_rfl
  · exact P.κ_le_one _

theorem next_nonneg (hf : 0 < f) (hC0 : ∀ x y, 0 ≤ C x y) (a b : Lex (V × Fin (P.m + 1))) :
    0 ≤ P.next X Y f C a b :=
  copyStage_nonneg (P.weight_nonneg (X := X) (Y := Y) (f := f) (C := C))
    (P.residual_nonneg hf hC0) (fun _ => P.χ_nonneg _) (fun _ => P.χ_le_one _) _ _

theorem next_mulVec_one_le (hf : 0 < f) (hC0 : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) :
    P.next X Y f C *ᵥ 1 ≤ 1 := by
  have h := copyStage_mulVec_one_le (χ := P.copyCutoff f)
    (P.weight_nonneg (X := X) (Y := Y) (f := f) (C := C)) (P.weight_le_one (X := X) (Y := Y)
      (f := f) (C := C)) (P.residual_nonneg hf hC0) (D := P.residual X Y f C) ?_
  · intro a
    have h' := h (ofLex a)
    simp only [mulVec, dotProduct, Pi.one_apply, mul_one] at h' ⊢
    calc ∑ i, P.next X Y f C a i
        = ∑ x, copyStage (P.copyCutoff f) P.m (P.weight X Y f C) (P.residual X Y f C)
            (ofLex a) x := Fintype.sum_equiv ofLex _ _ fun _ => rfl
      _ ≤ 1 := h'
  · unfold residual correction
    exact (correction_mulVec_one_le (fun x y => cutoffCorrectionIter_nonneg
      (φ := fun y t => P.cutoff f t * P.γ (P.pilot X Y f C y)) (P.phi_nonneg hf) _ x y)
      hC1).trans hC1

theorem proj_nonneg [DecidableEq V] (a : Lex (V × Fin (P.m + 1))) (x : V) :
    0 ≤ P.proj X Y f C a x := by
  simp only [proj, submatrix_apply, copyWeight, of_apply, id]
  split_ifs
  · exact P.weight_nonneg _ _
  · exact le_rfl

theorem proj_mulVec_one_le [DecidableEq V] : P.proj X Y f C *ᵥ 1 ≤ 1 := by
  intro a
  have h := copyWeight_mulVec (P.weight X Y f C) 1 (ofLex a)
  simp only [Pi.one_apply, mul_one] at h
  have : (P.proj X Y f C *ᵥ 1) a = (copyWeight (P.weight X Y f C) *ᵥ 1) (ofLex a) := rfl
  rw [this, h]
  exact P.weight_le_one _ _

/-- The primary copy projects to its parent with weight one. -/
theorem proj_primary [DecidableEq V] (x w : V) :
    P.proj X Y f C (toLex (x, 0)) w = if w = x then 1 else 0 := by
  simp only [proj, submatrix_apply, id, ofLex_toLex]
  exact copyWeight_apply_of_eq_one (by simp [weight, detectorWeight]) w

end Stage

end HierarchyParams

end Matrix
