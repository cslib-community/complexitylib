/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.CorrectionAtom
import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the correction atoms

* The normalization principle on a concrete gate.
* The incoming cap on a concrete column, and the column and row support bounds.
* The correction atom identity with every hypothesis discharged, for a concrete matrix and for every
  matrix under the affine retention channels over `𝔽_P`.
* Rank stability on concrete values.
-/

namespace ComplexityTests.CorrectionAtom

open Finset Matrix Cslib Cslib.Probability
open scoped BigOperators

/-- Correction cutoff: zero through `1/4`. -/
private noncomputable def Q : ℝ → ℝ := fun v => if v ≤ 1 / 4 then 0 else v

/-- Row gate: one below `1/1000`. -/
private noncomputable def ρ : ℝ → ℝ := fun r => if r < 1 / 1000 then 1 else 0

/-- Incoming gate: one below `1/4`. -/
private noncomputable def τ : ℝ → ℝ := fun r => if r < 1 / 4 then 1 else 0

/-- Auxiliary score: one above entry `1/8`, ignoring the rank. -/
private noncomputable def I : ℝ → ℝ → ℝ := fun v _ => if v ≤ 1 / 8 then 0 else 1

private theorem ρ_nonneg (r : ℝ) : 0 ≤ ρ r := by unfold ρ; split_ifs <;> norm_num
private theorem ρ_le_one (r : ℝ) : ρ r ≤ 1 := by unfold ρ; split_ifs <;> norm_num
private theorem τ_nonneg (r : ℝ) : 0 ≤ τ r := by unfold τ; split_ifs <;> norm_num
private theorem τ_le_one (r : ℝ) : τ r ≤ 1 := by unfold τ; split_ifs <;> norm_num

private theorem ρ_eq_one (r : ℝ) (hr : r ≤ 1 / 2000) : ρ r = 1 := by
  unfold ρ
  split_ifs with h
  · rfl
  · exact absurd (by linarith) h

private theorem τ_eq_one (r : ℝ) (hr : r ≤ 1 / 8) : τ r = 1 := by
  unfold τ
  split_ifs with h
  · rfl
  · exact absurd (by linarith) h

private theorem τ_eq_zero (r : ℝ) (hr : 1 / 4 ≤ r) : τ r = 0 := by
  unfold τ
  split_ifs with h
  · exact absurd hr (not_le.mpr h)
  · rfl

private theorem I_eq_zero (v r : ℝ) (hv : v ≤ 1 / 8) : I v r = 0 := by
  simp only [I, ite_eq_left_iff]
  exact fun h => absurd hv h

private theorem Q_eq_zero (v : ℝ) (hv : v ≤ 1 / 4) : Q v = 0 := by
  simp only [Q, ite_eq_left_iff]
  exact fun h => absurd hv h

private theorem I_eq_one (v r : ℝ) (hQ : Q v ≠ 0) (_ : ρ r ≠ 0) : I v r = 1 := by
  unfold I
  split_ifs with h
  · exact absurd (Q_eq_zero v (by linarith)) hQ
  · rfl

/-! ### The normalization principle -/

-- A gate that is closed on one of three draws: dividing by its mean `2/3` removes the bias.
example (m : ℝ) :
    𝔼 s ∈ (univ : Finset (Fin 3)), m * ![1, 1, 0] s / max (1 / 2) (min 1
      (𝔼 s ∈ (univ : Finset (Fin 3)), (![1, 1, 0] : Fin 3 → ℝ) s)) = m :=
  expect_mul_div_clip_eq univ_nonempty (fun s _ => by fin_cases s <;> norm_num)
    (fun s _ => by fin_cases s <;> norm_num) (by
      have : (univ.filter fun s : Fin 3 => (![1, 1, 0] : Fin 3 → ℝ) s < 1) = {2} := by
        ext s; fin_cases s <;> norm_num
      rw [this]; norm_num) m

/-! ### The incoming cap -/

/-- Every source has entry `1` in every column. -/
private noncomputable def J : Matrix (Fin 3) (Fin 3) ℝ := fun _ _ => 1

-- All three retained sources score one at column `0`, so with `K_c = 2` the incoming gate is
-- closed.
example (T : Finset (Fin 3)) : incomingGate I τ 5 2 1 J univ T 0 = 0 := by
  refine incomingGate_eq_zero (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 1) τ_eq_zero ?_
  have : (univ.filter fun x : Fin 3 => (1 : ℝ) ≤ auxScore I 5 1 J T x 0) = univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, auxScore, J, div_one, I]
    norm_num
  rw [this]
  decide

-- Column and row support on every draw of any channels, with `K_c = 2` and `K = 3`.
example {ι κ : Type*} [Fintype ι] [Fintype κ] (X : ι → Fin 3 → Prop) (Y Yt : κ → Fin 3 → Prop)
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Yt t v)]
    (G : Matrix (Fin 3) (Fin 3) ℝ) (g₀ : Fin 3 → ℝ) (d : ι × κ) (x y : Fin 3) :
    #{x ∈ ({w | X d.1 w} : Finset (Fin 3)) |
        correctionAtom I τ 3 2 1 G X Y Yt Q (fun _ => 1) ρ g₀ d x y ≠ 0} < 2 ∧
      #{y ∈ ({w | Y d.2 w} : Finset (Fin 3)) |
        correctionAtom I τ 3 2 1 G X Y Yt Q (fun _ => 1) ρ g₀ d x y ≠ 0} < 3 := by
  refine ⟨card_filter_correctionAtom_col_ne_zero_lt (by norm_num) I_eq_one
      (by norm_num : (1 / 4 : ℝ) ≤ 1) τ_eq_zero d y,
    card_filter_correctionAtom_row_ne_zero_lt (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      Q_eq_zero (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 4)
      (fun r hr => ?_) d x⟩
  unfold ρ
  split_ifs with h
  · exact absurd hr (not_le.mpr h)
  · rfl

/-! ### The identity with all hypotheses discharged -/

/-- The `½`-walk `0 → 1 → 2` on three vertices. -/
private noncomputable def W : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem filter_W : (univ.filter fun w : Fin 3 => (1 / 8 : ℝ) < W w 1 / 1) = {0} := by
  ext w; fin_cases w <;> norm_num [W]

-- With channels that retain everything, `K = 4004` and `K_c = 8`, the correction atom at
-- `(0, 1)` with multiplier `3` has conditional mean `Q (1/2) · 3 = 3/2`.
example : 𝔼 d ∈ (univ.filter fun _ : Unit => True) ×ˢ (univ.filter fun _ : Unit => True),
    correctionAtom I τ 4004 8 1 W (fun _ _ => True) (fun _ _ => True) (fun _ _ => True) Q
      (fun _ => 1) ρ (fun _ => 3) d 0 1 = 3 / 2 := by
  have h := expect_correctionAtom (I := I) (τ := τ) (K := 4004) (Kc := 8) (f := 1) (G := W)
    (X := fun (_ : Unit) (_ : Fin 3) => True) (Y := fun (_ : Unit) (_ : Fin 3) => True)
    (Yt := fun _ _ => True) (Q := Q) (h := fun _ => 1) (ρ := ρ) (g₀ := fun _ => 3) (x := 0)
    (y := 1) ⟨(), by simp⟩ ⟨(), by simp⟩ (fun _ _ => rfl) ρ_nonneg ρ_le_one
    (by norm_num : (0 : ℝ) < 1 / 2000) ρ_eq_one τ_nonneg τ_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 8) τ_eq_one I_eq_zero one_pos
    (fun w => by fin_cases w <;> norm_num [W]) (M := 1 / 2) (by simp [W, Fin.sum_univ_three])
    (c := 1) zero_le_one (by norm_num) (fun w _ => by simp) (p := 1) zero_le_one
    (fun w _ => by simp) (B := 1) (fun _ => by rw [filter_W]; norm_num) (by norm_num)
  rw [h]
  norm_num [Q, W]

/-- The pair bound of a retention channel, as a count over the draws retaining `y`. -/
private theorem card_pair_le {κ V : Type*} [Fintype κ] {Y : κ → V → Prop}
    [∀ t v, Decidable (Y t v)] {q : ℝ} {w y : V}
    (h : (dens {t | Y t w ∧ Y t y} : ℝ) ≤ q * dens {t | Y t y}) :
    (#{t | Y t y ∧ Y t w} : ℝ) ≤ q * #{t | Y t y} := by
  have hcard : ∀ T : Finset κ, ((dens T : ℚ≥0) : ℝ) = #T / Fintype.card κ := fun T => by
    rw [dens_eq_card_div_card]; push_cast; rfl
  rw [hcard, hcard, ← mul_div_assoc] at h
  have hset : ({t | Y t y ∧ Y t w} : Finset κ) = ({t | Y t w ∧ Y t y} : Finset κ) := by
    ext t; simp only [mem_filter, mem_univ, true_and]; tauto
  rw [hset]
  rcases (Fintype.card κ).eq_zero_or_pos with h0 | h0
  · have : (univ : Finset κ) = ∅ := univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp h0)
    simp [this]
  · exact (div_le_div_iff_of_pos_right (by exact_mod_cast h0)).mp h

/-- The identity for one retention channel `C` used on both sides, at rate `f`, for every
nonnegative `G` with row mass at most one and at most `R / f` sources above `f / 8` in column
`y`, once `K ≥ 4 (1 + C_pair · 2000)` and `K_c ≥ 4 (1 + C_pair R)`. -/
private theorem expect_correctionAtom_channel {V κ : Type*} [Fintype V] [Fintype κ]
    {C : κ → V → Prop} [∀ t v, Decidable (C t v)] {f π Cπ Cpair Cvar : ℝ}
    (hch : RetentionChannels C C f π 1 Cπ Cpair Cvar) (hf : 0 < f) (hCpair : 0 ≤ Cpair)
    (G : Matrix V V ℝ) {x y : V} (hG0 : ∀ w, 0 ≤ G x w) (hG1 : ∑ w, G x w ≤ 1) {R : ℝ}
    (hD : (#({w | 1 / 8 < G w y / f} : Finset V) : ℝ) * f ≤ R) {K Kc : ℕ}
    (hK : 4 * (1 + Cpair * 2000) ≤ (K : ℝ)) (hKc : 4 * (1 + Cpair * R) ≤ (Kc : ℝ))
    (g₀ : V → ℝ) :
    𝔼 d ∈ ({s | C s x} : Finset κ) ×ˢ ({t | C t y} : Finset κ),
      correctionAtom I τ K Kc f G C C C Q (fun _ => 1) ρ g₀ d x y = Q (G x y / f) * g₀ y := by
  have hπ := (mul_pos one_pos hf).trans_le hch.lower
  have hne : ∀ v, ({s | C s v} : Finset κ).Nonempty := fun v => by
    by_contra hv
    rw [not_nonempty_iff_eq_empty] at hv
    have h := hch.dens_Y v
    rw [hv, dens_empty, NNRat.cast_zero] at h
    linarith
  refine expect_correctionAtom (hne x) (hne y) (fun _ _ => rfl) ρ_nonneg ρ_le_one
    (by norm_num : (0 : ℝ) < 1 / 2000) ρ_eq_one τ_nonneg τ_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 8) τ_eq_one I_eq_zero hf hG0 hG1 (c := Cpair) hCpair
    (by rw [show Cpair * 1 / (1 / 2000) = Cpair * 2000 by field_simp]; exact hK)
    (fun w hwy => card_pair_le (hch.pair w y hwy)) (p := Cpair * f) (by positivity)
    (fun w hwx => card_pair_le (hch.pair w x hwx)) (B := Cpair * R) (fun _ => ?_) hKc
  calc Cpair * f * (#({w | 1 / 8 < G w y / f} : Finset V) : ℝ)
      = Cpair * ((#({w | 1 / 8 < G w y / f} : Finset V) : ℝ) * f) := by ring
    _ ≤ Cpair * R := by gcongr

-- Affine retention channels over `𝔽_P` for both the start and the terminal side, at rate
-- `f = a ^ H` (`C_pair = 2 ^ H`).
example {V : Type*} [Fintype V] {P H : ℕ} [Fact P.Prime] {ident : V → ZMod P}
    (hident : Function.Injective ident) {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) (ha0 : 0 < a)
    (G : Matrix V V ℝ) {x y : V} (hG0 : ∀ w, 0 ≤ G x w) (hG1 : ∑ w, G x w ≤ 1) {R : ℝ}
    (hD : (#({w | 1 / 8 < G w y / a ^ H} : Finset V) : ℝ) * a ^ H ≤ R) {K Kc : ℕ}
    (hK : 4 * (1 + 2 ^ H * 2000) ≤ (K : ℝ)) (hKc : 4 * (1 + 2 ^ H * R) ≤ (Kc : ℝ))
    (g₀ : V → ℝ) :
    𝔼 d ∈ ({s | affineRetains P H ⌈P * a⌉₊ s (ident x)} : Finset _) ×ˢ
        ({t | affineRetains P H ⌈P * a⌉₊ t (ident y)} : Finset _),
      correctionAtom I τ K Kc (a ^ H) G (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
        (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
        (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v)) Q (fun _ => 1) ρ g₀ d x y =
      Q (G x y / a ^ H) * g₀ y :=
  expect_correctionAtom_channel (retentionChannels_affineRetains hident hPa ha) (pow_pos ha0 H)
    (by positivity) G hG0 hG1 hD hK hKc g₀

/-! ### Rank stability -/

-- Perturbing `3, 1, 2, 0` by at most `1/2` moves its second largest value `2` by at most `1/2`.
example : |kthLargest 2 univ (![3, 1, 2, 0] : Fin 4 → ℚ) -
    kthLargest 2 univ (![5 / 2, 1, 5 / 2, 1 / 2] : Fin 4 → ℚ)| ≤ 1 / 2 :=
  abs_kthLargest_sub_kthLargest_le (by norm_num) (by norm_num) fun x _ => by
    fin_cases x <;> norm_num

end ComplexityTests.CorrectionAtom
