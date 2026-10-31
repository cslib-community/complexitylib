/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.StochasticAtom
import Complexity.Probability.PairwiseIndependentHash.DetectorChannels
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for the stochastic atoms

* A computed two-draw atom: the row gate fails on half of the draws, the normalizer is `1/2`, and
  the normalized atom still has the exact entry as its mean.
* The dense atom identity, with every hypothesis discharged, for a concrete matrix and for every
  matrix under the affine retention channels over `𝔽_P`.
* Row support on every draw, and concrete bin weights.
-/

namespace ComplexityTests.StochasticAtom

open Finset Matrix Cslib Cslib.Probability
open scoped BigOperators

/-- Main function of the dense bins: zero through `1/2`. -/
private noncomputable def k : ℝ → ℝ := fun d => if d ≤ 1 / 2 then 0 else d

/-- Gate function: one below `1/1000`, zero from `1/1000` on. -/
private noncomputable def ρ : ℝ → ℝ := fun r => if r < 1 / 1000 then 1 else 0

private theorem ρ_nonneg (r : ℝ) : 0 ≤ ρ r := by unfold ρ; split_ifs <;> norm_num

private theorem ρ_le_one (r : ℝ) : ρ r ≤ 1 := by unfold ρ; split_ifs <;> norm_num

private theorem ρ_eq_one (r : ℝ) (hr : r ≤ 1 / 2000) : ρ r = 1 := by
  unfold ρ
  split_ifs with h
  · rfl
  · exact absurd (by linarith) h

private theorem ρ_eq_zero (r : ℝ) (hr : 1 / 1000 ≤ r) : ρ r = 0 := by
  unfold ρ
  split_ifs with h
  · exact absurd hr (not_le.mpr h)
  · rfl

private theorem k_eq_zero (d : ℝ) (hd : d ≤ 1 / 2) : k d = 0 := by
  simp only [k, ite_eq_left_iff]
  exact fun h => absurd hd h

/-! ### A computed atom: normalization compensates a failing gate -/

/-- Draw `false` retains `{1}`, draw `true` retains `{1, 2}`. -/
private abbrev Y : Bool → Fin 3 → Prop := fun s v => v = 1 ∨ (s = true ∧ v = 2)

/-- Row `0` has the two entries `G 0 1 = G 0 2 = 1`. -/
private noncomputable def G : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 1; 0, 0, 0; 0, 0, 0]

private theorem retained_false : ({w | Y false w} : Finset (Fin 3)) = {1} := by decide

private theorem retained_true : ({w | Y true w} : Finset (Fin 3)) = {1, 2} := by decide

/-- On draw `false` only one entry is retained, so the second largest is the padding `0` and the
gate is open. -/
private theorem rowGate_false : rowGate ρ 2 1 G {w | Y false w} 0 = 1 := by
  have h : kthLargest 2 ({w | Y false w} : Finset (Fin 3)) (fun w => G 0 w / 1) = 0 := by
    refine le_antisymm (not_lt.mp fun hlt => ?_) kthLargest_nonneg
    have := (lt_kthLargest_iff (by norm_num) le_rfl).mp hlt
    rw [retained_false] at this
    exact absurd (this.trans (card_filter_le _ _)) (by simp)
  rw [rowGate, h]
  exact ρ_eq_one 0 (by norm_num)

/-- On draw `true` two entries `1` are retained, so the second largest is `1` and the gate is
closed. -/
private theorem rowGate_true : rowGate ρ 2 1 G {w | Y true w} 0 = 0 := by
  have h : 1 ≤ kthLargest 2 ({w | Y true w} : Finset (Fin 3)) (fun w => G 0 w / 1) := by
    rw [le_kthLargest_iff (by norm_num) (by norm_num), retained_true]
    have : ({x ∈ ({1, 2} : Finset (Fin 3)) | (1 : ℝ) ≤ G 0 x / 1}) = {1, 2} := by
      ext x; fin_cases x <;> simp [G]
    rw [this]; rfl
  rw [rowGate]
  exact ρ_eq_zero _ (by linarith)

private theorem draws_one : ({s | Y s 1} : Finset Bool) = univ := by decide

/-- The normalizer is `1/2`: the gate is open on one of the two draws. -/
private theorem atomNormalizer_eq :
    atomNormalizer Y Y (fun _ => 1) ρ 2 1 G 0 1 = 1 / 2 := by
  rw [atomNormalizer, draws_one]
  simp only [atomPrep, one_mul, Fintype.expect_bool, rowGate_true, rowGate_false]
  norm_num

-- The atom doubles the entry on the open draw, vanishes on the closed one, and has mean
-- exactly `k (G 0 1) = 1`, although the gate fails half of the time. (Here `K = 2` is far below
-- the sufficient condition of `expect_denseAtom`; the normalizer still is at least `1/2`.)
example : denseAtom Y Y k (fun _ => 1) ρ 2 1 G false 0 1 = 2 ∧
    denseAtom Y Y k (fun _ => 1) ρ 2 1 G true 0 1 = 0 ∧
    𝔼 s ∈ ({s | Y s 1} : Finset Bool), denseAtom Y Y k (fun _ => 1) ρ 2 1 G s 0 1 = k (G 0 1 / 1)
    := by
  have hY : ∀ s, Y s 1 := fun s => Or.inl rfl
  have hk : k (G 0 1 / 1) = 1 := by norm_num [k, G]
  have hfalse : denseAtom Y Y k (fun _ => 1) ρ 2 1 G false 0 1 = 2 := by
    simp only [denseAtom, hY false, ↓reduceIte, atomNormalizer_eq, rowGate_false, hk]
    norm_num
  have htrue : denseAtom Y Y k (fun _ => 1) ρ 2 1 G true 0 1 = 0 := by
    simp only [denseAtom, hY true, ↓reduceIte, rowGate_true]
    simp
  refine ⟨hfalse, htrue, ?_⟩
  rw [draws_one, Fintype.expect_bool, hfalse, htrue, hk]
  norm_num

-- Row support: on every draw, row `0` has fewer than `K = 2` nonzero atoms.
example (s : Bool) : #{y | denseAtom Y Y k (fun _ => 1) ρ 2 1 G s 0 y ≠ 0} < 2 :=
  card_filter_denseAtom_ne_zero_lt (fun _ _ h => h) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    k_eq_zero (by norm_num : (1 / 1000 : ℝ) ≤ 1 / 2) ρ_eq_zero s 0

/-! ### The identity with all hypotheses discharged -/

/-- The `½`-walk `0 → 1 → 2` on three vertices. -/
private noncomputable def W : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

-- With a channel that retains everything (one seed), `K = 2002` satisfies
-- `K ≥ 2 (1 + c M / η)` for `c = 1`, `M = 1/2`, `η = 1/2000`. The main function `d ↦ d` and the
-- conditional mean recovers the entry `1/2`.
example : 𝔼 s ∈ (univ.filter fun _ => True : Finset Unit),
    denseAtom (fun _ (_ : Fin 3) => True) (fun _ _ => True) (fun d => d) (fun _ => 1) ρ 2002 1 W
      s 0 1 = 1 / 2 := by
  have h := expect_denseAtom (Y := fun _ (_ : Fin 3) => True) (Yt := fun _ _ => True)
    (k := fun d => d) (h := fun _ => 1) (K := 2002) (G := W) (x := 0) (y := 1)
    ⟨(), by simp⟩ (fun _ _ => rfl) ρ_nonneg ρ_le_one (by norm_num : (0 : ℝ) < 1 / 2000) ρ_eq_one
    one_pos (fun w => by fin_cases w <;> norm_num [W]) (M := 1 / 2)
    (by simp [W, Fin.sum_univ_three]) (c := 1) zero_le_one (by norm_num)
    (fun w _ => by simp)
  rw [h]
  norm_num [W]

-- For every injective identification with `𝔽_P` and every rate `f = a ^ H` with `1 ≤ P a ≤ P`,
-- the affine retention channels give the identity for any nonnegative matrix with row mass at
-- most one, once `K ≥ 2 (1 + 2 ^ H · 2000)`.
example {V : Type*} [Fintype V] {P H : ℕ} [Fact P.Prime] {ident : V → ZMod P}
    (hident : Function.Injective ident) {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) (ha0 : 0 < a)
    (G : Matrix V V ℝ) {x : V} (hG0 : ∀ w, 0 ≤ G x w) (hG1 : ∑ w, G x w ≤ 1) {K : ℕ}
    (hK : 2 * (1 + 2 ^ H * 2000) ≤ (K : ℝ)) (y : V) :
    𝔼 s ∈ ({s | affineRetains P H ⌈P * a⌉₊ s (ident y)} : Finset _),
      denseAtom (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v))
        (fun s v => affineRetains P H ⌈P * a⌉₊ s (ident v)) k (fun _ => 1) ρ K (a ^ H) G s x y =
      k (G x y / a ^ H) :=
  expect_denseAtom_of_retentionChannels (retentionChannels_affineRetains hident hPa ha)
    (pow_pos ha0 H) one_pos (by positivity) (fun _ _ => rfl) ρ_nonneg ρ_le_one
    (by norm_num : (0 : ℝ) < 1 / 2000) ρ_eq_one hG0 hG1 (by
      have : (2 : ℝ) ^ H * 1 / (1 / 2000) = 2 ^ H * 2000 := by field_simp
      rw [this]; exact hK)

/-! ### Bins -/

/-- A switch: zero through `1/2`, one from `1`, linear in between. -/
private noncomputable def χ : ℝ → ℝ := fun t => max 0 (min 1 (2 * t - 1))

/-- Dyadic scales `b_k = 2^{-k}`. -/
private noncomputable def b : ℕ → ℝ := fun k => (1 / 2) ^ k

-- At `w = 3/8`, with scales `1, 1/2, 1/4`: `ω₀ = 0`, `ω₁ = 1/2`, `ω₂ = 1/2`.
example : binWeight χ b 0 (3 / 8) = 0 ∧ binWeight χ b 1 (3 / 8) = 1 / 2 ∧
    binWeight χ b 2 (3 / 8) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [binWeight, χ, b]

-- The weights reproduce `w = 3/8` from scale `b₂ = 1/4` on.
example : ∑ k ∈ range 3, (3 / 8 : ℝ) * binWeight χ b k (3 / 8) = 3 / 8 :=
  sum_range_mul_binWeight (n := 2) (fun t ht => by simp only [χ]; rw [min_eq_left (by linarith),
    max_eq_right zero_le_one]) (by norm_num [b]) (by norm_num [b])

-- `ω₂(w) ≠ 0` locates `w` in `(b₂ / 2, b₁) = (1/8, 1/2)`.
example {w : ℝ} (hω : binWeight χ b 2 w ≠ 0) : 1 / 8 < w ∧ w < 1 / 2 := by
  have h := binWeight_succ_ne_zero (k := 1) (fun t ht => by
      simp only [χ]; rw [max_eq_left (by have := min_le_right 1 (2 * t - 1); linarith)])
    (fun t ht => by simp only [χ]; rw [min_eq_left (by linarith), max_eq_right zero_le_one])
    (fun k => by positivity) (fun i j hij => pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)
    hω
  norm_num [b] at h
  exact h

end ComplexityTests.StochasticAtom
