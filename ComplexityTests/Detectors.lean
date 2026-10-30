/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.DetectedStage
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FinCases

/-!
# Tests for the pilot, the column detectors and a detected stage
-/

namespace ComplexityTests.Detectors

open Finset Matrix Cslib.Probability

/-! ### Channels that retain every vertex -/

/-- A channel with one seed that retains every vertex. -/
private abbrev all {V : Type*} : Unit → V → Prop := fun _ _ => True

/-- Channels that retain everything satisfy the channel interface at every rate `f ∈ (0, 1]`, with
`c_π = 1`, `C_π = C_pair = 1 / f` and `C_var = 0`. -/
private theorem retentionChannels_all {V : Type*} {f : ℝ} (hf : 0 < f) (hf1 : f ≤ 1) :
    RetentionChannels (all (V := V)) all f 1 1 (1 / f) (1 / f) 0 where
  dens_X _ := by simp [all]
  dens_Y _ := by simp [all]
  lower := by simpa using hf1
  upper := by rw [one_div_mul_cancel hf.ne']
  pair _ _ _ := by simp [all, hf.ne']
  tail A _ := by
    have : ({s | 2 * (#{x ∈ A | all s x} : ℝ) < #A * 1} : Finset Unit) = ∅ := by
      ext s
      simp only [all, filter_true, mul_one, mem_filter, mem_univ, true_and, notMem_empty,
        iff_false, not_lt]
      linarith [(Nat.cast_nonneg (α := ℝ) #A)]
    rw [this]
    simp

/-! ### Step cutoffs -/

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
private theorem down_antitone (a : ℝ) : Antitone (down a) := fun s t hst => by
  unfold down; split_ifs with h1 h2 <;> first | exact absurd (hst.trans h1) h2 | norm_num

/-! ### The detector lemma on a concrete column -/

/-- Rows `0, …, 4` each have one entry `1 / 5`, in column `5`. -/
private noncomputable def G : Matrix (Fin 6) (Fin 6) ℝ :=
  of fun x y => if y = 5 ∧ x ≠ 5 then 1 / 5 else 0

private theorem G0 : ∀ x w, 0 ≤ G x w := by
  intro x w; simp only [G, of_apply]; split_ifs <;> norm_num

private theorem G_row : ∀ x, ∑ w, G x w ≤ (1 : ℝ) := by
  intro x; fin_cases x <;> simp [G] <;> norm_num

-- Column `5` has five entries `1 / 5 ≥ δ₁ f` with `f = 1` and `δ₁ = 1 / 6`, more than
-- `R / f = 4`, so its detector number is at least `19 / 20`. The score is the step at `1 / 10`,
-- the gate the step at `η = 1 / 2`, and the gate rank `K = 480 ≥ 160 (1 + 1 / (1 / 2))`.
example : 19 / 20 ≤ columnDetector all all (up (1 / 10)) (down (1 / 2)) 1 480 1 G 5 := by
  have hcount : (4 : ℝ) / 1 < #(univ.filter fun x => 1 / 6 * 1 ≤ G x 5) := by
    have hsub : (univ.erase 5 : Finset (Fin 6)) ⊆ univ.filter fun x => 1 / 6 * 1 ≤ G x 5 :=
      fun x hx => by
        have hx5 : x ≠ 5 := ne_of_mem_erase hx
        simp only [mem_filter, mem_univ, true_and, G, of_apply, hx5, ne_eq, not_false_eq_true,
          ↓reduceIte]
        norm_num
    have := card_le_card hsub
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin] at this
    have : (5 : ℝ) ≤ #(univ.filter fun x => 1 / 6 * 1 ≤ G x 5) := by exact_mod_cast this
    linarith
  exact le_columnDetector (J := 1) (K := 480) (G := G) (R := 4)
    (retentionChannels_all (V := Fin 6) one_pos le_rfl) one_pos one_pos (by norm_num)
    (δ₁ := 1 / 6) (fun t ht => up_of_lt (by linarith)) (down_le_one _)
    (by norm_num : (0 : ℝ) < 1 / 2) (fun t ht => down_of_le ht) G0 G_row (by norm_num)
    one_pos (by norm_num) (by norm_num) hcount

-- An empty column has no substantial entries, so its detector number is at most `1 / 4`.
example : columnDetector all all (up (1 / 10)) (down (1 / 2)) 1 480 1 G 0 ≤ 1 / 4 := by
  refine not_lt.mp fun h => ?_
  have := lt_card_of_lt_columnDetector (J := 1) (K := 480) (G := G)
    (retentionChannels_all (V := Fin 6) one_pos le_rfl) one_pos (up_nonneg _) (up_le_one _)
    (fun t ht => up_of_le ht) (down_le_one _) one_pos h
  have hempty : (univ.filter fun x => 1 / 10 * 1 < G x 0) = ∅ := by
    ext x; simp only [G, of_apply, Fin.reduceEq, false_and, ↓reduceIte, mem_filter, mem_univ,
      true_and, notMem_empty, iff_false, not_lt]; norm_num
  rw [hempty, card_empty, Nat.cast_zero] at this
  norm_num at this

/-! ### A stage of the hierarchy with detector-chosen multipliers -/

/-- A walk on three time layers: from `0` to `1` and from `1` to `2`, each with probability
`f = 1 / 2`. -/
private noncomputable def C : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem hC : C.IsStrictUpperTriangular := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [C]

private theorem hC0 : ∀ x y, 0 ≤ C x y := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hCf : ∀ x y, C x y ≤ 1 / 2 := by
  intro x y; fin_cases x <;> fin_cases y <;> norm_num [C]

private theorem hC1 : C *ᵥ 1 ≤ 1 := by
  intro x; fin_cases x <;> norm_num [C, mulVec, dotProduct, Fin.sum_univ_three]

/-- The hard base cutoff `t ↦ max (t - θ f) 0` with `θ = 1 / 4`, `f = 1 / 2`. -/
private noncomputable def c (t : ℝ) : ℝ := max (t - 1 / 8) 0

private theorem hcL : ∀ s t, s ≤ t → c t - c s ≤ 1 * (t - s) := fun s t _ => by
  simp only [c, one_mul]
  have := le_max_left (s - 1 / 8) 0
  have := le_max_right (s - 1 / 8) 0
  have : max (t - 1 / 8) 0 ≤ max (s - 1 / 8) 0 + (t - s) := max_le (by linarith) (by linarith)
  linarith

private theorem c_nonneg (t : ℝ) : 0 ≤ c t := le_max_right _ _
private theorem c_le (t : ℝ) (ht : 0 ≤ t) : c t ≤ t := max_le (by linarith) ht
private theorem c_mono : Monotone c := fun _ _ h => max_le_max (by linarith) le_rfl

/-! ### The pilot -/

/-- A column number that flags column `2`, whatever the input. -/
private noncomputable def flag2 : Matrix (Fin 3) (Fin 3) ℝ → Fin 3 → ℝ :=
  fun _ y => if y = 2 then 1 else 0

-- After one pilot step the running maximum flags column `2`, which loses its multiplier.
example : pilotMax c (down (1 / 2)) flag2 C 1 2 = 1 := by
  rw [pilotMax_succ]; norm_num [flag2]

-- Column `1` is corrected, `Ê₁ (0, 1) = c (1 / 2) = 3 / 8`; column `2` is not.
example : pilotCorrection c (down (1 / 2)) flag2 C 1 0 1 = 3 / 8 := by
  rw [pilotCorrection_succ_apply, pilotMax_succ]
  norm_num [pilotInput, flag2, c, C, down]

example : pilotCorrection c (down (1 / 2)) flag2 C 1 1 2 = 0 := by
  rw [pilotCorrection_succ_apply, pilotMax_succ]
  norm_num [flag2, down]

-- The pilot corrections have row sums at most the step count.
example (x : Fin 3) : ∑ y, pilotCorrection c (down (1 / 2)) flag2 C 2 x y ≤ 2 := by
  exact_mod_cast (isCorrectionSeq_pilotCorrection hC0 c_nonneg c_le (down_nonneg _)
    (down_le_one _)).sum_le hC1 2 x

-- The actual correction with the final multiplier stays below the pilot.
example (x y : Fin 3) :
    cutoffCorrectionIter (fun y t => c t * down (1 / 2) (pilotMax c (down (1 / 2)) flag2 C 2 y))
      C 1 x y ≤ pilotCorrection c (down (1 / 2)) flag2 C 1 x y :=
  (cutoffCorrectionIter_le_pilotCorrection hC0 c_nonneg c_le c_mono (down_nonneg _)
    (down_le_one _) (down_antitone _) (by norm_num : 1 ≤ 2) x y).1

/-! ### One stage -/

/-- `e ^ 4 · 4 ^ 15 / 15! ≤ 1 / 8`: fifteen iterations make the truncation error small. -/
private theorem factorial_bound :
    (1 / 2 : ℝ) * Real.exp (1 / (1 / 4)) * (1 / (1 / 4)) ^ 15 / (Nat.factorial 15) ≤ 1 / 16 := by
  have he : Real.exp 4 ≤ 55 := by
    have h1 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h1]
    calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 :=
          pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 4
      _ ≤ 55 := by norm_num
  norm_num [Nat.factorial]
  nlinarith

-- One stage with `k = 15` pilot and correction steps, `m + 1 = 32` copies, the full-retention
-- channels at rate `f = 1 / 2`, the detector score `up (1 / 10)` with `δ₀ = 1 / 10` and rank
-- `J = 297600 ≥ 2 C_π m k (k + 1) / δ₀`: the copies have entries at most `f / q = 1 / 4`,
-- intertwine with their projection, and at most `2 · 3` of them are active.
example :
    let M := pilotMax c (down (1 / 2)) (columnDetector all all (up (1 / 10)) (down (1 / 2)) 297600
      1 (1 / 2)) C 15
    let E := cutoffCorrectionIter (fun y t => c t * down (1 / 2) (M y)) C 15
    let D := C - E + E * C
    (∀ a b, copyStage (up (3 / 16)) 31 (detectorWeight (up (1 / 4)) M) D a b ≤ 1 / 2 / 2) ∧
      copyStage (up (3 / 16)) 31 (detectorWeight (up (1 / 4)) M) D *
          copyWeight (detectorWeight (up (1 / 4)) M) =
        copyWeight (detectorWeight (up (1 / 4)) M) * D ∧
      (∀ a b, copyStage (up (3 / 16)) 31 (detectorWeight (up (1 / 4)) M) D a b ≠ 0 →
        a ∈ copyCover univ (overloaded M) ∧ b ∈ copyCover univ (overloaded M)) ∧
      #(copyCover (m := 31) (univ : Finset (Fin 3)) (overloaded M)) ≤
        2 * #(univ : Finset (Fin 3)) :=
  detectedStage_rates (X := all) (Y := all) (ϕ := up (1 / 10)) (ρ := down (1 / 2)) (J := 297600)
    (K := 1) (f := 1 / 2) (c := c) (γ := down (1 / 2)) (C := C) (A := univ) (κ := up (1 / 4))
    (χ := up (3 / 16)) (q := 2) (k := 15) (m := 31) (θ := 1 / 4) (L := 1) (θ₂ := 1 / 4)
    (τ₀ := 3 / 16) (τ₁ := 1 / 4) (δ₀ := 1 / 10)
    (retentionChannels_all (V := Fin 3) (by norm_num) (by norm_num)) hC hC0 hCf hC1
    (fun _ _ _ => ⟨mem_univ _, mem_univ _⟩) (by norm_num) c_nonneg
    (fun t => le_of_eq (by norm_num [c])) c_mono hcL
    (fun t => by norm_num [c]) (by norm_num) zero_le_one (down_nonneg _) (down_le_one _)
    (fun t ht => down_of_le ht) (up_nonneg _) (up_le_one _) (fun t ht => up_of_le ht)
    (fun t ht => up_of_lt (by linarith)) (by norm_num) (up_nonneg _) (up_le_one _) (by norm_num)
    (fun t ht => up_of_le ht) (down_le_one _) (by norm_num) (by norm_num)
    (by linarith [factorial_bound]) (up_nonneg _) (up_le_one _) (fun t ht => up_of_le ht)
    (fun t ht => up_of_lt (by linarith)) (by norm_num) (by norm_num)

end ComplexityTests.Detectors
