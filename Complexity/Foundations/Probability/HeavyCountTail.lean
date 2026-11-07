/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HeavyCountRarity
public import Complexity.Foundations.Probability.RootMetric.Minkowski
public import Complexity.Foundations.Analysis.RowCompression.OverflowBudget

/-!
# Rare mean tails and correlated first-overflow noise

Conditional rarity contracts deterministic endpoint mean errors before finite Minkowski sums
are formed. The resulting weighted mean-tail budget contains the `p`-th root of each rarity
factor. Correlated noise instead uses the existing unconditional actual first-overflow budget.
A pointwise comparison connects their sum to the actual true-overflow mask in compression.

These are finite, exponent-parametric versions of the mean and noise aggregation in
[OpenAI2026LogSpace, Section 8.4, proof of Proposition 8.5], source labels `buf-true-sum` and
`buf-noise-sum`, revision `7ef5c0cc` (23 September 2026, not peer reviewed). Fourth moments
are included. Conditional rarity and the individual mean/noise budgets remain hypotheses;
this module does not derive them for the recursive estimator or choose convergent schedules.

## Main results

* `Cslib.vertexNormPow_heavyCountTail_le`: the weighted deterministic mean-tail budget.
* `Cslib.vertexNormPow_trueOverflowTail_le`: the actual mixed tail with unconditional noise.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, proof of Proposition 8.5, equations `buf-true-sum` and `buf-noise-sum`,
  revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

/-- A finite weighted tail selected by each row event. -/
@[expose] noncomputable def eventTail (m : ℕ) (Θ : ℕ → Ω → V → Prop)
    (w : ℕ → ℝ) (β : ℕ → Ω → V → ℝ) (σ : Ω) (x : V) : ℝ := by
  classical
  exact ∑ j ∈ range m, if Θ j σ x then ∑ i ∈ Ico j m, w i * β i σ x else 0

/-- Conditional rarity for deterministic endpoint errors gives a rooted rarity factor for each
weighted tail. All retained sets and row events may depend on the same environment. -/
theorem vertexNormPow_eventTail_le {p : ℕ} (hp : p ≠ 0) {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (m : ℕ) (Θ : ℕ → Ω → V → Prop) [∀ j σ x, Decidable (Θ j σ x)]
    (q w ε : ℕ → ℝ) (b : ℕ → V → V → ℝ)
    (hq : ∀ j < m, 0 ≤ q j) (hw : ∀ i < m, 0 ≤ w i) (hε : ∀ i < m, 0 ≤ ε i)
    (hrare : ∀ j < m, ∀ x y, (#{σ | X σ x ∧ Y σ y ∧ Θ j σ x} : ℝ) ≤
      q j * #{σ | X σ x ∧ Y σ y})
    (hmean : ∀ i < m, rowNormPow p N u X Y (fun _ x y => b i x y) ≤ ε i ^ p) :
    vertexNormPow p N u X (eventTail m Θ w (fun i σ x =>
      kthLargest 1 {y | Y σ y} (fun y => |b i x y|))) ≤
      (∑ j ∈ range m, (q j) ^ (p⁻¹ : ℝ) * ∑ i ∈ Ico j m, w i * ε i) ^ p := by
  classical
  let β := fun i σ x => kthLargest 1 {y | Y σ y} (fun y => |b i x y|)
  let B := fun j => (q j) ^ (p⁻¹ : ℝ) * ∑ i ∈ Ico j m, w i * ε i
  have hB (j : ℕ) (hj : j < m) : 0 ≤ B j :=
    mul_nonneg (Real.rpow_nonneg (hq j hj) _)
      (sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hε i (mem_Ico.mp hi).2))
  have hterm (j : ℕ) (hj : j < m) :
      vertexNormPow p N u X (fun σ x => if Θ j σ x then
        ∑ i ∈ Ico j m, w i * β i σ x else 0) ≤ B j ^ p := by
    have hbudget (i : ℕ) (hi : i ∈ Ico j m) :
        vertexNormPow p N u X (fun σ x => if Θ j σ x then β i σ x else 0) ≤
          ((q j) ^ (p⁻¹ : ℝ) * ε i) ^ p := by
      have h := (vertexNormPow_kthLargest_event_le hp hNu (hrare j hj) (b i)).trans
        (mul_le_mul_of_nonneg_left (hmean i (mem_Ico.mp hi).2) (hq j hj))
      simpa only [mul_pow, Real.rpow_inv_natCast_pow (hq j hj) hp] using h
    have h := vertexNormPow_sum_le_pow_sum hp hNu (Ico j m)
      (fun i σ x => if Θ j σ x then β i σ x else 0) w
      (fun i => (q j) ^ (p⁻¹ : ℝ) * ε i)
      (fun i hi => hw i (mem_Ico.mp hi).2)
      (fun i hi => mul_nonneg (Real.rpow_nonneg (hq j hj) _) (hε i (mem_Ico.mp hi).2)) hbudget
    have hmask : (fun σ x => ∑ i ∈ Ico j m, w i * (if Θ j σ x then β i σ x else 0)) =
        (fun σ x => if Θ j σ x then ∑ i ∈ Ico j m, w i * β i σ x else 0) := by
      funext σ x
      by_cases h : Θ j σ x <;> simp [h]
    have hsum : (∑ i ∈ Ico j m, w i * ((q j) ^ (p⁻¹ : ℝ) * ε i)) = B j := by
      dsimp only [B]
      rw [mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    simpa only [hmask, hsum] using h
  have h := vertexNormPow_sum_le_pow_sum hp hNu (range m)
    (fun j σ x => if Θ j σ x then ∑ i ∈ Ico j m, w i * β i σ x else 0)
    (fun _ => 1) B (by intros; norm_num) (fun j hj => hB j (mem_range.mp hj))
    (fun j hj => hterm j (mem_range.mp hj))
  have heq : eventTail m Θ w β = (fun σ x => ∑ j ∈ range m,
      if Θ j σ x then ∑ i ∈ Ico j m, w i * β i σ x else 0) := by
    funext σ x
    unfold eventTail
    apply sum_congr rfl
    intro j _
    by_cases hj : Θ j σ x <;> simp only [hj, ↓reduceIte]
  change vertexNormPow p N u X (eventTail m Θ w β) ≤ _
  rw [heq]
  simpa only [one_mul, β, B] using h

open Classical in
/-- The actual heavy-count events may be substituted directly in the weighted mean bound.
The rarity premise is conditional on the source and usage endpoint; it does not require
independence and may be supplied by `Probability.card_filter_heavyCountEvent_le`. -/
theorem vertexNormPow_heavyCountTail_le {p : ℕ} (hp : p ≠ 0) {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y Yt : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Yt σ y)]
    (m : ℕ) (d : V → V → ℝ) (ρ : ℕ → ℝ) (n : ℕ → ℕ)
    (q w ε : ℕ → ℝ) (b : ℕ → V → V → ℝ)
    (hq : ∀ j < m, 0 ≤ q j) (hw : ∀ i < m, 0 ≤ w i) (hε : ∀ i < m, 0 ≤ ε i)
    (hrare : ∀ j < m, ∀ x y,
      (#{σ | X σ x ∧ Yt σ y ∧ Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ} : ℝ) ≤
        q j * #{σ | X σ x ∧ Yt σ y})
    (hmean : ∀ i < m, rowNormPow p N u X Yt (fun _ x y => b i x y) ≤ ε i ^ p) :
    vertexNormPow p N u X (eventTail m
      (fun j σ x => Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ) w
      (fun i σ x => kthLargest 1 {y | Yt σ y} (fun y => |b i x y|))) ≤
      (∑ j ∈ range m, (q j) ^ (p⁻¹ : ℝ) * ∑ i ∈ Ico j m, w i * ε i) ^ p := by
  classical
  exact vertexNormPow_eventTail_le hp hNu X Yt m _ q w ε b hq hw hε hrare hmean

private theorem vertexNormPow_add_le_budgets {p : ℕ} (hp : p ≠ 0) {N u : ℝ}
    (hNu : 0 ≤ N * u) (X : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    (f g : Ω → V → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : vertexNormPow p N u X f ≤ a ^ p) (hg : vertexNormPow p N u X g ≤ b ^ p) :
    vertexNormPow p N u X (fun σ x => f σ x + g σ x) ≤ (a + b) ^ p := by
  have h := vertexNormPow_add_rpow_le (X := X) hp hNu f g
  have hf' := (Real.rpow_le_rpow (vertexNormPow_nonneg hNu f) hf (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast ha hp)
  have hg' := (Real.rpow_le_rpow (vertexNormPow_nonneg hNu g) hg (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast hb hp)
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (vertexNormPow_nonneg hNu _) _) (h.trans (add_le_add hf' hg')) p
  rwa [Real.rpow_inv_natCast_pow (vertexNormPow_nonneg hNu _) hp] at hpow

open Classical in
/-- A deterministic rare mean tail and actual correlated first-overflow noise add their rooted
budgets. Noise receives no rarity factor, even when concentrated on the heavy event. -/
private theorem vertexNormPow_heavyCountTail_add_noise_le {ι : Type*} {p : ℕ} (hp : p ≠ 0)
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y Yt : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Yt σ y)]
    (m : ℕ) (d : V → V → ℝ) (ρ : ℕ → ℝ) (n : ℕ → ℕ)
    (q w ε δ : ℕ → ℝ) (b : ℕ → V → V → ℝ)
    (hq : ∀ j < m, 0 ≤ q j) (hw : ∀ i < m, 0 ≤ w i)
    (hε : ∀ i < m, 0 ≤ ε i) (hδ : ∀ i < m, 0 ≤ δ i)
    (hrare : ∀ j < m, ∀ x y,
      (#{σ | X σ x ∧ Yt σ y ∧ Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ} : ℝ) ≤
        q j * #{σ | X σ x ∧ Yt σ y})
    (hmean : ∀ i < m, rowNormPow p N u X Yt (fun _ x y => b i x y) ≤ ε i ^ p)
    (S : Ω → V → Finset ι) (capacity : ℕ → ℕ) (floor : ℕ → ℝ)
    (Δ : Ω → V → ℕ → ι → Fin 2 → ℝ) (a : Ω → V → RowCompression.State ι)
    (γ : ℕ → Ω → V → ℝ)
    (hγ : ∀ i < m, ∀ σ x, X σ x → 0 ≤ γ i σ x)
    (hnoise : ∀ i < m, vertexNormPow p N u X (γ i) ≤ δ i ^ p) :
    vertexNormPow p N u X (fun σ x =>
      eventTail m (fun j σ x => Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ) w
        (fun i σ x => kthLargest 1 {y | Yt σ y} (fun y => |b i x y|)) σ x +
      RowCompression.firstOverflowNoiseTail (S σ x) n capacity floor (Δ σ x) (a σ x) m w
        (fun i => γ i σ x)) ≤
      ((∑ j ∈ range m, (q j) ^ (p⁻¹ : ℝ) * ∑ i ∈ Ico j m, w i * ε i) +
        ∑ i ∈ range m, w i * δ i) ^ p := by
  classical
  refine vertexNormPow_add_le_budgets hp hNu X _ _ ?_ ?_ ?_ ?_
  · exact sum_nonneg fun j hj => mul_nonneg (Real.rpow_nonneg (hq j (mem_range.mp hj)) _)
      (sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hε i (mem_Ico.mp hi).2))
  · exact sum_nonneg fun i hi => mul_nonneg (hw i (mem_range.mp hi)) (hδ i (mem_range.mp hi))
  · exact vertexNormPow_heavyCountTail_le hp hNu X Y Yt m d ρ n q w ε b hq hw hε hrare hmean
  · exact RowCompression.vertexNormPow_firstOverflowNoiseTail_le_pow_sum S n capacity floor
      Δ a m hp hNu X w δ γ hw hδ hγ hnoise

namespace RowCompression

open Classical in
/-- The actual true-overflow tail is bounded by the enlarged heavy mean tail plus the unique
actual first-overflow noise tail. This is pointwise and requires no independence. -/
theorem trueOverflowTail_le_add {ι : Type*} (S : Finset ι) (n K : ℕ → ℕ) (ρ : ℕ → ℝ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (m : ℕ) (heavy : ℕ → Prop)
    (w β γ : ℕ → ℝ) (hw : ∀ i < m, 0 ≤ w i)
    (hβ : ∀ i < m, 0 ≤ β i) (hγ : ∀ i < m, 0 ≤ γ i) :
    (∑ j ∈ range m, if IsFirstOverflow S n K ρ Δ a j ∧ heavy j then
      ∑ i ∈ Ico j m, w i * (β i + γ i) else 0) ≤
      (∑ j ∈ range m, if heavy j then ∑ i ∈ Ico j m, w i * β i else 0) +
        firstOverflowNoiseTail S n K ρ Δ a m w γ := by
  classical
  unfold firstOverflowNoiseTail
  rw [← sum_add_distrib]
  refine sum_le_sum fun j hj => ?_
  have hβtail : 0 ≤ ∑ i ∈ Ico j m, w i * β i :=
    sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hβ i (mem_Ico.mp hi).2)
  have hγtail : 0 ≤ ∑ i ∈ Ico j m, w i * γ i :=
    sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hγ i (mem_Ico.mp hi).2)
  by_cases ho : IsFirstOverflow S n K ρ Δ a j <;> by_cases hh : heavy j <;>
    simp [ho, hh, mul_add, sum_add_distrib, hβtail, hγtail]

end RowCompression

open Classical in
/-- The actual true-first-overflow mixed tail has a rare deterministic-mean budget and a
correlated-noise budget with no rarity discount. This matches the tail mask consumed by the
compression assembly, after a pointwise mean/noise envelope has been supplied. -/
theorem vertexNormPow_trueOverflowTail_le {ι : Type*} {p : ℕ} (hp : p ≠ 0)
    {N u : ℝ} (hNu : 0 ≤ N * u)
    (X Y Yt : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Yt σ y)]
    (m : ℕ) (d : V → V → ℝ) (ρ : ℕ → ℝ) (n : ℕ → ℕ)
    (q w ε δ : ℕ → ℝ) (b : ℕ → V → V → ℝ)
    (hq : ∀ j < m, 0 ≤ q j) (hw : ∀ i < m, 0 ≤ w i)
    (hε : ∀ i < m, 0 ≤ ε i) (hδ : ∀ i < m, 0 ≤ δ i)
    (hrare : ∀ j < m, ∀ x y,
      (#{σ | X σ x ∧ Yt σ y ∧ Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ} : ℝ) ≤
        q j * #{σ | X σ x ∧ Yt σ y})
    (hmean : ∀ i < m, rowNormPow p N u X Yt (fun _ x y => b i x y) ≤ ε i ^ p)
    (S : Ω → V → Finset ι) (capacity : ℕ → ℕ) (floor : ℕ → ℝ)
    (Δ : Ω → V → ℕ → ι → Fin 2 → ℝ) (a : Ω → V → RowCompression.State ι)
    (γ : ℕ → Ω → V → ℝ)
    (hγ : ∀ i < m, ∀ σ x, X σ x → 0 ≤ γ i σ x)
    (hnoise : ∀ i < m, vertexNormPow p N u X (γ i) ≤ δ i ^ p) :
    vertexNormPow p N u X (fun σ x => ∑ j ∈ range m,
      if RowCompression.IsFirstOverflow (S σ x) n capacity floor (Δ σ x) (a σ x) j ∧
          Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ then
        ∑ i ∈ Ico j m, w i *
          (kthLargest 1 {y | Yt σ y} (fun y => |b i x y|) + γ i σ x) else 0) ≤
      ((∑ j ∈ range m, (q j) ^ (p⁻¹ : ℝ) * ∑ i ∈ Ico j m, w i * ε i) +
        ∑ i ∈ range m, w i * δ i) ^ p := by
  classical
  have hbudget := vertexNormPow_heavyCountTail_add_noise_le hp hNu X Y Yt m d ρ n
    q w ε δ b hq hw hε hδ hrare hmean S capacity floor Δ a γ hγ hnoise
  refine le_trans ?_ hbudget
  unfold vertexNormPow
  refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
  refine sum_le_sum fun x hx => ?_
  have hx' := (mem_filter.mp hx).2
  let β := fun i => kthLargest 1 {y | Yt σ y} (fun y => |b i x y|)
  have hβ (i : ℕ) (_hi : i < m) : 0 ≤ β i := kthLargest_nonneg
  have hselected := RowCompression.trueOverflowTail_le_add (S σ x) n capacity floor
    (Δ σ x) (a σ x) m
    (fun j => Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ)
    w β (fun i => γ i σ x) hw hβ (fun i hi => hγ i hi σ x hx')
  have hleft0 : 0 ≤ ∑ j ∈ range m,
      if RowCompression.IsFirstOverflow (S σ x) n capacity floor (Δ σ x) (a σ x) j ∧
          Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ then
        ∑ i ∈ Ico j m, w i * (β i + γ i σ x) else 0 := by
    refine sum_nonneg fun j _ => ?_
    split_ifs
    · exact sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2)
        (add_nonneg (hβ i (mem_Ico.mp hi).2) (hγ i (mem_Ico.mp hi).2 σ x hx'))
    · exact le_rfl
  have hright0 : 0 ≤ eventTail m
      (fun j σ x => Probability.heavyCountEvent Y univ (d x) (ρ j) (n j) σ) w
      (fun i σ x => kthLargest 1 {y | Yt σ y} (fun y => |b i x y|)) σ x +
      RowCompression.firstOverflowNoiseTail (S σ x) n capacity floor (Δ σ x) (a σ x) m w
        (fun i => γ i σ x) := by
    apply add_nonneg
    · unfold eventTail
      refine sum_nonneg fun j _ => ?_
      split_ifs
      · exact sum_nonneg fun i hi => mul_nonneg (hw i (mem_Ico.mp hi).2) (hβ i (mem_Ico.mp hi).2)
      · exact le_rfl
    · exact RowCompression.firstOverflowNoiseTail_nonneg (S σ x) n capacity floor
        (Δ σ x) (a σ x) m hw (fun i hi => hγ i hi σ x hx')
  rw [abs_of_nonneg hleft0, abs_of_nonneg hright0]
  exact pow_le_pow_left₀ hleft0 (by simpa only [eventTail, β] using hselected) p

end Cslib
