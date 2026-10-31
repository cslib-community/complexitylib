/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.ConditionalProductMean
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Fine-bin conditional product comparison

For a fine bin, conditioning must change to its narrower terminal slice before taking an
ordinary error power. The seed space here is the actual finite product `Γ × Υ`: source masks
depend on `Γ`, and the nested terminal masks depend on `Υ`. Every value and error may depend
on both coordinates. No independence of estimated factors is assumed.

The terminal hit probabilities are the actual uniform densities `πa`, `πb`. Changing slices
inside the mean cancels the importance coefficient `πa / πb`; changing the integrated endpoint
mask leaves exactly one factor `πa / πb` outside the power. Thus the scale factor is
`(b / a) ^ s * (πa / πb)`, bounded by a fixed constant times `(b / a) ^ (s - 1)` when the
actual hit probabilities are comparable to their rates.

The product comparison bounds each concrete product using the left row cap in each version,
then applies the existing ordinary-versus-root and coupled product estimates. Source release
still costs exactly `f / u`. Positive terminal densities are stated explicitly; source slices
and the source seed type may be empty.

This proves the fine-product comparison in the proof of [OpenAI2026LogSpace, Lemma 7.3].
Copy projections, detectors, rewards, clipped residual domination and the recursive estimator
remain separate.

## Main results

* `Cslib.rowNormPow_fineMean_le`: change actual conditioning before the ordinary error power.
* `Cslib.rowNormPow_product_sub_le`: bound each product from its own left row cap.
* `Cslib.fineScaleCost_le`: turn the exact density factor into the fine-scale power.
* `Cslib.rowNormPow_fineProductMean_le`: the concrete fine-product comparison with source release.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  proof of Lemma 7.3, September 23, 2026 revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

/-- The ordinary absolute error power contracts through a finite mean, including an empty
mean when the exponent is positive. -/
theorem abs_expect_pow_le {Ω : Type*} (S : Finset Ω) {s : ℕ} (hs : s ≠ 0) (v : Ω → ℝ) :
    |𝔼 σ ∈ S, v σ| ^ s ≤ 𝔼 σ ∈ S, |v σ| ^ s := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [hs]
  have hcard : (#S : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hw : ∑ _σ ∈ S, (#S : ℝ)⁻¹ = 1 := by simp [hcard]
  calc
    _ ≤ (𝔼 σ ∈ S, |v σ|) ^ s := pow_le_pow_left₀ (abs_nonneg _) (abs_expect_le S v) s
    _ ≤ _ := by
      simpa only [expect_eq_sum_div_card, div_eq_inv_mul, mul_sum] using
        Real.pow_arith_mean_le_arith_mean_pow S (fun _ => (#S : ℝ)⁻¹) (fun σ => |v σ|)
          (fun _ _ => by positivity) hw (fun _ _ => abs_nonneg _) s

variable {Ω V : Type*} [Fintype Ω] [Fintype V]

omit [Fintype V] in
/-- The conditional mean of a scaled difference is exactly the difference of the two scaled
conditional means. Thus the product-difference integrand below is the actual mean error. -/
theorem conditionalTableMean_mul_sub (X Y : Ω → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (c : ℝ) (H H' : Ω → V → V → ℝ) (x y : V) :
    conditionalTableMean X Y (fun σ x y => c * (H σ x y - H' σ x y)) x y =
      c * conditionalTableMean X Y H x y - c * conditionalTableMean X Y H' x y := by
  simp only [conditionalTableMean, mul_sub, expect_sub_distrib, ← mul_expect]

/-- The integrated ordinary error of the actual conditional mean is at most the original
integrated ordinary error. The density of each conditioning slice cancels exactly. -/
theorem rowNormPow_conditionalTableMean_le {s : ℕ} {N u : ℝ} (hs : s ≠ 0)
    (hNu : 0 ≤ N * u) (X Y : Ω → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)] (D : Ω → V → V → ℝ) :
    rowNormPow s N u X Y (fun _ x y => conditionalTableMean X Y D x y) ≤
      rowNormPow s N u X Y D := by
  classical
  rw [rowNormPow, rowNormPow, expect_filtered_sum_eq, expect_filtered_sum_eq]
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => sum_le_sum fun y _ => ?_)
    (inv_nonneg.mpr hNu)
  let S : Finset Ω := {σ | X σ x ∧ Y σ y}
  have hmask := expect_mask_const S (|conditionalTableMean X Y D x y| ^ s)
  simp only [S, mem_filter, mem_univ, true_and] at hmask
  rw [hmask]
  have hpoint := mul_le_mul_of_nonneg_left (abs_expect_pow_le S hs (fun σ => D σ x y))
    (show (0 : ℝ) ≤ dens S by positivity)
  have hright : (dens S : ℝ) * (𝔼 σ ∈ S, |D σ x y| ^ s) =
      𝔼 σ, if X σ x ∧ Y σ y then |D σ x y| ^ s else 0 := by
    simpa only [S, mem_filter, mem_univ, true_and, NNRat.smul_def] using
      (Fintype.expect_ite_mem S (fun σ => |D σ x y| ^ s)).symm
  exact hright ▸ hpoint

/-- A deterministic table is weighted by the actual joint source/endpoint densities. -/
theorem rowNormPow_const_eq_dens_sum (s : ℕ) (N u : ℝ) (X Y : Ω → V → Prop)
    [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)] (v : V → V → ℝ) :
    rowNormPow s N u X Y (fun _ => v) =
      (N * u)⁻¹ * ∑ x, ∑ y, (dens {σ | X σ x ∧ Y σ y} : ℝ) * |v x y| ^ s := by
  classical
  rw [rowNormPow, expect_filtered_sum_eq]
  congr 1
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  simpa only [mem_filter, mem_univ, true_and] using
    expect_mask_const ({σ | X σ x ∧ Y σ y} : Finset Ω) (|v x y| ^ s)

private theorem rowNormPow_mul {s : ℕ} {N u c : ℝ} (hc : 0 ≤ c)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (D : Ω → V → V → ℝ) :
    rowNormPow s N u X Y (fun σ x y => c * D σ x y) = c ^ s * rowNormPow s N u X Y D := by
  simp only [rowNormPow, abs_mul, abs_of_nonneg hc, mul_pow, ← mul_sum, ← mul_expect]
  ring

section ProductSlices

variable {Γ Υ : Type*} [Fintype Γ] [Fintype Υ]
  (X : Γ → V → Prop) (Ya Yb : Υ → V → Prop)
  [∀ γ x, Decidable (X γ x)] [∀ τ y, Decidable (Ya τ y)] [∀ τ y, Decidable (Yb τ y)]

omit [Fintype V] in
private theorem conditionalTableMean_two_product (D : (Γ × Υ) → V → V → ℝ) (x y : V) :
    conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x) (fun (σ : Γ × Υ) y => Ya σ.2 y) D x y =
      𝔼 σ ∈ ({γ | X γ x} : Finset Γ) ×ˢ ({τ | Ya τ y} : Finset Υ), D σ x y := by
  unfold conditionalTableMean
  congr 1
  ext σ
  simp

omit [Fintype V] in
private theorem dens_source_terminal (x y : V) :
    (dens {σ : Γ × Υ | X σ.1 x ∧ Ya σ.2 y} : ℝ) =
      (dens {γ | X γ x} : ℝ) * (dens {τ | Ya τ y} : ℝ) := by
  have hset : ({σ : Γ × Υ | X σ.1 x ∧ Ya σ.2 y} : Finset (Γ × Υ)) =
      ({γ | X γ x} : Finset Γ) ×ˢ ({τ | Ya τ y} : Finset Υ) := by
    ext σ
    simp
  rw [hset]
  simp only [nnratCast_dens, card_product, Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

omit [Fintype V] in
/-- Change actual terminal conditioning before any error power is taken. The source can have
an empty slice; only the narrower terminal density is required to be positive. -/
theorem conditionalTableMean_change_terminal {πa πb : ℝ} (hπb : 0 < πb)
    (hYaπ : ∀ y, (dens {τ | Ya τ y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {τ | Yb τ y} : ℝ) = πb)
    (hsub : ∀ τ y, Yb τ y → Ya τ y) (D : (Γ × Υ) → V → V → ℝ)
    (hD : ∀ σ x y, ¬ Yb σ.2 y → D σ x y = 0) (x y : V) :
    conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x) (fun (σ : Γ × Υ) y => Ya σ.2 y)
        (fun σ x y => (πa / πb) * D σ x y) x y =
      conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun (σ : Γ × Υ) y => Yb σ.2 y) D x y := by
  have hT : ({τ | Yb τ y} : Finset Υ).Nonempty := by
    apply dens_ne_zero.mp
    intro hz
    have hpos : (0 : ℝ) < dens {τ | Yb τ y} := by rw [hYbπ]; exact hπb
    rw [hz] at hpos
    norm_num at hpos
  have hTS : ({τ | Yb τ y} : Finset Υ) ⊆ ({τ | Ya τ y} : Finset Υ) := by
    intro τ hτ
    simpa using hsub τ y (by simpa using hτ)
  rw [conditionalTableMean_two_product, conditionalTableMean_two_product,
    expect_product, expect_product]
  refine expect_congr rfl fun γ _ => ?_
  have h := expect_mul_dens_div_of_subset hTS hT (fun τ => D (γ, τ) x y)
    (fun τ _ hτ => hD (γ, τ) x y (by simpa using hτ))
  rwa [hYaπ, hYbπ] at h

/-- For a deterministic table, changing the integrated terminal mask leaves one exact density
ratio outside the error power. This follows from finite product cardinalities. -/
theorem rowNormPow_const_change_terminal (s : ℕ) (N u : ℝ) {πa πb : ℝ} (hπb : 0 < πb)
    (hYaπ : ∀ y, (dens {τ | Ya τ y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {τ | Yb τ y} : ℝ) = πb) (v : V → V → ℝ) :
    rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x) (fun (σ : Γ × Υ) y => Ya σ.2 y) (fun _ => v) =
      (πa / πb) * rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun (σ : Γ × Υ) y => Yb σ.2 y) (fun _ => v) := by
  rw [rowNormPow_const_eq_dens_sum, rowNormPow_const_eq_dens_sum]
  simp_rw [dens_source_terminal, hYaπ, hYbπ]
  have hpoint : ∀ x y, (dens {γ | X γ x} : ℝ) * πa * |v x y| ^ s =
      (πa / πb) * ((dens {γ | X γ x} : ℝ) * πb * |v x y| ^ s) := by
    intro x y
    field_simp
  simp_rw [hpoint]
  simp only [← mul_sum]
  ring

/-- **Fine conditioning before powers**. The supported sample has importance factor
`πa / πb` inside the broad-slice mean. After changing to the fine slice, Jensen contributes
`c ^ s`, while the integrated mask change contributes only one `πa / πb`.
The function may couple both seed coordinates arbitrarily. -/
theorem rowNormPow_fineMean_le {s : ℕ} {N u c πa πb : ℝ} (hs : s ≠ 0)
    (hNu : 0 ≤ N * u) (hc : 0 ≤ c) (hπa : 0 < πa) (hπb : 0 < πb)
    (hYaπ : ∀ y, (dens {τ | Ya τ y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {τ | Yb τ y} : ℝ) = πb)
    (hsub : ∀ τ y, Yb τ y → Ya τ y) (D : (Γ × Υ) → V → V → ℝ)
    (hD : ∀ σ x y, ¬ Yb σ.2 y → D σ x y = 0) :
    rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x) (fun (σ : Γ × Υ) y => Ya σ.2 y)
        (fun _ x y => conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x)
          (fun (σ : Γ × Υ) y => Ya σ.2 y)
          (fun σ x y => c * (πa / πb) * D σ x y) x y) ≤
      c ^ s * (πa / πb) * rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun (σ : Γ × Υ) y => Yb σ.2 y) D := by
  have hchange : ∀ x y,
      conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x) (fun (σ : Γ × Υ) y => Ya σ.2 y)
          (fun σ x y => c * (πa / πb) * D σ x y) x y =
        c * conditionalTableMean (fun (σ : Γ × Υ) x => X σ.1 x)
          (fun (σ : Γ × Υ) y => Yb σ.2 y) D x y := by
    intro x y
    have hcomm : (fun σ x y => c * (πa / πb) * D σ x y) =
        (fun σ x y => (πa / πb) * (c * D σ x y)) := by funext σ x y; ring
    rw [hcomm, conditionalTableMean_change_terminal X Ya Yb hπb hYaπ hYbπ hsub
      (fun σ x y => c * D σ x y) (fun σ x y h => by rw [hD σ x y h, mul_zero])]
    exact (mul_expect ..).symm
  simp_rw [hchange]
  rw [rowNormPow_const_change_terminal X Ya Yb s N u hπb hYaπ hYbπ, rowNormPow_mul hc]
  calc
    _ ≤ (πa / πb) * (c ^ s * rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun (σ : Γ × Υ) y => Yb σ.2 y) D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (rowNormPow_conditionalTableMean_le hs hNu _ _ D) (by positivity)) (by positivity)
    _ = _ := by ring

end ProductSlices

private theorem sum_mul_le_of_row_cap {α : Type*} (T : Finset α) {A D : α → ℝ}
    {CA CD : ℝ} {K : ℕ} (hCA : 0 ≤ CA) (hCD : 0 ≤ CD)
    (hA : ∀ z, A z ≤ CA) (hD0 : ∀ z, 0 ≤ D z) (hD : ∀ z, D z ≤ CD)
    (hK : #{z ∈ T | A z ≠ 0} ≤ K) : ∑ z ∈ T, A z * D z ≤ K * CA * CD := by
  classical
  have hsum : ∑ z ∈ T, A z * D z = ∑ z ∈ T with A z ≠ 0, A z * D z := by
    rw [sum_filter]
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : A z = 0 <;> simp [hz]
  rw [hsum]
  calc
    _ ≤ ∑ z ∈ T with A z ≠ 0, CA * CD :=
      sum_le_sum fun z _ => mul_le_mul (hA z) (hD z) (hD0 z) hCA
    _ = (#{z ∈ T | A z ≠ 0} : ℝ) * (CA * CD) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ K * (CA * CD) := mul_le_mul_of_nonneg_right (by exact_mod_cast hK) (mul_nonneg hCA hCD)
    _ = _ := by ring

/-- **Ordinary coupled product errors**. Both left row caps bound each actual product by
`Kf * CF * CB`. The resulting ordinary-versus-root factor is explicit, and the remaining
product estimate retains the exact source-release factor `f / u`. -/
theorem rowNormPow_product_sub_le {s Kf Kr Kc : ℕ} {N u f CF CB : ℝ}
    {X Z Y : Ω → V → Prop}
    [∀ σ x, Decidable (X σ x)] [∀ σ z, Decidable (Z σ z)] [∀ σ y, Decidable (Y σ y)]
    (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u) (hf : 0 < f) (hCF : 0 ≤ CF) (hCB : 0 ≤ CB)
    {F F' B B' : Ω → V → V → ℝ}
    (hF : ∀ σ x z, 0 ≤ F σ x z) (hF' : ∀ σ x z, 0 ≤ F' σ x z)
    (hB : ∀ σ z y, 0 ≤ B σ z y) (hB' : ∀ σ z y, 0 ≤ B' σ z y)
    (hFbound : ∀ σ x z, F σ x z ≤ CF) (hF'bound : ∀ σ x z, F' σ x z ≤ CF)
    (hBbound : ∀ σ z y, B σ z y ≤ CB) (hB'bound : ∀ σ z y, B' σ z y ≤ CB)
    (hleft : ∀ σ x, X σ x → #{z ∈ ({z | Z σ z} : Finset V) | F σ x z ≠ 0} ≤ Kf)
    (hleft' : ∀ σ x, X σ x → #{z ∈ ({z | Z σ z} : Finset V) | F' σ x z ≠ 0} ≤ Kf)
    (hrow : ∀ σ z, Z σ z → #{y ∈ ({y | Y σ y} : Finset V) | B σ z y ≠ 0} ≤ Kr)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ x} : Finset V) | F' σ x z ≠ 0} ≤ Kc) :
    rowNormPow s N u X Y (fun σ x y =>
        (∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y) -
          ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y) ≤
      ((s : ℝ) * ((Kf : ℝ) * CF * CB) ^ (((s : ℝ) - 1) / s)) ^ s *
        (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
        (CB * Kr * rootDistPow s N u X Z F F' +
          CF * Kc * (f / u) * rootDistPow s N f Z Y B B') := by
  have hproduct : rowNormPow s N u X Y (fun σ x y =>
        (∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y) -
          ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y) ≤
      ((s : ℝ) * ((Kf : ℝ) * CF * CB) ^ (((s : ℝ) - 1) / s)) ^ s *
        rootDistPow s N u X Y
          (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y)
          (fun σ x y => ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y) := by
    refine rowNormPow_sub_le_rootDistPow hs (by positivity) ?_ ?_
    · intro σ x y hx _
      exact ⟨sum_nonneg fun z _ => mul_nonneg (hF σ x z) (hB σ z y),
        sum_mul_le_of_row_cap _ hCF hCB (hFbound σ x) (fun z => hB σ z y)
          (fun z => hBbound σ z y) (hleft σ x hx)⟩
    · intro σ x y hx _
      exact ⟨sum_nonneg fun z _ => mul_nonneg (hF' σ x z) (hB' σ z y),
        sum_mul_le_of_row_cap _ hCF hCB (hF'bound σ x) (fun z => hB' σ z y)
          (fun z => hB'bound σ z y) (hleft' σ x hx)⟩
  calc
    _ ≤ _ := hproduct
    _ ≤ ((s : ℝ) * ((Kf : ℝ) * CF * CB) ^ (((s : ℝ) - 1) / s)) ^ s *
        ((2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
          (CB * Kr * rootDistPow s N u X Z F F' +
            CF * Kc * (f / u) * rootDistPow s N f Z Y B B')) :=
      mul_le_mul_of_nonneg_left
        (rootDistPow_mul_le hs hN hu hf hF hF' hB hB' hCF hCB hF'bound hBbound hrow hcol)
        (by positivity)
    _ = _ := by ring

/-- The exact terminal-density factor becomes the fine-scale power `s - 1` when the actual
hit probabilities are bounded above and below by fixed multiples of their positive rates. -/
theorem fineScaleCost_le {s : ℕ} (hs : s ≠ 0) {a b πa πb Ca cb : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hπb : 0 < πb)
    (hCa : 0 ≤ Ca) (hcb : 0 < cb) (hupper : πa ≤ Ca * a) (hlower : cb * b ≤ πb) :
    (b / a) ^ s * (πa / πb) ≤ (Ca / cb) * (b / a) ^ (s - 1) := by
  have hratio : πa / πb ≤ (Ca / cb) * (a / b) := by
    calc
      _ ≤ (Ca * a) / (cb * b) := by
        rw [div_le_div_iff₀ hπb (mul_pos hcb hb)]
        exact (mul_le_mul_of_nonneg_right hupper (mul_nonneg hcb.le hb.le)).trans
          (mul_le_mul_of_nonneg_left hlower (mul_nonneg hCa ha.le))
      _ = _ := by ring
  have hcancel : (b / a) ^ s * (a / b) = (b / a) ^ (s - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hs
    rw [Nat.add_sub_cancel, pow_succ]
    field_simp
  calc
    _ ≤ (b / a) ^ s * ((Ca / cb) * (a / b)) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (Ca / cb) * ((b / a) ^ s * (a / b)) := by ring
    _ = _ := by rw [hcancel]

/-- **Fine-bin conditional product comparison** [OpenAI2026LogSpace, proof of Lemma 7.3].
Both sample products are concrete finite sums. The actual terminal density ratio is removed
inside the conditional mean and paid once outside the power. The two left row caps prove the
product bound used in the ordinary-versus-root comparison. All estimated factors may be coupled.

The rates satisfy `0 < b ≤ a`, and the actual densities satisfy `πa ≤ Ca * a` and
`cb * b ≤ πb`. The explicit scale factor is therefore
`(f / πf) ^ s * (Ca / cb) * (b / a) ^ (s - 1)`; the right child still costs exactly `f / u`.
This is an ordinary mean-error bound, so clipped relative error is no larger when its normalized
denominator is at least one. -/
theorem rowNormPow_fineProductMean_le {Γ Υ : Type*} [Fintype Γ] [Fintype Υ]
    {s Kf Kr Kc : ℕ} {N u a b f πa πb πf Ca cb CF CB : ℝ}
    (X : Γ → V → Prop) (Ya Yb : Υ → V → Prop) (Z : (Γ × Υ) → V → Prop)
    [∀ γ x, Decidable (X γ x)] [∀ τ y, Decidable (Ya τ y)] [∀ τ y, Decidable (Yb τ y)]
    [∀ σ z, Decidable (Z σ z)]
    (hs : s ≠ 0) (hN : 0 < N) (hu : 0 < u) (hb : 0 < b) (hba : b ≤ a)
    (hf : 0 < f) (hπa : 0 < πa) (hπb : 0 < πb) (hπf : 0 < πf)
    (hCa : 0 ≤ Ca) (hcb : 0 < cb) (hupper : πa ≤ Ca * a) (hlower : cb * b ≤ πb)
    (hYaπ : ∀ y, (dens {τ | Ya τ y} : ℝ) = πa)
    (hYbπ : ∀ y, (dens {τ | Yb τ y} : ℝ) = πb) (hsub : ∀ τ y, Yb τ y → Ya τ y)
    (hCF : 0 ≤ CF) (hCB : 0 ≤ CB) {F F' B B' : (Γ × Υ) → V → V → ℝ}
    (hF : ∀ σ x z, 0 ≤ F σ x z) (hF' : ∀ σ x z, 0 ≤ F' σ x z)
    (hB : ∀ σ z y, 0 ≤ B σ z y) (hB' : ∀ σ z y, 0 ≤ B' σ z y)
    (hFbound : ∀ σ x z, F σ x z ≤ CF) (hF'bound : ∀ σ x z, F' σ x z ≤ CF)
    (hBbound : ∀ σ z y, B σ z y ≤ CB) (hB'bound : ∀ σ z y, B' σ z y ≤ CB)
    (hleft : ∀ σ x, X σ.1 x → #{z ∈ ({z | Z σ z} : Finset V) | F σ x z ≠ 0} ≤ Kf)
    (hleft' : ∀ σ x, X σ.1 x → #{z ∈ ({z | Z σ z} : Finset V) | F' σ x z ≠ 0} ≤ Kf)
    (hrow : ∀ σ z, Z σ z → #{y ∈ ({y | Yb σ.2 y} : Finset V) | B σ z y ≠ 0} ≤ Kr)
    (hcol : ∀ σ z, Z σ z → #{x ∈ ({x | X σ.1 x} : Finset V) | F' σ x z ≠ 0} ≤ Kc)
    (hBsupport : ∀ σ z y, ¬ Yb σ.2 y → B σ z y = 0)
    (hB'support : ∀ σ z y, ¬ Yb σ.2 y → B' σ z y = 0) :
    let E := fun σ x y => (∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y) -
      ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y
    rowNormPow s N u (fun (σ : Γ × Υ) x => X σ.1 x) (fun σ y => Ya σ.2 y)
        (fun _ x y => conditionalTableMean (fun σ x => X σ.1 x) (fun σ y => Ya σ.2 y)
          (fun σ x y => (b / a) * (f / πf) * (πa / πb) * E σ x y) x y) ≤
      ((f / πf) ^ s * (Ca / cb) * (b / a) ^ (s - 1)) *
        (((s : ℝ) * ((Kf : ℝ) * CF * CB) ^ (((s : ℝ) - 1) / s)) ^ s *
          (2 ^ (2 * (s - 1)) * (s : ℝ) ^ s) *
          (CB * Kr * rootDistPow s N u (fun σ x => X σ.1 x) Z F F' +
            CF * Kc * (f / u) * rootDistPow s N f Z (fun σ y => Yb σ.2 y) B B')) := by
  dsimp only
  let E : (Γ × Υ) → V → V → ℝ := fun σ x y =>
    (∑ z ∈ ({z | Z σ z} : Finset V), F σ x z * B σ z y) -
      ∑ z ∈ ({z | Z σ z} : Finset V), F' σ x z * B' σ z y
  have ha : 0 < a := hb.trans_le hba
  have hNu : 0 ≤ N * u := mul_nonneg hN.le hu.le
  have hEsupport : ∀ σ x y, ¬ Yb σ.2 y → E σ x y = 0 := by
    intro σ x y hy
    simp [E, hBsupport σ _ y hy, hB'support σ _ y hy]
  have hscale : ((b / a) * (f / πf)) ^ s * (πa / πb) ≤
      (f / πf) ^ s * (Ca / cb) * (b / a) ^ (s - 1) := by
    rw [mul_pow]
    calc
      _ = (f / πf) ^ s * ((b / a) ^ s * (πa / πb)) := by ring
      _ ≤ (f / πf) ^ s * ((Ca / cb) * (b / a) ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left (fineScaleCost_le hs ha hb hπb hCa hcb hupper hlower)
          (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ((b / a) * (f / πf)) ^ s * (πa / πb) *
        rowNormPow s N u (fun σ x => X σ.1 x) (fun σ y => Yb σ.2 y) E :=
      rowNormPow_fineMean_le X Ya Yb hs hNu (by positivity) hπa hπb hYaπ hYbπ hsub E hEsupport
    _ ≤ ((f / πf) ^ s * (Ca / cb) * (b / a) ^ (s - 1)) *
        rowNormPow s N u (fun σ x => X σ.1 x) (fun σ y => Yb σ.2 y) E :=
      mul_le_mul_of_nonneg_right hscale (rowNormPow_nonneg hNu E)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rowNormPow_product_sub_le hs hN hu hf hCF hCB hF hF' hB hB' hFbound hF'bound
        hBbound hB'bound hleft hleft' hrow hcol) (by positivity)

end Cslib
