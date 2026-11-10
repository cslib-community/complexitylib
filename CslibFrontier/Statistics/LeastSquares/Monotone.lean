/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Single-observation monotonicity of weighted least squares

This module proves the rank-one update and single-weight monotonicity of
[XuGaoHu2027], Lemma 3.1 (PDF p. 6, printed p. 4). The base Gram
matrix is positive definite; the new observation has arbitrary real design vector
and response, and its weight ranges over the nonnegative reals. Every linear
functional of the actual inverse-matrix least-squares estimate is monotone or
antitone. No sign hypothesis on the response or target is required.

The module also proves successive rounding with a positive definite fixed backbone,
including strict retained-mass loss below the number of fractional weights. The full
Theorem 3.3 remains unproved: sparse optimal weights, attainment and the construction
of the backbone from general position are not provided here.

## Main definitions

* `rankOneGram`: addition of one weighted observation to a Gram matrix.
* `rankOneEstimate`: the least-squares estimate after that addition.

## Main results

* `rankOneEstimate_eq`: exact Sherman–Morrison estimate formula.
* `rankOneEstimate_monotone_or_antitone`: every linear target is monotone in the weight.
* `exists_round_weights_loss_lt`: rounding with a positive definite backbone and strict mass loss.

## References

* [XuGaoHu2027], Lemma 3.1, PDF p. 6.
-/

public section

namespace Cslib.LeastSquares

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Gram matrix after adding an observation `x` with weight `a`. -/
@[expose] def rankOneGram (G : Matrix d d ℝ) (x : d → ℝ) (a : ℝ) : Matrix d d ℝ :=
  G + a • vecMulVec x x

/-- The actual weighted least-squares estimate with one additional observation. -/
@[expose] noncomputable def rankOneEstimate (G : Matrix d d ℝ) (g x : d → ℝ)
    (y a : ℝ) : d → ℝ :=
  (rankOneGram G x a)⁻¹ *ᵥ (g + (a * y) • x)

omit [Fintype d] [DecidableEq d] in
/-- Adding a nonnegative observation weight preserves positive definiteness. -/
theorem rankOneGram_posDef [Finite d] {G : Matrix d d ℝ} (hG : G.PosDef)
    (x : d → ℝ) {a : ℝ} (ha : 0 ≤ a) : (rankOneGram G x a).PosDef := by
  have hx : (vecMulVec x x).PosSemidef := by
    simpa using posSemidef_vecMulVec_self_star x
  exact hG.add_posSemidef (hx.smul ha)

/-- The leverage of an observation relative to a positive definite Gram matrix is nonnegative. -/
theorem leverage_nonneg {G : Matrix d d ℝ} (hG : G.PosDef) (x : d → ℝ) :
    0 ≤ x ⬝ᵥ (G⁻¹ *ᵥ x) := by
  simpa using hG.inv.posSemidef.dotProduct_mulVec_nonneg x

/-- Sherman–Morrison, specialized to the least-squares estimate. -/
theorem rankOneEstimate_eq {G : Matrix d d ℝ} (hG : G.PosDef)
    (g x : d → ℝ) (y : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    rankOneEstimate G g x y a =
      G⁻¹ *ᵥ g + (a / (1 + a * (x ⬝ᵥ (G⁻¹ *ᵥ x))) *
        (y - x ⬝ᵥ (G⁻¹ *ᵥ g))) • (G⁻¹ *ᵥ x) := by
  have hden : 1 + a * (x ⬝ᵥ (G⁻¹ *ᵥ x)) ≠ 0 :=
    ne_of_gt (by have := mul_nonneg ha (leverage_nonneg hG x); linarith)
  have hdet := (isUnit_iff_isUnit_det G).mp hG.isUnit
  have hinv (v : d → ℝ) : G *ᵥ (G⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hnew := rankOneGram_posDef hG x ha
  apply hnew.mulVec_injective
  rw [rankOneEstimate, mulVec_mulVec,
    mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hnew.isUnit), one_mulVec]
  simp only [rankOneGram, add_mulVec, mulVec_add, mulVec_smul, hinv,
    smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

private theorem monotoneOn_weightFraction {η : ℝ} (hη : 0 ≤ η) :
    MonotoneOn (fun a : ℝ => a / (1 + a * η)) (Set.Ici 0) := by
  intro a ha b hb hab
  have hda : 0 < 1 + a * η := by nlinarith [mul_nonneg ha hη]
  have hdb : 0 < 1 + b * η := by nlinarith [mul_nonneg hb hη]
  apply (div_le_div_iff₀ hda hdb).mpr
  nlinarith

/-- Every linear functional of the actual estimate is monotone or antitone as
one nonnegative observation weight varies. This is Lemma 3.1 of STOC submission 1326. -/
theorem rankOneEstimate_monotone_or_antitone {G : Matrix d d ℝ} (hG : G.PosDef)
    (g x e : d → ℝ) (y : ℝ) :
    MonotoneOn (fun a => e ⬝ᵥ rankOneEstimate G g x y a) (Set.Ici 0) ∨
      AntitoneOn (fun a => e ⬝ᵥ rankOneEstimate G g x y a) (Set.Ici 0) := by
  let c := (y - x ⬝ᵥ (G⁻¹ *ᵥ g)) * (e ⬝ᵥ (G⁻¹ *ᵥ x))
  have heq (a : ℝ) (ha : 0 ≤ a) :
      e ⬝ᵥ rankOneEstimate G g x y a =
        e ⬝ᵥ (G⁻¹ *ᵥ g) + a / (1 + a * (x ⬝ᵥ (G⁻¹ *ᵥ x))) * c := by
    rw [rankOneEstimate_eq hG g x y ha, dotProduct_add, dotProduct_smul]
    simp only [smul_eq_mul, c]
    ring
  have hm := monotoneOn_weightFraction (leverage_nonneg hG x)
  rcases le_total 0 c with hc | hc
  · left
    intro a ha b hb hab
    dsimp only
    rw [heq a ha, heq b hb]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (hm ha hb hab) hc)
  · right
    intro a ha b hb hab
    dsimp only
    rw [heq a ha, heq b hb]
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_right (hm ha hb hab) hc)

/-- A feasible weight in `[0,1]` can be moved to an endpoint without increasing
any specified linear target of the estimate. The base observations are unchanged. -/
theorem exists_rankOneEstimate_endpoint {G : Matrix d d ℝ} (hG : G.PosDef)
    (g x e : d → ℝ) (y : ℝ) {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∃ b : ℝ, (b = 0 ∨ b = 1) ∧
      e ⬝ᵥ rankOneEstimate G g x y b ≤ e ⬝ᵥ rankOneEstimate G g x y a := by
  rcases rankOneEstimate_monotone_or_antitone hG g x e y with hm | hm
  · exact ⟨0, Or.inl rfl, hm (by simp) ha.1 ha.1⟩
  · exact ⟨1, Or.inr rfl, hm ha.1 (by simp) ha.2⟩

variable {ι : Type*}

/-- A fixed Gram matrix plus the contributions of a finite set of observations. -/
@[expose] def weightedGram (G : Matrix d d ℝ) (s : Finset ι)
    (x : ι → d → ℝ) (w : ι → ℝ) : Matrix d d ℝ :=
  G + ∑ i ∈ s, w i • vecMulVec (x i) (x i)

/-- The corresponding right-hand side of the weighted normal equations. -/
@[expose] def weightedResponse (g : d → ℝ) (s : Finset ι)
    (x : ι → d → ℝ) (y w : ι → ℝ) : d → ℝ :=
  g + ∑ i ∈ s, (w i * y i) • x i

/-- Least squares with fixed base observations and finitely many variable weights. -/
@[expose] noncomputable def weightedEstimate (G : Matrix d d ℝ) (g : d → ℝ)
    (s : Finset ι) (x : ι → d → ℝ) (y w : ι → ℝ) : d → ℝ :=
  (weightedGram G s x w)⁻¹ *ᵥ weightedResponse g s x y w

omit [Fintype d] [DecidableEq d] in
/-- A positive definite backbone keeps every nonnegatively weighted design nonsingular. -/
theorem weightedGram_posDef [Finite d] {G : Matrix d d ℝ} (hG : G.PosDef)
    (s : Finset ι) (x : ι → d → ℝ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : (weightedGram G s x w).PosDef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [weightedGram] using hG
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hw j (Finset.mem_insert_of_mem hj))
    have hp := rankOneGram_posDef hs (x i) (hw i (Finset.mem_insert_self _ _))
    simpa [weightedGram, rankOneGram, Finset.sum_insert hi,
      add_assoc, add_left_comm, add_comm] using hp

private theorem weightedEstimate_insert [DecidableEq ι]
    (G : Matrix d d ℝ) (g : d → ℝ) (s : Finset ι) {i : ι} (hi : i ∉ s)
    (x : ι → d → ℝ) (y w : ι → ℝ) :
    weightedEstimate G g (insert i s) x y w =
      rankOneEstimate (weightedGram G s x w) (weightedResponse g s x y w)
        (x i) (y i) (w i) := by
  simp [weightedEstimate, weightedGram, weightedResponse, rankOneEstimate, rankOneGram,
    Finset.sum_insert hi, add_left_comm, add_comm]

private theorem weightedEstimate_base_insert [DecidableEq ι]
    (G : Matrix d d ℝ) (g : d → ℝ) (s : Finset ι) {i : ι} (hi : i ∉ s)
    (x : ι → d → ℝ) (y w : ι → ℝ) :
    weightedEstimate G g (insert i s) x y w =
      weightedEstimate (rankOneGram G (x i) (w i))
        (g + (w i * y i) • x i) s x y w := by
  simp [weightedEstimate, weightedGram, weightedResponse, rankOneGram,
    Finset.sum_insert hi, add_assoc]

/-- Round all weights to endpoints without increasing a linear target, provided
that fixed base observations already have a positive definite Gram matrix.
This proves the successive-rounding step of Theorem 3.3 and the spanning-backbone
extension in Remark 3.5 of STOC submission 1326. It does not assume monotonicity. -/
theorem exists_round_weights {G : Matrix d d ℝ} (hG : G.PosDef) (g e : d → ℝ)
    (s : Finset ι) (x : ι → d → ℝ) (y w : ι → ℝ)
    (hw : ∀ i ∈ s, w i ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u : ι → ℝ, (∀ i ∈ s, u i = 0 ∨ u i = 1) ∧
      (∀ i, i ∉ s → u i = w i) ∧
      e ⬝ᵥ weightedEstimate G g s x y u ≤ e ⬝ᵥ weightedEstimate G g s x y w := by
  classical
  induction s using Finset.induction_on generalizing G g w with
  | empty => exact ⟨w, by simp, by simp, le_rfl⟩
  | @insert i s hi ih =>
    have hws : ∀ j ∈ s, w j ∈ Set.Icc (0 : ℝ) 1 :=
      fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hGs := weightedGram_posDef hG s x w (fun j hj => (hws j hj).1)
    obtain ⟨b, hb, hcost⟩ := exists_rankOneEstimate_endpoint hGs
      (weightedResponse g s x y w) (x i) e (y i) (hw i (Finset.mem_insert_self _ _))
    have hb0 : 0 ≤ b := by rcases hb with rfl | rfl <;> norm_num
    let v := Function.update w i b
    have hvi : v i = b := by simp [v]
    have hvs : ∀ j ∈ s, v j = w j := fun j hj =>
      Function.update_of_ne (ne_of_mem_of_not_mem hj hi) _ _
    have hgram : weightedGram G s x v = weightedGram G s x w := by
      unfold weightedGram
      congr 1
      exact Finset.sum_congr rfl (fun j hj => by rw [hvs j hj])
    have hresp : weightedResponse g s x y v = weightedResponse g s x y w := by
      unfold weightedResponse
      congr 1
      exact Finset.sum_congr rfl (fun j hj => by rw [hvs j hj])
    have hfirst : e ⬝ᵥ weightedEstimate G g (insert i s) x y v ≤
        e ⬝ᵥ weightedEstimate G g (insert i s) x y w := by
      rw [weightedEstimate_insert G g s hi, weightedEstimate_insert G g s hi,
        hgram, hresp, hvi]
      exact hcost
    obtain ⟨u, hu, hout, hlast⟩ := ih (rankOneGram_posDef hG (x i) hb0)
      (g + (b * y i) • x i) v (fun j hj => (hvs j hj).symm ▸ hws j hj)
    have hui : u i = b := (hout i hi).trans hvi
    refine ⟨u, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hui.symm ▸ hb
      · exact hu j hj
    · intro j hj
      have hji : j ≠ i := fun heq => hj (by simp [heq])
      exact (hout j (fun h => hj (Finset.mem_insert_of_mem h))).trans
        (Function.update_of_ne hji _ _)
    · have hsecond : e ⬝ᵥ weightedEstimate G g (insert i s) x y u ≤
          e ⬝ᵥ weightedEstimate G g (insert i s) x y v := by
        rw [weightedEstimate_base_insert G g s hi, weightedEstimate_base_insert G g s hi,
          hui, hvi]
        exact hlast
      exact hsecond.trans hfirst

/-- With at most `k` genuinely fractional weights and `k > 0`, the rounding
loses strictly less than `k` units of retained mass. The fixed base observations
are retained throughout. This is the quantitative rounding step in
[XuGaoHu2027], Theorem 3.3, after sparse weights and a spanning backbone
have been obtained. -/
theorem exists_round_weights_loss_lt {G : Matrix d d ℝ} (hG : G.PosDef) (g e : d → ℝ)
    (s : Finset ι) (x : ι → d → ℝ) (y w : ι → ℝ) {k : ℕ}
    (hk : 0 < k) (hcard : s.card ≤ k)
    (hw : ∀ i ∈ s, w i ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ u : ι → ℝ, (∀ i ∈ s, u i = 0 ∨ u i = 1) ∧
      (∀ i, i ∉ s → u i = w i) ∧
      e ⬝ᵥ weightedEstimate G g s x y u ≤ e ⬝ᵥ weightedEstimate G g s x y w ∧
      (∑ i ∈ s, w i) - (∑ i ∈ s, u i) < k := by
  obtain ⟨u, hu, hout, hcost⟩ := exists_round_weights hG g e s x y w
    (fun i hi => ⟨(hw i hi).1.le, (hw i hi).2.le⟩)
  refine ⟨u, hu, hout, hcost, ?_⟩
  have hsum : 0 ≤ ∑ i ∈ s, u i := Finset.sum_nonneg fun i hi => by
    rcases hu i hi with h | h <;> simp [h]
  have hwk : (∑ i ∈ s, w i) < (k : ℝ) := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using (Nat.cast_pos.mpr hk : (0 : ℝ) < k)
    · have hlt : (∑ i ∈ s, w i) < ∑ _i ∈ s, (1 : ℝ) :=
        Finset.sum_lt_sum (fun i hi => (hw i hi).2.le)
          (by obtain ⟨i, hi⟩ := hs; exact ⟨i, hi, (hw i hi).2⟩)
      have hle : (∑ _i ∈ s, (1 : ℝ)) ≤ k := by
        simpa using (Nat.cast_le.mpr hcard : (s.card : ℝ) ≤ k)
      exact hlt.trans_le hle
  linarith

end Cslib.LeastSquares
