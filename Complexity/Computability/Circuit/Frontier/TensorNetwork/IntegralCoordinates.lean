/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Deformation
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.Integers
import Complexity.Foundations.NumberTheory.Padics.RatValuation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Integral local coordinates for the Cauchy kernel

This file proves Lemma D.4 of [OpenAI2026ETH] (§D.4.3, p. 59; proof on p. 60): near each grid
point the Cauchy kernel has `2`-integral coefficients. Let `L = 2 ^ a`, so that the grid
`S = {-L, …, L - 1}` is a complete residue system modulo `α = 2 ^ (a + 1)`. For `t, d ∈ S`, the
polynomial `z ↦ W_d(t + α z)` obtained from the Cauchy kernel `W_d = cauchyKernel L d` has
coefficients in `ℤ_(2)`, the rationals with odd denominator
(`Cslib.Circuits.Frontier.cauchyKernel_comp_mem_lifts`); when `d ≠ t` it is moreover divisible by
`2` (`Cslib.Circuits.Frontier.exists_cauchyKernel_comp_eq_two_mul`). Here `ℤ_(2)` is the valuation
ring `(Rat.padicValuation 2).integer`, and "coefficients in `ℤ_(2)`" is membership in
`Polynomial.lifts` of its inclusion.

The proof is the manuscript's. Since `S` is a complete residue system modulo `2 ^ (a + 1)`, the
nonzero differences `t - q`, `q ∈ S`, have the same `2`-adic valuations for every `t`; so
`C'(t) = ∏_{q ≠ t} (t - q)` has the valuation of `C'(0)`
(`Cslib.Circuits.Frontier.padicValuation_prod_sub_eq`). Each factor `t - q + α z` with `q ≠ t` is
`(t - q) (1 + α / (t - q) z)` with `α / (t - q)` divisible by `2`, and the factor `q = t` is
`α z`.

Entrywise, the Cauchy matrix has the same property
(`Cslib.Circuits.Frontier.cauchyMatrix_comp_mem_lifts`). Consequently, for tensors with entries in
a subring `B` of a `ℚ`-algebra `R` that contains `ℤ_(2)`, the deformed contraction `F(T)` along the
Cauchy matrix satisfies `F(t + α z) ∈ B[z]`
(`Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_cauchyMatrix_comp_mem_liftsRing`): the
manuscript's `F(t + α z) ∈ A[z]` with `B = O`. Coefficients in `ℤ_(2)` reduce modulo `2 ^ p`
through `Rat.padicIntegerToZModPow`; the valuations of integers that the proof uses are
`Rat.padicValuation_pow_le_of_abs_lt` and `Rat.padicValuation_add_pow_of_abs_lt`. The algorithmic
half of the lemma, evaluating `W_xy(t + α ζ) mod 2 ^ p` in polynomial time, belongs to the
runtime development.

## Main results

* `Cslib.Circuits.Frontier.padicValuation_prod_sub_eq`: `v₂(C'(t)) = v₂(C'(0))` on the grid.
* `Cslib.Circuits.Frontier.cauchyKernel_comp_mem_lifts`: `W_d(t + α z)` has `2`-integral
  coefficients.
* `Cslib.Circuits.Frontier.exists_cauchyKernel_comp_eq_two_mul`: it is divisible by `2` unless
  `d = t`.
* `Cslib.Circuits.Frontier.cauchyMatrix_comp_mem_lifts`: the same for the Cauchy matrix.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_mem`: a deformed contraction lies in
  any subring containing the tensor and matrix entries.
* `Cslib.Circuits.Frontier.TensorNetwork.deformedContraction_cauchyMatrix_comp_mem_liftsRing`:
  `F(t + α z)` has coefficients in any subring containing `ℤ_(2)` and the tensor entries.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.3, Lemma D.4,
  pp. 59–60.
-/

public section

namespace Cslib.Circuits.Frontier

open Polynomial
open scoped WithZero

/-! ### Two-adic valuations on the grid -/

/-- The `2`-adic valuation of a power of two. -/
private theorem padicValuation_two_pow (k : ℕ) :
    Rat.padicValuation 2 ((2 : ℚ) ^ k) = WithZero.exp (-(k : ℤ)) := by
  exact_mod_cast Rat.padicValuation_pow_self 2 k

private theorem padicValuation_two_pow_le {a : ℕ} {x : ℤ} (hx : x ≠ 0)
    (hlt : |x| < 2 ^ (a + 1)) :
    Rat.padicValuation 2 ((2 : ℚ) ^ a) ≤ Rat.padicValuation 2 (x : ℚ) := by
  exact_mod_cast Rat.padicValuation_pow_le_of_abs_lt (p := 2) hx (by exact_mod_cast hlt)

private theorem padicValuation_add_two_pow {a : ℕ} {x : ℤ} (hx : x ≠ 0)
    (hlt : |x| < 2 ^ (a + 1)) :
    Rat.padicValuation 2 ((x : ℚ) + 2 ^ (a + 1)) = Rat.padicValuation 2 (x : ℚ) := by
  exact_mod_cast Rat.padicValuation_add_pow_of_abs_lt (p := 2) hx (by exact_mod_cast hlt)

/-- **The grid is a complete residue system.** For `t` on the grid of `L = 2 ^ a` slots, the
nonzero differences `t - q`, `q ∈ S`, have the valuations of `1, …, 2 L - 1`: send `q` to the
residue of `t - q` modulo `2 L`. -/
theorem padicValuation_prod_sub_eq_prod_Ioo {a : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) :
    Rat.padicValuation 2 (∏ q ∈ (cauchyGrid (2 ^ a)).erase t, ((t : ℚ) - q)) =
      ∏ r ∈ Finset.Ioo (0 : ℤ) (2 ^ (a + 1)), Rat.padicValuation 2 (r : ℚ) := by
  rw [map_prod]
  set L : ℤ := 2 ^ a with hL
  have hL2 : (2 : ℤ) ^ (a + 1) = 2 * L := by rw [hL, pow_succ, mul_comm]
  have hLpos : 0 < L := by positivity
  rw [mem_cauchyGrid] at ht
  simp only [cauchyGrid, Nat.cast_pow, Nat.cast_ofNat, ← hL] at ht ⊢
  rw [hL2]
  refine Finset.prod_nbij' (fun q => if q < t then t - q else t - q + 2 * L)
    (fun r => if -L ≤ t - r then t - r else t - r + 2 * L) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ioo] at hq ⊢
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_erase, Finset.mem_Ico, Finset.mem_Ioo] at hr ⊢
    split_ifs <;> omega
  · intro q hq
    simp only [Finset.mem_erase, Finset.mem_Ico] at hq
    split_ifs <;> omega
  · intro r hr
    simp only [Finset.mem_Ioo] at hr
    split_ifs <;> omega
  · intro q hq
    simp only [Finset.mem_erase, Finset.mem_Ico] at hq
    have hne : t - q ≠ 0 := by omega
    have habs : |t - q| < 2 ^ (a + 1) := by rw [hL2, abs_lt]; omega
    have h2L : (2 : ℚ) * (L : ℚ) = 2 ^ (a + 1) := by exact_mod_cast hL2.symm
    have hadd := padicValuation_add_two_pow hne habs
    push_cast at hadd
    split_ifs
    · push_cast; rfl
    · push_cast
      rw [h2L]
      exact hadd.symm

/-- **`v₂(C'(t)) = v₂(C'(0))` on the grid** of `L = 2 ^ a` slots, where
`C'(t) = ∏_{q ∈ S, q ≠ t} (t - q)`. -/
theorem padicValuation_prod_sub_eq {a : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a)) :
    Rat.padicValuation 2 (∏ q ∈ (cauchyGrid (2 ^ a)).erase t, ((t : ℚ) - q)) =
      Rat.padicValuation 2 (∏ q ∈ (cauchyGrid (2 ^ a)).erase 0, ((0 : ℚ) - q)) := by
  have h0 : (0 : ℤ) ∈ cauchyGrid (2 ^ a) := by
    have : (0 : ℤ) < ((2 ^ a : ℕ) : ℤ) := by positivity
    rw [mem_cauchyGrid]
    exact ⟨by linarith, this⟩
  rw [padicValuation_prod_sub_eq_prod_Ioo ht]
  exact_mod_cast (padicValuation_prod_sub_eq_prod_Ioo h0).symm

/-- Distinct grid points of `L = 2 ^ a` slots differ by at most `a` factors of two. -/
theorem padicValuation_two_pow_le_sub {a : ℕ} {t q : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hq : q ∈ cauchyGrid (2 ^ a)) (hne : q ≠ t) :
    Rat.padicValuation 2 ((2 : ℚ) ^ a) ≤ Rat.padicValuation 2 ((t : ℚ) - q) := by
  rw [mem_cauchyGrid] at ht hq
  push_cast at ht hq
  have hlt : |t - q| < 2 ^ (a + 1) := by
    rw [pow_succ, abs_lt]
    constructor <;> linarith
  exact_mod_cast padicValuation_two_pow_le (sub_ne_zero.mpr hne.symm) hlt

/-! ### The kernel in local coordinates -/

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

private theorem C_mem_lifts_of_le_one {c : ℚ} (hc : Rat.padicValuation 2 c ≤ 1) :
    C c ∈ lifts (ℤ₍₂₎).subtype :=
  C_mem_lifts (ℤ₍₂₎).subtype (⟨c, hc⟩ : ℤ₍₂₎)

/-- A shifted factor `t + α z - q` with `q ≠ t` is `(t - q) (1 + α / (t - q) z)`. -/
private theorem shift_factor {t q α : ℚ} (h : t - q ≠ 0) :
    C t + C α * X - C q = C (t - q) * (1 + C (α / (t - q)) * X) := by
  rw [mul_add, mul_one, ← mul_assoc, ← C_mul, mul_div_cancel₀ _ h, C_sub]
  ring

/-- The kernel in local coordinates, as a product of the shifted factors. -/
private theorem cauchyKernel_comp (L : ℕ) (d : ℤ) (t α : ℚ) :
    (cauchyKernel L d).comp (C t + C α * X) =
      C ((∏ q ∈ (cauchyGrid L).erase 0, ((0 : ℚ) - q))⁻¹) *
        ∏ q ∈ (cauchyGrid L).erase d, (C t + C α * X - C (q : ℚ)) := by
  rw [cauchyKernel, Lagrange.eval_nodal, mul_comp, C_comp, Lagrange.nodal, prod_comp]
  simp only [sub_comp, X_comp, C_comp]

/-- The unit factors `1 + α / (t - q) z` with `q ≠ t` are integral. -/
private theorem prod_one_add_mem_lifts {a : ℕ} {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (s : Finset ℤ) (hs : s ⊆ (cauchyGrid (2 ^ a)).erase t) :
    ∏ q ∈ s, (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X) ∈ lifts (ℤ₍₂₎).subtype := by
  refine Subsemiring.prod_mem _ fun q hq => ?_
  obtain ⟨hqt, hqS⟩ := Finset.mem_erase.mp (hs hq)
  refine add_mem (one_mem _) (mul_mem (C_mem_lifts_of_le_one ?_) (X_mem_lifts _))
  have hle := padicValuation_two_pow_le_sub ht hqS hqt
  have hne : ((t : ℚ) - q) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hqt.symm)
  rw [map_div₀, div_le_one₀ ((Rat.padicValuation 2).pos_iff.mpr hne)]
  refine le_trans ?_ hle
  rw [padicValuation_two_pow, padicValuation_two_pow, WithZero.exp_le_exp]
  omega

/-- A product of differences `t - q` over points `q ≠ t` is nonzero. -/
private theorem prod_sub_ne_zero {t : ℤ} {s : Finset ℤ} (hs : t ∉ s) :
    ∏ q ∈ s, ((t : ℚ) - q) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun q hq =>
    sub_ne_zero.mpr fun h => hs (by rw [show t = q by exact_mod_cast h]; exact hq)

/-- Shifted factors at points `q ≠ t` split into a constant and the unit factors. -/
private theorem prod_shift {t : ℤ} (α : ℚ) {s : Finset ℤ} (hs : t ∉ s) :
    ∏ q ∈ s, (C (t : ℚ) + C α * X - C (q : ℚ)) =
      C (∏ q ∈ s, ((t : ℚ) - q)) * ∏ q ∈ s, (1 + C (α / ((t : ℚ) - q)) * X) := by
  calc
    ∏ q ∈ s, (C (t : ℚ) + C α * X - C (q : ℚ)) =
        ∏ q ∈ s, (C ((t : ℚ) - q) * (1 + C (α / ((t : ℚ) - q)) * X)) :=
      Finset.prod_congr rfl fun (q : ℤ) hq => shift_factor
        (sub_ne_zero.mpr fun h => hs (by rw [show t = q by exact_mod_cast h]; exact hq))
    _ = _ := by rw [Finset.prod_mul_distrib, map_prod]

/-- **Lemma D.4, divisibility.** Away from its own node, `d ≠ t`, the Cauchy kernel in local
coordinates `z ↦ W_d(t + α z)`, `α = 2 ^ (a + 1)`, is twice a polynomial with `2`-integral
coefficients: the factor `α z` survives, and `α / (t - d)` is divisible by `2`. -/
theorem exists_cauchyKernel_comp_eq_two_mul {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) (hdt : d ≠ t) :
    ∃ P ∈ lifts (ℤ₍₂₎).subtype,
      (cauchyKernel (2 ^ a) d).comp (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X) = C 2 * P := by
  have htd : t ∈ (cauchyGrid (2 ^ a)).erase d := Finset.mem_erase.mpr ⟨hdt.symm, ht⟩
  set s := ((cauchyGrid (2 ^ a)).erase d).erase t with hs_def
  have hts : t ∉ s := Finset.notMem_erase t _
  have hs : s ⊆ (cauchyGrid (2 ^ a)).erase t := fun q hq => by
    simp only [s, Finset.mem_erase] at hq ⊢
    exact ⟨hq.1, hq.2.2⟩
  have htd' : ((t : ℚ) - d) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hdt.symm)
  have hdt' : d ∈ (cauchyGrid (2 ^ a)).erase t := Finset.mem_erase.mpr ⟨hdt, hd⟩
  have hCt : ∏ q ∈ (cauchyGrid (2 ^ a)).erase t, ((t : ℚ) - q) =
      ((t : ℚ) - d) * ∏ q ∈ s, ((t : ℚ) - q) := by
    rw [hs_def, Finset.erase_right_comm]
    exact (Finset.mul_prod_erase _ (fun q : ℤ => (t : ℚ) - q) hdt').symm
  obtain ⟨C₀, hC₀def⟩ : ∃ C₀ : ℚ, C₀ = ∏ q ∈ (cauchyGrid (2 ^ a)).erase 0, ((0 : ℚ) - q) :=
    ⟨_, rfl⟩
  have hC₀ : C₀ ≠ 0 := by
    have := prod_sub_ne_zero (Finset.notMem_erase (0 : ℤ) (cauchyGrid (2 ^ a)))
    push_cast at this
    rwa [hC₀def]
  obtain ⟨c, hc⟩ : ∃ c : ℚ, c = C₀⁻¹ * (2 ^ (a + 1) * ∏ q ∈ s, ((t : ℚ) - q)) := ⟨_, rfl⟩
  refine ⟨C (c / 2) * X * ∏ q ∈ s, (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X), ?_, ?_⟩
  · refine mul_mem (mul_mem (C_mem_lifts_of_le_one ?_) (X_mem_lifts _))
      (prod_one_add_mem_lifts ht s hs)
    have hc2 : c / 2 =
        2 ^ a * (C₀⁻¹ * ∏ q ∈ (cauchyGrid (2 ^ a)).erase t, ((t : ℚ) - q)) / ((t : ℚ) - d) := by
      rw [hc, hCt, pow_succ]
      field_simp
    have hval :
        Rat.padicValuation 2 (C₀⁻¹ * ∏ q ∈ (cauchyGrid (2 ^ a)).erase t, ((t : ℚ) - q)) = 1 := by
      rw [map_mul, map_inv₀, padicValuation_prod_sub_eq ht, ← hC₀def,
        inv_mul_cancel₀ ((Rat.padicValuation 2).ne_zero_iff.mpr hC₀)]
    rw [hc2, map_div₀, map_mul, hval, mul_one,
      div_le_one₀ ((Rat.padicValuation 2).pos_iff.mpr htd')]
    exact padicValuation_two_pow_le_sub ht hd hdt
  · rw [cauchyKernel_comp, ← Finset.mul_prod_erase _ _ htd, prod_shift _ hts, ← hC₀def,
      show C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X - C (t : ℚ) = C ((2 : ℚ) ^ (a + 1)) * X by ring]
    have h2 : C (2 : ℚ) * C (c / 2) = C c := by rw [← C_mul, mul_div_cancel₀ _ two_ne_zero]
    have hcC : C c = C C₀⁻¹ * (C ((2 : ℚ) ^ (a + 1)) * C (∏ q ∈ s, ((t : ℚ) - q))) := by
      rw [hc, C_mul, C_mul]
    linear_combination
      (-(X * ∏ q ∈ s, (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X))) * h2 -
        (X * ∏ q ∈ s, (1 + C ((2 : ℚ) ^ (a + 1) / ((t : ℚ) - q)) * X)) * hcC

/-- **Lemma D.4, integrality.** For grid points `t, d` of `L = 2 ^ a` slots, the Cauchy kernel in
local coordinates `z ↦ W_d(t + α z)`, `α = 2 ^ (a + 1)`, has coefficients in `ℤ_(2)`. At its own
node, `d = t`, its constant term is `C'(t) / C'(0)`, of valuation one, and the other factors are
`1 + α / (t - q) z`. -/
theorem cauchyKernel_comp_mem_lifts {a : ℕ} {t d : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (hd : d ∈ cauchyGrid (2 ^ a)) :
    (cauchyKernel (2 ^ a) d).comp (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X) ∈
      lifts (ℤ₍₂₎).subtype := by
  rcases eq_or_ne d t with rfl | hdt
  · have hts : d ∉ (cauchyGrid (2 ^ a)).erase d := Finset.notMem_erase d _
    rw [cauchyKernel_comp, prod_shift _ hts, ← mul_assoc, ← C_mul]
    refine mul_mem (C_mem_lifts_of_le_one (le_of_eq ?_)) (prod_one_add_mem_lifts ht _ subset_rfl)
    have hC₀ := prod_sub_ne_zero (Finset.notMem_erase (0 : ℤ) (cauchyGrid (2 ^ a)))
    push_cast at hC₀
    rw [map_mul, map_inv₀, padicValuation_prod_sub_eq ht,
      inv_mul_cancel₀ ((Rat.padicValuation 2).ne_zero_iff.mpr hC₀)]
  · obtain ⟨P, hP, h⟩ := exists_cauchyKernel_comp_eq_two_mul ht hd hdt
    rw [h]
    refine mul_mem (C_mem_lifts_of_le_one ?_) hP
    have h2 := padicValuation_two_pow 1
    rw [pow_one] at h2
    rw [h2, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num

/-! ### The Cauchy matrix and the deformed contraction -/

/-- **Lemma D.4 for the Cauchy matrix.** For a packing into packets of `2 ^ a` slots, every entry
of the Cauchy matrix in local coordinates `z ↦ W(t + α z)` has `2`-integral coefficients. -/
theorem cauchyMatrix_comp_mem_lifts {E P : Type*} [DecidableEq P] {a : ℕ} {packet : E → P}
    {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (e e' : E) :
    (cauchyMatrix (2 ^ a) packet slot e e').comp (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X) ∈
      lifts (ℤ₍₂₎).subtype := by
  unfold cauchyMatrix
  split_ifs
  · exact cauchyKernel_comp_mem_lifts ht (sub_mem_cauchyGrid (hslot e) (hslot e'))
  · rw [zero_comp]
    exact zero_mem _

namespace TensorNetwork

variable {R V E : Type*} [CommRing R] [Fintype V] [Fintype E] [DecidableEq E]

/-- A deformed contraction lies in every subring that contains the tensor entries and the matrix
entries: it is a polynomial expression in them. -/
theorem deformedContraction_mem (N : TensorNetwork R Bool V E) (side : V → Bool)
    (W : Matrix E E R) (T : Subring R) (hN : ∀ v x, N.tensor v x ∈ T)
    (hW : ∀ e e', W e e' ∈ T) : N.deformedContraction side W ∈ T := by
  unfold deformedContraction
  refine T.sum_mem fun X _ => T.sum_mem fun Y _ => T.mul_mem (T.mul_mem
    (T.prod_mem fun v _ => hN v Y) (T.prod_mem fun v _ => hN v X)) (T.prod_mem fun e _ => ?_)
  have hv : W.mulVec (fun e' => if X e' then (1 : R) else 0) e ∈ T := by
    unfold Matrix.mulVec dotProduct
    refine T.sum_mem fun e' _ => T.mul_mem (hW e e') ?_
    dsimp only
    split_ifs
    exacts [T.one_mem, T.zero_mem]
  unfold affineFactor
  split_ifs
  exacts [hv, T.sub_mem T.one_mem hv]

/-- **Lemma D.4 for the deformed contraction.** Let `R` be a `ℚ`-algebra and `B` a subring of `R`
containing `ℤ_(2)`, and let the tensors have entries in `B`. Along the Cauchy matrix of a packing
into packets of `2 ^ a` slots, the deformed contraction `F(T)` satisfies `F(t + α z) ∈ B[z]` at
every grid point `t`, with `α = 2 ^ (a + 1)`. For the manuscript, `R = K`, `B = O` and `F(0)` is
the contraction (`eval_zero_deformedContraction_cauchyMatrix`). -/
theorem deformedContraction_cauchyMatrix_comp_mem_liftsRing [Algebra ℚ R] {P : Type*}
    [DecidableEq P] (N : TensorNetwork R Bool V E) (side : V → Bool) {a : ℕ} {packet : E → P}
    {slot : E → ℕ} (hslot : ∀ e, slot e < 2 ^ a) {t : ℤ} (ht : t ∈ cauchyGrid (2 ^ a))
    (B : Subring R) (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ R c ∈ B) (hN : ∀ v x, N.tensor v x ∈ B) :
    ((N.map Polynomial.C).deformedContraction side
        ((cauchyMatrix (2 ^ a) packet slot).map (Polynomial.mapRingHom (algebraMap ℚ R)))).comp
      (C (t : R) + C (2 ^ (a + 1)) * X) ∈ liftsRing B.subtype := by
  have hq : (C (t : R) + C (2 ^ (a + 1)) * X : R[X]) =
      (C (t : ℚ) + C ((2 : ℚ) ^ (a + 1)) * X).map (algebraMap ℚ R) := by
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
      Polynomial.map_X]
    exact congrArg₂ (· + ·) (congrArg C (map_intCast _ t).symm)
      (congrArg (C · * X) (by rw [map_pow, map_ofNat]))
  rw [← coe_compRingHom_apply, ← deformedContraction_map]
  refine deformedContraction_mem _ side _ _ (fun v x => ?_) (fun e e' => ?_)
  · rw [map_tensor, map_tensor, coe_compRingHom_apply, C_comp, ← lifts_iff_liftsRing]
    exact C_mem_lifts B.subtype ⟨_, hN v x⟩
  · rw [Matrix.map_apply, Matrix.map_apply, coe_compRingHom_apply, coe_mapRingHom, hq,
      ← map_comp, ← lifts_iff_liftsRing, lifts_iff_coeff_lifts]
    intro n
    obtain ⟨c, hc⟩ := (lifts_iff_coeff_lifts _).mp
      (cauchyMatrix_comp_mem_lifts (packet := packet) hslot ht e e') n
    rw [coeff_map, ← hc]
    exact ⟨⟨_, hB c c.2⟩, rfl⟩

end TensorNetwork

end Cslib.Circuits.Frontier
