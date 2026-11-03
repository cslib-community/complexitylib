/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula.Andreev
public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.DepthTwo
public import Complexity.Foundations.BooleanAnalysis.Fourier

/-!
# Exact quadratic depth-two weighted threshold circuits for Andreev's function

For all `b, m : ℕ`, Andreev's function `Boolean.andreev b m` on `n = 2 ^ b + b * m` bits is
computed by an explicit depth-two weighted threshold circuit (`THR ∘ THR`) with
`4 * 4 ^ b + b * m * 2 ^ b` bottom gates (and one top gate). This general all-`b, m` quadratic
construction is an original AI-assisted result and proof tracked in
[#2347](https://github.com/cslib-community/complexitylib/issues/2347). In the balanced
specialization `b = k`, `N = 2 ^ b = b * m`, `n = 2 * 2 ^ b` (matching the paper's Andreev
family up to truth-table bit numbering), it uses `4 N ^ 2 + b m N = (5 / 4) n ^ 2` bottom gates,
improving the published `O(n ^ 3 / log n)` depth-two upper bound of Kane and Williams
([KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.2, printed p. 2).

## Mathematical construction

Let `w : BitString (2 ^ b + b * m)` have truth-table bits `x_c = w (andreevTableIndex b m c)` with
signs `ξ_c = 1 - 2 x_c ∈ {-1, +1}`, and block sums `s_j = ∑_{t < m} w (andreevBlockVar b m j t)`
with parities `p_j = s_j mod 2`. For each `S ⊆ Fin b`, define the integer linear forms
`X_S(w) = ∑_{c : BitString b} χ_S(c) ξ_c(w) ∈ [-2 ^ b, 2 ^ b]`,
`t_S(w) = ∑_{j ∈ S} s_j(w) ∈ [0, #S * m]`, and `u^±_S(w) = X_S(w) ± t_S(w)`.
By `altLinear_add_add_altLinear_sub`,
`altLinear (X_S(w) + t_S(w)) + altLinear (X_S(w) - t_S(w)) = 2 * (-1) ^ (2 ^ b) * X_S(w) * χ_S(p)`.
Telescoping each `altLinear (u^±_S(w))` into `2 * 2 ^ b + #S * m` threshold indicators via
`sum_sub_mul_decide_le` and applying Fourier inversion on the `b`-bit cube yields
`2 * 2 ^ b * signVal (andreev b m w)` as a single linear threshold form over
`∑_{S ⊆ Fin b} 2 * (2 * 2 ^ b + #S * m) = 4 * 4 ^ b + b * m * 2 ^ b` bottom threshold gates,
with bottom weights in `{-2, -1, 0, 1, 2}` and odd integer top weights bounded by
`2 * (2 ^ b + b * m) - 1`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.AndreevBottomIndex`: index type
  `Σ S : Finset (Fin b), Bool × Fin (2 * 2 ^ b + #S * m)` of bottom gates.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevBottomOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevTopOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuit`: explicit depth-two weighted threshold
  circuit for `andreev b m`.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuitEvalInt`: choice-free computable integer
  evaluation of the two-layer threshold network.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_andreevBottomIndex`:
  `Fintype.card (AndreevBottomIndex b m) = 4 * 4 ^ b + b * m * 2 ^ b`.
* `Cslib.Circuits.Boolean.WeightedThreshold.computes_andreevCircuit`,
  `Cslib.Circuits.Boolean.WeightedThreshold.size_andreevCircuit`,
  `Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevCircuit_le`: `andreevCircuit b m` computes
  `single (andreev b m)` with `4 * 4 ^ b + b * m * 2 ^ b + 1` gates and depth at most `2`.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevBottomWeightInt_mem`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_weight_andreevBottomOp_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_weight_andreevTopOp_le`: explicit bottom and top
  weight bounds.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Theorem 1.2 (printed p. 2) for the prior `O(n ^ 3 / log n)` depth-two upper bound on the
  balanced specialization; the all-`b, m` quadratic construction formalized here is from
  [complexitylib#2347](https://github.com/cslib-community/complexitylib/issues/2347).
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### Combinatorial index and exact bottom-gate count `4 * 4 ^ b + b * m * 2 ^ b` -/

/-- Index type for the bottom threshold gates of the exact depth-two circuit for `andreev b m`:
a subset `S ⊆ Fin b`, a sign bit `σ : Bool` selecting `u⁺_S` or `u⁻_S`, and a threshold step
`k < 2 * 2 ^ b + #S * m`. -/
abbrev AndreevBottomIndex (b m : ℕ) : Type :=
  Σ S : Finset (Fin b), Bool × Fin (2 * 2 ^ b + #S * m)

/-- The exact number of bottom gates in `andreevCircuit b m` is `4 * 4 ^ b + b * m * 2 ^ b`. -/
theorem card_andreevBottomIndex (b m : ℕ) :
    Fintype.card (AndreevBottomIndex b m) = 4 * 4 ^ b + b * m * 2 ^ b := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, mul_add, sum_add_distrib]
  have h1 : (∑ _S : Finset (Fin b), 2 * (2 * 2 ^ b)) = 4 * 4 ^ b := by
    simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
    rw [show (4 : ℕ) ^ b = (2 * 2) ^ b from rfl, mul_pow]; ring
  have h2 : (∑ S : Finset (Fin b), 2 * (#S * m)) = b * m * 2 ^ b := by
    rw [show (∑ S : Finset (Fin b), 2 * (#S * m)) = (2 * ∑ S : Finset (Fin b), #S) * m by
      rw [mul_sum, sum_mul]; exact sum_congr rfl fun _ _ => by ring,
      two_mul_sum_card_finset]; ring
  rw [h1, h2]

/-- Equivalence between `AndreevBottomIndex b m` and `Fin (4 * 4 ^ b + b * m * 2 ^ b)`. -/
noncomputable def andreevBottomEquiv (b m : ℕ) :
    AndreevBottomIndex b m ≃ Fin (4 * 4 ^ b + b * m * 2 ^ b) :=
  Fintype.equivFinOfCardEq (card_andreevBottomIndex b m)

/-! ### Integer linear forms and gate parameters for Andreev's function -/

/-- The `b`-bit vector of block parities of an Andreev input `w : BitString (2 ^ b + b * m)`. -/
def andreevParities (b m : ℕ) (w : BitString (2 ^ b + b * m)) : BitString b :=
  fun j => parity m fun t => w (andreevBlockVar b m j t)

/-- `andreev b m w` reads the truth-table bit indexed by `andreevParities b m w`. -/
theorem andreev_eq_table_parities (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreev b m w = w (andreevTableIndex b m (BitString.equivFin b (andreevParities b m w))) :=
  rfl

/-- The unnormalized integer Walsh-Fourier score
`X_S(w) = ∑_{c : BitString b} χ_S(c) * (1 - 2 * x_c(w))`. -/
def andreevTableScore (b m : ℕ) (S : Finset (Fin b)) (w : BitString (2 ^ b + b * m)) : ℤ :=
  ∑ c : BitString b,
    chi ℤ S c * (1 - 2 * (w (andreevTableIndex b m (BitString.equivFin b c))).toNat)

/-- The integer sum `t_S(w) = ∑_{j ∈ S} ∑_{t < m} w (andreevBlockVar b m j t)` of the blocks in
`S`. -/
def andreevBlockSum (b m : ℕ) (S : Finset (Fin b)) (w : BitString (2 ^ b + b * m)) : ℤ :=
  ∑ j ∈ S, ∑ t : Fin m, (w (andreevBlockVar b m j t)).toNat

/-- The signed integer linear form `u^±_S(w) = X_S(w) ± t_S(w)` (`σ = true` for `+`, `σ = false`
for `-`). -/
def andreevLinearForm (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (w : BitString (2 ^ b + b * m)) : ℤ :=
  andreevTableScore b m S w + (if σ then 1 else -1) * andreevBlockSum b m S w

/-- The lower endpoint `ℓ_{S,σ}` of the interval containing `andreevLinearForm b m S σ w`:
`-2 ^ b` when `σ = true` and `-2 ^ b - #S * m` when `σ = false`. -/
def andreevLowerBound (b m : ℕ) (S : Finset (Fin b)) (σ : Bool) : ℤ :=
  if σ then -(2 ^ b : ℤ) else -(2 ^ b : ℤ) - (#S * m : ℤ)

/-- Constant offset `C_S = ∑_{c : BitString b} χ_S(c)` separating `X_S(w)` from its homogeneous
linear part in the `0`/`1` truth-table bits. -/
def andreevTableOffset (b : ℕ) (S : Finset (Fin b)) : ℤ :=
  ∑ c : BitString b, chi ℤ S c

/-- Integer input weight vector of a bottom gate attached to `(S, σ)`:
`-2 * χ_S(c)` on truth-table bit `c`, `±1` on block variables in blocks `j ∈ S`, and `0` on
block variables in blocks `j ∉ S`. -/
def andreevBottomWeightInt (b m : ℕ) (S : Finset (Fin b)) (σ : Bool) :
    Fin (2 ^ b + b * m) → ℤ :=
  Fin.addCases
    (fun idx => -2 * chi ℤ S ((BitString.equivFin b).symm idx))
    (fun u => if (finProdFinEquiv.symm u).1 ∈ S then (if σ then 1 else -1) else 0)

/-- Integer threshold `θ_{S,σ,k} = ℓ_{S,σ} + k + 1 - C_S` of bottom gate `⟨S, (σ, k)⟩`. -/
def andreevBottomThresholdInt (b m : ℕ) (idx : AndreevBottomIndex b m) : ℤ :=
  andreevLowerBound b m idx.1 idx.2.1 + idx.2.2 + 1 - andreevTableOffset b idx.1

/-- Integer top-gate weight on bottom gate `⟨S, (σ, k)⟩`. -/
def andreevTopWeightInt (b m : ℕ) (idx : AndreevBottomIndex b m) : ℤ :=
  -(-1 : ℤ) ^ (2 ^ b) *
    (altLinear (andreevLowerBound b m idx.1 idx.2.1 + idx.2.2 + 1) -
      altLinear (andreevLowerBound b m idx.1 idx.2.1 + idx.2.2))

/-- Integer threshold of the top gate of `andreevCircuit b m`. -/
def andreevTopThresholdInt (b m : ℕ) : ℤ :=
  ∑ S : Finset (Fin b), ∑ σ : Bool,
    (-1 : ℤ) ^ (2 ^ b) * altLinear (andreevLowerBound b m S σ)

/-! ### Properties of the integer linear forms -/

private theorem chi_int_eq_one_or_neg_one {ι : Type*} (S : Finset ι) (c : ι → Bool) :
    chi ℤ S c = 1 ∨ chi ℤ S c = -1 := by
  rw [chi_eq_neg_one_pow_parityOn]; cases parityOn S c <;> simp

private theorem negOnePow_chi_int_mul_sign {b : ℕ} (S : Finset (Fin b)) (c : BitString b)
    (v : Bool) : (((chi ℤ S c * (1 - 2 * (v.toNat : ℤ))).negOnePow : ℤ)) = -1 := by
  rcases chi_int_eq_one_or_neg_one S c with h | h <;> cases v <;> simp [h]

/-- The parity sign `((andreevTableScore b m S w).negOnePow : ℤ)` of `X_S(w)` is `(-1) ^ (2 ^ b)`,
independent of `S` and `w`. -/
theorem negOnePow_andreevTableScore (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    ((andreevTableScore b m S w).negOnePow : ℤ) = (-1 : ℤ) ^ (2 ^ b) := by
  rw [andreevTableScore, negOnePow_sum]; simp [negOnePow_chi_int_mul_sign]

/-- The parity sign `((andreevBlockSum b m S w).negOnePow : ℤ)` of `t_S(w)` is the character
`χ_S(andreevParities b m w)`. -/
theorem negOnePow_andreevBlockSum (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    ((andreevBlockSum b m S w).negOnePow : ℤ) = chi ℤ S (andreevParities b m w) := by
  rw [andreevBlockSum, negOnePow_sum, chi]
  refine prod_congr rfl fun j _ => ?_
  rw [negOnePow_sum]; simp only [Int.coe_negOnePow_natCast]
  simpa [chi, andreevParities, parity] using
    chi_eq_neg_one_pow_parityOn (R := ℤ) (univ : Finset (Fin m))
      (fun t => w (andreevBlockVar b m j t))

/-- `X_S(w)` lies in the interval `[-2 ^ b, 2 ^ b]`. -/
theorem andreevTableScore_bounds (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    -(2 ^ b : ℤ) ≤ andreevTableScore b m S w ∧ andreevTableScore b m S w ≤ (2 ^ b : ℤ) := by
  have hterm (c : BitString b) :
      (-1 : ℤ) ≤ chi ℤ S c * (1 - 2 * (w (andreevTableIndex b m (BitString.equivFin b c))).toNat) ∧
        chi ℤ S c * (1 - 2 * (w (andreevTableIndex b m (BitString.equivFin b c))).toNat) ≤ 1 := by
    rcases chi_int_eq_one_or_neg_one S c with h | h <;>
      cases w (andreevTableIndex b m (BitString.equivFin b c)) <;> simp [h]
  exact ⟨(by simp : -(2 ^ b : ℤ) = ∑ _c : BitString b, (-1 : ℤ)).trans_le
    (sum_le_sum fun c _ => (hterm c).1),
    (sum_le_sum fun c _ => (hterm c).2).trans_eq (by simp)⟩

/-- `t_S(w)` lies in the interval `[0, #S * m]`. -/
theorem andreevBlockSum_bounds (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    0 ≤ andreevBlockSum b m S w ∧ andreevBlockSum b m S w ≤ (#S * m : ℤ) := by
  refine ⟨sum_nonneg fun j _ => sum_nonneg fun t _ => Nat.cast_nonneg _, ?_⟩
  refine (sum_le_sum fun j _ => sum_le_sum fun t _ => ?_).trans_eq
    (by simp : (∑ _j ∈ S, ∑ _t : Fin m, (1 : ℤ)) = (#S * m : ℤ))
  cases w (andreevBlockVar b m j t) <;> decide

/-- `u^±_S(w)` lies in `[ℓ_{S,σ}, ℓ_{S,σ} + (2 * 2 ^ b + #S * m)]`. -/
theorem andreevLinearForm_bounds (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (w : BitString (2 ^ b + b * m)) :
    andreevLowerBound b m S σ ≤ andreevLinearForm b m S σ w ∧
      andreevLinearForm b m S σ w ≤ andreevLowerBound b m S σ + (2 * 2 ^ b + #S * m : ℕ) := by
  have hX := andreevTableScore_bounds b m S w
  have ht := andreevBlockSum_bounds b m S w
  cases σ <;>
    simp only [andreevLowerBound, andreevLinearForm, ↓reduceIte, Bool.false_eq_true,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] <;>
    omega

/-- The integer dot product of `andreevBottomWeightInt b m S σ` with `w` equals
`u^±_S(w) - C_S`. -/
theorem sum_andreevBottomWeightInt_mul (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (w : BitString (2 ^ b + b * m)) :
    (∑ i : Fin (2 ^ b + b * m), andreevBottomWeightInt b m S σ i * (w i).toNat) =
      andreevLinearForm b m S σ w - andreevTableOffset b S := by
  rw [Fin.sum_univ_add]
  have hleft :
      (∑ idx : Fin (2 ^ b),
        andreevBottomWeightInt b m S σ (Fin.castAdd (b * m) idx) *
          (w (Fin.castAdd (b * m) idx)).toNat) =
        andreevTableScore b m S w - andreevTableOffset b S := by
    simp only [andreevBottomWeightInt, Fin.addCases_left]
    rw [← (BitString.equivFin b).sum_comp
      (fun idx => -2 * chi ℤ S ((BitString.equivFin b).symm idx) *
        ((w (Fin.castAdd (b * m) idx)).toNat : ℤ))]
    simp only [Equiv.symm_apply_apply, andreevTableScore, andreevTableOffset, ← sum_sub_distrib,
      andreevTableIndex]
    exact sum_congr rfl fun _ _ => by ring
  have hright :
      (∑ u : Fin (b * m),
        andreevBottomWeightInt b m S σ (Fin.natAdd (2 ^ b) u) *
          (w (Fin.natAdd (2 ^ b) u)).toNat) =
        (if σ then 1 else -1) * andreevBlockSum b m S w := by
    simp only [andreevBottomWeightInt, Fin.addCases_right]
    rw [← finProdFinEquiv.sum_comp
      (fun u => (if (finProdFinEquiv.symm u).1 ∈ S then (if σ then (1 : ℤ) else -1) else 0) *
        ((w (Fin.natAdd (2 ^ b) u)).toNat : ℤ)),
      Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, ite_mul, zero_mul, sum_ite_irrel, sum_const_zero,
      andreevBlockSum, andreevBlockVar, mul_sum]
    cases σ <;> simp
  rw [hleft, hright, andreevLinearForm]
  ring

/-! ### Choice-free integer evaluation and exact Fourier-telescoping proof -/

/-- Choice-free computable evaluation of bottom gate `idx : AndreevBottomIndex b m` on input `w`. -/
def andreevBottomEvalInt (b m : ℕ) (idx : AndreevBottomIndex b m)
    (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevBottomThresholdInt b m idx ≤
    ∑ i : Fin (2 ^ b + b * m), andreevBottomWeightInt b m idx.1 idx.2.1 i * (w i).toNat)

/-- Bottom gate `⟨S, (σ, k)⟩` evaluates to `decide (ℓ_{S,σ} + k + 1 ≤ u^±_S(w))`. -/
theorem andreevBottomEvalInt_eq_decide (b m : ℕ) (idx : AndreevBottomIndex b m)
    (w : BitString (2 ^ b + b * m)) :
    andreevBottomEvalInt b m idx w =
      decide (andreevLowerBound b m idx.1 idx.2.1 + idx.2.2 + 1 ≤
        andreevLinearForm b m idx.1 idx.2.1 w) := by
  rw [andreevBottomEvalInt, sum_andreevBottomWeightInt_mul, andreevBottomThresholdInt]
  exact decide_eq_decide.mpr ⟨by omega, by omega⟩

/-- Choice-free computable evaluation of the full depth-two threshold network for `andreev b m`. -/
def andreevCircuitEvalInt (b m : ℕ) (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevTopThresholdInt b m ≤
    ∑ S : Finset (Fin b), ∑ σ : Bool, ∑ k : Fin (2 * 2 ^ b + #S * m),
      andreevTopWeightInt b m ⟨S, (σ, k)⟩ * (andreevBottomEvalInt b m ⟨S, (σ, k)⟩ w).toNat)

private theorem cast_chi_int {ι : Type*} (S : Finset ι) (c : ι → Bool) :
    ((chi ℤ S c : ℤ) : ℝ) = chi ℝ S c := by simp [chi]

private theorem cast_one_sub_two_mul_toNat (v : Bool) :
    ((1 - 2 * (v.toNat : ℤ) : ℤ) : ℝ) = signVal v := by cases v <;> simp

/-- Fourier inversion identity for Andreev's function:
`∑_S X_S(w) * χ_S(andreevParities b m w) = 2 ^ b * signVal (andreev b m w)` over `ℝ`. -/
theorem sum_andreevTableScore_mul_chi (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    (∑ S : Finset (Fin b),
      (andreevTableScore b m S w : ℝ) * chi ℝ S (andreevParities b m w)) =
      (2 ^ b : ℝ) * signVal (andreev b m w) := by
  let f : BitString b → ℝ :=
    fun c => signVal (w (andreevTableIndex b m (BitString.equivFin b c)))
  have hX (S : Finset (Fin b)) :
      (andreevTableScore b m S w : ℝ) = (2 ^ b : ℝ) * BitString.fourierCoeff f S := by
    rw [BitString.fourierCoeff_eq_sum]; simp only [Fintype.card_fin]
    rw [mul_div_cancel₀ _ (by positivity)]
    simp only [andreevTableScore, Int.cast_sum, Int.cast_mul, cast_chi_int,
      cast_one_sub_two_mul_toNat, f, mul_comm (chi ℝ S _)]
  simp_rw [hX, mul_assoc, ← mul_sum, BitString.sum_fourierCoeff_mul_chi]; rfl

/-- Summing the top-gate weighted bottom-gate outputs minus the top-gate threshold gives
`-2 * ∑_S X_S(w) * χ_S(p)` in `ℤ`. -/
theorem sum_andreevTopWeightInt_sub_threshold (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    (∑ S : Finset (Fin b), ∑ σ : Bool, ∑ k : Fin (2 * 2 ^ b + #S * m),
      andreevTopWeightInt b m ⟨S, (σ, k)⟩ * (andreevBottomEvalInt b m ⟨S, (σ, k)⟩ w).toNat) -
      andreevTopThresholdInt b m =
      -2 * ∑ S : Finset (Fin b),
        andreevTableScore b m S w * chi ℤ S (andreevParities b m w) := by
  have hsign_sq : (-1 : ℤ) ^ (2 ^ b) * (-1 : ℤ) ^ (2 ^ b) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  rw [andreevTopThresholdInt, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun S _ => ?_
  rw [← sum_sub_distrib]
  have htele (σ : Bool) :
      (∑ k : Fin (2 * 2 ^ b + #S * m),
        andreevTopWeightInt b m ⟨S, (σ, k)⟩ * (andreevBottomEvalInt b m ⟨S, (σ, k)⟩ w).toNat) -
        (-1 : ℤ) ^ (2 ^ b) * altLinear (andreevLowerBound b m S σ) =
        -(-1 : ℤ) ^ (2 ^ b) * altLinear (andreevLinearForm b m S σ w) := by
    have hbds := andreevLinearForm_bounds b m S σ w
    have hsum := sum_sub_mul_decide_le altLinear hbds.1 hbds.2
    simp only [andreevTopWeightInt, andreevBottomEvalInt_eq_decide, mul_assoc, ← mul_sum]
    rw [← hsum]
    ring
  simp only [Fintype.sum_bool, htele]
  have hpol := altLinear_add_add_altLinear_sub (andreevTableScore b m S w)
    (andreevBlockSum b m S w)
  have hplus : andreevLinearForm b m S true w =
      andreevTableScore b m S w + andreevBlockSum b m S w := by simp [andreevLinearForm]
  have hminus : andreevLinearForm b m S false w =
      andreevTableScore b m S w - andreevBlockSum b m S w := by
    simp [andreevLinearForm, sub_eq_add_neg]
  rw [hplus, hminus, ← mul_add, hpol, negOnePow_andreevTableScore, negOnePow_andreevBlockSum]
  calc -(-1 : ℤ) ^ (2 ^ b) *
        (2 * (-1 : ℤ) ^ (2 ^ b) * andreevTableScore b m S w *
          chi ℤ S (andreevParities b m w))
      = -2 * ((-1 : ℤ) ^ (2 ^ b) * (-1 : ℤ) ^ (2 ^ b)) *
          (andreevTableScore b m S w * chi ℤ S (andreevParities b m w)) := by ring
    _ = -2 * (andreevTableScore b m S w * chi ℤ S (andreevParities b m w)) := by
          rw [hsign_sq, mul_one]

/-- The computable integer evaluation `andreevCircuitEvalInt b m` computes `andreev b m` on every
input. -/
theorem andreevCircuitEvalInt_eq_andreev (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevCircuitEvalInt b m w = andreev b m w := by
  rw [andreevCircuitEvalInt]
  have hint := sum_andreevTopWeightInt_sub_threshold b m w
  have hreal :
      (((∑ S : Finset (Fin b), ∑ σ : Bool, ∑ k : Fin (2 * 2 ^ b + #S * m),
        andreevTopWeightInt b m ⟨S, (σ, k)⟩ *
          (andreevBottomEvalInt b m ⟨S, (σ, k)⟩ w).toNat) -
        andreevTopThresholdInt b m : ℤ) : ℝ) =
      -2 * (2 ^ b : ℝ) * signVal (andreev b m w) := by
    rw [hint]; push_cast; simp_rw [cast_chi_int]; rw [sum_andreevTableScore_mul_chi]; ring
  have h2pow : (0 : ℝ) < (2 ^ b : ℝ) := by positivity
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← sub_nonneg, ← @Int.cast_nonneg_iff ℝ, hreal]
  cases andreev b m w <;> simp

/-! ### Explicit `WeightedThreshold` depth-two circuit and weight bounds -/

/-- The `j`-th bottom gate of `andreevCircuit b m`. -/
noncomputable abbrev andreevBottomOp (b m : ℕ) (j : Fin (4 * 4 ^ b + b * m * 2 ^ b)) : Op :=
  let idx := (andreevBottomEquiv b m).symm j
  { arity := 2 ^ b + b * m
    weight := fun i => (andreevBottomWeightInt b m idx.1 idx.2.1 i : ℝ)
    threshold := (andreevBottomThresholdInt b m idx : ℝ) }

/-- The top output gate of `andreevCircuit b m`. -/
noncomputable abbrev andreevTopOp (b m : ℕ) : Op where
  arity := 4 * 4 ^ b + b * m * 2 ^ b
  weight := fun j => (andreevTopWeightInt b m ((andreevBottomEquiv b m).symm j) : ℝ)
  threshold := (andreevTopThresholdInt b m : ℝ)

/-- **Exact quadratic depth-two weighted threshold circuit for Andreev's function**
`Boolean.andreev b m`, with `4 * 4 ^ b + b * m * 2 ^ b` bottom gates and one top gate. -/
noncomputable def andreevCircuit (b m : ℕ) : Circuit signature (2 ^ b + b * m) 1 :=
  depthTwo (andreevTopOp b m) (andreevBottomOp b m) (fun _ => id)

/-- Evaluating `andreevBottomOp b m j` agrees with `andreevBottomEvalInt`. -/
theorem interpretation_andreevBottomOp (b m : ℕ) (j : Fin (4 * 4 ^ b + b * m * 2 ^ b))
    (w : BitString (2 ^ b + b * m)) :
    interpretation (andreevBottomOp b m j) w =
      andreevBottomEvalInt b m ((andreevBottomEquiv b m).symm j) w := by
  unfold interpretation andreevBottomOp andreevBottomEvalInt
  dsimp only
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-- Evaluating `andreevCircuit b m` agrees with `andreevCircuitEvalInt b m`. -/
theorem eval_andreevCircuit_eq_evalInt (b m : ℕ) (w : BitString (2 ^ b + b * m)) (o : Fin 1) :
    (andreevCircuit b m).eval interpretation w o = andreevCircuitEvalInt b m w := by
  rw [andreevCircuit, eval_depthTwo]
  simp only [id, interpretation_andreevBottomOp]
  unfold interpretation andreevTopOp andreevCircuitEvalInt
  dsimp only
  rw [← (andreevBottomEquiv b m).sum_comp
    (fun j => (andreevTopWeightInt b m ((andreevBottomEquiv b m).symm j) : ℝ) *
      (andreevBottomEvalInt b m ((andreevBottomEquiv b m).symm j) w).toNat)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-- **`andreevCircuit b m` computes `Boolean.andreev b m`.** -/
theorem computes_andreevCircuit (b m : ℕ) :
    (andreevCircuit b m).Computes interpretation (single (andreev b m)) := by
  intro w; funext o
  rw [eval_andreevCircuit_eq_evalInt, andreevCircuitEvalInt_eq_andreev, single_apply]

/-- `andreevCircuit b m` has `4 * 4 ^ b + b * m * 2 ^ b` bottom gates and `1` top gate, for
`4 * 4 ^ b + b * m * 2 ^ b + 1` gates in total. -/
@[simp]
theorem size_andreevCircuit (b m : ℕ) :
    (andreevCircuit b m).size = 4 * 4 ^ b + b * m * 2 ^ b + 1 := by simp [andreevCircuit]

/-- `andreevCircuit b m` has depth at most `2`. -/
theorem depth_andreevCircuit_le (b m : ℕ) : (andreevCircuit b m).depth ≤ 2 :=
  depth_depthTwo_le _ _ _

/-- The active wire count of `andreevCircuit b m` is at most
`(4 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1)`. -/
theorem wireCount_andreevCircuit_le (b m : ℕ) :
    (andreevCircuit b m).wireCount ≤ (4 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1) := by
  refine (wireCount_depthTwo_le _ _ _).trans ?_
  simp only [andreevTopOp, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; linarith

/-! ### Explicit weight bounds for bottom and top gates -/

/-- Every integer bottom-gate weight lies in `{-2, -1, 0, 1, 2}`. -/
theorem andreevBottomWeightInt_mem (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (i : Fin (2 ^ b + b * m)) :
    andreevBottomWeightInt b m S σ i ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  refine Fin.addCases (fun idx => ?_) (fun u => ?_) i
  · simp only [andreevBottomWeightInt, Fin.addCases_left]
    rcases chi_int_eq_one_or_neg_one S ((BitString.equivFin b).symm idx) with h | h <;>
      simp [h]
  · simp only [andreevBottomWeightInt, Fin.addCases_right]
    split_ifs <;> cases σ <;> decide

/-- Every integer bottom-gate weight has absolute value at most `2`. -/
theorem abs_andreevBottomWeightInt_le (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (i : Fin (2 ^ b + b * m)) :
    |andreevBottomWeightInt b m S σ i| ≤ 2 := by
  have hmem := andreevBottomWeightInt_mem b m S σ i
  simp only [mem_insert, mem_singleton] at hmem
  rcases hmem with h | h | h | h | h <;> rw [h] <;> decide

/-- Every bottom gate of `andreevCircuit b m` has real weights of absolute value at most `2`. -/
theorem abs_weight_andreevBottomOp_le (b m : ℕ) (j : Fin (4 * 4 ^ b + b * m * 2 ^ b))
    (i : Fin (2 ^ b + b * m)) :
    |(andreevBottomOp b m j).weight i| ≤ 2 := by
  unfold andreevBottomOp
  dsimp only
  exact_mod_cast abs_andreevBottomWeightInt_le b m
    ((andreevBottomEquiv b m).symm j).1 ((andreevBottomEquiv b m).symm j).2.1 i

/-- Every top-gate weight of `andreevCircuit b m` is an odd integer. -/
theorem andreevTopWeightInt_emod_two_ne_zero (b m : ℕ) (idx : AndreevBottomIndex b m) :
    andreevTopWeightInt b m idx % 2 ≠ 0 := by
  rw [andreevTopWeightInt, altLinear_add_one_sub]
  rcases neg_one_pow_eq_or ℤ (2 ^ b) with h1 | h1 <;>
    rcases Int.units_eq_one_or (andreevLowerBound b m idx.1 idx.2.1 + idx.2.2 + 1).negOnePow with
      h2 | h2 <;>
    simp only [h1, h2, Units.val_one, Units.val_neg] <;> omega

/-- Every integer top-gate weight has absolute value at most `2 * (2 ^ b + b * m) - 1`. -/
theorem abs_andreevTopWeightInt_le (b m : ℕ) (idx : AndreevBottomIndex b m) :
    |andreevTopWeightInt b m idx| ≤ 2 * (2 ^ b + b * m : ℤ) - 1 := by
  rcases idx with ⟨S, ⟨σ, k⟩⟩
  rw [andreevTopWeightInt, altLinear_add_one_sub]
  have h1 : |(-(-1 : ℤ) ^ (2 ^ b))| = 1 := by simp
  have h2 : |(((andreevLowerBound b m S σ + k + 1).negOnePow : ℤ))| = 1 := Int.abs_negOnePow _
  rw [abs_mul, abs_mul, h1, h2, one_mul, one_mul]
  have hS : #S ≤ b := (card_le_univ S).trans_eq (Fintype.card_fin b)
  have hSm : (#S * m : ℤ) ≤ (b * m : ℤ) := by exact_mod_cast Nat.mul_le_mul_right m hS
  have hk_lt : (k : ℤ) < 2 * (2 ^ b : ℤ) + (#S * m : ℤ) := by exact_mod_cast k.isLt
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg k
  have hpow_pos : (1 : ℤ) ≤ (2 ^ b : ℤ) := by exact_mod_cast Nat.one_le_two_pow
  have hbm_nonneg : (0 : ℤ) ≤ (b : ℤ) * (m : ℤ) :=
    mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg m)
  rw [abs_le]
  cases σ <;>
    simp only [andreevLowerBound, ↓reduceIte, Bool.false_eq_true] <;>
    constructor <;> omega

/-- Every top-gate weight of `andreevCircuit b m` has absolute value at most
`2 * (2 ^ b + b * m) - 1`. -/
theorem abs_weight_andreevTopOp_le (b m : ℕ) (j : Fin (4 * 4 ^ b + b * m * 2 ^ b)) :
    |(andreevTopOp b m).weight j| ≤ 2 * (2 ^ b + b * m : ℝ) - 1 := by
  unfold andreevTopOp
  dsimp only
  exact_mod_cast abs_andreevTopWeightInt_le b m ((andreevBottomEquiv b m).symm j)

/-- **Exact quadratic depth-two threshold circuit upper bound for Andreev's function**:
for all `b, m : ℕ`, there is a depth-two weighted threshold circuit with
`4 * 4 ^ b + b * m * 2 ^ b` bottom gates computing `Boolean.andreev b m`, with bottom weights in
`{-2, -1, 0, 1, 2}` and odd integer top weights of absolute value at most
`2 * (2 ^ b + b * m) - 1`. -/
theorem exists_depthTwo_computes_andreev (b m : ℕ) :
    ∃ (top : Op) (bottom : Fin top.arity → Op)
      (args : ∀ j, Fin (bottom j).arity → Fin (2 ^ b + b * m)),
      top.arity = 4 * 4 ^ b + b * m * 2 ^ b ∧
      (depthTwo top bottom args).Computes interpretation (single (andreev b m)) ∧
      (depthTwo top bottom args).size = 4 * 4 ^ b + b * m * 2 ^ b + 1 ∧
      (depthTwo top bottom args).depth ≤ 2 ∧
      (∀ j a, |(bottom j).weight a| ≤ 2) ∧
      (∀ j, |(top.weight j)| ≤ 2 * (2 ^ b + b * m : ℝ) - 1) :=
  ⟨andreevTopOp b m, andreevBottomOp b m, fun _ => id, rfl,
    computes_andreevCircuit b m, size_andreevCircuit b m, depth_andreevCircuit_le b m,
    fun j a => abs_weight_andreevBottomOp_le b m j a,
    fun j => abs_weight_andreevTopOp_le b m j⟩

/-! ### Checked small-parameter example (`b = 2, m = 2`, `n = 8`) -/

/-- At `b = 2, m = 2` (`n = 8` input bits), `andreevCircuit 2 2` has `80` bottom gates. -/
theorem card_andreevBottomIndex_two_two : Fintype.card (AndreevBottomIndex 2 2) = 80 := by
  rw [card_andreevBottomIndex]; rfl

/-- At `b = 2, m = 2`, `andreevCircuit 2 2` has `81` gates in total (`80` bottom gates and `1`
top gate). -/
theorem size_andreevCircuit_two_two : (andreevCircuit 2 2).size = 81 := by simp

/-- At `b = 2, m = 2`, `andreevCircuit 2 2` has at most `720` active wires. -/
theorem wireCount_andreevCircuit_two_two_le : (andreevCircuit 2 2).wireCount ≤ 720 :=
  wireCount_andreevCircuit_le 2 2

/-- Checked evaluation of `andreevCircuitEvalInt 2 2` on mixed truth-table `8`-bit inputs where
truth-table entries `1` and `2` are `true` (entries `0` and `3` are `false`) and toggling the
second bit of block `0` flips the selected truth-table address from odd-parity entry `1`/`2`
(`true`) back to entry `0` (`false`). -/
theorem andreevCircuitEvalInt_two_two_mixed :
    andreevCircuitEvalInt 2 2 (fun i => decide (i = 1 ∨ i = 2 ∨ i = 4)) = true ∧
      andreevCircuitEvalInt 2 2 (fun i => decide (i = 1 ∨ i = 2 ∨ i = 4 ∨ i = 5)) = false := by
  decide

end Cslib.Circuits.Boolean.WeightedThreshold
