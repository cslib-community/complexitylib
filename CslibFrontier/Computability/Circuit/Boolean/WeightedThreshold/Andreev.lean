/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev
public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.DepthTwo
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier

/-!
# Exact quadratic depth-two weighted threshold circuits for Andreev's function

For all `b, m : ℕ`, Andreev's function `Boolean.andreev b m` on `n = 2 ^ b + b * m` bits is
computed by an explicit depth-two weighted threshold circuit (`THR ∘ THR`) with
`2 * 4 ^ b + b * m * 2 ^ b` bottom gates (and one top gate). This general all-`b, m` quadratic
construction is an original AI-assisted result and proof tracked in
[#2347](https://github.com/cslib-community/cslib-frontier/issues/2347) and
[#2812](https://github.com/cslib-community/cslib-frontier/issues/2812). In the balanced
specialization `b = k`, `N = 2 ^ b = b * m`, `n = 2 * 2 ^ b` (matching the paper's Andreev
family up to truth-table bit numbering), it uses `2 N ^ 2 + b m N = (3 / 4) n ^ 2` bottom gates,
improving the published `O(n ^ 3 / log n)` depth-two upper bound of Kane and Williams
([KaneWilliams2016], `arXiv:1511.07860v1`, Theorem 1.2, printed p. 2).

## Mathematical construction

Let `w : BitString (2 ^ b + b * m)` have truth-table bits `x_c = w (andreevTableIndex b m c)` with
signs `ξ_c = 1 - 2 x_c ∈ {-1, +1}`, and block sums `s_j = ∑_{t < m} w (andreevBlockVar b m j t)`
with parities `p_j = s_j mod 2`. For each `S ⊆ Fin b`, define the integer linear forms
`X_S(w) = ∑_{c : BitString b} χ_S(c) ξ_c(w) ∈ [-2 ^ b, 2 ^ b]` and
`t_S(w) = ∑_{j ∈ S} s_j(w) ∈ [0, #S * m]`. Since `X_S(w)` is a sum of `2 ^ b` signs, its parity
sign is `ε = (-1) ^ (2 ^ b)`, so `negOnePow_mul_altLinear_add_sub_altLinear` gives
`ε * altLinear (X_S(w) + t_S(w)) - altLinear (t_S(w)) = X_S(w) * χ_S(p)`.
Telescoping `altLinear (X_S(w) + t_S(w))` over `[-2 ^ b, 2 ^ b + #S * m]` into
`2 * 2 ^ b + #S * m` threshold indicators and `altLinear (t_S(w))` over `[0, #S * m]` into
`#S * m` indicators (none for `S = ∅`) via `sum_sub_mul_decide_le`, and applying Fourier inversion
on the `b`-bit cube, yields `2 ^ b * signVal (andreev b m w)` as a single linear threshold form over
`∑_{S ⊆ Fin b} (2 * 2 ^ b + 2 * #S * m) = 2 * 4 ^ b + b * m * 2 ^ b` bottom threshold gates,
with bottom weights in `{-2, -1, 0, 1, 2}` and odd integer top weights bounded by
`2 * (2 ^ b + b * m) - 1`.

The `±`-signed forms `u^±_S(w) = X_S(w) ± t_S(w)` (`andreevLinearForm`) and their weight vectors
(`andreevBottomWeightInt`) are also defined here: the exact circuit uses `u^+_S`, and the windowed
circuits of `AndreevWindowed` truncate the polarization `φ(u^+_S) + φ(u^-_S) = 2 ε X_S χ_S(p)`.

## Main definitions

* `Cslib.Circuits.Boolean.WeightedThreshold.AndreevBottomIndex`: index type
  `Σ S : Finset (Fin b), Σ τ : Bool, Fin (andreevStairLength b m S τ)` of bottom gates, where
  `τ = true` indexes the staircase for `X_S + t_S` and `τ = false` the staircase for `t_S`.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevStairForm`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevStairLower`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevStairSign`: the telescoped forms, their lower
  endpoints, and their top-gate signs.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevBottomOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevTopOp`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuit`: explicit depth-two weighted threshold
  circuit for `andreev b m`.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevCircuitEvalInt`: choice-free computable integer
  evaluation of the two-layer threshold network.

## Main results

* `Cslib.Circuits.Boolean.WeightedThreshold.card_andreevBottomIndex`:
  `Fintype.card (AndreevBottomIndex b m) = 2 * 4 ^ b + b * m * 2 ^ b`.
* `Cslib.Circuits.Boolean.WeightedThreshold.computes_andreevCircuit`,
  `Cslib.Circuits.Boolean.WeightedThreshold.size_andreevCircuit`,
  `Cslib.Circuits.Boolean.WeightedThreshold.depth_andreevCircuit_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.wireCount_andreevCircuit_le`: `andreevCircuit b m`
  computes `single (andreev b m)` with `2 * 4 ^ b + b * m * 2 ^ b + 1` gates, depth at most `2`,
  and at most `(2 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1)` active wires.
* `Cslib.Circuits.Boolean.WeightedThreshold.andreevStairWeightInt_mem`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_weight_andreevBottomOp_le`,
  `Cslib.Circuits.Boolean.WeightedThreshold.andreevTopWeightInt_emod_two_ne_zero`,
  `Cslib.Circuits.Boolean.WeightedThreshold.abs_weight_andreevTopOp_le`: explicit bottom and top
  weight bounds.
* `Cslib.Circuits.Boolean.WeightedThreshold.lines_andreevCircuit_bottom_or_top`: gate by gate, every
  gate of `andreevCircuit b m` reads only original inputs with integer weights of absolute value at
  most `2`, or reads only gates with odd integer weights of absolute value below
  `2 * (2 ^ b + b * m)`.
* `Cslib.Circuits.Boolean.WeightedThreshold.exists_depthTwo_computes_andreev`: the bundled
  existence statement.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016], `arXiv:1511.07860v1`,
  Theorem 1.2 (printed p. 2) for the prior `O(n ^ 3 / log n)` depth-two upper bound on the
  balanced specialization; the all-`b, m` quadratic construction formalized here is from
  [cslib-frontier#2347](https://github.com/cslib-community/cslib-frontier/issues/2347) and
  [cslib-frontier#2812](https://github.com/cslib-community/cslib-frontier/issues/2812).
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset

/-! ### Combinatorial index and exact bottom-gate count `2 * 4 ^ b + b * m * 2 ^ b` -/

/-- Number of threshold steps of staircase `τ` for subset `S`: `2 * 2 ^ b + #S * m` for the
staircase of `X_S + t_S` (`τ = true`) and `#S * m` for the staircase of `t_S` (`τ = false`). -/
def andreevStairLength (b m : ℕ) (S : Finset (Fin b)) (τ : Bool) : ℕ :=
  if τ then 2 * 2 ^ b + #S * m else #S * m

/-- Index type for the bottom threshold gates of the exact depth-two circuit for `andreev b m`:
a subset `S ⊆ Fin b`, a staircase selector `τ : Bool` (`true` for `X_S + t_S`, `false` for
`t_S`), and a threshold step `k < andreevStairLength b m S τ`. -/
abbrev AndreevBottomIndex (b m : ℕ) : Type :=
  Σ S : Finset (Fin b), Σ τ : Bool, Fin (andreevStairLength b m S τ)

/-- The subset `S` of a bottom-gate index. -/
abbrev AndreevBottomIndex.subset {b m : ℕ} (idx : AndreevBottomIndex b m) : Finset (Fin b) :=
  idx.1

/-- The staircase selector of a bottom-gate index: `true` for `X_S + t_S`, `false` for `t_S`. -/
abbrev AndreevBottomIndex.stair {b m : ℕ} (idx : AndreevBottomIndex b m) : Bool :=
  idx.2.1

/-- The threshold step of a bottom-gate index within its staircase. -/
abbrev AndreevBottomIndex.step {b m : ℕ} (idx : AndreevBottomIndex b m) :
    Fin (andreevStairLength b m idx.subset idx.stair) :=
  idx.2.2

/-- The exact number of bottom gates in `andreevCircuit b m` is `2 * 4 ^ b + b * m * 2 ^ b`. -/
theorem card_andreevBottomIndex (b m : ℕ) :
    Fintype.card (AndreevBottomIndex b m) = 2 * 4 ^ b + b * m * 2 ^ b := by
  have hS (S : Finset (Fin b)) :
      Fintype.card (Σ τ : Bool, Fin (andreevStairLength b m S τ)) = 2 * 2 ^ b + 2 * (#S * m) := by
    rw [Fintype.card_sigma, Fintype.sum_bool]
    simp only [Fintype.card_fin, andreevStairLength, ↓reduceIte, Bool.false_eq_true]
    ring
  rw [Fintype.card_sigma]
  simp only [hS]
  have h1 : (∑ _S : Finset (Fin b), 2 * 2 ^ b) = 2 * 4 ^ b := by
    simp only [sum_const, card_univ, Fintype.card_finset, Fintype.card_fin, smul_eq_mul]
    rw [show (4 : ℕ) ^ b = (2 * 2) ^ b from rfl, mul_pow]; ring
  have h2 : (∑ S : Finset (Fin b), 2 * (#S * m)) = b * m * 2 ^ b := by
    rw [show (∑ S : Finset (Fin b), 2 * (#S * m)) = (2 * ∑ S : Finset (Fin b), #S) * m by
      rw [mul_sum, sum_mul]; exact sum_congr rfl fun _ _ => by ring,
      two_mul_sum_card_finset]; ring
  rw [← h1, ← h2, ← sum_add_distrib]

/-- Equivalence between `AndreevBottomIndex b m` and `Fin (2 * 4 ^ b + b * m * 2 ^ b)`. -/
noncomputable def andreevBottomEquiv (b m : ℕ) :
    AndreevBottomIndex b m ≃ Fin (2 * 4 ^ b + b * m * 2 ^ b) :=
  Fintype.equivFinOfCardEq (card_andreevBottomIndex b m)

/-! ### Integer linear forms and gate parameters for Andreev's function -/

/-- The `b`-bit vector of block parities of an Andreev input `w : BitString (2 ^ b + b * m)`. -/
def andreevParities (b m : ℕ) (w : BitString (2 ^ b + b * m)) : BitString b :=
  fun j => parity m fun t => w (andreevBlockVar b m j t)

/-- `andreev b m w` reads the truth-table bit indexed by `andreevParities b m w`. -/
theorem andreev_eq_table_parities (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreev b m w = w (andreevTableIndex b m (BitString.equivFin b (andreevParities b m w))) :=
  rfl

/-- `andreevTableIndex b m` is injective. -/
theorem andreevTableIndex_injective (b m : ℕ) : Function.Injective (andreevTableIndex b m) :=
  Fin.castAdd_injective (2 ^ b) (b * m)

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

/-- The integer form telescoped by staircase `τ` of subset `S`: `X_S(w) + t_S(w)` for `τ = true`
and `t_S(w)` for `τ = false`. -/
def andreevStairForm (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (w : BitString (2 ^ b + b * m)) : ℤ :=
  if τ then andreevTableScore b m S w + andreevBlockSum b m S w else andreevBlockSum b m S w

/-- The lower endpoint of the interval containing `andreevStairForm b m S τ w`: `-2 ^ b` for
`τ = true` and `0` for `τ = false`. -/
def andreevStairLower (b : ℕ) (τ : Bool) : ℤ :=
  if τ then -(2 ^ b : ℤ) else 0

/-- The top-gate sign of staircase `τ`: `-(-1) ^ (2 ^ b)` for `τ = true` and `1` for
`τ = false`. -/
def andreevStairSign (b : ℕ) (τ : Bool) : ℤ :=
  if τ then -(-1 : ℤ) ^ (2 ^ b) else 1

/-- Integer input weight vector of the block sum `t_S`: `0` on truth-table bits, `1` on block
variables in blocks `j ∈ S`, and `0` on block variables in blocks `j ∉ S`. -/
def andreevBlockWeightInt (b m : ℕ) (S : Finset (Fin b)) : Fin (2 ^ b + b * m) → ℤ :=
  Fin.addCases (fun _ => 0) (fun u => if (finProdFinEquiv.symm u).1 ∈ S then 1 else 0)

/-- Integer input weight vector of the bottom gates of staircase `τ` for subset `S`:
`andreevBottomWeightInt b m S true` (the form `u^+_S`) for `τ = true` and
`andreevBlockWeightInt b m S` for `τ = false`. -/
def andreevStairWeightInt (b m : ℕ) (S : Finset (Fin b)) (τ : Bool) :
    Fin (2 ^ b + b * m) → ℤ :=
  if τ then andreevBottomWeightInt b m S true else andreevBlockWeightInt b m S

/-- Integer threshold `θ_{S,τ,k} = ℓ_τ + k + 1 - [τ] C_S` of bottom gate `⟨S, τ, k⟩`. -/
def andreevBottomThresholdInt (b m : ℕ) (idx : AndreevBottomIndex b m) : ℤ :=
  andreevStairLower b idx.stair + idx.step + 1 -
    (if idx.stair then andreevTableOffset b idx.subset else 0)

/-- Integer top-gate weight on bottom gate `⟨S, τ, k⟩`: the signed step
`andreevStairSign b τ * (φ(ℓ_τ + k + 1) - φ(ℓ_τ + k))` of `altLinear`. -/
def andreevTopWeightInt (b m : ℕ) (idx : AndreevBottomIndex b m) : ℤ :=
  andreevStairSign b idx.stair *
    (altLinear (andreevStairLower b idx.stair + idx.step + 1) -
      altLinear (andreevStairLower b idx.stair + idx.step))

/-- Integer threshold of the top gate of `andreevCircuit b m`. -/
def andreevTopThresholdInt (b : ℕ) : ℤ :=
  -∑ _S : Finset (Fin b), ∑ τ : Bool, andreevStairSign b τ * altLinear (andreevStairLower b τ)

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

/-- `andreevStairForm b m S τ w` lies in `[ℓ_τ, ℓ_τ + andreevStairLength b m S τ]`. -/
theorem andreevStairForm_bounds (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (w : BitString (2 ^ b + b * m)) :
    andreevStairLower b τ ≤ andreevStairForm b m S τ w ∧
      andreevStairForm b m S τ w ≤ andreevStairLower b τ + andreevStairLength b m S τ := by
  have hX := andreevTableScore_bounds b m S w
  have ht := andreevBlockSum_bounds b m S w
  cases τ <;>
    simp only [andreevStairLower, andreevStairForm, andreevStairLength, ↓reduceIte,
      Bool.false_eq_true, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] <;>
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

/-- The integer dot product of `andreevBlockWeightInt b m S` with `w` is `t_S(w)`. -/
theorem sum_andreevBlockWeightInt_mul (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    (∑ i : Fin (2 ^ b + b * m), andreevBlockWeightInt b m S i * (w i).toNat) =
      andreevBlockSum b m S w := by
  rw [Fin.sum_univ_add]
  simp only [andreevBlockWeightInt, Fin.addCases_left, Fin.addCases_right, zero_mul,
    sum_const_zero, zero_add]
  rw [← finProdFinEquiv.sum_comp
    (fun u => (if (finProdFinEquiv.symm u).1 ∈ S then (1 : ℤ) else 0) *
      ((w (Fin.natAdd (2 ^ b) u)).toNat : ℤ)),
    Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul, sum_ite_irrel, sum_const_zero,
    andreevBlockSum, andreevBlockVar]
  simp [sum_ite_mem]

/-- The integer dot product of `andreevStairWeightInt b m S τ` with `w` equals
`andreevStairForm b m S τ w` minus the offset `C_S` when `τ = true`. -/
theorem sum_andreevStairWeightInt_mul (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (w : BitString (2 ^ b + b * m)) :
    (∑ i : Fin (2 ^ b + b * m), andreevStairWeightInt b m S τ i * (w i).toNat) =
      andreevStairForm b m S τ w - (if τ then andreevTableOffset b S else 0) := by
  cases τ
  · simp only [andreevStairWeightInt, andreevStairForm, Bool.false_eq_true, ↓reduceIte,
      sum_andreevBlockWeightInt_mul, sub_zero]
  · simp only [andreevStairWeightInt, andreevStairForm, ↓reduceIte,
      sum_andreevBottomWeightInt_mul, andreevLinearForm, one_mul]

/-- The signed staircase combination for subset `S` is the Fourier term:
`∑_τ andreevStairSign b τ * φ(andreevStairForm b m S τ w) = -(X_S(w) * χ_S(p))`. -/
theorem sum_andreevStairSign_mul_altLinear (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    ∑ τ : Bool, andreevStairSign b τ * altLinear (andreevStairForm b m S τ w) =
      -(andreevTableScore b m S w * chi ℤ S (andreevParities b m w)) := by
  have h := negOnePow_mul_altLinear_add_sub_altLinear (andreevTableScore b m S w)
    (andreevBlockSum b m S w)
  rw [negOnePow_andreevTableScore, negOnePow_andreevBlockSum] at h
  simp only [Fintype.sum_bool, andreevStairSign, andreevStairForm, ↓reduceIte,
    Bool.false_eq_true, one_mul]
  rw [← h]
  ring

/-! ### Choice-free integer evaluation and exact Fourier-telescoping proof -/

/-- Choice-free computable evaluation of bottom gate `idx : AndreevBottomIndex b m` on input `w`. -/
def andreevBottomEvalInt (b m : ℕ) (idx : AndreevBottomIndex b m)
    (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevBottomThresholdInt b m idx ≤
    ∑ i : Fin (2 ^ b + b * m), andreevStairWeightInt b m idx.subset idx.stair i * (w i).toNat)

/-- Bottom gate `⟨S, τ, k⟩` evaluates to `decide (ℓ_τ + k + 1 ≤ andreevStairForm b m S τ w)`. -/
theorem andreevBottomEvalInt_eq_decide (b m : ℕ) (idx : AndreevBottomIndex b m)
    (w : BitString (2 ^ b + b * m)) :
    andreevBottomEvalInt b m idx w =
      decide (andreevStairLower b idx.stair + idx.step + 1 ≤
        andreevStairForm b m idx.subset idx.stair w) := by
  rw [andreevBottomEvalInt, sum_andreevStairWeightInt_mul, andreevBottomThresholdInt]
  exact decide_eq_decide.mpr ⟨by omega, by omega⟩

/-- Choice-free computable evaluation of the full depth-two threshold network for `andreev b m`. -/
def andreevCircuitEvalInt (b m : ℕ) (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevTopThresholdInt b ≤
    ∑ S : Finset (Fin b), ∑ τ : Bool, ∑ k : Fin (andreevStairLength b m S τ),
      andreevTopWeightInt b m ⟨S, τ, k⟩ * (andreevBottomEvalInt b m ⟨S, τ, k⟩ w).toNat)

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
`-∑_S X_S(w) * χ_S(p)` in `ℤ`. -/
theorem sum_andreevTopWeightInt_sub_threshold (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    (∑ S : Finset (Fin b), ∑ τ : Bool, ∑ k : Fin (andreevStairLength b m S τ),
      andreevTopWeightInt b m ⟨S, τ, k⟩ * (andreevBottomEvalInt b m ⟨S, τ, k⟩ w).toNat) -
      andreevTopThresholdInt b =
      -∑ S : Finset (Fin b),
        andreevTableScore b m S w * chi ℤ S (andreevParities b m w) := by
  rw [andreevTopThresholdInt, sub_neg_eq_add, ← sum_add_distrib, ← sum_neg_distrib]
  refine sum_congr rfl fun S _ => ?_
  rw [← sum_add_distrib, ← sum_andreevStairSign_mul_altLinear]
  refine sum_congr rfl fun τ _ => ?_
  have hbds := andreevStairForm_bounds b m S τ w
  have hsum := sum_sub_mul_decide_le altLinear hbds.1 hbds.2
  simp only [andreevTopWeightInt, andreevBottomEvalInt_eq_decide, AndreevBottomIndex.subset,
    AndreevBottomIndex.stair, AndreevBottomIndex.step, mul_assoc, ← mul_sum]
  rw [← hsum]
  ring

/-- The computable integer evaluation `andreevCircuitEvalInt b m` computes `andreev b m` on every
input. -/
theorem andreevCircuitEvalInt_eq_andreev (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevCircuitEvalInt b m w = andreev b m w := by
  rw [andreevCircuitEvalInt]
  have hint := sum_andreevTopWeightInt_sub_threshold b m w
  have hreal :
      (((∑ S : Finset (Fin b), ∑ τ : Bool, ∑ k : Fin (andreevStairLength b m S τ),
        andreevTopWeightInt b m ⟨S, τ, k⟩ *
          (andreevBottomEvalInt b m ⟨S, τ, k⟩ w).toNat) -
        andreevTopThresholdInt b : ℤ) : ℝ) =
      -(2 ^ b : ℝ) * signVal (andreev b m w) := by
    rw [hint]; push_cast; simp_rw [cast_chi_int]; rw [sum_andreevTableScore_mul_chi]; ring
  have h2pow : (0 : ℝ) < (2 ^ b : ℝ) := by positivity
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← sub_nonneg, ← @Int.cast_nonneg_iff ℝ, hreal]
  cases andreev b m w <;> simp [h2pow, h2pow.le]

/-! ### Explicit `WeightedThreshold` depth-two circuit -/

/-- The `j`-th bottom gate of `andreevCircuit b m`. -/
noncomputable abbrev andreevBottomOp (b m : ℕ) (j : Fin (2 * 4 ^ b + b * m * 2 ^ b)) : Op :=
  let idx := (andreevBottomEquiv b m).symm j
  { arity := 2 ^ b + b * m
    weight := fun i => (andreevStairWeightInt b m idx.subset idx.stair i : ℝ)
    threshold := (andreevBottomThresholdInt b m idx : ℝ) }

/-- The top output gate of `andreevCircuit b m`. -/
noncomputable abbrev andreevTopOp (b m : ℕ) : Op where
  arity := 2 * 4 ^ b + b * m * 2 ^ b
  weight := fun j => (andreevTopWeightInt b m ((andreevBottomEquiv b m).symm j) : ℝ)
  threshold := (andreevTopThresholdInt b : ℝ)

/-- **Exact quadratic depth-two weighted threshold circuit for Andreev's function**
`Boolean.andreev b m`, with `2 * 4 ^ b + b * m * 2 ^ b` bottom gates and one top gate. -/
noncomputable def andreevCircuit (b m : ℕ) : Circuit signature (2 ^ b + b * m) 1 :=
  depthTwo (andreevTopOp b m) (andreevBottomOp b m) (fun _ => id)

/-- Evaluating `andreevBottomOp b m j` agrees with `andreevBottomEvalInt`. -/
theorem interpretation_andreevBottomOp (b m : ℕ) (j : Fin (2 * 4 ^ b + b * m * 2 ^ b))
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
  simp only [Fintype.sum_sigma]
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-- **`andreevCircuit b m` computes `Boolean.andreev b m`.** -/
theorem computes_andreevCircuit (b m : ℕ) :
    (andreevCircuit b m).Computes interpretation (single (andreev b m)) := by
  intro w; funext o
  rw [eval_andreevCircuit_eq_evalInt, andreevCircuitEvalInt_eq_andreev, single_apply]

/-- `andreevCircuit b m` has `2 * 4 ^ b + b * m * 2 ^ b` bottom gates and `1` top gate, for
`2 * 4 ^ b + b * m * 2 ^ b + 1` gates in total. -/
@[simp]
theorem size_andreevCircuit (b m : ℕ) :
    (andreevCircuit b m).size = 2 * 4 ^ b + b * m * 2 ^ b + 1 := by simp [andreevCircuit]

/-- `andreevCircuit b m` has depth at most `2`. -/
theorem depth_andreevCircuit_le (b m : ℕ) : (andreevCircuit b m).depth ≤ 2 :=
  depth_depthTwo_le _ _ _

/-- The active wire count of `andreevCircuit b m` is at most
`(2 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1)`. -/
theorem wireCount_andreevCircuit_le (b m : ℕ) :
    (andreevCircuit b m).wireCount ≤ (2 * 4 ^ b + b * m * 2 ^ b) * (2 ^ b + b * m + 1) := by
  refine (wireCount_depthTwo_le _ _ _).trans ?_
  simp only [andreevTopOp, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]; linarith

/-! ### Explicit weight bounds for bottom and top gates -/

private theorem abs_le_two_of_mem {z : ℤ} (h : z ∈ ({-2, -1, 0, 1, 2} : Finset ℤ)) :
    |z| ≤ 2 := by
  simp only [mem_insert, mem_singleton] at h
  rcases h with h | h | h | h | h <;> rw [h] <;> decide

/-- Every integer weight of `andreevBottomWeightInt b m S σ` lies in `{-2, -1, 0, 1, 2}`. -/
theorem andreevBottomWeightInt_mem (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (i : Fin (2 ^ b + b * m)) :
    andreevBottomWeightInt b m S σ i ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  refine Fin.addCases (fun idx => ?_) (fun u => ?_) i
  · simp only [andreevBottomWeightInt, Fin.addCases_left]
    rcases chi_int_eq_one_or_neg_one S ((BitString.equivFin b).symm idx) with h | h <;>
      simp [h]
  · simp only [andreevBottomWeightInt, Fin.addCases_right]
    split_ifs <;> cases σ <;> decide

/-- Every integer weight of `andreevBottomWeightInt b m S σ` has absolute value at most `2`. -/
theorem abs_andreevBottomWeightInt_le (b m : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (i : Fin (2 ^ b + b * m)) :
    |andreevBottomWeightInt b m S σ i| ≤ 2 :=
  abs_le_two_of_mem (andreevBottomWeightInt_mem b m S σ i)

/-- Every integer bottom-gate weight `andreevStairWeightInt b m S τ i` lies in
`{-2, -1, 0, 1, 2}`. -/
theorem andreevStairWeightInt_mem (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (i : Fin (2 ^ b + b * m)) :
    andreevStairWeightInt b m S τ i ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
  cases τ
  · simp only [andreevStairWeightInt, Bool.false_eq_true, ↓reduceIte]
    refine Fin.addCases (fun idx => ?_) (fun u => ?_) i
    · simp [andreevBlockWeightInt]
    · simp only [andreevBlockWeightInt, Fin.addCases_right]
      split_ifs <;> decide
  · exact andreevBottomWeightInt_mem b m S true i

/-- Every bottom gate of `andreevCircuit b m` has real weights of absolute value at most `2`. -/
theorem abs_weight_andreevBottomOp_le (b m : ℕ) (j : Fin (2 * 4 ^ b + b * m * 2 ^ b))
    (i : Fin (2 ^ b + b * m)) :
    |(andreevBottomOp b m j).weight i| ≤ 2 := by
  unfold andreevBottomOp
  dsimp only
  exact_mod_cast abs_le_two_of_mem (andreevStairWeightInt_mem b m
    ((andreevBottomEquiv b m).symm j).subset ((andreevBottomEquiv b m).symm j).stair i)

/-- Every top-gate weight of `andreevCircuit b m` is an odd integer. -/
theorem andreevTopWeightInt_emod_two_ne_zero (b m : ℕ) (idx : AndreevBottomIndex b m) :
    andreevTopWeightInt b m idx % 2 ≠ 0 := by
  rcases idx with ⟨S, τ, k⟩
  dsimp only [andreevTopWeightInt, AndreevBottomIndex.stair, AndreevBottomIndex.step]
  rw [altLinear_add_one_sub]
  rcases neg_one_pow_eq_or ℤ (2 ^ b) with h1 | h1 <;>
    rcases Int.units_eq_one_or (andreevStairLower b τ + k + 1).negOnePow with h2 | h2 <;>
    cases τ <;>
    simp only [andreevStairSign, h1, h2, ↓reduceIte, Bool.false_eq_true, Units.val_one,
      Units.val_neg] <;> omega

/-- Every integer top-gate weight has absolute value at most `2 * (2 ^ b + b * m) - 1`. -/
theorem abs_andreevTopWeightInt_le (b m : ℕ) (idx : AndreevBottomIndex b m) :
    |andreevTopWeightInt b m idx| ≤ 2 * (2 ^ b + b * m : ℤ) - 1 := by
  rcases idx with ⟨S, τ, k⟩
  have hsign : |andreevStairSign b τ| = 1 := by cases τ <;> simp [andreevStairSign]
  dsimp only [andreevTopWeightInt, AndreevBottomIndex.stair, AndreevBottomIndex.step]
  rw [altLinear_add_one_sub, abs_mul, abs_mul, hsign, Int.abs_negOnePow, one_mul, one_mul]
  have hS : #S ≤ b := (card_le_univ S).trans_eq (Fintype.card_fin b)
  have hSm : (#S * m : ℤ) ≤ (b * m : ℤ) := by exact_mod_cast Nat.mul_le_mul_right m hS
  have hk_lt : (k : ℤ) < (andreevStairLength b m S τ : ℤ) := by exact_mod_cast k.isLt
  have hk_nonneg : (0 : ℤ) ≤ (k : ℤ) := Nat.cast_nonneg k
  have hpow_pos : (1 : ℤ) ≤ (2 ^ b : ℤ) := by exact_mod_cast Nat.one_le_two_pow
  have hbm_nonneg : (0 : ℤ) ≤ (b : ℤ) * (m : ℤ) :=
    mul_nonneg (Nat.cast_nonneg b) (Nat.cast_nonneg m)
  rw [abs_le]
  cases τ <;>
    simp only [andreevStairLower, andreevStairLength, ↓reduceIte, Bool.false_eq_true,
      Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hk_lt ⊢ <;>
    constructor <;> omega

/-- Every top-gate weight of `andreevCircuit b m` has absolute value at most
`2 * (2 ^ b + b * m) - 1`. -/
theorem abs_weight_andreevTopOp_le (b m : ℕ) (j : Fin (2 * 4 ^ b + b * m * 2 ^ b)) :
    |(andreevTopOp b m).weight j| ≤ 2 * (2 ^ b + b * m : ℝ) - 1 := by
  unfold andreevTopOp
  dsimp only
  exact_mod_cast abs_andreevTopWeightInt_le b m ((andreevBottomEquiv b m).symm j)

/-- Gate by gate, every gate of `andreevCircuit b m` is either a bottom gate, reading only original
inputs with integer weights of absolute value at most `2`, or a top gate, reading only gates with
odd integer weights of absolute value below `2 * (2 ^ b + b * m)`. -/
theorem lines_andreevCircuit_bottom_or_top (b m : ℕ) (k : Fin (andreevCircuit b m).size) :
    ((∀ a, ∃ i, ((andreevCircuit b m).program.lines k).wires a = .input i) ∧
      ∀ a, ∃ z : ℤ, |z| ≤ 2 ∧ ((andreevCircuit b m).program.lines k).op.weight a = z) ∨
    ((∀ a, ∃ g, ((andreevCircuit b m).program.lines k).wires a = .gate g) ∧
      ∀ a, ∃ z : ℤ, Odd z ∧ |z| < 2 * ((2 ^ b + b * m : ℕ) : ℤ) ∧
        ((andreevCircuit b m).program.lines k).op.weight a = z) := by
  obtain ⟨j, hj⟩ | ⟨ws, hws⟩ :=
    lines_depthTwo_bottom_or_top (andreevTopOp b m) (andreevBottomOp b m) (fun _ => id) k
  · have hj' : (andreevCircuit b m).program.lines k =
        ⟨andreevBottomOp b m j, fun a => .input a⟩ := hj
    rw [hj']
    let idx := (andreevBottomEquiv b m).symm j
    exact .inl ⟨fun a => ⟨a, rfl⟩, fun a => ⟨andreevStairWeightInt b m idx.subset idx.stair a,
      abs_le_two_of_mem (andreevStairWeightInt_mem b m idx.subset idx.stair a), rfl⟩⟩
  · have hws' : (andreevCircuit b m).program.lines k =
        ⟨andreevTopOp b m, fun a => .gate (ws a)⟩ := hws
    rw [hws']
    refine .inr ⟨fun a => ⟨ws a, rfl⟩, fun a =>
      ⟨andreevTopWeightInt b m ((andreevBottomEquiv b m).symm a), ?_, ?_, rfl⟩⟩
    · exact Int.odd_iff.mpr (Int.emod_two_ne_zero.mp (andreevTopWeightInt_emod_two_ne_zero b m _))
    · refine (abs_andreevTopWeightInt_le b m _).trans_lt ?_
      push_cast
      exact sub_one_lt _

/-- **Exact quadratic depth-two threshold circuit upper bound for Andreev's function**:
for all `b, m : ℕ`, there is a depth-two weighted threshold circuit with
`2 * 4 ^ b + b * m * 2 ^ b` bottom gates computing `Boolean.andreev b m`, with bottom weights in
`{-2, -1, 0, 1, 2}` and odd integer top weights of absolute value at most
`2 * (2 ^ b + b * m) - 1`. -/
theorem exists_depthTwo_computes_andreev (b m : ℕ) :
    ∃ (top : Op) (bottom : Fin top.arity → Op)
      (args : ∀ j, Fin (bottom j).arity → Fin (2 ^ b + b * m)),
      top.arity = 2 * 4 ^ b + b * m * 2 ^ b ∧
      (depthTwo top bottom args).Computes interpretation (single (andreev b m)) ∧
      (depthTwo top bottom args).size = 2 * 4 ^ b + b * m * 2 ^ b + 1 ∧
      (depthTwo top bottom args).depth ≤ 2 ∧
      (∀ j a, |(bottom j).weight a| ≤ 2) ∧
      (∀ j, |(top.weight j)| ≤ 2 * (2 ^ b + b * m : ℝ) - 1) :=
  ⟨andreevTopOp b m, andreevBottomOp b m, fun _ => id, rfl,
    computes_andreevCircuit b m, size_andreevCircuit b m, depth_andreevCircuit_le b m,
    fun j a => abs_weight_andreevBottomOp_le b m j a,
    fun j => abs_weight_andreevTopOp_le b m j⟩

/-! ### Checked small-parameter example (`b = 2, m = 2`, `n = 8`) -/

/-- At `b = 2, m = 2` (`n = 8` input bits), `andreevCircuit 2 2` has `48` bottom gates. -/
theorem card_andreevBottomIndex_two_two : Fintype.card (AndreevBottomIndex 2 2) = 48 := by
  rw [card_andreevBottomIndex]; norm_num

/-- At `b = 2, m = 2`, `andreevCircuit 2 2` has `49` gates in total (`48` bottom gates and `1`
top gate). -/
theorem size_andreevCircuit_two_two : (andreevCircuit 2 2).size = 49 := by simp

/-- At `b = 2, m = 2`, `andreevCircuit 2 2` has at most `432` active wires. -/
theorem wireCount_andreevCircuit_two_two_le : (andreevCircuit 2 2).wireCount ≤ 432 :=
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
