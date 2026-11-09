/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Andreev
public import Complexity.Foundations.Combinatorics.Hoeffding

/-!
# Windowed depth-two weighted threshold circuits for Andreev's function

This module constructs the windowed depth-two weighted threshold circuit
`andreevWindowedCircuit b m r B` for Andreev's function `Boolean.andreev b m` on
`n = 2 ^ b + b * m` bits (Milestone 2 of
[#2347](https://github.com/cslib-community/complexitylib/issues/2347)).

Given a prefix length `r ≤ b` and a window half-width `B : ℕ`, the circuit sums only over subsets
`S ⊆ {0, …, r - 1}` (`andreevPrefixSubsets b r`, of size `t = 2 ^ r`) and telescopes each
`altLinear (u^±_S(w))` only over the integer window `[μ_{S,σ} - B, μ_{S,σ} + B]` of length `2 * B`
centered at `μ_{S,σ} = ±⌊(#S * m) / 2⌋` (`andreevWindowCenter`). This uses `4 * 2 ^ r * B` bottom
threshold gates (`4 * 2 ^ r * B + 1` total gates) with bottom weights in `{-2, -1, 0, 1, 2}`.

Whenever every `u^±_S(w)` for `S ∈ andreevPrefixSubsets b r` lies in its window
(`andreevInWindow b m r B w`), `andreevWindowedCircuit b m r B` agrees with the untruncated
subcube predictor `andreevSubcubeEval b m r w = decide (andreevSubcubeScore b m r w ≤ 0)`.
At `r = b`, `andreevSubcubeEval b m b w = andreev b m w` on every input, so
`andreevWindowedCircuit b m b B` computes `andreev b m w` on every in-window input.

## Main definitions

* `andreevPrefixCoords`, `andreevPrefixSubsets`: the first `r` block coordinates and their `2 ^ r`
  subsets.
* `andreevWindowCenter`, `andreevWindowLower`: window center `±⌊(#S * m) / 2⌋` and lower endpoint
  `μ_{S,σ} - B`.
* `andreevWindowedCircuit`, `andreevWindowedCircuitEvalInt`: explicit depth-two weighted threshold
  circuit with `4 * 2 ^ r * B` bottom gates and its choice-free integer evaluator.
* `andreevSubcubeScore`, `andreevSubcubeEval`, `andreevInWindow`: untruncated subcube Fourier sum,
  Boolean predictor, and the event that all `u^±_S(w)` for `S ∈ andreevPrefixSubsets b r` lie
  within `B` of `andreevWindowCenter m S σ`.

## Main results

* `size_andreevWindowedCircuit`, `depth_andreevWindowedCircuit_le`,
  `wireCount_andreevWindowedCircuit_le`, `abs_weight_andreevWindowedBottomOp_le`,
  `abs_weight_andreevWindowedTopOp_le`: gate, depth, wire, and weight bounds for
  `andreevWindowedCircuit b m r B`.
* `andreevWindowedCircuitEvalInt_eq_subcubeEval_of_inWindow`,
  `eval_andreevWindowedCircuit_self_eq_andreev_of_inWindow`: in-window agreement with
  `andreevSubcubeEval b m r` and (at `r = b`) with `andreev b m`.
* `card_filter_le_abs_andreevBlockSum_sub_half`, `card_filter_le_abs_andreevTableScore`: Hoeffding
  tail bounds for `andreevBlockSum` and `andreevTableScore`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Real

/-! ### Prefix subsets and windowed bottom-gate index -/

/-- The first `r` block coordinates in `Fin b`. -/
def andreevPrefixCoords (b r : ℕ) : Finset (Fin b) :=
  univ.filter fun j : Fin b => j.val < r

@[simp]
theorem mem_andreevPrefixCoords {b r : ℕ} (j : Fin b) :
    j ∈ andreevPrefixCoords b r ↔ j.val < r := by simp [andreevPrefixCoords]

/-- When `r ≤ b`, `andreevPrefixCoords b r` has cardinality `r`. -/
theorem card_andreevPrefixCoords {b r : ℕ} (hr : r ≤ b) : #(andreevPrefixCoords b r) = r := by
  have hmap : andreevPrefixCoords b r =
      (univ : Finset (Fin r)).map ⟨Fin.castLE hr, Fin.castLE_injective hr⟩ := by
    ext j
    simp only [mem_andreevPrefixCoords, mem_map, mem_univ, true_and, Function.Embedding.coeFn_mk]
    exact ⟨fun hj => ⟨⟨j.val, hj⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.isLt⟩
  rw [hmap, card_map, card_univ, Fintype.card_fin]

/-- At `r = b`, `andreevPrefixCoords b b` is `univ`. -/
@[simp]
theorem andreevPrefixCoords_self (b : ℕ) : andreevPrefixCoords b b = univ := by ext j; simp [j.isLt]

/-- The family of subsets of the first `r` block coordinates in `Fin b`. -/
def andreevPrefixSubsets (b r : ℕ) : Finset (Finset (Fin b)) :=
  (andreevPrefixCoords b r).powerset

@[simp]
theorem mem_andreevPrefixSubsets {b r : ℕ} (S : Finset (Fin b)) :
    S ∈ andreevPrefixSubsets b r ↔ S ⊆ andreevPrefixCoords b r := by simp [andreevPrefixSubsets]

/-- When `r ≤ b`, `andreevPrefixSubsets b r` has `2 ^ r` subsets. -/
theorem card_andreevPrefixSubsets {b r : ℕ} (hr : r ≤ b) :
    #(andreevPrefixSubsets b r) = 2 ^ r := by
  rw [andreevPrefixSubsets, card_powerset, card_andreevPrefixCoords hr]

/-- At `r = b`, `andreevPrefixSubsets b b` is `univ`. -/
@[simp]
theorem andreevPrefixSubsets_self (b : ℕ) : andreevPrefixSubsets b b = univ := by
  ext S; simp [subset_univ]

/-- Index type for the bottom gates of `andreevWindowedCircuit b m r B`:
a prefix subset `S ∈ andreevPrefixSubsets b r`, a sign bit `σ : Bool`, and a window step
`k : Fin (2 * B)`. -/
abbrev AndreevWindowedBottomIndex (b r B : ℕ) : Type :=
  {S : Finset (Fin b) // S ∈ andreevPrefixSubsets b r} × Bool × Fin (2 * B)

/-- The number of bottom gates in `andreevWindowedCircuit b m r B` is
`4 * #(andreevPrefixSubsets b r) * B`. -/
theorem card_andreevWindowedBottomIndex (b r B : ℕ) :
    Fintype.card (AndreevWindowedBottomIndex b r B) = 4 * #(andreevPrefixSubsets b r) * B := by
  simp only [AndreevWindowedBottomIndex, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
    Fintype.card_fin]; ring

/-- When `r ≤ b`, `AndreevWindowedBottomIndex b r B` has cardinality `4 * 2 ^ r * B`. -/
theorem card_andreevWindowedBottomIndex_of_le {b r : ℕ} (hr : r ≤ b) (B : ℕ) :
    Fintype.card (AndreevWindowedBottomIndex b r B) = 4 * 2 ^ r * B := by
  rw [card_andreevWindowedBottomIndex, card_andreevPrefixSubsets hr]

/-- Equivalence between `AndreevWindowedBottomIndex b r B` and
`Fin (4 * #(andreevPrefixSubsets b r) * B)`. -/
noncomputable def andreevWindowedBottomEquiv (b r B : ℕ) :
    AndreevWindowedBottomIndex b r B ≃ Fin (4 * #(andreevPrefixSubsets b r) * B) :=
  Fintype.equivFinOfCardEq (card_andreevWindowedBottomIndex b r B)

/-! ### Window parameters and untruncated subcube predictor -/

/-- Integer center `μ_{S,σ} = ±⌊(#S * m) / 2⌋` of the window for `(S, σ)`. -/
def andreevWindowCenter {b : ℕ} (m : ℕ) (S : Finset (Fin b)) (σ : Bool) : ℤ :=
  if σ then ((#S * m) / 2 : ℕ) else -(((#S * m) / 2 : ℕ) : ℤ)

/-- Lower endpoint `ℓ_{S,σ,B} = μ_{S,σ} - B` of the window of length `2 * B` for `(S, σ)`. -/
def andreevWindowLower {b : ℕ} (m B : ℕ) (S : Finset (Fin b)) (σ : Bool) : ℤ :=
  andreevWindowCenter m S σ - B

/-- Integer threshold of windowed bottom gate `(S, σ, k)`. -/
def andreevWindowedBottomThresholdInt (b m B : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (k : Fin (2 * B)) : ℤ :=
  andreevWindowLower m B S σ + k + 1 - andreevTableOffset b S

/-- Integer top-gate weight on windowed bottom gate `(S, σ, k)`. -/
def andreevWindowedTopWeightInt (b m B : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (k : Fin (2 * B)) : ℤ :=
  -(-1 : ℤ) ^ (2 ^ b) *
    (altLinear (andreevWindowLower m B S σ + k + 1) - altLinear (andreevWindowLower m B S σ + k))

/-- Integer threshold of the top gate of `andreevWindowedCircuit b m r B`. -/
def andreevWindowedTopThresholdInt (b m r B : ℕ) : ℤ :=
  ∑ S ∈ andreevPrefixSubsets b r, ∑ σ : Bool,
    (-1 : ℤ) ^ (2 ^ b) * altLinear (andreevWindowLower m B S σ)

/-- Choice-free computable evaluation of windowed bottom gate `(S, σ, k)` on input `w`. -/
def andreevWindowedBottomEvalInt (b m B : ℕ) (S : Finset (Fin b)) (σ : Bool) (k : Fin (2 * B))
    (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevWindowedBottomThresholdInt b m B S σ k ≤
    ∑ i : Fin (2 ^ b + b * m), andreevBottomWeightInt b m S σ i * (w i).toNat)

/-- Windowed bottom gate `(S, σ, k)` evaluates to `decide (ℓ_{S,σ,B} + k + 1 ≤ u^±_S(w))`. -/
theorem andreevWindowedBottomEvalInt_eq_decide (b m B : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (k : Fin (2 * B)) (w : BitString (2 ^ b + b * m)) :
    andreevWindowedBottomEvalInt b m B S σ k w =
      decide (andreevWindowLower m B S σ + k + 1 ≤ andreevLinearForm b m S σ w) := by
  rw [andreevWindowedBottomEvalInt, sum_andreevBottomWeightInt_mul,
    andreevWindowedBottomThresholdInt]
  exact decide_eq_decide.mpr ⟨by omega, by omega⟩

/-- Choice-free computable evaluation of the full windowed depth-two threshold network. -/
def andreevWindowedCircuitEvalInt (b m r B : ℕ) (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevWindowedTopThresholdInt b m r B ≤
    ∑ S ∈ andreevPrefixSubsets b r, ∑ σ : Bool, ∑ k : Fin (2 * B),
      andreevWindowedTopWeightInt b m B S σ k *
        (andreevWindowedBottomEvalInt b m B S σ k w).toNat)

/-- The untruncated subcube Fourier sum
`G_{b,m,r}(w) = ∑_{S ∈ andreevPrefixSubsets b r} X_S(w) * χ_S(andreevParities b m w)`. -/
def andreevSubcubeScore (b m r : ℕ) (w : BitString (2 ^ b + b * m)) : ℤ :=
  ∑ S ∈ andreevPrefixSubsets b r, andreevTableScore b m S w * chi ℤ S (andreevParities b m w)

/-- The untruncated subcube Boolean predictor `decide (andreevSubcubeScore b m r w ≤ 0)`. -/
def andreevSubcubeEval (b m r : ℕ) (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevSubcubeScore b m r w ≤ 0)

/-- At `r = b`, the untruncated subcube predictor equals `andreev b m` on every input. -/
theorem andreevSubcubeEval_self (b m : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevSubcubeEval b m b w = andreev b m w := by
  rw [andreevSubcubeEval, andreevSubcubeScore, andreevPrefixSubsets_self]
  have hreal : ((∑ S : Finset (Fin b),
      andreevTableScore b m S w * chi ℤ S (andreevParities b m w) : ℤ) : ℝ) =
      (2 ^ b : ℝ) * signVal (andreev b m w) := by
    push_cast; simpa [chi] using sum_andreevTableScore_mul_chi b m w
  have h2pow : (0 : ℝ) < (2 ^ b : ℝ) := by positivity
  rw [Bool.eq_iff_iff, decide_eq_true_eq, ← @Int.cast_nonpos ℝ, hreal]
  cases andreev b m w <;> simp

/-! ### In-window event and pointwise agreement -/

/-- The event that for every `S ∈ andreevPrefixSubsets b r` and `σ : Bool`,
`u^±_S(w)` lies in the window `[andreevWindowLower m B S σ, andreevWindowLower m B S σ + 2 * B]`. -/
def andreevInWindow (b m r B : ℕ) (w : BitString (2 ^ b + b * m)) : Prop :=
  ∀ S ∈ andreevPrefixSubsets b r, ∀ σ : Bool,
    andreevWindowLower m B S σ ≤ andreevLinearForm b m S σ w ∧
      andreevLinearForm b m S σ w ≤ andreevWindowLower m B S σ + (2 * B : ℕ)

instance (b m r B : ℕ) (w : BitString (2 ^ b + b * m)) :
    Decidable (andreevInWindow b m r B w) := by
  unfold andreevInWindow; infer_instance

/-- On any input `w` satisfying `andreevInWindow b m r B w`, the top-gate weighted sum minus the
top-gate threshold equals `-2 * andreevSubcubeScore b m r w`. -/
theorem sum_andreevWindowedTopWeightInt_sub_threshold_of_inWindow {b m r B : ℕ}
    {w : BitString (2 ^ b + b * m)} (hw : andreevInWindow b m r B w) :
    (∑ S ∈ andreevPrefixSubsets b r, ∑ σ : Bool, ∑ k : Fin (2 * B),
      andreevWindowedTopWeightInt b m B S σ k *
        (andreevWindowedBottomEvalInt b m B S σ k w).toNat) -
      andreevWindowedTopThresholdInt b m r B = -2 * andreevSubcubeScore b m r w := by
  have hsign_sq : (-1 : ℤ) ^ (2 ^ b) * (-1 : ℤ) ^ (2 ^ b) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [andreevWindowedTopThresholdInt, andreevSubcubeScore, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun S hS => ?_
  rw [← sum_sub_distrib]
  have htele (σ : Bool) :
      (∑ k : Fin (2 * B), andreevWindowedTopWeightInt b m B S σ k *
        (andreevWindowedBottomEvalInt b m B S σ k w).toNat) -
        (-1 : ℤ) ^ (2 ^ b) * altLinear (andreevWindowLower m B S σ) =
        -(-1 : ℤ) ^ (2 ^ b) * altLinear (andreevLinearForm b m S σ w) := by
    have hsum := sum_sub_mul_decide_le altLinear (hw S hS σ).1 (hw S hS σ).2
    simp only [andreevWindowedTopWeightInt, andreevWindowedBottomEvalInt_eq_decide,
      mul_assoc, ← mul_sum]
    rw [← hsum]; ring
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
        (2 * (-1 : ℤ) ^ (2 ^ b) * andreevTableScore b m S w * chi ℤ S (andreevParities b m w))
      = -2 * ((-1 : ℤ) ^ (2 ^ b) * (-1 : ℤ) ^ (2 ^ b)) *
          (andreevTableScore b m S w * chi ℤ S (andreevParities b m w)) := by ring
    _ = -2 * (andreevTableScore b m S w * chi ℤ S (andreevParities b m w)) := by
          rw [hsign_sq, mul_one]

/-- On any input `w` satisfying `andreevInWindow b m r B w`, `andreevWindowedCircuitEvalInt`
agrees with `andreevSubcubeEval b m r w`. -/
theorem andreevWindowedCircuitEvalInt_eq_subcubeEval_of_inWindow {b m r B : ℕ}
    {w : BitString (2 ^ b + b * m)} (hw : andreevInWindow b m r B w) :
    andreevWindowedCircuitEvalInt b m r B w = andreevSubcubeEval b m r w := by
  rw [andreevWindowedCircuitEvalInt, andreevSubcubeEval]
  have hint := sum_andreevWindowedTopWeightInt_sub_threshold_of_inWindow hw
  exact decide_eq_decide.mpr ⟨by omega, by omega⟩

/-- At `r = b`, on any input `w` satisfying `andreevInWindow b m b B w`,
`andreevWindowedCircuitEvalInt b m b B w` equals `andreev b m w`. -/
theorem andreevWindowedCircuitEvalInt_self_eq_andreev_of_inWindow {b m B : ℕ}
    {w : BitString (2 ^ b + b * m)} (hw : andreevInWindow b m b B w) :
    andreevWindowedCircuitEvalInt b m b B w = andreev b m w := by
  rw [andreevWindowedCircuitEvalInt_eq_subcubeEval_of_inWindow hw, andreevSubcubeEval_self]

/-! ### Explicit `WeightedThreshold` depth-two circuit `andreevWindowedCircuit` -/

/-- The `j`-th bottom gate of `andreevWindowedCircuit b m r B`. -/
noncomputable abbrev andreevWindowedBottomOp (b m r B : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsets b r) * B)) : Op :=
  let idx := (andreevWindowedBottomEquiv b r B).symm j
  { arity := 2 ^ b + b * m
    weight := fun i => (andreevBottomWeightInt b m idx.1.1 idx.2.1 i : ℝ)
    threshold := (andreevWindowedBottomThresholdInt b m B idx.1.1 idx.2.1 idx.2.2 : ℝ) }

/-- The top output gate of `andreevWindowedCircuit b m r B`. -/
noncomputable abbrev andreevWindowedTopOp (b m r B : ℕ) : Op where
  arity := 4 * #(andreevPrefixSubsets b r) * B
  weight := fun j =>
    let idx := (andreevWindowedBottomEquiv b r B).symm j
    (andreevWindowedTopWeightInt b m B idx.1.1 idx.2.1 idx.2.2 : ℝ)
  threshold := (andreevWindowedTopThresholdInt b m r B : ℝ)

/-- **Windowed depth-two weighted threshold circuit for Andreev's function**
`Boolean.andreev b m`, with `4 * #(andreevPrefixSubsets b r) * B` (`= 4 * 2 ^ r * B` for `r ≤ b`)
bottom gates and one top gate. -/
noncomputable def andreevWindowedCircuit (b m r B : ℕ) : Circuit signature (2 ^ b + b * m) 1 :=
  depthTwo (andreevWindowedTopOp b m r B) (andreevWindowedBottomOp b m r B) (fun _ => id)

/-- Evaluating `andreevWindowedBottomOp b m r B j` agrees with `andreevWindowedBottomEvalInt`. -/
theorem interpretation_andreevWindowedBottomOp (b m r B : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsets b r) * B)) (w : BitString (2 ^ b + b * m)) :
    interpretation (andreevWindowedBottomOp b m r B j) w =
      let idx := (andreevWindowedBottomEquiv b r B).symm j
      andreevWindowedBottomEvalInt b m B idx.1.1 idx.2.1 idx.2.2 w := by
  unfold interpretation andreevWindowedBottomOp andreevWindowedBottomEvalInt
  dsimp only
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-- Evaluating `andreevWindowedCircuit b m r B` agrees with `andreevWindowedCircuitEvalInt`. -/
theorem eval_andreevWindowedCircuit_eq_evalInt (b m r B : ℕ)
    (w : BitString (2 ^ b + b * m)) (o : Fin 1) :
    (andreevWindowedCircuit b m r B).eval interpretation w o =
      andreevWindowedCircuitEvalInt b m r B w := by
  rw [andreevWindowedCircuit, eval_depthTwo]
  simp only [id, interpretation_andreevWindowedBottomOp]
  unfold interpretation andreevWindowedTopOp andreevWindowedCircuitEvalInt
  dsimp only
  rw [← (andreevWindowedBottomEquiv b r B).sum_comp
    (fun j =>
      let idx := (andreevWindowedBottomEquiv b r B).symm j
      (andreevWindowedTopWeightInt b m B idx.1.1 idx.2.1 idx.2.2 : ℝ) *
        (andreevWindowedBottomEvalInt b m B idx.1.1 idx.2.1 idx.2.2 w).toNat)]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [Finset.sum_coe_sort (andreevPrefixSubsets b r) (fun S =>
    ∑ x_1 : Bool, ∑ x_2 : Fin (2 * B),
      (andreevWindowedTopWeightInt b m B S x_1 x_2 : ℝ) *
        (andreevWindowedBottomEvalInt b m B S x_1 x_2 w).toNat)]
  exact decide_eq_decide.mpr (by rw [← @Int.cast_le ℝ]; push_cast; rfl)

/-- On any in-window input `w`, `andreevWindowedCircuit b m r B` evaluates to
`andreevSubcubeEval b m r w`. -/
theorem eval_andreevWindowedCircuit_eq_subcubeEval_of_inWindow {b m r B : ℕ}
    {w : BitString (2 ^ b + b * m)} (hw : andreevInWindow b m r B w) (o : Fin 1) :
    (andreevWindowedCircuit b m r B).eval interpretation w o = andreevSubcubeEval b m r w := by
  rw [eval_andreevWindowedCircuit_eq_evalInt,
    andreevWindowedCircuitEvalInt_eq_subcubeEval_of_inWindow hw]

/-- At `r = b`, on any in-window input `w`, `andreevWindowedCircuit b m b B` evaluates to
`andreev b m w`. -/
theorem eval_andreevWindowedCircuit_self_eq_andreev_of_inWindow {b m B : ℕ}
    {w : BitString (2 ^ b + b * m)} (hw : andreevInWindow b m b B w) (o : Fin 1) :
    (andreevWindowedCircuit b m b B).eval interpretation w o = andreev b m w := by
  rw [eval_andreevWindowedCircuit_eq_evalInt,
    andreevWindowedCircuitEvalInt_self_eq_andreev_of_inWindow hw]

/-- When `r ≤ b`, `andreevWindowedCircuit b m r B` has `4 * 2 ^ r * B + 1` gates. -/
theorem size_andreevWindowedCircuit {b r : ℕ} (hr : r ≤ b) (m B : ℕ) :
    (andreevWindowedCircuit b m r B).size = 4 * 2 ^ r * B + 1 := by
  simp [andreevWindowedCircuit, card_andreevPrefixSubsets hr]

/-- `andreevWindowedCircuit b m r B` has depth at most `2`. -/
theorem depth_andreevWindowedCircuit_le (b m r B : ℕ) :
    (andreevWindowedCircuit b m r B).depth ≤ 2 :=
  depth_depthTwo_le _ _ _

/-- When `r ≤ b`, the active wire count of `andreevWindowedCircuit b m r B` is at most
`(4 * 2 ^ r * B) * (2 ^ b + b * m + 1)`. -/
theorem wireCount_andreevWindowedCircuit_le {b r : ℕ} (hr : r ≤ b) (m B : ℕ) :
    (andreevWindowedCircuit b m r B).wireCount ≤ (4 * 2 ^ r * B) * (2 ^ b + b * m + 1) := by
  refine (wireCount_depthTwo_le _ _ _).trans ?_
  simp only [andreevWindowedTopOp, sum_const, card_univ, Fintype.card_fin, smul_eq_mul,
    card_andreevPrefixSubsets hr]
  linarith

/-- Every bottom gate of `andreevWindowedCircuit b m r B` has real weights of absolute value at
most `2`. -/
theorem abs_weight_andreevWindowedBottomOp_le (b m r B : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsets b r) * B)) (i : Fin (2 ^ b + b * m)) :
    |(andreevWindowedBottomOp b m r B j).weight i| ≤ 2 := by
  unfold andreevWindowedBottomOp; dsimp only
  exact_mod_cast abs_andreevBottomWeightInt_le b m
    ((andreevWindowedBottomEquiv b r B).symm j).1.1
    ((andreevWindowedBottomEquiv b r B).symm j).2.1 i

/-- Every integer top-gate weight in `andreevWindowedCircuit b m r B` has absolute value at most
`b * m + 2 * B + 1`. -/
theorem abs_andreevWindowedTopWeightInt_le (b m B : ℕ) (S : Finset (Fin b)) (σ : Bool)
    (k : Fin (2 * B)) :
    |andreevWindowedTopWeightInt b m B S σ k| ≤ b * m + 2 * B + 1 := by
  have hS : #S * m ≤ b * m :=
    Nat.mul_le_mul_right m ((card_le_univ S).trans_eq (Fintype.card_fin b))
  have hdiv : 2 * ((#S * m) / 2) ≤ #S * m := Nat.mul_div_le (#S * m) 2
  have hk : (k : ℕ) < 2 * B := k.isLt
  rw [andreevWindowedTopWeightInt, abs_mul, abs_neg, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    altLinear_add_one_sub, abs_mul, Int.abs_negOnePow, one_mul]
  cases σ <;>
    simp only [andreevWindowLower, andreevWindowCenter, ↓reduceIte, Bool.false_eq_true] <;>
    exact abs_le.mpr ⟨by omega, by omega⟩

/-- The top gate of `andreevWindowedCircuit b m r B` has real weights of absolute value at most
`b * m + 2 * B + 1`. -/
theorem abs_weight_andreevWindowedTopOp_le (b m r B : ℕ)
    (j : Fin (4 * #(andreevPrefixSubsets b r) * B)) :
    |(andreevWindowedTopOp b m r B).weight j| ≤ b * m + 2 * B + 1 := by
  unfold andreevWindowedTopOp; dsimp only
  exact_mod_cast abs_andreevWindowedTopWeightInt_le b m B
    ((andreevWindowedBottomEquiv b r B).symm j).1.1
    ((andreevWindowedBottomEquiv b r B).symm j).2.1
    ((andreevWindowedBottomEquiv b r B).symm j).2.2

/-! ### Hoeffding concentration bounds -/

/-- `andreevTableIndex b m` is injective. -/
theorem andreevTableIndex_injective (b m : ℕ) :
    Function.Injective (andreevTableIndex b m) :=
  Fin.castAdd_injective (2 ^ b) (b * m)

/-- The `2 ^ b` truth-table coordinates of `BitString (2 ^ b + b * m)`. -/
def andreevTableSupport (b m : ℕ) : Finset (Fin (2 ^ b + b * m)) :=
  univ.map ⟨andreevTableIndex b m, andreevTableIndex_injective b m⟩

@[simp]
theorem card_andreevTableSupport (b m : ℕ) : #(andreevTableSupport b m) = 2 ^ b := by
  simp [andreevTableSupport]

/-- The `#S * m` block coordinates in `BitString (2 ^ b + b * m)` belonging to blocks `j ∈ S`. -/
def andreevBlockSupport {b : ℕ} (m : ℕ) (S : Finset (Fin b)) : Finset (Fin (2 ^ b + b * m)) :=
  (S ×ˢ (univ : Finset (Fin m))).map
    ⟨fun p => andreevBlockVar b m p.1 p.2, fun p q hpq => by
      simpa [andreevBlockVar, Fin.natAdd_inj] using hpq⟩

@[simp]
theorem card_andreevBlockSupport {b : ℕ} (m : ℕ) (S : Finset (Fin b)) :
    #(andreevBlockSupport m S) = #S * m := by
  simp [andreevBlockSupport]

/-- As a real number, `andreevBlockSum b m S w` is the number of true coordinates of `w` in
`andreevBlockSupport m S`. -/
theorem cast_andreevBlockSum_eq_card_filter (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    (andreevBlockSum b m S w : ℝ) =
      (#{i ∈ andreevBlockSupport m S | w i = true} : ℝ) := by
  rw [andreevBlockSupport, card_filter, sum_map, sum_product]
  simp only [andreevBlockSum, Int.cast_sum, Int.cast_natCast, Nat.cast_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun t _ => ?_
  cases w (andreevBlockVar b m j t) <;> simp

/-- **Hoeffding tail bound for `andreevBlockSum`**: at most a
`2 * exp (-(2 * t ^ 2 / (#S * m)))` fraction of inputs `w` have `|t_S(w) - #S * m / 2| ≥ t`. -/
theorem card_filter_le_abs_andreevBlockSum_sub_half (b m : ℕ) (S : Finset (Fin b))
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) |
      t ≤ |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2|} : ℝ) ≤
      2 * 2 ^ (2 ^ b + b * m) * exp (-(2 * t ^ 2 / (#S * m))) := by
  have h := Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le
    (andreevBlockSupport m S) ht
  simpa [cast_andreevBlockSum_eq_card_filter, Fintype.card_fin, Nat.cast_mul] using h

/-- Uniform Hoeffding tail bound for `andreevBlockSum` with denominator `b * m` in the exponent,
valid for all `S : Finset (Fin b)` (including `S = ∅` or `m = 0`). -/
theorem card_filter_le_abs_andreevBlockSum_sub_half_bm (b m : ℕ) (S : Finset (Fin b))
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) |
      t ≤ |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2|} : ℝ) ≤
      2 * 2 ^ (2 ^ b + b * m) * exp (-(2 * t ^ 2 / (b * m : ℝ))) := by
  rcases eq_or_lt_of_le (by positivity : (0 : ℝ) ≤ (#S * m : ℝ)) with hSm | hSm_pos
  · rcases eq_or_lt_of_le ht with rfl | ht_pos
    · have hreal : (#{w : BitString (2 ^ b + b * m) |
          (0 : ℝ) ≤ |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2|} : ℝ) ≤
          2 ^ (2 ^ b + b * m) := by
        exact_mod_cast (card_le_univ _).trans_eq BitString.card
      have h2 : (0 : ℝ) ≤ 2 ^ (2 ^ b + b * m) := by positivity
      simp only [sq, mul_zero, zero_div, neg_zero, exp_zero, mul_one]; linarith
    · have hzero_sum (w : BitString (2 ^ b + b * m)) : (andreevBlockSum b m S w : ℝ) = 0 := by
        have hnat : #S * m = 0 := by exact_mod_cast hSm.symm
        have hempty : andreevBlockSupport m S = ∅ :=
          card_eq_zero.mp (by rw [card_andreevBlockSupport, hnat])
        rw [cast_andreevBlockSum_eq_card_filter, hempty]; simp
      have hempty_filter : ({w : BitString (2 ^ b + b * m) |
          t ≤ |(andreevBlockSum b m S w : ℝ) - (#S * m : ℝ) / 2|} : Finset _) = ∅ := by
        ext w; simp [hzero_sum, ← hSm, not_le.mpr ht_pos]
      rw [hempty_filter, card_empty, Nat.cast_zero]; positivity
  · refine (card_filter_le_abs_andreevBlockSum_sub_half b m S ht).trans ?_
    refine mul_le_mul_of_nonneg_left (exp_le_exp.mpr (neg_le_neg_iff.mpr ?_)) (by positivity)
    have hS : (#S * m : ℝ) ≤ (b * m : ℝ) := by
      have : #S ≤ b := (card_le_univ S).trans_eq (Fintype.card_fin b)
      exact_mod_cast Nat.mul_le_mul_right m this
    exact div_le_div_of_nonneg_left (by positivity) hSm_pos hS

/-- Measure-preserving involution on `BitString (2 ^ b + b * m)` that XORs each truth-table bit
`c` with `parityOn S c` and leaves all block variables unchanged. -/
def andreevFlipTable (b m : ℕ) (S : Finset (Fin b)) :
    Equiv.Perm (BitString (2 ^ b + b * m)) where
  toFun w := Fin.addCases
    (fun idx => xor (w (andreevTableIndex b m idx))
      (parityOn S ((BitString.equivFin b).symm idx)))
    (fun u => w (Fin.natAdd (2 ^ b) u))
  invFun w := Fin.addCases
    (fun idx => xor (w (andreevTableIndex b m idx))
      (parityOn S ((BitString.equivFin b).symm idx)))
    (fun u => w (Fin.natAdd (2 ^ b) u))
  left_inv w := by
    funext i; refine Fin.addCases (fun idx => ?_) (fun u => ?_) i <;> simp [andreevTableIndex]
  right_inv w := by
    funext i; refine Fin.addCases (fun idx => ?_) (fun u => ?_) i <;> simp [andreevTableIndex]

/-- Applying `andreevFlipTable b m S` turns `andreevTableScore b m S` into the unweighted
truth-table discrepancy `2 ^ b - 2 * #{i ∈ andreevTableSupport b m | w i = true}`. -/
theorem cast_andreevTableScore_flipTable (b m : ℕ) (S : Finset (Fin b))
    (w : BitString (2 ^ b + b * m)) :
    (andreevTableScore b m S (andreevFlipTable b m S w) : ℝ) =
      -2 * ((#{i ∈ andreevTableSupport b m | w i = true} : ℝ) - (2 ^ b : ℝ) / 2) := by
  have hxor (p v : Bool) :
      ((-1 : ℝ) ^ p.toNat) * (1 - 2 * ((xor v p).toNat : ℝ)) = 1 - 2 * (v.toNat : ℝ) := by
    cases p <;> cases v <;> norm_num
  have hscore : (andreevTableScore b m S (andreevFlipTable b m S w) : ℝ) =
      ∑ c : BitString b,
        (1 - 2 * ((w (andreevTableIndex b m (BitString.equivFin b c))).toNat : ℝ)) := by
    simp only [andreevTableScore, Int.cast_sum, Int.cast_mul, Int.cast_sub, Int.cast_one,
      Int.cast_ofNat, Int.cast_natCast]
    refine sum_congr rfl fun c _ => ?_
    have hchi : ((chi ℤ S c : ℤ) : ℝ) = (-1 : ℝ) ^ (parityOn S c).toNat := by
      rw [chi_eq_neg_one_pow_parityOn]; push_cast; rfl
    rw [hchi]
    simpa [andreevFlipTable, andreevTableIndex] using
      hxor (parityOn S c) (w (andreevTableIndex b m (BitString.equivFin b c)))
  have hcard : (#{i ∈ andreevTableSupport b m | w i = true} : ℝ) =
      ∑ c : BitString b, ((w (andreevTableIndex b m (BitString.equivFin b c))).toNat : ℝ) := by
    rw [andreevTableSupport, card_filter, sum_map]
    simp only [Function.Embedding.coeFn_mk, Nat.cast_sum]
    rw [← (BitString.equivFin b).sum_comp
      (fun idx => ((if w (andreevTableIndex b m idx) = true then 1 else 0 : ℕ) : ℝ))]
    refine sum_congr rfl fun c _ => ?_
    cases w (andreevTableIndex b m (BitString.equivFin b c)) <;> simp
  rw [hscore, hcard, sum_sub_distrib, ← mul_sum]
  simp only [sum_const, card_univ, BitString.card, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- **Hoeffding tail bound for `andreevTableScore`**: at most a
`2 * exp (-(2 * t ^ 2 / 2 ^ b))` fraction of inputs `w` have `|X_S(w)| ≥ 2 * t`. -/
theorem card_filter_le_abs_andreevTableScore (b m : ℕ) (S : Finset (Fin b))
    {t : ℝ} (ht : 0 ≤ t) :
    (#{w : BitString (2 ^ b + b * m) | 2 * t ≤ |(andreevTableScore b m S w : ℝ)|} : ℝ) ≤
      2 * 2 ^ (2 ^ b + b * m) * exp (-(2 * t ^ 2 / (2 ^ b : ℝ))) := by
  have hbij : #{w : BitString (2 ^ b + b * m) | 2 * t ≤ |(andreevTableScore b m S w : ℝ)|} =
      #{w : BitString (2 ^ b + b * m) |
        t ≤ |(#{i ∈ andreevTableSupport b m | w i = true} : ℝ) -
          #(andreevTableSupport b m) / 2|} := by
    rw [← card_map (andreevFlipTable b m S).toEmbedding]
    congr 1; ext w
    simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hinv : andreevFlipTable b m S (andreevFlipTable b m S u) = u :=
        (andreevFlipTable b m S).symm_apply_apply u
      have hscore := cast_andreevTableScore_flipTable b m S (andreevFlipTable b m S u)
      rw [hinv] at hscore
      rw [hscore, abs_mul, show |(-2 : ℝ)| = 2 by norm_num] at hu
      rw [card_andreevTableSupport, Nat.cast_pow, Nat.cast_ofNat]; linarith
    · intro hw
      refine ⟨andreevFlipTable b m S w, ?_, (andreevFlipTable b m S).apply_symm_apply w⟩
      rw [cast_andreevTableScore_flipTable b m S w, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
      rw [card_andreevTableSupport, Nat.cast_pow, Nat.cast_ofNat] at hw; linarith
  rw [hbij]
  simpa [Fintype.card_fin] using
    Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le (andreevTableSupport b m) ht

end Cslib.Circuits.Boolean.WeightedThreshold
