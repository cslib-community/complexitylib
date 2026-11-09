/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.KaneWilliamsB
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Discriminator
import CslibFrontier.Probability.SmallBias.Correlation
import Mathlib.Tactic.FinCases

/-! Tests for the Kane–Williams depth-three function: its values on concrete inputs, tightness of
the correlation-list bound (Kane–Williams Lemma 6.1) for the full list of rows, the discriminator
lemma on a majority vote, a depth-two circuit computing the function (so that the hypotheses of the
worst-case bounds can all hold), and the gate, wire and agreement bounds at `p = 20`. -/

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.WeightedThreshold Finset Probability

namespace KaneWilliamsBTests

/-! ### The function on concrete inputs -/

/-- Two rows of length two, indexed by one parity bit. -/
private def rows : BitString 1 → BitString 2 :=
  fun z => if z 0 then ![true, true] else ![true, false]

-- Message `(1, 0)` and block `(1, 0)` of parity `1` read the row `(1, 1)`: the value is `1`.
example : kaneWilliamsB rows 2 ![true, false, true, false] = true := by decide

-- Message `(0, 1)` and block `(1, 1)` of parity `0` read the row `(1, 0)`: the value is `0`.
example : kaneWilliamsB rows 2 ![false, true, true, true] = false := by decide

example : kaneWilliamsMessage 2 1 2 ![false, true, true, true] = ![false, true] := by decide

example : kaneWilliamsParities 2 1 2 ![false, true, true, true] = ![false] := by decide

/-! ### The correlation-list bound is attained by the full list -/

private theorem sum_bitString_two (f : BitString 2 → ℝ) :
    ∑ z, f z = f ![false, false] + f ![false, true] + (f ![true, false] + f ![true, true]) := by
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  simp only [finTwoArrowEquiv_symm_apply, Fintype.sum_bool]
  ring

private theorem dotProduct_two (a b c d : Bool) :
    ![a, b] ⬝ᵥ ![c, d] = ((a && c) ^^ (b && d)) := by
  decide +revert

private theorem eq_two (x : BitString 2) : x = ![x 0, x 1] := by
  ext i; fin_cases i <;> rfl

/-- The full list of rows `BitString 2 → BitString 2` is unbiased. -/
private theorem isSmallBias_id : IsSmallBias 0 ((PMF.uniformOfFintype (BitString 2)).map id) := by
  rw [PMF.map_id]
  exact isSmallBias_uniformOfFintype

/-- The bent word `z 0 && z 1` has correlation `±2 = ±|Z| / 2` with all four codewords. -/
private theorem card_bent :
    (#{x : BitString 2 | (1 / 2 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0 && z 1) * signVal (id z ⬝ᵥ x)|} : ℝ) = 4 := by
  have h (x : BitString 2) : (1 / 2 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0 && z 1) * signVal (id z ⬝ᵥ x)| := by
    rw [sum_bitString_two, eq_two x]
    simp only [id, dotProduct_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    cases x 0 <;> cases x 1 <;> norm_num
  rw [filter_true_of_mem fun x _ => h x]
  simp

-- Lemma 6.1 at `γ = 1 / 2` and `δ = 0` allows at most `1 / γ ^ 2 = 4` messages whose codewords
-- correlate with a fixed word by `γ |Z|`; the bent word attains this.
example : (#{x : BitString 2 | (1 / 2 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0 && z 1) * signVal (id z ⬝ᵥ x)|} : ℝ) * ((1 / 2) ^ 2 - 0) = 1 := by
  rw [card_bent]; norm_num

example : (#{x : BitString 2 | (1 / 2 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0 && z 1) * signVal (id z ⬝ᵥ x)|} : ℝ) * ((1 / 2) ^ 2 - 0) ≤ 1 :=
  card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le le_rfl (by norm_num) isSmallBias_id _

-- Only one codeword, that of `(1, 0)`, correlates perfectly with the dictator word `z 0`.
example : (#{x : BitString 2 | (1 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0) * signVal (id z ⬝ᵥ x)|} : ℝ) = 1 := by
  have hle := card_le_abs_sum_signVal_mul_signVal_dotProduct_mul_le le_rfl zero_le_one
    isSmallBias_id fun z => z 0
  have hmem : ![true, false] ∈ ({x : BitString 2 | (1 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0) * signVal (id z ⬝ᵥ x)|} : Finset (BitString 2)) := by
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    rw [sum_bitString_two]
    simp only [id, dotProduct_two, Matrix.cons_val_zero]
    norm_num
  have hpos : (1 : ℝ) ≤ #({x : BitString 2 | (1 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0) * signVal (id z ⬝ᵥ x)|} : Finset (BitString 2)) := by
    exact_mod_cast card_pos.mpr ⟨_, hmem⟩
  have hle' : (#({x : BitString 2 | (1 : ℝ) * Fintype.card (BitString 2) ≤
      |∑ z, signVal (z 0) * signVal (id z ⬝ᵥ x)|} : Finset (BitString 2)) : ℝ) ≤ 1 := by
    simpa only [one_pow, sub_zero, mul_one] using hle
  exact le_antisymm hle' hpos

/-! ### The discriminator lemma on a majority vote -/

/-- The majority of the votes `(u 0, u 0, u 1)` is `u 0`. -/
private theorem majority_votes (u : BitString 2) : threshold 3 2 ![u 0, u 0, u 1] = u 0 := by
  rw [eq_two u]
  cases u 0 <;> cases u 1 <;> decide

-- The target `u 0` is balanced, so the votes correlate with it by at least `|U| = 4` in total.
example : (4 : ℝ) ≤ ∑ i, ∑ u : BitString 2, signVal (![u 0, u 0, u 1] i) * signVal (u 0) := by
  have h := sub_le_sum_sum_signVal_mul_of_threshold_eq (fun u : BitString 2 => ![u 0, u 0, u 1])
    (fun u => u 0) majority_votes
  have hbal : ∑ u : BitString 2, signVal (u 0) = 0 := by
    rw [sum_bitString_two]; norm_num
  rw [hbal] at h
  norm_num at h
  exact h

-- A unanimous threshold vote of one voter correlates fully with its target.
example (F : BitString 2 → Bool) :
    (4 : ℝ) - 2 * |∑ u, signVal (F u)| ≤ ∑ i : Fin 1, ∑ u, signVal (![F u] i) * signVal (F u) := by
  have h := sub_le_sum_sum_signVal_mul_of_threshold_eq (θ := 1) (fun u : BitString 2 => ![F u]) F
    fun u => by cases F u <;> decide
  norm_num at h ⊢
  linarith

/-! ### The hypotheses of the worst-case bounds can hold

Every Boolean function has a depth-two weighted threshold circuit: an `OR` gate over minterm gates.
Below it computes the Kane–Williams function at `p = 20` under a top gate `threshold 1 1`, which
passes its single input through. -/

/-- The minterm gate of `a`: `∑ i, ±x i ≥ weight a`, with `+` exactly where `a` is true. -/
private abbrev mintermOp {N : ℕ} (a : BitString N) : WeightedThreshold.Op :=
  ⟨N, fun i => if a i then 1 else -1, (weight a : ℝ)⟩

/-- The minterm gate of `a` is true exactly at `a`. -/
private theorem interpretation_mintermOp {N : ℕ} (a x : BitString N) :
    WeightedThreshold.interpretation (mintermOp a) x = decide (x = a) := by
  have hterm (i : Fin N) :
      (if a i then (1 : ℝ) else -1) * ((x i).toNat : ℝ) ≤ ((a i).toNat : ℝ) := by
    cases a i <;> cases x i <;> norm_num
  have hweight : (weight a : ℝ) = ∑ i, ((a i).toNat : ℝ) := by
    rw [weight_eq_sum_toNat]; push_cast; rfl
  change decide ((weight a : ℝ) ≤ ∑ i, (if a i then (1 : ℝ) else -1) * ((x i).toNat : ℝ)) = _
  rw [hweight, Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
  constructor
  · intro h
    have heq := (sum_eq_sum_iff_of_le fun i _ => hterm i).mp
      (le_antisymm (sum_le_sum fun i _ => hterm i) h)
    funext i
    have hi := heq i (mem_univ i)
    revert hi
    cases a i <;> cases x i <;> norm_num
  · rintro rfl
    exact le_of_eq (sum_congr rfl fun i _ => by cases x i <;> norm_num)

/-- The disjunctive normal form of `f` as a depth-two weighted threshold circuit: an `OR` gate over
the minterm gates of all points, with weight one exactly at the points where `f` is true. -/
private noncomputable def dnfCircuit {N : ℕ} (f : BitString N → Bool) :
    Circuit WeightedThreshold.signature N 1 :=
  depthTwo ⟨2 ^ N, fun j => if f ((BitString.equivFin N).symm j) then 1 else 0, 1⟩
    (fun j => mintermOp ((BitString.equivFin N).symm j)) fun _ => id

private theorem eval_dnfCircuit {N : ℕ} (f : BitString N → Bool) (x : BitString N) :
    (dnfCircuit f).eval WeightedThreshold.interpretation x 0 = f x := by
  rw [dnfCircuit, eval_depthTwo]
  simp only [interpretation_mintermOp, id]
  change decide ((1 : ℝ) ≤ ∑ j : Fin (2 ^ N),
    (if f ((BitString.equivFin N).symm j) then (1 : ℝ) else 0) *
      ((decide ((fun a => x a) = (BitString.equivFin N).symm j)).toNat : ℝ)) = f x
  rw [Fintype.sum_equiv (BitString.equivFin N).symm _
    (fun a => (if f a then (1 : ℝ) else 0) * ((decide (x = a)).toNat : ℝ)) fun j => rfl,
    sum_eq_single x (fun a _ hax => by simp [Ne.symm hax]) (by simp)]
  cases f x <;> norm_num

private theorem threshold_one_one (v : BitString 1) : threshold 1 1 v = v 0 := by
  revert v; decide

-- At `p = 20` and `n = 16 * 20 * 3276 = 1048320 ≤ 2 ^ 20`, the rows of bias `2 ^ (-140)` exist and
-- a depth-two circuit computes the Kane–Williams function with top fan-in `t = 1`: the hypotheses
-- of `size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced` hold together.
example : ∃ (r : BitString (16 * 20) → BitString (16 * 20 * 3276))
    (c : Circuit WeightedThreshold.signature (16 * 20 * 3276 + 16 * 20 * 3276) 1),
    IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r) ∧
      c.depth ≤ 2 ∧
      ∀ y, threshold 1 1 (c.eval WeightedThreshold.interpretation y) = kaneWilliamsB r 3276 y := by
  obtain ⟨r, hr⟩ := exists_isSmallBias_kaneWilliamsRows (p := 20) (n := 16 * 20 * 3276)
    (by norm_num) (by norm_num)
  exact ⟨r, dnfCircuit (kaneWilliamsB r 3276), hr, depth_depthTwo_le _ _ _,
    fun y => by rw [threshold_one_one, eval_dnfCircuit]⟩

/-! ### Balanced bounds at `p = 20`: `n = 1048320`, so `2 n = 2096640` inputs -/

private theorem sqrt_two_mul_le : Real.sqrt (2 * ((16 * 20 * 3276 : ℕ) : ℝ)) ≤ 1448 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

-- Every unweighted threshold gate of fan-in at most `n ^ 3 / 4` over a depth-two circuit computing
-- the function needs at least `350` gates in the depth-two circuit.
example {t : ℕ} (ht : 4 * t ≤ (16 * 20 * 3276) ^ 3)
    {r : BitString (16 * 20) → BitString (16 * 20 * 3276)}
    (hr : IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r))
    (c : Circuit WeightedThreshold.signature (16 * 20 * 3276 + 16 * 20 * 3276) t)
    (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval WeightedThreshold.interpretation y) = kaneWilliamsB r 3276 y) :
    350 ≤ c.size := by
  have h := size_ge_of_threshold_eval_eq_kaneWilliamsB_balanced (p := 20) (n := 16 * 20 * 3276)
    (ℓ := 3276) (by norm_num) rfl (by norm_num) ht hr c hd θ hc
  by_contra hlt
  have hs : (c.size : ℝ) ≤ 349 := by exact_mod_cast (show c.size ≤ 349 by omega)
  have hprod := mul_le_mul hs sqrt_two_mul_le (Real.sqrt_nonneg _) (by norm_num)
  norm_num at h hprod
  nlinarith

-- ... and more than `28 * 10 ^ 6` wires, about `13` per input.
example {t : ℕ} (ht : 4 * t ≤ (16 * 20 * 3276) ^ 3)
    {r : BitString (16 * 20) → BitString (16 * 20 * 3276)}
    (hr : IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r))
    (c : Circuit WeightedThreshold.signature (16 * 20 * 3276 + 16 * 20 * 3276) t)
    (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval WeightedThreshold.interpretation y) = kaneWilliamsB r 3276 y) :
    28 * 10 ^ 6 < c.wireCount := by
  have h := wireCount_ge_of_threshold_eval_eq_kaneWilliamsB_balanced (p := 20)
    (n := 16 * 20 * 3276) (ℓ := 3276) (by norm_num) rfl (by norm_num) ht hr c hd θ hc
  have hsn : (1023 : ℝ) ≤ Real.sqrt ((16 * 20 * 3276 : ℕ) : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have hsp : Real.sqrt ((20 : ℕ) : ℝ) ≤ 448 / 100 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  by_contra hlt
  have hw : (c.wireCount : ℝ) ≤ 28 * 10 ^ 6 := by
    exact_mod_cast (show c.wireCount ≤ 28 * 10 ^ 6 by omega)
  have hprod := mul_le_mul hsp hw (Nat.cast_nonneg _) (by norm_num)
  norm_num at h hsn hprod
  nlinarith

-- A depth-two circuit with at most `10` gates agrees with the function on at most `52%` of the
-- inputs.
example {r : BitString (16 * 20) → BitString (16 * 20 * 3276)}
    (hr : IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r))
    (c : Circuit WeightedThreshold.signature (16 * 20 * 3276 + 16 * 20 * 3276) 1)
    (hd : c.depth ≤ 2) (hs : c.size ≤ 10) :
    (#{y | c.eval WeightedThreshold.interpretation y 0 = kaneWilliamsB r 3276 y} : ℝ) ≤
      2 ^ (2 * (16 * 20 * 3276)) * (52 / 100) := by
  have h := card_eval_eq_kaneWilliamsB_le_balanced_size (p := 20) (n := 16 * 20 * 3276)
    (ℓ := 3276) (by norm_num) rfl (by norm_num) (by norm_num) hr c hd 0
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hs' : (c.size : ℝ) ≤ 10 := by exact_mod_cast hs
  have hprod := mul_le_mul hs' sqrt_two_mul_le (Real.sqrt_nonneg _) (by norm_num)
  norm_num at hprod ⊢
  have key : 972800 * (c.size : ℝ) * Real.sqrt 2096640 / 983719376640 ≤
      972800 * 14480 / 983719376640 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith

/-! ### Bounds for any block length at `p = 20`: `2 ^ 20` message bits, blocks of `3276` bits -/

-- Rows of bias `2 ^ (-140)` exist for messages of `2 ^ 20` bits.
example : ∃ r : BitString (16 * 20) → BitString (2 ^ 20),
    IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r) :=
  exists_isSmallBias_kaneWilliamsRows (by norm_num) le_rfl

private theorem sqrt_inputs_le : Real.sqrt ((2 ^ 20 + 16 * 20 * 3276 : ℕ) : ℝ) ≤ 1449 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

-- With `2 ^ 20` message bits and blocks of `3276` bits (`2 ^ 21 - 256` inputs), every unweighted
-- threshold gate of fan-in at most `2 ^ 58` over a depth-two circuit computing the function needs
-- at least `350` gates in the depth-two circuit.
example {t : ℕ} (ht : t ≤ 2 ^ 58) {r : BitString (16 * 20) → BitString (2 ^ 20)}
    (hr : IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r))
    (c : Circuit WeightedThreshold.signature (2 ^ 20 + 16 * 20 * 3276) t) (hd : c.depth ≤ 2) (θ : ℕ)
    (hc : ∀ y, threshold t θ (c.eval WeightedThreshold.interpretation y) = kaneWilliamsB r 3276 y) :
    350 ≤ c.size := by
  have h := size_ge_of_threshold_eval_eq_kaneWilliamsB_of_le_two_pow (p := 20) (by norm_num)
    le_rfl (by norm_num) (by norm_num) (by omega) hr c hd θ hc
  by_contra hlt
  have hs : (c.size : ℝ) ≤ 349 := by exact_mod_cast (show c.size ≤ 349 by omega)
  have hprod := mul_le_mul hs sqrt_inputs_le (Real.sqrt_nonneg _) (by norm_num)
  norm_num at h hprod
  nlinarith

-- A depth-two circuit with at most `10` gates agrees with the function on at most `52%` of the
-- inputs.
example {r : BitString (16 * 20) → BitString (2 ^ 20)}
    (hr : IsSmallBias ((1 / 2) ^ (7 * 20)) ((PMF.uniformOfFintype (BitString (16 * 20))).map r))
    (c : Circuit WeightedThreshold.signature (2 ^ 20 + 16 * 20 * 3276) 1) (hd : c.depth ≤ 2)
    (hs : c.size ≤ 10) :
    (#{y | c.eval WeightedThreshold.interpretation y 0 = kaneWilliamsB r 3276 y} : ℝ) ≤
      2 ^ (2 ^ 20 + 16 * 20 * 3276) * (52 / 100) := by
  have h := card_eval_eq_kaneWilliamsB_le_of_le_two_pow_size (p := 20) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (by norm_num) hr c hd 0
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hs' : (c.size : ℝ) ≤ 10 := by exact_mod_cast hs
  have hprod := mul_le_mul hs' sqrt_inputs_le (Real.sqrt_nonneg _) (by norm_num)
  norm_num at hprod ⊢
  have key : 3040 * (c.size : ℝ) * Real.sqrt 2096896 / 3074961708 ≤ 3040 * 14490 / 3074961708 :=
    div_le_div_of_nonneg_right (by linarith) (by norm_num)
  linarith

end KaneWilliamsBTests
