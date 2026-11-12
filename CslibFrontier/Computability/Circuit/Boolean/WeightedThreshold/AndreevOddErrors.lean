/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedThreshold.AndreevAverage
public import CslibFrontier.Foundations.Combinatorics.TailSum
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Odd errors are orthogonal: truncating the subcube vote for Andreev's function

This module formalizes Lemma 6 and the error analysis in the proof of Theorem 7 of
C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function* (preprint, November 2026),
issue [#4640](https://github.com/cslib-community/cslib-frontier/issues/4640), Milestone 2.
Notation: `N = 2 ^ k` table bits (Lean `b = k`), `k` address blocks of `m` bits, `n = N + k m`,
`X_S` = `andreevTableScore`, `t_S` = `andreevBlockSum`, `q = 2 ^ r`, `v = N + k m / 4`
(`andreevVarianceProxy`).

**Lemma 6** (`sum_mul_andreevTableScore_eq_zero_of_odd`): for a uniform input, distinct sets
`S ≠ T` and functions `g h` on the integers with `g` odd, `𝔼[g(X_S) h(X_T)] = 0`. Translating the
table by a `u` with `(S Δ T) · u` odd and flipping it by `T · u` (`andreevTranslateTable`)
negates `X_S` and fixes `X_T` and the address. The general form
`sum_mul_andreevTableScore_eq_zero` lets `g` and `h` also depend on the address bits.

**Truncated vote.** The subcube vote `andreevSubcubeEval b m r` reads
`P_* = 2 ∑_{S ⊆ [r]} X_S (-1) ^ t_S` (`andreevSubcubeScore` is `P_* / 2`). With the centred
address count `D_S = t_S - ⌊|S| m / 2⌋` and `η_S = (-1) ^ ⌊|S| m / 2⌋`, every nonempty term is
`η_S (φ(X_S + D_S) + φ(X_S - D_S))` for `φ(u) = (-1) ^ u u` (`two_mul_andreevSubcubeScore_eq`).
Replacing `φ` by its truncation `f_R(u) = φ(u) [|u| ≤ R]` (`altLinearTrunc`, in `DepthTwo.lean`)
gives the truncated score `P_R` (`andreevTruncatedScore`) and the truncated vote
`andreevTruncatedVote`, which agrees with the subcube vote whenever `|P_R - P_*| < 2 q`
(`andreevTruncatedVote_eq_subcubeEval`). Each staircase of `f_R` has `2 R + 2` steps, so `P_R`
is a sum of `4 (q - 1) (R + 1)` threshold indicators of the reflected forms plus the affine term
`2 X_∅`; the circuit is built in a separate module.

**Error analysis.** For a fixed address, the error `e_S` of each set is odd in `X_S`, so Lemma 6
makes the errors orthogonal (`sum_andreevTruncationError_mul_eq_zero`,
`sum_sq_andreevTruncatedScore_sub_eq`). Each reflected form is a centred weighted bit sum with
squared weights at most `4 v`, shifted by at most `1 / 2` (`cast_andreevReflectedForm_eq`), so
Hoeffding's inequality and a discrete tail sum bound its truncated second moment
(`sum_sq_andreevReflectedForm_le`). Markov's inequality then bounds the disagreements between the
truncated vote and the subcube vote by
`2 ^ n · 2 (q - 1) / q² · ((R + 1)² + 8 v) exp (-(R + 1)² / (8 v))`
(`card_andreevTruncatedVote_ne_subcubeEval_le`), and by the preprint's
`2 ^ n (16 v / q) exp (-R² / (16 v))` (`card_andreevTruncatedVote_ne_subcubeEval_le_exp`).
The radius `R = ⌈4 √(v log (16 v / (q δ)))⌉` (`andreevTruncationRadius`) makes this at most `δ`.

## Main definitions

* `andreevTranslateTable`: the table translation and flip of Lemma 6.
* `andreevCentredBlockSum`, `andreevReflectedForm`, `andreevReflectionSign`: `D_S`, `X_S ± D_S`
  and `η_S`.
* `andreevTruncatedScore`, `andreevVoteThreshold`, `andreevTruncatedVote`: `P_R` and the
  truncated vote.
* `andreevTruncationError`: the error `e_S` of a set.
* `andreevVarianceProxy`, `andreevReflectedWeight`, `andreevTruncationRadius`: `v`, the weights
  of a reflected form, and the radius.

## Main results

* `sum_mul_andreevTableScore_eq_zero_of_odd`, `sum_mul_andreevTableScore_eq_zero`: Lemma 6.
* `andreevReflectionSign_mul_altLinear_add`, `two_mul_andreevSubcubeScore_eq`: the reflection
  identity.
* `sum_andreevTruncationError_mul_eq_zero`, `sum_sq_andreevTruncatedScore_sub_eq`: cancellation
  of cross terms.
* `card_le_natAbs_andreevReflectedForm_le`, `sum_sq_andreevReflectedForm_le`: Gaussian tails and
  the truncated second moment of a reflected form.
* `sum_sq_andreevTruncatedScore_sub_le`, `card_andreevTruncatedVote_ne_subcubeEval_le`,
  `card_andreevTruncatedVote_ne_subcubeEval_le_exp`: the disagreement bound.
* `card_andreevTruncatedVote_ne_andreev_le_of_radius`,
  `half_add_mul_le_card_andreevTruncatedVote_eq_andreev`: Parts 1 and 2 of Thm. 7 for the
  truncated vote: agreement `1 - δ` at `q = N`, and agreement `1 / 2 + ε` when
  `32 ε² N ≤ q < N`.

## Differences from the preprint

* The vote breaks ties towards `1` (`andreevSubcubeEval` is `P_* ≤ 0`), the preprint towards `0`;
  the agreement count is the same. The threshold is `2 q` for `q < N` and `0` for `q = N`, where
  `P_* = ±2 N`; the preprint's single gate `[-P_* ≥ 2 q]` fits only `q < N`.
* The preprint bounds the diagonal terms by `16 v exp (-R² / (16 v))` "integrating Hoeffding's tail
  from `R / 2`". That integration gives `(2 R² + 16 v) exp (-R² / (8 v))`, which exceeds
  `16 v exp (-R² / (16 v))` when `R² < 20 v` (roughly). Here the sharp form is kept, and the
  preprint's final bound follows for `(R + 1)² ≥ 32 v`; below that, `(16 v / q) exp (-R² / (16 v))`
  exceeds `1` and the bound is trivial.

## References

* C. Reitwiessner, *Depth-Two Threshold Circuits for Andreev's Function*, preprint (November
  2026), Lemma 6 (`lem:odd`) and Theorem 7 (`thm:avgupper`).
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.WeightedThreshold

open BitString Finset Real

/-! ### Table symmetries -/

private theorem add_add_cancel_right_bitString {b : ℕ} (c u : BitString b) : c + u + u = c := by
  funext j
  simp [Bool.add_eq_xor]

theorem andreevTranslateTableFun_involutive (b m : ℕ) (u : BitString b) (β : Bool) :
    Function.Involutive (andreevTranslateTableFun b m u β) := fun w => by
  funext i
  refine Fin.addCases (fun idx => ?_) (fun i => by simp [andreevTranslateTableFun]) i
  change andreevTranslateTableFun b m u β (andreevTranslateTableFun b m u β w)
    (andreevTableIndex b m idx) = w (andreevTableIndex b m idx)
  rw [andreevTranslateTableFun_tableIndex, andreevTranslateTableFun_tableIndex,
    Equiv.symm_apply_apply, add_add_cancel_right_bitString, Equiv.apply_symm_apply,
    Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The measure-preserving involution of the inputs that translates the truth table by `u`
(the bit at index `c` becomes the bit at `c + u`) and flips it when `β = true`, leaving the
address bits unchanged. -/
def andreevTranslateTable (b m : ℕ) (u : BitString b) (β : Bool) :
    Equiv.Perm (BitString (2 ^ b + b * m)) :=
  (andreevTranslateTableFun_involutive b m u β).toPerm

@[simp]
theorem andreevTranslateTable_apply (b m : ℕ) (u : BitString b) (β : Bool)
    (w : BitString (2 ^ b + b * m)) :
    andreevTranslateTable b m u β w = andreevTranslateTableFun b m u β w := rfl

/-- Translating the table by `u` and flipping it by `β` multiplies `X_S` by `(-1) ^ β χ_S(u)`. -/
theorem andreevTableScore_translateTable (b m : ℕ) (S : Finset (Fin b)) (u : BitString b)
    (β : Bool) (w : BitString (2 ^ b + b * m)) :
    andreevTableScore b m S (andreevTranslateTable b m u β w) =
      (-1) ^ β.toNat * chi ℤ S u * andreevTableScore b m S w := by
  have hxor (v : Bool) :
      (1 - 2 * ((xor v β).toNat : ℤ)) = (-1) ^ β.toNat * (1 - 2 * (v.toNat : ℤ)) := by
    cases v <;> cases β <;> rfl
  simp only [andreevTableScore, andreevTranslateTable_apply, andreevTable_translateTableFun, hxor,
    mul_sum]
  rw [← Equiv.sum_comp (Equiv.addRight u)]
  refine sum_congr rfl fun c _ => ?_
  simp only [Equiv.coe_addRight, add_add_cancel_right_bitString, chi_add]
  ring

/-- The address bits of an Andreev input, as a `b × m` array. -/
def andreevAddress (b m : ℕ) (w : BitString (2 ^ b + b * m)) : Fin b → Fin m → Bool :=
  fun j t => w (andreevBlockVar b m j t)

theorem andreevAddress_translateTable (b m : ℕ) (u : BitString b) (β : Bool)
    (w : BitString (2 ^ b + b * m)) :
    andreevAddress b m (andreevTranslateTable b m u β w) = andreevAddress b m w := by
  funext j t
  simp [andreevAddress]

/-! ### Lemma 6: odd errors are orthogonal -/

/-- **Odd errors are orthogonal** (preprint Lemma 6, general form). For distinct sets `S ≠ T`,
and functions `g h` of a table score and the address bits with `g` odd in the score,
`∑_w g(X_S(w), a(w)) h(X_T(w), a(w)) = 0`: some translation and flip of the table negates `X_S`
and fixes `X_T` and the address. -/
theorem sum_mul_andreevTableScore_eq_zero {b m : ℕ} {S T : Finset (Fin b)} (hST : S ≠ T)
    (g h : ℤ → (Fin b → Fin m → Bool) → ℝ) (hg : ∀ x a, g (-x) a = -g x a) :
    ∑ w : BitString (2 ^ b + b * m),
      g (andreevTableScore b m S w) (andreevAddress b m w) *
        h (andreevTableScore b m T w) (andreevAddress b m w) = 0 := by
  -- A coordinate `i` in exactly one of `S` and `T`, and the translation `u = e_i`.
  obtain ⟨i, hi⟩ : (symmDiff S T).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, ← bot_eq_empty, symmDiff_eq_bot]
    exact hST
  set u : BitString b := Function.update 0 i true
  have hu : chi ℤ S u * chi ℤ T u = -1 := by
    rw [chi_mul_chi, chi_update_of_mem hi, chi_zero]
    rfl
  -- Flip by the parity of `T` at `u`, so that `(-1) ^ β = χ_T(u)`.
  set β := parityOn T u
  have hβ : ((-1 : ℤ) ^ β.toNat) = chi ℤ T u := (chi_eq_neg_one_pow_parityOn T u).symm
  have hT1 : chi ℤ T u * chi ℤ T u = 1 := chi_mul_self T u
  set σ := andreevTranslateTable b m u β
  have hS (w) : andreevTableScore b m S (σ w) = -andreevTableScore b m S w := by
    rw [andreevTableScore_translateTable, hβ]
    linear_combination (andreevTableScore b m S w) * hu
  have hT (w) : andreevTableScore b m T (σ w) = andreevTableScore b m T w := by
    rw [andreevTableScore_translateTable, hβ, hT1, one_mul]
  set F : BitString (2 ^ b + b * m) → ℝ := fun w =>
    g (andreevTableScore b m S w) (andreevAddress b m w) *
      h (andreevTableScore b m T w) (andreevAddress b m w)
  have hF : ∑ w, F w = -∑ w, F w := by
    conv_lhs => rw [← Equiv.sum_comp σ]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun w _ => ?_
    simp only [F, hS, hT, σ, andreevAddress_translateTable, hg]
    ring
  change ∑ w, F w = 0
  linarith

/-- **Odd errors are orthogonal** (preprint Lemma 6). For a uniformly random input, distinct sets
`S ≠ T`, and functions `g h` on the integers with `g` odd, `𝔼[g(X_S) h(X_T)] = 0`. -/
theorem sum_mul_andreevTableScore_eq_zero_of_odd {b m : ℕ} {S T : Finset (Fin b)} (hST : S ≠ T)
    (g h : ℤ → ℝ) (hg : ∀ x, g (-x) = -g x) :
    ∑ w : BitString (2 ^ b + b * m),
      g (andreevTableScore b m S w) * h (andreevTableScore b m T w) = 0 :=
  sum_mul_andreevTableScore_eq_zero hST (fun x _ => g x) (fun x _ => h x) fun x _ => hg x

/-! ### Reflected forms and the truncated score -/

/-- The centred address count `D_S = t_S - ⌊|S| m / 2⌋` of the blocks in `S`. -/
def andreevCentredBlockSum (b m : ℕ) (S : Finset (Fin b)) (w : BitString (2 ^ b + b * m)) : ℤ :=
  andreevBlockSum b m S w - andreevWindowCenter m S

/-- The reflected forms `X_S + D_S` (`τ = true`) and `X_S - D_S` (`τ = false`). -/
def andreevReflectedForm (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (w : BitString (2 ^ b + b * m)) : ℤ :=
  if τ then andreevTableScore b m S w + andreevCentredBlockSum b m S w
  else andreevTableScore b m S w - andreevCentredBlockSum b m S w

/-- The sign `η_S = (-1) ^ ⌊|S| m / 2⌋` relating the reflected forms to `X_S (-1) ^ t_S`. -/
def andreevReflectionSign {b : ℕ} (m : ℕ) (S : Finset (Fin b)) : ℤ :=
  (andreevWindowCenter m S).negOnePow

private theorem altLinear_reflect {X D η c : ℤ} (hX : (X.negOnePow : ℤ) = 1)
    (hD : (D.negOnePow : ℤ) = η * c) (hη : η * η = 1) :
    η * (altLinear (X + D) + altLinear (X - D)) = 2 * X * c := by
  simp only [altLinear, Int.negOnePow_add,
    Int.negOnePow_sub, Units.val_mul, hX, hD]
  linear_combination (2 * X * c) * hη

/-- **Reflection identity** (preprint, proof of Thm. 7). For a nonempty set `S`,
`η_S (φ(X_S + D_S) + φ(X_S - D_S)) = 2 X_S (-1) ^ t_S`. -/
theorem andreevReflectionSign_mul_altLinear_add {b m : ℕ} {S : Finset (Fin b)} (hS : S.Nonempty)
    (w : BitString (2 ^ b + b * m)) :
    andreevReflectionSign m S *
        (altLinear (andreevReflectedForm b m S true w) +
          altLinear (andreevReflectedForm b m S false w)) =
      2 * andreevTableScore b m S w * chi ℤ S (andreevParities b m w) := by
  -- `X_S` is even, because `N = 2 ^ b` is even.
  have hb : b ≠ 0 := by
    rintro rfl
    exact hS.ne_empty (Subsingleton.elim _ _)
  have hX : ((andreevTableScore b m S w).negOnePow : ℤ) = 1 := by
    rw [negOnePow_andreevTableScore, (Nat.even_pow.mpr ⟨even_two, hb⟩).neg_one_pow]
  have hD : ((andreevCentredBlockSum b m S w).negOnePow : ℤ) =
      andreevReflectionSign m S * chi ℤ S (andreevParities b m w) := by
    rw [andreevReflectionSign, ← negOnePow_andreevBlockSum, andreevCentredBlockSum,
      Int.negOnePow_sub, Units.val_mul, mul_comm]
  have hη : andreevReflectionSign m S * andreevReflectionSign m S = 1 := by
    rw [andreevReflectionSign, ← Units.val_mul, Int.units_mul_self, Units.val_one]
  simp only [andreevReflectedForm, ↓reduceIte, Bool.false_eq_true]
  exact altLinear_reflect hX hD hη

/-- The prefix subsets other than `∅`. -/
def andreevPrefixSubsetsNonempty (b r : ℕ) : Finset (Finset (Fin b)) :=
  (andreevPrefixSubsets b r).erase ∅

theorem nonempty_of_mem_andreevPrefixSubsetsNonempty {b r : ℕ} {S : Finset (Fin b)}
    (hS : S ∈ andreevPrefixSubsetsNonempty b r) : S.Nonempty :=
  nonempty_iff_ne_empty.mpr (mem_erase.mp hS).1

theorem card_andreevPrefixSubsetsNonempty {b r : ℕ} (hr : r ≤ b) :
    #(andreevPrefixSubsetsNonempty b r) = 2 ^ r - 1 := by
  rw [andreevPrefixSubsetsNonempty, card_erase_of_mem (by simp), card_andreevPrefixSubsets hr]

/-- The doubled subcube vote score `P_* = 2 ∑_{S ⊆ [r]} X_S (-1) ^ t_S` in reflected form:
`P_* = 2 X_∅ + ∑_{∅ ≠ S ⊆ [r]} η_S (φ(X_S + D_S) + φ(X_S - D_S))`. -/
theorem two_mul_andreevSubcubeScore_eq (b m r : ℕ) (w : BitString (2 ^ b + b * m)) :
    2 * andreevSubcubeScore b m r w =
      2 * andreevTableScore b m ∅ w +
        ∑ S ∈ andreevPrefixSubsetsNonempty b r, andreevReflectionSign m S *
          (altLinear (andreevReflectedForm b m S true w) +
            altLinear (andreevReflectedForm b m S false w)) := by
  rw [andreevSubcubeScore, mul_sum, andreevPrefixSubsetsNonempty,
    ← add_sum_erase _ _ (show ∅ ∈ andreevPrefixSubsets b r by simp), chi_empty, mul_one]
  congr 1
  refine sum_congr rfl fun S hS => ?_
  rw [andreevReflectionSign_mul_altLinear_add (nonempty_iff_ne_empty.mpr (mem_erase.mp hS).1)]
  ring

/-- The truncated score `P_R`: `P_*` in reflected form with every `φ` replaced by `f_R`; the
affine term `2 X_∅` stays. -/
def andreevTruncatedScore (b m r R : ℕ) (w : BitString (2 ^ b + b * m)) : ℤ :=
  2 * andreevTableScore b m ∅ w +
    ∑ S ∈ andreevPrefixSubsetsNonempty b r, andreevReflectionSign m S *
      (altLinearTrunc R (andreevReflectedForm b m S true w) +
        altLinearTrunc R (andreevReflectedForm b m S false w))

/-- The threshold of the truncated vote: `2 q` for `q = 2 ^ r < N`, where `P_*` takes values in
`4 q ℤ`, and `0` for `q = N`, where `P_* = ±2 N`. -/
def andreevVoteThreshold (b r : ℕ) : ℤ :=
  if r < b then 2 * 2 ^ r else 0

/-- The truncated vote: `P_R` below the threshold `andreevVoteThreshold b r`. -/
def andreevTruncatedVote (b m r R : ℕ) (w : BitString (2 ^ b + b * m)) : Bool :=
  decide (andreevTruncatedScore b m r R w < andreevVoteThreshold b r)

/-- The truncated vote agrees with the subcube vote `andreevSubcubeEval` whenever `P_R` is within
`2 q` of `P_*`, since the values of `P_*` lie at distance at least `2 q` from the threshold. -/
theorem andreevTruncatedVote_eq_subcubeEval {b m r R : ℕ} (hr : r ≤ b)
    {w : BitString (2 ^ b + b * m)}
    (hw : |andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w| < 2 * 2 ^ r) :
    andreevTruncatedVote b m r R w = andreevSubcubeEval b m r w := by
  -- `P_* = 2 q s` with `s = L - 2 k`, where `L = 2 ^ (b - r)` and `0 ≤ k ≤ L`.
  set p := andreevParities b m w
  set k : ℤ := ∑ c ∈ andreevSubcube b r p, ((andreevTable b m w c).toNat : ℤ)
  have hk : 0 ≤ k ∧ k ≤ 2 ^ (b - r) := by
    refine ⟨sum_nonneg fun c _ => by positivity, ?_⟩
    calc k ≤ ∑ _c ∈ andreevSubcube b r p, (1 : ℤ) :=
          sum_le_sum fun c _ => by
            cases andreevTable b m w c <;> simp
      _ = 2 ^ (b - r) := by simp [card_andreevSubcube hr]
  have hscore : andreevSubcubeScore b m r w = 2 ^ r * (2 ^ (b - r) - 2 * k) := by
    rw [andreevSubcubeScore_eq_two_pow_mul_sum, card_andreevPrefixCoords hr, sum_sub_distrib,
      ← mul_sum, sum_const, card_andreevSubcube hr]
    simp [k, p]
  have hq : (0 : ℤ) < 2 ^ r := by positivity
  rw [andreevTruncatedVote, andreevSubcubeEval, hscore, andreevVoteThreshold]
  rw [hscore, abs_lt] at hw
  set s : ℤ := 2 ^ (b - r) - 2 * k with hsdef
  rcases hr.lt_or_eq with hrb | rfl
  · -- `L` is even, so `s` is even.
    have hL : (2 : ℤ) ^ (b - r) = 2 * 2 ^ (b - r - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ b - r)]
    simp only [hrb, ↓reduceIte]
    by_cases hs : s ≤ 0
    · have h1 : 2 ^ r * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hs
      simp only [h1, decide_true, decide_eq_true_eq]
      linarith
    · have hs2 : 2 ≤ s := by omega
      have : 2 * 2 ^ r ≤ 2 ^ r * s := by nlinarith
      have hnot : ¬ 2 ^ r * s ≤ 0 := by nlinarith
      simp only [hnot, decide_false, decide_eq_false_iff_not, not_lt]
      linarith
  · -- `L = 1`, so `s = ±1`.
    have hs : s = 1 ∨ s = -1 := by
      simp only [Nat.sub_self, pow_zero] at hsdef hk
      omega
    simp only [lt_irrefl, ↓reduceIte]
    rcases hs with h | h <;> rw [h] at hw ⊢
    · have : ¬ (2 : ℤ) ^ r * 1 ≤ 0 := by linarith
      simp only [this, decide_false, decide_eq_false_iff_not, not_lt]
      linarith
    · have : (2 : ℤ) ^ r * -1 ≤ 0 := by linarith
      simp only [this, decide_true, decide_eq_true_eq]
      linarith

/-! ### The truncation errors are orthogonal -/

/-- The truncation error `e_S = η_S ((f_R - φ)(X_S + D_S) + (f_R - φ)(X_S - D_S))` of a set `S`:
its term in `P_R` minus its term in `P_*`. -/
def andreevTruncationError (b m R : ℕ) (S : Finset (Fin b)) (w : BitString (2 ^ b + b * m)) : ℤ :=
  andreevReflectionSign m S *
    altLinearTruncErrorPair R (andreevTableScore b m S w) (andreevCentredBlockSum b m S w)

/-- `P_R - P_* = ∑_{∅ ≠ S ⊆ [r]} e_S`. -/
theorem andreevTruncatedScore_sub_eq_sum (b m r R : ℕ) (w : BitString (2 ^ b + b * m)) :
    andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w =
      ∑ S ∈ andreevPrefixSubsetsNonempty b r, andreevTruncationError b m R S w := by
  rw [two_mul_andreevSubcubeScore_eq, andreevTruncatedScore, add_sub_add_left_eq_sub,
    ← sum_sub_distrib]
  refine sum_congr rfl fun S _ => ?_
  simp only [andreevTruncationError, altLinearTruncErrorPair, andreevReflectedForm, ↓reduceIte,
    Bool.false_eq_true]
  ring

/-- **The truncation errors are orthogonal**: for distinct sets `S ≠ T`,
`∑_w e_S(w) e_T(w) = 0`. For a fixed address, `e_S` is an odd function of `X_S`, so this is
Lemma 6 (`sum_mul_andreevTableScore_eq_zero`). -/
theorem sum_andreevTruncationError_mul_eq_zero {b m R : ℕ} {S T : Finset (Fin b)}
    (hST : S ≠ T) :
    ∑ w : BitString (2 ^ b + b * m),
      (andreevTruncationError b m R S w : ℝ) * andreevTruncationError b m R T w = 0 := by
  -- `D_U` is a function of the address bits.
  let D (U : Finset (Fin b)) (a : Fin b → Fin m → Bool) : ℤ :=
    (∑ j ∈ U, ∑ t : Fin m, ((a j t).toNat : ℤ)) - andreevWindowCenter m U
  let g (U : Finset (Fin b)) (x : ℤ) (a : Fin b → Fin m → Bool) : ℝ :=
    ((andreevReflectionSign m U * altLinearTruncErrorPair R x (D U a) : ℤ) : ℝ)
  have hg (x : ℤ) (a : Fin b → Fin m → Bool) : g S (-x) a = -g S x a := by
    simp only [g, altLinearTruncErrorPair_neg]
    push_cast
    ring
  exact sum_mul_andreevTableScore_eq_zero hST (g S) (g T) hg

/-- **Cancellation of cross terms**: `∑_w (P_R - P_*)² = ∑_{∅ ≠ S ⊆ [r]} ∑_w e_S²`. -/
theorem sum_sq_andreevTruncatedScore_sub_eq (b m r R : ℕ) :
    ∑ w : BitString (2 ^ b + b * m),
      ((andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w : ℤ) : ℝ) ^ 2 =
      ∑ S ∈ andreevPrefixSubsetsNonempty b r, ∑ w : BitString (2 ^ b + b * m),
        (andreevTruncationError b m R S w : ℝ) ^ 2 := by
  simp_rw [andreevTruncatedScore_sub_eq_sum, Int.cast_sum, sq, sum_mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun S hS => ?_
  rw [sum_comm, sum_eq_single_of_mem S hS fun T _ hTS =>
    sum_andreevTruncationError_mul_eq_zero (Ne.symm hTS)]

/-! ### Diagonal terms: Hoeffding for the reflected forms -/

/-- The variance proxy `v = N + k m / 4` of the reflected forms. -/
noncomputable def andreevVarianceProxy (b m : ℕ) : ℝ :=
  2 ^ b + b * m / 4

theorem one_le_andreevVarianceProxy (b m : ℕ) : 1 ≤ andreevVarianceProxy b m := by
  unfold andreevVarianceProxy
  have : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  have : (0 : ℝ) ≤ b * m / 4 := by positivity
  linarith

/-- The real weights of the reflected form `X_S ± D_S` as a centred sum of the input bits:
`-2 χ_S(c)` on table bit `c`, and `±1` on the address bits of the blocks in `S`. -/
def andreevReflectedWeight (b m : ℕ) (S : Finset (Fin b)) (τ : Bool) :
    Fin (2 ^ b + b * m) → ℝ :=
  Fin.addCases (fun idx => -2 * chi ℝ S ((BitString.equivFin b).symm idx))
    (fun i => if (finProdFinEquiv.symm i).1 ∈ S then (if τ then 1 else -1) else 0)

/-- The reflected form `X_S ± D_S` is the centred weighted bit sum with weights
`andreevReflectedWeight`, shifted by `±(|S| m / 2 - ⌊|S| m / 2⌋)`. -/
theorem cast_andreevReflectedForm_eq (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    (w : BitString (2 ^ b + b * m)) :
    (andreevReflectedForm b m S τ w : ℝ) =
      ∑ i, andreevReflectedWeight b m S τ i * (((w i).toNat : ℝ) - 1 / 2) +
        (if τ then 1 else -1) * ((#S * m : ℝ) / 2 - andreevWindowCenter m S) := by
  have hX : (andreevTableScore b m S w : ℝ) = ∑ idx : Fin (2 ^ b),
      -2 * chi ℝ S ((BitString.equivFin b).symm idx) *
        (((w (Fin.castAdd (b * m) idx)).toNat : ℝ) - 1 / 2) := by
    rw [andreevTableScore, Int.cast_sum, ← (BitString.equivFin b).sum_comp]
    refine sum_congr rfl fun c _ => ?_
    simp only [Equiv.symm_apply_apply, andreevTable, andreevTableIndex, Int.cast_mul,
      Int.cast_sub, Int.cast_one, Int.cast_ofNat, Int.cast_natCast]
    rw [show ((chi ℤ S c : ℤ) : ℝ) = chi ℝ S c by simp [chi]]
    ring
  have ht : (andreevBlockSum b m S w : ℝ) - #S * m / 2 = ∑ i : Fin (b * m),
      (if (finProdFinEquiv.symm i).1 ∈ S then 1 else 0) *
        (((w (Fin.natAdd (2 ^ b) i)).toNat : ℝ) - 1 / 2) := by
    rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply, ite_mul, one_mul, zero_mul]
    simp only [sum_ite_irrel, sum_const_zero]
    rw [sum_ite_mem, univ_inter]
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      andreevBlockSum, Int.cast_sum, Int.cast_natCast, andreevBlockVar]
    ring
  rw [andreevReflectedForm, Fin.sum_univ_add]
  simp only [andreevReflectedWeight, Fin.addCases_left, Fin.addCases_right, ← hX]
  have hblock : ∑ i : Fin (b * m), (if (finProdFinEquiv.symm i).1 ∈ S then
      (if τ then 1 else -1 : ℝ) else 0) * (((w (Fin.natAdd (2 ^ b) i)).toNat : ℝ) - 1 / 2) =
      (if τ then 1 else -1) * ((andreevBlockSum b m S w : ℝ) - #S * m / 2) := by
    rw [ht, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  rw [hblock, andreevCentredBlockSum]
  cases τ <;> simp <;> ring

/-- The squared weights of a reflected form sum to between `4 N` and `4 v = 4 N + k m`. -/
theorem sum_andreevReflectedWeight_sq_mem (b m : ℕ) (S : Finset (Fin b)) (τ : Bool) :
    4 * 2 ^ b ≤ ∑ i, andreevReflectedWeight b m S τ i ^ 2 ∧
      ∑ i, andreevReflectedWeight b m S τ i ^ 2 ≤ 4 * andreevVarianceProxy b m := by
  have htable : ∑ idx : Fin (2 ^ b), (-2 * chi ℝ S ((BitString.equivFin b).symm idx)) ^ 2 =
      4 * 2 ^ b := by
    have h4 (x : BitString b) : (-2 * chi ℝ S x) ^ 2 = 4 := by
      rw [mul_pow, sq (chi ℝ S x), chi_mul_self]
      norm_num
    simp only [h4, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hblock (i : Fin (b * m)) :
      0 ≤ (if (finProdFinEquiv.symm i).1 ∈ S then (if τ then 1 else -1 : ℝ) else 0) ^ 2 ∧
        (if (finProdFinEquiv.symm i).1 ∈ S then (if τ then 1 else -1 : ℝ) else 0) ^ 2 ≤ 1 := by
    constructor
    · positivity
    · split_ifs <;> norm_num
  rw [Fin.sum_univ_add]
  simp only [andreevReflectedWeight, Fin.addCases_left, Fin.addCases_right, htable]
  constructor
  · linarith [sum_nonneg fun i (_ : i ∈ univ) => (hblock i).1]
  · have := sum_le_sum fun i (_ : i ∈ univ) => (hblock i).2
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    unfold andreevVarianceProxy
    push_cast at this ⊢
    linarith

/-- **Gaussian tails of a reflected form**: for every `j ≥ 1`, at most a
`2 exp (-j² / (8 v))` fraction of the inputs have `|X_S ± D_S| ≥ j`. -/
theorem card_le_natAbs_andreevReflectedForm_le (b m : ℕ) (S : Finset (Fin b)) (τ : Bool)
    {j : ℕ} (hj : 1 ≤ j) :
    (#{w : BitString (2 ^ b + b * m) | j ≤ (andreevReflectedForm b m S τ w).natAbs} : ℝ) ≤
      2 * 2 ^ (2 ^ b + b * m) * exp (-((j : ℝ) ^ 2 / (8 * andreevVarianceProxy b m))) := by
  set a := andreevReflectedWeight b m S τ
  set μ : ℝ := (if τ then 1 else -1) * ((#S * m : ℝ) / 2 - andreevWindowCenter m S)
  have hμ : |μ| ≤ 1 / 2 := by
    have h := sub_andreevWindowCenter_mem_Icc m S
    rw [abs_le]
    cases τ <;> simp only [μ, Bool.false_eq_true, ↓reduceIte] <;> constructor <;> linarith
  have hσ := sum_andreevReflectedWeight_sq_mem b m S τ
  have hpos : (0 : ℝ) < ∑ i, a i ^ 2 := lt_of_lt_of_le (by positivity) hσ.1
  have hsub : ({w : BitString (2 ^ b + b * m) | j ≤ (andreevReflectedForm b m S τ w).natAbs} :
      Finset _) ⊆
      ({w : BitString (2 ^ b + b * m) | (j : ℝ) / 2 ≤ |∑ i, a i * (((w i).toNat : ℝ) - 1 / 2)|} :
        Finset _) := by
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    have hU : (j : ℝ) ≤ |(andreevReflectedForm b m S τ w : ℝ)| := by
      rw [← Int.cast_abs, ← Nat.cast_natAbs]
      exact_mod_cast hw
    rw [cast_andreevReflectedForm_eq] at hU
    change (j : ℝ) ≤ |∑ i, a i * (((w i).toNat : ℝ) - 1 / 2) + μ| at hU
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have := abs_add_le (∑ i, a i * (((w i).toNat : ℝ) - 1 / 2)) μ
    linarith
  calc (#{w : BitString (2 ^ b + b * m) | j ≤ (andreevReflectedForm b m S τ w).natAbs} : ℝ)
      ≤ #{w : BitString (2 ^ b + b * m) |
          (j : ℝ) / 2 ≤ |∑ i, a i * (((w i).toNat : ℝ) - 1 / 2)|} := by
        exact_mod_cast card_le_card hsub
    _ ≤ 2 * 2 ^ Fintype.card (Fin (2 ^ b + b * m)) *
          exp (-(2 * ((j : ℝ) / 2) ^ 2 / ∑ i, a i ^ 2)) :=
        BitString.card_filter_le_abs_sum_mul_sub_half_le a (by positivity)
    _ ≤ 2 * 2 ^ (2 ^ b + b * m) * exp (-((j : ℝ) ^ 2 / (8 * andreevVarianceProxy b m))) := by
        rw [Fintype.card_fin]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [exp_le_exp, neg_le_neg_iff,
          show 2 * ((j : ℝ) / 2) ^ 2 / ∑ i, a i ^ 2 = (j : ℝ) ^ 2 / (2 * ∑ i, a i ^ 2) by
            field_simp]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hσ.2])

/-- **Truncated second moment of a reflected form** (preprint, proof of Thm. 7, "diagonal
terms"): `∑_w U² [|U| > R] ≤ 2 · 2 ^ n ((R + 1)² + 8 v) exp (-(R + 1)² / (8 v))` for
`U = X_S ± D_S`. -/
theorem sum_sq_andreevReflectedForm_le (b m R : ℕ) (S : Finset (Fin b)) (τ : Bool) :
    ∑ w : BitString (2 ^ b + b * m),
      (if R < (andreevReflectedForm b m S τ w).natAbs then
        (andreevReflectedForm b m S τ w : ℝ) ^ 2 else 0) ≤
      2 * 2 ^ (2 ^ b + b * m) * (((R : ℝ) + 1) ^ 2 + 8 * andreevVarianceProxy b m) *
        exp (-(((R : ℝ) + 1) ^ 2 / (8 * andreevVarianceProxy b m))) := by
  have hv := one_le_andreevVarianceProxy b m
  have h := sum_sq_ite_lt_le_of_tail (fun w => (andreevReflectedForm b m S τ w).natAbs) R
    (M := 2 * 2 ^ (2 ^ b + b * m)) (by positivity) fun j hj =>
      card_le_natAbs_andreevReflectedForm_le b m S τ (by omega)
  refine le_of_eq_of_le (sum_congr rfl fun w _ => ?_) h
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-! ### The disagreement bound -/

/-- `∑_w e_S² ≤ 8 · 2 ^ n ((R + 1)² + 8 v) exp (-(R + 1)² / (8 v))`. -/
theorem sum_sq_andreevTruncationError_le (b m R : ℕ) (S : Finset (Fin b)) :
    ∑ w : BitString (2 ^ b + b * m), (andreevTruncationError b m R S w : ℝ) ^ 2 ≤
      8 * 2 ^ (2 ^ b + b * m) * (((R : ℝ) + 1) ^ 2 + 8 * andreevVarianceProxy b m) *
        exp (-(((R : ℝ) + 1) ^ 2 / (8 * andreevVarianceProxy b m))) := by
  have hη : ((andreevReflectionSign m S : ℤ) : ℝ) ^ 2 = 1 := by
    rw [← Int.cast_pow, andreevReflectionSign, ← Units.val_pow_eq_pow_val, Int.units_sq,
      Units.val_one, Int.cast_one]
  have hterm (w : BitString (2 ^ b + b * m)) : (andreevTruncationError b m R S w : ℝ) ^ 2 ≤
      2 * (if R < (andreevReflectedForm b m S true w).natAbs then
        (andreevReflectedForm b m S true w : ℝ) ^ 2 else 0) +
      2 * (if R < (andreevReflectedForm b m S false w).natAbs then
        (andreevReflectedForm b m S false w : ℝ) ^ 2 else 0) := by
    rw [← sq_altLinearTrunc_sub_altLinear, ← sq_altLinearTrunc_sub_altLinear]
    simp only [andreevTruncationError, altLinearTruncErrorPair, andreevReflectedForm, ↓reduceIte,
      Bool.false_eq_true, Int.cast_mul, mul_pow, hη, one_mul, Int.cast_add]
    nlinarith [sq_nonneg (((altLinearTrunc R (andreevTableScore b m S w +
        andreevCentredBlockSum b m S w) - altLinear (andreevTableScore b m S w +
        andreevCentredBlockSum b m S w) : ℤ) : ℝ) - ((altLinearTrunc R
        (andreevTableScore b m S w - andreevCentredBlockSum b m S w) -
        altLinear (andreevTableScore b m S w - andreevCentredBlockSum b m S w) : ℤ) : ℝ))]
  refine (sum_le_sum fun w _ => hterm w).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  linarith [sum_sq_andreevReflectedForm_le b m R S true,
    sum_sq_andreevReflectedForm_le b m R S false]

/-- **Mean squared truncation error**: `∑_w (P_R - P_*)² ≤
8 (q - 1) 2 ^ n ((R + 1)² + 8 v) exp (-(R + 1)² / (8 v))` for `q = 2 ^ r`. -/
theorem sum_sq_andreevTruncatedScore_sub_le {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    ∑ w : BitString (2 ^ b + b * m),
      ((andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w : ℤ) : ℝ) ^ 2 ≤
      8 * ((2 : ℝ) ^ r - 1) * 2 ^ (2 ^ b + b * m) *
        (((R : ℝ) + 1) ^ 2 + 8 * andreevVarianceProxy b m) *
          exp (-(((R : ℝ) + 1) ^ 2 / (8 * andreevVarianceProxy b m))) := by
  rw [sum_sq_andreevTruncatedScore_sub_eq]
  refine (sum_le_sum fun S _ => sum_sq_andreevTruncationError_le b m R S).trans_eq ?_
  rw [sum_const, card_andreevPrefixSubsetsNonempty hr, nsmul_eq_mul,
    Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  ring

/-- **The truncated vote differs from the subcube vote on few inputs** (sharp form): on at most
`2 ^ n · 2 (q - 1) / q² · ((R + 1)² + 8 v) exp (-(R + 1)² / (8 v))` inputs, for `q = 2 ^ r`.
This is Markov's inequality for `(P_R - P_*)²`, since a disagreement needs `|P_R - P_*| ≥ 2 q`. -/
theorem card_andreevTruncatedVote_ne_subcubeEval_le {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    (#{w : BitString (2 ^ b + b * m) |
        andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} : ℝ) ≤
      2 ^ (2 ^ b + b * m) * (2 * ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ r) ^ 2 *
        (((R : ℝ) + 1) ^ 2 + 8 * andreevVarianceProxy b m) *
          exp (-(((R : ℝ) + 1) ^ 2 / (8 * andreevVarianceProxy b m)))) := by
  set d : BitString (2 ^ b + b * m) → ℝ := fun w =>
    ((andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w : ℤ) : ℝ)
  set bad := ({w : BitString (2 ^ b + b * m) |
    andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} : Finset _)
  have hbad (w) (hw : w ∈ bad) : (2 * (2 : ℝ) ^ r) ^ 2 ≤ d w ^ 2 := by
    simp only [bad, mem_filter, mem_univ, true_and] at hw
    have h : 2 * (2 : ℤ) ^ r ≤ |andreevTruncatedScore b m r R w - 2 * andreevSubcubeScore b m r w|
      := not_lt.mp fun h => hw (andreevTruncatedVote_eq_subcubeEval hr h)
    have h' : 2 * (2 : ℝ) ^ r ≤ |d w| := by
      simp only [d]
      rw [← Int.cast_abs]
      exact_mod_cast h
    rw [← sq_abs (d w)]
    exact pow_le_pow_left₀ (by positivity) h' 2
  have hmarkov : (#bad : ℝ) * (2 * (2 : ℝ) ^ r) ^ 2 ≤ ∑ w, d w ^ 2 := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact (sum_le_sum hbad).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun w _ _ => sq_nonneg _)
  have htotal := sum_sq_andreevTruncatedScore_sub_le hr m R
  have hq : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  rw [← le_div_iff₀ (by positivity)] at hmarkov
  refine hmarkov.trans ?_
  rw [div_le_iff₀ (by positivity)]
  refine htotal.trans_eq ?_
  field_simp
  ring

/-- `(2 z + 1) exp (-2 z) ≤ exp (-z)` for `z ≥ 2`. -/
private theorem two_mul_add_one_mul_exp_neg_le {z : ℝ} (hz : 2 ≤ z) :
    (2 * z + 1) * exp (-(2 * z)) ≤ exp (-z) := by
  have h := quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ z)
  have h2 : 2 * z + 1 ≤ exp z := by nlinarith
  calc (2 * z + 1) * exp (-(2 * z)) ≤ exp z * exp (-(2 * z)) :=
        mul_le_mul_of_nonneg_right h2 (exp_pos _).le
    _ = exp (-z) := by rw [← exp_add]; ring_nf

/-- **The truncated vote differs from the subcube vote on few inputs** (preprint, proof of
Thm. 7): on at most a `(16 v / q) exp (-R² / (16 v))` fraction of the inputs, for `q = 2 ^ r` and
`v = N + k m / 4`. -/
theorem card_andreevTruncatedVote_ne_subcubeEval_le_exp {b r : ℕ} (hr : r ≤ b) (m R : ℕ) :
    (#{w : BitString (2 ^ b + b * m) |
        andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} : ℝ) ≤
      2 ^ (2 ^ b + b * m) * (16 * andreevVarianceProxy b m / 2 ^ r *
        exp (-((R : ℝ) ^ 2 / (16 * andreevVarianceProxy b m)))) := by
  set v := andreevVarianceProxy b m
  have hv : 1 ≤ v := one_le_andreevVarianceProxy b m
  have hq : (0 : ℝ) < 2 ^ r := by positivity
  have hqv : (2 : ℝ) ^ r ≤ v := by
    have : (2 : ℝ) ^ r ≤ 2 ^ b := pow_le_pow_right₀ (by norm_num) hr
    have : (0 : ℝ) ≤ b * m / 4 := by positivity
    simp only [v, andreevVarianceProxy]
    linarith
  have hn : (0 : ℝ) < 2 ^ (2 ^ b + b * m) := by positivity
  by_cases hR : 32 * v ≤ ((R : ℝ) + 1) ^ 2
  · -- Large radius: the sharp form, with `z = (R + 1)² / (16 v) ≥ 2`.
    set z := ((R : ℝ) + 1) ^ 2 / (16 * v)
    have hz : 2 ≤ z := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hzR : (R : ℝ) ^ 2 / (16 * v) ≤ z :=
      div_le_div_of_nonneg_right (by nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)])
        (by positivity)
    refine (card_andreevTruncatedVote_ne_subcubeEval_le hr m R).trans
      (mul_le_mul_of_nonneg_left ?_ hn.le)
    have hsharp : ((R : ℝ) + 1) ^ 2 + 8 * v = 8 * v * (2 * z + 1) := by
      simp only [z]
      field_simp
      ring
    have hexp : ((R : ℝ) + 1) ^ 2 / (8 * v) = 2 * z := by
      simp only [z]
      field_simp
      ring
    rw [hsharp, hexp]
    have h1 := two_mul_add_one_mul_exp_neg_le hz
    have h2 : exp (-z) ≤ exp (-((R : ℝ) ^ 2 / (16 * v))) := exp_le_exp.mpr (by linarith)
    have h3 : 2 * ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ r) ^ 2 ≤ 2 / 2 ^ r := by
      rw [div_le_div_iff₀ (by positivity) hq]
      nlinarith
    calc 2 * ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ r) ^ 2 * (8 * v * (2 * z + 1)) * exp (-(2 * z))
        = 2 * ((2 : ℝ) ^ r - 1) / ((2 : ℝ) ^ r) ^ 2 * (8 * v) *
            ((2 * z + 1) * exp (-(2 * z))) := by ring
      _ ≤ 2 / 2 ^ r * (8 * v) * exp (-((R : ℝ) ^ 2 / (16 * v))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h3 (by positivity)) (h1.trans h2)
            (mul_nonneg (by linarith) (exp_pos _).le) (by positivity)
      _ = 16 * v / 2 ^ r * exp (-((R : ℝ) ^ 2 / (16 * v))) := by ring
  · -- Small radius: the bound is at least `16 e⁻² 2 ^ n ≥ 2 ^ n`.
    have hall : (#{w : BitString (2 ^ b + b * m) |
        andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} : ℝ) ≤
        2 ^ (2 ^ b + b * m) := by
      exact_mod_cast (card_filter_le _ _).trans_eq (by simp)
    refine hall.trans (le_mul_of_one_le_right hn.le ?_)
    have hR2 : (R : ℝ) ^ 2 / (16 * v) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
    -- `exp (-2) = exp (-1 / 2) ^ 4 ≥ (1 / 2) ^ 4`.
    have he2 : 1 ≤ 16 * exp (-2) := by
      have h := add_one_le_exp (-1 / 2 : ℝ)
      have h4 : exp (-2) = exp (-1 / 2) ^ 4 := by
        rw [← exp_nat_mul]
        norm_num
      rw [h4]
      have : (1 / 2 : ℝ) ^ 4 ≤ exp (-1 / 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      linarith
    have h16 : 16 ≤ 16 * v / 2 ^ r := by
      rw [le_div_iff₀ hq]
      linarith
    have hexp : exp (-2) ≤ exp (-((R : ℝ) ^ 2 / (16 * v))) := exp_le_exp.mpr (by linarith)
    calc (1 : ℝ) ≤ 16 * exp (-2) := he2
      _ ≤ 16 * v / 2 ^ r * exp (-((R : ℝ) ^ 2 / (16 * v))) := by
          gcongr

/-! ### Agreement with Andreev's function -/

/-- **Part 1 of Thm. 7 at the level of the vote** (`q = N`): the truncated vote at `r = k`
differs from `andreev b m` on at most a `(16 v / N) exp (-R² / (16 v))` fraction of the inputs. -/
theorem card_andreevTruncatedVote_ne_andreev_le (b m R : ℕ) :
    (#{w : BitString (2 ^ b + b * m) | andreevTruncatedVote b m b R w ≠ andreev b m w} : ℝ) ≤
      2 ^ (2 ^ b + b * m) * (16 * andreevVarianceProxy b m / 2 ^ b *
        exp (-((R : ℝ) ^ 2 / (16 * andreevVarianceProxy b m)))) := by
  simpa only [andreevSubcubeEval_self] using
    card_andreevTruncatedVote_ne_subcubeEval_le_exp le_rfl m R

/-- **Part 2 of Thm. 7 at the level of the vote** (`q < N`): the truncated vote agrees with
`andreev b m` on at least a `1 / 2 + 1 / (2 √(2 L)) - (16 v / q) exp (-R² / (16 v))` fraction of
the inputs, for `q = 2 ^ r` and `L = N / q`. -/
theorem two_pow_mul_sub_le_card_andreevTruncatedVote_eq_andreev {b r : ℕ} (hr : r < b)
    (m R : ℕ) :
    (2 ^ (2 ^ b + b * m) : ℝ) * (1 / 2 + 1 / (2 * Real.sqrt (2 * 2 ^ (b - r))) -
        16 * andreevVarianceProxy b m / 2 ^ r *
          exp (-((R : ℝ) ^ 2 / (16 * andreevVarianceProxy b m)))) ≤
      (#{w : BitString (2 ^ b + b * m) | andreevTruncatedVote b m r R w = andreev b m w} : ℝ) := by
  have hvote := two_pow_mul_le_card_andreevSubcubeEval_eq_andreev hr m
  have hne := card_andreevTruncatedVote_ne_subcubeEval_le_exp hr.le m R
  have hsplit : #{w : BitString (2 ^ b + b * m) | andreevSubcubeEval b m r w = andreev b m w} ≤
      #{w : BitString (2 ^ b + b * m) | andreevTruncatedVote b m r R w = andreev b m w} +
        #{w : BitString (2 ^ b + b * m) |
          andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} := by
    refine (card_le_card fun w hw => ?_).trans (card_union_le _ _)
    simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
    by_cases h : andreevTruncatedVote b m r R w = andreevSubcubeEval b m r w
    · exact Or.inl (h.trans hw)
    · exact Or.inr h
  have hsplit' : (#{w : BitString (2 ^ b + b * m) |
      andreevSubcubeEval b m r w = andreev b m w} : ℝ) ≤
      #{w : BitString (2 ^ b + b * m) | andreevTruncatedVote b m r R w = andreev b m w} +
        #{w : BitString (2 ^ b + b * m) |
          andreevTruncatedVote b m r R w ≠ andreevSubcubeEval b m r w} := by
    exact_mod_cast hsplit
  nlinarith

/-! ### Choosing the radius -/

/-- The radius `R = ⌈4 √(v log (16 v / (q δ)))⌉` for `q = 2 ^ r`, which makes the truncation lose
at most a `δ` fraction (`andreevTruncationRadius_spec`). -/
noncomputable def andreevTruncationRadius (b m r : ℕ) (δ : ℝ) : ℕ :=
  ⌈4 * Real.sqrt (andreevVarianceProxy b m *
    Real.log (16 * andreevVarianceProxy b m / (2 ^ r * δ)))⌉₊

/-- With the radius `andreevTruncationRadius b m r δ`, the truncation loss
`(16 v / q) exp (-R² / (16 v))` is at most `δ`. -/
theorem andreevTruncationRadius_spec (b m r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    16 * andreevVarianceProxy b m / 2 ^ r *
        exp (-((andreevTruncationRadius b m r δ : ℝ) ^ 2 / (16 * andreevVarianceProxy b m))) ≤
      δ := by
  set v := andreevVarianceProxy b m
  set R := andreevTruncationRadius b m r δ
  have hv : 0 < v := lt_of_lt_of_le one_pos (one_le_andreevVarianceProxy b m)
  have hq : (0 : ℝ) < 2 ^ r := by positivity
  set L := Real.log (16 * v / (2 ^ r * δ))
  have hratio : 0 < 16 * v / (2 ^ r * δ) := by positivity
  rcases le_or_gt L 0 with hL | hL
  · -- `16 v / (q δ) ≤ 1`.
    have h1 : 16 * v / (2 ^ r * δ) ≤ 1 := by
      have := Real.exp_le_exp.mpr hL
      rwa [Real.exp_log hratio, exp_zero] at this
    have h2 : 16 * v / 2 ^ r ≤ δ := by
      rw [div_le_one (by positivity)] at h1
      rw [div_le_iff₀ hq]
      linarith
    have h3 : exp (-((R : ℝ) ^ 2 / (16 * v))) ≤ 1 := by
      rw [exp_le_one_iff, neg_nonpos]
      positivity
    calc 16 * v / 2 ^ r * exp (-((R : ℝ) ^ 2 / (16 * v))) ≤ 16 * v / 2 ^ r * 1 := by gcongr
      _ ≤ δ := by linarith
  · -- `R² ≥ 16 v L`.
    have hR : 4 * Real.sqrt (v * L) ≤ R := Nat.le_ceil _
    have hR2 : 16 * (v * L) ≤ (R : ℝ) ^ 2 := by
      have h0 : 0 ≤ 4 * Real.sqrt (v * L) := by positivity
      have := pow_le_pow_left₀ h0 hR 2
      rw [mul_pow, Real.sq_sqrt (by positivity)] at this
      linarith
    have hexp : exp (-((R : ℝ) ^ 2 / (16 * v))) ≤ exp (-L) := by
      rw [exp_le_exp, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      linarith
    have hL' : exp (-L) = 2 ^ r * δ / (16 * v) := by
      rw [exp_neg, Real.exp_log hratio, inv_div]
    rw [hL'] at hexp
    calc 16 * v / 2 ^ r * exp (-((R : ℝ) ^ 2 / (16 * v)))
        ≤ 16 * v / 2 ^ r * (2 ^ r * δ / (16 * v)) := by gcongr
      _ = δ := by field_simp

/-- **Part 1 of Thm. 7 at the level of the vote**: with the radius
`R = andreevTruncationRadius b m b δ`, the truncated vote at `r = k` differs from `andreev b m` on
at most a `δ` fraction of the inputs. -/
theorem card_andreevTruncatedVote_ne_andreev_le_of_radius (b m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (#{w : BitString (2 ^ b + b * m) |
        andreevTruncatedVote b m b (andreevTruncationRadius b m b δ) w ≠ andreev b m w} : ℝ) ≤
      δ * 2 ^ (2 ^ b + b * m) := by
  refine (card_andreevTruncatedVote_ne_andreev_le b m _).trans ?_
  rw [mul_comm δ]
  exact mul_le_mul_of_nonneg_left (andreevTruncationRadius_spec b m b hδ) (by positivity)

/-- **Part 2 of Thm. 7 at the level of the vote**: if `32 ε² N ≤ q = 2 ^ r < N` and `ε > 0`, then
with the radius `R = andreevTruncationRadius b m r ε` the truncated vote agrees with `andreev b m`
on at least a `1 / 2 + ε` fraction of the inputs: the vote's advantage is at least `2 ε`, and
truncation loses at most `ε`. -/
theorem half_add_mul_le_card_andreevTruncatedVote_eq_andreev {b r : ℕ} (hr : r < b) (m : ℕ)
    {ε : ℝ} (hε : 0 < ε) (hq : 32 * ε ^ 2 * 2 ^ b ≤ 2 ^ r) :
    (1 / 2 + ε) * 2 ^ (2 ^ b + b * m) ≤
      (#{w : BitString (2 ^ b + b * m) |
        andreevTruncatedVote b m r (andreevTruncationRadius b m r ε) w = andreev b m w} : ℝ) := by
  refine le_trans ?_ (two_pow_mul_sub_le_card_andreevTruncatedVote_eq_andreev hr m _)
  have hloss := andreevTruncationRadius_spec b m r hε
  -- The vote's advantage `1 / (2 √(2 L))` is at least `2 ε`.
  set t := Real.sqrt (2 * 2 ^ (b - r))
  have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have hpow : (2 : ℝ) ^ (b - r) * 2 ^ r = 2 ^ b := by
    rw [← pow_add, Nat.sub_add_cancel hr.le]
  have ht2 : t ^ 2 = 2 * 2 ^ (b - r) := Real.sq_sqrt (by positivity)
  have h4 : 4 * ε * t ≤ 1 := by
    have h16 : (4 * ε * t) ^ 2 ≤ 1 := by
      have hr0 : (0 : ℝ) < 2 ^ r := by positivity
      rw [mul_pow, ht2]
      have : 16 * ε ^ 2 * (2 * 2 ^ (b - r)) * 2 ^ r ≤ 1 * 2 ^ r := by nlinarith
      nlinarith
    nlinarith [mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hε) ht]
  have hadv : 2 * ε ≤ 1 / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hn : (0 : ℝ) < 2 ^ (2 ^ b + b * m) := by positivity
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (by linarith) hn.le

end Cslib.Circuits.Boolean.WeightedThreshold
