/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.PairwiseIndependentHash.Affine
public import Complexity.Probability.PairwiseIndependentHash.Retention
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Retention channels over a prime field

A *retention channel* selects a random set of identifiers at a prescribed rate, with pairwise
independence. Its seed is an affine map `y ↦ A y + b` from `𝔽_P` to `𝔽_P ^ H`, with a uniformly
random matrix `A` and vector `b`. The identifier `y : ZMod P` is *retained*
(`affineRetains P H L s y`) when every coordinate of `A y + b`, read as a number in
`{0, …, P - 1}`, is less than `L`. The target is then the box `retentionBox P H L` with `L ^ H`
points (`card_retentionBox`). By the pairwise independence of affine hashing
(`isPairwiseIndependentHash_affineHash`) and the general retention bounds of
`Complexity.Probability.PairwiseIndependentHash.Retention`, every identifier is retained with
probability exactly `π = (L / P) ^ H`, and two distinct identifiers both with probability `π ^ 2`.
This is sampling by pairwise independent hashing [ChorGoldreich1989] with the hash families of
Carter and Wegman [CarterWegman1979].

For a target rate `f = a ^ H` with `1 ≤ P a` and `a ≤ 1`, the side `L = ⌈P a⌉` gives
`f ≤ π ≤ 2 ^ H f` (`affineRetains_rates`). Then the conditional probability that `w` is
retained, given that `y ≠ w` is retained, is at most `2 ^ H f`. A deterministic nonempty set `A`
retains fewer than `#A π / 2` of its identifiers with probability at most `4 / (#A π)`. Two
channels with independent seeds, on the product seed space, give independent events
(`dens_filter_fst_and_snd`).

These are the channel properties used in Section 4 of the unrefereed preprint
[OpenAI2026LogSpace]: there, `c_π f ≤ π_f ≤ C_π f`,
`Pr[Y(w) | Y(y)] ≤ C_pair f`, the lower tail `Pr[∑_{x ∈ A} X(x) < |A| π / 2] ≤ C_var / (|A| π)`,
and the independence of the channels `X` and `Y`. Here the constants are `c_π = 1`,
`C_π = C_pair = 2 ^ H` and `C_var = 4`. The preprint conditions its channels on linearly
independent frames, which changes these constants only by a bounded factor. The frames matter
only for the later averaging walks, so they are not needed here.

## Main definitions

* `Cslib.Probability.retentionBox`: the box `{v | ∀ j, (v j).val < L}` in `ZMod P ^ H`.
* `Cslib.Probability.affineRetains`: the identifier `y` is retained by the affine seed `s`.

## Main results

* `Cslib.Probability.card_retentionBox`: the box has `L ^ H` points.
* `Cslib.Probability.dens_affineRetains`, `Cslib.Probability.dens_affineRetains_and`: exact
  retention probabilities of one identifier and of two distinct ones.
* `Cslib.Probability.dens_two_mul_card_filter_affineRetains_lt_le`: the lower tail of the number
  of retained identifiers of a set.
* `Cslib.Probability.dens_filter_fst_and_snd`: events about independent seeds are independent.
* `Cslib.Probability.affineRetains_rates`: the four channel properties at rate `f = a ^ H`.

## References

* [B. Chor, O. Goldreich, *On the power of two-point based sampling*][ChorGoldreich1989]
* [J. L. Carter, M. N. Wegman, *Universal classes of hash functions*][CarterWegman1979]
* [OpenAI, *Exact Derandomization of Logarithmic Space*][OpenAI2026LogSpace]
-/

public section

namespace Cslib.Probability

open Finset
open scoped BigOperators

/-- **Independence of separate seeds**: on the product of two seed spaces, an event about the
first seed and an event about the second have probability equal to the product of their
probabilities. -/
theorem dens_filter_fst_and_snd {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → Prop)
    (q : κ → Prop) [DecidablePred p] [DecidablePred q] :
    dens {z : ι × κ | p z.1 ∧ q z.2} = dens {i | p i} * dens {j | q j} := by
  rw [dens_eq_card_div_card, dens_eq_card_div_card, dens_eq_card_div_card,
    ← univ_product_univ, filter_product, card_product, Fintype.card_prod]
  push_cast
  rw [mul_div_mul_comm]

variable (P H L : ℕ) [NeZero P]

/-- The **retention box** `{v | ∀ j, (v j).val < L}` in `ZMod P ^ H`: every coordinate, read as
a number in `{0, …, P - 1}`, is less than `L`. -/
def retentionBox : Finset (Fin H → ZMod P) :=
  Fintype.piFinset fun _ ↦ {a : ZMod P | a.val < L}

variable {P H L}

/-- `L` residues of `ZMod P` have representatives less than `L ≤ P`. -/
private theorem card_filter_val_lt (hL : L ≤ P) : #{a : ZMod P | a.val < L} = L := by
  have himage : ({a : ZMod P | a.val < L} : Finset (ZMod P)).image ZMod.val = range L := by
    ext k
    simp only [mem_image, mem_filter, mem_univ, true_and, mem_range]
    refine ⟨fun ⟨a, ha, hak⟩ ↦ hak ▸ ha, fun hk ↦ ⟨k, ?_, ?_⟩⟩ <;>
      rw [ZMod.val_cast_of_lt (by omega)]
    exact hk
  calc #({a : ZMod P | a.val < L} : Finset (ZMod P))
      = #(({a : ZMod P | a.val < L} : Finset (ZMod P)).image ZMod.val) :=
        (card_image_of_injective _ (ZMod.val_injective P)).symm
    _ = L := by rw [himage, card_range]

/-- The retention box has `L ^ H` points when `L ≤ P`. -/
theorem card_retentionBox (hL : L ≤ P) : #(retentionBox P H L) = L ^ H := by
  rw [retentionBox, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
    card_filter_val_lt hL]

variable (P H L)

/-- The identifier `y` is **retained** by the affine seed `s = (A, b)` when `A y + b` lies in the
retention box. -/
abbrev affineRetains (s : Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P)) (y : ZMod P) :
    Prop :=
  affineHash s (fun _ ↦ y) ∈ retentionBox P H L

variable {P H L} [Fact P.Prime]

/-- The affine hash of identifiers is pairwise independent. -/
private theorem isPairwiseIndependentHash_affineIdentifier :
    IsPairwiseIndependentHash fun (s : Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P))
      (y : ZMod P) ↦ affineHash s (fun _ ↦ y) :=
  isPairwiseIndependentHash_affineHash.comp (e := fun y _ ↦ y) fun _ _ h ↦ congrFun h 0

/-- **Retention probability**: every identifier is retained with probability `(L / P) ^ H`. -/
theorem dens_affineRetains (hL : L ≤ P) (y : ZMod P) :
    dens {s | affineRetains P H L s y} = ((L : ℚ≥0) / P) ^ H := by
  have h := isPairwiseIndependentHash_affineIdentifier.dens_filter_apply_mem y
    (retentionBox P H L)
  rw [card_retentionBox hL, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  unfold affineRetains
  rw [h, div_pow]
  push_cast
  rfl

/-- **Pairwise independent retention**: two distinct identifiers are both retained with
probability `((L / P) ^ H) ^ 2`. -/
theorem dens_affineRetains_and (hL : L ≤ P) {w y : ZMod P} (hwy : w ≠ y) :
    dens {s | affineRetains P H L s w ∧ affineRetains P H L s y} =
      ((L : ℚ≥0) / P) ^ H * ((L : ℚ≥0) / P) ^ H := by
  have h := isPairwiseIndependentHash_affineIdentifier.dens_filter_apply_mem_and_apply_mem hwy
    (retentionBox P H L) (retentionBox P H L)
  rw [card_retentionBox hL, Fintype.card_fun, Fintype.card_fin, ZMod.card] at h
  unfold affineRetains
  rw [h, div_pow]
  push_cast
  rfl

/-- **Lower tail of the retained count**: a set `A` of identifiers retains fewer than half of its
expected number `#A π`, with `π = (L / P) ^ H`, with probability at most `4 / (#A π)`. -/
theorem dens_two_mul_card_filter_affineRetains_lt_le (hL : L ≤ P) (A : Finset (ZMod P))
    (hpos : 0 < (#A : ℝ) * ((L : ℝ) / P) ^ H) :
    (dens {s | 2 * (#{y ∈ A | affineRetains P H L s y} : ℝ) < #A * ((L : ℝ) / P) ^ H} : ℝ) ≤
      4 / (#A * ((L : ℝ) / P) ^ H) := by
  have hrate : ((#(retentionBox P H L) : ℝ) / Fintype.card (Fin H → ZMod P)) =
      ((L : ℝ) / P) ^ H := by
    rw [card_retentionBox hL, Fintype.card_fun, Fintype.card_fin, ZMod.card, div_pow]
    push_cast
    rfl
  have h := isPairwiseIndependentHash_affineIdentifier.dens_two_mul_card_filter_apply_mem_lt_le
    (𝕜 := ℝ) A (retentionBox P H L) (by rwa [hrate])
  rw [hrate] at h
  exact h

/-- **The four channel properties at rate `f = a ^ H`.** Let `1 ≤ P a`, `a ≤ 1` and
`L = ⌈P a⌉`, and write `π = (L / P) ^ H` for the retention probability. Then `L ≤ P`,
`f ≤ π ≤ 2 ^ H f`, two distinct identifiers are both retained with probability at most
`2 ^ H f` times the probability that one of them is, and a nonempty set `A` retains fewer than
`#A π / 2` of its identifiers with probability at most `4 / (#A π)`. Independence of two channels
is `dens_filter_fst_and_snd`. -/
theorem affineRetains_rates {a : ℝ} (hPa : 1 ≤ P * a) (ha : a ≤ 1) :
    let L := ⌈P * a⌉₊
    L ≤ P ∧ a ^ H ≤ ((L : ℝ) / P) ^ H ∧ ((L : ℝ) / P) ^ H ≤ 2 ^ H * a ^ H ∧
      (∀ w y : ZMod P, w ≠ y →
        (dens {s | affineRetains P H L s w ∧ affineRetains P H L s y} : ℝ) ≤
          2 ^ H * a ^ H * dens {s | affineRetains P H L s y}) ∧
      ∀ A : Finset (ZMod P), A.Nonempty →
        (dens {s | 2 * (#{y ∈ A | affineRetains P H L s y} : ℝ) < #A * ((L : ℝ) / P) ^ H} :
            ℝ) ≤ 4 / (#A * ((L : ℝ) / P) ^ H) := by
  intro L
  have hP : (0 : ℝ) < P := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne P)
  have ha0 : 0 < a := by
    by_contra h
    have := mul_nonpos_of_nonneg_of_nonpos hP.le (not_lt.1 h)
    linarith
  have hLlo : (P : ℝ) * a ≤ L := Nat.le_ceil _
  have hLhi : (L : ℝ) ≤ 2 * (P * a) := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ P * a)
    linarith
  have hLP : L ≤ P := Nat.ceil_le.2 (by nlinarith)
  have hlo : a ≤ (L : ℝ) / P := by
    rw [le_div_iff₀ hP]
    linarith
  have hhi : (L : ℝ) / P ≤ 2 * a := by
    rw [div_le_iff₀ hP]
    linarith
  have hrate_hi : ((L : ℝ) / P) ^ H ≤ 2 ^ H * a ^ H := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hhi H
  refine ⟨hLP, pow_le_pow_left₀ ha0.le hlo H, hrate_hi, fun w y hwy ↦ ?_, fun A hA ↦ ?_⟩
  · rw [dens_affineRetains_and hLP hwy, dens_affineRetains hLP]
    push_cast
    exact mul_le_mul_of_nonneg_right hrate_hi (by positivity)
  · refine dens_two_mul_card_filter_affineRetains_lt_le hLP A ?_
    have : (0 : ℝ) < #A := by exact_mod_cast hA.card_pos
    have : 0 < (L : ℝ) / P := ha0.trans_le hlo
    positivity

end Cslib.Probability
