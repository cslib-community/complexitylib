/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardCore
public import CslibFrontier.Foundations.Data.BitString.Block
public import CslibFrontier.Foundations.Data.BitString.Parity
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Circuit.Boolean.Substitution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Yao's XOR lemma

The `k`-fold XOR of a Boolean function `f` on `n` bits is the function
`f^{⊕k}(x_1, …, x_k) = f(x_1) ⊕ ⋯ ⊕ f(x_k)` on `k` blocks of `n` bits (`xorPower`). **Yao's XOR
lemma** [Yao1982] says that XOR amplifies hardness: if every small circuit errs on a `δ` fraction
of the inputs of `f`, then somewhat smaller circuits agree with `f^{⊕k}` on at most a
`1 / 2 + ε + (1 - δ) ^ k` fraction of its inputs.

We derive it from Impagliazzo's hard-core lemma (`Cslib.Circuits.Boolean.exists_isHardCoreMeasure`)
as in [Impagliazzo1995]. Write each input weight as `1 = M x + (1 - M x)` for a hard-core measure
`M` of density `δ`. Expanding the first block, the part weighted by `M` is a prediction of `f` on
the mass of `M` by a circuit with the other blocks fixed, which agrees with `f` on at most a
`1 / 2 + ε` fraction; the part weighted by `1 - M` has mass at most `(1 - δ) 2 ^ n` and is handled
by induction on the remaining blocks. This purely combinatorial step holds for any function all of
whose single-block restrictions are hard on `M`, over any finite set of inputs
(`card_eq_sum_le`): the agreement is at most `(1 / 2 + ε) N ^ k + (1 / 2 - ε) (N - μ) ^ k` for `N`
inputs and a measure of mass `μ`. Fixing all blocks but one costs two gates for the constants
(`Cslib.Circuits.Boolean.complexity_substitute_le`) and complementing costs one, so a hard-core
measure against size `s + 3` controls all circuits of size `s` (`card_eq_xorPower_div_le`).

Everything is nonuniform, over De Morgan circuits with sizes as in `Cslib.Circuits.complexity`.

## Main definitions

* `Cslib.Circuits.Boolean.xorPower`: the `k`-fold XOR `f^{⊕k}` of a Boolean function.

## Main results

* `Cslib.Circuits.Boolean.card_eq_sum_le`: the XOR lemma for a measure, over any finite set.
* `Cslib.Circuits.Boolean.IsHardCoreMeasure.card_eq_xorPower_div_le`: a hard-core measure of
  density `δ` against size `s + 3` bounds the agreement of circuits of size `s` with `f^{⊕k}` by
  `1 / 2 + ε + (1 / 2 - ε) (1 - δ) ^ k`.
* `Cslib.Circuits.Boolean.card_eq_xorPower_div_le`: **Yao's XOR lemma** with explicit parameters.

## References

* [A. C. Yao, *Theory and applications of trapdoor functions*][Yao1982]
* [R. Impagliazzo, *Hard-core distributions for somewhat hard problems*][Impagliazzo1995]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset Function

variable {n : ℕ}

/-- The `k`-fold XOR `f^{⊕k}` of a Boolean function `f` on `n` bits: on `k` blocks of `n` bits
(`Cslib.BitString.block`), the parity of the values of `f` on the blocks. -/
def xorPower (f : BooleanFunction n) (k : ℕ) : BooleanFunction (k * n) :=
  fun x => parity k fun i => f (BitString.block x i)

/-- The `k`-fold XOR is the sum of the values on the blocks in the Boolean ring `Bool`. -/
theorem xorPower_apply (f : BooleanFunction n) (k : ℕ) (x : BitString (k * n)) :
    xorPower f k x = ∑ i, f (BitString.block x i) :=
  parityOn_eq_sum _ _

/-- In the Boolean ring, `a = b + c` exactly when `a ^^ c = b`. -/
private theorem eq_add_iff_xor_eq (a b c : Bool) : a = b + c ↔ (a ^^ c) = b := by
  cases a <;> cases b <;> cases c <;> decide

/-- In the Boolean ring, `a = b + c` exactly when `a ^^ b = c`. -/
private theorem eq_add_iff_xor_eq' (a b c : Bool) : a = b + c ↔ (a ^^ b) = c := by
  cases a <;> cases b <;> cases c <;> decide

/-- **The XOR lemma for a measure.** Let `M` be a measure with weights in `[0, 1]` on a finite
set `X` of `N` inputs, with mass `μ`, and let `G` be a function of `k` inputs all of whose
single-input restrictions, complemented or not, agree with `f` on at most a `1 / 2 + ε` fraction
of the mass of `M`. Then `G` agrees with `f(x_1) ⊕ ⋯ ⊕ f(x_k)` on at most
`(1 / 2 + ε) N ^ k + (1 / 2 - ε) (N - μ) ^ k` of the `N ^ k` tuples. -/
theorem card_eq_sum_le {X : Type*} [Fintype X] (f : X → Bool) {M : X → ℝ}
    (hM : ∀ x, M x ∈ Set.Icc (0 : ℝ) 1) {ε : ℝ} :
    ∀ (k : ℕ) (G : (Fin k → X) → Bool),
      (∀ (i : Fin k) (t : Fin k → X) (b : Bool),
        ∑ y with (G (update t i y) ^^ b) = f y, M y ≤ (1 / 2 + ε) * ∑ y, M y) →
      (#{t | G t = ∑ i, f (t i)} : ℝ) ≤
        (1 / 2 + ε) * Fintype.card X ^ k + (1 / 2 - ε) * (Fintype.card X - ∑ y, M y) ^ k
  | 0, G, _ => by
    have h : (#{t : Fin 0 → X | G t = ∑ i, f (t i)} : ℝ) ≤ 1 := by
      exact_mod_cast (card_filter_le _ _).trans (by simp)
    linarith
  | k + 1, G, hG => by
    rcases isEmpty_or_nonempty X with hX | ⟨⟨z⟩⟩
    · simp
    -- Split off the first input.
    set A : X → (Fin k → X) → ℝ := fun y t =>
      if G (Fin.cons y t) = f y + ∑ i, f (t i) then 1 else 0 with hA
    have hsplit : (#{t | G t = ∑ i, f (t i)} : ℝ) = ∑ y, ∑ t, A y t := by
      rw [natCast_card_filter, ← Fintype.sum_prod_type',
        ← (Fin.consEquiv fun _ : Fin (k + 1) => X).sum_comp]
      refine sum_congr rfl fun p _ => ?_
      simp [A, Fin.consEquiv, Fin.sum_univ_succ]
    -- The part weighted by `M`: a prediction of `f` with the other inputs fixed.
    have hhard (t : Fin k → X) : ∑ y, M y * A y t ≤ (1 / 2 + ε) * ∑ y, M y := by
      refine le_of_eq_of_le ?_ (hG 0 (Fin.cons z t) (∑ i, f (t i)))
      rw [sum_filter]
      refine sum_congr rfl fun y _ => ?_
      rw [Fin.update_cons_zero, hA, mul_ite, mul_one, mul_zero]
      exact if_congr (eq_add_iff_xor_eq _ _ _) rfl rfl
    -- The part weighted by `1 - M`: the remaining inputs, by induction.
    set B := (1 / 2 + ε) * (Fintype.card X : ℝ) ^ k +
      (1 / 2 - ε) * (Fintype.card X - ∑ y, M y) ^ k
    have hrest (y : X) : (1 - M y) * ∑ t, A y t ≤ (1 - M y) * B := by
      refine mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 (hM y).2)
      have h := card_eq_sum_le f hM k (fun t => G (Fin.cons y t) ^^ f y) fun i t b => by
        simpa only [Fin.cons_update, Bool.xor_assoc] using hG i.succ (Fin.cons y t) (f y ^^ b)
      refine le_of_eq_of_le ?_ h
      rw [natCast_card_filter]
      exact sum_congr rfl fun t _ => if_congr (eq_add_iff_xor_eq' _ _ _) rfl rfl
    calc (#{t | G t = ∑ i, f (t i)} : ℝ)
        = ∑ y, (M y * ∑ t, A y t + (1 - M y) * ∑ t, A y t) := by
          rw [hsplit]
          exact sum_congr rfl fun y _ => by ring
      _ = ∑ t, ∑ y, M y * A y t + ∑ y, (1 - M y) * ∑ t, A y t := by
          rw [sum_add_distrib]
          simp only [mul_sum]
          rw [sum_comm]
      _ ≤ ∑ _t : Fin k → X, (1 / 2 + ε) * ∑ y, M y + ∑ y, (1 - M y) * B :=
          add_le_add (sum_le_sum fun t _ => hhard t) (sum_le_sum fun y _ => hrest y)
      _ = (1 / 2 + ε) * Fintype.card X ^ (k + 1) +
            (1 / 2 - ε) * (Fintype.card X - ∑ y, M y) ^ (k + 1) := by
          rw [← sum_mul, ← sum_mul, sum_sub_distrib]
          simp only [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul,
            mul_one, B]
          push_cast
          ring

/-- **A hard-core measure makes the XOR hard.** If `M` is a hard-core measure of density `δ` for
`f` against circuits of size `s + 3` with advantage `ε ≤ 1 / 2`, then every Boolean function of
De Morgan circuit complexity at most `s` agrees with the `k`-fold XOR `f^{⊕k}` on at most a
`1 / 2 + ε + (1 / 2 - ε) (1 - δ) ^ k` fraction of its inputs. -/
theorem IsHardCoreMeasure.card_eq_xorPower_div_le {f : BooleanFunction n} {s : ℕ} {δ ε : ℝ}
    {M : BitString n → ℝ} (hM : IsHardCoreMeasure f (s + 3) δ ε M) (hε : ε ≤ 1 / 2) (k : ℕ)
    {g : BooleanFunction (k * n)} (hg : complexity interpretation (single g) ≤ s) :
    (#{x | g x = xorPower f k x} : ℝ) / 2 ^ (k * n) ≤ 1 / 2 + ε + (1 / 2 - ε) * (1 - δ) ^ k := by
  let G : (Fin k → BitString n) → Bool := fun t => g (BitString.blocksEquiv.symm t)
  have hcard : #{x | g x = xorPower f k x} = #{t | G t = ∑ i, f (t i)} :=
    card_equiv BitString.blocksEquiv fun x => by
      simp only [mem_filter, mem_univ, true_and, G, Equiv.symm_apply_apply, xorPower_apply]
      rfl
  -- Every single-block restriction, complemented or not, costs at most three more gates.
  have hG (i : Fin k) (t : Fin k → BitString n) (b : Bool) :
      ∑ y with (G (update t i y) ^^ b) = f y, M y ≤ (1 / 2 + ε) * ∑ y, M y := by
    refine hM.sum_agree_le _ ?_
    let ρ : Fin (k * n) → Fin n ⊕ Bool := fun p =>
      if (finProdFinEquiv.symm p).1 = i then .inl (finProdFinEquiv.symm p).2
      else .inr (t (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2)
    have hρ (y : BitString n) : BitString.blocksEquiv.symm (update t i y) = substitute ρ y := by
      funext p
      simp only [BitString.blocksEquiv_symm_apply, substitute, ρ]
      split_ifs with h
      · rw [h, update_self]
        rfl
      · rw [update_of_ne h]
        rfl
    have hrestrict : complexity interpretation (single fun y => G (update t i y)) ≤ s + 2 := by
      simp only [G, hρ]
      exact (complexity_substitute_le ρ g).trans (by omega)
    cases b
    · simpa only [Bool.xor_false] using hrestrict.trans (Nat.le_succ _)
    · simpa only [Bool.xor_true] using
        (complexity_not_le _).trans (Nat.add_le_add_right hrestrict 1)
  have hbound := card_eq_sum_le f hM.mem_Icc k G hG
  rw [← hcard, BitString.card] at hbound
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hμ := hM.sum_le
  have hδμ := hM.mul_two_pow_le_sum
  have hpow : ((2 : ℝ) ^ n - ∑ y, M y) ^ k ≤ ((1 - δ) * 2 ^ n) ^ k :=
    pow_le_pow_left₀ (sub_nonneg.2 hμ) (by linarith) k
  rw [show (2 : ℝ) ^ (k * n) = ((2 : ℝ) ^ n) ^ k by rw [mul_comm, pow_mul],
    div_le_iff₀ (by positivity)]
  push_cast at hbound
  calc (#{x | g x = xorPower f k x} : ℝ)
      ≤ (1 / 2 + ε) * ((2 : ℝ) ^ n) ^ k + (1 / 2 - ε) * ((2 : ℝ) ^ n - ∑ y, M y) ^ k := hbound
    _ ≤ (1 / 2 + ε) * ((2 : ℝ) ^ n) ^ k + (1 / 2 - ε) * ((1 - δ) * 2 ^ n) ^ k := by
        linarith [mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ 1 / 2 - ε)]
    _ = (1 / 2 + ε + (1 / 2 - ε) * (1 - δ) ^ k) * ((2 : ℝ) ^ n) ^ k := by
        rw [mul_pow]
        ring

/-- **Yao's XOR lemma** [Yao1982], derived from Impagliazzo's hard-core lemma [Impagliazzo1995],
with explicit parameters. Let `0 < δ`, `0 < ε ≤ 1 / 2`, and let `T` be a number of rounds with
`1 ≤ 3 ε² δ² T`. If every Boolean function of De Morgan circuit complexity at most
`T (s + 3) + (2 + T (2 (T + 2)))` agrees with `f` on at most a `1 - δ` fraction of the inputs,
then every Boolean function of complexity at most `s` agrees with the `k`-fold XOR `f^{⊕k}` on at
most a `1 / 2 + ε + (1 / 2 - ε) (1 - δ) ^ k` fraction of its inputs. -/
theorem card_eq_xorPower_div_le {f : BooleanFunction n} {s T : ℕ} {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T)
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ T * (s + 3) + (2 + T * (2 * (T + 2))) →
        (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ)
    (k : ℕ) {g : BooleanFunction (k * n)} (hg : complexity interpretation (single g) ≤ s) :
    (#{x | g x = xorPower f k x} : ℝ) / 2 ^ (k * n) ≤ 1 / 2 + ε + (1 / 2 - ε) * (1 - δ) ^ k := by
  obtain ⟨M, hM⟩ := exists_isHardCoreMeasure hδ hε hT hf
  exact hM.card_eq_xorPower_div_le hε' k hg

end Cslib.Circuits.Boolean
