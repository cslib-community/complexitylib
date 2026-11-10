/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AtLeast
public import CslibFrontier.Computability.Circuit.Boolean.Synthesis
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Potential
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Impagliazzo's hard-core lemma

A *measure* on the inputs of a Boolean function `f` on `n` bits is a weight `M x ∈ [0, 1]` for
each input; its *density* is its total mass divided by `2 ^ n`. A function `g` agrees with `f` on
a `p` fraction of the mass of `M` when `∑ x with g x = f x, M x = p ∑ x, M x`. A
*hard-core measure* of density `δ` for `f` against circuits of size `s` with advantage `ε`
(`IsHardCoreMeasure`) is a measure of density at least `δ` on whose mass every Boolean function
of De Morgan circuit complexity at most `s` agrees with `f` on at most a `1 / 2 + ε` fraction.

**Impagliazzo's hard-core lemma** [Impagliazzo1995] says that a function which every small
circuit gets wrong on a `δ` fraction of the inputs has a hard-core measure of density `δ` on
which somewhat smaller circuits barely beat a coin flip (`exists_isHardCoreMeasure`). Precisely,
let `T` be a number of rounds with `3 ε² δ² T ≥ 1`. If every function of complexity at most
`T s + 2 + 2 T (T + 2)` agrees with `f` on at most a `1 - δ` fraction of the inputs, then `f`
has a hard-core measure of density `δ` against circuits of size `s` with advantage `ε`. So
hardness for size `S ≥ 2 + 2 T (T + 2)` gives a hard-core measure against size
`(S - 2 - 2 T (T + 2)) / T` (`exists_isHardCoreMeasure_of_le`): for `T = ⌈1 / (3 ε² δ²)⌉` the
size shrinks by a factor polynomial in `1 / ε` and `1 / δ` and by an additive `O(T)`,
independently of `n`.

The proof is Impagliazzo's boosting argument with the clipped linear weights of
`Cslib.Crypto.Pseudoentropy.Boosting.weight`, at rate `ε δ`. If no hard-core measure exists, a
small circuit `g_j` beats the measure `M_j(x) = weight (ε δ) (N_j x)` built from the margin
`N_j x = #{l < j | g_l x = f x} - #{l < j | g_l x ≠ f x}` of the previous circuits, as long as
`M_j` has density at least `δ`. Each such round gains at least `2 ε δ 2 ^ n` in the correlation
`∑ x, M_j x (±1)`, while the potential `Cslib.Crypto.Pseudoentropy.Boosting.potential` caps the
total gain over `T` rounds at `2 ^ n (1 / (2 ε δ) + T ε δ / 2)`. So within `T` rounds some
`M_j` has density less than `δ`; the strict majority of `g_0, …, g_{j-1}` is then correct on
every input of positive margin, and the inputs of nonpositive margin have weight `1`, so it errs
on fewer than `δ 2 ^ n` inputs. The majority costs at most `T s` gates for the votes and
`2 + 2 T (T + 2)` for strict majority (`Cslib.Circuits.Boolean.complexity_threshold_le`).

Everything is nonuniform: the circuits are arbitrary De Morgan circuits, sizes are counted as in
`Cslib.Circuits.complexity`, and nothing is claimed about constructing them.

## Main definitions

* `Cslib.Circuits.Boolean.IsHardCoreMeasure`: a hard-core measure of density `δ` against
  circuits of size `s` with advantage `ε`.

## Main results

* `Cslib.Circuits.Boolean.exists_isHardCoreMeasure`: Impagliazzo's hard-core lemma, with the
  size loss `s ↦ T s + 2 + 2 T (T + 2)` for any `T` with `3 ε² δ² T ≥ 1`.
* `Cslib.Circuits.Boolean.exists_isHardCoreMeasure_of_le`: the same, from hardness for a given
  size `S`.

## References

* [R. Impagliazzo, *Hard-core distributions for somewhat hard problems*][Impagliazzo1995]
* [T. Holenstein, *Key agreement from weak bit agreement*][Holenstein2005], Section 2.2
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- A *hard-core measure* `M` of density `δ` for `f` against circuits of size `s` with advantage
`ε` [Impagliazzo1995]: its weights lie in `[0, 1]`, its total mass is at least `δ 2 ^ n`, and every
Boolean function of De Morgan circuit complexity at most `s` agrees with `f` on at most a
`1 / 2 + ε` fraction of its mass. -/
structure IsHardCoreMeasure (f : BooleanFunction n) (s : ℕ) (δ ε : ℝ) (M : BitString n → ℝ) :
    Prop where
  /-- Every weight is a probability. -/
  mem_Icc : ∀ x, M x ∈ Set.Icc (0 : ℝ) 1
  /-- The measure has density at least `δ`. -/
  mul_two_pow_le_sum : δ * 2 ^ n ≤ ∑ x, M x
  /-- Every function computed with at most `s` gates agrees with `f` on at most a `1 / 2 + ε`
  fraction of the mass. -/
  sum_agree_le : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ s →
    ∑ x with g x = f x, M x ≤ (1 / 2 + ε) * ∑ x, M x

/-- The total mass of a measure is at most the number of inputs. -/
theorem IsHardCoreMeasure.sum_le {f : BooleanFunction n} {s : ℕ} {δ ε : ℝ}
    {M : BitString n → ℝ} (hM : IsHardCoreMeasure f s δ ε M) : ∑ x, M x ≤ 2 ^ n := by
  calc ∑ x, M x ≤ ∑ _x : BitString n, (1 : ℝ) := sum_le_sum fun x _ => (hM.mem_Icc x).2
    _ = 2 ^ n := by simp

section Boosting

open Cslib.Crypto.Pseudoentropy.Boosting

variable (f : BooleanFunction n)

/-- The vote of a predictor `g` on `x`: `1` if it agrees with `f` there and `-1` otherwise. -/
private def vote (g : BooleanFunction n) (x : BitString n) : ℝ := if g x = f x then 1 else -1

private theorem vote_sq (g : BooleanFunction n) (x : BitString n) : vote f g x ^ 2 = 1 := by
  unfold vote
  split_ifs <;> norm_num

/-- The correlation of a predictor with `f` under weights `w` is twice its agreement minus the
mass. -/
private theorem sum_mul_vote (w : BitString n → ℝ) (g : BooleanFunction n) :
    ∑ x, w x * vote f g x = 2 * ∑ x with g x = f x, w x - ∑ x, w x := by
  have hsplit := sum_filter_add_sum_filter_not univ (fun x => g x = f x) w
  have hvote : ∑ x, w x * vote f g x =
      ∑ x with g x = f x, w x - ∑ x with ¬g x = f x, w x := by
    simp only [vote, mul_ite, mul_one, mul_neg, sum_ite, sum_neg_distrib, sub_eq_add_neg]
  linarith

/-- With `±1` votes, the sum of the votes is the number of votes minus twice the number of
votes against. -/
private theorem sum_ite_eq {j : ℕ} (v : Fin j → Bool) (b : Bool) :
    ∑ l, (if v l = b then (1 : ℝ) else -1) = j - 2 * #{l | v l ≠ b} := by
  have hsplit := card_filter_add_card_filter_not (s := univ) fun l => v l = b
  simp only [card_univ, Fintype.card_fin] at hsplit
  have hsplit' : (#{l | v l = b} : ℝ) + #{l | ¬v l = b} = j := by exact_mod_cast hsplit
  rw [sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
  change (#{l | v l = b} : ℝ) * 1 + #{l | ¬v l = b} * -1 = j - 2 * #{l | ¬v l = b}
  linarith

/-- The margins of the boosting loop when each round's predictor is chosen by `next` from the
current margins: the margin of `x` after `j` rounds is the number of the first `j` predictors
that agree with `f` on `x` minus the number that do not. -/
private def margin (next : (BitString n → ℝ) → BooleanFunction n) :
    ℕ → BitString n → ℝ
  | 0 => 0
  | j + 1 => fun x => margin next j x + vote f (next (margin next j)) x

variable {f}

/-- The margin is the sum of the votes of the predictors chosen so far. -/
private theorem margin_eq_sum (next : (BitString n → ℝ) → BooleanFunction n) (j : ℕ)
    (x : BitString n) :
    margin f next j x = ∑ l : Fin j, vote f (next (margin f next l)) x := by
  induction j with
  | zero => simp [margin]
  | succ j ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, ← ih]
    rfl

/-- **Telescoping the potential.** On each input, the weighted votes of the first `j` rounds sum
to at most `1 / (2 r) + j r / 2` at rate `r > 0`. -/
private theorem sum_weight_mul_vote_le {rate : ℝ} (hrate : 0 < rate)
    (next : (BitString n → ℝ) → BooleanFunction n) (x : BitString n) (j : ℕ) :
    ∑ l ∈ range j, weight rate (margin f next l x) * vote f (next (margin f next l)) x ≤
      1 / (2 * rate) + j * (rate / 2) := by
  suffices h : ∑ l ∈ range j, weight rate (margin f next l x) *
      vote f (next (margin f next l)) x ≤
        1 / (2 * rate) - potential rate (margin f next j x) + j * (rate / 2) by
    linarith [potential_nonneg hrate (margin f next j x)]
  induction j with
  | zero =>
    simp only [range_zero, sum_empty, Nat.cast_zero, zero_mul, add_zero]
    rw [show margin f next 0 x = 0 from rfl, potential_of_nonpos rate le_rfl]
    linarith
  | succ j ih =>
    rw [sum_range_succ]
    have hq := potential_le_quadratic hrate (margin f next j x) (margin f next (j + 1) x)
    have hstep : margin f next (j + 1) x - margin f next j x =
        vote f (next (margin f next j)) x := by
      simp only [margin]
      ring
    rw [hstep, vote_sq] at hq
    push_cast
    linarith

end Boosting

open Cslib.Crypto.Pseudoentropy.Boosting

/-- **Impagliazzo's hard-core lemma** [Impagliazzo1995], with explicit parameters. Let
`0 < δ`, `0 < ε`, and let `T` be a number of rounds with `1 ≤ 3 ε² δ² T`. If every Boolean
function of De Morgan circuit complexity at most `T s + (2 + T (2 (T + 2)))` agrees with `f` on at
most a `1 - δ` fraction of the inputs, then `f` has a hard-core measure of density `δ` against
circuits of size `s` with advantage `ε`: a measure `M` with weights in `[0, 1]` and mass at least
`δ 2 ^ n` on whose mass every function of complexity at most `s` agrees with `f` on at most a
`1 / 2 + ε` fraction. -/
theorem exists_isHardCoreMeasure {f : BooleanFunction n} {s T : ℕ} {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T)
    (hf : ∀ g : BooleanFunction n,
      complexity interpretation (single g) ≤ T * s + (2 + T * (2 * (T + 2))) →
        (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ) :
    ∃ M, IsHardCoreMeasure f s δ ε M := by
  by_contra hno
  set rate := ε * δ with hrate_def
  have hrate : 0 < rate := mul_pos hε hδ
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  -- Against every dense measure of clipped weights some small predictor has advantage `ε`.
  have key (N : BitString n → ℝ) : ∃ g : BooleanFunction n,
      δ * 2 ^ n ≤ ∑ x, weight rate (N x) →
        complexity interpretation (single g) ≤ s ∧
          (1 / 2 + ε) * ∑ x, weight rate (N x) < ∑ x with g x = f x, weight rate (N x) := by
    by_cases hd : δ * 2 ^ n ≤ ∑ x, weight rate (N x)
    · by_contra! hall
      exact hno ⟨fun x => weight rate (N x),
        ⟨fun x => weight_mem_Icc rate (N x), hd, fun g hg => (hall g).2 hg⟩⟩
    · exact ⟨fun _ => false, fun h => absurd h hd⟩
  choose next hnext using key
  let dense (j : ℕ) : Prop := δ * 2 ^ n ≤ ∑ x, weight rate (margin f next j x)
  -- Within `T` rounds the measure stops being dense.
  have hex : ∃ j, j < T ∧ ¬dense j := by
    by_contra! hall
    have hT1 : 0 < T := Nat.pos_of_ne_zero fun h => by norm_num [h] at hT
    have hT' : 1 ≤ 3 * rate ^ 2 * T := by grind
    -- Each dense round gains more than `2 ε δ 2 ^ n` in correlation.
    have hround (j : ℕ) (hj : j ∈ range T) : 2 * rate * 2 ^ n <
        ∑ x, weight rate (margin f next j x) * vote f (next (margin f next j)) x := by
      have hd := hall j (mem_range.1 hj)
      have hgood := (hnext (margin f next j) hd).2
      rw [sum_mul_vote, hrate_def]
      nlinarith
    have hlower := sum_lt_sum_of_nonempty (nonempty_range_iff.2 hT1.ne') hround
    rw [sum_comm] at hlower
    -- The potential caps the total correlation.
    have hupper : ∑ x : BitString n, ∑ j ∈ range T,
        weight rate (margin f next j x) * vote f (next (margin f next j)) x ≤
          ∑ _x : BitString n, (1 / (2 * rate) + T * (rate / 2)) :=
      sum_le_sum fun x _ => sum_weight_mul_vote_le hrate next x T
    simp only [sum_const, card_range, card_univ, BitString.card, nsmul_eq_mul] at hlower hupper
    push_cast at hlower hupper
    have h1 : T * (2 * rate) < 1 / (2 * rate) + T * (rate / 2) :=
      lt_of_mul_lt_mul_right (by linarith [hlower.trans_le hupper]) hN.le
    have h2 := mul_lt_mul_of_pos_right h1 (by positivity : (0 : ℝ) < 2 * rate)
    rw [add_mul, one_div_mul_cancel (by positivity : (2 * rate) ≠ 0)] at h2
    nlinarith
  classical
  obtain ⟨j₁, hj₁T, hj₁⟩ := hex
  let j := Nat.find (⟨j₁, hj₁⟩ : ∃ j, ¬dense j)
  have hjT : j < T := (Nat.find_min' _ hj₁).trans_lt hj₁T
  have hjsparse : ¬dense j := Nat.find_spec (⟨j₁, hj₁⟩ : ∃ j, ¬dense j)
  have hdense (l : ℕ) (hl : l < j) : dense l := by
    by_contra h
    exact Nat.find_min _ hl h
  -- The strict majority of the first `j` predictors.
  let g : BooleanFunction n := fun x => strictMajority j fun l : Fin j => next (margin f next l) x
  have hcomplexity : complexity interpretation (single g) ≤ T * s + (2 + T * (2 * (T + 2))) := by
    have h : complexity interpretation (single g) ≤
        ∑ l : Fin j, complexity interpretation (single (next (margin f next l))) +
          complexity interpretation (single (strictMajority j)) :=
      (complexity_comp_le (fun x (l : Fin j) => next (margin f next l) x)
        (single (strictMajority j))).trans
        (Nat.add_le_add_right (complexity_pi_le fun l : Fin j => next (margin f next l)) _)
    have hsum : ∑ l : Fin j, complexity interpretation (single (next (margin f next l))) ≤
        ∑ _l : Fin j, s :=
      sum_le_sum fun l _ => (hnext (margin f next l) (hdense l l.2)).1
    simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
    have hmaj : complexity interpretation (single (strictMajority j)) ≤
        2 + j * (2 * (j + 2)) := complexity_threshold_le j (j / 2 + 1)
    have hjT' := hjT.le
    have : j * s + (2 + j * (2 * (j + 2))) ≤ T * s + (2 + T * (2 * (T + 2))) := by
      gcongr
    omega
  -- Where the majority errs, the margin is nonpositive.
  have herr (x : BitString n) (hx : g x ≠ f x) : margin f next j x ≤ 0 := by
    have hcount := le_card_ne_of_strictMajority_ne hx
    have hcount' : (j : ℝ) ≤ 2 * #{l : Fin j | next (margin f next l) x ≠ f x} := by
      exact_mod_cast (show j ≤ 2 * #{l : Fin j | next (margin f next l) x ≠ f x} by omega)
    rw [margin_eq_sum]
    simp only [vote]
    rw [sum_ite_eq (fun l : Fin j => next (margin f next l) x) (f x)]
    linarith
  -- So the majority errs on fewer than `δ 2 ^ n` inputs.
  have hfew : (#{x | g x ≠ f x} : ℝ) < δ * 2 ^ n := by
    calc (#{x | g x ≠ f x} : ℝ) = ∑ x with g x ≠ f x, (1 : ℝ) := by simp
      _ = ∑ x with g x ≠ f x, weight rate (margin f next j x) :=
          sum_congr rfl fun x hx => (weight_of_nonpos hrate.le (herr x (mem_filter.1 hx).2)).symm
      _ ≤ ∑ x, weight rate (margin f next j x) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun x _ _ => (weight_mem_Icc rate _).1
      _ < δ * 2 ^ n := not_le.1 hjsparse
  have hsplit := card_filter_add_card_filter_not (s := univ) fun x => g x = f x
  simp only [card_univ, BitString.card] at hsplit
  have hsplit' : (#{x | g x = f x} : ℝ) + #{x | g x ≠ f x} = 2 ^ n := by exact_mod_cast hsplit
  have hbound := hf g hcomplexity
  rw [div_le_iff₀ hN] at hbound
  linarith

/-- **Impagliazzo's hard-core lemma** [Impagliazzo1995] from hardness for a given size. Let
`0 < δ`, `0 < ε`, let `T` be a number of rounds with `1 ≤ 3 ε² δ² T`, and let
`2 + T (2 (T + 2)) ≤ S`. If every Boolean function of De Morgan circuit complexity at most `S`
agrees with `f` on at most a `1 - δ` fraction of the inputs, then `f` has a hard-core measure of
density `δ` against circuits of size `(S - (2 + T (2 (T + 2)))) / T` with advantage `ε`. -/
theorem exists_isHardCoreMeasure_of_le {f : BooleanFunction n} {S T : ℕ} {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hT : 1 ≤ 3 * ε ^ 2 * δ ^ 2 * T) (hS : 2 + T * (2 * (T + 2)) ≤ S)
    (hf : ∀ g : BooleanFunction n, complexity interpretation (single g) ≤ S →
      (#{x | g x = f x} : ℝ) / 2 ^ n ≤ 1 - δ) :
    ∃ M, IsHardCoreMeasure f ((S - (2 + T * (2 * (T + 2)))) / T) δ ε M :=
  exists_isHardCoreMeasure hδ hε hT fun g hg => hf g <| by
    have h₁ := Nat.div_mul_le_self (S - (2 + T * (2 * (T + 2)))) T
    have h₂ := mul_comm T ((S - (2 + T * (2 * (T + 2)))) / T)
    omega

end Cslib.Circuits.Boolean
