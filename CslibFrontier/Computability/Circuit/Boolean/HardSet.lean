/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardDistribution
import CslibFrontier.Probability.Chernoff
import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Hard sets for shallow formulas

[ChukhinKulikovMihajlinSmal2026], Lemma 6.3 (printed pp. 15–16; PDF pp. 16–17): if every
nonempty `S ⊆ {0, 1}ⁿ` admits a formula of depth at most `t` that agrees with `g` on at least
`2|S|/3` points of `S`, then `D(g) ≤ t + O(log n)`. Here
`formulaDepth_le_of_forall_exists_agree` gives `D(g) ≤ 4 ⌈log₂ n⌉ + ⌈log₂ K⌉ + 18` for
`K = hardSetSize n t = 14117 · 2^t · (4n + 4)`, and `formulaDepth_le_add_of_forall_exists_agree`
gives `D(g) ≤ t + 4 ⌈log₂ n⌉ + ⌈log₂(4n + 4)⌉ + 32`. Depth is `binaryCost` depth, so negations
and constants are free.

The proof follows the source.
1. A hard distribution, by minimax and Lemma 3.7 for formulas, spread out by removing the `K`
   heaviest points: `exists_spread_hardDistribution_of_lt_formulaDepth`. It has
   `ν(x) < 1/(7K)` and accuracy below `9/14` for every formula of depth at most
   `⌈log₂ n⌉ + ⌈log₂ K⌉ ≥ t`.
2. Rounding (`exists_hardSet_of_spread`). Each point joins a random set `S` independently with
   probability `K ν(x)`. A union bound over the functions of depth-`t` formulas
   (`depthFunctions`) leaves an `S` on which every such formula agrees with `g` on fewer than
   `2|S|/3` points.

Two points differ from the source; neither changes the statement.
* The source bounds `Pr[w_h ≥ 0]` for `w_h = Σ_{x ∈ S} (1[h(x) = g(x)] - 2/3)` by Bernstein's
  inequality. Here the event `3X ≥ 2|S|`, for `X` the agreements in `S`, is split into an upper
  tail of `X` and a lower tail of `|S|` with `δ = 1/55`, and each tail is bounded by the
  multiplicative Chernoff bounds of `Probability.Chernoff`.
* The source takes `K = c_K 2^t log₂(4n + 4)`. The cruder `K = 14117 · 2^t · (4n + 4)` here only
  changes the `O(log n)` term. The source's union bound over padded formulas is a union bound over
  computed functions here, because free negations make the formulas of bounded depth infinitely
  many.

## Main definitions

* `Cslib.Circuits.Boolean.hardSetSize`: the size `K` of the rounding.

## Main results

* `Cslib.Circuits.Boolean.exists_hardSet_of_spread`: rounding a spread hard distribution.
* `Cslib.Circuits.Boolean.formulaDepth_le_of_forall_exists_agree`: Lemma 6.3.
* `Cslib.Circuits.Boolean.formulaDepth_le_add_of_forall_exists_agree`: Lemma 6.3 as
  `D(g) ≤ t + O(log n)`.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Formula Cslib.Probability.PMF

variable {n : ℕ}

/-- The number of sampled points in the rounding of [ChukhinKulikovMihajlinSmal2026], Lemma 6.3:
`K = 14117 · 2^t · (4n + 4)`. The source takes `K = c_K 2^t log₂(4n + 4)`; the cruder size here
changes only the `O(log n)` term of the lemma. -/
@[expose] def hardSetSize (n t : ℕ) : ℕ := 14117 * 2 ^ t * (4 * n + 4)

/-- With `K = hardSetSize n t`, the union bound over `(4n + 4)^{2^t}` functions succeeds:
`(4n + 4)^{2^t} exp(-3K/42350) < 1`. -/
private theorem pow_mul_exp_hardSetSize_lt_one (n t : ℕ) :
    ((4 * n + 4 : ℕ) : ℝ) ^ 2 ^ t * Real.exp (-(3 * (hardSetSize n t : ℝ) / 42350)) < 1 := by
  set c : ℝ := ((4 * n + 4 : ℕ) : ℝ)
  have hc : 0 < c := by positivity
  have hK : (2 : ℝ) ^ t * c ≤ 3 * (hardSetSize n t : ℝ) / 42350 := by
    simp only [hardSetSize, c]
    push_cast
    have : (0 : ℝ) ≤ 2 ^ t * (4 * n + 4) := by positivity
    nlinarith
  have hexp : Real.exp (-(3 * (hardSetSize n t : ℝ) / 42350)) ≤ Real.exp (-c) ^ 2 ^ t := by
    rw [← Real.exp_nat_mul, Real.exp_le_exp]
    push_cast
    linarith
  have hlt : c * Real.exp (-c) < 1 := by
    rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos c), one_mul]
    linarith [Real.add_one_le_exp c]
  calc c ^ 2 ^ t * Real.exp (-(3 * (hardSetSize n t : ℝ) / 42350))
      ≤ c ^ 2 ^ t * Real.exp (-c) ^ 2 ^ t := by gcongr
    _ = (c * Real.exp (-c)) ^ 2 ^ t := (mul_pow _ _ _).symm
    _ < 1 := pow_lt_one₀ (by positivity) hlt (by positivity)

open scoped Classical unitInterval in
/-- **Rounding to a hard set** ([ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3, printed
pp. 15–16; PDF pp. 16–17). Let `ν` have `7K ν(x) < 1` everywhere, let every formula of depth at
most `t` have accuracy below `9/14` under `ν`, and let `(4n + 4)^{2^t} exp(-3K/42350) < 1`. Then
some set `S` has `3 · |{x ∈ S | h(x) = g(x)}| < 2 |S|` for every formula `h` of depth at most `t`.

Each point `x` joins `S` independently with probability `K ν(x)` (`Probability.PMF.coin` under
`Probability.PMF.pi`). Then the number `X` of points of `S` where `h` agrees with `g` has mean
`K · accuracy < 9K/14`, and `|S|` has mean `K`. With `δ = 1/55`, `3X ≥ 2|S|` forces
`X ≥ (1 + δ) 9K/14` or `|S| ≤ (1 - δ) K`. The multiplicative Chernoff bounds
(`Probability.PMF.pi_sum_ge_one_add_mul_of_le_one`, `Probability.PMF.pi_sum_le_one_sub_mul`)
bound each by `exp(-3K/42350)`. A union bound over the at most `(4n + 4)^{2^t} / 2` functions of
such formulas (`two_mul_card_depthFunctions_le`) leaves a set `S` good for all of them. The source
uses Bernstein's inequality for `X - 2|S|/3` instead; the two tails here give the same
`2^{-Ω(K)}`. -/
theorem exists_hardSet_of_spread (g : BitString n → Bool) {t K : ℕ} {ν : PMF (BitString n)}
    (hν : ∀ x, 7 * K * (ν x).toReal < 1)
    (hacc : ∀ F : Formula signature n, F.depthWith binaryCost ≤ t → accuracy ν g F < 9 / 14)
    (hK : ((4 * n + 4 : ℕ) : ℝ) ^ 2 ^ t * Real.exp (-(3 * (K : ℝ) / 42350)) < 1) :
    ∃ S : Finset (BitString n), ∀ F : Formula signature n, F.depthWith binaryCost ≤ t →
      3 * (S.filter fun x => F.eval interpretation x = g x).card < 2 * S.card := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hνr (x : BitString n) : 0 ≤ (K : ℝ) * (ν x).toReal :=
    mul_nonneg hK0 ENNReal.toReal_nonneg
  have hν1 (x : BitString n) : (K : ℝ) * (ν x).toReal ≤ 1 := by
    have := hν x
    have : 0 ≤ (K : ℝ) * (ν x).toReal := hνr x
    nlinarith
  -- The rounding: `x` joins `S` with probability `K ν(x)`.
  let q (x : BitString n) : I := ⟨(K : ℝ) * (ν x).toReal, hνr x, hν1 x⟩
  let P : PMF (BitString n → Bool) := pi fun x => coin (q x)
  have hq (x : BitString n) (b : Bool) :
      (coin (q x) b).toReal = if b then (K : ℝ) * (ν x).toReal else 1 - K * (ν x).toReal :=
    coin_apply_toReal _ _
  -- The functions of formulas of depth at most `t`, each with a witness formula.
  set H := (depthFunctions n t).filter fun f =>
    ∃ F : Formula signature n, F.depthWith binaryCost ≤ t ∧ F.eval interpretation = f
  have hH (f : BitString n → Bool) (hf : f ∈ H) :
      ∃ F : Formula signature n, F.depthWith binaryCost ≤ t ∧ F.eval interpretation = f :=
    (Finset.mem_filter.1 hf).2
  set δ : ℝ := 1 / 55
  set X : (BitString n → Bool) → (BitString n → Bool) → ℝ := fun f y =>
    ∑ x, (fun (x : BitString n) (b : Bool) => if b ∧ f x = g x then (1 : ℝ) else 0) x (y x)
  set Y : (BitString n → Bool) → ℝ := fun y =>
    ∑ x, (fun (_ : BitString n) (b : Bool) => if b then (1 : ℝ) else 0) x (y x)
  set e : ℝ := Real.exp (-(3 * (K : ℝ) / 42350))
  -- Each tail has probability at most `e`.
  have htailX (f : BitString n → Bool) (hf : f ∈ H) :
      (P.toOuterMeasure {y | (1 + δ) * (9 / 14 * K) ≤ X f y}).toReal ≤ e := by
    obtain ⟨F, hFd, rfl⟩ := hH f hf
    have hmean : ∑ x, ∑ b, (coin (q x) b).toReal *
        (fun (x : BitString n) (b : Bool) =>
          if b ∧ F.eval interpretation x = g x then (1 : ℝ) else 0) x b ≤ 9 / 14 * K := by
      have hA := hacc F hFd
      have : ∑ x, ∑ b, (coin (q x) b).toReal *
          (fun (x : BitString n) (b : Bool) =>
            if b ∧ F.eval interpretation x = g x then (1 : ℝ) else 0) x b =
          K * accuracy ν g F := by
        rw [accuracy, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_bool, hq, hq]
        by_cases hx : F.eval interpretation x = g x <;> simp [hx]
      rw [this]
      nlinarith
    refine (pi_sum_ge_one_add_mul_of_le_one (fun x => coin (q x)) _ (fun x b _ => by
      split_ifs <;> simp) hmean (by norm_num) (by norm_num)).trans ?_
    refine Real.exp_le_exp.2 ?_
    simp only [δ]
    nlinarith
  have htailY : (P.toOuterMeasure {y | Y y ≤ (1 - δ) * K}).toReal ≤ e := by
    have hmean : (K : ℝ) ≤ ∑ x, ∑ b, (coin (q x) b).toReal *
        (fun (_ : BitString n) (b : Bool) => if b then (1 : ℝ) else 0) x b := by
      have : ∑ x, ∑ b, (coin (q x) b).toReal *
          (fun (_ : BitString n) (b : Bool) => if b then (1 : ℝ) else 0) x b =
          K * ∑ x, (ν x).toReal := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Fintype.sum_bool, hq, hq]
        simp
      rw [this, sum_toReal, mul_one]
    refine (pi_sum_le_one_sub_mul (fun x => coin (q x)) _ (fun x b _ => by
      split_ifs <;> simp) hmean (by norm_num)).trans ?_
    refine Real.exp_le_exp.2 ?_
    simp only [δ]
    nlinarith
  -- `3X ≥ 2|S|` forces one of the two tails.
  have hsplit (f : BitString n → Bool) (y : BitString n → Bool) (hy : 2 * Y y ≤ 3 * X f y) :
      (1 + δ) * (9 / 14 * K) ≤ X f y ∨ Y y ≤ (1 - δ) * K := by
    by_contra hcon
    push Not at hcon
    simp only [δ] at hcon
    linarith
  -- The union bound, as a double count over outcomes.
  set w : (BitString n → Bool) → ℝ := fun y => (P y).toReal
  have hw0 (y : BitString n → Bool) : 0 ≤ w y := ENNReal.toReal_nonneg
  have hw1 : ∑ y, w y = 1 := sum_toReal P
  set bad : (BitString n → Bool) → ℕ := fun y => (H.filter fun f => 2 * Y y ≤ 3 * X f y).card
  have hcount : ∑ y, w y * bad y ≤ H.card * (2 * e) := by
    have hbad (y : BitString n → Bool) : (bad y : ℝ) ≤ ∑ f ∈ H,
        ((if (1 + δ) * (9 / 14 * K) ≤ X f y then 1 else 0) +
          (if Y y ≤ (1 - δ) * K then 1 else 0) : ℝ) := by
      simp only [bad, Finset.card_filter]
      push_cast
      refine Finset.sum_le_sum fun f _ => ?_
      split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> norm_num
      · rcases hsplit f y h1 with h | h
        · exact absurd h h2
        · exact absurd h h3
    calc ∑ y, w y * bad y
        ≤ ∑ y, w y * ∑ f ∈ H, ((if (1 + δ) * (9 / 14 * K) ≤ X f y then 1 else 0) +
          (if Y y ≤ (1 - δ) * K then 1 else 0) : ℝ) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hbad y) (hw0 y)
      _ = ∑ f ∈ H, ((P.toOuterMeasure {y | (1 + δ) * (9 / 14 * K) ≤ X f y}).toReal +
          (P.toOuterMeasure {y | Y y ≤ (1 - δ) * K}).toReal) := by
          simp only [toOuterMeasure_apply_toReal, Finset.mul_sum, ← Finset.sum_add_distrib]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun y _ => ?_
          simp only [Set.mem_ofPred_eq, w]
          split_ifs <;> ring
      _ ≤ ∑ _f ∈ H, 2 * e :=
          Finset.sum_le_sum fun f hf => (add_le_add (htailX f hf) htailY).trans (two_mul e).ge
      _ = H.card * (2 * e) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hHcard : 2 * (H.card : ℝ) ≤ ((4 * n + 4 : ℕ) : ℝ) ^ 2 ^ t := by
    have h₁ : H.card ≤ (depthFunctions n t).card := Finset.card_filter_le _ _
    have h₂ := two_mul_card_depthFunctions_le (n := n) t
    exact_mod_cast (show 2 * H.card ≤ (4 * n + 4) ^ 2 ^ t by omega)
  have hsum_lt : ∑ y, w y * bad y < 1 := by
    have he : 0 ≤ e := (Real.exp_pos _).le
    calc ∑ y, w y * bad y ≤ H.card * (2 * e) := hcount
      _ = 2 * H.card * e := by ring
      _ ≤ ((4 * n + 4 : ℕ) : ℝ) ^ 2 ^ t * e := mul_le_mul_of_nonneg_right hHcard he
      _ < 1 := hK
  -- Some outcome is good for every function.
  obtain ⟨y, hy⟩ : ∃ y, bad y = 0 := by
    by_contra hall
    push Not at hall
    have : ∑ y, w y ≤ ∑ y, w y * bad y := Finset.sum_le_sum fun y _ => by
      have : (1 : ℝ) ≤ bad y := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (hall y)
      nlinarith [hw0 y]
    linarith
  refine ⟨Finset.univ.filter fun x => y x = true, fun F hF => ?_⟩
  have hFH : F.eval interpretation ∈ H :=
    Finset.mem_filter.2 ⟨(eval_mem_depthFunctions F hF).1, F, hF, rfl⟩
  have hnot : ¬ 2 * Y y ≤ 3 * X (F.eval interpretation) y := fun h => by
    have hmem : F.eval interpretation ∈ H.filter fun f => 2 * Y y ≤ 3 * X f y :=
      Finset.mem_filter.2 ⟨hFH, h⟩
    rw [Finset.card_eq_zero.1 hy] at hmem
    simp at hmem
  have hX : X (F.eval interpretation) y =
      ((Finset.univ.filter fun x => y x = true).filter
        fun x => F.eval interpretation x = g x).card := by
    simp only [X, Finset.filter_filter, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp_all
  have hY : Y y = (Finset.univ.filter fun x => y x = true).card := by
    simp only [Y, Finset.card_filter]
    push_cast
    rfl
  rw [hX, hY] at hnot
  push Not at hnot
  exact_mod_cast hnot

/-- **[ChukhinKulikovMihajlinSmal2026], Lemma 6.3** (printed pp. 15–16; PDF pp. 16–17). Let
`g : {0, 1}ⁿ → {0, 1}` and `t ≥ 0`. Suppose that every nonempty `S ⊆ {0, 1}ⁿ` admits a formula of
`binaryCost` depth at most `t` that agrees with `g` on at least `2|S|/3` points of `S`. Then
`D(g) ≤ 4 ⌈log₂ n⌉ + ⌈log₂ K⌉ + 18` for `K = hardSetSize n t = 14117 · 2^t · (4n + 4)`. This is
the source's `D(g) ≤ t + O(log n)`; see `formulaDepth_le_add_of_forall_exists_agree`.

Otherwise `D(g)` exceeds `d + 18 + 3 ⌈log₂ n⌉` for `d = ⌈log₂ n⌉ + ⌈log₂ K⌉ ≥ t`. Then a spread
hard distribution exists (`exists_spread_hardDistribution_of_lt_formulaDepth`), and rounding it
(`exists_hardSet_of_spread`) gives a set `S` violating the assumption. Such an `S` is nonempty,
since on the empty set the strict inequality `0 < 0` fails. -/
theorem formulaDepth_le_of_forall_exists_agree (g : BooleanFunction n) (t : ℕ)
    (h : ∀ S : Finset (BitString n), S.Nonempty → ∃ F : Formula signature n,
      F.depthWith binaryCost ≤ t ∧
        2 * S.card ≤ 3 * (S.filter fun x => F.eval interpretation x = g x).card) :
    formulaDepth g ≤ 4 * Nat.clog 2 n + Nat.clog 2 (hardSetSize n t) + 18 := by
  by_contra hlt
  push Not at hlt
  set K := hardSetSize n t
  obtain ⟨ν, hν, hacc⟩ := exists_spread_hardDistribution_of_lt_formulaDepth (K := K) g
    (by omega)
  have htK : t ≤ Nat.clog 2 K := by
    have : 2 ^ t ≤ K := by
      simp only [K, hardSetSize]
      have := Nat.one_le_two_pow (n := t)
      nlinarith
    exact (Nat.clog_pow 2 t one_lt_two).symm.le.trans (Nat.clog_mono_right 2 this)
  obtain ⟨S, hS⟩ := exists_hardSet_of_spread g hν
    (fun F hF => hacc F (hF.trans (by omega))) (pow_mul_exp_hardSetSize_lt_one n t)
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simpa using hS (.const false) (by simp)
  obtain ⟨F, hF, hagree⟩ := h S hne
  have := hS F hF
  omega

/-- `⌈log₂ (14117 · 2^t · (4n + 4))⌉ ≤ t + ⌈log₂(4n + 4)⌉ + 14`. -/
private theorem clog_hardSetSize_le (n t : ℕ) :
    Nat.clog 2 (hardSetSize n t) ≤ t + Nat.clog 2 (4 * n + 4) + 14 := by
  refine Nat.clog_le_of_le_pow ?_
  have h₁ := Nat.le_pow_clog one_lt_two (4 * n + 4)
  calc hardSetSize n t = 14117 * 2 ^ t * (4 * n + 4) := rfl
    _ ≤ 2 ^ 14 * 2 ^ t * 2 ^ Nat.clog 2 (4 * n + 4) := by
        gcongr
        norm_num
    _ = 2 ^ (t + Nat.clog 2 (4 * n + 4) + 14) := by rw [← pow_add, ← pow_add]; ring_nf

/-- **Lemma 6.3 in the source's form** `D(g) ≤ t + O(log n)`: under its assumption,
`D(g) ≤ t + 4 ⌈log₂ n⌉ + ⌈log₂(4n + 4)⌉ + 32`. -/
theorem formulaDepth_le_add_of_forall_exists_agree (g : BooleanFunction n) (t : ℕ)
    (h : ∀ S : Finset (BitString n), S.Nonempty → ∃ F : Formula signature n,
      F.depthWith binaryCost ≤ t ∧
        2 * S.card ≤ 3 * (S.filter fun x => F.eval interpretation x = g x).card) :
    formulaDepth g ≤ t + 4 * Nat.clog 2 n + Nat.clog 2 (4 * n + 4) + 32 := by
  have := formulaDepth_le_of_forall_exists_agree g t h
  have := clog_hardSetSize_le n t
  omega

end Cslib.Circuits.Boolean
