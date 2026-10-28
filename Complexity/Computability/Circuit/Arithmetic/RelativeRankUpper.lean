/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.RelativeRank
public import Complexity.Computability.Circuit.Arithmetic.SetMultilinear
public import Complexity.Computability.Circuit.Arithmetic.Word
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational

/-!
# Upper bound on the relative rank of set-multilinear formulas

This file proves the upper bound of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021]
on the relative rank of small set-multilinear formulas of low product-depth (LST Claim 16,
ECCC TR21-081 revision 1, §5, pp. 12–13).

Fix `k` and a word `w : Fin d → ℤ` whose letters are `⌊k / √2⌋` and `-k`, and let block `i`
have `2 ^ |w i|` variables. For a set `S` of blocks, the measure `relrk_{w|S}` of LST is
`relRank blk (wordPos w ∩ S) (wordNeg w ∩ S)`: rows are indexed by the positive blocks of
`S`, columns by the negative ones. If `k ≥ 10 d` and `Δ ≥ 1`, a set-multilinear formula on `S`
of product-depth at most `Δ` with `s` nodes satisfies
`relrk_{w|S} ≤ s · 2 ^ (-(k |S| ^ (1 / (2 ^ Δ - 1)) / 20))`
(`SPFormula.IsSetMultilinear.relRank_polynomial_le`, and the case of all blocks
`SPFormula.IsSetMultilinear.relRank_polynomial_le_univ`).

The proof follows the source, along the structure of the formula
(`SPFormula.relRank_polynomial_le_nodeCount_mul`): sum gates by subadditivity, and product gates
by multiplicativity (`relRank_prod_le`). A product gate of product-depth `Δ + 1` on `m` blocks is
of *type 1* if a factor lives on more than `τ = m ^ ((2 ^ Δ - 1) / (2 ^ (Δ + 1) - 1))` blocks,
handled by induction on `Δ`, and of *type 2* otherwise. For a type-2 factor on `T`, the sum
`w_T` is far from zero by the Diophantine bound for `1 / √2`
(LST Claim 17, `one_div_le_abs_div_sqrt_two_sub`), so its relative rank is small by imbalance
(`relRank_le_two_rpow_abs_sum`, LST Claim 7(1)).

Claim 16 holds for every word over the alphabet `{⌊k / √2⌋, -k}`; the choice of a `k`-unbiased
word (the greedy word `Cslib.Circuits.Arithmetic.greedyWord`) only matters for the lower bound on
the hard polynomial, which is not part of this file.

Departures from the source, all original:
* Claim 17 is stated for all integers `a` and `b`; it fails for `a = b = 0`, which is excluded
  here. The source only applies it when `a + b ≥ 1`.
* Claim 16 is stated on every set `S` of blocks, the form its induction uses.
* Factors on no block (constants, and products of them) have relative rank at most `1` and do
  not count towards the factors of a type-2 product; the source does not discuss them. A formula
  of product-depth zero may be set-multilinear on two or more blocks only by computing zero (a
  sum gate without arguments), which the base case handles separately
  (`SPFormula.IsSetMultilinear.card_le_one_or_polynomial_eq_zero`).
* The base case `Δ = 1` is the type-2 argument with `τ = 1`, giving the source's bound.

## Main results

* `Cslib.Circuits.Arithmetic.relRank_sum_le`,
  `Cslib.Circuits.Arithmetic.relRank_inter_biUnion_prod_le`: subadditivity and multiplicativity
  (as an inequality) over finite sums and products.
* `Cslib.Circuits.Arithmetic.relRank_le_two_rpow_abs_sum`: imbalance for a word,
  `relrk_{w|S} ≤ 2 ^ (-|w_S| / 2)`.
* `Cslib.Circuits.Arithmetic.one_div_le_abs_div_sqrt_two_sub`: LST Claim 17.
* `Cslib.Circuits.Arithmetic.relRank_le_two_rpow_of_card_le`: the type-2 bound for one factor.
* `Cslib.Circuits.Arithmetic.SPFormula.relRank_polynomial_le_nodeCount_mul`: the induction frame
  along a set-multilinear formula.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSetMultilinear.relRank_polynomial_le`: LST Claim 16.

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1: §2 (words, p. 6), Claim 7
  (§2.1, pp. 6–7), proof of Lemma 15 and Claims 16 and 17 (§5, pp. 12–13)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open Function MvPolynomial

variable {σ K : Type*} {d : ℕ}

/-! ### Products of set-multilinear polynomials -/

section Products

variable [Fintype σ] [Field K] {blk : σ → Fin d}

/-- **Subadditivity over finite sums** (LST Claim 7(2), iterated). -/
theorem relRank_sum_le (A B : Finset (Fin d)) {ι : Type*} (s : Finset ι)
    (f : ι → MvPolynomial σ K) :
    relRank blk A B (∑ j ∈ s, f j) ≤ ∑ j ∈ s, relRank blk A B (f j) :=
  Finset.le_sum_of_subadditive (relRank blk A B) (relRank_zero blk A B).le
    (relRank_add_le blk A B) s f

/-- **Multiplicativity over finite products, restricted to the blocks of the product**
(LST Claim 7(3), `relRank_prod_le`): the relative rank, on the blocks of `⋃ T j`, of a product of
set-multilinear polynomials on pairwise disjoint sets of blocks is at most the product of their
relative ranks on their own blocks. -/
theorem relRank_inter_biUnion_prod_le (A B : Finset (Fin d)) {ι : Type*} (s : Finset ι)
    (T : ι → Finset (Fin d)) (f : ι → MvPolynomial σ K) (hT : (s : Set ι).PairwiseDisjoint T)
    (hf : ∀ j ∈ s, IsSetMultilinear blk (T j) (f j)) :
    relRank blk (A ∩ s.biUnion T) (B ∩ s.biUnion T) (∏ j ∈ s, f j) ≤
      ∏ j ∈ s, relRank blk (A ∩ T j) (B ∩ T j) (f j) := by
  classical
  refine (relRank_prod_le s hT hf Finset.inter_subset_right Finset.inter_subset_right).trans_eq
    (Finset.prod_congr rfl fun j hj => ?_)
  have hj' : T j ⊆ s.biUnion T := Finset.subset_biUnion_of_mem T hj
  rw [Finset.inter_assoc, Finset.inter_assoc, Finset.inter_eq_right.2 hj']

/-- The relative rank of a product of set-multilinear polynomials on pairwise disjoint sets of
blocks is at most the relative rank of any one factor. -/
theorem relRank_prod_le_of_mem (A B : Finset (Fin d)) {ι : Type*} {s : Finset ι}
    (T : ι → Finset (Fin d)) (f : ι → MvPolynomial σ K) (hT : (s : Set ι).PairwiseDisjoint T)
    (hf : ∀ j ∈ s, IsSetMultilinear blk (T j) (f j)) {j : ι} (hj : j ∈ s) :
    relRank blk (A ∩ s.biUnion T) (B ∩ s.biUnion T) (∏ j ∈ s, f j) ≤
      relRank blk (A ∩ T j) (B ∩ T j) (f j) := by
  classical
  refine (relRank_inter_biUnion_prod_le A B s T f hT hf).trans ?_
  rw [← Finset.mul_prod_erase s _ hj]
  exact mul_le_of_le_one_right (relRank_nonneg _ _ _ _)
    (Finset.prod_le_one₀ (fun _ _ => relRank_nonneg _ _ _ _) fun _ _ => relRank_le_one _ _ _ _)

/-- If each factor of a product of set-multilinear polynomials on pairwise disjoint sets of
blocks has relative rank at most `2 ^ (-(|T j| * c))`, the product has relative rank at most
`2 ^ (-(|⋃ T j| * c))`. -/
theorem relRank_prod_le_two_rpow (A B : Finset (Fin d)) {ι : Type*} (s : Finset ι)
    (T : ι → Finset (Fin d)) (f : ι → MvPolynomial σ K) (hT : (s : Set ι).PairwiseDisjoint T)
    (hf : ∀ j ∈ s, IsSetMultilinear blk (T j) (f j)) (c : ℝ)
    (hc : ∀ j ∈ s, relRank blk (A ∩ T j) (B ∩ T j) (f j) ≤ 2 ^ (-((T j).card * c))) :
    relRank blk (A ∩ s.biUnion T) (B ∩ s.biUnion T) (∏ j ∈ s, f j) ≤
      2 ^ (-((s.biUnion T).card * c)) := by
  classical
  refine (relRank_inter_biUnion_prod_le A B s T f hT hf).trans ?_
  refine (Finset.prod_le_prod₀ (fun _ _ => relRank_nonneg _ _ _ _) hc).trans_eq ?_
  rw [← Real.rpow_sum_of_pos two_pos, Finset.card_biUnion hT]
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]

end Products

/-! ### The word measure and imbalance -/

section Word

/-- `√(2 ^ p / 2 ^ q) = 2 ^ ((p - q) / 2)`. -/
private theorem sqrt_two_pow_div_two_pow (p q : ℕ) :
    √((2 : ℝ) ^ p / 2 ^ q) = 2 ^ (((p : ℝ) - q) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_sub two_pos, Real.sqrt_eq_rpow,
    ← Real.rpow_mul zero_le_two]
  congr 1
  ring

variable [Fintype σ] [Field K] {blk : σ → Fin d}

/-- **Imbalance for a word** (LST Claim 7(1) in the form used in §5): if block `i` has
`2 ^ |w i|` variables, then on a set `S` of blocks, with rows the positive and columns the
negative blocks of `S`, the relative rank is at most `2 ^ (-|w_S| / 2)`, where
`w_S = ∑ i ∈ S, w i`. -/
theorem relRank_le_two_rpow_abs_sum (w : Fin d → ℤ)
    (hblk : ∀ i, Fintype.card {x : σ // blk x = i} = 2 ^ (w i).natAbs) (S : Finset (Fin d))
    (f : MvPolynomial σ K) :
    relRank blk (wordPos w ∩ S) (wordNeg w ∩ S) f ≤
      2 ^ (-(|∑ i ∈ S, (w i : ℝ)| / 2)) := by
  classical
  set p := ∑ i ∈ wordPos w ∩ S, (w i).natAbs
  set q := ∑ i ∈ wordNeg w ∩ S, (w i).natAbs
  have hrows : Fintype.card (BlockChoice blk (wordPos w ∩ S)) = 2 ^ p := by
    rw [card_blockChoice, Finset.prod_congr rfl fun i _ => hblk i, Finset.prod_pow_eq_pow_sum]
  have hcols : Fintype.card (BlockChoice blk (wordNeg w ∩ S)) = 2 ^ q := by
    rw [card_blockChoice, Finset.prod_congr rfl fun i _ => hblk i, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ i ∈ S, (w i : ℝ) = (p : ℝ) - q := by
    have hP : wordPos w ∩ S = S.filter fun i => 0 ≤ w i := by
      ext i
      simp [and_comm]
    have hN : wordNeg w ∩ S = S.filter fun i => ¬ 0 ≤ w i := by
      ext i
      simp [and_comm]
    rw [← Finset.sum_filter_add_sum_filter_not S fun i => 0 ≤ w i, ← hP, ← hN]
    simp only [p, q, Nat.cast_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi : 0 ≤ w i := mem_wordBlocks.mp (Finset.mem_inter.mp hi).1
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg (by exact_mod_cast hi : (0 : ℝ) ≤ w i)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi : w i < 0 := mem_wordBlocks.mp (Finset.mem_inter.mp hi).1
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hi : (w i : ℝ) < 0), neg_neg]
  rw [hsum]
  rcases le_total (q : ℝ) p with hpq | hpq
  · refine (relRank_le_sqrt_cols_div_rows blk _ _ f).trans_eq ?_
    rw [hcols, hrows, Nat.cast_pow, Nat.cast_pow, Nat.cast_two, sqrt_two_pow_div_two_pow,
      abs_of_nonneg (sub_nonneg.mpr hpq)]
    ring_nf
  · refine (relRank_le_sqrt_rows_div_cols blk _ _ f).trans_eq ?_
    rw [hcols, hrows, Nat.cast_pow, Nat.cast_pow, Nat.cast_two, sqrt_two_pow_div_two_pow,
      abs_of_nonpos (sub_nonpos.mpr hpq)]
    ring_nf

end Word

/-! ### Diophantine approximation of `1 / √2` (LST Claim 17) -/

section Diophantine

/-- `a ^ 2 ≠ 2 * b ^ 2` for integers that are not both zero, since `√2` is irrational. -/
private theorem sq_ne_two_mul_sq {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) : a ^ 2 ≠ 2 * b ^ 2 := by
  intro h
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [ne_eq, not_true_eq_false, or_false] at hab
    exact hab (pow_eq_zero_iff two_ne_zero |>.mp (by simpa using h))
  · refine irrational_sqrt_two.ne_rational |a| |b| ?_
    have hb' : (0 : ℝ) < |(b : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hb)
    have hR : ((a : ℝ)) ^ 2 = 2 * (b : ℝ) ^ 2 := by exact_mod_cast h
    rw [Real.sqrt_eq_iff_eq_sq zero_le_two (by push_cast; positivity)]
    push_cast
    rw [div_pow, sq_abs, sq_abs, hR]
    field_simp

/-- **LST Claim 17** (ECCC TR21-081 rev. 1, §5, proof of Claim 16): for integers `a` and `b`,
`|a / √2 - b| ≥ 1 / (4 |a / √2| + 2)`. The source states it for all integers; it fails for
`a = b = 0`, which this statement excludes (original correction; the source applies it only
when `a + b ≥ 1`). -/
theorem one_div_le_abs_div_sqrt_two_sub {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) :
    1 / (4 * |(a : ℝ) / √2| + 2) ≤ |(a : ℝ) / √2 - b| := by
  set x : ℝ := (a : ℝ) / √2
  have hx2 : x ^ 2 = (a : ℝ) ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt zero_le_two]
  have h1 : (1 : ℝ) ≤ |(a : ℝ) ^ 2 - 2 * (b : ℝ) ^ 2| := by
    have : (1 : ℤ) ≤ |a ^ 2 - 2 * b ^ 2| := Int.one_le_abs (sub_ne_zero.mpr (sq_ne_two_mul_sq hab))
    exact_mod_cast this
  have hprod : |x - b| * |x + b| = |(a : ℝ) ^ 2 - 2 * (b : ℝ) ^ 2| / 2 := by
    rw [← abs_mul, show (x - b) * (x + b) = ((a : ℝ) ^ 2 - 2 * (b : ℝ) ^ 2) / 2 by
      rw [show (x - b) * (x + b) = x ^ 2 - (b : ℝ) ^ 2 by ring, hx2]; ring,
      abs_div, abs_two]
  have hx0 : 0 ≤ |x| := abs_nonneg x
  rcases le_or_gt (|x| + 1) |(b : ℝ)| with hb | hb
  · have : 1 ≤ |x - b| := by
      rw [abs_sub_comm]
      linarith [abs_sub_abs_le_abs_sub (b : ℝ) x]
    refine le_trans ?_ this
    rw [div_le_one (by positivity)]
    linarith
  · have hxb : |x + b| ≤ 2 * |x| + 1 := (abs_add_le x b).trans (by linarith)
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg (x - b), abs_nonneg (x + b)]

end Diophantine

/-! ### Words over the alphabet `{⌊k / √2⌋, -k}` -/

section WordSum

/-- **Sums of a word over few blocks are far from zero** (LST, proof of Claim 16, type 2): if
every entry of `w` is `⌊k / √2⌋` or `-k`, then on a nonempty set `T` of at most `τ` blocks,
`|w_T| ≥ k / (10 τ)` provided `k ≥ 10 τ ^ 2`. -/
private theorem div_le_abs_sum_of_card_le {k : ℕ} {w : Fin d → ℤ}
    (hw : ∀ i, w i = ⌊(k : ℝ) / √2⌋ ∨ w i = -k) {T : Finset (Fin d)} {τ : ℝ}
    (hT : T.Nonempty) (hTτ : (T.card : ℝ) ≤ τ) (hk : 10 * τ ^ 2 ≤ k) :
    (k : ℝ) / (10 * τ) ≤ |∑ i ∈ T, (w i : ℝ)| := by
  classical
  have hab : (T.filter fun i => w i = -k).card + (T.filter fun i => ¬ w i = -k).card =
      T.card := Finset.card_filter_add_card_filter_not _
  have h1 : ∑ i ∈ T.filter (fun i => w i = -k), (w i : ℝ) =
      ∑ i ∈ T.filter (fun i => w i = -k), (-(k : ℝ)) :=
    Finset.sum_congr rfl fun i hi => by simp [(Finset.mem_filter.mp hi).2]
  have h2 : ∑ i ∈ T.filter (fun i => ¬ w i = -k), (w i : ℝ) =
      ∑ i ∈ T.filter (fun i => ¬ w i = -k), ((⌊(k : ℝ) / √2⌋ : ℤ) : ℝ) :=
    Finset.sum_congr rfl fun i hi => by
      rw [(hw i).resolve_right (Finset.mem_filter.mp hi).2]
  rw [← Finset.sum_filter_add_sum_filter_not T (fun i => w i = -k), h1, h2,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  generalize (T.filter fun i => w i = -k).card = b at hab ⊢
  generalize (T.filter fun i => ¬ w i = -k).card = a at hab ⊢
  generalize hF : ⌊(k : ℝ) / √2⌋ = F
  have hab' : ((a : ℤ)) ≠ 0 ∨ ((b : ℤ)) ≠ 0 := by
    have := hT.card_pos
    omega
  have h17 := one_div_le_abs_div_sqrt_two_sub hab'
  push_cast at h17
  have hs2 : (4 : ℝ) / 3 ≤ √2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hs2pos : 0 < √2 := by positivity
  have hτ1 : 1 ≤ τ := le_trans (by exact_mod_cast hT.card_pos) hTτ
  have haτ : (a : ℝ) ≤ τ := le_trans (by exact_mod_cast (hab ▸ Nat.le_add_left a b)) hTτ
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hxa : (a : ℝ) / √2 ≤ 3 / 4 * a := by
    rw [div_le_iff₀ hs2pos]
    nlinarith
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ a / √2)] at h17
  have hden : 4 * ((a : ℝ) / √2) + 2 ≤ 5 * τ := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hA : (k : ℝ) / (5 * τ) ≤ k * |(a : ℝ) / √2 - b| := by
    calc (k : ℝ) / (5 * τ) ≤ k / (4 * ((a : ℝ) / √2) + 2) :=
          div_le_div_of_nonneg_left hk0 (by positivity) hden
      _ = k * (1 / (4 * ((a : ℝ) / √2) + 2)) := by ring
      _ ≤ k * |(a : ℝ) / √2 - b| := mul_le_mul_of_nonneg_left h17 hk0
  have hF1 : (F : ℝ) ≤ k / √2 := hF ▸ Int.floor_le _
  have hF2 : (k : ℝ) / √2 < F + 1 := hF ▸ Int.lt_floor_add_one _
  have hB : (k : ℝ) * |(a : ℝ) / √2 - b| - a ≤ |a * (F : ℝ) + b * -(k : ℝ)| := by
    have e : (a : ℝ) * F + b * -(k : ℝ) = k * ((a : ℝ) / √2 - b) - a * (k / √2 - F) := by ring
    have h0 : |(a : ℝ) * (k / √2 - F)| ≤ a := by
      rw [abs_of_nonneg (mul_nonneg ha0 (by linarith))]
      nlinarith
    rw [e]
    calc (k : ℝ) * |(a : ℝ) / √2 - b| - a
        ≤ |(k : ℝ) * ((a : ℝ) / √2 - b)| - |(a : ℝ) * (k / √2 - F)| := by
          rw [abs_mul, abs_of_nonneg hk0]
          linarith
      _ ≤ _ := abs_sub_abs_le_abs_sub _ _
  have hτk : τ ≤ k / (10 * τ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h52 : (k : ℝ) / (5 * τ) = 2 * (k / (10 * τ)) := by
    field_simp
    ring
  rw [add_comm]
  linarith

variable [Field K] {blk : σ → Fin d} [Fintype σ]

/-- **The relative rank on few blocks is small** (LST, proof of Claim 16, type 2): for a word
over `{⌊k / √2⌋, -k}` with block `i` of `2 ^ |w i|` variables, the relative rank on a set `T` of
at most `τ` blocks is at most `2 ^ (-(|T| k / (20 τ ^ 2)))` when `k ≥ 10 τ ^ 2`. -/
theorem relRank_le_two_rpow_of_card_le {k : ℕ} {w : Fin d → ℤ}
    (hblk : ∀ i, Fintype.card {x : σ // blk x = i} = 2 ^ (w i).natAbs)
    (hw : ∀ i, w i = ⌊(k : ℝ) / √2⌋ ∨ w i = -k) {T : Finset (Fin d)} {τ : ℝ}
    (hTτ : (T.card : ℝ) ≤ τ) (hτ : 0 < τ) (hk : 10 * τ ^ 2 ≤ k) (f : MvPolynomial σ K) :
    relRank blk (wordPos w ∩ T) (wordNeg w ∩ T) f ≤
      2 ^ (-(T.card * (k / (20 * τ ^ 2)))) := by
  rcases T.eq_empty_or_nonempty with rfl | hT
  · simpa using relRank_le_one blk _ _ f
  · refine (relRank_le_two_rpow_abs_sum w hblk T f).trans
      (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
    have h := div_le_abs_sum_of_card_le hw hT hTτ hk
    have h1 : (T.card : ℝ) * (k / (20 * τ ^ 2)) ≤ k / (20 * τ) := by
      rw [show (k : ℝ) / (20 * τ) = τ * (k / (20 * τ ^ 2)) by field_simp]
      exact mul_le_mul_of_nonneg_right hTτ (by positivity)
    have h2 : (k : ℝ) / (20 * τ) = (k / (10 * τ)) / 2 := by
      field_simp
      ring
    linarith

end WordSum

/-! ### Set-multilinear formulas -/

namespace SPFormula

variable {n : ℕ} {blk : Fin n → Fin d}

/-- An argument of a product gate has at most as many nodes as the gate. -/
theorem nodeCount_le_nodeCount_mul {m : ℕ} (G : Fin m → SPFormula K n) (j : Fin m) :
    (G j).nodeCount ≤ (mul G).nodeCount := by
  rw [Formula.nodeCount_gate]
  exact Nat.le_succ_of_le (Finset.single_le_sum (f := fun j => (G j).nodeCount)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))

/-- A set-multilinear formula of product-depth zero lives on at most one block, unless it
computes zero (a sum gate without arguments is set-multilinear on every set of blocks). -/
theorem IsSetMultilinear.card_le_one_or_polynomial_eq_zero [CommSemiring K] {F : SPFormula K n}
    {S : Finset (Fin d)} (h : F.IsSetMultilinear blk S) (h0 : F.productDepth = 0) :
    S.card ≤ 1 ∨ F.polynomial = 0 := by
  induction h with
  | input i => exact Or.inl (Finset.card_singleton _).le
  | const a => exact Or.inl (by simp)
  | add c F S _ ih =>
    rw [productDepth_add] at h0
    have hd (j : Fin _) : (F j).productDepth = 0 :=
      Nat.eq_zero_of_le_zero (h0 ▸ Finset.le_sup (f := fun j => (F j).productDepth)
        (Finset.mem_univ j))
    by_cases hS : S.card ≤ 1
    · exact Or.inl hS
    · refine Or.inr ?_
      rw [polynomial_add]
      exact Finset.sum_eq_zero fun j _ => by rw [(ih j (hd j)).resolve_left hS, mul_zero]
  | mul F T _ _ _ =>
    rw [productDepth_mul] at h0
    exact absurd h0 (Nat.succ_ne_zero _)

variable [Field K]

/-- **Relative rank along the formula** (the induction frame of LST Claim 16): if every
polynomial on at most one block has relative rank at most `β S`, and every product gate of
product-depth at most `Δ` on `S` has relative rank at most its node count times `β S`, then
every set-multilinear formula on `S` of product-depth at most `Δ` has relative rank at most its
node count times `β S`. Sum gates are handled by subadditivity. -/
theorem relRank_polynomial_le_nodeCount_mul (A B : Finset (Fin d)) (Δ : ℕ)
    (β : Finset (Fin d) → ℝ) (hβ : ∀ S, 0 ≤ β S)
    (hsmall : ∀ S : Finset (Fin d), S.card ≤ 1 → ∀ f : MvPolynomial (Fin n) K,
      relRank blk (A ∩ S) (B ∩ S) f ≤ β S)
    (hmul : ∀ (m : ℕ) (G : Fin m → SPFormula K n) (T : Fin m → Finset (Fin d)),
      Pairwise (Disjoint on T) → (∀ j, (G j).IsSetMultilinear blk (T j)) →
      (∀ j, (G j).productDepth < Δ) →
      relRank blk (A ∩ Finset.univ.biUnion T) (B ∩ Finset.univ.biUnion T) (mul G).polynomial ≤
        (mul G).nodeCount * β (Finset.univ.biUnion T))
    {F : SPFormula K n} {S : Finset (Fin d)} (hF : F.IsSetMultilinear blk S)
    (hΔ : F.productDepth ≤ Δ) :
    relRank blk (A ∩ S) (B ∩ S) F.polynomial ≤ F.nodeCount * β S := by
  induction hF with
  | input i =>
    rw [Formula.nodeCount_input, Nat.cast_one, one_mul]
    exact hsmall _ (Finset.card_singleton _).le _
  | const a =>
    rw [nodeCount_const, Nat.cast_one, one_mul]
    exact hsmall _ (by simp) _
  | add c F S _ ih =>
    rw [productDepth_add, Finset.sup_le_iff] at hΔ
    rw [polynomial_add, Formula.nodeCount_gate]
    calc relRank blk (A ∩ S) (B ∩ S) (∑ j, C (c j) * (F j).polynomial)
        ≤ ∑ j, relRank blk (A ∩ S) (B ∩ S) (C (c j) * (F j).polynomial) :=
          relRank_sum_le _ _ _ _
      _ ≤ ∑ j, ((F j).nodeCount * β S : ℝ) := Finset.sum_le_sum fun j _ => by
          rw [C_mul']
          exact (relRank_smul_le _ _ _ _ _).trans (ih j (hΔ j (Finset.mem_univ j)))
      _ ≤ (((∑ j, (F j).nodeCount) + 1 : ℕ) : ℝ) * β S := by
          rw [← Finset.sum_mul]
          push_cast
          nlinarith [hβ S]
  | mul F T hT hF _ =>
    rw [productDepth_mul] at hΔ
    exact hmul _ F T hT hF fun j =>
      lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := fun j => (F j).productDepth)
        (Finset.mem_univ j))) hΔ

/-- `0 < 1 / (2 ^ Δ - 1)` for `Δ ≥ 1`. -/
private theorem one_div_two_pow_sub_one_pos {Δ : ℕ} (hΔ : 1 ≤ Δ) :
    0 < 1 / ((2 : ℝ) ^ Δ - 1) := by
  have : (2 : ℝ) ≤ 2 ^ Δ := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ Δ := pow_le_pow_right₀ one_le_two hΔ
  exact one_div_pos.mpr (by linarith)

/-- On at most one block, the exponent of LST Claim 16 is the number of blocks. -/
private theorem rpow_of_le_one {Δ : ℕ} (hΔ : 1 ≤ Δ) {m : ℕ} (hm : m ≤ 1) :
    (m : ℝ) ^ (1 / ((2 : ℝ) ^ Δ - 1)) = m := by
  interval_cases m
  · rw [Nat.cast_zero, Real.zero_rpow (one_div_two_pow_sub_one_pos hΔ).ne']
  · rw [Nat.cast_one, Real.one_rpow]

/-- **LST Claim 16** (ECCC TR21-081 rev. 1, §5, pp. 12–13): let `k ≥ 10 d`, and let `w` be a
word whose entries are `⌊k / √2⌋` or `-k`, with block `i` of `2 ^ |w i|` variables. For `Δ ≥ 1`,
every set-multilinear formula on a set `S` of blocks with product-depth at most `Δ` has relative
rank (rows: the positive blocks of `S`, columns: the negative ones) at most
`nodeCount · 2 ^ (-(k |S| ^ (1 / (2 ^ Δ - 1)) / 20))`.

The source states the bound for `S` the set of all blocks; the induction applies it to the
factors, on smaller sets of blocks, so it is stated here for every `S`. As in the source, the
proof splits a product gate by whether some factor has more than `τ = |S| ^ ((2 ^ Δ' - 1) /
(2 ^ (Δ' + 1) - 1))` blocks. Factors on no block (constants, and products of them) have
relative rank at most `1` and contribute nothing, which the source does not discuss (original
handling); formulas of product-depth zero that are set-multilinear on two or more blocks compute
zero. -/
theorem IsSetMultilinear.relRank_polynomial_le {k : ℕ} {w : Fin d → ℤ}
    (hblk : ∀ i, Fintype.card {x : Fin n // blk x = i} = 2 ^ (w i).natAbs) (hk : 10 * d ≤ k)
    (hw : ∀ i, w i = ⌊(k : ℝ) / √2⌋ ∨ w i = -k) {Δ : ℕ} (hΔ : 1 ≤ Δ) {F : SPFormula K n}
    {S : Finset (Fin d)} (hF : F.IsSetMultilinear blk S) (hFΔ : F.productDepth ≤ Δ) :
    relRank blk (wordPos w ∩ S) (wordNeg w ∩ S) F.polynomial ≤
      F.nodeCount * 2 ^ (-(k * (S.card : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20)) := by
  have hcard (U : Finset (Fin d)) : (U.card : ℝ) ≤ d := by
    exact_mod_cast (Finset.card_le_univ U).trans (Fintype.card_fin d).le
  have hdk (U : Finset (Fin d)) (hU : U.Nonempty) : (10 : ℝ) ≤ k := by
    obtain ⟨i, -⟩ := hU
    have := i.pos
    exact_mod_cast (by omega : 10 ≤ k)
  have hsmall (U : Finset (Fin d)) (hU : U.card ≤ 1) (f : MvPolynomial (Fin n) K) :
      relRank blk (wordPos w ∩ U) (wordNeg w ∩ U) f ≤ 2 ^ (-(U.card * ((k : ℝ) / 20))) := by
    rcases U.eq_empty_or_nonempty with rfl | hne
    · simpa using relRank_le_one blk _ _ f
    · have h := relRank_le_two_rpow_of_card_le hblk hw (τ := 1) (by exact_mod_cast hU) one_pos
        (by have := hdk U hne; nlinarith) f
      rwa [one_pow, mul_one] at h
  have hnode (G : SPFormula K n) : (1 : ℝ) ≤ G.nodeCount := by
    exact_mod_cast Formula.nodeCount_pos G
  suffices H : ∀ Δ, 1 ≤ Δ → ∀ {F : SPFormula K n} {S : Finset (Fin d)},
      F.IsSetMultilinear blk S → F.productDepth ≤ Δ →
      relRank blk (wordPos w ∩ S) (wordNeg w ∩ S) F.polynomial ≤
        F.nodeCount * 2 ^ (-(k * (S.card : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20)) from
    H Δ hΔ hF hFΔ
  intro Δ hΔ
  induction Δ, hΔ using Nat.le_induction with
  | base =>
    intro F S hF hFΔ
    have e1 : (1 / ((2 : ℝ) ^ 1 - 1)) = 1 := by norm_num
    simp only [e1, Real.rpow_one]
    refine relRank_polynomial_le_nodeCount_mul _ _ 1 (fun U => 2 ^ (-(k * (U.card : ℝ) / 20)))
      (fun U => by positivity) (fun U hU f => (hsmall U hU f).trans_eq (by ring_nf)) ?_ hF hFΔ
    intro m G T hT hG hGΔ
    have hG0 (j : Fin m) : (G j).productDepth = 0 := Nat.lt_one_iff.mp (hGΔ j)
    rw [polynomial_mul]
    refine (relRank_prod_le_two_rpow _ _ Finset.univ T _ (hT.set_pairwise _)
      (fun j _ => (hG j).isSetMultilinear_polynomial) ((k : ℝ) / 20) fun j _ => ?_).trans ?_
    · rcases (hG j).card_le_one_or_polynomial_eq_zero (hG0 j) with h | h
      · exact hsmall _ h _
      · rw [h, relRank_zero]
        positivity
    · rw [show -(((Finset.univ.biUnion T).card : ℝ) * (k / 20)) =
          -(k * (Finset.univ.biUnion T).card / 20) by ring]
      exact le_mul_of_one_le_left (by positivity) (hnode _)
  | succ Δ hΔ ih =>
    intro F S hF hFΔ
    refine relRank_polynomial_le_nodeCount_mul _ _ (Δ + 1)
      (fun U => 2 ^ (-(k * (U.card : ℝ) ^ (1 / (2 ^ (Δ + 1) - 1 : ℝ)) / 20)))
      (fun U => by positivity) (fun U hU f => ?_) ?_ hF hFΔ
    · rw [rpow_of_le_one (by omega) hU]
      exact (hsmall U hU f).trans_eq (by ring_nf)
    intro m G T hT hG hGΔ
    have hGΔ' (j : Fin m) : (G j).productDepth ≤ Δ := Nat.lt_succ_iff.mp (hGΔ j)
    have hGp : ∀ j ∈ (Finset.univ : Finset (Fin m)),
        MvPolynomial.IsSetMultilinear blk (T j) (G j).polynomial :=
      fun j _ => (hG j).isSetMultilinear_polynomial
    have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint T :=
      hT.set_pairwise _
    rw [polynomial_mul]
    rcases (Finset.univ.biUnion T).eq_empty_or_nonempty with hU0 | hUne
    · rw [hU0, Finset.card_empty, Nat.cast_zero,
        Real.zero_rpow (one_div_two_pow_sub_one_pos (by omega)).ne', mul_zero, zero_div,
        neg_zero, Real.rpow_zero, mul_one]
      exact (relRank_le_one _ _ _ _).trans (hnode _)
    set U := Finset.univ.biUnion T with hU
    set M : ℝ := (U.card : ℝ) with hM
    have hM1 : 1 ≤ M := by
      rw [hM]
      exact_mod_cast hUne.card_pos
    have hM0 : 0 < M := by linarith
    set u : ℝ := 2 ^ Δ - 1 with hu
    set v : ℝ := 2 ^ (Δ + 1) - 1 with hv
    have hu1 : 1 ≤ u := by
      have := one_div_two_pow_sub_one_pos hΔ
      have h2 : (2 : ℝ) ≤ 2 ^ Δ := by
        calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ Δ := pow_le_pow_right₀ one_le_two hΔ
      linarith
    have hvu : v = 2 * u + 1 := by
      rw [hv, hu, pow_succ]
      ring
    have hv0 : 0 < v := by linarith
    have hu0 : u ≠ 0 := (by linarith : (0 : ℝ) < u).ne'
    have hv0' : v ≠ 0 := hv0.ne'
    set τ : ℝ := M ^ (u / v) with hτ
    have hτ1 : 1 ≤ τ := Real.one_le_rpow hM1 (by positivity)
    by_cases htype : ∃ j, τ < (T j).card
    · -- Type 1: some factor lives on more than `τ` blocks; apply the induction hypothesis to it.
      obtain ⟨j, hj⟩ := htype
      refine (relRank_prod_le_of_mem _ _ T _ hdisj hGp (Finset.mem_univ j)).trans ?_
      refine (ih (hG j) (hGΔ' j)).trans ?_
      refine mul_le_mul (by exact_mod_cast nodeCount_le_nodeCount_mul G j)
        (Real.rpow_le_rpow_of_exponent_le one_le_two ?_) (by positivity) (by positivity)
      have hMτ : M ^ (1 / v) = τ ^ (1 / u) := by
        rw [hτ, ← Real.rpow_mul hM0.le]
        congr 1
        field_simp
      have h := Real.rpow_le_rpow (by positivity) hj.le (by positivity : (0 : ℝ) ≤ 1 / u)
      rw [← hMτ] at h
      rw [neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k))
        (by norm_num)
    · -- Type 2: every factor lives on at most `τ` blocks; the word makes each of them small.
      push Not at htype
      have hτ2 : τ ^ 2 ≤ M := by
        rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
        calc M ^ (u / v * ((2 : ℕ) : ℝ)) ≤ M ^ (1 : ℝ) := by
              refine Real.rpow_le_rpow_of_exponent_le hM1 ?_
              rw [Nat.cast_two, div_mul_eq_mul_div, div_le_one hv0]
              linarith
          _ = M := Real.rpow_one M
      have hk' : 10 * τ ^ 2 ≤ k := by
        have h1 := hcard U
        have h2 : (10 : ℝ) * d ≤ k := by exact_mod_cast hk
        linarith
      refine (relRank_prod_le_two_rpow _ _ Finset.univ T _ hdisj hGp ((k : ℝ) / (20 * τ ^ 2))
        fun j _ => relRank_le_two_rpow_of_card_le hblk hw (htype j) (by positivity) hk' _).trans ?_
      have hMv : M / τ ^ 2 = M ^ (1 / v) := by
        have he : 1 - u / v * ((2 : ℕ) : ℝ) = 1 / v := by
          field_simp
          rw [hvu]
          push_cast
          ring
        rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le,
          ← Real.rpow_one_sub' hM0.le (by rw [he]; positivity), he]
      rw [← hU, ← hM, show -(M * (k / (20 * τ ^ 2))) = -(k * M ^ (1 / v) / 20) by
        rw [← hMv]
        field_simp]
      exact le_mul_of_one_le_left (by positivity) (hnode _)

/-- **LST Claim 16** on all blocks: with the hypotheses of `relRank_polynomial_le`, a
set-multilinear formula of product-depth at most `Δ` on all `d` blocks has relative rank at most
`nodeCount · 2 ^ (-(k d ^ (1 / (2 ^ Δ - 1)) / 20))`. -/
theorem IsSetMultilinear.relRank_polynomial_le_univ {k : ℕ} {w : Fin d → ℤ}
    (hblk : ∀ i, Fintype.card {x : Fin n // blk x = i} = 2 ^ (w i).natAbs) (hk : 10 * d ≤ k)
    (hw : ∀ i, w i = ⌊(k : ℝ) / √2⌋ ∨ w i = -k) {Δ : ℕ} (hΔ : 1 ≤ Δ) {F : SPFormula K n}
    (hF : F.IsSetMultilinear blk Finset.univ) (hFΔ : F.productDepth ≤ Δ) :
    relRank blk (wordPos w) (wordNeg w) F.polynomial ≤
      F.nodeCount * 2 ^ (-(k * (d : ℝ) ^ (1 / (2 ^ Δ - 1 : ℝ)) / 20)) := by
  have h := hF.relRank_polynomial_le hblk hk hw hΔ hFΔ
  rwa [Finset.inter_univ, Finset.inter_univ, Finset.card_univ, Fintype.card_fin] at h

end SPFormula

end Cslib.Circuits.Arithmetic
