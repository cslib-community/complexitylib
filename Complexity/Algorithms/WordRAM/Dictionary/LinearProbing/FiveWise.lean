/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.PMF.Expect

/-!
# Constant-independence cluster bounds for linear probing

This file proves the probabilistic core of constant-time linear probing under $5$-wise independent
hashing, adapting [Pagh, Pagh and Ružić, *Linear Probing with Constant Independence*, *SIAM J.
Comput.* 39(3):1107–1120, 2009, Section 2.3 (Lemma 2.1, pp. 1110–1111) and Section 4 (Lemma 4.1,
Theorem 4.3, and Theorem 4.5, pp. 1114–1118)][PaghPaghRuzic2009]; see also [Cormen, Leiserson,
Rivest and Stein, *Introduction to Algorithms*, Section 11.4][CLRS2009] and [Vadhan,
*Pseudorandomness*, Section 3.5][Vadhan2012].

## Source statement and proof adaptation

In `[PaghPaghRuzic2009]`, Lemma 2.1 (Section 2.3, pp. 1110–1111) shows that for a stored key set
$S \subseteq U$ of size $n$, a $5$-wise independent hash family $\mathcal{H} : U \to [r]$ with
maximum load $\bar{\alpha} < 1$, any subset $Q \subset [r]$ of size $q$, any $d > 0$, and any fixed
$x \in U \setminus S$, conditioning on $h(x) = \rho$ leaves a $4$-wise independent family on
$U \setminus \{x\}$ and the centered fourth-moment Markov bound gives
$\Pr[|\{y \in S : h(y) \in h(x) + Q\}| \ge \bar{\alpha} q + d] < 4 \bar{\alpha} q^2 / d^4$.
Combining Lemma 2.1 with the occupied-run witness in Lemma 4.1 (Section 4, p. 1114), Theorem 4.3
(Section 4.1, pp. 1115–1116) and Theorem 4.5 (Section 4.2, p. 1118) bound the expected number of
probes per operation by $O((1 - \bar{\alpha})^{-5/2})$ and $O((1 - \bar{\alpha})^{-13/6})$ for any
maximum load $\bar{\alpha} < 1$.

Our formalization specializes to a power-of-$2$ table of size $m = 2^M \ge 8 n_{\max}$ (exact
uniform load factor $\bar{\alpha} = \alpha = \#S / 2^M \le 1/8$) and an exact uniform $5$-wise
independent family $h : \iota \to X \to \mathrm{Fin}(2^M)$ (`IsKWiseIndependentHash 5 h`), using an
original simplified dyadic-window proof adaptation in place of the interval-grid decompositions of
Lemmas 4.2 and 4.4 in `[PaghPaghRuzic2009]`:
1. **Left-anchored cluster witness (`HasClusterWitness`, adapting the proof of Lemma 4.1,
   p. 1114):**
   If probing key $u$ from $b = h_i(u)$ steps over $t \ge 1$ occupied slots belonging to
   $S = \mathrm{dom}(s) \setminus \{u\}$, walking backwards from $b$ to the nearest preceding empty
   slot yields a contiguous cyclic interval $J(b, a, \ell)$ (`cyclicInterval M b a ℓ`) of length
   $\ell = a + t \in [t, \#S]$ containing $b$ into which at least $\ell$ keys of $S$ hash.
2. **Centered dyadic-scale window (`scaleWindow`, original proof adaptation at load $\le 1/8$):**
   For the dyadic scale $j = \lfloor \log_2 \ell \rfloor + 1 \in \{1, \dots, M\}$, we have
   $2^{j-1} \le \ell < 2^j$. Every cyclic interval $J(b, a, \ell)$ containing $b$ is contained in a
   single centered window $W_j(b)$ (`scaleWindow M b j`) of size at most $2^{j+1}$
   (`cyclicInterval_subset_scaleWindow`, `card_scaleWindow_le`). Consequently, at least $2^{j-1}$
   keys of $S$ hash into $W_j(b)$, whereas at load $\#S \le 2^M / 8$ the expected load of $W_j(b)$
   is $\mu_{j,b} \le \#S \cdot 2^{j+1} / 2^M \le 2^{j-2}$, leaving deviation slack
   $2^{j-1} - \mu_{j,b} \ge 2^{j-2}$.
3. **Conditioned fourth-moment tail bound (`expect_indicator_mul_sum_pow_four_le` and
   `expect_scaleOverload_le`, adapting Lemma 2.1, pp. 1110–1111):**
   Conditioning on $h_i(u) = b$ consumes $1$ degree of independence, leaving $4$-wise independence
   on $S$. Expanding the fourth central moment via `IsKWiseIndependentHash.expect_prod` on sets
   $\mathrm{insert}\ u\ (\mathrm{image}\ t)$ of size at most $5$ bounds the scale-$j$ overload
   probability (`scaleOverload`) by $18 / (2^{j-2})^2 = 288 / 4^j$, and summing
   $\sum_{j=1}^M 2^j \cdot (288 / 4^j)$ yields the original explicit constant upper bound
   $288 = O(1)$ on the expected number of skipped occupied slots
   (`expect_probe_le_of_cluster_witness`, `tsum_uniform_probe_le_of_cluster_witness`).

## Main definitions

* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.tableLog`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.tableSize`: power-of-$2$ table bit-width
  $M = \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ and capacity $2^M$.
* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.cyclicSlotMod`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.cyclicInterval`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.scaleWindow`: cyclic slot indexing, contiguous
  cyclic intervals containing $b$, and centered dyadic-scale windows $W_j(b)$.
* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.scaleOverload`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.HasClusterWitness`: scale-$j$ window overload
  event $2^{j-1} \le \#\{x \in S \mid h_i(x) \in W_j(h_i(u))\}$ and left-anchored cluster-witness
  predicate.

## Main results

* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.eight_mul_le_tableSize`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.tableSize_le_sixteen_mul`: load-factor and
  linear-space bounds for `tableSize`.
* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.expect_indicator_mul_sum_pow_four_le`:
  fourth-moment bound for centered bucket indicators conditioned on $h_i(u) = b$ under $5$-wise
  independence.
* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.expect_scaleOverload_le`: scale-$j$ overload
  probability bound $\le 288 / 4^j$.
* `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.expect_probe_le_of_cluster_witness`,
  `Cslib.Algorithms.WordRAM.Dictionary.LinearProbing.tsum_uniform_probe_le_of_cluster_witness`:
  expected probe count $\le 288$ under `Finset.expect` and `PMF.uniformOfFintype`.

## References

* [A. Pagh, R. Pagh and M. Ružić, *Linear Probing with Constant Independence*][PaghPaghRuzic2009]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 11.4][CLRS2009]
* [S. P. Vadhan, *Pseudorandomness*, Section 3.5][Vadhan2012]
-/

public section

namespace Cslib.Algorithms.WordRAM.Dictionary.LinearProbing

open Cslib.Probability Finset Fintype
open scoped BigOperators ENNReal

/-! ## Section 1: Table size parameters and load-factor bounds -/

/-- Base-2 logarithm $M = \lceil \log_2 \max(8 n_{\max}, 8) \rceil$ of the linear-probing table
size, ensuring $M \ge 3$ and $8 n_{\max} \le 2^M < 16 \max(n_{\max}, 1)$. -/
@[expose] def tableLog (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max (8 * n_max) 8)

/-- Power-of-$2$ table size $m = 2^{\mathrm{tableLog}(n_{\max})}$. -/
@[expose] def tableSize (n_max : ℕ) : ℕ :=
  2 ^ tableLog n_max

/-- `tableLog n_max` is always at least `3`. -/
theorem three_le_tableLog (n_max : ℕ) : 3 ≤ tableLog n_max := by
  dsimp only [tableLog]
  have h8 : 8 ≤ max (8 * n_max) 8 := le_max_right _ _
  calc 3 = Nat.clog 2 8 := by decide
    _ ≤ Nat.clog 2 (max (8 * n_max) 8) := Nat.clog_mono_right 2 h8

/-- `tableLog n_max` is always positive. -/
theorem tableLog_pos (n_max : ℕ) : 0 < tableLog n_max := by
  have := three_le_tableLog n_max
  omega

/-- `tableSize n_max` is always positive. -/
theorem tableSize_pos (n_max : ℕ) : 0 < tableSize n_max := by
  dsimp only [tableSize]
  positivity

/-- `tableSize n_max` is always at least `8`. -/
theorem eight_le_tableSize (n_max : ℕ) : 8 ≤ tableSize n_max := by
  dsimp only [tableSize]
  calc 8 = 2 ^ 3 := by decide
    _ ≤ 2 ^ tableLog n_max := Nat.pow_le_pow_right (by decide) (three_le_tableLog n_max)

/-- The table size is at least $8 n_{\max}$ (load factor $\le 1/8$). -/
theorem eight_mul_le_tableSize (n_max : ℕ) : 8 * n_max ≤ tableSize n_max := by
  dsimp only [tableSize, tableLog]
  calc 8 * n_max ≤ max (8 * n_max) 8 := le_max_left _ _
    _ ≤ 2 ^ Nat.clog 2 (max (8 * n_max) 8) := Nat.le_pow_clog (by decide) _

/-- `n_max` is strictly less than `tableSize n_max`, so at least $7/8$ of the table slots are
always empty. -/
theorem n_max_lt_tableSize (n_max : ℕ) : n_max < tableSize n_max := by
  have h8 := eight_le_tableSize n_max
  have hmul := eight_mul_le_tableSize n_max
  omega

/-- `tableSize n_max` is strictly less than $16 \max(n_{\max}, 1)$. -/
theorem tableSize_lt_sixteen_mul (n_max : ℕ) : tableSize n_max < 16 * max n_max 1 := by
  dsimp only [tableSize, tableLog]
  have hpos : 1 < max (8 * n_max) 8 := by
    have : 8 ≤ max (8 * n_max) 8 := le_max_right _ _
    omega
  have hlt : 2 ^ (Nat.clog 2 (max (8 * n_max) 8) - 1) < max (8 * n_max) 8 :=
    Nat.pow_pred_clog_lt_self (by decide) hpos
  have hclog_pos : 1 ≤ Nat.clog 2 (max (8 * n_max) 8) := by
    have := three_le_tableLog n_max
    dsimp only [tableLog] at this
    omega
  have hpow : 2 ^ Nat.clog 2 (max (8 * n_max) 8) =
      2 * 2 ^ (Nat.clog 2 (max (8 * n_max) 8) - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hclog_pos, Nat.pow_succ']
  have hmax : max (8 * n_max) 8 = 8 * max n_max 1 := by omega
  omega

/-- `tableSize n_max` is at most $16 \max(n_{\max}, 1) = O(n_{\max})$. -/
theorem tableSize_le_sixteen_mul (n_max : ℕ) : tableSize n_max ≤ 16 * max n_max 1 :=
  le_of_lt (tableSize_lt_sixteen_mul n_max)

/-! ## Section 2: Fourth central moment under $5$-wise independence conditioned on $h_i(u) = b$ -/

/-- Tuples of `n` elements of `S` with at most `m ≤ n` distinct entries factor through `Fin m`, so
there are at most `m ^ n * #S ^ m` of them. -/
private theorem card_filter_card_image_le {X : Type*} [DecidableEq X] (S : Finset X) {m n : ℕ}
    (hmn : m ≤ n) :
    #{t ∈ piFinset fun _ : Fin n => S | #(univ.image t) ≤ m} ≤ m ^ n * #S ^ m := by
  classical
  calc #{t ∈ piFinset fun _ : Fin n => S | #(univ.image t) ≤ m}
      ≤ #(((piFinset fun _ : Fin n => (univ : Finset (Fin m))) ×ˢ
          (piFinset fun _ : Fin m => S)).image fun q => q.2 ∘ q.1) := by
        refine card_le_card fun t ht => ?_
        rw [mem_filter, mem_piFinset] at ht
        obtain ⟨htS, hcard⟩ := ht
        set I := univ.image t
        let e := I.equivFin
        have hmem (j : Fin n) : t j ∈ I := mem_image_of_mem t (mem_univ j)
        let v (r : Fin m) : X := if hr : r.1 < #I then (e.symm ⟨r, hr⟩).1 else
          t ⟨0, lt_of_lt_of_le (Nat.zero_lt_of_lt r.2) hmn⟩
        refine mem_image.2 ⟨(fun j => Fin.castLE hcard (e ⟨t j, hmem j⟩), v), ?_, ?_⟩
        · refine mem_product.2 ⟨by simp, mem_piFinset.2 fun r => ?_⟩
          by_cases hr : r.1 < #I
          · obtain ⟨j, -, hj⟩ := mem_image.1 (e.symm ⟨r, hr⟩).2
            simp only [v, hr, ↓reduceDIte, ← hj]
            exact htS j
          · simp only [v, hr, ↓reduceDIte]
            exact htS _
        · funext j
          have hlt : (Fin.castLE hcard (e ⟨t j, hmem j⟩)).1 < #I := (e ⟨t j, hmem j⟩).2
          simp only [Function.comp_apply, v, hlt, ↓reduceDIte]
          have : (⟨(Fin.castLE hcard (e ⟨t j, hmem j⟩)).1, hlt⟩ : Fin #I) = e ⟨t j, hmem j⟩ :=
            Fin.ext rfl
          rw [this, Equiv.symm_apply_apply]
    _ ≤ m ^ n * #S ^ m := card_image_le.trans (by simp [card_piFinset])

/-- Centered indicator of a bucket subset `W ⊆ Y`: `1 - #W / |Y|` on `W` and `- #W / |Y|` outside
`W`. -/
@[expose] noncomputable def bucketCentered {Y : Type*} [Fintype Y] [DecidableEq Y]
    (W : Finset Y) (y : Y) : ℝ :=
  (if y ∈ W then (1 : ℝ) else 0) - (#W : ℝ) / (Fintype.card Y : ℝ)

/-- The uniform expectation of `bucketCentered W` over a nonempty finite type `Y` is `0`. -/
theorem expect_bucketCentered {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (W : Finset Y) :
    𝔼 y : Y, bucketCentered W y = 0 := by
  have hpos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  rw [Fintype.expect_eq_sum_div_card]
  simp only [bucketCentered, sum_sub_distrib, sum_boole, filter_mem_eq_inter, univ_inter,
    sum_const, card_univ, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ hpos.ne', sub_self, zero_div]

/-- `bucketCentered W y` always has absolute value at most `1`. -/
theorem abs_bucketCentered_le_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (W : Finset Y) (y : Y) :
    |bucketCentered W y| ≤ 1 := by
  have hcard : (#W : ℝ) ≤ (Fintype.card Y : ℝ) := by
    exact_mod_cast W.card_le_univ
  have hp0 : 0 ≤ (#W : ℝ) / (Fintype.card Y : ℝ) := by positivity
  have hp1 : (#W : ℝ) / (Fintype.card Y : ℝ) ≤ 1 := div_le_one_of_le₀ hcard (by positivity)
  dsimp only [bucketCentered]
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

/-- The second moment of `bucketCentered W` is at most `p = #W / |Y|`. -/
theorem expect_bucketCentered_sq_le {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (W : Finset Y) :
    𝔼 y : Y, (bucketCentered W y) ^ 2 ≤ (#W : ℝ) / (Fintype.card Y : ℝ) := by
  set p : ℝ := (#W : ℝ) / (Fintype.card Y : ℝ)
  have hpos : (0 : ℝ) < Fintype.card Y := Nat.cast_pos.mpr Fintype.card_pos
  have hp0 : 0 ≤ p := by positivity
  have hcard : (#W : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast W.card_le_univ
  have hp1 : p ≤ 1 := div_le_one_of_le₀ hcard (by positivity)
  have hle_pt (y : Y) : (bucketCentered W y) ^ 2 ≤
      (if y ∈ W then (1 : ℝ) else 0) * (1 - p) + (1 - (if y ∈ W then (1 : ℝ) else 0)) * p ^ 2 := by
    dsimp only [bucketCentered, p]
    split_ifs <;> nlinarith
  have hmean : (𝔼 y : Y, if y ∈ W then (1 : ℝ) else 0) = p := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [sum_boole, filter_mem_eq_inter, univ_inter, p]
  calc 𝔼 y : Y, (bucketCentered W y) ^ 2
      ≤ 𝔼 y : Y, ((if y ∈ W then (1 : ℝ) else 0) * (1 - p) +
          (1 - (if y ∈ W then (1 : ℝ) else 0)) * p ^ 2) :=
        expect_le_expect fun y _ => hle_pt y
    _ = (𝔼 y : Y, if y ∈ W then (1 : ℝ) else 0) * (1 - p) +
          (1 - (𝔼 y : Y, if y ∈ W then (1 : ℝ) else 0)) * p ^ 2 := by
        rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
        simp only [sum_add_distrib, ← sum_mul, add_div, mul_div_right_comm, sub_div,
          sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
        rw [div_self hpos.ne']
    _ = p * (1 - p) + (1 - p) * p ^ 2 := by rw [hmean]
    _ ≤ p := by nlinarith

/-- Any moment of degree `c ≥ 2` of `bucketCentered W` has absolute value at most
`p = #W / |Y|`. -/
theorem abs_expect_bucketCentered_pow_le {Y : Type*} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (W : Finset Y) {c : ℕ} (hc : 2 ≤ c) :
    |𝔼 y : Y, (bucketCentered W y) ^ c| ≤ (#W : ℝ) / (Fintype.card Y : ℝ) := by
  refine (abs_expect_le _ _).trans ((expect_le_expect fun y _ => ?_).trans
    (expect_bucketCentered_sq_le W))
  rw [abs_pow]
  have habs := abs_bucketCentered_le_one W y
  have h0 : 0 ≤ |bucketCentered W y| := abs_nonneg _
  have hpow : |bucketCentered W y| ^ c ≤ |bucketCentered W y| ^ 2 :=
    pow_le_pow_of_le_one h0 habs hc
  simpa only [sq_abs] using hpow

/-- **Conditioned fourth-moment bound under $5$-wise independence**: for a $5$-wise independent
family `h : ι → X → Y`, a finite set `S ⊆ X`, a query point `u ∉ S`, a target bucket `b : Y`, and a
window `W ⊆ Y` of density `p = #W / |Y|`, the expectation of
`(if h i u = b then 1 else 0) * (∑ x ∈ S, bucketCentered W (h i x)) ^ 4` is at most
`(𝔼 y, if y = b then 1 else 0) * (#S * p + 16 * (#S * p) ^ 2)`. -/
theorem expect_indicator_mul_sum_pow_four_le {ι X Y : Type*} [Fintype ι] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] {h : ι → X → Y}
    (hh : IsKWiseIndependentHash 5 h) (S : Finset X) {u : X} (hu : u ∉ S)
    (b : Y) (W : Finset Y) :
    let p : ℝ := (#W : ℝ) / (Fintype.card Y : ℝ)
    𝔼 i, (if h i u = b then (1 : ℝ) else 0) * (∑ x ∈ S, bucketCentered W (h i x)) ^ 4 ≤
      (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
        ((#S : ℝ) * p + 16 * ((#S : ℝ) * p) ^ 2) := by
  classical
  intro p
  have := hh.nonempty
  have hp0 : 0 ≤ p := by positivity
  have hcardW : (#W : ℝ) ≤ (Fintype.card Y : ℝ) := by exact_mod_cast W.card_le_univ
  have hp1 : p ≤ 1 := div_le_one_of_le₀ hcardW (by positivity)
  have hb0 : 0 ≤ (𝔼 y : Y, if y = b then (1 : ℝ) else 0) :=
    expect_nonneg fun y _ => by split_ifs <;> positivity
  simp only [sum_pow', mul_sum]
  rw [expect_sum_comm]
  have hterm : ∀ t ∈ piFinset fun _ : Fin 4 => S,
      𝔼 i, (if h i u = b then (1 : ℝ) else 0) * ∏ r : Fin 4, bucketCentered W (h i (t r)) ≤
        (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
          ((if #(univ.image t) ≤ 1 then p else 0) +
            (if #(univ.image t) ≤ 2 then p ^ 2 else 0)) := by
    intro t ht
    set I := univ.image t
    have htS : ∀ x ∈ I, x ∈ S := by
      intro x hx
      obtain ⟨r, -, rfl⟩ := mem_image.1 hx
      exact mem_piFinset.1 ht r
    have huI : u ∉ I := fun hmem => hu (htS u hmem)
    have hcard_I : #I ≤ 4 := card_image_le.trans (by simp)
    have hcard_ins : #(insert u I) ≤ 5 := by
      rw [card_insert_of_notMem huI]
      omega
    let f : X → Y → ℝ := fun z y =>
      if z = u then (if y = b then 1 else 0)
      else (bucketCentered W y) ^ #{r : Fin 4 | t r = z}
    have hprod_i (i : ι) :
        (if h i u = b then (1 : ℝ) else 0) * (∏ r : Fin 4, bucketCentered W (h i (t r))) =
          ∏ z ∈ insert u I, f z (h i z) := by
      rw [prod_insert huI, prod_comp (fun x => bucketCentered W (h i x)) t]
      simp only [f, ↓reduceIte]
      congr 1
      refine prod_congr rfl fun x hx => ?_
      have hne : x ≠ u := fun h => huI (h ▸ hx)
      simp only [hne, ↓reduceIte]
    simp only [hprod_i]
    rw [hh.expect_prod hcard_ins f, prod_insert huI]
    have hfu : (𝔼 y : Y, f u y) = 𝔼 y : Y, if y = b then (1 : ℝ) else 0 := by
      simp only [f, ↓reduceIte]
    have hfI : (∏ x ∈ I, 𝔼 y : Y, f x y) =
        ∏ x ∈ I, 𝔼 y : Y, (bucketCentered W y) ^ #{r : Fin 4 | t r = x} := by
      refine prod_congr rfl fun x hx => ?_
      have hne : x ≠ u := fun h => huI (h ▸ hx)
      simp only [f, hne, ↓reduceIte]
    rw [hfu, hfI]
    refine mul_le_mul_of_nonneg_left ?_ hb0
    by_cases hall2 : ∀ x ∈ I, 2 ≤ #{r : Fin 4 | t r = x}
    · have hsum_mult := card_eq_sum_card_image t (univ : Finset (Fin 4))
      have h2I : 2 * #I ≤ 4 := by
        have hle : ∑ _x ∈ I, 2 ≤ ∑ x ∈ I, #{r : Fin 4 | t r = x} :=
          sum_le_sum fun x hx => hall2 x hx
        rw [← hsum_mult, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hle
        omega
      have hI_le2 : #I ≤ 2 := by omega
      have hI_pos : 1 ≤ #I := by
        have : t 0 ∈ I := mem_image_of_mem t (mem_univ 0)
        exact Finset.card_pos.mpr ⟨t 0, this⟩
      have hprod_le : (∏ x ∈ I, 𝔼 y : Y, (bucketCentered W y) ^ #{r : Fin 4 | t r = x}) ≤
          p ^ #I := by
        refine (le_abs_self _).trans ?_
        rw [abs_prod]
        calc ∏ x ∈ I, |𝔼 y : Y, (bucketCentered W y) ^ #{r : Fin 4 | t r = x}|
            ≤ ∏ _x ∈ I, p := by
              gcongr with x hx
              exact abs_expect_bucketCentered_pow_le W (hall2 x hx)
          _ = p ^ #I := by rw [prod_const]
      by_cases hI1 : #I ≤ 1
      · have hI_eq1 : #I = 1 := by omega
        rw [hI_eq1, pow_one] at hprod_le
        simp only [hI1, hI_le2, ↓reduceIte]
        linarith [sq_nonneg p]
      · have hI_eq2 : #I = 2 := by omega
        rw [hI_eq2] at hprod_le
        simp only [hI1, hI_le2, ↓reduceIte, zero_add]
        exact hprod_le
    · push Not at hall2
      obtain ⟨x, hx, hlt2⟩ := hall2
      obtain ⟨r, -, rfl⟩ := mem_image.1 hx
      have hpos : 0 < #{r' : Fin 4 | t r' = t r} := card_pos.2 ⟨r, by simp⟩
      have hc1 : #{r' : Fin 4 | t r' = t r} = 1 := by omega
      have hzero : (∏ z ∈ I, 𝔼 y : Y, (bucketCentered W y) ^ #{r' : Fin 4 | t r' = z}) = 0 :=
        prod_eq_zero hx (by simp only [hc1, pow_one, expect_bucketCentered])
      rw [hzero]
      positivity
  calc ∑ t ∈ piFinset (fun _ : Fin 4 => S),
        𝔼 i, (if h i u = b then (1 : ℝ) else 0) * ∏ r : Fin 4, bucketCentered W (h i (t r))
      ≤ ∑ t ∈ piFinset (fun _ : Fin 4 => S),
          (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
            ((if #(univ.image t) ≤ 1 then p else 0) +
              (if #(univ.image t) ≤ 2 then p ^ 2 else 0)) :=
        sum_le_sum hterm
    _ = (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
          ((∑ t ∈ piFinset (fun _ : Fin 4 => S), if #(univ.image t) ≤ 1 then p else 0) +
            (∑ t ∈ piFinset (fun _ : Fin 4 => S), if #(univ.image t) ≤ 2 then p ^ 2 else 0)) := by
        rw [← mul_sum, sum_add_distrib]
    _ = (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
          ((#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 1} : ℝ) * p +
            (#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 2} : ℝ) * p ^ 2) := by
        simp only [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    _ ≤ (𝔼 y : Y, if y = b then (1 : ℝ) else 0) *
          ((#S : ℝ) * p + 16 * ((#S : ℝ) * p) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hb0
        have hc1 : (#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 1} : ℝ) ≤ #S := by
          have h1 := card_filter_card_image_le S (m := 1) (n := 4) (by decide)
          simpa using (Nat.cast_le (α := ℝ)).mpr h1
        have hc2 : (#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 2} : ℝ) ≤
            16 * (#S : ℝ) ^ 2 := by
          have h2 := card_filter_card_image_le S (m := 2) (n := 4) (by decide)
          exact_mod_cast h2
        have h1 : (#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 1} : ℝ) * p ≤
            (#S : ℝ) * p := mul_le_mul_of_nonneg_right hc1 hp0
        have h2 : (#{t ∈ piFinset (fun _ : Fin 4 => S) | #(univ.image t) ≤ 2} : ℝ) * p ^ 2 ≤
            16 * (#S : ℝ) ^ 2 * p ^ 2 := mul_le_mul_of_nonneg_right hc2 (sq_nonneg p)
        linarith

/-! ## Section 3: Cyclic intervals, scale windows, and expected probe bound -/

/-- Slot in `Fin (2 ^ M)` corresponding to natural number `x` modulo `2 ^ M`. -/
@[expose] def cyclicSlotMod (M : ℕ) (x : ℕ) : Fin (2 ^ M) :=
  ⟨x % 2 ^ M, Nat.mod_lt _ (by positivity)⟩

/-- Contiguous cyclic interval of length `len` starting `a` slots before `b` in `Fin (2 ^ M)`:
$\{(b - a + \mathrm{idx}) \bmod 2^M \mid 0 \le \mathrm{idx} < \mathrm{len}\}$. -/
@[expose] def cyclicInterval (M : ℕ) (b : Fin (2 ^ M)) (a len : ℕ) : Finset (Fin (2 ^ M)) :=
  (Finset.range len).image fun idx => cyclicSlotMod M (b.val + 2 ^ M * (a + 1) - a + idx)

/-- Centered dyadic-scale window $W_j(b)$ of width $2^{j+1}$ around $b$ in `Fin (2 ^ M)`:
$\{(b - 2^j + d) \bmod 2^M \mid 0 \le d < 2^{j+1}\}$. -/
@[expose] def scaleWindow (M : ℕ) (b : Fin (2 ^ M)) (j : ℕ) : Finset (Fin (2 ^ M)) :=
  (Finset.range (2 ^ (j + 1))).image fun d =>
    cyclicSlotMod M (b.val + 2 ^ M * 2 ^ j - 2 ^ j + d)

/-- The scale window `scaleWindow M b j` has at most `2 ^ (j + 1)` elements. -/
theorem card_scaleWindow_le (M : ℕ) (b : Fin (2 ^ M)) (j : ℕ) :
    #(scaleWindow M b j) ≤ 2 ^ (j + 1) := by
  dsimp only [scaleWindow]
  exact card_image_le.trans (by simp)

/-- Every cyclic interval `cyclicInterval M b a len` with `a < 2 ^ j` and `len ≤ 2 ^ j` is a
subset of the centered window `scaleWindow M b j`. -/
theorem cyclicInterval_subset_scaleWindow {M : ℕ} (b : Fin (2 ^ M)) {a len j : ℕ}
    (ha : a < 2 ^ j) (hlen : len ≤ 2 ^ j) :
    cyclicInterval M b a len ⊆ scaleWindow M b j := by
  intro y hy
  simp only [cyclicInterval, mem_image, mem_range] at hy
  obtain ⟨idx, hidx, rfl⟩ := hy
  simp only [scaleWindow, mem_image, mem_range]
  refine ⟨2 ^ j - a + idx, ?_, ?_⟩
  · rw [Nat.pow_succ]
    omega
  · apply Fin.ext
    simp only [cyclicSlotMod]
    have h1 : 1 ≤ 2 ^ M := Nat.one_le_two_pow
    have hmul : 2 ^ M * 2 ^ j = 2 ^ M * (a + 1) + 2 ^ M * (2 ^ j - (a + 1)) := by
      rw [← Nat.mul_add, Nat.add_sub_cancel' (by omega)]
    have ha_le : a ≤ 2 ^ M * (a + 1) := by
      calc a ≤ 1 * (a + 1) := by omega
        _ ≤ 2 ^ M * (a + 1) := Nat.mul_le_mul_right (a + 1) h1
    have hj_le : 2 ^ j ≤ 2 ^ M * 2 ^ j := by
      calc 2 ^ j = 1 * 2 ^ j := (Nat.one_mul _).symm
        _ ≤ 2 ^ M * 2 ^ j := Nat.mul_le_mul_right (2 ^ j) h1
    have heq : b.val + 2 ^ M * 2 ^ j - 2 ^ j + (2 ^ j - a + idx) =
        (b.val + 2 ^ M * (a + 1) - a + idx) + 2 ^ M * (2 ^ j - (a + 1)) := by
      omega
    rw [heq, Nat.add_mul_mod_self_left]

/-- Scale-$j$ window overload event: at least $2^{j-1}$ keys of $S$ hash into the centered window
`scaleWindow M (h i u) j` around $h_i(u)$. -/
@[expose] def scaleOverload {ι X : Type*} (M : ℕ) (h : ι → X → Fin (2 ^ M))
    (S : Finset X) (u : X) (j : ℕ) (i : ι) : Prop :=
  2 ^ (j - 1) ≤ #(S.filter fun x => h i x ∈ scaleWindow M (h i u) j)

instance instDecidablePredScaleOverload {ι X : Type*} (M : ℕ) (h : ι → X → Fin (2 ^ M))
    (S : Finset X) (u : X) (j : ℕ) : DecidablePred (scaleOverload M h S u j) :=
  fun _ => inferInstanceAs (Decidable (_ ≤ _))

/-- Pointwise sum identity for `bucketCentered W`: summing `bucketCentered W (g x)` over `x ∈ S`
equals `#(S.filter (g · ∈ W)) - #S * (#W / |Y|)`. -/
private theorem sum_bucketCentered_eq {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset X) (W : Finset Y) (g : X → Y) :
    ∑ x ∈ S, bucketCentered W (g x) =
      (#(S.filter fun x => g x ∈ W) : ℝ) - (#S : ℝ) * ((#W : ℝ) / (Fintype.card Y : ℝ)) := by
  simp only [bucketCentered, sum_sub_distrib, sum_boole, sum_const, nsmul_eq_mul]

/-- **Scale-$j$ overload probability bound**: when `8 * n_max ≤ 2 ^ M`, `#S ≤ n_max`, `u ∉ S`,
`hh : IsKWiseIndependentHash 5 h`, and `1 ≤ j`, the probability of `scaleOverload M h S u j` is at
most `288 / (2 ^ j : ℝ) ^ 2`. -/
theorem expect_scaleOverload_le {ι X : Type*} [Fintype ι]
    {M n_max j : ℕ} {h : ι → X → Fin (2 ^ M)}
    (hh : IsKWiseIndependentHash 5 h) (S : Finset X) {u : X} (hu : u ∉ S)
    (hS : #S ≤ n_max) (hM : 8 * n_max ≤ 2 ^ M) (hj : 1 ≤ j) :
    (𝔼 i, if scaleOverload M h S u j i then (1 : ℝ) else 0) ≤
      288 / ((2 ^ j : ℝ) ^ 2) := by
  have := hh.nonempty
  set δ : ℝ := (2 ^ (j - 1) : ℝ) / 2
  have hpow_pos : (0 : ℝ) < 2 ^ (j - 1) := by positivity
  have hδ_pos : 0 < δ := by dsimp only [δ]; positivity
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by
    dsimp only [δ]
    have h1 : (1 : ℝ) ≤ (2 ^ (j - 1) : ℝ) := by
      exact_mod_cast (Nat.one_le_two_pow (n := j - 1))
    linarith
  have h2j_eq : (2 ^ j : ℝ) = 4 * δ := by
    have hj_eq : j = (j - 1) + 1 := by omega
    conv_lhs => rw [hj_eq, pow_succ]
    dsimp only [δ]
    ring
  have hcardY : (Fintype.card (Fin (2 ^ M)) : ℝ) = 2 ^ M := by simp
  have h2M_pos : (0 : ℝ) < 2 ^ M := by positivity
  have hmean_le (b : Fin (2 ^ M)) :
      (#S : ℝ) * ((#(scaleWindow M b j) : ℝ) / (Fintype.card (Fin (2 ^ M)) : ℝ)) ≤ δ := by
    rw [hcardY, ← mul_div_assoc, div_le_iff₀ h2M_pos]
    have hW : (#(scaleWindow M b j) : ℝ) ≤ (2 ^ (j + 1) : ℝ) := by
      exact_mod_cast card_scaleWindow_le M b j
    have hj1 : (2 ^ (j + 1) : ℝ) = 4 * (2 ^ (j - 1) : ℝ) := by
      have : j + 1 = (j - 1) + 2 := by omega
      rw [this, pow_add]
      ring
    have hSn : (#S : ℝ) ≤ n_max := by exact_mod_cast hS
    have h8n : (8 * (n_max : ℝ)) ≤ 2 ^ M := by exact_mod_cast hM
    calc (#S : ℝ) * (#(scaleWindow M b j) : ℝ)
        ≤ (n_max : ℝ) * (4 * (2 ^ (j - 1) : ℝ)) := by
          rw [← hj1]
          exact mul_le_mul hSn hW (by positivity) (by positivity)
      _ = (8 * (n_max : ℝ)) * δ := by dsimp only [δ]; ring
      _ ≤ δ * (2 ^ M : ℝ) := by nlinarith
  have hpt_le (i : ι) :
      δ ^ 4 * (if scaleOverload M h S u j i then (1 : ℝ) else 0) ≤
        ∑ b : Fin (2 ^ M),
          (if h i u = b then (1 : ℝ) else 0) *
            (∑ x ∈ S, bucketCentered (scaleWindow M b j) (h i x)) ^ 4 := by
    have hsum_b :
        (∑ b : Fin (2 ^ M),
          (if h i u = b then (1 : ℝ) else 0) *
            (∑ x ∈ S, bucketCentered (scaleWindow M b j) (h i x)) ^ 4) =
          (∑ x ∈ S, bucketCentered (scaleWindow M (h i u) j) (h i x)) ^ 4 := by
      simp only [boole_mul, Fintype.sum_ite_eq]
    rw [hsum_b]
    by_cases hov : scaleOverload M h S u j i
    · simp only [hov, ↓reduceIte, mul_one]
      have hov_real : (2 ^ (j - 1) : ℝ) ≤
          (#(S.filter fun x => h i x ∈ scaleWindow M (h i u) j) : ℝ) := by
        exact_mod_cast hov
      have hsum_eq := sum_bucketCentered_eq S (scaleWindow M (h i u) j) (h i)
      have hm := hmean_le (h i u)
      have hdiff : δ ≤ ∑ x ∈ S, bucketCentered (scaleWindow M (h i u) j) (h i x) := by
        rw [hsum_eq]
        have : (2 ^ (j - 1) : ℝ) = 2 * δ := by dsimp only [δ]; ring
        linarith
      exact pow_le_pow_left₀ hδ_pos.le hdiff 4
    · simp only [hov, ↓reduceIte, mul_zero]
      positivity
  have hexp_b (b : Fin (2 ^ M)) :
      𝔼 i, (if h i u = b then (1 : ℝ) else 0) *
          (∑ x ∈ S, bucketCentered (scaleWindow M b j) (h i x)) ^ 4 ≤
        (𝔼 y : Fin (2 ^ M), if y = b then (1 : ℝ) else 0) * (18 * δ ^ 2) := by
    have h4 := expect_indicator_mul_sum_pow_four_le hh S hu b (scaleWindow M b j)
    refine h4.trans (mul_le_mul_of_nonneg_left ?_
      (expect_nonneg fun y _ => by split_ifs <;> positivity))
    set μ := (#S : ℝ) * ((#(scaleWindow M b j) : ℝ) / (Fintype.card (Fin (2 ^ M)) : ℝ))
    have hμ_le : μ ≤ δ := hmean_le b
    have hμ_nonneg : 0 ≤ μ := by dsimp only [μ]; positivity
    have hμ_sq : μ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hμ_nonneg hμ_le 2
    have hδ_le_2sq : δ ≤ 2 * δ ^ 2 := by nlinarith
    linarith
  have hsum_exp_b :
      (∑ b : Fin (2 ^ M), (𝔼 y : Fin (2 ^ M), if y = b then (1 : ℝ) else 0) * (18 * δ ^ 2)) =
        18 * δ ^ 2 := by
    rw [← sum_mul]
    have hsum1 : (∑ b : Fin (2 ^ M), 𝔼 y : Fin (2 ^ M), if y = b then (1 : ℝ) else 0) = 1 := by
      rw [← expect_sum_comm]
      simp only [Fintype.sum_ite_eq, Fintype.expect_const]
    rw [hsum1, one_mul]
  have hmarkov :
      δ ^ 4 * (𝔼 i, if scaleOverload M h S u j i then (1 : ℝ) else 0) ≤ 18 * δ ^ 2 := by
    calc δ ^ 4 * (𝔼 i, if scaleOverload M h S u j i then (1 : ℝ) else 0)
        = 𝔼 i, δ ^ 4 * (if scaleOverload M h S u j i then (1 : ℝ) else 0) := by
          rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, ← mul_sum,
            mul_div_assoc]
      _ ≤ 𝔼 i, ∑ b : Fin (2 ^ M),
            (if h i u = b then (1 : ℝ) else 0) *
              (∑ x ∈ S, bucketCentered (scaleWindow M b j) (h i x)) ^ 4 :=
          expect_le_expect fun i _ => hpt_le i
      _ = ∑ b : Fin (2 ^ M),
            𝔼 i, (if h i u = b then (1 : ℝ) else 0) *
              (∑ x ∈ S, bucketCentered (scaleWindow M b j) (h i x)) ^ 4 :=
          expect_sum_comm _ _ _
      _ ≤ ∑ b : Fin (2 ^ M),
            (𝔼 y : Fin (2 ^ M), if y = b then (1 : ℝ) else 0) * (18 * δ ^ 2) :=
          sum_le_sum fun b _ => hexp_b b
      _ = 18 * δ ^ 2 := hsum_exp_b
  have hδ4_pos : 0 < δ ^ 4 := pow_pos hδ_pos 4
  rw [← le_div_iff₀' hδ4_pos] at hmarkov
  refine hmarkov.trans_eq ?_
  rw [h2j_eq]
  field_simp [hδ_pos.ne']
  ring

/-- Left-anchored cluster witness predicate for hash family `h` at `(S, u, i, t)`: if `1 ≤ t`,
there is a cyclic interval `cyclicInterval M (h i u) a ℓ` of length `ℓ ∈ [t, #S]` with `a < ℓ`
into which at least `ℓ` keys of `S` hash. -/
@[expose] def HasClusterWitness {ι X : Type*} {M : ℕ} (h : ι → X → Fin (2 ^ M))
    (S : Finset X) (u : X) (i : ι) (t : ℕ) : Prop :=
  1 ≤ t →
    ∃ a ℓ, a < ℓ ∧ t ≤ ℓ ∧ ℓ ≤ #S ∧
      ℓ ≤ #(S.filter fun x => h i x ∈ cyclicInterval M (h i u) a ℓ)

private theorem probe_le_sum_scaleOverload {ι X : Type*}
    {M n_max : ℕ} (h : ι → X → Fin (2 ^ M)) (S : Finset X) (u : X)
    (hS : #S ≤ n_max) (hM : 8 * n_max ≤ 2 ^ M) (i : ι) (t : ℕ)
    (hwit : HasClusterWitness h S u i t) :
    (t : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 M,
        (2 ^ j : ℝ) * (if scaleOverload M h S u j i then (1 : ℝ) else 0) := by
  by_cases ht : 1 ≤ t
  · obtain ⟨a, ℓ, ha_lt_ℓ, ht_le_ℓ, hℓ_le_S, hℓ_card⟩ := hwit ht
    have hℓ_pos : 0 < ℓ := by omega
    set j := Nat.log 2 ℓ + 1
    have hj_ge_one : 1 ≤ j := Nat.le_add_left 1 _
    have h2j1_le : 2 ^ (j - 1) ≤ ℓ := by
      dsimp only [j]
      exact Nat.pow_log_le_self 2 (by omega)
    have hℓ_lt_2j : ℓ < 2 ^ j := by
      dsimp only [j]
      exact Nat.lt_pow_succ_log_self (by decide) ℓ
    have hℓ_lt_2M : ℓ < 2 ^ M := by
      have : 1 ≤ 2 ^ M := Nat.one_le_two_pow
      omega
    have hj_le_M : j ≤ M := by
      have hpow_lt : 2 ^ (j - 1) < 2 ^ M := lt_of_le_of_lt h2j1_le hℓ_lt_2M
      have hj1_lt : j - 1 < M := (Nat.pow_lt_pow_iff_right (by decide)).mp hpow_lt
      omega
    have hj_mem : j ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨hj_ge_one, hj_le_M⟩
    have hov : scaleOverload M h S u j i := by
      dsimp only [scaleOverload]
      have hsub : cyclicInterval M (h i u) a ℓ ⊆ scaleWindow M (h i u) j :=
        cyclicInterval_subset_scaleWindow (h i u) (by omega) (by omega)
      have hfilter :
          #(S.filter fun x => h i x ∈ cyclicInterval M (h i u) a ℓ) ≤
            #(S.filter fun x => h i x ∈ scaleWindow M (h i u) j) := by
        refine card_le_card fun x hx => ?_
        simp only [mem_filter] at hx ⊢
        exact ⟨hx.1, hsub hx.2⟩
      omega
    calc (t : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast ht_le_ℓ
      _ ≤ (2 ^ j : ℝ) := by exact_mod_cast hℓ_lt_2j.le
      _ = (2 ^ j : ℝ) * (if scaleOverload M h S u j i then (1 : ℝ) else 0) := by
          simp [hov]
      _ ≤ ∑ k ∈ Finset.Icc 1 M,
            (2 ^ k : ℝ) * (if scaleOverload M h S u k i then (1 : ℝ) else 0) := by
          refine single_le_sum
            (f := fun k => (2 ^ k : ℝ) * (if scaleOverload M h S u k i then (1 : ℝ) else 0))
            (fun k _ => ?_) hj_mem
          split_ifs <;> positivity
  · have ht0 : t = 0 := by omega
    rw [ht0, Nat.cast_zero]
    refine sum_nonneg fun k _ => ?_
    split_ifs <;> positivity

private theorem sum_Icc_two_pow_mul_div_sq_eq (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2)) =
      288 - 288 / (2 ^ M : ℝ) := by
  induction M with
  | zero =>
    simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (Nat.le_add_left 1 M), ih, pow_succ']
    have hpowM : (2 ^ M : ℝ) ≠ 0 := by positivity
    field_simp [hpowM]
    ring

/-- If a nonnegative probe count `probe : ι → ℕ` satisfies the **left-anchored cluster witness**
property — every seed `i` with `1 ≤ probe i` has an occupied cyclic interval
`cyclicInterval M (h i u) a ℓ` of length `ℓ ∈ [probe i, #S]` with `0 ≤ a < ℓ` into which at
least `ℓ` keys of `S` hash — then under a `5`-wise independent hash family at load factor
`8 * n_max ≤ 2 ^ M` and `#S ≤ n_max`, the expected probe count is at most `288`. -/
theorem expect_probe_le_of_cluster_witness {ι X : Type*} [Fintype ι]
    {M n_max : ℕ} {h : ι → X → Fin (2 ^ M)}
    (hh : IsKWiseIndependentHash 5 h)
    (S : Finset X) {u : X} (hu : u ∉ S)
    (hS : #S ≤ n_max) (hM : 8 * n_max ≤ 2 ^ M)
    (probe : ι → ℕ)
    (hwit : ∀ i, HasClusterWitness h S u i (probe i)) :
    𝔼 i, (probe i : ℝ) ≤ 288 := by
  have hpt (i : ι) :
      (probe i : ℝ) ≤
        ∑ j ∈ Finset.Icc 1 M,
          (2 ^ j : ℝ) * (if scaleOverload M h S u j i then (1 : ℝ) else 0) :=
    probe_le_sum_scaleOverload h S u hS hM i (probe i) (hwit i)
  calc 𝔼 i, (probe i : ℝ)
      ≤ 𝔼 i, ∑ j ∈ Finset.Icc 1 M,
          (2 ^ j : ℝ) * (if scaleOverload M h S u j i then (1 : ℝ) else 0) :=
        expect_le_expect fun i _ => hpt i
    _ = ∑ j ∈ Finset.Icc 1 M,
          𝔼 i, (2 ^ j : ℝ) * (if scaleOverload M h S u j i then (1 : ℝ) else 0) :=
        expect_sum_comm _ _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 M, (2 ^ j : ℝ) * (288 / (2 ^ j : ℝ) ^ 2) := by
        refine sum_le_sum fun j hj => ?_
        rw [Finset.mem_Icc] at hj
        rw [Fintype.expect_eq_sum_div_card, ← mul_sum, mul_div_assoc,
          ← Fintype.expect_eq_sum_div_card]
        exact mul_le_mul_of_nonneg_left
          (expect_scaleOverload_le hh S hu hS hM hj.1) (by positivity)
    _ = 288 - 288 / (2 ^ M : ℝ) := sum_Icc_two_pow_mul_div_sq_eq M
    _ ≤ 288 := by
        have : (0 : ℝ) ≤ 288 / (2 ^ M : ℝ) := by positivity
        linarith

/-- Natural-number sum form of `expect_probe_le_of_cluster_witness`: the sum of `probe i` over all
seeds `i : ι` is at most `288 * Fintype.card ι`. -/
theorem sum_probe_le_of_cluster_witness {ι X : Type*} [Fintype ι]
    {M n_max : ℕ} {h : ι → X → Fin (2 ^ M)}
    (hh : IsKWiseIndependentHash 5 h)
    (S : Finset X) {u : X} (hu : u ∉ S)
    (hS : #S ≤ n_max) (hM : 8 * n_max ≤ 2 ^ M)
    (probe : ι → ℕ)
    (hwit : ∀ i, HasClusterWitness h S u i (probe i)) :
    (∑ i : ι, probe i) ≤ 288 * Fintype.card ι := by
  have := hh.nonempty
  have hexp := expect_probe_le_of_cluster_witness hh S hu hS hM probe hwit
  rw [Fintype.expect_eq_sum_div_card] at hexp
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hcard_pos] at hexp
  exact_mod_cast hexp

/-- `ℝ≥0∞` expectation form of `expect_probe_le_of_cluster_witness` under `PMF.uniformOfFintype`:
`∑' i, (PMF.uniformOfFintype ι) i * (probe i : ℝ≥0∞) ≤ 288`. -/
theorem tsum_uniform_probe_le_of_cluster_witness {ι X : Type*} [Fintype ι] [Nonempty ι]
    {M n_max : ℕ} {h : ι → X → Fin (2 ^ M)}
    (hh : IsKWiseIndependentHash 5 h)
    (S : Finset X) {u : X} (hu : u ∉ S)
    (hS : #S ≤ n_max) (hM : 8 * n_max ≤ 2 ^ M)
    (probe : ι → ℕ)
    (hwit : ∀ i, HasClusterWitness h S u i (probe i)) :
    (∑' i : ι, (PMF.uniformOfFintype ι) i * (probe i : ℝ≥0∞)) ≤ 288 := by
  have hsum := sum_probe_le_of_cluster_witness hh S hu hS hM probe hwit
  calc (∑' i : ι, (PMF.uniformOfFintype ι) i * (probe i : ℝ≥0∞))
      = ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ * (probe i : ℝ≥0∞) := by
        rw [tsum_fintype]
        simp [PMF.uniformOfFintype_apply]
    _ = (Fintype.card ι : ℝ≥0∞)⁻¹ * ((∑ i : ι, probe i : ℕ) : ℝ≥0∞) := by
        rw [← Finset.mul_sum, Nat.cast_sum]
    _ ≤ (Fintype.card ι : ℝ≥0∞)⁻¹ * ((288 * Fintype.card ι : ℕ) : ℝ≥0∞) := by
        gcongr
    _ = 288 := by
        push_cast
        rw [mul_comm (288 : ℝ≥0∞), ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
        · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
        · exact ENNReal.natCast_ne_top _

end Cslib.Algorithms.WordRAM.Dictionary.LinearProbing
