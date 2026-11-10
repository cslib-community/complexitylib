/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.TotallyRegular
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rigidity
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Combinatorics.KovariSosTuran
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Rigidity of totally regular matrices

A matrix is *totally regular* when all of its square submatrices are nonsingular
(`Matrix.IsTotallyRegular`); Cauchy matrices are the standard example. This module proves the
explicit rigidity lower bound of Friedman [Friedman1993] and Shokrollahi, Spielman and Stemann
[ShokrollahiSpielmanStemann1997], in the form of [Lokam2009], Theorem 2.5: an `n × n` totally
regular matrix needs at least `n ^ 2 / (4 (r + 1)) · log₂ (n / r)` changes to bring its rank down
to at most `r`. [Lokam2009] proves this for `log² n ≤ r ≤ n / 2`; here it is proved for
`n ≤ 2 ^ r` and `2 r ≤ n` (`Matrix.IsTotallyRegular.le_rigidity_of_le_two_pow`), a wider range
(see below).

The proof follows [Lokam2009], §2.2 (pp. 15–17). If few entries are changed, then by the
Kővári–Sós–Turán theorem (`Cslib.kovari_sos_turan`) some `(r + 1) × (r + 1)` submatrix contains no
changed entry (`Cslib.exists_disjoint_product_of_card_lt`, [Lokam2009], Lemma 2.4). It is a square
submatrix of the original totally regular matrix, so it is nonsingular and the changed matrix has
rank at least `r + 1`.

The general statement is for `m × n` matrices (`Matrix.IsTotallyRegular.le_rigidity`):
`n (m - r) / (2 (r + 1)) · log₂ (n / r)` changes are needed whenever `n ≤ r 2 ^ (r + 1)` (for
`r ≥ m` the bound is `0`). [Lokam2009] states Lemma 2.4 and Theorem 2.5 for square matrices and
`log² n ≤ r`, with the square of the logarithm. The same proof works under the weaker hypotheses
used here: with logarithms to base `2`, `log² n ≤ r` implies `log₂ n ≤ r`, that is `n ≤ 2 ^ r`,
which implies `n ≤ r 2 ^ (r + 1)` for `r ≥ 1`. The range is genuinely wider (`n = 64`, `r = 6`
satisfies `n ≤ 2 ^ r` but not `log² n ≤ r`); this extends the stated range of the same argument
and is not a new result. The logarithm in the bound is to base `2`; [Lokam2009] leaves the base of
`log (n / r)` unstated, and base `2` gives the strongest of the usual readings.

The library's Cauchy matrices are `1 / (x i - y j)` (`Matrix.cauchy`); [Lokam2009] uses
`1 / (x i + y j)`, which is `Matrix.cauchy x (-y)`. Both are totally regular when the nodes are
distinct and the denominators nonzero, so the bound applies to them
(`Matrix.le_rigidity_cauchy`), and to the explicit families `Matrix.cauchyNat` over fields of
characteristic zero and over `ZMod q` for primes `q ≥ 2 n`.

## Main results

* `Cslib.exists_disjoint_product_of_card_lt`: few marked positions leave an unmarked
  `(r + 1) × (r + 1)` rectangle.
* `Matrix.IsTotallyRegular.le_rigidity`: the rigidity lower bound for `m × n` totally regular
  matrices.
* `Matrix.IsTotallyRegular.le_rigidity_of_le_two_pow`: [Lokam2009], Theorem 2.5.
* `Matrix.le_rigidity_cauchy`, `Matrix.le_rigidity_cauchyNat`, `Matrix.le_rigidity_cauchyNat_zmod`:
  the bound for Cauchy matrices.

## References

* [J. Friedman, *A note on matrix rigidity*][Friedman1993]
* [Shokrollahi, Spielman, Stemann, *A remark on matrix rigidity*][ShokrollahiSpielmanStemann1997]
* [S. V. Lokam, *Complexity Lower Bounds using Linear Algebra*][Lokam2009], Lemma 2.4 and
  Theorem 2.5
-/

public section

open Finset

namespace Cslib

/-- `2 ^ (-2 w) ≤ 1 - w` for `0 ≤ w ≤ 1 / 2`: Bernoulli's inequality `(1 + x) ^ p ≤ 1 + p x` for
`p ∈ [0, 1]`, at `x = -1 / 2` and `p = 2 w` (equivalently, convexity of `p ↦ (1 / 2) ^ p`). -/
private theorem two_rpow_neg_le_one_sub {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2) :
    (2 : ℝ) ^ (-(2 * w)) ≤ 1 - w := by
  have h := rpow_one_add_le_one_add_mul_self (s := -1 / 2) (by norm_num) (p := 2 * w)
    (by linarith) (by linarith)
  calc (2 : ℝ) ^ (-(2 * w)) = (1 + -1 / 2) ^ (2 * w) := by
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
    _ ≤ 1 + 2 * w * (-1 / 2) := h
    _ = 1 - w := by ring

/-- **The numerical core of [Lokam2009], Lemma 2.4.** Let `N` positions be available and
`s < N / (2 (r + 1)) · log₂ (n / r)` of them be marked, where `n ≤ r 2 ^ (r + 1)`. Then `s < N`
and `r N ^ (r + 1) < n (N - s) ^ (r + 1)`: with `w = log₂ (n / r) / (2 (r + 1)) ∈ (0, 1 / 2]`,
`N - s > N (1 - w)` and `(1 - w) ^ (r + 1) ≥ 2 ^ (-log₂ (n / r)) = r / n`. -/
private theorem lt_and_mul_pow_lt {n r N s : ℕ} (hn : n ≤ r * 2 ^ (r + 1))
    (hs : (s : ℝ) < N / (2 * (r + 1)) * Real.logb 2 (n / r)) :
    s < N ∧ (r : ℝ) * N ^ (r + 1) < n * (N - s) ^ (r + 1) := by
  set L := Real.logb 2 (n / r) with hLdef
  set w := L / (2 * (r + 1)) with hwdef
  have hr1 : (0 : ℝ) < 2 * (r + 1) := by positivity
  have hsw : (s : ℝ) < N * w := by
    calc (s : ℝ) < N / (2 * (r + 1)) * L := hs
      _ = N * w := by rw [hwdef]; ring
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- The bound is positive, so `r ≥ 1`, `n > r` and `0 < w ≤ 1 / 2`.
  have hw : 0 < w := by
    by_contra hw
    have : (N : ℝ) * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN0 (not_lt.1 hw)
    linarith
  have hL : 0 < L := by
    rw [hwdef] at hw
    exact (div_pos_iff_of_pos_right hr1).1 hw
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [hLdef] at hL
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hnr : (0 : ℝ) < n / r := by
    refine lt_of_le_of_ne (by positivity) fun h => ?_
    rw [hLdef, ← h, Real.logb_zero] at hL
    exact lt_irrefl _ hL
  have hnpos : (0 : ℝ) < n := (div_pos_iff_of_pos_right hrpos).1 hnr
  have hLle : L ≤ r + 1 := by
    rw [hLdef, Real.logb_le_iff_le_rpow (by norm_num) hnr, div_le_iff₀ hrpos]
    have : (n : ℝ) ≤ r * 2 ^ (r + 1) := by exact_mod_cast hn
    calc (n : ℝ) ≤ r * 2 ^ (r + 1) := this
      _ = (2 : ℝ) ^ ((r : ℝ) + 1) * r := by
        rw [mul_comm, ← Real.rpow_natCast]; push_cast; ring_nf
  have hw1 : w ≤ 1 / 2 := by
    rw [hwdef, div_le_iff₀ hr1]
    linarith
  -- `N - s > N (1 - w)` and `(1 - w) ^ (r + 1) ≥ 2 ^ (-L) = r / n`.
  have hgap : (N : ℝ) * (1 - w) < N - s := by
    have : (N : ℝ) * (1 - w) = N - N * w := by ring
    linarith
  have hrn : (r : ℝ) / n ≤ (1 - w) ^ (r + 1) := by
    have h2L : (2 : ℝ) ^ (-L) = r / n := by
      rw [Real.rpow_neg (by norm_num), hLdef, Real.rpow_logb (by norm_num) (by norm_num) hnr,
        inv_div]
    calc (r : ℝ) / n = 2 ^ (-L) := h2L.symm
      _ = ((2 : ℝ) ^ (-(2 * w))) ^ (r + 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hwdef]
        congr 1
        push_cast
        field_simp
      _ ≤ (1 - w) ^ (r + 1) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (two_rpow_neg_le_one_sub hw.le hw1) _
  refine ⟨by exact_mod_cast (show (s : ℝ) < N by nlinarith), ?_⟩
  calc (r : ℝ) * N ^ (r + 1) = n * (r / n * N ^ (r + 1)) := by field_simp
    _ ≤ n * ((1 - w) ^ (r + 1) * N ^ (r + 1)) := by gcongr
    _ = n * (N * (1 - w)) ^ (r + 1) := by rw [mul_pow]; ring
    _ < n * (N - s) ^ (r + 1) := by gcongr; nlinarith

variable {α β : Type*} [Fintype α] [Fintype β]

/-- **Untouched rectangles** ([Lokam2009], Lemma 2.4). If fewer than
`n (m - r) / (2 (r + 1)) · log₂ (n / r)` positions of an `m × n` grid (`m = |α|`, `n = |β|`) are
marked, where `n ≤ r 2 ^ (r + 1)`, then some `(r + 1) × (r + 1)` rectangle contains no marked
position (for `r ≥ m` the bound is `0`, so there is nothing to prove). [Lokam2009] states the
square case `m = n` under `log² n ≤ r`; with base-`2` logarithms this implies
`n ≤ 2 ^ r ≤ r 2 ^ (r + 1)` for `r ≥ 1`, so the hypothesis here is weaker. -/
theorem exists_disjoint_product_of_card_lt (S : Finset (α × β)) {r : ℕ}
    (hn : Fintype.card β ≤ r * 2 ^ (r + 1))
    (hS : (#S : ℝ) < Fintype.card β * (Fintype.card α - r : ℕ) / (2 * (r + 1)) *
      Real.logb 2 (Fintype.card β / r)) :
    ∃ I : Finset α, ∃ J : Finset β, #I = r + 1 ∧ #J = r + 1 ∧ Disjoint (I ×ˢ J) S := by
  classical
  -- For `r ≥ m` the bound is `0`.
  have hrm : r < Fintype.card α := by
    by_contra h
    rw [Nat.sub_eq_zero_of_le (not_lt.1 h), Nat.cast_zero, mul_zero, zero_div, zero_mul] at hS
    exact absurd hS (not_lt.2 (Nat.cast_nonneg _))
  by_contra hne
  simp only [not_exists, not_and] at hne
  -- The unmarked positions contain no `(r + 1) × (r + 1)` rectangle.
  have hK := kovari_sos_turan (univ \ S) (s := r + 1) fun I J hI hJ hsub =>
    hne I J hI hJ (disjoint_left.2 fun p hp hpS => (mem_sdiff.1 (hsub hp)).2 hpS)
  rw [card_univ_sdiff, Fintype.card_prod, Nat.add_sub_cancel,
    show Fintype.card α + 1 - (r + 1) = Fintype.card α - r by omega] at hK
  generalize Fintype.card α = m at hrm hK hS
  generalize Fintype.card β = n at hn hK hS
  -- With `N = (m - r) n` markable positions, Kővári–Sós–Turán gives
  -- `n (N - |S|) ^ (r + 1) ≤ r N ^ (r + 1)`, which the numerical core contradicts.
  have hmn : m * n = (m - r) * n + r * n := by
    rw [← add_mul, Nat.sub_add_cancel hrm.le]
  rw [show m * n - #S - r * n = (m - r) * n - #S by omega, mul_comm n (m - r)] at hK
  rw [mul_comm (n : ℝ) _] at hS
  generalize hN : (m - r) * n = N at hK hS
  have hNcast : ((m - r : ℕ) : ℝ) * n = N := by exact_mod_cast hN
  rw [hNcast] at hS
  obtain ⟨hSN, hlt⟩ := lt_and_mul_pow_lt hn hS
  have hK' : (n : ℝ) * (N - #S) ^ (r + 1) ≤ r * N ^ (r + 1) := by
    rw [← Nat.cast_sub hSN.le]
    exact_mod_cast hK
  linarith

end Cslib

namespace Matrix

variable {m n K : Type*} [Fintype m] [Fintype n] [Field K]

/-- **Rigidity of totally regular matrices** ([Lokam2009], Theorem 2.5, after [Friedman1993] and
[ShokrollahiSpielmanStemann1997]), for `m × n` matrices. If `A` is totally regular and
`|n| ≤ r 2 ^ (r + 1)`, then bringing the rank of `A` down to at most `r` needs at least
`|n| (|m| - r) / (2 (r + 1)) · log₂ (|n| / r)` changes: with fewer changes, some
`(r + 1) × (r + 1)` submatrix is unchanged (`Cslib.exists_disjoint_product_of_card_lt`), and it is
nonsingular. [Lokam2009] states the square case for `log² n ≤ r ≤ n / 2`, which implies the
hypothesis here for `r ≥ 1`. -/
theorem IsTotallyRegular.le_rigidity {A : Matrix m n K} (hA : A.IsTotallyRegular) {r : ℕ}
    (hn : Fintype.card n ≤ r * 2 ^ (r + 1)) :
    (Fintype.card n * (Fintype.card m - r : ℕ) / (2 * (r + 1)) *
      Real.logb 2 (Fintype.card n / r) : ℝ) ≤ A.rigidity r := by
  classical
  by_contra hlt
  obtain ⟨B, hB, hAB⟩ := exists_rigidity_eq A r
  set S := univ.filter fun p : m × n => A p.1 p.2 ≠ B p.1 p.2 with hSdef
  have hS : (#S : ℝ) < Fintype.card n * (Fintype.card m - r : ℕ) / (2 * (r + 1)) *
      Real.logb 2 (Fintype.card n / r) := by
    rw [hSdef, ← diffCount_eq_card_filter, hAB]
    exact not_le.1 hlt
  obtain ⟨I, J, hI, hJ, hdisj⟩ := Cslib.exists_disjoint_product_of_card_lt S hn hS
  -- `A` and `B` agree on `I × J`.
  have hagree : ∀ i ∈ I, ∀ j ∈ J, A i j = B i j := fun i hi j hj => by
    by_contra hne
    have hmem : (i, j) ∈ I ×ˢ J := mem_product.2 ⟨hi, hj⟩
    exact disjoint_left.1 hdisj hmem (by simpa [hSdef] using hne)
  let f : Fin (r + 1) → m := (↑) ∘ (I.equivFinOfCardEq hI).symm
  let g : Fin (r + 1) → n := (↑) ∘ (J.equivFinOfCardEq hJ).symm
  have hf : f.Injective := Subtype.val_injective.comp (Equiv.injective _)
  have hg : g.Injective := Subtype.val_injective.comp (Equiv.injective _)
  have hsub : A.submatrix f g = B.submatrix f g := by
    ext a b
    exact hagree _ (Subtype.prop _) _ (Subtype.prop _)
  -- The common `(r + 1) × (r + 1)` submatrix is nonsingular, so `rank B ≥ r + 1`.
  have hdet : (B.submatrix f g).det ≠ 0 := hsub ▸ hA (r + 1) f g hf hg
  have hrank : (B.submatrix f g).rank = r + 1 := by
    rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)),
      Fintype.card_fin]
  have := (rank_submatrix_le B f g).trans hB
  omega

/-- **Rigidity of totally regular matrices** ([Lokam2009], Theorem 2.5). An `n × n` totally
regular matrix needs at least `n ^ 2 / (4 (r + 1)) · log₂ (n / r)` changes to bring its rank down
to at most `r`, for `n ≤ 2 ^ r` and `2 r ≤ n`. [Lokam2009] states this for `log² n ≤ r ≤ n / 2`;
with base-`2` logarithms `log² n ≤ r` implies `n ≤ 2 ^ r`, so the range here is wider. -/
theorem IsTotallyRegular.le_rigidity_of_le_two_pow {A : Matrix n n K} (hA : A.IsTotallyRegular)
    {r : ℕ} (hn : Fintype.card n ≤ 2 ^ r) (hr : 2 * r ≤ Fintype.card n) :
    (Fintype.card n ^ 2 / (4 * (r + 1)) * Real.logb 2 (Fintype.card n / r) : ℝ) ≤
      A.rigidity r := by
  set N := Fintype.card n with hN
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp
  have hrN : r < N := by
    have : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    rcases Nat.eq_zero_or_pos N with h | h
    · omega
    · omega
  refine le_trans ?_ (hA.le_rigidity (hn.trans ?_))
  · -- `N / 2 ≤ N - r` and `log₂ (N / r) ≥ 1`.
    have hrpos : (0 : ℝ) < r := by exact_mod_cast hr0
    have hL : 0 ≤ Real.logb 2 (N / r) := by
      refine Real.logb_nonneg (by norm_num) ?_
      rw [le_div_iff₀ hrpos, one_mul]
      exact_mod_cast hrN.le
    have hNr : (N : ℝ) / 2 ≤ (N - r : ℕ) := by
      rw [Nat.cast_sub hrN.le, div_le_iff₀ (by norm_num)]
      have : (2 * r : ℝ) ≤ N := by exact_mod_cast hr
      linarith
    calc (N : ℝ) ^ 2 / (4 * (r + 1)) * Real.logb 2 (N / r)
        = N * (N / 2) / (2 * (r + 1)) * Real.logb 2 (N / r) := by
          rw [show (4 : ℝ) * (r + 1) = 2 * (2 * (r + 1)) by ring, ← div_div]; ring
      _ ≤ N * (N - r : ℕ) / (2 * (r + 1)) * Real.logb 2 (N / r) := by gcongr
  · calc 2 ^ r = 1 * 2 ^ r := (one_mul _).symm
      _ ≤ r * 2 ^ (r + 1) := by
        gcongr
        · omega
        · omega

variable {F : Type*} [Field F]

/-- **Rigidity of Cauchy matrices** ([Lokam2009], Theorem 2.5). The `n × n` Cauchy matrix
`1 / (x i - y j)`, with distinct `x i`, distinct `y j` and `x i ≠ y j`, needs at least
`n ^ 2 / (4 (r + 1)) · log₂ (n / r)` changes to bring its rank down to at most `r`, for
`n ≤ 2 ^ r` and `2 r ≤ n` (a wider range than the `log² n ≤ r ≤ n / 2` of [Lokam2009]).
[Lokam2009] writes the Cauchy matrix as `1 / (x i + y j)`, which is
`cauchy x (-y)`. -/
theorem le_rigidity_cauchy {x y : n → F} (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ i j, x i ≠ y j) {r : ℕ} (hn : Fintype.card n ≤ 2 ^ r)
    (hr : 2 * r ≤ Fintype.card n) :
    (Fintype.card n ^ 2 / (4 * (r + 1)) * Real.logb 2 (Fintype.card n / r) : ℝ) ≤
      (cauchy x y).rigidity r :=
  (isTotallyRegular_cauchy hx hy hxy).le_rigidity_of_le_two_pow hn hr

/-- The explicit Cauchy matrices `1 / (i - (N + j))` over a field of characteristic zero need at
least `N ^ 2 / (4 (r + 1)) · log₂ (N / r)` changes to bring their rank down to at most `r`, for
`N ≤ 2 ^ r` and `2 r ≤ N`. -/
theorem le_rigidity_cauchyNat [CharZero F] {N r : ℕ} (hN : N ≤ 2 ^ r) (hr : 2 * r ≤ N) :
    (N ^ 2 / (4 * (r + 1)) * Real.logb 2 (N / r) : ℝ) ≤ (cauchyNat F N).rigidity r := by
  simpa using (isTotallyRegular_cauchyNat (F := F) N).le_rigidity_of_le_two_pow
    (by simpa using hN) (by simpa using hr)

/-- The explicit Cauchy matrices `1 / (i - (N + j))` over `ZMod q`, for a prime `q ≥ 2 N`, need at
least `N ^ 2 / (4 (r + 1)) · log₂ (N / r)` changes to bring their rank down to at most `r`, for
`N ≤ 2 ^ r` and `2 r ≤ N`. -/
theorem le_rigidity_cauchyNat_zmod {q : ℕ} [Fact q.Prime] {N r : ℕ} (hq : 2 * N ≤ q)
    (hN : N ≤ 2 ^ r) (hr : 2 * r ≤ N) :
    (N ^ 2 / (4 * (r + 1)) * Real.logb 2 (N / r) : ℝ) ≤ (cauchyNat (ZMod q) N).rigidity r := by
  simpa using (isTotallyRegular_cauchyNat_zmod hq).le_rigidity_of_le_two_pow
    (by simpa using hN) (by simpa using hr)

end Matrix
