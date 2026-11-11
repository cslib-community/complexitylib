/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Hamming balls, the Hamming bound and the Gilbert–Varshamov bound

The words `∀ i, β i` at Hamming distance exactly `r` from a word `x` are obtained by choosing the
`r` positions where they differ and a different letter at each, so there are
`∑_{|S| = r} ∏_{i ∈ S} (|β i| - 1)` of them, whatever `x` is
(`Cslib.Code.card_filter_hammingDist_eq`); over an alphabet of `q` letters at each of `n` positions
this is `C(n, r) (q - 1) ^ r` (`Cslib.Code.card_filter_hammingDist_eq_choose_mul_pow`). Balls of
radius `r` around the words of a code of minimum distance `Cslib.Code.minDist` more than `2 r` are
disjoint, so the code has at most `q ^ n / V` words, where `V` is the size of a ball: the
**Hamming bound** (`Cslib.Code.card_mul_card_filter_hammingDist_le_le_prod`,
`Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist`) [Hamming1950],
[MacWilliams and Sloane, Chapter 1, Theorem 6][MacWilliamsSloane1977]. Conversely, the balls of
radius `d - 1` around a largest code of minimum distance at least `d` cover every word, so some
code of minimum distance at least `d` has at least `q ^ n / V` words, where `V` is the size of a
ball of radius `d - 1`: the **Gilbert–Varshamov bound**
(`Cslib.Code.exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt`,
`Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose`) [Gilbert1952], by Gilbert's greedy
argument; Varshamov proved the same bound for linear codes [Varshamov1957]. The same greedy argument
covers any finite set of words by the balls of radius `r` around a subset whose words are pairwise
more than `r` apart (`Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`). Over
`16` letters the
balls of radius less than `⌈L / 2⌉` have at most `8 ^ L` words, so some code of length `L` has
`2 ^ L` words any two of which differ in at least half of the positions
(`Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist`).

## Main results

* `Cslib.Code.card_filter_hammingDist_eq`: the size of a Hamming sphere.
* `Cslib.Code.card_filter_hammingDist_le_eq_sum`: the size of a Hamming ball, as a sum of sphere
  sizes.
* `Cslib.Code.card_filter_hammingDist_le_le_pow`: a Hamming ball of radius `r` over `q` letters at
  `n` positions has at most `(n (q - 1) + 1) ^ r` words.
* `Cslib.Code.card_mul_card_filter_hammingDist_le_le_prod`: the Hamming bound.
* `Cslib.Code.card_mul_sum_choose_le_of_two_mul_lt_minDist`: the Hamming bound over a `q`-letter
  alphabet.
* `Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le`: a finite set of words is
  covered by the balls of radius `r` around a subset of words pairwise more than `r` apart.
* `Cslib.Code.exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt`: the
  Gilbert–Varshamov bound.
* `Cslib.Code.exists_le_minDist_and_pow_le_card_mul_sum_choose`: the Gilbert–Varshamov bound over a
  `q`-letter alphabet.
* `Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist`: `2 ^ L` words of length `L` over
  `16` letters, any two differing in at least half of the positions.

## References

* [R. W. Hamming, *Error detecting and error correcting codes*][Hamming1950]
* [E. N. Gilbert, *A comparison of signalling alphabets*][Gilbert1952]
* [R. R. Varshamov, *Estimate of the number of signals in error correcting codes*][Varshamov1957]
* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

public section

namespace Cslib.Code

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*} [∀ i, Fintype (β i)]
  [∀ i, DecidableEq (β i)]

/-- The words differing from `x` exactly at the positions `S`: a different letter at each position
of `S`. -/
theorem card_filter_filter_ne_eq (x : ∀ i, β i) (S : Finset ι) :
    #{y : ∀ i, β i | ({i | x i ≠ y i} : Finset ι) = S} = ∏ i ∈ S, (Fintype.card (β i) - 1) := by
  have h : #{y : ∀ i, β i | ({i | x i ≠ y i} : Finset ι) = S} =
      Fintype.card (∀ i, {b : β i // (i ∈ S ↔ x i ≠ b)}) := by
    rw [← Fintype.card_coe]
    refine Fintype.card_congr ((Equiv.subtypeEquivRight fun y => ?_).trans
      Equiv.subtypePiEquivPi)
    simp only [mem_filter, mem_univ, true_and, Finset.ext_iff]
    exact forall_congr' fun i => Iff.comm
  rw [h, Fintype.card_pi]
  have hi (i : ι) : Fintype.card {b : β i // (i ∈ S ↔ x i ≠ b)} =
      if i ∈ S then Fintype.card (β i) - 1 else 1 := by
    by_cases hiS : i ∈ S
    · simp only [hiS, true_iff, ↓reduceIte]
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq']
    · simp only [hiS, false_iff, not_not, ↓reduceIte]
      rw [Fintype.card_subtype_eq']
  simp only [hi]
  rw [prod_ite, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter]

/-- **The size of a Hamming sphere**: the words at distance `r` from `x`. It does not depend on
`x`. -/
theorem card_filter_hammingDist_eq (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y = r} =
      ∑ S ∈ powersetCard r (univ : Finset ι), ∏ i ∈ S, (Fintype.card (β i) - 1) := by
  rw [← sum_congr rfl fun S _ => card_filter_filter_ne_eq x S, ← card_biUnion]
  · congr 1
    ext y
    simp [hammingDist, mem_powersetCard]
  · intro S _ T _ hST
    exact disjoint_left.2 fun y hS hT => hST ((mem_filter.1 hS).2.symm.trans (mem_filter.1 hT).2)

/-- Over an alphabet of `q` letters at each of `n` positions, a Hamming sphere of radius `r` has
`C(n, r) (q - 1) ^ r` words. -/
theorem card_filter_hammingDist_eq_choose_mul_pow {q : ℕ} (hq : ∀ i, Fintype.card (β i) = q)
    (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y = r} = (Fintype.card ι).choose r * (q - 1) ^ r := by
  rw [card_filter_hammingDist_eq, sum_congr rfl fun S hS => by
    rw [prod_congr rfl fun i _ => by rw [hq i], prod_const, (mem_powersetCard.1 hS).2],
    sum_const, card_powersetCard, card_univ, smul_eq_mul]

/-- **The size of a Hamming ball** is the sum of the sizes of the spheres. -/
theorem card_filter_hammingDist_le_eq_sum (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y ≤ r} =
      ∑ j ∈ range (r + 1), #{y : ∀ i, β i | hammingDist x y = j} := by
  rw [← card_biUnion]
  · congr 1
    ext y
    simp
  · intro i _ j _ hij
    exact disjoint_left.2 fun y hi hj => hij ((mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2)

/-- Over an alphabet of `q` letters at each of `n` positions, a Hamming ball of radius `r` has at
most `(n (q - 1) + 1) ^ r` words: by the binomial theorem this dominates
`∑_{j ≤ r} C(n, j) (q - 1) ^ j`. -/
theorem card_filter_hammingDist_le_le_pow {q : ℕ} (hq : ∀ i, Fintype.card (β i) = q)
    (x : ∀ i, β i) (r : ℕ) :
    #{y : ∀ i, β i | hammingDist x y ≤ r} ≤ (Fintype.card ι * (q - 1) + 1) ^ r := by
  rw [card_filter_hammingDist_le_eq_sum, add_pow]
  refine sum_le_sum fun j hj => ?_
  rw [card_filter_hammingDist_eq_choose_mul_pow hq x j, one_pow, mul_one, mul_pow]
  calc (Fintype.card ι).choose j * (q - 1) ^ j
      ≤ Fintype.card ι ^ j * (q - 1) ^ j :=
        Nat.mul_le_mul_right _ (Nat.choose_le_pow _ j)
    _ ≤ Fintype.card ι ^ j * (q - 1) ^ j * r.choose j :=
        Nat.le_mul_of_pos_right _ (Nat.choose_pos (Nat.lt_succ_iff.mp (mem_range.mp hj)))

/-- **The Hamming bound**: a code of minimum distance more than `2 r` has at most `∏ i, |β i|`
words in all of its balls of radius `r` together. -/
theorem card_mul_card_filter_hammingDist_le_le_prod {C : Finset (∀ i, β i)} {r : ℕ}
    (hC : 2 * (r : ℕ∞) < minDist (C : Set (∀ i, β i))) (x₀ : ∀ i, β i) :
    #C * #{y : ∀ i, β i | hammingDist x₀ y ≤ r} ≤ ∏ i, Fintype.card (β i) := by
  -- the balls around the codewords are disjoint, and have the same size
  have hdisj : (C : Set (∀ i, β i)).PairwiseDisjoint
      fun x => ({y : ∀ i, β i | hammingDist x y ≤ r} : Finset (∀ i, β i)) := by
    intro x hx y hy hxy
    exact disjoint_left.2 fun z hzx hzy =>
      hxy (eq_of_hammingDist_le_of_two_mul_lt_minDist hC hx hy (mem_filter.1 hzx).2
        (mem_filter.1 hzy).2)
  have hsize (x : ∀ i, β i) : #{y : ∀ i, β i | hammingDist x y ≤ r} =
      #{y : ∀ i, β i | hammingDist x₀ y ≤ r} := by
    simp only [card_filter_hammingDist_le_eq_sum, card_filter_hammingDist_eq]
  calc #C * #{y : ∀ i, β i | hammingDist x₀ y ≤ r}
      = ∑ x ∈ C, #{y : ∀ i, β i | hammingDist x y ≤ r} := by
        rw [sum_congr rfl fun x _ => hsize x, sum_const, smul_eq_mul]
    _ = #(C.biUnion fun x => {y : ∀ i, β i | hammingDist x y ≤ r}) := (card_biUnion hdisj).symm
    _ ≤ #(univ : Finset (∀ i, β i)) := card_le_univ _
    _ = ∏ i, Fintype.card (β i) := by rw [card_univ, Fintype.card_pi]

omit [DecidableEq ι] in
/-- **The Hamming bound** [Hamming1950] over a `q`-letter alphabet at each of `n` positions: a code
of minimum distance more than `2 r` has at most `q ^ n / V` words, where
`V = ∑_{j ≤ r} C(n, j) (q - 1) ^ j` is the size of a ball of radius `r`. -/
theorem card_mul_sum_choose_le_of_two_mul_lt_minDist {q : ℕ}
    (hq : ∀ i, Fintype.card (β i) = q) {C : Finset (∀ i, β i)} {r : ℕ}
    (hC : 2 * (r : ℕ∞) < minDist (C : Set (∀ i, β i))) :
    #C * ∑ j ∈ range (r + 1), (Fintype.card ι).choose j * (q - 1) ^ j ≤ q ^ Fintype.card ι := by
  classical
  rcases C.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · simp
  have h := card_mul_card_filter_hammingDist_le_le_prod hC x₀
  rwa [card_filter_hammingDist_le_eq_sum, sum_congr rfl fun j _ =>
    card_filter_hammingDist_eq_choose_mul_pow hq x₀ j, prod_congr rfl fun i _ => hq i,
    prod_const, card_univ] at h

/-- The balls of radius less than `d ≥ 1` all have the size of the ball of radius `d - 1`. -/
private theorem card_filter_hammingDist_lt_eq_sum {d : ℕ} (hd : 0 < d) (x : ∀ i, β i) :
    #{y : ∀ i, β i | hammingDist x y < d} =
      ∑ j ∈ range d, #{y : ∀ i, β i | hammingDist x y = j} := by
  simp only [Nat.lt_iff_le_pred hd, card_filter_hammingDist_le_eq_sum, Nat.sub_add_cancel hd]

omit [DecidableEq ι] [∀ i, Fintype (β i)] in
/-- **Covering by a maximal separated subset**: every finite set `L` of words contains a subset
`C` of words pairwise more than `r` apart such that every word of `L` lies within distance `r` of
a word of `C`. A largest such subset works: a word of `L` farther than `r` from all of it could
be added to it. -/
theorem exists_subset_pairwise_lt_hammingDist_forall_exists_le (L : Finset (∀ i, β i)) (r : ℕ) :
    ∃ C ⊆ L, (C : Set (∀ i, β i)).Pairwise (fun x y => r < hammingDist x y) ∧
      ∀ y ∈ L, ∃ x ∈ C, hammingDist x y ≤ r := by
  classical
  -- a largest subset of words pairwise more than `r` apart
  obtain ⟨C, hC, hmax⟩ := exists_max_image
    (L.powerset.filter fun C : Finset (∀ i, β i) =>
      (C : Set (∀ i, β i)).Pairwise fun x y => r < hammingDist x y) card
    ⟨∅, by simp⟩
  obtain ⟨hCL, hCr⟩ := mem_filter.1 hC
  refine ⟨C, mem_powerset.1 hCL, hCr, fun y hy => ?_⟩
  by_contra hfar
  simp only [not_exists, not_and, not_le] at hfar
  have hyC : y ∉ C := fun h => by simpa using hfar y h
  have hins : ((insert y C : Finset (∀ i, β i)) : Set (∀ i, β i)).Pairwise
      fun x y => r < hammingDist x y := by
    rw [coe_insert]
    exact hCr.insert fun x hx _ => ⟨by rw [hammingDist_comm]; exact hfar x hx, hfar x hx⟩
  have := hmax _ (mem_filter.2 ⟨mem_powerset.2 (insert_subset hy (mem_powerset.1 hCL)), hins⟩)
  rw [card_insert_of_notMem hyC] at this
  omega

/-- **The Gilbert–Varshamov bound** [Gilbert1952]: for `d ≥ 1` there is a code of minimum distance
at least `d` which has at least `∏ i, |β i| / V` words, where `V` is the size of a ball of radius
`d - 1`. A largest such code works: its balls of radius `d - 1` cover every word, since a word at
distance at least `d` from every codeword could be added to it. -/
theorem exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt {d : ℕ} (hd : 0 < d)
    (x₀ : ∀ i, β i) :
    ∃ C : Finset (∀ i, β i), (d : ℕ∞) ≤ minDist (C : Set (∀ i, β i)) ∧
      ∏ i, Fintype.card (β i) ≤ #C * #{y : ∀ i, β i | hammingDist x₀ y < d} := by
  classical
  -- a maximal set of words pairwise at distance at least `d`
  obtain ⟨C, -, hCd, hcov⟩ := exists_subset_pairwise_lt_hammingDist_forall_exists_le
    (univ : Finset (∀ i, β i)) (d - 1)
  refine ⟨C, le_minDist_iff.2 fun x hx y hy hxy => Nat.cast_le.2 (by
    have := hCd hx hy hxy
    omega), ?_⟩
  -- its balls of radius `d - 1` cover every word
  have hcover : (univ : Finset (∀ i, β i)) ⊆ C.biUnion fun x => {y | hammingDist x y < d} := by
    intro y _
    obtain ⟨x, hx, hxy⟩ := hcov y (mem_univ y)
    exact mem_biUnion.2 ⟨x, hx, mem_filter.2 ⟨mem_univ y, by omega⟩⟩
  have hsize (x : ∀ i, β i) : #{y : ∀ i, β i | hammingDist x y < d} =
      #{y : ∀ i, β i | hammingDist x₀ y < d} := by
    simp only [card_filter_hammingDist_lt_eq_sum hd, card_filter_hammingDist_eq]
  calc ∏ i, Fintype.card (β i)
      = #(univ : Finset (∀ i, β i)) := by rw [card_univ, Fintype.card_pi]
    _ ≤ #(C.biUnion fun x => {y : ∀ i, β i | hammingDist x y < d}) := card_le_card hcover
    _ ≤ ∑ x ∈ C, #{y : ∀ i, β i | hammingDist x y < d} := card_biUnion_le
    _ = #C * #{y : ∀ i, β i | hammingDist x₀ y < d} := by
        rw [sum_congr rfl fun x _ => hsize x, sum_const, smul_eq_mul]

omit [DecidableEq ι] in
/-- **The Gilbert–Varshamov bound** [Gilbert1952] over a `q`-letter alphabet at each of `n`
positions: for `d ≥ 1` some code of minimum distance at least `d` has at least `q ^ n / V` words,
where `V = ∑_{j < d} C(n, j) (q - 1) ^ j` is the size of a ball of radius `d - 1`. -/
theorem exists_le_minDist_and_pow_le_card_mul_sum_choose {q : ℕ}
    (hq : ∀ i, Fintype.card (β i) = q) {d : ℕ} (hd : 0 < d) :
    ∃ C : Finset (∀ i, β i), (d : ℕ∞) ≤ minDist (C : Set (∀ i, β i)) ∧
      q ^ Fintype.card ι ≤ #C * ∑ j ∈ range d, (Fintype.card ι).choose j * (q - 1) ^ j := by
  classical
  have hprod : ∏ i, Fintype.card (β i) = q ^ Fintype.card ι := by
    rw [prod_congr rfl fun i _ => hq i, prod_const, card_univ]
  rcases isEmpty_or_nonempty (∀ i, β i) with hempty | hne
  · refine ⟨∅, by simp, ?_⟩
    rw [← hprod, ← Fintype.card_pi, Fintype.card_eq_zero]
    exact Nat.zero_le _
  obtain ⟨x₀⟩ := hne
  obtain ⟨C, hCd, hC⟩ := exists_le_minDist_and_prod_le_card_mul_card_filter_hammingDist_lt hd x₀
  refine ⟨C, hCd, ?_⟩
  rwa [card_filter_hammingDist_lt_eq_sum hd, sum_congr rfl fun j _ =>
    card_filter_hammingDist_eq_choose_mul_pow hq x₀ j, hprod] at hC

/-- Over `16` letters, the balls of radius less than `⌈L / 2⌉` have at most `8 ^ L` words: each
sphere of radius `j < ⌈L / 2⌉` has `C(L, j) 15 ^ j ≤ C(L, j) 4 ^ L` words. -/
private theorem sum_range_choose_mul_fifteen_pow_le (L : ℕ) :
    ∑ j ∈ range ((L + 1) / 2), L.choose j * 15 ^ j ≤ 8 ^ L := by
  calc ∑ j ∈ range ((L + 1) / 2), L.choose j * 15 ^ j
      ≤ ∑ j ∈ range ((L + 1) / 2), L.choose j * 4 ^ L := by
        refine sum_le_sum fun j hj => Nat.mul_le_mul_left _ ?_
        have hj' : 2 * j ≤ L := by
          have := mem_range.1 hj
          omega
        calc 15 ^ j ≤ 16 ^ j := Nat.pow_le_pow_left (by norm_num) j
          _ = 4 ^ (2 * j) := by rw [pow_mul]; norm_num
          _ ≤ 4 ^ L := Nat.pow_le_pow_right (by norm_num) hj'
    _ = (∑ j ∈ range ((L + 1) / 2), L.choose j) * 4 ^ L := by rw [sum_mul]
    _ ≤ (∑ j ∈ range (L + 1), L.choose j) * 4 ^ L := by
        gcongr
        omega
    _ = 8 ^ L := by
        rw [Nat.sum_range_choose, ← mul_pow]
        norm_num

/-- **A code of rate `1 / 4` and relative distance `1 / 2`**: some code of length `L` over `16`
letters has at least `2 ^ L` words, any two of which differ in at least half of the positions. By
the Gilbert–Varshamov bound, since the balls of radius less than `⌈L / 2⌉` have at most `8 ^ L`
words. -/
theorem exists_two_pow_le_card_and_le_two_mul_hammingDist (L : ℕ) :
    ∃ C : Finset (Fin L → Fin 16), 2 ^ L ≤ #C ∧
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → L ≤ 2 * hammingDist x y := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exact ⟨{fun i => i.elim0}, by simp, by simp⟩
  obtain ⟨C, hCd, hC⟩ := exists_le_minDist_and_pow_le_card_mul_sum_choose
    (ι := Fin L) (β := fun _ => Fin 16) (q := 16) (fun _ => Fintype.card_fin 16)
    (d := (L + 1) / 2) (by omega)
  rw [Fintype.card_fin] at hC
  refine ⟨C, ?_, fun x hx y hy hxy => ?_⟩
  · have h := hC.trans (Nat.mul_le_mul_left #C (sum_range_choose_mul_fifteen_pow_le L))
    have h16 : (16 : ℕ) ^ L = 2 ^ L * 8 ^ L := by rw [← mul_pow]; norm_num
    rw [h16] at h
    exact Nat.le_of_mul_le_mul_right h (by positivity)
  · have h' : (L + 1) / 2 ≤ hammingDist x y := by
      exact_mod_cast le_minDist_iff.1 hCd x hx y hy hxy
    omega

end Cslib.Code
