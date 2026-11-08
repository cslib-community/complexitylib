/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# The Plotkin bound

Let `C` be a code of length `n` and minimum distance at least `d` over an alphabet `α` of `q`
letters. At every coordinate, by the Cauchy–Schwarz inequality, at least a `1 / q` fraction of
the ordered pairs of codewords agree (`Cslib.Code.sq_card_le_card_mul_sum_sum_ite`). Summing
over the coordinates, the sum of the distances over all ordered pairs of codewords is at most
`(1 - 1 / q) n |C|²` (`Cslib.Code.card_mul_sum_sum_hammingDist_add_le`), while each of the
`|C| (|C| - 1)` pairs of distinct codewords contributes at least `d`. Comparing the two gives the
**Plotkin bound** [Plotkin1960], [GuruswamiRudraSudan2019, Theorem 4.4.1 and Exercise 4.17]:
`|C| (q d - (q - 1) n) ≤ q d` (`Cslib.Code.card_mul_sub_le_of_le_minDist`), so that
`|C| ≤ q d / (q d - (q - 1) n)` when `d > (1 - 1 / q) n`
(`Cslib.Code.card_le_div_of_le_minDist`).

The argument only uses the coordinates where codewords may differ, so it bounds every code whose
words agree outside a set `T` of coordinates by the same expression with `|T|` in place of `n`
(`Cslib.Code.card_mul_sub_le_of_le_minDist_of_forall_notMem_eq`). *Shortening* a code to any `m`
coordinates, that is splitting it according to its letters at the other `n - m` coordinates,
gives `|C| (q d - (q - 1) m) ≤ q ^ (n - m) q d`
(`Cslib.Code.card_mul_sub_le_pow_mul_of_le_minDist`). Two consequences:

* At relative distance exactly `1 - 1 / q`, that is `q d = (q - 1) n`, shortening one coordinate
  gives `|C| ≤ q n` (`Cslib.Code.card_le_mul_of_le_minDist_of_mul_eq`), which is at least as sharp
  as the bounds `2 q n` of [GuruswamiRudraSudan2019, Theorem 4.4.1, part 1] and `2 (q - 1) n` of
  its Exercise 4.13. For binary codes of length `2 d` this is `|C| ≤ 2 n`
  (`Cslib.Code.card_le_two_mul_of_le_minDist_of_card_eq`), attained by the Hadamard code together
  with its complements [GuruswamiRudraSudan2019, Exercise 4.14].
* Below that distance, shortening to the largest `m` with `(q - 1) m < q d` gives
  `log_q |C| ≤ n - q d / (q - 1) + 2 + log_q d` (`Cslib.Code.logb_card_le_of_le_minDist`): the
  **asymptotic Plotkin bound** `R ≤ 1 - q δ / (q - 1)` on the rate `R` of codes of relative distance
  `δ ≤ 1 - 1 / q` (`Cslib.Code.eventually_logb_card_le_of_le_hammingDist`)
  [GuruswamiRudraSudan2019, Corollary 4.4.2].

## Main results

* `Cslib.Code.card_mul_sub_le_of_le_minDist`, `Cslib.Code.card_le_div_of_le_minDist`: the Plotkin
  bound.
* `Cslib.Code.card_mul_sub_le_pow_mul_of_le_minDist`: the Plotkin bound for shortened codes.
* `Cslib.Code.card_le_mul_of_le_minDist_of_mul_eq`,
  `Cslib.Code.card_le_two_mul_of_le_minDist_of_card_eq`: the Plotkin bound at relative distance
  `1 - 1 / q`.
* `Cslib.Code.logb_card_le_of_le_minDist`,
  `Cslib.Code.eventually_logb_card_le_of_le_hammingDist`: the asymptotic Plotkin bound.

## References

* [M. Plotkin, *Binary codes with specified minimum distance*][Plotkin1960]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]

omit [Fintype ι] in
/-- The ordered pairs of words of `C` that agree at the coordinate `i`, counted by their common
letter there. -/
theorem sum_sum_ite_eq_sum_sq (C : Finset (ι → α)) (i : ι) :
    ∑ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) = ∑ b : α, #{x ∈ C | x i = b} ^ 2 := by
  have h : ∀ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) = #{y ∈ C | y i = x i} := by
    intro x _
    rw [card_filter]
    exact sum_congr rfl fun y _ => by simp only [eq_comm]
  rw [sum_congr rfl h, ← sum_fiberwise C (fun x => x i)]
  refine sum_congr rfl fun b _ => ?_
  rw [sq, ← smul_eq_mul, ← sum_const]
  exact sum_congr rfl fun x hx => by rw [(mem_filter.1 hx).2]

omit [Fintype ι] in
/-- **The column bound.** At every coordinate, at least a `1 / q` fraction of the ordered pairs
of words of `C` agree, where `q = |α|`. -/
theorem sq_card_le_card_mul_sum_sum_ite (C : Finset (ι → α)) (i : ι) :
    #C ^ 2 ≤ Fintype.card α * ∑ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) := by
  rw [sum_sum_ite_eq_sum_sq]
  have hC : #C = ∑ b : α, #{x ∈ C | x i = b} :=
    card_eq_sum_card_fiberwise fun x _ => mem_coe.2 (mem_univ (x i))
  rw [hC, ← card_univ]
  exact sq_sum_le_card_mul_sum_sq

omit [Fintype α] in
/-- For words that agree outside `T`, the Hamming distance plus the number of coordinates of `T`
where they agree is `|T|`. -/
theorem hammingDist_add_sum_ite_eq_card {x y : ι → α} {T : Finset ι}
    (h : ∀ i ∉ T, x i = y i) :
    hammingDist x y + ∑ i ∈ T, (if x i = y i then 1 else 0) = #T := by
  have hsub : ({i | x i ≠ y i} : Finset ι) = {i ∈ T | x i ≠ y i} := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun hi => ⟨by_contra fun hT => hi (h i hT), hi⟩, fun hi => hi.2⟩
  rw [hammingDist, hsub, ← card_filter, add_comm]
  exact card_filter_add_card_filter_not (s := T) (fun i => x i = y i)

omit [Fintype α] in
/-- **Double counting** for words that agree outside `T`: the distances plus the agreements in
`T`, summed over the ordered pairs of words of `C`, add up to `|T| |C|²`. -/
theorem sum_sum_hammingDist_add_sum_sum_sum_ite {C : Finset (ι → α)} {T : Finset ι}
    (hT : ∀ x ∈ C, ∀ y ∈ C, ∀ i ∉ T, x i = y i) :
    ∑ x ∈ C, ∑ y ∈ C, hammingDist x y +
        ∑ x ∈ C, ∑ y ∈ C, ∑ i ∈ T, (if x i = y i then 1 else 0) = #T * #C ^ 2 := by
  simp only [← sum_add_distrib]
  rw [sum_congr rfl fun x hx => sum_congr rfl fun y hy =>
    hammingDist_add_sum_ite_eq_card (hT x hx y hy)]
  rw [sum_const, sum_const, smul_eq_mul, smul_eq_mul, sq]
  ring

/-- **The total distance** of a code whose words agree outside `T`:
`q ∑ Δ(x, y) + |T| |C|² ≤ q |T| |C|²`, the sum over the ordered pairs of words of `C`, where
`q = |α|`. In other words, the average distance is at most `(1 - 1 / q) |T|`. -/
theorem card_mul_sum_sum_hammingDist_add_le {C : Finset (ι → α)} {T : Finset ι}
    (hT : ∀ x ∈ C, ∀ y ∈ C, ∀ i ∉ T, x i = y i) :
    Fintype.card α * ∑ x ∈ C, ∑ y ∈ C, hammingDist x y + #T * #C ^ 2 ≤
      Fintype.card α * (#T * #C ^ 2) := by
  set q := Fintype.card α
  set D := ∑ x ∈ C, ∑ y ∈ C, hammingDist x y
  set P := ∑ x ∈ C, ∑ y ∈ C, ∑ i ∈ T, (if x i = y i then 1 else 0)
  have hDP : D + P = #T * #C ^ 2 := sum_sum_hammingDist_add_sum_sum_sum_ite hT
  have hP : #T * #C ^ 2 ≤ q * P := by
    have hswap : P = ∑ i ∈ T, ∑ x ∈ C, ∑ y ∈ C, (if x i = y i then 1 else 0) :=
      calc P = ∑ x ∈ C, ∑ i ∈ T, ∑ y ∈ C, (if x i = y i then 1 else 0) :=
            sum_congr rfl fun x _ => sum_comm
        _ = _ := sum_comm
    have hconst : #T * #C ^ 2 = ∑ _i ∈ T, #C ^ 2 := by rw [sum_const, smul_eq_mul]
    rw [hswap, mul_sum, hconst]
    exact sum_le_sum fun i _ => sq_card_le_card_mul_sum_sum_ite C i
  calc q * D + #T * #C ^ 2 ≤ q * D + q * P := Nat.add_le_add_left hP _
    _ = q * (#T * #C ^ 2) := by rw [← mul_add, hDP]

omit [Fintype α] in
/-- The distances between distinct words of a code of minimum distance at least `d`, summed over
the ordered pairs of codewords, add up to at least `|C| (|C| - 1) d`. -/
theorem card_mul_card_sub_one_mul_le_sum_sum_hammingDist {C : Finset (ι → α)}
    {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) :
    #C * (#C - 1) * d ≤ ∑ x ∈ C, ∑ y ∈ C, hammingDist x y := by
  calc #C * (#C - 1) * d = ∑ x ∈ C, (#C - 1) * d := by
        rw [sum_const, smul_eq_mul, mul_assoc]
    _ ≤ ∑ x ∈ C, ∑ y ∈ C, hammingDist x y := by
        refine sum_le_sum fun x hx => ?_
        calc (#C - 1) * d = ∑ y ∈ C.erase x, d := by
              rw [sum_const, card_erase_of_mem hx, smul_eq_mul]
          _ ≤ ∑ y ∈ C.erase x, hammingDist x y := sum_le_sum fun y hy =>
              Nat.cast_le.1 (le_minDist_iff.1 hd x hx y (mem_of_mem_erase hy)
                (ne_of_mem_erase hy).symm)
          _ ≤ ∑ y ∈ C, hammingDist x y := sum_le_sum_of_subset (erase_subset x C)

/-- **The Plotkin bound for codes that agree outside `T`.** If the words of a code `C` of minimum
distance at least `d` over `q` letters agree outside a set `T` of coordinates, then
`|C| (q d - (q - 1) |T|) ≤ q d`. -/
theorem card_mul_sub_le_of_le_minDist_of_forall_notMem_eq {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) {T : Finset ι}
    (hT : ∀ x ∈ C, ∀ y ∈ C, ∀ i ∉ T, x i = y i) :
    #C * (Fintype.card α * d - (Fintype.card α - 1) * #T) ≤ Fintype.card α * d := by
  set q := Fintype.card α
  have h1 : q * (#C * (#C - 1) * d) + #T * #C ^ 2 ≤ q * (#T * #C ^ 2) :=
    (Nat.add_le_add_right (Nat.mul_le_mul_left q
      (card_mul_card_sub_one_mul_le_sum_sum_hammingDist hd)) _).trans
      (card_mul_sum_sum_hammingDist_add_le hT)
  rcases Nat.eq_zero_or_pos #C with hM | hM
  · rw [hM, zero_mul]
    exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos q with hq | hq
  · rw [hq]
    simp
  rcases le_or_gt (q * d) ((q - 1) * #T) with hle | hlt
  · rw [Nat.sub_eq_zero_of_le hle, mul_zero]
    exact Nat.zero_le _
  have hM1 : 1 ≤ #C := hM
  have hq1 : 1 ≤ q := hq
  zify [hM1, hq1, hlt.le] at h1 ⊢
  -- divide `h1` by `|C|`
  have h2 : (#C : ℤ) * (#C * (q * d) + #T * #C - q * #T * #C - q * d) ≤ 0 := by linarith
  have hMz : (0 : ℤ) < #C := by exact_mod_cast hM
  have h3 : (#C : ℤ) * (q * d) + #T * #C - q * #T * #C - q * d ≤ 0 := by nlinarith
  linarith

/-- **The Plotkin bound for shortened codes.** For a code `C` of length `n` and minimum distance
at least `d` over `q` letters, and any `m ≤ n`, `|C| (q d - (q - 1) m) ≤ q ^ (n - m) q d`:
fixing the letters at `n - m` coordinates leaves a code that agrees outside the other `m`
coordinates, to which the Plotkin bound applies [GuruswamiRudraSudan2019, proof of
Corollary 4.4.2]. -/
theorem card_mul_sub_le_pow_mul_of_le_minDist {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) {m : ℕ} (hm : m ≤ Fintype.card ι) :
    #C * (Fintype.card α * d - (Fintype.card α - 1) * m) ≤
      Fintype.card α ^ (Fintype.card ι - m) * (Fintype.card α * d) := by
  classical
  obtain ⟨T, -, hTm⟩ := exists_subset_card_eq (s := (univ : Finset ι)) (n := m)
    (by rw [card_univ]; exact hm)
  set k := Fintype.card α * d - (Fintype.card α - 1) * m
  -- group the codewords by their letters outside `T`
  have hfiber (v : (Tᶜ : Finset ι) → α) : #{x ∈ C | Tᶜ.restrict x = v} * k ≤
      Fintype.card α * d := by
    have hsub := card_mul_sub_le_of_le_minDist_of_forall_notMem_eq
      (C := {x ∈ C | Tᶜ.restrict x = v}) (d := d)
      (hd.trans (minDist_anti fun x hx => (mem_filter.1 hx).1)) (T := T)
      (fun x hx y hy i hi => by
        have h1 := congrFun (mem_filter.1 hx).2 ⟨i, mem_compl.2 hi⟩
        have h2 := congrFun (mem_filter.1 hy).2 ⟨i, mem_compl.2 hi⟩
        exact h1.trans h2.symm)
    rwa [hTm] at hsub
  have hcard : Fintype.card ((Tᶜ : Finset ι) → α) = Fintype.card α ^ (Fintype.card ι - m) := by
    rw [Fintype.card_fun, Fintype.card_coe, card_compl, hTm]
  calc #C * k = ∑ v : (Tᶜ : Finset ι) → α, #{x ∈ C | Tᶜ.restrict x = v} * k := by
        rw [← sum_mul, ← card_eq_sum_card_fiberwise fun x _ => mem_coe.2 (mem_univ _)]
    _ ≤ ∑ _v : (Tᶜ : Finset ι) → α, Fintype.card α * d := sum_le_sum fun v _ => hfiber v
    _ = _ := by rw [sum_const, card_univ, hcard, smul_eq_mul]

/-- **The Plotkin bound** [Plotkin1960], [GuruswamiRudraSudan2019, Theorem 4.4.1, part 2]: a code
`C` of length `n` and minimum distance at least `d` over `q` letters satisfies
`|C| (q d - (q - 1) n) ≤ q d`. It bounds `|C|` when `d > (1 - 1 / q) n` and says nothing
otherwise. -/
theorem card_mul_sub_le_of_le_minDist {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) :
    #C * (Fintype.card α * d - (Fintype.card α - 1) * Fintype.card ι) ≤ Fintype.card α * d := by
  have h := card_mul_sub_le_of_le_minDist_of_forall_notMem_eq hd (T := univ)
    (fun _ _ _ _ i hi => absurd (mem_univ i) hi)
  rwa [card_univ] at h

/-- **The Plotkin bound** [Plotkin1960], [GuruswamiRudraSudan2019, Theorem 4.4.1, part 2], quotient
form: if `d > (1 - 1 / q) n`, a code of length `n` and minimum distance at least `d` over `q`
letters has at most `q d / (q d - (q - 1) n)` codewords. -/
theorem card_le_div_of_le_minDist {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (h : (Fintype.card α - 1) * Fintype.card ι < Fintype.card α * d) :
    #C ≤ Fintype.card α * d / (Fintype.card α * d - (Fintype.card α - 1) * Fintype.card ι) :=
  (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt h)).2 (card_mul_sub_le_of_le_minDist hd)

/-- **The Plotkin bound at relative distance `1 - 1 / q`.** A code of length `n` and minimum
distance at least `d > 0` over `q` letters with `q d = (q - 1) n` has at most `q n` codewords.
Shortening one coordinate and applying the Plotkin bound gives this; it sharpens the bound `2 q n`
of [GuruswamiRudraSudan2019, Theorem 4.4.1, part 1] and, for `q ≥ 3`, the bound `2 (q - 1) n` of its
Exercise 4.13. -/
theorem card_le_mul_of_le_minDist_of_mul_eq [Nonempty α] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (hd0 : 0 < d)
    (h : Fintype.card α * d = (Fintype.card α - 1) * Fintype.card ι) :
    #C ≤ Fintype.card α * Fintype.card ι := by
  set q := Fintype.card α
  set n := Fintype.card ι
  have hq : 0 < q := Fintype.card_pos
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, mul_zero] at h
      exact absurd h (Nat.mul_pos hq hd0).ne'
    · exact hn
  have hs := card_mul_sub_le_pow_mul_of_le_minDist hd (m := n - 1) (Nat.sub_le n 1)
  have hk : q * d - (q - 1) * (n - 1) = q - 1 := by
    rw [h, Nat.mul_sub_one, Nat.sub_sub_self (Nat.le_mul_of_pos_right _ hn)]
  have hnn : n - (n - 1) = 1 := by omega
  rw [hk, hnn, pow_one, h] at hs
  have hq1 : 0 < q - 1 := by
    rcases Nat.lt_or_ge 1 q with hq1 | hq1
    · omega
    · have : q - 1 = 0 := by omega
      rw [this, zero_mul] at h
      exact absurd h (Nat.mul_pos hq hd0).ne'
  rw [mul_left_comm, mul_comm #C] at hs
  exact Nat.le_of_mul_le_mul_left hs hq1

/-- **The binary Plotkin bound at relative distance one half.** A binary code of length `n = 2 d`
and minimum distance at least `d > 0` has at most `2 n` codewords; the Hadamard code together with
its complements attains this [GuruswamiRudraSudan2019, Exercise 4.14]. -/
theorem card_le_two_mul_of_le_minDist_of_card_eq {C : Finset (ι → Bool)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → Bool))) (hd0 : 0 < d)
    (hn : Fintype.card ι = 2 * d) :
    #C ≤ 2 * Fintype.card ι := by
  have h := card_le_mul_of_le_minDist_of_mul_eq hd hd0 (by rw [Fintype.card_bool, hn]; ring)
  rwa [Fintype.card_bool] at h

/-- **The Plotkin bound below relative distance `1 - 1 / q`**, logarithmic form: a code of length
`n` and minimum distance at least `d > 0` over `q ≥ 2` letters with `q d ≤ (q - 1) n` satisfies
`log_q |C| ≤ n - q d / (q - 1) + 2 + log_q d`. -/
theorem logb_card_le_of_le_minDist [Nontrivial α] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (hd0 : 0 < d)
    (h : Fintype.card α * d ≤ (Fintype.card α - 1) * Fintype.card ι) :
    Real.logb (Fintype.card α) #C ≤
      Fintype.card ι - Fintype.card α * d / (Fintype.card α - 1) + 2 +
        Real.logb (Fintype.card α) d := by
  set q := Fintype.card α
  set n := Fintype.card ι
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hq1 : 0 < q - 1 := by omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd0
  have hlogd : 0 ≤ Real.logb q (d : ℝ) := Real.logb_nonneg hqR hdR
  -- shorten to length `m`, the largest with `(q - 1) m < q d`
  set m := (q * d - 1) / (q - 1)
  have hqd : 0 < q * d := Nat.mul_pos (by omega) hd0
  have hm1 : (q - 1) * m ≤ q * d - 1 := Nat.mul_div_le _ _
  have hm2 : q * d - 1 < (q - 1) * (m + 1) := Nat.lt_mul_div_succ _ hq1
  have hmn : m ≤ n := by
    by_contra hlt
    have : (q - 1) * n < (q - 1) * m := Nat.mul_lt_mul_of_pos_left (by omega) hq1
    omega
  have hgap : 1 ≤ q * d - (q - 1) * m := by omega
  have hs := card_mul_sub_le_pow_mul_of_le_minDist hd hmn
  have hC : #C ≤ q ^ (n - m) * (q * d) := (Nat.le_mul_of_pos_right _ hgap).trans hs
  -- `(q - 1) (m + 1) ≥ q d` over the reals
  have hmR : (q : ℝ) * d ≤ ((q : ℝ) - 1) * (m + 1) := by
    have : q * d ≤ (q - 1) * (m + 1) := by omega
    have h' : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * (m + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h'
    exact h'
  have hdiv : (q : ℝ) * d / ((q : ℝ) - 1) ≤ m + 1 := by
    rw [div_le_iff₀ hq1R]
    linarith
  rcases Nat.eq_zero_or_pos #C with h0 | h0
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    have : (q : ℝ) * d / ((q : ℝ) - 1) ≤ n := by
      rw [div_le_iff₀ hq1R]
      have h' : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * n : ℕ) : ℝ) := by exact_mod_cast h
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h'
      linarith
    linarith
  have hlog : Real.logb q (#C : ℝ) ≤ (n - m : ℕ) + (1 + Real.logb q (d : ℝ)) := by
    have hCR : (#C : ℝ) ≤ (q : ℝ) ^ (n - m) * (q * d) := by exact_mod_cast hC
    calc Real.logb q (#C : ℝ) ≤ Real.logb q ((q : ℝ) ^ (n - m) * (q * d)) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hCR
      _ = (n - m : ℕ) + (1 + Real.logb q (d : ℝ)) := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_mul (by positivity) (by positivity), Real.logb_self_eq_one hqR, mul_one]
  rw [Nat.cast_sub hmn] at hlog
  linarith

/-- **The asymptotic Plotkin bound** [GuruswamiRudraSudan2019, Corollary 4.4.2]. Let `C s` be codes
over `q ≥ 2` letters whose lengths `n_s` tend to infinity along a filter `l`, with relative
distance at least `δ`, where `0 ≤ δ ≤ 1 - 1 / q`: distinct codewords of `C s` differ on at least
`δ n_s` coordinates. Then for every `ε > 0`, eventually `log_q |C s| ≤ (1 - q δ / (q - 1) + ε) n_s`;
that is, the rate is at most `1 - q δ / (q - 1) + o(1)`. -/
theorem eventually_logb_card_le_of_le_hammingDist {σ : Type*} {ιs : σ → Type*}
    [∀ s, Fintype (ιs s)] [Nontrivial α] {l : Filter σ} {C : ∀ s, Finset (ιs s → α)} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : Fintype.card α * δ ≤ Fintype.card α - 1)
    (hC : ∀ s, ∀ x ∈ C s, ∀ y ∈ C s, x ≠ y → δ * Fintype.card (ιs s) ≤ hammingDist x y)
    (hn : Filter.Tendsto (fun s => Fintype.card (ιs s)) l Filter.atTop) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in l, Real.logb (Fintype.card α) #(C s) ≤
      (1 - Fintype.card α / (Fintype.card α - 1) * δ + ε) * Fintype.card (ιs s) := by
  classical
  set q := Fintype.card α
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hnR : Filter.Tendsto (fun s => (Fintype.card (ιs s) : ℝ)) l Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hn
  -- the trivial bound `|C| ≤ q ^ n`
  have htriv (s : σ) : Real.logb q #(C s) ≤ Fintype.card (ιs s) := by
    rcases Nat.eq_zero_or_pos #(C s) with h0 | h0
    · rw [h0, Nat.cast_zero, Real.logb_zero]
      positivity
    have hle : (#(C s) : ℝ) ≤ (q : ℝ) ^ Fintype.card (ιs s) := by
      have := card_le_univ (C s)
      rw [Fintype.card_fun] at this
      exact_mod_cast this
    calc Real.logb q #(C s) ≤ Real.logb q ((q : ℝ) ^ Fintype.card (ιs s)) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast h0) hle
      _ = Fintype.card (ιs s) := by rw [Real.logb_pow, Real.logb_self_eq_one hqR, mul_one]
  rcases hδ0.eq_or_lt with rfl | hδpos
  · refine Filter.Eventually.of_forall fun s => (htriv s).trans ?_
    have : (0 : ℝ) ≤ Fintype.card (ιs s) := by positivity
    nlinarith
  -- eventually `δ n ≥ 1`, `4 ≤ ε n / 2` and `log_q n ≤ ε n / 2`
  have h1 : ∀ᶠ s in l, 1 / δ + 8 / ε ≤ (Fintype.card (ιs s) : ℝ) :=
    hnR.eventually_ge_atTop _
  have h2 : ∀ᶠ s in l, Real.log (Fintype.card (ιs s)) ≤
      ε * Real.log q / 2 * Fintype.card (ιs s) := by
    have hlogq : 0 < Real.log q := Real.log_pos hqR
    have := (Real.isLittleO_log_id_atTop.bound (c := ε * Real.log q / 2) (by positivity))
    filter_upwards [hnR.eventually this, hnR.eventually_ge_atTop 1] with s hs hs1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, id, abs_of_nonneg (Real.log_nonneg hs1),
      abs_of_nonneg (by linarith)] at hs
    exact hs
  filter_upwards [h1, h2] with s hs1 hs2
  set n := Fintype.card (ιs s)
  set d := ⌊δ * n⌋₊
  have h8ε : 0 ≤ 8 / ε := by positivity
  have h1δ : 0 < 1 / δ := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hδn : 1 ≤ δ * n := by
    have : 1 / δ ≤ n := by linarith
    rw [div_le_iff₀ hδpos] at this
    linarith
  have hd0 : 0 < d := Nat.floor_pos.2 hδn
  have hdle : (d : ℝ) ≤ δ * n := Nat.floor_le (by positivity)
  have hdgt : δ * n < d + 1 := Nat.lt_floor_add_one _
  have hdmin : (d : ℕ∞) ≤ minDist ((C s : Finset (ιs s → α)) : Set (ιs s → α)) := by
    rw [le_minDist_iff]
    intro x hx y hy hxy
    have := hC s x hx y hy hxy
    exact_mod_cast Nat.floor_le_of_le (R := ℝ) this
  have hqd : q * d ≤ (q - 1) * n := by
    have : ((q * d : ℕ) : ℝ) ≤ (((q - 1) * n : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
      calc (q : ℝ) * d ≤ q * (δ * n) := by gcongr
        _ = (q * δ) * n := by ring
        _ ≤ ((q : ℝ) - 1) * n := by gcongr
    exact_mod_cast this
  have hmain := logb_card_le_of_le_minDist hdmin hd0 hqd
  have hlogd : Real.logb q (d : ℝ) ≤ ε / 2 * n := by
    have hdn : (d : ℝ) ≤ n := by
      have : δ ≤ 1 := by
        have : (q : ℝ) * δ ≤ q := by linarith
        nlinarith
      nlinarith
    calc Real.logb q (d : ℝ) ≤ Real.logb q (n : ℝ) :=
          Real.logb_le_logb_of_le hqR (by exact_mod_cast hd0) hdn
      _ = Real.log n / Real.log q := rfl
      _ ≤ ε / 2 * n := by
          rw [div_le_iff₀ (Real.log_pos hqR)]
          linarith
  -- `q d / (q - 1) ≥ q δ n / (q - 1) - 2`
  have hqd' : (q : ℝ) / (q - 1) * δ * n - 2 ≤ (q : ℝ) * d / (q - 1) := by
    have h2q : (q : ℝ) / (q - 1) ≤ 2 := by
      rw [div_le_iff₀ hq1R]
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have : (q : ℝ) / (q - 1) * δ * n - (q : ℝ) * d / (q - 1) =
        (q : ℝ) / (q - 1) * (δ * n - d) := by
      ring
    have hq0 : (0 : ℝ) ≤ (q : ℝ) / (q - 1) := by positivity
    nlinarith
  have h8 : 4 ≤ ε / 2 * n := by
    have : 8 / ε ≤ n := by linarith
    rw [div_le_iff₀ hε] at this
    linarith
  nlinarith

end Cslib.Code
