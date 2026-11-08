/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
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
* Below that distance, shortening gives the **asymptotic Plotkin bound** on the rate
  [GuruswamiRudraSudan2019, Corollary 4.4.2], in
  `Complexity.Foundations.Data.Code.Plotkin.Asymptotic`.

## Main results

* `Cslib.Code.card_mul_sub_le_of_le_minDist`, `Cslib.Code.card_le_div_of_le_minDist`: the Plotkin
  bound.
* `Cslib.Code.card_mul_sub_le_pow_mul_of_le_minDist`: the Plotkin bound for shortened codes.
* `Cslib.Code.card_le_mul_of_le_minDist_of_mul_eq`,
  `Cslib.Code.card_le_two_mul_of_le_minDist_of_card_eq`: the Plotkin bound at relative distance
  `1 - 1 / q`.

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

end Cslib.Code
