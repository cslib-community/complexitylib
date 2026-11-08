/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
public import Complexity.Foundations.Data.Code.ListDecoding
import Complexity.Foundations.Data.Code.Plotkin
import Complexity.Foundations.Data.Hamming
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.List.GetD

/-!
# The Johnson bound

Let `C` be a code of length `n` and minimum distance at least `d`, and let `w` be a word. Each
codeword `c` within distance `e` of `w` agrees with `w` on a set of at least `a = n - e`
coordinates, and two distinct codewords agree with each other, hence on the intersection of their
sets, on at most `t = n - d` coordinates. Counting the pairs of such codewords that agree with
`w` at a coordinate, and applying the Cauchy–Schwarz inequality to the numbers of codewords that
agree with `w` at each coordinate, the number `L` of codewords within distance `e` satisfies
`L * (a ^ 2 - n * t) ≤ n * (a - t)` (`Cslib.Code.card_filter_hammingDist_le_mul_le`). When
`a ^ 2 > n * t`, that is when `e < n - √(n * (n - d))`, a Hamming ball of radius `e` therefore
contains at most `n * (d - e)` codewords (`Cslib.Code.card_filter_hammingDist_le_le`), whatever
the alphabet: the **Johnson bound** [Johnson1962], [GuruswamiRudraSudan2019]. Listing the messages
whose codewords lie in the ball is then a list decoder up to radius `e / n` with lists of
`n * (d - e)` messages (`Cslib.Code.exists_listCode_listDecodes`), in the sense of
`Cslib.ListCode.ListDecodes`; the decoder is chosen noncomputably, and no running time is claimed.

Over an alphabet of `q` letters the radius improves. If `a` of the `M` codewords in the ball agree
with `w` at a coordinate, the other `M - a` spread over `q - 1` letters, so at least
`a ^ 2 + (M - a) ^ 2 / (q - 1)` ordered pairs of them agree there. Combining this with the
double counting behind the Plotkin bound (`Cslib.Code.sum_sum_hammingDist_add_sum_sum_sum_ite`)
gives, for `q e ≤ (q - 1) n`,
`M ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ (q - 1) n d`
(`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`): the **q-ary Johnson bound**
[GuruswamiRudraSudan2019, Theorem 7.3.1], which the source proves for `q = 2` and leaves to its
Exercise 7.7 for general `q`. If `d ≤ (1 - 1 / q) n`, its hypotheses hold exactly when
`e / n < J_q(d / n)`, where `J_q(δ) = (1 - 1 / q) (1 - √(1 - q δ / (q - 1)))`; for larger `d` they
hold whenever `q e ≤ (q - 1) n`. A ball of such a radius then contains at most `(q - 1) n d`
codewords (`Cslib.Code.card_filter_hammingDist_le_le_of_mul_le`): the radius of Exercise 7.7, with
a list size within the `q d n` of Theorem 7.3.1 (Exercise 7.7 states `2 q n`). As `q` grows,
`J_q(δ)` decreases to the alphabet-free radius `1 - √(1 - δ)`.

## Main results

* `Cslib.Code.card_filter_hammingDist_le_mul_le`: the Johnson bound, in agreement form.
* `Cslib.Code.card_filter_hammingDist_le_le`: the Johnson bound on list sizes.
* `Cslib.Code.exists_listCode_listDecodes`: list decoding up to the Johnson radius.
* `Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`,
  `Cslib.Code.card_filter_hammingDist_le_le_of_mul_le`: the q-ary Johnson bound.

## References

* [S. M. Johnson, *A new upper bound for error-correcting codes*][Johnson1962]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

@[expose] public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [DecidableEq α]

/-- **Double counting for the Johnson bound.** If `L` sets `B c ⊆ ι` of size `a` meet pairwise in
at most `t` elements, then `L * a ^ 2 ≤ n * (a + (L - 1) * t)`, where `n = |ι|`. -/
private theorem card_mul_sq_le {κ : Type*} [DecidableEq ι] (L : Finset κ)
    (B : κ → Finset ι) {a t : ℕ} (hB : ∀ c ∈ L, #(B c) = a)
    (hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ t) :
    #L * a ^ 2 ≤ Fintype.card ι * (a + (#L - 1) * t) := by
  classical
  -- `m i` codewords agree with the word at the coordinate `i`
  let m : ι → ℕ := fun i => #{c ∈ L | i ∈ B c}
  have hsum : ∑ i, m i = #L * a := by
    simp only [m, card_filter]
    rw [sum_comm]
    simp only [← card_filter, filter_mem_eq_inter, univ_inter]
    rw [sum_congr rfl hB, sum_const, smul_eq_mul]
  have hsq : ∑ i, m i ^ 2 = ∑ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') := by
    simp only [m, card_filter, sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun c' _ => ?_
    simp only [ite_zero_mul_ite_zero, mul_one, ← card_filter]
    congr 1
    ext i
    simp
  have hrow : ∀ c ∈ L, ∑ c' ∈ L, #(B c ∩ B c') ≤ a + (#L - 1) * t := by
    intro c hc
    rw [← add_sum_erase L _ hc, inter_self, hB c hc]
    gcongr
    calc ∑ c' ∈ L.erase c, #(B c ∩ B c') ≤ ∑ _c' ∈ L.erase c, t :=
          sum_le_sum fun c' hc' => hinter c hc c' (mem_of_mem_erase hc') (ne_of_mem_erase hc').symm
      _ = (#L - 1) * t := by rw [sum_const, card_erase_of_mem hc, smul_eq_mul]
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := m)
  rw [hsum, hsq, card_univ] at hcs
  rcases L.eq_empty_or_nonempty with rfl | hL
  · simp
  have hL0 : 0 < #L := hL.card_pos
  have : (#L * a) ^ 2 ≤ Fintype.card ι * (#L * (a + (#L - 1) * t)) :=
    hcs.trans (Nat.mul_le_mul_left _ ((sum_le_sum hrow).trans_eq (by rw [sum_const, smul_eq_mul])))
  rw [mul_pow, sq (#L), mul_assoc, Nat.mul_left_comm (Fintype.card ι) (#L)] at this
  exact Nat.le_of_mul_le_mul_left this hL0

/-- **The Johnson bound**, in agreement form: for a code of length `n` and minimum distance at
least `d`, the number `L` of codewords within distance `e` of a word `w` satisfies
`L * ((n - e) ^ 2 - n * (n - d)) ≤ n * (d - e)`. It bounds `L` when `n * (n - d) < (n - e) ^ 2`
and says nothing otherwise. -/
theorem card_filter_hammingDist_le_mul_le {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) (e : ℕ) :
    #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card ι - e) ^ 2 - Fintype.card ι * (Fintype.card ι - d)) ≤
      Fintype.card ι * (d - e) := by
  classical
  set n := Fintype.card ι
  set L : Finset (ι → α) := {c ∈ C | hammingDist c w ≤ e}
  -- each codeword in the ball agrees with `w` on a set `B c` of exactly `n - e` coordinates
  have hagree : ∀ c ∈ L, n - e ≤ #({i | c i = w i} : Finset ι) := by
    intro c hc
    have h1 := card_filter_eq_add_hammingDist c w
    have h2 := (mem_filter.1 hc).2
    omega
  choose! B hBsub hBcard using fun c hc => exists_subset_card_eq (hagree c hc)
  -- two distinct codewords agree on at most `n - d` coordinates
  have hinter : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → #(B c ∩ B c') ≤ n - d := by
    intro c hc c' hc' hne
    have hsub : B c ∩ B c' ⊆ ({i | c i = c' i} : Finset ι) := by
      intro i hi
      have h1 := (mem_filter.1 (hBsub c hc (mem_inter.1 hi).1)).2
      have h2 := (mem_filter.1 (hBsub c' hc' (mem_inter.1 hi).2)).2
      exact mem_filter.2 ⟨mem_univ i, h1.trans h2.symm⟩
    have h1 := card_filter_eq_add_hammingDist c c'
    have h2 := Nat.cast_le.1 (le_minDist_iff.1 hd c (mem_filter.1 hc).1 c' (mem_filter.1 hc').1 hne)
    have := card_le_card hsub
    omega
  have key := card_mul_sq_le L B hBcard hinter
  -- arithmetic, with `a = n - e` and `t = n - d`
  have hmain : #L * ((n - e) ^ 2 - n * (n - d)) ≤ n * ((n - e) - (n - d)) := by
    rcases le_or_gt ((n - e) ^ 2) (n * (n - d)) with h | h
    · rw [Nat.sub_eq_zero_of_le h, mul_zero]
      exact Nat.zero_le _
    rcases Nat.eq_zero_or_pos #L with hL | hL
    · rw [hL, zero_mul]
      exact Nat.zero_le _
    have ht : n - d ≤ n := Nat.sub_le _ _
    have hat : n - d ≤ n - e := by
      by_contra hlt
      have : (n - e) ^ 2 ≤ (n - d) * (n - d) := by
        rw [sq]
        exact Nat.mul_le_mul (by omega) (by omega)
      exact absurd h (not_lt.2 (this.trans (Nat.mul_le_mul_right _ ht)))
    zify [h.le, hat, Nat.one_le_iff_ne_zero.2 hL.ne'] at key ⊢
    nlinarith
  exact hmain.trans (Nat.mul_le_mul_left _ (by omega))

/-- **The Johnson bound** [Johnson1962]: if `n * (n - d) < (n - e) ^ 2`, that is if
`e < n - √(n * (n - d))`, a Hamming ball of radius `e` contains at most `n * (d - e)` codewords of a
code of length `n` and minimum distance at least `d`, whatever the alphabet. -/
theorem card_filter_hammingDist_le_le {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} ≤ Fintype.card ι * (d - e) :=
  (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt h)).trans
    (card_filter_hammingDist_le_mul_le hd w e)

/-- **List decoding up to the Johnson radius.** Let `enc` be an injective encoding of a finite
nonempty set of messages whose codewords have minimum distance at least `d`. If
`n * (n - d) < (n - e) ^ 2`, some list decoder with lists of `n * (d - e)` messages list decodes
`enc` up to radius `e / n`: it lists the messages whose codewords are within distance `e` of the
received word. -/
theorem exists_listCode_listDecodes {M : Type*} [Finite M] [Nonempty M]
    {enc : M → ι → α} (henc : Function.Injective enc) {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (Set.range enc))
    (h : Fintype.card ι * (Fintype.card ι - d) < (Fintype.card ι - e) ^ 2) :
    ∃ C : ListCode M ι α (Fintype.card ι * (d - e)),
      C.encode = enc ∧ C.ListDecodes (e / Fintype.card ι) := by
  classical
  have := Fintype.ofFinite M
  -- the messages whose codewords are within distance `e`
  let S : (ι → α) → Finset M := fun w => {x | hammingDist (enc x) w ≤ e}
  have hS (w : ι → α) : #(S w) ≤ Fintype.card ι * (d - e) := by
    have hC : (d : ℕ∞) ≤ minDist ((univ.image enc : Finset (ι → α)) : Set (ι → α)) := by
      rwa [coe_image, coe_univ, Set.image_univ]
    calc #(S w) = #{c ∈ univ.image enc | hammingDist c w ≤ e} := by
          rw [filter_image, card_image_of_injective _ henc]
      _ ≤ _ := card_filter_hammingDist_le_le hC h w
  refine ⟨⟨enc, fun w k => (S w).toList.getD k (Classical.arbitrary M)⟩, rfl, fun x w hx => ?_⟩
  have hxe : hammingDist (enc x) w ≤ e := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn | hn
    · have := hammingDist_le_card_fintype (x := enc x) (y := w)
      omega
    · rw [div_mul_cancel₀ _ (by positivity)] at hx
      exact_mod_cast hx
  have hx : x ∈ (S w).toList := mem_toList.2 (mem_filter.2 ⟨mem_univ x, hxe⟩)
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 hx
  refine ⟨⟨i, hi.trans_le ((length_toList _).trans_le (hS w))⟩, ?_⟩
  change (S w).toList.getD i _ = x
  rw [List.getD_eq_getElem _ _ hi, hix]

/-! ### The q-ary Johnson bound -/

section Qary

variable [Fintype α]

omit [Fintype ι] in
/-- **The column bound for the q-ary Johnson bound.** If `a` of the `M` words of `L` have the
letter `w i` at the coordinate `i`, then `(q - 1) a ^ 2 + (M - a) ^ 2` is at most `q - 1` times the
number of ordered pairs of words of `L` that agree at `i`. -/
private theorem sub_one_mul_sq_add_sq_le_sub_one_mul_sum_sum_ite (L : Finset (ι → α))
    (w : ι → α) (i : ι) :
    ((Fintype.card α : ℤ) - 1) * (#{x ∈ L | x i = w i} : ℤ) ^ 2 +
        ((#L : ℤ) - #{x ∈ L | x i = w i}) ^ 2 ≤
      ((Fintype.card α : ℤ) - 1) * ∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0) := by
  have hsq := sum_sum_ite_eq_sum_sq L i
  set m : α → ℕ := fun b => #{x ∈ L | x i = b}
  have hC : #L = ∑ b : α, m b := card_eq_sum_card_fiberwise fun x _ => mem_coe.2 (mem_univ (x i))
  -- the other `q - 1` letters
  have hrest : #L = m (w i) + ∑ b ∈ univ.erase (w i), m b := by
    rw [hC, add_sum_erase _ _ (mem_univ _)]
  have hrest2 : ∑ b : α, m b ^ 2 = m (w i) ^ 2 + ∑ b ∈ univ.erase (w i), m b ^ 2 := by
    rw [add_sum_erase _ (fun b => m b ^ 2) (mem_univ _)]
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase (w i)) (f := m)
  rw [card_erase_of_mem (mem_univ _), card_univ] at hcs
  have hq : 1 ≤ Fintype.card α := Fintype.card_pos_iff.2 ⟨w i⟩
  have hcsZ : ((#L : ℤ) - m (w i)) ^ 2 ≤
      ((Fintype.card α : ℤ) - 1) * ∑ b ∈ univ.erase (w i), (m b : ℤ) ^ 2 := by
    have h1 : (#L : ℤ) - m (w i) = ∑ b ∈ univ.erase (w i), (m b : ℤ) := by
      rw [hrest]; push_cast; ring
    rw [h1]
    have := hcs
    push_cast [Nat.cast_sub hq] at this ⊢
    exact_mod_cast this
  have hsqZ : ((∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0) : ℕ) : ℤ) =
      (m (w i) : ℤ) ^ 2 + ∑ b ∈ univ.erase (w i), (m b : ℤ) ^ 2 := by
    rw [hsq, hrest2]; push_cast; ring
  push_cast at hsqZ
  rw [hsqZ]
  nlinarith

/-- The q-ary Johnson bound over the integers. -/
private theorem card_filter_hammingDist_le_mul_le_of_mul_le_int [Nonempty α]
    {C : Finset (ι → α)} {d : ℕ} (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α)
    {e : ℕ} (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    (#{c ∈ C | hammingDist c w ≤ e} : ℤ) *
        (((Fintype.card α : ℤ) - 1) * ((Fintype.card ι : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
          ((Fintype.card α : ℤ) - 1) * Fintype.card ι * ((Fintype.card ι : ℤ) - d)) ≤
      ((Fintype.card α : ℤ) - 1) * Fintype.card ι * d := by
  classical
  set n := Fintype.card ι
  set q := Fintype.card α
  set L : Finset (ι → α) := {c ∈ C | hammingDist c w ≤ e}
  have hq : 1 ≤ q := Fintype.card_pos
  have heZ : (q : ℤ) * e ≤ ((q : ℤ) - 1) * n := by
    have : ((q * e : ℕ) : ℤ) ≤ (((q - 1) * n : ℕ) : ℤ) := by exact_mod_cast he
    push_cast [Nat.cast_sub hq] at this
    exact this
  -- `a i` words of `L` agree with `w` at `i`
  set a : ι → ℕ := fun i => #{x ∈ L | x i = w i}
  set A : ℤ := ∑ i, (a i : ℤ)
  have hA : (#L : ℤ) * ((n : ℤ) - e) ≤ A := by
    have hswap : A = ∑ x ∈ L, (#({i | x i = w i} : Finset ι) : ℤ) := by
      simp only [A, a, card_filter]
      push_cast
      rw [sum_comm]
    have hrow : ∀ x ∈ L, (n : ℤ) - e ≤ #({i | x i = w i} : Finset ι) := by
      intro x hx
      have h1 := card_filter_eq_add_hammingDist x w
      have h2 := (mem_filter.1 hx).2
      omega
    rw [hswap]
    calc (#L : ℤ) * ((n : ℤ) - e) = ∑ _x ∈ L, ((n : ℤ) - e) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hrow
  -- pairwise distances and agreements
  set D : ℕ := ∑ x ∈ L, ∑ y ∈ L, hammingDist x y
  set P : ℕ := ∑ i, ∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0)
  have hDP : D + P = n * #L ^ 2 := by
    have h := sum_sum_hammingDist_add_sum_sum_sum_ite (C := L) (T := univ)
      (fun _ _ _ _ i hi => absurd (mem_univ i) hi)
    rw [card_univ] at h
    have hswap : ∑ x ∈ L, ∑ y ∈ L, ∑ i, (if x i = y i then 1 else 0) = P :=
      calc _ = ∑ x ∈ L, ∑ i, ∑ y ∈ L, (if x i = y i then 1 else 0) :=
            sum_congr rfl fun x _ => sum_comm
        _ = P := sum_comm
    rw [hswap] at h
    exact h
  have hD : #L * (#L - 1) * d ≤ D :=
    card_mul_card_sub_one_mul_le_sum_sum_hammingDist
      (hd.trans (minDist_anti fun x hx => (mem_filter.1 hx).1))
  rcases Nat.eq_zero_or_pos #L with hM | hM
  · rw [hM, Nat.cast_zero, zero_mul]
    have h1 : (1 : ℤ) ≤ q := by exact_mod_cast hq
    have : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
    positivity
  set M := #L
  -- sum the column bounds
  have hcol : ∑ i, (((q : ℤ) - 1) * (a i : ℤ) ^ 2 + ((M : ℤ) - a i) ^ 2) ≤
      ((q : ℤ) - 1) * P := by
    have : ((q : ℤ) - 1) * (P : ℤ) =
        ∑ i, ((q : ℤ) - 1) * ((∑ x ∈ L, ∑ y ∈ L, (if x i = y i then 1 else 0) : ℕ) : ℤ) := by
      simp only [P]; push_cast; rw [mul_sum]
    rw [this]
    exact sum_le_sum fun i _ => by
      exact_mod_cast sub_one_mul_sq_add_sq_le_sub_one_mul_sum_sum_ite L w i
  -- Cauchy–Schwarz on both sums
  have hcs1 : A ^ 2 ≤ n * ∑ i, (a i : ℤ) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => (a i : ℤ))
    rwa [card_univ] at this
  have hcs2 : ((n : ℤ) * M - A) ^ 2 ≤ n * ∑ i, ((M : ℤ) - a i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => (M : ℤ) - a i)
    rw [card_univ, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul] at this
    exact this
  have hq1' : (1 : ℤ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℤ) ≤ (q : ℤ) - 1 := by linarith
  have hg : ((q : ℤ) - 1) * A ^ 2 + ((n : ℤ) * M - A) ^ 2 ≤ n * (((q : ℤ) - 1) * P) := by
    rw [sum_add_distrib, ← mul_sum] at hcol
    have h1 : ((q : ℤ) - 1) * A ^ 2 ≤ ((q : ℤ) - 1) * (n * ∑ i, (a i : ℤ) ^ 2) := by gcongr
    have h2 : (0 : ℤ) ≤ n := by positivity
    nlinarith
  -- the left side increases in `A` beyond `n M / q`, and `A ≥ M (n - e) ≥ n M / q`
  set A0 : ℤ := (M : ℤ) * ((n : ℤ) - e)
  have hA0 : (n : ℤ) * M ≤ q * A0 := by
    have hMz : (0 : ℤ) ≤ M := by positivity
    have : (n : ℤ) ≤ q * ((n : ℤ) - e) := by linarith
    calc (n : ℤ) * M ≤ q * ((n : ℤ) - e) * M := mul_le_mul_of_nonneg_right this hMz
      _ = q * A0 := by ring
  have hmono : ((q : ℤ) - 1) * A0 ^ 2 + ((n : ℤ) * M - A0) ^ 2 ≤
      ((q : ℤ) - 1) * A ^ 2 + ((n : ℤ) * M - A) ^ 2 := by
    have hfac : ((q : ℤ) - 1) * A ^ 2 + ((n : ℤ) * M - A) ^ 2 -
        (((q : ℤ) - 1) * A0 ^ 2 + ((n : ℤ) * M - A0) ^ 2) =
        (A - A0) * (q * (A + A0) - 2 * n * M) := by ring
    have h1 : 0 ≤ A - A0 := by linarith
    have h2 : 0 ≤ (q : ℤ) * (A + A0) - 2 * n * M := by
      have : (q : ℤ) * A0 ≤ q * A := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      linarith
    nlinarith
  -- combine with `P = n M² - D ≤ n M² - M (M - 1) d`
  have hPZ : (P : ℤ) ≤ n * (M : ℤ) ^ 2 - M * ((M : ℤ) - 1) * d := by
    have h1 : ((D + P : ℕ) : ℤ) = ((n * M ^ 2 : ℕ) : ℤ) := by rw [hDP]
    have h2 : ((M * (M - 1) * d : ℕ) : ℤ) ≤ (D : ℤ) := by exact_mod_cast hD
    push_cast [Nat.cast_sub (show 1 ≤ M from hM)] at h1 h2
    linarith
  have hfinal : ((q : ℤ) - 1) * A0 ^ 2 + ((n : ℤ) * M - A0) ^ 2 ≤
      n * (((q : ℤ) - 1) * (n * (M : ℤ) ^ 2 - M * ((M : ℤ) - 1) * d)) := by
    have : (n : ℤ) * (((q : ℤ) - 1) * P) ≤
        n * (((q : ℤ) - 1) * (n * (M : ℤ) ^ 2 - M * ((M : ℤ) - 1) * d)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPZ hq1) (by positivity)
    linarith
  -- divide by `M`
  have hA0def : A0 = (M : ℤ) * ((n : ℤ) - e) := rfl
  rw [hA0def] at hfinal
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  have h1 : (M : ℤ) * ((M : ℤ) * (((q : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
      ((q : ℤ) - 1) * n * ((n : ℤ) - d)) - ((q : ℤ) - 1) * n * d) ≤ 0 := by
    linarith
  have h2 : (M : ℤ) * (((q : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 -
      ((q : ℤ) - 1) * n * ((n : ℤ) - d)) - ((q : ℤ) - 1) * n * d ≤ 0 := by
    nlinarith
  linarith

/-- **The q-ary Johnson bound**, in agreement form [GuruswamiRudraSudan2019, Theorem 7.3.1, at the
radius of Exercise 7.7 for general `q`]: for a code of length `n` and minimum distance at least `d`
over `q` letters, and a radius `e` with `q e ≤ (q - 1) n`, the number `M` of codewords within
distance `e` of a word `w` satisfies
`M ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ (q - 1) n d`. It bounds `M` when
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2` and says nothing otherwise. The hypothesis
`q e ≤ (q - 1) n` cannot be dropped: for `q = 2` and `e = d = n` the ball is the whole space. -/
theorem card_filter_hammingDist_le_mul_le_of_mul_le [Nonempty α] {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) (w : ι → α) {e : ℕ}
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) ≤
      (Fintype.card α - 1) * Fintype.card ι * d := by
  have h := card_filter_hammingDist_le_mul_le_of_mul_le_int hd w he
  set n := Fintype.card ι
  set q := Fintype.card α
  set M := #{c ∈ C | hammingDist c w ≤ e}
  have hq : 1 ≤ q := Fintype.card_pos
  have hen : e ≤ n := by
    by_contra hlt
    have : (q - 1) * n < q * e :=
      (Nat.mul_le_mul_right n (Nat.sub_le q 1)).trans_lt (Nat.mul_lt_mul_of_pos_left
        (by omega) hq)
    omega
  set B := (q - 1) * (n - e) ^ 2 + e ^ 2
  set X := (q - 1) * n * (n - d)
  rcases le_or_gt B X with hBX | hBX
  · rw [Nat.sub_eq_zero_of_le hBX, mul_zero]
    exact Nat.zero_le _
  have hBZ : ((B : ℕ) : ℤ) = ((q : ℤ) - 1) * ((n : ℤ) - e) ^ 2 + (e : ℤ) ^ 2 := by
    simp only [B]
    push_cast [Nat.cast_sub hq, Nat.cast_sub hen]
    ring
  -- `X ≥ (q - 1) n (n - d)` over the integers, with equality when `d ≤ n`
  have hXZ : ((q : ℤ) - 1) * n * ((n : ℤ) - d) ≤ ((X : ℕ) : ℤ) := by
    simp only [X]
    push_cast [Nat.cast_sub hq]
    have h0 : (0 : ℤ) ≤ ((q : ℤ) - 1) * n := by
      have : (1 : ℤ) ≤ q := by exact_mod_cast hq
      have : (0 : ℤ) ≤ n := by positivity
      nlinarith
    have : (n : ℤ) - d ≤ ((n - d : ℕ) : ℤ) := by
      rcases le_total d n with hdn | hdn
      · rw [Nat.cast_sub hdn]
      · rw [Nat.sub_eq_zero_of_le hdn]
        push_cast
        linarith [(Nat.cast_le (α := ℤ)).2 hdn]
    exact mul_le_mul_of_nonneg_left this h0
  have hgoal : ((M * (B - X) : ℕ) : ℤ) ≤ (((q - 1) * n * d : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hBX.le, Nat.cast_sub hq]
    rw [hBZ]
    have hM : (0 : ℤ) ≤ M := by positivity
    nlinarith
  exact_mod_cast hgoal

/-- **The q-ary Johnson bound** on list sizes [GuruswamiRudraSudan2019, Theorem 7.3.1, at the
radius of Exercise 7.7 for general `q`]: if `q e ≤ (q - 1) n` and
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, that is if `e / n < J_q(d / n)` when
`d ≤ (1 - 1 / q) n`, a Hamming ball of radius `e` contains at most `(q - 1) n d` codewords of a code
of length `n` and minimum distance at least `d` over `q` letters. The list size `(q - 1) n d` is
within the `q d n` of Theorem 7.3.1 (Exercise 7.7 states `2 q n`). -/
theorem card_filter_hammingDist_le_le_of_mul_le [Nonempty α] {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι)
    (h : (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d) <
      (Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2) (w : ι → α) :
    #{c ∈ C | hammingDist c w ≤ e} ≤ (Fintype.card α - 1) * Fintype.card ι * d :=
  (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt h)).trans
    (card_filter_hammingDist_le_mul_le_of_mul_le hd w he)

end Qary

end Cslib.Code
