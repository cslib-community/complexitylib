/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.Code.Basic
import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Foundations.Data.Code.Johnson

/-!
# The Elias–Bassalygo bound

Let `C` be a code of length `n` over an alphabet of `q` letters, and let
`V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` be the volume of a Hamming ball of radius `e`. Every
codeword lies in `V` balls of radius `e`, so on average a ball of radius `e` contains
`|C| V / q ^ n` codewords, and some ball contains at least that many
(`Cslib.Code.exists_card_mul_sum_choose_le_pow_mul`) [GuruswamiRudraSudan2019, Lemma 8.1.2]. If the
code has minimum distance at least `d` and `q e ≤ (q - 1) n`, the q-ary Johnson bound
(`Cslib.Code.card_filter_hammingDist_le_mul_le_of_mul_le`) bounds the number of codewords in that
ball, which gives the **Elias–Bassalygo bound** [Bassalygo1965], [GuruswamiRudraSudan2019,
Section 8.1] in finite form:
`|C| V ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ q ^ n (q - 1) n d`
(`Cslib.Code.card_mul_sum_choose_mul_le`). Below the q-ary Johnson radius, that is when
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, this reads `|C| V ≤ q ^ n (q - 1) n d`
(`Cslib.Code.card_mul_sum_choose_le`): the Hamming bound `|C| V ≤ q ^ n` at a radius that may
exceed half the minimum distance, at the price of a polynomial factor.

The asymptotic form `R ≤ 1 - H_q(J_q(δ)) + o(1)` of [GuruswamiRudraSudan2019, Theorem 8.1.1]
follows from these bounds together with the lower bound `q ^ (H_q(e / n) n - o(n))` on the
volume `V`, which is not formalized here.

## Main results

* `Cslib.Code.exists_card_mul_sum_choose_le_pow_mul`: some Hamming ball contains its share of the
  codewords.
* `Cslib.Code.card_mul_sum_choose_mul_le`, `Cslib.Code.card_mul_sum_choose_le`: the
  Elias–Bassalygo bound in finite form.

## References

* [L. A. Bassalygo, *New upper bounds for error-correcting codes*][Bassalygo1965]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
-/

public section

namespace Cslib.Code

open Finset

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]

/-- **Some Hamming ball contains its share of the code** [GuruswamiRudraSudan2019, Lemma 8.1.2]:
for a code `C` of length `n` over `q` letters and a radius `e`, some word `w` has at least
`|C| V / q ^ n` codewords within distance `e`, where `V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is
the volume of a Hamming ball of radius `e`. -/
theorem exists_card_mul_sum_choose_le_pow_mul (C : Finset (ι → α)) (e : ℕ) :
    ∃ w : ι → α, #C * ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j ≤
      Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} := by
  classical
  set V := ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j
  have hball (x : ι → α) : #{y : ι → α | hammingDist x y ≤ e} = V := by
    rw [card_filter_hammingDist_le_eq_sum]
    exact sum_congr rfl fun j _ =>
      card_filter_hammingDist_eq_choose_mul_pow (β := fun _ => α) (fun _ => rfl) x j
  -- count the pairs `(w, c)` with `c ∈ C` within distance `e` of `w`
  have hcount : ∑ w : ι → α, #{c ∈ C | hammingDist c w ≤ e} = #C * V :=
    calc ∑ w : ι → α, #{c ∈ C | hammingDist c w ≤ e}
        = ∑ c ∈ C, #{w : ι → α | hammingDist c w ≤ e} := by
          simp only [card_filter]
          exact sum_comm
      _ = ∑ _c ∈ C, V := sum_congr rfl fun c _ => hball c
      _ = #C * V := by rw [sum_const, smul_eq_mul]
  have hsum : ∑ _w : ι → α, #C * V ≤
      ∑ w : ι → α, Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} := by
    rw [sum_const, card_univ, Fintype.card_fun, smul_eq_mul, ← mul_sum, hcount]
  obtain ⟨w, -, hw⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨w, hw⟩

/-- **The Elias–Bassalygo bound**, finite form [Bassalygo1965], [GuruswamiRudraSudan2019,
Section 8.1]: a code `C` of length `n` and minimum distance at least `d` over `q` letters
satisfies `|C| V ((q - 1) (n - e) ^ 2 + e ^ 2 - (q - 1) n (n - d)) ≤ q ^ n (q - 1) n d` for every
radius `e` with `q e ≤ (q - 1) n`, where `V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is the volume of
a Hamming ball of radius `e`. -/
theorem card_mul_sum_choose_mul_le {C : Finset (ι → α)} {d : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α))) {e : ℕ}
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι) :
    #C * (∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j) *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) ≤
      Fintype.card α ^ Fintype.card ι * ((Fintype.card α - 1) * Fintype.card ι * d) := by
  obtain ⟨w, hw⟩ := exists_card_mul_sum_choose_le_pow_mul C e
  calc _ ≤ Fintype.card α ^ Fintype.card ι * #{c ∈ C | hammingDist c w ≤ e} *
        ((Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2 -
          (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d)) :=
        Nat.mul_le_mul_right _ hw
    _ ≤ _ := by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left _ (card_filter_hammingDist_le_mul_le_of_mul_le hd w he)

/-- **The Elias–Bassalygo bound**, finite form below the q-ary Johnson radius [Bassalygo1965],
[GuruswamiRudraSudan2019, Section 8.1]: if `q e ≤ (q - 1) n` and
`(q - 1) n (n - d) < (q - 1) (n - e) ^ 2 + e ^ 2`, a code `C` of length `n` and minimum distance at
least `d` over `q` letters satisfies `|C| V ≤ q ^ n (q - 1) n d`, where
`V = ∑_{j ≤ e} (n choose j) (q - 1) ^ j` is the volume of a Hamming ball of radius `e`. -/
theorem card_mul_sum_choose_le {C : Finset (ι → α)} {d e : ℕ}
    (hd : (d : ℕ∞) ≤ minDist (C : Set (ι → α)))
    (he : Fintype.card α * e ≤ (Fintype.card α - 1) * Fintype.card ι)
    (h : (Fintype.card α - 1) * Fintype.card ι * (Fintype.card ι - d) <
      (Fintype.card α - 1) * (Fintype.card ι - e) ^ 2 + e ^ 2) :
    #C * ∑ j ∈ range (e + 1), (Fintype.card ι).choose j * (Fintype.card α - 1) ^ j ≤
      Fintype.card α ^ Fintype.card ι * ((Fintype.card α - 1) * Fintype.card ι * d) := by
  obtain ⟨w, hw⟩ := exists_card_mul_sum_choose_le_pow_mul C e
  exact hw.trans (Nat.mul_le_mul_left _ (card_filter_hammingDist_le_le_of_mul_le hd he h w))

end Cslib.Code
