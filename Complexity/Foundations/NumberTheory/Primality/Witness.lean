/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/` next to `FermatPsp`)

public import Complexity.Init
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Witnesses for odd composite moduli

The Solovay–Strassen and Miller–Rabin bounds [Solovay and Strassen][SolovayStrassen1977]
[Rabin][Rabin1980] show that the bases fooling a primality test modulo an odd composite `n` lie in a
proper subgroup of `(ZMod n)ˣ`, hence make up at most half of the units. Both proofs split an odd
composite `n` into one of two shapes and build a unit witness for each; this file collects the
shared facts.

## Main results

* `Subgroup.two_mul_card_le_of_ne_top`: a proper subgroup of a finite group has at most half of
  its elements.
* `Nat.exists_sq_dvd_or_eq_mul_coprime`: an odd composite number is divisible by the square of an
  odd prime, or is the product of an odd prime `p` and an odd `q > 1` coprime to `p`.
* `ZMod.exists_unit_castHom_eq`: the Chinese remainder theorem for units.
* `ZMod.exists_unit_pow_of_sq_dvd`: if `p ^ 2 ∣ n` for an odd prime `p`, then the unit
  `1 + n / p` modulo `n` has `p ∣ m` whenever its `m`-th power is `1`, and no power equal to `-1`.

## References

* [R. Solovay, V. Strassen, *A fast Monte-Carlo test for primality*][SolovayStrassen1977]
* [M. O. Rabin, *Probabilistic algorithm for testing primality*][Rabin1980]
-/

public section

/-- A proper subgroup of a finite group has at most half of its elements. -/
theorem Subgroup.two_mul_card_le_of_ne_top {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : H ≠ ⊤) : 2 * Nat.card H ≤ Nat.card G := by
  rw [← H.card_mul_index, mul_comm 2]
  exact Nat.mul_le_mul_left _ (Subgroup.one_lt_index_of_ne_top hH)

/-- An odd composite number is divisible by the square of an odd prime, or is the product of an
odd prime `p` and an odd `q > 1` coprime to `p`. -/
theorem Nat.exists_sq_dvd_or_eq_mul_coprime {n : ℕ} (hodd : Odd n) (h1 : 1 < n)
    (hn : ¬ n.Prime) :
    (∃ p, p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) ∨
      ∃ p q, n = p * q ∧ p.Prime ∧ p ≠ 2 ∧ p.Coprime q ∧ Odd q ∧ 1 < q := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hpn : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := by
    intro h
    rw [h] at hpn
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hpn)
  by_cases hpq : n.minFac ∣ n / n.minFac
  · left
    refine ⟨n.minFac, hp, hp2, ?_⟩
    rw [pow_two]
    calc n.minFac * n.minFac ∣ n.minFac * (n / n.minFac) := Nat.mul_dvd_mul_left _ hpq
      _ = n := Nat.mul_div_cancel' hpn
  · right
    refine ⟨n.minFac, n / n.minFac, (Nat.mul_div_cancel' hpn).symm, hp, hp2,
      (Nat.Prime.coprime_iff_not_dvd hp).2 hpq, Odd.of_dvd_nat hodd (Nat.div_dvd_of_dvd hpn), ?_⟩
    rcases Nat.lt_or_ge 1 (n / n.minFac) with h | h
    · exact h
    · exfalso
      interval_cases hq : n / n.minFac
      · rw [Nat.div_eq_zero_iff] at hq
        rcases hq with hq | hq
        · exact hp.ne_zero hq
        · exact absurd (Nat.minFac_le (show 0 < n by omega)) (not_le.2 hq)
      · apply hn
        have := Nat.mul_div_cancel' hpn
        rw [hq, mul_one] at this
        rwa [this] at hp

/-- If `x ^ 2 = 0`, then `(1 + x) ^ k = 1 + k x`. -/
theorem one_add_pow_of_sq_eq_zero {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0) (k : ℕ) :
    (1 + x) ^ k = 1 + k * x := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, add_zero]
  | succ k ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (k : R) * hx

namespace ZMod

/-- The Chinese remainder isomorphism reduces modulo each factor. -/
theorem chineseRemainder_apply {p q : ℕ} (h : p.Coprime q) (z : ZMod (p * q)) :
    chineseRemainder h z =
      (castHom (dvd_mul_right p q) (ZMod p) z, castHom (dvd_mul_left q p) (ZMod q) z) := by
  ext <;> simp [chineseRemainder, castHom_apply, Prod.fst_zmod_cast, Prod.snd_zmod_cast]

/-- **Chinese remainder theorem for units**: units modulo coprime `p` and `q` lift to a unit
modulo `p * q`. -/
theorem exists_unit_castHom_eq {p q : ℕ} (h : p.Coprime q) (u : (ZMod p)ˣ) (v : (ZMod q)ˣ) :
    ∃ c : (ZMod (p * q))ˣ, castHom (dvd_mul_right p q) (ZMod p) c = u ∧
      castHom (dvd_mul_left q p) (ZMod q) c = v := by
  set z := (chineseRemainder h).symm ((u : ZMod p), (v : ZMod q))
  have hz := (chineseRemainder h).apply_symm_apply ((u : ZMod p), (v : ZMod q))
  rw [chineseRemainder_apply, Prod.ext_iff] at hz
  have hu : IsUnit z := by
    have : IsUnit (chineseRemainder h z) := by
      rw [(chineseRemainder h).apply_symm_apply]
      exact Prod.isUnit_iff.2 ⟨u.isUnit, v.isUnit⟩
    simpa [z] using this.map (chineseRemainder h).symm
  exact ⟨hu.unit, hz.1, hz.2⟩

/-- `-1 ≠ 1` modulo an odd `n > 1`. -/
theorem neg_one_ne_one_of_odd {n : ℕ} (hn : Odd n) (h1 : 1 < n) : (-1 : ZMod n) ≠ 1 := by
  have : Fact (2 < n) := ⟨by obtain ⟨k, rfl⟩ := hn; omega⟩
  exact ZMod.neg_one_ne_one

/-- **The witness for a square factor.** If `p ^ 2 ∣ n` for an odd prime `p` and `n ≠ 0`, then
`c = 1 + n / p` is a unit modulo `n` with `c ^ m = 1` only when `p ∣ m`, and never `c ^ m = -1`. -/
theorem exists_unit_pow_of_sq_dvd {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n ≠ 0)
    (hpn : p ^ 2 ∣ n) :
    ∃ c : (ZMod n)ˣ, (∀ m, (c : ZMod n) ^ m = 1 → p ∣ m) ∧ ∀ m, (c : ZMod n) ^ m ≠ -1 := by
  obtain ⟨k, rfl⟩ := hpn
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  set x : ZMod (p ^ 2 * k) := ((p * k : ℕ) : ZMod (p ^ 2 * k)) with hxdef
  have hx : x ^ 2 = 0 := by
    rw [hxdef, ← Nat.cast_pow, natCast_eq_zero_iff]
    exact ⟨k, by ring⟩
  let c : (ZMod (p ^ 2 * k))ˣ := ⟨1 + x, 1 - x, by linear_combination -hx,
    by linear_combination -hx⟩
  refine ⟨c, fun m hm => ?_, fun m hm => ?_⟩
  · rw [one_add_pow_of_sq_eq_zero hx] at hm
    have h' : ((m * (p * k) : ℕ) : ZMod (p ^ 2 * k)) = 0 := by
      push_cast
      rw [hxdef] at hm
      push_cast at hm
      linear_combination hm
    rw [natCast_eq_zero_iff] at h'
    refine Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hp.pos hk) ?_
    calc p * (p * k) = p ^ 2 * k := by ring
      _ ∣ m * (p * k) := h'
  · rw [one_add_pow_of_sq_eq_zero hx] at hm
    have h' := congrArg (castHom (show p ∣ p ^ 2 * k from ⟨p * k, by ring⟩) (ZMod p)) hm
    rw [map_add, map_mul, map_one, map_neg, map_one, map_natCast, hxdef, map_natCast,
      Nat.cast_mul, ZMod.natCast_self, zero_mul, mul_zero, add_zero] at h'
    exact neg_one_ne_one_of_odd (hp.odd_of_ne_two hp2) hp.one_lt h'.symm

end ZMod
