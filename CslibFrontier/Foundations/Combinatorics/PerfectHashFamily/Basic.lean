/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Defs
import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.LinearHash
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.Interval.Finset.Fin

/-!
# A perfect hash family of size `n * 2 ^ (25 * r)`

For all `n` and `r ≥ 1` we construct a family of at most `n * 2 ^ (25 * r)` maps
`Fin n → Fin r` such that every `r`-element subset of `Fin n` is mapped injectively by some
member.

The construction and the bound are ours and are not optimal: Schmidt and Siegel (*The spatial
complexity of oblivious `k`-probe hash functions*, 1990) prove the sharper bound
`2 ^ O(r) * (log n) ^ 2` by a more intricate construction, which is not formalized here. A
bound of the form `poly(n) * 2 ^ O(r)` is what the applications to hitting sets need; the
two-level scheme of Fredman, Komlós and Szemerédi gives only `r ^ O(r)`.

The family `splitHash q s`, of maps `ℕ → ℕ` that is perfect for `s`-element sets of numbers
below `q` with values below `s`, is defined by recursion on `s`. For `s ≥ 2` choose a prime
`p` with `s ^ 2 + 1 < p ≤ 2 * (s ^ 2 + 1)`. A member consists of a linear hash map `u` from
numbers below `q` to numbers below `p` (see `Cslib.linearHash`), a threshold `θ < p`, and
members `h₁`, `h₂` of the families for `(p, s / 2)` and `(p, s - s / 2)`; it sends `x` to
`h₁ (u x)` if `u x < θ` and to `s / 2 + h₂ (u x)` otherwise. Given an `s`-element set `S`,
take `u` injective on `S` and `θ` with exactly `s / 2` elements of `u(S)` below it. Splitting
into halves is essential for the size: `#(splitHash q s) * s ^ 8 ≤ q * (2 ^ 25) ^ (s - 1)` by
induction, using `2 * s ^ 2 ≤ 9 * ((s / 2) * (s - s / 2))`.

## Main definitions

* `Cslib.perfectHashFamily`: the family of maps `Fin n → Fin r`.

## Main results

* `Cslib.isPerfectHashFamily_perfectHashFamily`: it is a perfect hash family for `r`-element
  sets when `0 < r`.
* `Cslib.card_perfectHashFamily_le`: it has at most `n * 2 ^ (25 * r)` members.
-/

public section

namespace Cslib

open Finset

/-- A prime `p` with `s ^ 2 + 1 < p ≤ 2 * (s ^ 2 + 1)`, by Bertrand's postulate. -/
private noncomputable def hashPrime (s : ℕ) : ℕ :=
  (Nat.exists_prime_lt_and_le_two_mul (s ^ 2 + 1) (Nat.succ_ne_zero _)).choose

private lemma hashPrime_spec (s : ℕ) :
    (hashPrime s).Prime ∧ s ^ 2 + 1 < hashPrime s ∧ hashPrime s ≤ 2 * (s ^ 2 + 1) :=
  (Nat.exists_prime_lt_and_le_two_mul (s ^ 2 + 1) (Nat.succ_ne_zero _)).choose_spec

private instance (s : ℕ) : Fact (hashPrime s).Prime := ⟨(hashPrime_spec s).1⟩

open scoped Classical in
/-- Maps `ℕ → ℕ` with values below `s` such that every `s`-element set of numbers below `q` is
mapped injectively by one of them: for `s ≥ 2`, a linear hash map to numbers below a prime `p`
followed by a member for `(p, s / 2)` below a threshold and a member for `(p, s - s / 2)`,
shifted by `s / 2`, from the threshold on. -/
private noncomputable def splitHash (q s : ℕ) : Finset (ℕ → ℕ) :=
  if h : s < 2 then {0} else
    ((linearHash (hashPrime s) q ×ˢ range (hashPrime s)) ×ˢ
      splitHash (hashPrime s) (s / 2) ×ˢ splitHash (hashPrime s) (s - s / 2)).image
      fun ((u, θ), h₁, h₂) x => if u x < θ then h₁ (u x) else s / 2 + h₂ (u x)
termination_by s
decreasing_by all_goals omega

/-- Every `k` below the size of a set of numbers is the number of its elements below one of
its elements. -/
private lemma exists_card_filter_lt (T : Finset ℕ) {k : ℕ} (hk : k < #T) :
    ∃ θ ∈ T, #{t ∈ T | t < θ} = k := by
  refine ⟨T.orderEmbOfFin rfl ⟨k, hk⟩, T.orderEmbOfFin_mem rfl _, ?_⟩
  have h : {t ∈ T | t < T.orderEmbOfFin rfl ⟨k, hk⟩} =
      (Iio (⟨k, hk⟩ : Fin #T)).map (T.orderEmbOfFin rfl).toEmbedding := by
    ext t
    simp only [mem_filter, mem_map, mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ht, hlt⟩
      obtain ⟨j, rfl⟩ : t ∈ Set.range (T.orderEmbOfFin rfl) := by rwa [T.range_orderEmbOfFin]
      exact ⟨j, (T.orderEmbOfFin rfl).lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨T.orderEmbOfFin_mem rfl j, (T.orderEmbOfFin rfl).lt_iff_lt.2 hj⟩
  rw [h, card_map, Fin.card_Iio]

/-- `splitHash q s` is perfect for `s`-element sets of numbers below `q`, with values below
`s`. -/
private theorem exists_injOn_splitHash (s : ℕ) : ∀ (q : ℕ) (S : Finset ℕ), S ⊆ range q →
    #S = s → ∃ h ∈ splitHash q s, Set.InjOn h S ∧ ∀ x ∈ S, h x < s := by
  classical
  induction s using Nat.strong_induction_on with | _ s ih
  intro q S hS hcard
  rw [splitHash]
  split_ifs with hs
  · exact ⟨0, mem_singleton_self _, fun x hx y hy _ => card_le_one.1 (by omega) x hx y hy,
      fun x hx => hcard ▸ card_pos.2 ⟨x, hx⟩⟩
  obtain ⟨u, hu, hinj⟩ := exists_injOn_linearHash (p := hashPrime s) hS <| by
    have := (hashPrime_spec s).2.1
    rw [offDiag_card, hcard]
    exact (Nat.sub_le _ _).trans_lt (by rw [← sq]; omega)
  have hlt (t) (ht : t ∈ S.image u) : t ∈ range (hashPrime s) := by
    obtain ⟨x, -, rfl⟩ := mem_image.1 ht
    exact mem_range.2 (linearHash_lt hu x)
  obtain ⟨θ, hθ, hcount⟩ := exists_card_filter_lt (S.image u) (k := s / 2) <| by
    rw [card_image_of_injOn hinj]
    omega
  have hcount' := card_filter_add_card_filter_not (s := S.image u) (· < θ)
  rw [card_image_of_injOn hinj] at hcount'
  obtain ⟨h₁, hh₁, hinj₁, hlt₁⟩ := ih (s / 2) (by omega) (hashPrime s) {t ∈ S.image u | t < θ}
    (fun t ht => hlt t (mem_filter.1 ht).1) hcount
  obtain ⟨h₂, hh₂, hinj₂, hlt₂⟩ := ih (s - s / 2) (by omega) (hashPrime s)
    {t ∈ S.image u | ¬t < θ} (fun t ht => hlt t (mem_filter.1 ht).1) (by omega)
  have hmem₁ {x} (hx : x ∈ S) (h : u x < θ) : u x ∈ {t ∈ S.image u | t < θ} :=
    mem_filter.2 ⟨mem_image_of_mem u hx, h⟩
  have hmem₂ {x} (hx : x ∈ S) (h : ¬u x < θ) : u x ∈ {t ∈ S.image u | ¬t < θ} :=
    mem_filter.2 ⟨mem_image_of_mem u hx, h⟩
  refine ⟨fun x => if u x < θ then h₁ (u x) else s / 2 + h₂ (u x),
    mem_image.2 ⟨((u, θ), h₁, h₂), by simp [hu, hh₁, hh₂, mem_range.1 (hlt θ hθ)], rfl⟩,
    fun x hx y hy hxy => ?_, fun x hx => ?_⟩
  · dsimp only at hxy
    split_ifs at hxy with hx' hy' hy'
    · exact hinj hx hy (hinj₁ (hmem₁ hx hx') (hmem₁ hy hy') hxy)
    · have := hlt₁ _ (hmem₁ hx hx')
      omega
    · have := hlt₁ _ (hmem₁ hy hy')
      omega
    · exact hinj hx hy (hinj₂ (hmem₂ hx hx') (hmem₂ hy hy') (Nat.add_left_cancel hxy))
  · dsimp only
    split_ifs with hx'
    · have := hlt₁ _ (hmem₁ hx hx')
      omega
    · have := hlt₂ _ (hmem₂ hx hx')
      omega

/-- The size invariant of `splitHash`, for any constant `K` with `9 ^ 10 ≤ 2 ^ 8 * K`. -/
private theorem card_splitHash_mul_le {K : ℕ} (hK : 9 ^ 10 ≤ 2 ^ 8 * K) (s : ℕ) :
    ∀ q, q ≠ 0 → #(splitHash q s) * s ^ 8 ≤ q * K ^ (s - 1) := by
  classical
  induction s using Nat.strong_induction_on with | _ s ih
  intro q hq
  rw [splitHash]
  split_ifs with hs
  · interval_cases s
    · simp
    · simpa using Nat.one_le_iff_ne_zero.2 hq
  refine (Nat.mul_le_mul_right _ card_image_le).trans ?_
  rw [card_product, card_product, card_product, card_range]
  have hL := card_linearHash_le (p := hashPrime s) hq
  generalize #(linearHash (hashPrime s) q) = L at hL ⊢
  obtain ⟨hp, -, hle⟩ := hashPrime_spec s
  generalize hashPrime s = p at *
  have h₁ := ih (s / 2) (by omega) p hp.ne_zero
  have h₂ := ih (s - s / 2) (by omega) p hp.ne_zero
  generalize #(splitHash p (s / 2)) = N₁ at h₁
  generalize #(splitHash p (s - s / 2)) = N₂ at h₂
  have hab : 2 * s ^ 2 ≤ 9 * (s / 2 * (s - s / 2)) := by
    obtain ⟨k, rfl | rfl⟩ := s.even_or_odd'
    · rw [Nat.mul_div_cancel_left k two_pos, show 2 * k - k = k by omega]
      nlinarith
    · rw [show (2 * k + 1) / 2 = k by omega, show 2 * k + 1 - k = k + 1 by omega]
      nlinarith [show 1 ≤ k by omega]
  have hs' : 1 + (s / 2 - 1) + (s - s / 2 - 1) = s - 1 := by omega
  generalize s / 2 = a at *
  generalize s - a = b at *
  have hps : p ^ 4 * s ^ 8 ≤ K * (a * b) ^ 8 := by
    refine Nat.le_of_mul_le_mul_left (c := 2 ^ 8) ?_ (by positivity)
    calc 2 ^ 8 * (p ^ 4 * s ^ 8) ≤ 2 ^ 8 * ((3 * s ^ 2) ^ 4 * s ^ 8) := by
          gcongr
          nlinarith
      _ = 9 ^ 2 * (2 * s ^ 2) ^ 8 := by ring
      _ ≤ 9 ^ 2 * (9 * (a * b)) ^ 8 := by gcongr
      _ = 9 ^ 10 * (a * b) ^ 8 := by ring
      _ ≤ 2 ^ 8 * K * (a * b) ^ 8 := by gcongr
      _ = 2 ^ 8 * (K * (a * b) ^ 8) := mul_assoc ..
  refine Nat.le_of_mul_le_mul_right (c := (a * b) ^ 8) ?_ (by
    have : 0 < a * b := by nlinarith
    positivity)
  calc L * p * (N₁ * N₂) * s ^ 8 * (a * b) ^ 8
      = L * p * s ^ 8 * (N₁ * a ^ 8) * (N₂ * b ^ 8) := by ring
    _ ≤ p * q * p * s ^ 8 * (p * K ^ (a - 1)) * (p * K ^ (b - 1)) := by gcongr
    _ = q * (p ^ 4 * s ^ 8) * (K ^ (a - 1) * K ^ (b - 1)) := by ring
    _ ≤ q * (K * (a * b) ^ 8) * (K ^ (a - 1) * K ^ (b - 1)) := by gcongr
    _ = q * K ^ (1 + (a - 1) + (b - 1)) * (a * b) ^ 8 := by ring
    _ = q * K ^ (s - 1) * (a * b) ^ 8 := by rw [hs']

open scoped Classical in
/-- An explicit family of maps `Fin n → Fin r` that is a perfect hash family for `r`-element
sets when `0 < r` (`isPerfectHashFamily_perfectHashFamily`) and has at most `n * 2 ^ (25 * r)`
members (`card_perfectHashFamily_le`). It is empty when `n = 0` or `r = 0`.

The construction, by linear hashing and recursive splitting at a threshold, is ours; Schmidt
and Siegel (1990) construct families of the smaller size `2 ^ O(r) * (log n) ^ 2`. -/
noncomputable def perfectHashFamily (n r : ℕ) : Finset (Fin n → Fin r) :=
  if h : n = 0 ∨ r = 0 then ∅ else
    haveI : NeZero r := ⟨fun hr => h (.inr hr)⟩
    (splitHash n r).image fun h i => Fin.ofNat r (h i)

/-- Every `r`-element subset of `Fin n` is mapped injectively by a member of
`perfectHashFamily n r`, for `0 < r`. (For `r = 0 < n` there is no map `Fin n → Fin r`.) -/
theorem isPerfectHashFamily_perfectHashFamily (n r : ℕ) (hr : 0 < r) :
    IsPerfectHashFamily (perfectHashFamily n r) r := fun S hS => by
  classical
  have : NeZero r := ⟨hr.ne'⟩
  obtain ⟨x₀, -⟩ := card_pos.1 (hS ▸ hr)
  obtain ⟨h, hh, hinj, hlt⟩ := exists_injOn_splitHash r n (S.map Fin.valEmbedding)
    (fun x hx => by
      obtain ⟨y, -, rfl⟩ := mem_map.1 hx
      exact mem_range.2 y.isLt)
    (by rw [card_map, hS])
  rw [perfectHashFamily]
  split_ifs with h
  · have := x₀.pos
    omega
  refine ⟨_, mem_image_of_mem _ hh, fun x hx y hy hxy => ?_⟩
  have hx' : x.val ∈ S.map Fin.valEmbedding := mem_map_of_mem _ hx
  have hy' : y.val ∈ S.map Fin.valEmbedding := mem_map_of_mem _ hy
  have hval := congrArg Fin.val hxy
  simp only [Fin.val_ofNat] at hval
  rw [Nat.mod_eq_of_lt (hlt _ hx'), Nat.mod_eq_of_lt (hlt _ hy')] at hval
  exact Fin.val_injective (hinj hx' hy' hval)

/-- `perfectHashFamily n r` has at most `n * 2 ^ (25 * r)` members. This bound is ours;
Schmidt and Siegel (1990) prove `2 ^ O(r) * (log n) ^ 2` for a different family. -/
theorem card_perfectHashFamily_le (n r : ℕ) : #(perfectHashFamily n r) ≤ n * 2 ^ (25 * r) := by
  classical
  rw [perfectHashFamily]
  split_ifs with h
  · exact Nat.zero_le _
  calc _ ≤ #(splitHash n r) * r ^ 8 :=
        card_image_le.trans (Nat.le_mul_of_pos_right _ (pow_pos (by omega) 8))
    _ ≤ n * (2 ^ 25) ^ (r - 1) := card_splitHash_mul_le (by norm_num) r n (by omega)
    _ ≤ n * 2 ^ (25 * r) := by
      rw [← pow_mul]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))

end Cslib
