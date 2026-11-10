/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MinEntropy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Flat sources

A flat source is the uniform distribution on a finite set. A distribution on a finite type whose
outcomes all have probability at most `1 / K` is a mixture of flat distributions on sets of
exactly `K` outcomes (`exists_eq_bind_uniformOfFinset`). In particular, for a natural number `k`,
every `k`-source is a mixture of flat `k`-sources, the uniform distributions on sets of `2^k`
outcomes [Chor, Goldreich][ChorGoldreich1988], [Vadhan, Chapter 6][Vadhan2012]. Since mixtures of
`k`-sources are `k`-sources (`le_minEntropy_bind`), this characterizes the `k`-sources
(`le_minEntropy_iff_exists_eq_bind_uniformOfFinset`).

The proof is combinatorial. Scaled by `K`, the masses form a point of `[0, 1]^α` with coordinate
sum `K`. Moving weight between two coordinates strictly between `0` and `1` writes such a point
as a convex combination of two points with fewer such coordinates. When no such coordinate
remains, the point is the indicator of a set of `K` outcomes.

## Main results

* `Cslib.Probability.PMF.exists_eq_bind_uniformOfFinset`: a distribution with masses at most
  `1 / K` is a mixture of flat distributions on `K` outcomes.
* `Cslib.Probability.PMF.le_minEntropy_iff_exists_eq_bind_uniformOfFinset`: the `k`-sources are
  exactly the mixtures of flat `k`-sources.

## References

* [B. Chor, O. Goldreich, *Unbiased Bits from Sources of Weak Randomness and Probabilistic
  Communication Complexity*][ChorGoldreich1988]
* [S. Vadhan, *Pseudorandomness*][Vadhan2012], Chapter 6
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset

variable {α : Type*}

/-! ### Points of the hypersimplex -/

/-- The outcomes whose weight lies strictly between `0` and `1`. -/
private noncomputable def fractional [Fintype α] (f : α → ℝ) : Finset α :=
  univ.filter fun a => 0 < f a ∧ f a < 1

private theorem mem_fractional [Fintype α] {f : α → ℝ} {a : α} :
    a ∈ fractional f ↔ 0 < f a ∧ f a < 1 := by
  simp only [fractional, mem_filter, mem_univ, true_and]

/-- Weights in `{0, 1}` sum to the number of ones. -/
private theorem sum_eq_card_filter (s : Finset α) (f : α → ℝ)
    (h : ∀ a ∈ s, f a = 0 ∨ f a = 1) :
    ∑ a ∈ s, f a = (s.filter fun a => f a = 1).card := by
  rw [card_filter, Nat.cast_sum]
  refine sum_congr rfl fun a ha => ?_
  rcases h a ha with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Weights in `[0, 1]` outside the fractional set are `0` or `1`. -/
private theorem eq_zero_or_eq_one [Fintype α] {f : α → ℝ} (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    {a : α}
    (ha : a ∉ fractional f) : f a = 0 ∨ f a = 1 := by
  rw [mem_fractional] at ha
  rcases (hf a).1.eq_or_lt with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm (hf a).2 (not_lt.mp fun h' => ha ⟨h, h'⟩))

/-- Move `min (1 - f x) (f y)` units of weight from `y` to `x`. -/
private def transfer [DecidableEq α] (f : α → ℝ) (x y a : α) : ℝ :=
  f a + min (1 - f x) (f y) * ((if a = x then 1 else 0) - (if a = y then 1 else 0))

private theorem transfer_apply_left [DecidableEq α] (f : α → ℝ) {x y : α} (hxy : x ≠ y) :
    transfer f x y x = f x + min (1 - f x) (f y) := by
  simp [transfer, hxy]

private theorem transfer_apply_right [DecidableEq α] (f : α → ℝ) {x y : α} (hxy : x ≠ y) :
    transfer f x y y = f y - min (1 - f x) (f y) := by
  simp [transfer, hxy.symm, sub_eq_add_neg]

private theorem transfer_apply_of_ne [DecidableEq α] (f : α → ℝ) {x y a : α} (hax : a ≠ x)
    (hay : a ≠ y) : transfer f x y a = f a := by
  simp [transfer, hax, hay]

/-- Transferring weight between two fractional coordinates stays in the hypersimplex and makes
one of them integral. -/
private theorem transfer_spec [Fintype α] [DecidableEq α] {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) {x y : α} (hxy : x ≠ y) (hx : x ∈ fractional f)
    (hy : y ∈ fractional f) :
    (∀ a, 0 ≤ transfer f x y a ∧ transfer f x y a ≤ 1) ∧
      ∑ a, transfer f x y a = ∑ a, f a ∧ fractional (transfer f x y) ⊂ fractional f := by
  rw [mem_fractional] at hx hy
  have hleft := min_le_left (1 - f x) (f y)
  have hright := min_le_right (1 - f x) (f y)
  have hpos : 0 < min (1 - f x) (f y) := lt_min (by linarith) hy.1
  refine ⟨fun a => ?_, ?_, ?_⟩
  · by_cases hax : a = x
    · subst hax
      rw [transfer_apply_left f hxy]
      constructor <;> linarith [hf a]
    by_cases hay : a = y
    · subst hay
      rw [transfer_apply_right f hxy]
      constructor <;> linarith [hf a]
    rw [transfer_apply_of_ne f hax hay]
    exact hf a
  · simp only [transfer, sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_ite_eq', mem_univ,
      ite_true, sub_self, mul_zero, add_zero]
  · have hsubset : fractional (transfer f x y) ⊆ fractional f := by
      intro a ha
      by_cases hax : a = x
      · exact hax ▸ mem_fractional.mpr hx
      by_cases hay : a = y
      · exact hay ▸ mem_fractional.mpr hy
      rwa [mem_fractional, transfer_apply_of_ne f hax hay, ← mem_fractional] at ha
    rw [ssubset_iff_of_subset hsubset]
    rcases min_choice (1 - f x) (f y) with h | h
    · refine ⟨x, mem_fractional.mpr hx, fun hmem => ?_⟩
      rw [mem_fractional, transfer_apply_left f hxy, h] at hmem
      linarith [hmem.2]
    · refine ⟨y, mem_fractional.mpr hy, fun hmem => ?_⟩
      rw [mem_fractional, transfer_apply_right f hxy, h] at hmem
      linarith [hmem.1]

/-- Every point of `[0, 1]^α` with coordinate sum `K` is a convex combination of indicators of
`K`-element sets, by induction on the number of fractional coordinates. -/
private theorem exists_weights [Fintype α] [DecidableEq α] (K n : ℕ) (f : α → ℝ)
    (hn : (fractional f).card = n)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hsum : ∑ a, f a = K) :
    ∃ w : {S : Finset α // S.card = K} → ℝ, (∀ S, 0 ≤ w S) ∧ ∑ S, w S = 1 ∧
      ∀ a, ∑ S ∈ univ.filter (fun S => a ∈ S.1), w S = f a := by
  induction n using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  by_cases hempty : fractional f = ∅
  · -- Every weight is `0` or `1`, so `f` is the indicator of the set of its ones.
    have hint (a : α) : f a = 0 ∨ f a = 1 :=
      eq_zero_or_eq_one hf (by simp [hempty])
    have hcard : (univ.filter fun a => f a = 1).card = K := by
      have h := sum_eq_card_filter univ f fun a _ => hint a
      rw [hsum] at h
      exact_mod_cast h.symm
    refine ⟨fun S => if S = ⟨_, hcard⟩ then 1 else 0,
      fun S => by dsimp only; split_ifs <;> norm_num,
      by simp, fun a => ?_⟩
    rw [sum_ite_eq']
    rcases hint a with h | h <;> simp [h]
  · -- Split `f` along two distinct fractional coordinates.
    obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hempty
    obtain ⟨y, hy, hyx⟩ : ∃ y ∈ fractional f, y ≠ x := by
      by_contra! hsingle
      have hrest : ∑ a ∈ univ.erase x, f a = ((univ.erase x).filter fun a => f a = 1).card :=
        sum_eq_card_filter _ f fun a ha =>
          eq_zero_or_eq_one hf fun hmem => (mem_erase.mp ha).1 (hsingle a hmem)
      have htotal := add_sum_erase univ f (mem_univ x)
      rw [hsum, hrest] at htotal
      have hfx := mem_fractional.mp hx
      have hlt : ((univ.erase x).filter fun a => f a = 1).card < K := by
        exact_mod_cast (show (((univ.erase x).filter fun a => f a = 1).card : ℝ) < K by linarith)
      have hgt : K < ((univ.erase x).filter fun a => f a = 1).card + 1 := by
        exact_mod_cast (show (K : ℝ) < ((univ.erase x).filter fun a => f a = 1).card + 1 by
          linarith)
      omega
    obtain ⟨hf₁, hsum₁, hsub₁⟩ := transfer_spec hf hyx.symm hx hy
    obtain ⟨hf₂, hsum₂, hsub₂⟩ := transfer_spec hf hyx hy hx
    obtain ⟨w₁, hw₁, hone₁, hmass₁⟩ :=
      ih _ (hn ▸ card_lt_card hsub₁) _ rfl hf₁ (hsum₁.trans hsum)
    obtain ⟨w₂, hw₂, hone₂, hmass₂⟩ :=
      ih _ (hn ▸ card_lt_card hsub₂) _ rfl hf₂ (hsum₂.trans hsum)
    have hx' := mem_fractional.mp hx
    have hy' := mem_fractional.mp hy
    set d₁ := min (1 - f x) (f y)
    set d₂ := min (1 - f y) (f x)
    have hd₁ : 0 < d₁ := lt_min (by linarith) hy'.1
    have hd₂ : 0 < d₂ := lt_min (by linarith) hx'.1
    refine ⟨fun S => (d₂ * w₁ S + d₁ * w₂ S) / (d₁ + d₂),
      fun S => by have := hw₁ S; have := hw₂ S; positivity, ?_, fun a => ?_⟩
    · rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum, hone₁, hone₂]
      field_simp
      ring
    · rw [← sum_div, sum_add_distrib, ← mul_sum, ← mul_sum, hmass₁, hmass₂]
      field_simp
      simp only [transfer, d₁, d₂]
      split_ifs <;> ring

/-! ### Flat decompositions -/

/-- **Flat decomposition.** A distribution on a finite type whose outcomes all have probability
at most `1 / K` is a mixture of uniform distributions on sets of exactly `K` outcomes. -/
theorem exists_eq_bind_uniformOfFinset [Finite α] (p : PMF α) {K : ℕ} (hK : K ≠ 0)
    (hp : ∀ a, (p a).toReal ≤ (K : ℝ)⁻¹) :
    ∃ mix : PMF {S : Finset α // S.card = K},
      p = mix.bind fun S => uniformOfFinset S.1 (card_ne_zero.mp (S.2.trans_ne hK)) := by
  classical
  let := Fintype.ofFinite α
  have hKpos : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK
  obtain ⟨w, hw, hone, hmass⟩ := exists_weights K _ (fun a => K * (p a).toReal) rfl
    (fun a => ⟨by positivity, by
      calc (K : ℝ) * (p a).toReal ≤ K * (K : ℝ)⁻¹ := by gcongr; exact hp a
        _ = 1 := mul_inv_cancel₀ hKpos.ne'⟩)
    (by rw [← mul_sum, sum_toReal, mul_one])
  let mix : PMF {S : Finset α // S.card = K} := PMF.ofFintype (fun S => ENNReal.ofReal (w S))
    (by rw [← ENNReal.ofReal_sum_of_nonneg fun S _ => hw S, hone, ENNReal.ofReal_one])
  refine ⟨mix, PMF.ext fun a => ?_⟩
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    bind_apply_toReal]
  have hterm (S : {S : Finset α // S.card = K}) :
      (mix S).toReal * (uniformOfFinset S.1 (card_ne_zero.mp (S.2.trans_ne hK)) a).toReal =
        if a ∈ S.1 then w S * (K : ℝ)⁻¹ else 0 := by
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (hw S), uniformOfFinset_apply]
    split_ifs
    · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, S.2]
    · rw [ENNReal.toReal_zero, mul_zero]
  simp only [hterm]
  rw [← sum_filter, ← sum_mul, hmass a, mul_comm, ← mul_assoc, inv_mul_cancel₀ hKpos.ne',
    one_mul]

/-- **Every `k`-source is a mixture of flat `k`-sources.** A distribution with min-entropy at
least a natural number `k` is a mixture of uniform distributions on sets of `2^k` outcomes. -/
theorem exists_eq_bind_uniformOfFinset_of_le_minEntropy [Finite α] (p : PMF α) {k : ℕ}
    (hk : (k : ℝ) ≤ minEntropy p) :
    ∃ mix : PMF {S : Finset α // S.card = 2 ^ k},
      p = mix.bind fun S =>
        uniformOfFinset S.1 (card_ne_zero.mp (S.2.trans_ne (pow_ne_zero k two_ne_zero))) :=
  exists_eq_bind_uniformOfFinset p (pow_ne_zero k two_ne_zero) fun a => by
    have h := (le_minEntropy_iff p).mp hk a
    rwa [Real.rpow_neg (by norm_num), Real.rpow_natCast, ← Nat.cast_ofNat, ← Nat.cast_pow] at h

/-- **`k`-sources are mixtures of flat `k`-sources.** For a natural number `k`, a distribution has
min-entropy at least `k` exactly when it is a mixture of uniform distributions on sets of `2^k`
outcomes. -/
theorem le_minEntropy_iff_exists_eq_bind_uniformOfFinset [Finite α] (p : PMF α) (k : ℕ) :
    (k : ℝ) ≤ minEntropy p ↔ ∃ mix : PMF {S : Finset α // S.card = 2 ^ k},
      p = mix.bind fun S =>
        uniformOfFinset S.1 (card_ne_zero.mp (S.2.trans_ne (pow_ne_zero k two_ne_zero))) := by
  refine ⟨exists_eq_bind_uniformOfFinset_of_le_minEntropy p, ?_⟩
  rintro ⟨mix, rfl⟩
  refine le_minEntropy_bind _ _ fun S _ => ?_
  rw [minEntropy_uniformOfFinset, S.2, Nat.cast_pow, Nat.cast_ofNat,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

end Cslib.Probability.PMF
