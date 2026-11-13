/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Computability.Communication.Rectangle
public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Foundations.BooleanAnalysis.HadamardRectangles
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.PMF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The discrepancy bound and the inner product

The *discrepancy* of `f : X → Y → Bool` under a distribution `ν` on `X × Y` is the largest
imbalance `|ν(S ∩ f⁻¹ false) - ν(S ∩ f⁻¹ true)|` over rectangles `S = A × B` (`discrepancy`)
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]. The output of a protocol is constant on
each leaf rectangle, so its correlation with `f` under `ν`, which is `1 - 2 ε` for a protocol
erring with probability `ε` on inputs drawn from `ν`, is at most the number of leaves times the
discrepancy (`Protocol.abs_sum_mul_signVal_le`, splitting the sum by
`Protocol.sum_eq_sum_leaves`). Hence a protocol sending `c` bits with error `1 / 2 - γ` under `ν`
has `2 γ ≤ 2 ^ c disc_ν(f)` (`Protocol.two_mul_le_two_pow_mul_discrepancy`), and by averaging the
same holds for public-coin protocols with error `1 / 2 - γ` on every input
(`PublicCoin.two_mul_le_two_pow_mul_discrepancy`).

For the inner product, Lindsey's lemma (`Matrix.sq_sum_bilinear_mul_two_pow_rank_le`) bounds the
signed sum of the inner product modulo two over a rectangle `A × B` of `n`-bit strings by
`√(|A| |B| 2 ^ n)` (`BitString.sq_sum_signVal_dotProduct_le`), so under the uniform distribution
the inner product has discrepancy at most `2 ^ (-n / 2)`
(`discrepancy_dotProduct_sq_mul_two_pow_le`). So public-coin protocols for the inner product with
error `1 / 2 - γ` send `c` bits with `(2 γ)² 2 ^ n ≤ 4 ^ c`
(`PublicCoin.Solves.sq_mul_two_pow_le_four_pow_of_dotProduct`), and with error `1 / 3` at least
`(n - 3) / 2` bits: `R(IP) = Ω(n)` (`PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three`)
[Chor and Goldreich][ChorGoldreich1988].

## Main definitions

* `Cslib.Communication.discrepancy`: the discrepancy of a Boolean function under a distribution.

## Main results

* `Cslib.Communication.one_div_discrepancy_le_tilingNumber`: the arbitrary tiling bound.
* `Cslib.Communication.Protocol.two_mul_le_two_pow_mul_discrepancy`,
  `Cslib.Communication.PublicCoin.two_mul_le_two_pow_mul_discrepancy`: the discrepancy bound.
* `Cslib.Communication.discrepancy_dotProduct_sq_mul_two_pow_le`: the discrepancy of the inner
  product.
* `Cslib.Communication.PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three`,
  `Cslib.Communication.PrivateCoin.le_two_mul_ecomplexityFun_dotProduct_add_three`: randomized
  protocols for the inner product of `n` bits send `Ω(n)` bits.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
* [B. Chor and O. Goldreich, *Unbiased bits from sources of weak randomness and probabilistic
  communication complexity*][ChorGoldreich1988]
* [S. Jukna, *Extremal Combinatorics*, Ch. 14][Jukna2011]
-/

@[expose] public section

namespace Cslib.Communication

open Finset BitString Probability

variable {X Y Z : Type*}

/-! ### Discrepancy -/

/-- The *discrepancy* of `f : X → Y → Bool` under a distribution `ν` on `X × Y`: the largest
imbalance `|ν(S ∩ f⁻¹ false) - ν(S ∩ f⁻¹ true)|` of `f` on a rectangle `S = A × B`, written as the
signed sum `|∑_{x ∈ A, y ∈ B} ν(x, y) (-1)^{f x y}|`. The results about it assume that `X` and `Y`
are finite. -/
noncomputable def discrepancy (ν : PMF (X × Y)) (f : X → Y → Bool) : ℝ :=
  ⨆ S : Finset X × Finset Y, |∑ x ∈ S.1, ∑ y ∈ S.2, (ν (x, y)).toReal * signVal (f x y)|

variable {ν : PMF (X × Y)} {f : X → Y → Bool}

section Finite

variable [Finite X] [Finite Y]

theorem abs_sum_le_discrepancy (ν : PMF (X × Y)) (f : X → Y → Bool) (A : Finset X)
    (B : Finset Y) :
    |∑ x ∈ A, ∑ y ∈ B, (ν (x, y)).toReal * signVal (f x y)| ≤ discrepancy ν f :=
  le_ciSup (f := fun S : Finset X × Finset Y =>
    |∑ x ∈ S.1, ∑ y ∈ S.2, (ν (x, y)).toReal * signVal (f x y)|) (Set.finite_range _).bddAbove
    (A, B)

/-- The discrepancy is attained on some rectangle. -/
theorem exists_abs_sum_eq_discrepancy (ν : PMF (X × Y)) (f : X → Y → Bool) :
    ∃ (A : Finset X) (B : Finset Y),
      |∑ x ∈ A, ∑ y ∈ B, (ν (x, y)).toReal * signVal (f x y)| = discrepancy ν f := by
  obtain ⟨S, hS⟩ := exists_eq_ciSup_of_finite (f := fun S : Finset X × Finset Y =>
    |∑ x ∈ S.1, ∑ y ∈ S.2, (ν (x, y)).toReal * signVal (f x y)|)
  exact ⟨S.1, S.2, hS⟩

theorem discrepancy_nonneg : 0 ≤ discrepancy ν f :=
  (abs_nonneg _).trans (abs_sum_le_discrepancy ν f ∅ ∅)

end Finite

/-! ### The discrepancy bound -/

namespace RectanglePartition

/-- **Correlation with a rectangle partition is bounded by discrepancy**: the correlation of `f`
with the partition labels is at most its number of pieces times the discrepancy of `f`
under `ν`. -/
theorem abs_sum_mul_signVal_le [Fintype X] [Fintype Y]
    (p : RectanglePartition X Y Bool) (ν : PMF (X × Y))
    (f : X → Y → Bool) :
    |∑ x, ∑ y, (ν (x, y)).toReal * signVal (f x y) * signVal (p.run x y)| ≤
      p.size * discrepancy ν f := by
  classical
  rw [p.sum_eq_sum_rectangles]
  calc |∑ i, ∑ x with x ∈ p.alice i, ∑ y with y ∈ p.bob i,
          (ν (x, y)).toReal * signVal (f x y) * signVal (p.run x y)|
      = |∑ i, signVal (p.output i) * ∑ x with x ∈ p.alice i,
          ∑ y with y ∈ p.bob i, (ν (x, y)).toReal * signVal (f x y)| := by
        congr 1
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun x hx => ?_
        rw [mul_sum]
        refine sum_congr rfl fun y hy => ?_
        rw [run_eq_output (mem_filter.mp hx).2 (mem_filter.mp hy).2]
        ring
    _ ≤ ∑ i, |signVal (p.output i) * ∑ x with x ∈ p.alice i,
          ∑ y with y ∈ p.bob i, (ν (x, y)).toReal * signVal (f x y)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin p.size, discrepancy ν f := by
        refine sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_signVal, one_mul]
        exact abs_sum_le_discrepancy ν f _ _
    _ = p.size * discrepancy ν f := by simp

/-- Every monochromatic tiling has size times discrepancy at least one, for any input PMF. -/
theorem one_le_size_mul_discrepancy [Finite X] [Finite Y]
    (p : RectanglePartition X Y Bool) {f : X → Y → Bool} (hp : p.run = f)
    (ν : PMF (X × Y)) : 1 ≤ p.size * discrepancy ν f := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  have h := p.abs_sum_mul_signVal_le ν f
  rw [hp] at h
  simp only [mul_assoc, signVal_mul_self, mul_one] at h
  rw [← Fintype.sum_prod_type', PMF.sum_toReal, abs_one] at h
  exact h

end RectanglePartition

/-- The minimum arbitrary monochromatic tiling satisfies the discrepancy bound, for any PMF. -/
theorem one_le_tilingNumber_mul_discrepancy [Finite X] [Finite Y]
    (ν : PMF (X × Y)) (f : X → Y → Bool) :
    1 ≤ (tilingNumber f).toNat * discrepancy ν f := by
  obtain ⟨p, hp, hmin⟩ := exists_minimal_tiling f
  rw [← hmin, ENat.toNat_natCast]
  exact p.one_le_size_mul_discrepancy hp ν

/-- **The arbitrary-tiling discrepancy bound** [AroraBarak07, Lemma 12.11]. The PMF may be
nonuniform; on equal bit cubes the uniform PMF gives the draft's normalization. -/
theorem one_div_discrepancy_le_tilingNumber [Finite X] [Finite Y]
    (ν : PMF (X × Y)) (f : X → Y → Bool) :
    1 / discrepancy ν f ≤ (tilingNumber f).toNat := by
  have h := one_le_tilingNumber_mul_discrepancy ν f
  have hd : 0 < discrepancy ν f := by
    have hn : (0 : ℝ) ≤ (tilingNumber f).toNat := Nat.cast_nonneg _
    nlinarith [discrepancy_nonneg (ν := ν) (f := f)]
  exact (div_le_iff₀ hd).mpr h

namespace Protocol

/-- **Correlation with a protocol is bounded by discrepancy**: the correlation under `ν` of `f`
with the output of a protocol is at most the number of its leaves times the discrepancy of `f`
under `ν`. -/
theorem abs_sum_mul_signVal_le [Fintype X] [Fintype Y] (p : Protocol X Y Bool) (ν : PMF (X × Y))
    (f : X → Y → Bool) :
    |∑ x, ∑ y, (ν (x, y)).toReal * signVal (f x y) * signVal (p.run x y)| ≤
      p.leafCount * discrepancy ν f := by
  have h := p.toRectanglePartition.abs_sum_mul_signVal_le ν f
  rw [run_toRectanglePartition] at h
  simpa only [toRectanglePartition] using h

/-- The correlation under `ν` of `f` with the output of a protocol is `1 - 2 ε`, where `ε` is the
probability that the protocol errs on inputs drawn from `ν`. -/
theorem sum_mul_signVal_eq [Fintype X] [Fintype Y] (p : Protocol X Y Bool) (ν : PMF (X × Y))
    (f : X → Y → Bool) :
    ∑ x, ∑ y, (ν (x, y)).toReal * signVal (f x y) * signVal (p.run x y) =
      1 - 2 * p.distributionalError ν (fun x y b => f x y = b) := by
  classical
  rw [distributionalError, PMF.toOuterMeasure_apply_toReal, ← PMF.sum_toReal ν, mul_sum,
    ← sum_sub_distrib, ← Fintype.sum_prod_type' (fun x y =>
      (ν (x, y)).toReal * signVal (f x y) * signVal (p.run x y))]
  refine sum_congr rfl fun q _ => ?_
  rw [mul_assoc, signVal_mul_signVal]
  by_cases h : f q.1 q.2 = p.run q.1 q.2
  · simp [h]
  · simp only [h, ite_false, Set.mem_ofPred_eq, not_false_eq_true, ite_true]
    ring

/-- **The discrepancy bound** for deterministic protocols: a protocol erring with probability at
most `1 / 2 - γ` on inputs drawn from `ν` has `2 γ ≤ 2 ^ depth · disc_ν(f)`. -/
theorem two_mul_le_two_pow_mul_discrepancy [Finite X] [Finite Y] (p : Protocol X Y Bool)
    {γ : ℝ} (hp : p.distributionalError ν (fun x y b => f x y = b) ≤ 1 / 2 - γ) :
    2 * γ ≤ 2 ^ p.depth * discrepancy ν f := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  have h := p.abs_sum_mul_signVal_le ν f
  rw [p.sum_mul_signVal_eq] at h
  have hleaves : (p.leafCount : ℝ) ≤ 2 ^ p.depth := by exact_mod_cast p.leafCount_le_two_pow_depth
  calc 2 * γ ≤ |1 - 2 * p.distributionalError ν (fun x y b => f x y = b)| :=
        le_trans (by linarith) (le_abs_self _)
    _ ≤ p.leafCount * discrepancy ν f := h
    _ ≤ 2 ^ p.depth * discrepancy ν f := mul_le_mul_of_nonneg_right hleaves discrepancy_nonneg

end Protocol

namespace PublicCoin

/-- **The discrepancy bound** for public-coin protocols: a public-coin protocol sending at most
`c` bits and computing `f` with error at most `1 / 2 - γ` on every input has
`2 γ ≤ 2 ^ c · disc_ν(f)` for every distribution `ν`. -/
theorem Solves.two_mul_le_two_pow_mul_discrepancy [Finite X] [Finite Y] {μ : PublicCoin X Y Bool}
    {γ : ℝ} {c : ℕ} (hμ : μ.Solves (1 / 2 - γ) (fun x y b => f x y = b) Set.univ Set.univ)
    (hc : μ.depth ≤ c) (ν : PMF (X × Y)) : 2 * γ ≤ 2 ^ c * discrepancy ν f := by
  obtain ⟨p, hp, herr⟩ := hμ.exists_distributionalError_le ν fun _ _ => ⟨trivial, trivial⟩
  have hd : p.depth ≤ c := by exact_mod_cast (depth_le_depth hp).trans hc
  exact (p.two_mul_le_two_pow_mul_discrepancy herr).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hd) discrepancy_nonneg)

/-- **The discrepancy bound**: if `f` has public-coin communication complexity at most `c` with
error `1 / 2 - γ`, then `2 γ ≤ 2 ^ c · disc_ν(f)` for every distribution `ν`. -/
theorem two_mul_le_two_pow_mul_discrepancy [Finite X] [Finite Y] {γ : ℝ} {c : ℕ}
    (h : ecomplexityFun (1 / 2 - γ) f ≤ c) (ν : PMF (X × Y)) :
    2 * γ ≤ 2 ^ c * discrepancy ν f := by
  obtain ⟨μ, hμ, hc⟩ := ecomplexity_le_iff.mp h
  exact hμ.two_mul_le_two_pow_mul_discrepancy hc ν

end PublicCoin

/-! ### The inner product -/

/-- **The inner product has discrepancy at most `2 ^ (-n / 2)`** under the uniform distribution on
pairs of `n`-bit strings, in the form `disc² · 2 ^ n ≤ 1`. -/
theorem discrepancy_dotProduct_sq_mul_two_pow_le (n : ℕ) :
    discrepancy (PMF.uniformOfFintype (BitString n × BitString n)) (fun x y => x ⬝ᵥ y) ^ 2 *
      2 ^ n ≤ 1 := by
  obtain ⟨A, B, hAB⟩ := exists_abs_sum_eq_discrepancy
    (PMF.uniformOfFintype (BitString n × BitString n)) (fun x y => x ⬝ᵥ y)
  rw [← hAB]
  have hcard : Fintype.card (BitString n × BitString n) = 2 ^ n * 2 ^ n := by
    simp [Fintype.card_prod]
  simp only [PMF.uniformOfFintype_apply, hcard, ← mul_sum]
  set S := ∑ x ∈ A, ∑ y ∈ B, signVal (x ⬝ᵥ y)
  have hS := BitString.sq_sum_signVal_dotProduct_le A B
  rw [Fintype.card_fin] at hS
  have hA : (#A : ℝ) ≤ 2 ^ n := by
    exact_mod_cast (card_le_univ A).trans_eq (by simp)
  have hB : (#B : ℝ) ≤ 2 ^ n := by
    exact_mod_cast (card_le_univ B).trans_eq (by simp)
  have hN : (0 : ℝ) < 2 ^ n := by positivity
  have hAB' : (#A : ℝ) * #B ≤ 2 ^ n * 2 ^ n :=
    mul_le_mul hA hB (Nat.cast_nonneg _) hN.le
  rw [abs_mul, mul_pow, sq_abs, sq_abs]
  push_cast
  rw [ENNReal.toReal_inv, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have hS' : S ^ 2 ≤ 2 ^ n * 2 ^ n * 2 ^ n :=
    hS.trans (mul_le_mul_of_nonneg_right hAB' hN.le)
  rw [inv_pow, mul_assoc, inv_mul_le_iff₀ (by positivity)]
  nlinarith

/-- **Randomized protocols for the inner product**: a public-coin protocol computing the inner
product modulo two of two `n`-bit strings with error at most `1 / 2 - γ`, for `γ ≥ 0`, and sending
at most `c` bits has `(2 γ)² 2 ^ n ≤ 4 ^ c`. -/
theorem PublicCoin.Solves.sq_mul_two_pow_le_four_pow_of_dotProduct {n c : ℕ} {γ : ℝ}
    {μ : PublicCoin (BitString n) (BitString n) Bool}
    (hμ : μ.Solves (1 / 2 - γ) (fun x y b => x ⬝ᵥ y = b) Set.univ Set.univ) (hc : μ.depth ≤ c)
    (hγ : 0 ≤ γ) : (2 * γ) ^ 2 * 2 ^ n ≤ 4 ^ c := by
  set D := discrepancy (PMF.uniformOfFintype (BitString n × BitString n)) (fun x y => x ⬝ᵥ y)
  have h := hμ.two_mul_le_two_pow_mul_discrepancy hc
    (PMF.uniformOfFintype (BitString n × BitString n))
  have hD := discrepancy_dotProduct_sq_mul_two_pow_le n
  have hsq : (2 * γ) ^ 2 ≤ (2 ^ c * D) ^ 2 := pow_le_pow_left₀ (by linarith) h 2
  have h4 : ((2 : ℝ) ^ c) ^ 2 = 4 ^ c := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hN : (0 : ℝ) ≤ 2 ^ n := by positivity
  calc (2 * γ) ^ 2 * 2 ^ n ≤ (2 ^ c * D) ^ 2 * 2 ^ n := mul_le_mul_of_nonneg_right hsq hN
    _ = 4 ^ c * (D ^ 2 * 2 ^ n) := by rw [mul_pow, h4, mul_assoc]
    _ ≤ 4 ^ c * 1 := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = 4 ^ c := mul_one _

/-- **The inner product needs `Ω(n)` bits with public coins**: computing the inner product modulo
two of two `n`-bit strings with error `1 / 3` needs at least `(n - 3) / 2` bits. -/
theorem PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three (n : ℕ) :
    (n : ℕ∞) ≤
      2 * PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString n => x ⬝ᵥ y) + 3 := by
  cases h : PublicCoin.ecomplexityFun (1 / 3) (fun x y : BitString n => x ⬝ᵥ y)
    using ENat.recTopCoe with
  | top => simp
  | coe c =>
    obtain ⟨μ, hμ, hc⟩ := PublicCoin.ecomplexity_le_iff.mp h.le
    have hμ' : μ.Solves (1 / 2 - 1 / 6) (fun x y b => x ⬝ᵥ y = b) Set.univ Set.univ :=
      hμ.mono (by norm_num) subset_rfl subset_rfl
    have hbound := hμ'.sq_mul_two_pow_le_four_pow_of_dotProduct hc (by norm_num)
    have hreal : (2 : ℝ) ^ n ≤ 9 * 4 ^ c := by nlinarith
    have hnat : 2 ^ n < 2 ^ (2 * c + 4) := by
      have : 2 ^ n ≤ 9 * 4 ^ c := by exact_mod_cast hreal
      calc 2 ^ n ≤ 9 * 4 ^ c := this
        _ < 16 * 4 ^ c := by
          have h4 : 0 < 4 ^ c := by positivity
          omega
        _ = 2 ^ (2 * c + 4) := by rw [pow_add, pow_mul]; norm_num; ring
    have hn := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hnat
    exact_mod_cast (by omega : n ≤ 2 * c + 3)

/-- **The inner product needs `Ω(n)` bits with private coins**: computing the inner product modulo
two of two `n`-bit strings with error `1 / 3` needs at least `(n - 3) / 2` bits. -/
theorem PrivateCoin.le_two_mul_ecomplexityFun_dotProduct_add_three (n : ℕ) :
    (n : ℕ∞) ≤
      2 * PrivateCoin.ecomplexityFun (1 / 3) (fun x y : BitString n => x ⬝ᵥ y) + 3 :=
  (PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three n).trans
    (by gcongr; exact PublicCoin.ecomplexityFun_le_privateCoin)

end Cslib.Communication
