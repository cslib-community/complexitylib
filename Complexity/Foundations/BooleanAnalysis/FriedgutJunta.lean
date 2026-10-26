/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.KahnKalaiLinial
public import Mathlib.Logic.Function.DependsOn
import Complexity.Foundations.BooleanAnalysis.FourierRestriction
import Complexity.Foundations.BooleanAnalysis.HammingFourier
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Friedgut's junta theorem

A Boolean function of small total influence is close to a function of few coordinates: if
`I[F] ≤ K` for a Boolean function `f` read as signs `F`, then for every `ε > 0`, `f` agrees with a
function of at most `4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates outside a fraction `ε` of the
inputs (`BitString.exists_dependsOn_hammingDist_div_le_of_totalInfluence_le`), so, for `ε ≤ 1`,
with a function of at most `3 · 2 ^ (8 K / ε)` coordinates
(`BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`) [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. A function of the coordinates in `J` is a `J`-junta,
written with Mathlib's `DependsOn`.

## Proof

Averaging out the coordinates outside a set `J` keeps the Fourier coefficients on the subsets of
`J` and kills the others (`BitString.fourierCoeff_expect_piecewise`), so `f` is within mean square
distance `∑_{S ⊄ J} F̂(S) ^ 2` of a function of the coordinates in `J`, and rounding it to a sign
gives a Boolean `J`-junta at relative Hamming distance at most that weight
(`BitString.exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq`). For the set `J`
of the coordinates of influence more than `τ`, the weight outside the subsets of `J` is at most
`log 3 / log A · I[F] + A / 3 · √τ · I[F]` for every `A > 1`
(`BitString.sum_filter_not_subset_fourierCoeff_sq_le`): the sets of size `m` with `3 ^ m ≥ A`
carry weight at most `log 3 / log A · I[F]`, and the hypercontractive bound of the
Kahn–Kalai–Linial theorem, `∑_{S ∋ i} 3 ^ (-|S|) F̂(S) ^ 2 ≤ Infᵢ[F] ^ (3/2) / 3`, summed over
the coordinates `i ∉ J`, bounds the others. Taking `A = 9 ^ (K / ε)` and
`√τ = 3 ε / (2 K A)` makes both terms at most `ε / 2`, and `J` has at most `K / τ` elements.

## Main results

* `Cslib.BitString.exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq`: a Boolean
  function is close to a `J`-junta when its Fourier weight is concentrated on the subsets of `J`.
* `Cslib.BitString.sum_filter_not_subset_fourierCoeff_sq_le`: the Fourier weight outside the
  subsets of the set of influential coordinates.
* `Cslib.BitString.exists_dependsOn_hammingDist_div_le_of_totalInfluence_le`,
  `Cslib.BitString.exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le`: Friedgut's
  junta theorem.

## References

* [E. Friedgut, *Boolean functions with low average sensitivity depend on few
  coordinates*][Friedgut1998]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Juntas from spectral concentration -/

/-- Rounding a real number to a sign costs at most its square distance to a sign: if `b` is the
bit of the sign of `t`, `(signVal a - signVal b) ^ 2 / 4 ≤ (signVal a - t) ^ 2`. -/
private theorem sq_signVal_sub_signVal_decide_div_four_le (a : Bool) (t : ℝ) :
    (signVal a - signVal (decide (t < 0))) ^ 2 / 4 ≤ (signVal a - t) ^ 2 := by
  by_cases ht : t < 0
  · simp only [ht, decide_true, signVal_true]
    cases a
    · simp only [signVal_false]
      nlinarith
    · simp only [signVal_true]
      nlinarith [sq_nonneg (-1 - t)]
  · simp only [ht, decide_false, signVal_false]
    cases a
    · simp only [signVal_false]
      nlinarith [sq_nonneg (1 - t)]
    · simp only [signVal_true]
      nlinarith

/-- **Spectral concentration gives a junta**: a Boolean function is at relative Hamming distance
at most `∑_{S ⊄ J} F̂(S) ^ 2` from a Boolean function of the coordinates in `J`, the sign of its
average over the other coordinates [O'Donnell, Proposition 3.31][ODonnell2014]. -/
theorem exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq (f : (ι → Bool) → Bool)
    (J : Finset ι) :
    ∃ g : (ι → Bool) → Bool, DependsOn g (J : Set ι) ∧
      (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤
        ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 := by
  set h : (ι → Bool) → ℝ := fun x => 𝔼 z, signVal (f (J.piecewise x z))
  refine ⟨fun x => decide (h x < 0), fun x y hxy => ?_, ?_⟩
  · have : h x = h y := expect_congr rfl fun z _ => by
      rw [J.piecewise_congr (fun i hi => hxy i (mem_coe.2 hi)) fun _ _ => rfl]
    simp only [this]
  · have hd := expect_sq_signVal_sub_signVal f fun x => decide (h x < 0)
    rw [← expect_sub_expect_piecewise_sq,
      show (hammingDist f fun x => decide (h x < 0) : ℝ) / 2 ^ Fintype.card ι =
        (𝔼 x, (signVal (f x) - signVal (decide (h x < 0))) ^ 2) / 4 by rw [hd]; ring,
      expect_div]
    exact expect_le_expect fun x _ => sq_signVal_sub_signVal_decide_div_four_le _ _

/-! ### The weight outside the influential coordinates -/

/-- If every coordinate outside `J` has influence at most `τ` on `F = signVal ∘ f`, then the
`1/3`-damped Fourier weight of sets meeting `Jᶜ`, counted with multiplicity `#(S \ J)`, is at
most `√τ / 3 * totalInfluence F`. -/
private theorem sum_card_sdiff_mul_one_third_pow_fourierCoeff_sq_le
    (f : (ι → Bool) → Bool) {J : Finset ι} {τ : ℝ}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ τ) :
    ∑ S : Finset ι, (#(S \ J) : ℝ) *
      ((1 / 3) ^ #S * fourierCoeff (fun x => signVal (f x)) S ^ 2) ≤
      √τ / 3 * totalInfluence (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set g : Finset ι → ℝ := fun S => (1 / 3) ^ #S * fourierCoeff F S ^ 2
  -- the sets meeting the complement of `J`, counted with multiplicity
  have hswap : ∑ S, (#(S \ J) : ℝ) * g S = ∑ i with i ∉ J, ∑ S with i ∈ S, g S := by
    have h := sum_comm' (s := univ) (t := fun S => S \ J) (t' := univ.filter (· ∉ J))
      (s' := fun i => univ.filter (i ∈ ·)) (f := fun S _ => g S) (fun S i => by simp [and_comm])
    rw [← h]
    exact sum_congr rfl fun S _ => by rw [sum_const, nsmul_eq_mul]
  rw [hswap]
  calc ∑ i with i ∉ J, ∑ S with i ∈ S, g S
      ≤ ∑ i with i ∉ J, influence i F * √τ / 3 := by
        refine sum_le_sum fun i hi => ?_
        refine (sum_filter_mem_one_third_pow_mul_fourierCoeff_sq_le f i).trans ?_
        have := Real.sqrt_le_sqrt (hJ i (mem_filter.1 hi).2)
        have := influence_nonneg i F
        gcongr
    _ ≤ ∑ i, influence i F * √τ / 3 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ =>
          div_nonneg (mul_nonneg (influence_nonneg i F) (Real.sqrt_nonneg τ)) (by norm_num)
    _ = √τ / 3 * totalInfluence F := by
        rw [totalInfluence, mul_sum]
        exact sum_congr rfl fun i _ => by ring

/-- **The Fourier weight outside the influential coordinates**: if every coordinate outside `J`
has influence at most `τ` on a Boolean function read as signs `F`, then for every `A > 1`,
`∑_{S ⊄ J} F̂(S) ^ 2 ≤ log 3 / log A · I[F] + A / 3 · √τ · I[F]`
[O'Donnell, Theorem 9.28][ODonnell2014]. -/
theorem sum_filter_not_subset_fourierCoeff_sq_le (f : (ι → Bool) → Bool) {J : Finset ι} {τ : ℝ}
    (hJ : ∀ i ∉ J, influence i (fun x => signVal (f x)) ≤ τ) {A : ℝ} (hA : 1 < A) :
    ∑ S with ¬S ⊆ J, fourierCoeff (fun x => signVal (f x)) S ^ 2 ≤
      log 3 / log A * totalInfluence (fun x => signVal (f x)) +
        A / 3 * √τ * totalInfluence (fun x => signVal (f x)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set c : Finset ι → ℝ := fun S => fourierCoeff F S ^ 2
  set g : Finset ι → ℝ := fun S => (1 / 3) ^ #S * c S
  have hc (S : Finset ι) : 0 ≤ c S := sq_nonneg _
  have hg (S : Finset ι) : 0 ≤ g S := mul_nonneg (by positivity) (hc S)
  have hA0 : 0 ≤ A := by linarith
  have hL : 0 ≤ log 3 / log A := div_nonneg (log_pos (by norm_num)).le (log_pos hA).le
  -- each set outside the subsets of `J` has large size or meets the complement of `J`
  have hpt (S : Finset ι) (hS : ¬S ⊆ J) :
      c S ≤ log 3 / log A * (#S * c S) + A * (#(S \ J) * g S) := by
    obtain ⟨i, hiS, hiJ⟩ := not_subset.1 hS
    have hk : (1 : ℝ) ≤ #(S \ J) := Nat.one_le_cast.2 (card_pos.2 ⟨i, mem_sdiff.2 ⟨hiS, hiJ⟩⟩)
    have h1 : 0 ≤ log 3 / log A * (#S * c S) := mul_nonneg hL (mul_nonneg (by positivity) (hc S))
    have h2 : 0 ≤ A * (#(S \ J) * g S) := mul_nonneg hA0 (mul_nonneg (by positivity) (hg S))
    rcases one_le_mul_log_three_div_log_or_one_lt_mul_one_third_pow hA #S with h | h
    · nlinarith [hc S]
    · have : c S ≤ A * (1 / 3) ^ #S * c S := le_mul_of_one_le_left (hc S) h.le
      nlinarith [hc S, hg S]
  have hlow := sum_card_sdiff_mul_one_third_pow_fourierCoeff_sq_le f hJ
  calc ∑ S with ¬S ⊆ J, c S
      ≤ ∑ S with ¬S ⊆ J, (log 3 / log A * (#S * c S) + A * (#(S \ J) * g S)) :=
        sum_le_sum fun S hS => hpt S (mem_filter.1 hS).2
    _ ≤ ∑ S, (log 3 / log A * (#S * c S) + A * (#(S \ J) * g S)) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun S _ _ =>
          add_nonneg (mul_nonneg hL (mul_nonneg (by positivity) (hc S)))
            (mul_nonneg hA0 (mul_nonneg (by positivity) (hg S)))
    _ = log 3 / log A * totalInfluence F + A * ∑ S, (#(S \ J) : ℝ) * g S := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum,
          totalInfluence_eq_sum_card_mul_fourierCoeff_sq]
    _ ≤ log 3 / log A * totalInfluence F + A / 3 * √τ * totalInfluence F := by
        have := mul_le_mul_of_nonneg_left hlow hA0
        linarith [show A * (√τ / 3 * totalInfluence F) = A / 3 * √τ * totalInfluence F by ring]

/-! ### Friedgut's junta theorem -/

/-- If `totalInfluence F ≤ K` with `0 < K` and `0 < ε`, then at most
`4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates have influence above
`(3 ε / (2 K · 9 ^ (K / ε))) ^ 2`. -/
private theorem card_filter_lt_influence_le_of_totalInfluence_le (F : (ι → Bool) → ℝ)
    {K ε : ℝ} (hK0 : 0 < K) (hε : 0 < ε) (hK : totalInfluence F ≤ K) :
    let A : ℝ := 9 ^ (K / ε)
    let τ : ℝ := (3 * ε / (2 * K * A)) ^ 2
    (#({i : ι | τ < influence i F} : Finset ι) : ℝ) ≤
      4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε) := by
  intro A τ
  have hA0 : 0 < A := rpow_pos_of_pos (by norm_num) _
  have hτ : 0 < τ := sq_pos_of_pos (by positivity)
  have hcard : #{i : ι | τ < influence i F} * τ ≤ K :=
    calc #{i : ι | τ < influence i F} * τ = ∑ _i ∈ {i : ι | τ < influence i F}, τ := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ {i : ι | τ < influence i F}, influence i F :=
          sum_le_sum fun i hi => (mem_filter.1 hi).2.le
      _ ≤ totalInfluence F :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => influence_nonneg i F
      _ ≤ K := hK
  have hA2 : A * A = 81 ^ (K / ε) := by
    rw [← mul_rpow (by norm_num) (by norm_num)]
    norm_num
  refine ((le_div_iff₀ hτ).2 hcard).trans_eq ?_
  rw [← hA2, show τ = (3 * ε / (2 * K * A)) ^ 2 from rfl]
  field_simp
  ring

/-- When `totalInfluence (signVal ∘ f) ≤ 0`, `f` is within relative Hamming distance `ε > 0` of a
function depending on `∅`. -/
private theorem exists_empty_dependsOn_of_totalInfluence_le_zero (f : (ι → Bool) → Bool)
    {K ε : ℝ} (hε : 0 < ε) (hK : totalInfluence (fun x => signVal (f x)) ≤ K) (hK0 : 0 = K) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε) ∧ DependsOn g (J : Set ι) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f ∅
  refine ⟨∅, g, by rw [← hK0]; simp, hg, hfg.trans ?_⟩
  have h := sum_filter_not_subset_fourierCoeff_sq_le f (J := ∅) (τ := 1)
    (fun i _ => influence_signVal_le_one f i) (A := 3) (by norm_num)
  have hI0 : totalInfluence (fun x => signVal (f x)) = 0 :=
    le_antisymm (hK0 ▸ hK) (totalInfluence_nonneg _)
  rw [hI0, mul_zero, mul_zero, add_zero] at h
  exact h.trans hε.le

/-- **Friedgut's junta theorem**: if a Boolean function read as signs `F` has total influence at
most `K`, then for every `ε > 0` it is at relative Hamming distance at most `ε` from a Boolean
function of at most `4 K ^ 3 / (9 ε ^ 2) · 81 ^ (K / ε)` coordinates [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_dependsOn_hammingDist_div_le_of_totalInfluence_le (f : (ι → Bool) → Bool)
    {K ε : ℝ} (hε : 0 < ε) (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ (K / ε) ∧ DependsOn g (J : Set ι) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  rcases ((totalInfluence_nonneg F).trans hK).lt_or_eq with hK0 | hK0
  swap
  · exact exists_empty_dependsOn_of_totalInfluence_le_zero f hε hK hK0
  -- the parameters `A = 9 ^ (K / ε)` and `√τ = 3 ε / (2 K A)`
  set A : ℝ := 9 ^ (K / ε)
  have hA : 1 < A := one_lt_rpow (by norm_num) (div_pos hK0 hε)
  have hA0 : 0 < A := by linarith
  have hlogA : log 3 / log A = ε / (2 * K) := by
    rw [log_rpow (by norm_num), show (9 : ℝ) = 3 ^ 2 by norm_num, log_pow]
    have := (log_pos (by norm_num : (1 : ℝ) < 3)).ne'
    field_simp
    push_cast
    ring
  set s : ℝ := 3 * ε / (2 * K * A)
  have hs : 0 < s := by positivity
  set τ : ℝ := s ^ 2
  set J : Finset ι := {i | τ < influence i F}
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_hammingDist_div_le_sum_not_subset_fourierCoeff_sq f J
  refine ⟨J, g, card_filter_lt_influence_le_of_totalInfluence_le F hK0 hε hK, hg, hfg.trans ?_⟩
  -- both terms of the weight bound are at most `ε / 2`
  have h := sum_filter_not_subset_fourierCoeff_sq_le f (J := J) (τ := τ)
    (fun i hi => not_lt.1 fun h => hi (mem_filter.2 ⟨mem_univ i, h⟩)) hA
  rw [hlogA, Real.sqrt_sq hs.le] at h
  refine h.trans ?_
  have e : A / 3 * s = ε / (2 * K) := by
    rw [show s = 3 * ε / (2 * K * A) from rfl]
    field_simp
  rw [e]
  have h1 : ε / (2 * K) * totalInfluence F ≤ ε / (2 * K) * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  have h2 : ε / (2 * K) * K = ε / 2 := by
    field_simp
  linarith

/-- **Friedgut's junta theorem, exponential form**: if a Boolean function read as signs `F` has
total influence at most `K`, then for every `0 < ε ≤ 1` it is at relative Hamming distance at most
`ε` from a Boolean function of at most `3 · 2 ^ (8 K / ε)` coordinates [Friedgut1998]
[O'Donnell, Section 9.6][ODonnell2014]. -/
theorem exists_card_le_three_mul_two_rpow_dependsOn_hammingDist_div_le (f : (ι → Bool) → Bool)
    {K ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : totalInfluence (fun x => signVal (f x)) ≤ K) :
    ∃ (J : Finset ι) (g : (ι → Bool) → Bool),
      (#J : ℝ) ≤ 3 * 2 ^ (8 * K / ε) ∧ DependsOn g (J : Set ι) ∧
        (hammingDist f g : ℝ) / 2 ^ Fintype.card ι ≤ ε := by
  obtain ⟨J, g, hJ, hg, hfg⟩ := exists_dependsOn_hammingDist_div_le_of_totalInfluence_le f hε hK
  refine ⟨J, g, hJ.trans ?_, hg, hfg⟩
  have hK0 : 0 ≤ K := (totalInfluence_nonneg _).trans hK
  set x := K / ε
  have hx : 0 ≤ x := div_nonneg hK0 hε.le
  -- `K ^ 3 / ε ^ 2 = x ^ 3 ε ≤ x ^ 3 ≤ 6 eˣ`
  have h1 : K ^ 3 / ε ^ 2 ≤ 6 * exp x := by
    have e : K ^ 3 / ε ^ 2 = x ^ 3 * ε := by
      rw [show x = K / ε from rfl]
      field_simp
    have h := Real.pow_div_factorial_le_exp x hx 3
    rw [show ((3 : ℕ).factorial : ℝ) = 6 by norm_num [Nat.factorial]] at h
    rw [e]
    nlinarith [mul_le_of_le_one_right (pow_nonneg hx 3) hε1]
  -- `eˣ 81 ^ x = (81 e) ^ x ≤ 256 ^ x = 2 ^ (8 x)`
  have h2 : exp x * 81 ^ x ≤ 2 ^ (8 * K / ε) := by
    rw [← exp_one_rpow, ← mul_rpow (exp_pos 1).le (by norm_num), mul_div_assoc,
      rpow_mul (by norm_num)]
    exact rpow_le_rpow (by positivity) (by norm_num; linarith [exp_one_lt_d9]) hx
  have h81 : (0 : ℝ) ≤ 81 ^ x := by positivity
  calc 4 * K ^ 3 / (9 * ε ^ 2) * 81 ^ x = 4 / 9 * (K ^ 3 / ε ^ 2) * 81 ^ x := by ring
    _ ≤ 4 / 9 * (6 * exp x) * 81 ^ x := by gcongr
    _ = 8 / 3 * (exp x * 81 ^ x) := by ring
    _ ≤ 3 * 2 ^ (8 * K / ε) := by nlinarith [exp_pos x]

end Cslib.BitString
