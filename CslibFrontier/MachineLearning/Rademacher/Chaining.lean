/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.Rademacher.Classification
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Code.HammingBound
import CslibFrontier.MachineLearning.PACLearning.Packing
import CslibFrontier.Probability.BitString.Chaining
import CslibFrontier.Probability.PMF.ToReal

/-!
# Rademacher complexity of VC classes by chaining

Massart's lemma bounds the empirical Rademacher complexity of a binary class `C` on `m` points by
`√(2 log Π_C(m) / m)`, which is `√(2 d log (e m / d) / m)` when every set shattered by `C` has at
most `d` points (`empiricalRademacherComplexity_signClass_le_vc`). Chaining removes the logarithm.
On a sample, the sign patterns `signVal ∘ u` of the labelings `u` realized by `C` satisfy
`‖signVal ∘ u - signVal ∘ v‖² = 4 · hammingDist u v`. A maximal separated set of labelings at
Hamming scale `m / 4 ^ (n + 1)` is a Euclidean net of the sign patterns at scale `√m / 2 ^ n`, and
by the packing bound (`card_le_div_pow_of_le_hammingDist`) it has at most `2 ^ (2 d (2 n + 5))`
points. Dudley's chaining bound (`Cslib.BitString.expect_ciSup_sum_mul_signVal_le_chaining`) with
these nets, and `T 0 = {0}`, gives the complexity bound `32 √(d / m)`. The argument uses only that
the vectors depend on realized labelings with squared distances at most a multiple of the Hamming
distance, so `expect_ciSup_sum_mul_signVal_le_of_hammingDist` states it in that generality; other
vectors, such as the loss differences on a double sample, have the same nets.

The constant `32` is far from optimal: for realistic sample sizes the logarithmic bound is smaller.
The point is the rate, which is what the sharp agnostic sample complexity
`O((d + log (1 / δ)) / ε²)` of [ShalevShwartzBenDavid2014, Theorem 6.8] needs.

## Main results

* `Cslib.MachineLearning.expect_ciSup_sum_mul_signVal_le_of_hammingDist`: let the vectors come
  from labelings realized by a class whose shattered sets have at most `d` points, with squared
  distances at most a fixed multiple of the Hamming distances of their labelings. Then their
  expected maximal correlation with random signs is at most `32 r √d`, where `r` bounds their norms.
* `Cslib.MachineLearning.empiricalRademacherComplexity_signClass_le_mul_sqrt`: the empirical
  Rademacher complexity of a class whose shattered sets have at most `d` points is at most
  `32 √(d / m)`.
* `Cslib.MachineLearning.rademacherComplexity_signClass_le_mul_sqrt`: the same bound for the
  Rademacher complexity on a finite domain.
* `Cslib.MachineLearning.PACLearning.IsERM.vc_agnostic_bound_mul_sqrt`: on a finite domain, an
  empirical risk minimizer is within `32 √(d / m) + √(2 log (2 / δ) / m)` of the best concept of
  `C` with probability at least `1 - δ`.

## References

* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Lemma 27.4 and Theorem 6.8
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Sections 8.1 and 8.3
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- The squared Euclidean distance between the sign patterns of two words is four times their
Hamming distance. -/
private theorem sum_sq_signVal_sub_signVal {m : ℕ} (u v : Fin m → Bool) :
    ∑ i, (signVal (u i) - signVal (v i)) ^ 2 = 4 * hammingDist u v := by
  classical
  have h (i : Fin m) : (signVal (u i) - signVal (v i)) ^ 2 = 4 * if u i ≠ v i then 1 else 0 := by
    cases u i <;> cases v i <;> norm_num
  rw [Finset.sum_congr rfl fun i _ => h i, ← mul_sum, sum_boole, hammingDist]

/-- `∑_{n < K} (n + 7) / 2 ^ n ≤ 16`. -/
private theorem sum_range_add_seven_div_two_pow_le (K : ℕ) :
    ∑ n ∈ range K, ((n : ℝ) + 7) / 2 ^ n ≤ 16 := by
  have h : ∀ K : ℕ, ∑ n ∈ range K, ((n : ℝ) + 7) / 2 ^ n = 16 - (2 * K + 16) / 2 ^ K := by
    intro K
    induction K with
    | zero => norm_num
    | succ K ih =>
      rw [sum_range_succ, ih, pow_succ]
      push_cast
      field_simp
      ring
  rw [h]
  have : (0 : ℝ) ≤ (2 * K + 16) / 2 ^ K := by positivity
  linarith

/-- **Chaining over the labelings of a VC class**, derived from the chaining bound
[ShalevShwartzBenDavid2014, Lemma 27.4] as in [Vershynin2018, Section 8.3]: let every finite set
shattered by `C` have at most `d` points, and let
`a j : κ → ℝ`, `j : ι`, be vectors of Euclidean norm at most `r` that depend on `j` only through a
labeling `ℓ j` realized by `C` on `n` points `x`, with
`‖a j - a j'‖² ≤ (4 r² / n) · hammingDist (ℓ j) (ℓ j')`. Then the expected maximum of their
correlations with a uniformly random sign vector is at most `32 r √d`.

The nets are images of maximal Hamming-separated sets of labelings at scales `n / 4 ^ (k + 1)`,
bounded by the packing bound `card_le_div_pow_of_le_hammingDist`; the truncation level of
`Cslib.BitString.expect_ciSup_sum_mul_signVal_le_chaining` is then sent to infinity. -/
theorem expect_ciSup_sum_mul_signVal_le_of_hammingDist {ι κ : Type*} [Fintype κ]
    [DecidableEq κ] {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {n : ℕ} (x : Fin n → α)
    (ℓ : ι → Fin n → Bool) (hℓ : ∀ j, ℓ j ∈ restriction C x) (a : ι → κ → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ r ^ 2)
    (hdist : ∀ j j', ∑ i, (a j i - a j' i) ^ 2 ≤ 4 * r ^ 2 / n * hammingDist (ℓ j) (ℓ j')) :
    𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i) ≤ 32 * r * √d := by
  classical
  -- The labelings realized by the family, and a vector of the family for each of them.
  set V : Finset (Fin n → Bool) := (Set.toFinite (Set.range ℓ)).toFinset with hV
  have hmemV (j : ι) : ℓ j ∈ V := (Set.Finite.mem_toFinset _).2 ⟨j, rfl⟩
  have hVex (v : Fin n → Bool) (hv : v ∈ V) : ∃ j, ℓ j = v := (Set.Finite.mem_toFinset _).1 hv
  set rep : (Fin n → Bool) → κ → ℝ := fun v => if h : ∃ j, ℓ j = v then a h.choose else 0
    with hrep
  -- Hamming nets of the realized labelings at scales `n / 4 ^ (k + 1)`.
  choose N hNV hNsep hNcov using fun k : ℕ =>
    Cslib.Code.exists_subset_pairwise_lt_hammingDist_forall_exists_le V (n / 4 ^ (k + 1))
  set T : ℕ → Finset (κ → ℝ) := fun k => if k = 0 then {0} else (N k).image rep with hT
  have hnet : ∀ k j, ∃ u ∈ T k, ∑ i, (a j i - u i) ^ 2 ≤ (r / 2 ^ k) ^ 2 := by
    intro k j
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨0, by simp [hT], by simpa using ha j⟩
    obtain ⟨v, hv, hd⟩ := hNcov k (ℓ j) (hmemV j)
    have hex : ∃ j', ℓ j' = v := hVex v (hNV k hv)
    refine ⟨rep v, by simp only [hT, hk.ne', ↓reduceIte]; exact mem_image_of_mem _ hv, ?_⟩
    simp only [hrep, hex, ↓reduceDIte]
    refine (hdist j hex.choose).trans ?_
    rw [hex.choose_spec, hammingDist_comm]
    have h4 : (4 * hammingDist v (ℓ j) * 4 ^ k : ℝ) ≤ n := by
      have : 4 * hammingDist v (ℓ j) * 4 ^ k ≤ n :=
        calc 4 * hammingDist v (ℓ j) * 4 ^ k = hammingDist v (ℓ j) * 4 ^ (k + 1) := by ring
          _ ≤ n / 4 ^ (k + 1) * 4 ^ (k + 1) := Nat.mul_le_mul_right _ hd
          _ ≤ n := Nat.div_mul_le_self n _
      exact_mod_cast this
    have hpow : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, hpow]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp only [hn, CharP.cast_eq_zero, div_zero, zero_mul]
      positivity
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hn' (by positivity)]
    calc 4 * r ^ 2 * hammingDist v (ℓ j) * 4 ^ k = r ^ 2 * (4 * hammingDist v (ℓ j) * 4 ^ k) := by
          ring
      _ ≤ r ^ 2 * n := mul_le_mul_of_nonneg_left h4 (sq_nonneg r)
  -- The sizes of the nets.
  have hlogT : ∀ k, Real.log (T k).card ≤ 2 * d * (2 * k + 5) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [hT, ↓reduceIte, card_singleton, Nat.cast_one, Real.log_one]
      positivity
    have hcard : ((T k).card : ℝ) ≤ (2 : ℝ) ^ (2 * d * (2 * k + 5)) := by
      have hsep : ∀ u ∈ N k, ∀ v ∈ N k, u ≠ v → (1 / 4 ^ (k + 1) : ℝ) * n ≤ hammingDist u v := by
        intro u hu v hv huv
        have hlt : n / 4 ^ (k + 1) + 1 ≤ hammingDist u v := hNsep k hu hv huv
        have h1 : n < (n / 4 ^ (k + 1) + 1) * 4 ^ (k + 1) := by
          rw [add_mul, one_mul]
          exact Nat.lt_div_mul_add (by positivity)
        have h2 : n ≤ hammingDist u v * 4 ^ (k + 1) :=
          (h1.trans_le (Nat.mul_le_mul_right _ hlt)).le
        rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        exact_mod_cast h2
      have hNC : ∀ u ∈ N k, u ∈ restriction C x := fun u hu => by
        obtain ⟨j, rfl⟩ := hVex u (hNV k hu)
        exact hℓ j
      have hP := card_le_div_pow_of_le_hammingDist hC hNC (by positivity)
        (div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity)) hsep
      calc ((T k).card : ℝ) ≤ (N k).card := by
            simp only [hT, hk.ne', ↓reduceIte]
            exact_mod_cast card_image_le
        _ ≤ (8 / (1 / 4 ^ (k + 1))) ^ (2 * d) := hP
        _ = (2 : ℝ) ^ (2 * d * (2 * k + 5)) := by
            rw [div_div_eq_mul_div, div_one, show (8 : ℝ) * 4 ^ (k + 1) = 2 ^ (2 * k + 5) by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]; ring, ← pow_mul]
            ring_nf
    rcases Nat.eq_zero_or_pos (T k).card with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; positivity
    calc Real.log (T k).card ≤ Real.log ((2 : ℝ) ^ (2 * d * (2 * k + 5))) :=
          Real.log_le_log (by exact_mod_cast hpos) hcard
      _ = (2 * d * (2 * k + 5) : ℕ) * Real.log 2 := Real.log_pow _ _
      _ ≤ (2 * d * (2 * k + 5) : ℕ) * 1 := by
          gcongr
          exact (Real.log_le_sub_one_of_pos two_pos).trans (by norm_num)
      _ = 2 * d * (2 * k + 5) := by push_cast; ring
  have hlog2 (k : ℕ) : Real.log ((T (k + 1)).card * (T k).card) ≤ 8 * d * (k + 3) := by
    rcases Nat.eq_zero_or_pos (T (k + 1)).card with h0 | h1
    · rw [h0, Nat.cast_zero, zero_mul, Real.log_zero]; positivity
    rcases Nat.eq_zero_or_pos (T k).card with h0 | h2
    · rw [h0, Nat.cast_zero, mul_zero, Real.log_zero]; positivity
    rw [Real.log_mul (by exact_mod_cast h1.ne') (by exact_mod_cast h2.ne')]
    have := hlogT (k + 1)
    have := hlogT k
    push_cast at *
    nlinarith
  -- Dudley's chaining bound, for every truncation level `K`.
  have hK (K : ℕ) : 𝔼 σ : κ → Bool, ⨆ j, ∑ i, a j i * signVal (σ i) ≤
      32 * r * √d + r * √(Fintype.card κ) * (1 / 2) ^ K := by
    have hch := expect_ciSup_sum_mul_signVal_le_chaining a hr ha T hnet K
    have hT0 : Real.log (T 0).card = 0 := by simp [hT]
    have hterm (k : ℕ) : 2 * r / 2 ^ k * √(2 * Real.log ((T (k + 1)).card * (T k).card)) ≤
        2 * r * √d * (((k : ℝ) + 7) / 2 ^ k) := by
      have hs : √(2 * Real.log ((T (k + 1)).card * (T k).card)) ≤ √d * (k + 7) := by
        calc √(2 * Real.log ((T (k + 1)).card * (T k).card)) ≤ √(d * (k + 7) ^ 2) := by
              refine Real.sqrt_le_sqrt ?_
              have := hlog2 k
              nlinarith [sq_nonneg ((k : ℝ) - 1), (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
          _ = √d * (k + 7) := by
              rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
      calc 2 * r / 2 ^ k * √(2 * Real.log ((T (k + 1)).card * (T k).card))
          ≤ 2 * r / 2 ^ k * (√d * (k + 7)) := by gcongr
        _ = 2 * r * √d * (((k : ℝ) + 7) / 2 ^ k) := by ring
    have hsum : ∑ k ∈ range K, 2 * r / 2 ^ k *
        √(2 * Real.log ((T (k + 1)).card * (T k).card)) ≤ 32 * r * √d := by
      calc _ ≤ ∑ k ∈ range K, 2 * r * √d * (((k : ℝ) + 7) / 2 ^ k) := sum_le_sum fun k _ => hterm k
        _ = 2 * r * √d * ∑ k ∈ range K, ((k : ℝ) + 7) / 2 ^ k := by rw [mul_sum]
        _ ≤ 2 * r * √d * 16 := by gcongr; exact sum_range_add_seven_div_two_pow_le K
        _ = 32 * r * √d := by ring
    rw [hT0, mul_zero, Real.sqrt_zero, mul_zero, zero_add] at hch
    have hres : r / 2 ^ K * √(Fintype.card κ) = r * √(Fintype.card κ) * (1 / 2) ^ K := by
      rw [one_div_pow]; ring
    linarith
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have hc : 0 < r * √(Fintype.card κ) + 1 := by positivity
  obtain ⟨K, hKε⟩ := exists_pow_lt_of_lt_one (div_pos hε hc) (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 : r * √(Fintype.card κ) * (1 / 2) ^ K < ε := by
    calc r * √(Fintype.card κ) * (1 / 2) ^ K ≤ (r * √(Fintype.card κ) + 1) * (1 / 2) ^ K := by
          gcongr; linarith
      _ < (r * √(Fintype.card κ) + 1) * (ε / (r * √(Fintype.card κ) + 1)) := by gcongr
      _ = ε := by field_simp
  linarith [hK K]

/-- **Chaining bound for VC classes**, derived from the chaining bound
[ShalevShwartzBenDavid2014, Lemma 27.4] as in [Vershynin2018, Section 8.3]: if every finite set
shattered by `C` has at most `d` points, the
empirical Rademacher complexity of `signClass C` on `m` points is at most `32 √(d / m)`. Unlike
`empiricalRademacherComplexity_signClass_le_vc`, the bound has no factor `log (m / d)`. -/
theorem empiricalRademacherComplexity_signClass_le_mul_sqrt {C : ConceptClass α Bool} {d : ℕ}
    (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) {m : ℕ} (S : Fin m → α) :
    empiricalRademacherComplexity (signClass C) S ≤ 32 * √(d / m) := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [empiricalRademacherComplexity_def, rademacherAverage_def]
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  -- The labelings realized on the sample, and their sign patterns.
  set V : Finset (Fin m → Bool) := (Set.toFinite (restriction C S)).toFinset with hV
  set sp : (Fin m → Bool) → Fin m → ℝ := fun u i => signVal (u i) with hsp
  have hsp_abs (u : Fin m → Bool) (i : Fin m) : |sp u i| ≤ 1 := (abs_signVal _).le
  -- Reduce to the Rademacher average of the finitely many sign patterns.
  have hred : empiricalRademacherComplexity (signClass C) S ≤
      rademacherAverage fun u : V => sp u := by
    rw [empiricalRademacherComplexity_def]
    refine rademacherAverage_le_of_forall_exists (fun u i => hsp_abs u i) fun f => ?_
    obtain ⟨c, hc, hcf⟩ := mem_signClass.1 f.2
    refine ⟨⟨fun i => c (S i), (Set.Finite.mem_toFinset _).2
      (mem_restriction.2 ⟨c, hc, fun _ => rfl⟩)⟩, ?_⟩
    funext i
    simp only [hsp, ← hcf]
  refine hred.trans ?_
  have hsq (u : Fin m → Bool) : ∑ i, sp u i ^ 2 = m := by
    simp [hsp, sq, signVal_mul_self]
  have h := expect_ciSup_sum_mul_signVal_le_of_hammingDist hC S (fun u : V => (u : Fin m → Bool))
    (fun u => (Set.Finite.mem_toFinset _).1 u.2) (fun u : V => sp u) (r := √m)
    (Real.sqrt_nonneg _) (fun u => by rw [hsq, Real.sq_sqrt hm'.le]) fun u v => by
      change ∑ i, (signVal ((u : Fin m → Bool) i) - signVal ((v : Fin m → Bool) i)) ^ 2 ≤ _
      rw [sum_sq_signVal_sub_signVal, Real.sq_sqrt hm'.le, mul_div_assoc, div_self hm'.ne',
        mul_one]
  rw [rademacherAverage_eq_expect_ciSup_sum_div, div_le_iff₀ hm']
  calc _ ≤ 32 * √m * √d := h
    _ = 32 * √(d / m) * m := by
        rw [Real.sqrt_div' _ hm'.le]
        field_simp
        rw [Real.sq_sqrt hm'.le]
        ring

/-- **Chaining bound for VC classes** for the Rademacher complexity on a finite domain. -/
theorem rademacherComplexity_signClass_le_mul_sqrt [Fintype α] (D : PMF α)
    {C : ConceptClass α Bool} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d) (m : ℕ) :
    rademacherComplexity D (signClass C) m ≤ 32 * √(d / m) :=
  rademacherComplexity_le D fun S => empiricalRademacherComplexity_signClass_le_mul_sqrt hC S

/-- **Agnostic VC bound without a logarithmic factor**: if every finite set shattered by `C` has
at most `d` points, then for `m > 0`, with probability at least `1 - δ` over `m` independent
examples from `D`, an empirical risk minimizer `A` for `C` satisfies
`err_D(A S) ≤ err_D(c) + 32 √(d / m) + √(2 log (2 / δ) / m)` for every `c ∈ C`. This is an excess
error of `O(√((d + log (1 / δ)) / m))`, the rate of [ShalevShwartzBenDavid2014, Theorem 6.8]. It
combines `PACLearning.IsERM.rademacherComplexity_agnostic_bound` with the chaining bound. The
domain is finite. -/
theorem PACLearning.IsERM.vc_agnostic_bound_mul_sqrt [Finite α] (D : PMF (α × Bool))
    {C : ConceptClass α Bool} {d : ℕ} (hC : ∀ W : Finset α, SetShatters C ↑W → W.card ≤ d)
    {m : ℕ} (hm : 0 < m) {A : Learner α Bool m} (hA : IsERM A C) {δ : ℝ} (hδ : 0 < δ) :
    ((Probability.PMF.pi fun _ : Fin m => D).toOuterMeasure
      {S | ∃ c ∈ C, (D.toOuterMeasure {p | c p.1 ≠ p.2}).toReal + 32 * √(d / m) +
        √(2 * Real.log (2 / δ) / m) < (D.toOuterMeasure {p | A S p.1 ≠ p.2}).toReal}).toReal ≤
      δ := by
  have := Fintype.ofFinite α
  refine le_trans (Probability.PMF.toOuterMeasure_toReal_mono _ ?_)
    (hA.rademacherComplexity_agnostic_bound D hm hδ)
  rintro S ⟨c, hc, hlt⟩
  refine ⟨c, hc, ?_⟩
  linarith [rademacherComplexity_signClass_le_mul_sqrt (D.map Prod.fst) hC m]

end Cslib.MachineLearning
