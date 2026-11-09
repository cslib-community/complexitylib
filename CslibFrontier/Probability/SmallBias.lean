/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Probability.Collision
public import Mathlib.Data.Matrix.Mul
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Expect

/-!
# Small-bias distributions and the XOR lemma

The *bias* of a distribution `X` on the cube `ι → Bool` at a set `S` of coordinates is the
expectation of the character `χ_S` under `X` (`Cslib.BitString.bias`), which is
`Pr[⊕_{i ∈ S} xᵢ = 0] - Pr[⊕_{i ∈ S} xᵢ = 1]` (`Cslib.BitString.bias_eq_one_sub_two_mul`).
The uniform distribution has bias zero at every nonempty set. A distribution is *`ε`-biased*
(`Cslib.BitString.IsSmallBias`) if its bias at every nonempty set is at most `ε` in absolute value
[Naor and Naor][NaorNaor1993], and *`k`-wise `ε`-biased* (`Cslib.BitString.IsKWiseSmallBias`) if
this holds for the nonempty sets of at most `k` coordinates
[Alon, Goldreich, Håstad and Peralta][AlonGoldreichHastadPeralta1992].

The bias at `S` is `2 ^ n` times the Fourier coefficient of the mass function of `X` at `S`, so
Parseval's identity gives `∑_S bias X S ^ 2 = 2 ^ n cp(X)` for the collision probability `cp`
(`Cslib.BitString.sum_bias_sq`). Combined with the collision bound on the distance to uniform,
this is **Vazirani's XOR lemma** [Vazirani][Vazirani1986]
(`Cslib.BitString.four_mul_dist_uniform_sq_le_sum_bias_sq`): the statistical distance of `X` from
uniform is at most half the root of the sum of the squared biases at the nonempty sets. An
`ε`-biased distribution on `n` bits is therefore within `√(2 ^ n - 1) ε / 2` of uniform
(`Cslib.BitString.IsSmallBias.dist_uniform_le`). The marginal of `X` on a set `T` of coordinates
has the biases of `X` at the subsets of `T` (`Cslib.BitString.bias_map_restrict`), so a `k`-wise
`ε`-biased distribution is *almost `k`-wise independent*: its marginal on any `k` coordinates is
within `√(2 ^ k - 1) ε / 2` of uniform (`Cslib.BitString.IsKWiseSmallBias.dist_map_restrict_le`).

Reading a distribution through `n` parities `y_j = c_j ⬝ᵥ x` of its bits turns the bias at a set
`T` of outputs into the bias at the support of `∑_{j ∈ T} c_j`
(`Cslib.BitString.bias_map_dotProduct`). If the vectors `c_j` are `k`-wise linearly independent,
an `ε`-biased distribution is read as a `k`-wise `ε`-biased one
(`Cslib.BitString.IsSmallBias.isKWiseSmallBias_map_dotProduct`), the linear composition of
[Naor and Naor][NaorNaor1993].

## Main definitions

* `Cslib.BitString.bias`: the bias of a distribution on the cube at a set of coordinates.
* `Cslib.BitString.IsSmallBias`: `ε`-biased distributions.
* `Cslib.BitString.IsKWiseSmallBias`: `k`-wise `ε`-biased distributions.

## Main results

* `Cslib.BitString.bias_eq_one_sub_two_mul`: the bias in terms of the probability of odd parity.
* `Cslib.BitString.bias_uniformOfFintype`: the uniform distribution is unbiased.
* `Cslib.BitString.sum_bias_sq`: Parseval's identity for the biases.
* `Cslib.BitString.four_mul_dist_uniform_sq_le_sum_bias_sq`,
  `Cslib.BitString.dist_uniform_le_sqrt_sum_bias_sq`: Vazirani's XOR lemma.
* `Cslib.BitString.IsSmallBias.dist_uniform_le`: `ε`-biased distributions are close to uniform.
* `Cslib.BitString.IsKWiseSmallBias.dist_map_restrict_le`: `k`-wise `ε`-biased distributions are
  almost `k`-wise independent.
* `Cslib.BitString.IsSmallBias.isKWiseSmallBias_map_dotProduct`: `k`-wise independent parities
  of an `ε`-biased distribution are `k`-wise `ε`-biased.

## References

* [J. Naor, M. Naor, *Small-bias probability spaces: efficient constructions and
  applications*][NaorNaor1993]
* [N. Alon, O. Goldreich, J. Håstad, R. Peralta, *Simple constructions of almost `k`-wise
  independent random variables*][AlonGoldreichHastadPeralta1992]
* [U. V. Vazirani, *Randomness, adversaries and computation*][Vazirani1986]
-/

@[expose] public section

namespace Cslib.BitString

open Finset Probability Cslib.Probability.PMF
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bias of a distribution `X` on the cube at a set `S` of coordinates: the expectation of the
character `χ_S` under `X`, which is `Pr[⊕_{i ∈ S} xᵢ = 0] - Pr[⊕_{i ∈ S} xᵢ = 1]`
(`bias_eq_one_sub_two_mul`). -/
def bias (X : PMF (ι → Bool)) (S : Finset ι) : ℝ :=
  ∑ x, (X x).toReal * chi ℝ S x

/-- Every distribution has bias one at the empty set. -/
@[simp]
theorem bias_empty (X : PMF (ι → Bool)) : bias X ∅ = 1 := by
  simp [bias, sum_toReal]

/-- The bias is the probability of even parity minus the probability of odd parity on `S`. -/
theorem bias_eq_one_sub_two_mul (X : PMF (ι → Bool)) (S : Finset ι) :
    bias X S = 1 - 2 * (X.toOuterMeasure {x | parityOn S x = true}).toReal := by
  have h (x : ι → Bool) : chi ℝ S x = 1 + (-2) * (if parityOn S x = true then 1 else 0) := by
    rw [chi_eq_signVal_parityOn]
    cases parityOn S x <;> norm_num
  rw [bias, sum_congr rfl fun x _ => congrArg _ (h x), sum_affine, toOuterMeasure_apply_toReal]
  simp only [Set.mem_ofPred_eq, mul_ite, mul_one, mul_zero, neg_mul, ← sub_eq_add_neg]
  congr!

/-- A bias lies in `[-1, 1]`. -/
theorem abs_bias_le_one (X : PMF (ι → Bool)) (S : Finset ι) : |bias X S| ≤ 1 := by
  rw [bias, ← sum_toReal X]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
  rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg, chi_eq_signVal_parityOn]
  cases parityOn S x <;> simp

/-- A point mass has the bias of its point: the value of the character there. -/
@[simp]
theorem bias_pure (x : ι → Bool) (S : Finset ι) : bias (PMF.pure x) S = chi ℝ S x := by
  rw [bias, sum_eq_single x (fun y _ hy => by simp [PMF.pure_apply, hy]) (by simp)]
  simp

/-- The bias of the image of a distribution is the expectation of the character of the image. -/
theorem bias_map {α : Type*} [Fintype α] (X : PMF α) (g : α → ι → Bool) (S : Finset ι) :
    bias (X.map g) S = ∑ a, (X a).toReal * chi ℝ S (g a) :=
  sum_map_mul X g (chi ℝ S)

/-- The bias of a sample space `g`, with a uniformly random seed, is the average of the character
over the seeds. -/
theorem bias_uniformOfFintype_map {σ : Type*} [Fintype σ] [Nonempty σ] (g : σ → ι → Bool)
    (S : Finset ι) : bias ((PMF.uniformOfFintype σ).map g) S = 𝔼 s, chi ℝ S (g s) := by
  rw [bias_map, Fintype.expect_eq_sum_div_card, sum_div]
  simp [div_eq_inv_mul]

/-- The uniform distribution has bias zero at every nonempty set. -/
theorem bias_uniformOfFintype (S : Finset ι) :
    bias (PMF.uniformOfFintype (ι → Bool)) S = if S = ∅ then 1 else 0 := by
  rw [← PMF.map_id (PMF.uniformOfFintype (ι → Bool)), bias_uniformOfFintype_map]
  exact expect_chi S

/-- **Parseval's identity for the biases**: the squared biases of `X` sum to `2 ^ n` times its
collision probability. -/
theorem sum_bias_sq (X : PMF (ι → Bool)) :
    ∑ S, bias X S ^ 2 = 2 ^ Fintype.card ι * collisionProbability X := by
  have h (S : Finset ι) : bias X S ^ 2 =
      ∑ x, ∑ y, (X x).toReal * (X y).toReal * (chi ℝ S x * chi ℝ S y) := by
    rw [bias, sq, sum_mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  calc ∑ S, bias X S ^ 2
      = ∑ x, ∑ y, (X x).toReal * (X y).toReal * ∑ S, chi ℝ S x * chi ℝ S y := by
        simp only [h, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_comm
    _ = 2 ^ Fintype.card ι * collisionProbability X := by
        simp only [sum_chi_mul_chi, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true,
          collisionProbability_eq_sum, mul_sum]
        exact sum_congr rfl fun x _ => by ring

/-- **Vazirani's XOR lemma**, squared form: four times the squared statistical distance of `X`
from uniform is at most the sum of the squared biases of `X` at the nonempty sets. -/
theorem four_mul_dist_uniform_sq_le_sum_bias_sq (X : PMF (ι → Bool)) :
    4 * dist X (PMF.uniformOfFintype (ι → Bool)) ^ 2 ≤ ∑ S with S.Nonempty, bias X S ^ 2 := by
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Finset ι)) (·.Nonempty)
    (fun S => bias X S ^ 2)
  have hempty : ∑ S with ¬S.Nonempty, bias X S ^ 2 = 1 := by
    rw [sum_eq_single_of_mem ∅ (by simp)]
    · simp
    · intro S hS hne
      simp_all [not_nonempty_iff_eq_empty]
  have hcard : (Fintype.card (ι → Bool) : ℝ) = 2 ^ Fintype.card ι := by simp
  have h := dist_uniform_sq_le X
  rw [hcard, ← sum_bias_sq, ← hsplit, hempty] at h
  linarith

/-- **Vazirani's XOR lemma**: the statistical distance of `X` from uniform is at most half the
square root of the sum of the squared biases of `X` at the nonempty sets. -/
theorem dist_uniform_le_sqrt_sum_bias_sq (X : PMF (ι → Bool)) :
    dist X (PMF.uniformOfFintype (ι → Bool)) ≤
      Real.sqrt (∑ S with S.Nonempty, bias X S ^ 2) / 2 := by
  rw [le_div_iff₀ two_pos]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [four_mul_dist_uniform_sq_le_sum_bias_sq X]

/-- A distribution `X` on the cube is *`ε`-biased* if its bias at every nonempty set of
coordinates is at most `ε` in absolute value [Naor and Naor][NaorNaor1993]. -/
def IsSmallBias (ε : ℝ) (X : PMF (ι → Bool)) : Prop :=
  ∀ S : Finset ι, S.Nonempty → |bias X S| ≤ ε

/-- A distribution `X` on the cube is *`k`-wise `ε`-biased* if its bias at every nonempty set of at
most `k` coordinates is at most `ε` in absolute value
[Alon, Goldreich, Håstad and Peralta][AlonGoldreichHastadPeralta1992]. -/
def IsKWiseSmallBias (k : ℕ) (ε : ℝ) (X : PMF (ι → Bool)) : Prop :=
  ∀ S : Finset ι, S.Nonempty → #S ≤ k → |bias X S| ≤ ε

/-- The uniform distribution is `0`-biased. -/
theorem isSmallBias_uniformOfFintype : IsSmallBias (ι := ι) 0 (PMF.uniformOfFintype _) :=
  fun S hS => by simp [bias_uniformOfFintype, hS.ne_empty]

/-- Every distribution is `1`-biased. -/
theorem isSmallBias_one (X : PMF (ι → Bool)) : IsSmallBias 1 X :=
  fun S _ => abs_bias_le_one X S

namespace IsSmallBias

variable {ε δ : ℝ} {X : PMF (ι → Bool)}

/-- An `ε`-biased distribution is `δ`-biased for every `δ ≥ ε`. -/
theorem mono (hX : IsSmallBias ε X) (h : ε ≤ δ) : IsSmallBias δ X :=
  fun S hS => (hX S hS).trans h

/-- An `ε`-biased distribution is `k`-wise `ε`-biased for every `k`. -/
theorem isKWiseSmallBias (hX : IsSmallBias ε X) (k : ℕ) : IsKWiseSmallBias k ε X :=
  fun S hS _ => hX S hS

/-- **Small bias implies closeness to uniform**: an `ε`-biased distribution on `n` bits is within
statistical distance `√(2 ^ n - 1) ε / 2` of uniform. -/
theorem dist_uniform_le (hX : IsSmallBias ε X) :
    dist X (PMF.uniformOfFintype (ι → Bool)) ≤
      Real.sqrt (2 ^ Fintype.card ι - 1) * ε / 2 := by
  refine (dist_uniform_le_sqrt_sum_bias_sq X).trans ?_
  have hcount : (#({S : Finset ι | S.Nonempty} : Finset (Finset ι)) : ℝ) =
      2 ^ Fintype.card ι - 1 := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Finset ι))) (·.Nonempty)
    have hne : #({S : Finset ι | ¬S.Nonempty} : Finset (Finset ι)) = 1 := by
      rw [card_eq_one]
      exact ⟨∅, by ext S; simp [not_nonempty_iff_eq_empty]⟩
    rw [hne, card_univ, Fintype.card_finset] at h
    rw [eq_sub_iff_add_eq]
    exact_mod_cast h
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : ({S : Finset ι | S.Nonempty} : Finset (Finset ι)) = ∅ := by
      ext S
      simp [Finset.eq_empty_of_isEmpty S]
    rw [this, sum_empty, Real.sqrt_zero, Fintype.card_eq_zero]
    simp
  · obtain ⟨i⟩ := hι
    have hε : 0 ≤ ε := (abs_nonneg _).trans (hX {i} (singleton_nonempty i))
    gcongr
    calc Real.sqrt (∑ S with S.Nonempty, bias X S ^ 2)
        ≤ Real.sqrt (∑ S : Finset ι with S.Nonempty, ε ^ 2) := by
          refine Real.sqrt_le_sqrt (sum_le_sum fun S hS => ?_)
          exact sq_le_sq' (abs_le.1 (hX S (mem_filter.1 hS).2)).1
            (abs_le.1 (hX S (mem_filter.1 hS).2)).2
      _ = Real.sqrt (2 ^ Fintype.card ι - 1) * ε := by
          rw [sum_const, nsmul_eq_mul, hcount, Real.sqrt_mul' _ (sq_nonneg ε),
            Real.sqrt_sq hε]

end IsSmallBias

/-- A distribution is `n`-wise `ε`-biased on `n` bits exactly when it is `ε`-biased. -/
theorem isKWiseSmallBias_card_iff {ε : ℝ} {X : PMF (ι → Bool)} :
    IsKWiseSmallBias (Fintype.card ι) ε X ↔ IsSmallBias ε X :=
  ⟨fun hX S hS => hX S hS (card_le_univ S), fun hX => hX.isKWiseSmallBias _⟩

section Marginal

omit [Fintype ι] [DecidableEq ι] in
/-- The character of a set `S` of coordinates in `T` at the restriction of `x` to `T` is the
character of `S`, as a set of coordinates of `x`. -/
theorem chi_restrict (T : Finset ι) (S : Finset T) (x : ι → Bool) :
    chi ℝ S (T.restrict x) = chi ℝ (S.map (Function.Embedding.subtype (· ∈ T))) x := by
  simp [chi, prod_map]

/-- The marginal of `X` on a set `T` of coordinates has the biases of `X` at the subsets of `T`. -/
theorem bias_map_restrict (X : PMF (ι → Bool)) (T : Finset ι) (S : Finset T) :
    bias (X.map T.restrict) S = bias X (S.map (Function.Embedding.subtype (· ∈ T))) := by
  rw [bias_map]
  simp only [chi_restrict, bias]

namespace IsKWiseSmallBias

variable {k : ℕ} {ε : ℝ} {X : PMF (ι → Bool)}

/-- A `k`-wise `ε`-biased distribution is `k'`-wise `ε`-biased for every `k' ≤ k`. -/
theorem mono (hX : IsKWiseSmallBias k ε X) {k' : ℕ} (hk : k' ≤ k) : IsKWiseSmallBias k' ε X :=
  fun S hS hSk => hX S hS (hSk.trans hk)

/-- The marginal of a `k`-wise `ε`-biased distribution on a set of at most `k` coordinates is
`ε`-biased. -/
theorem isSmallBias_map_restrict (hX : IsKWiseSmallBias k ε X) {T : Finset ι} (hT : #T ≤ k) :
    IsSmallBias ε (X.map T.restrict) := fun S hS => by
  rw [bias_map_restrict]
  refine hX _ (hS.map) ?_
  rw [card_map]
  exact (card_le_univ S).trans (by simpa using hT)

/-- **Almost `k`-wise independence**: the marginal of a `k`-wise `ε`-biased distribution on a set
`T` of at most `k` coordinates is within statistical distance `√(2 ^ #T - 1) ε / 2` of uniform
[Alon, Goldreich, Håstad and Peralta][AlonGoldreichHastadPeralta1992]. -/
theorem dist_map_restrict_le (hX : IsKWiseSmallBias k ε X) {T : Finset ι} (hT : #T ≤ k) :
    dist (X.map T.restrict) (PMF.uniformOfFintype (T → Bool)) ≤
      Real.sqrt (2 ^ #T - 1) * ε / 2 := by
  simpa using (hX.isSmallBias_map_restrict hT).dist_uniform_le

end IsKWiseSmallBias

end Marginal

section Linear

omit [DecidableEq ι] in
/-- The real sign of the inner product of bit strings `u ⬝ᵥ x` is the character, at `x`, of the
set of coordinates where `u` is `true`. -/
theorem signVal_dotProduct (u x : ι → Bool) : signVal (u ⬝ᵥ x) = chi ℝ {i | u i} x := by
  rw [chi_eq_signVal_parityOn, parityOn_eq_sum, dotProduct, sum_filter]
  congr 1
  exact sum_congr rfl fun i _ => by cases u i <;> rfl

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Reading `X` through the parities `y_j = c j ⬝ᵥ x` turns the bias at a set `T` of outputs into
the bias of `X` at the coordinates where `∑_{j ∈ T} c j` is `true`. -/
theorem bias_map_dotProduct (X : PMF (ι → Bool)) (c : κ → ι → Bool) (T : Finset κ) :
    bias (X.map fun x j => c j ⬝ᵥ x) T = bias X {i | (∑ j ∈ T, c j) i} := by
  rw [bias_map]
  refine sum_congr rfl fun x _ => ?_
  rw [chi_eq_signVal_parityOn, parityOn_eq_sum, ← sum_dotProduct, signVal_dotProduct]

/-- **Linear composition** [Naor and Naor][NaorNaor1993]: if every nonempty set of at most `k` of
the vectors `c j` has a nonzero sum, then the parities `c j ⬝ᵥ x` of an `ε`-biased distribution are
`k`-wise `ε`-biased. -/
theorem IsSmallBias.isKWiseSmallBias_map_dotProduct {ε : ℝ} {X : PMF (ι → Bool)}
    (hX : IsSmallBias ε X) {k : ℕ} {c : κ → ι → Bool}
    (hc : ∀ T : Finset κ, T.Nonempty → #T ≤ k → ∑ j ∈ T, c j ≠ 0) :
    IsKWiseSmallBias k ε (X.map fun x j => c j ⬝ᵥ x) := fun T hT hTk => by
  rw [bias_map_dotProduct]
  refine hX _ ?_
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hc T hT hTk)
  refine ⟨i, mem_filter.2 ⟨mem_univ i, ?_⟩⟩
  revert hi
  cases (∑ j ∈ T, c j) i <;> simp

end Linear

end Cslib.BitString
