/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BitString.Sign
public import CslibFrontier.Probability.Product
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Probability.BitString.Massart
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Rademacher complexity

The *empirical Rademacher complexity* of a class `F` of real functions on a sample
`S = (z₁, …, z_m)` is the expected best correlation of `F` with random signs,
`R̂_S(F) = 𝔼_σ sup_{f ∈ F} (1 / m) ∑ i, σ_i f (z_i)`, where `σ_1, …, σ_m` are independent uniform
signs [MohriRostamizadehTalwalkar2018, Definition 3.1]. The *Rademacher complexity*
`R_m(F) = 𝔼_{S ∼ D^m} R̂_S(F)` averages it over `m` independent draws from a distribution `D`
[MohriRostamizadehTalwalkar2018, Definition 3.2]. It measures how well the class can fit random
noise on typical samples, and controls the gap between empirical and population means uniformly
over the class (`CslibFrontier.MachineLearning.Rademacher.Generalization`).

Signs are bits through `Cslib.BitString.signVal` and expectations are uniform averages `𝔼`.
`rademacherAverage` is the underlying quantity for an indexed family of vectors in `ℝᵐ`;
the empirical Rademacher complexity is the Rademacher average of the restrictions
`(f (S 0), …, f (S (m - 1)))` of the functions `f ∈ F`. The supremum is the real `⨆`, so the
results assume a class that is uniformly bounded on the sample; an unbounded supremum takes the
junk value `0`. For the population version the domain is a finite type with a probability mass
function, the setting of the finite McDiarmid inequality.

Massart's lemma (`Cslib.BitString.expect_ciSup_sum_mul_signVal_le`) bounds the Rademacher average
of `N` vectors of norm at most `r` by `r √(2 log N) / m` [MohriRostamizadehTalwalkar2018,
Theorem 3.7]. For a class bounded by `B`, the empirical complexity is therefore at most
`B √(2 log P / m)`, where `P` is the number of distinct restrictions of the class to the sample
[MohriRostamizadehTalwalkar2018, Corollary 3.8], and at most `B √(2 log |F| / m)` for a finite
class.

## Main definitions

* `Cslib.MachineLearning.rademacherAverage`: the Rademacher average of a family of vectors.
* `Cslib.MachineLearning.empiricalRademacherComplexity`: the empirical Rademacher complexity.
* `Cslib.MachineLearning.rademacherComplexity`: its expectation over `m` independent draws.

## Main results

* `Cslib.MachineLearning.rademacherAverage_def`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_def`,
  `Cslib.MachineLearning.rademacherComplexity_def`: the defining equations; the definitions are
  not exposed.
* `Cslib.MachineLearning.rademacherAverage_eq_expect_ciSup_sum_div`: the Rademacher average with
  the normalization `1 / m` outside the expectation.
* `Cslib.MachineLearning.rademacherAverage_le`,
  `Cslib.MachineLearning.rademacherAverage_le_mul_sqrt`: Massart's lemma in normalized form.
* `Cslib.MachineLearning.rademacherAverage_nonneg`,
  `Cslib.MachineLearning.rademacherAverage_unique`,
  `Cslib.MachineLearning.rademacherAverage_of_isEmpty`,
  `Cslib.MachineLearning.rademacherAverage_le_of_forall_exists`: nonnegativity, the value `0` for a
  single vector and for the empty family, and monotonicity.
* `Cslib.MachineLearning.rademacherAverage_eq_of_forall_exists`: families realizing the same
  vectors have the same Rademacher average.
* `Cslib.MachineLearning.rademacherAverage_add_mul_signVal_mul`: affine invariance; a fixed
  translation, fixed coordinate flips and a scaling by `β ≥ 0` multiply the average by `β`.
* `Cslib.MachineLearning.empiricalRademacherComplexity_singleton`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_empty`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_nonneg`,
  `Cslib.MachineLearning.empiricalRademacherComplexity_mono`: a single function and the empty
  class have complexity `0`, a nonempty bounded class has nonnegative complexity, and the
  complexity is monotone in the class.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_of_finite`: the bound through the number
  of restriction patterns.
* `Cslib.MachineLearning.empiricalRademacherComplexity_le_of_finset`,
  `Cslib.MachineLearning.rademacherComplexity_le_of_finset`: finite classes.
* `Cslib.MachineLearning.rademacherComplexity_le`,
  `Cslib.MachineLearning.rademacherComplexity_nonneg`,
  `Cslib.MachineLearning.rademacherComplexity_singleton`: a bound on every empirical complexity
  bounds the Rademacher complexity, which is nonnegative for a nonempty bounded class and `0` for a
  single function.

## References

* [M. Mohri, A. Rostamizadeh, A. Talwalkar, *Foundations of Machine Learning*, 2nd
  ed.][MohriRostamizadehTalwalkar2018], Chapter 3
* [P. L. Bartlett, S. Mendelson, *Rademacher and Gaussian complexities: risk bounds and
  structural results*][BartlettMendelson2002]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014], Chapter 26
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.MachineLearning

open Cslib.BitString

/-! ### Rademacher averages of vectors -/

/-- The **Rademacher average** of a family `a : ι → Fin m → ℝ` of vectors: the expected maximal
correlation `𝔼_σ ⨆ j, (1 / m) ∑ i, σ_i a j i` with a uniformly random sign vector `σ`, where
`signVal` turns bits into signs. For a family that is unbounded above for some `σ`, the real
supremum takes the junk value `0`. -/
noncomputable def rademacherAverage {ι : Type*} {m : ℕ} (a : ι → Fin m → ℝ) : ℝ :=
  𝔼 σ : Fin m → Bool, ⨆ j, 𝔼 i, signVal (σ i) * a j i

theorem rademacherAverage_def {ι : Type*} {m : ℕ} (a : ι → Fin m → ℝ) :
    rademacherAverage a = 𝔼 σ : Fin m → Bool, ⨆ j, 𝔼 i, signVal (σ i) * a j i := by
  rw [rademacherAverage]

/-- The Rademacher average with the normalization `1 / m` taken outside. -/
theorem rademacherAverage_eq_expect_ciSup_sum_div {ι : Type*} {m : ℕ} (a : ι → Fin m → ℝ) :
    rademacherAverage a = (𝔼 σ : Fin m → Bool, ⨆ j, ∑ i, a j i * signVal (σ i)) / m := by
  rw [rademacherAverage, Finset.expect_div]
  refine Finset.expect_congr rfl fun σ _ => ?_
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  rw [div_eq_mul_inv, Real.iSup_mul_of_nonneg (by positivity)]
  refine iSup_congr fun j => ?_
  rw [← div_eq_mul_inv]
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The correlation of a fixed vector with a uniformly random sign vector has mean zero. -/
private theorem expect_expect_signVal_mul_eq_zero {m : ℕ} (b : Fin m → ℝ) :
    𝔼 σ : Fin m → Bool, 𝔼 i, signVal (σ i) * b i = 0 := by
  calc 𝔼 σ : Fin m → Bool, 𝔼 i, signVal (σ i) * b i
      = 𝔼 σ : Fin m → Bool, (∑ i, b i * signVal (σ i)) / m :=
        Finset.expect_congr rfl fun σ _ => by
          rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
          congr 1
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = 0 := by rw [← Finset.expect_div, expect_sum_mul_signVal_eq_zero, zero_div]

/-- The Rademacher average of a single vector is `0`. -/
theorem rademacherAverage_unique {ι : Type*} [Unique ι] {m : ℕ} (a : ι → Fin m → ℝ) :
    rademacherAverage a = 0 := by
  simp only [rademacherAverage, ciSup_unique]
  exact expect_expect_signVal_mul_eq_zero _

/-- The Rademacher average of the empty family is `0`. -/
theorem rademacherAverage_of_isEmpty {ι : Type*} [IsEmpty ι] {m : ℕ} (a : ι → Fin m → ℝ) :
    rademacherAverage a = 0 := by
  simp only [rademacherAverage, Real.iSup_of_isEmpty, Finset.expect_const_zero]

/-- The Rademacher average of a nonempty bounded family is nonnegative: its supremum dominates any
single member, whose correlation with random signs has mean zero. -/
theorem rademacherAverage_nonneg {ι : Type*} [Nonempty ι] {m : ℕ} {a : ι → Fin m → ℝ} {B : ℝ}
    (ha : ∀ j i, |a j i| ≤ B) : 0 ≤ rademacherAverage a := by
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  calc (0 : ℝ) = 𝔼 σ : Fin m → Bool, 𝔼 i, signVal (σ i) * a j₀ i :=
        (expect_expect_signVal_mul_eq_zero _).symm
    _ ≤ rademacherAverage a := Finset.expect_le_expect fun σ _ =>
        le_ciSup (bddAbove_range_expect_signVal_mul a ha σ) j₀

/-- **Monotonicity.** If every vector of `a` occurs in the bounded family `b`, the Rademacher
average of `a` is at most that of `b`. -/
theorem rademacherAverage_le_of_forall_exists {ι κ : Type*} {m : ℕ} {a : ι → Fin m → ℝ}
    {b : κ → Fin m → ℝ} {B : ℝ} (hb : ∀ k i, |b k i| ≤ B) (hab : ∀ j, ∃ k, a j = b k) :
    rademacherAverage a ≤ rademacherAverage b := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [rademacherAverage_of_isEmpty]
    rcases isEmpty_or_nonempty κ with hκ | hκ
    · rw [rademacherAverage_of_isEmpty]
    · exact rademacherAverage_nonneg hb
  refine Finset.expect_le_expect fun σ _ => ciSup_le fun j => ?_
  obtain ⟨k, hk⟩ := hab j
  rw [hk]
  exact le_ciSup (bddAbove_range_expect_signVal_mul b hb σ) k

/-- Two bounded families realizing the same vectors have the same Rademacher average. -/
theorem rademacherAverage_eq_of_forall_exists {ι κ : Type*} {m : ℕ} {a : ι → Fin m → ℝ}
    {b : κ → Fin m → ℝ} {B : ℝ} (ha : ∀ j i, |a j i| ≤ B) (hb : ∀ k i, |b k i| ≤ B)
    (hab : ∀ j, ∃ k, a j = b k) (hba : ∀ k, ∃ j, b k = a j) :
    rademacherAverage a = rademacherAverage b :=
  le_antisymm (rademacherAverage_le_of_forall_exists hb hab)
    (rademacherAverage_le_of_forall_exists ha hba)

/-- **Affine invariance.** Translating every vector by a fixed `c`, flipping fixed coordinates
(multiplying coordinate `i` by `signVal (s i)`) and scaling by `β ≥ 0` multiplies the Rademacher
average of a bounded family by `β`: the translation has mean-zero correlation with the signs, and
a fixed flip preserves the uniform distribution of the sign vector. This is the computation in
the proof of [MohriRostamizadehTalwalkar2018, Lemma 3.4]. -/
theorem rademacherAverage_add_mul_signVal_mul {ι : Type*} {m : ℕ} {a : ι → Fin m → ℝ} {B : ℝ}
    (ha : ∀ j i, |a j i| ≤ B) (c : Fin m → ℝ) (s : Fin m → Bool) {β : ℝ} (hβ : 0 ≤ β) :
    rademacherAverage (fun j i => c i + β * (signVal (s i) * a j i)) =
      β * rademacherAverage a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [rademacherAverage_of_isEmpty, rademacherAverage_of_isEmpty, mul_zero]
  have hbdd (σ : Fin m → Bool) := bddAbove_range_expect_signVal_mul a ha σ
  have hσ (σ : Fin m → Bool) :
      ⨆ j, 𝔼 i, signVal (σ i) * (c i + β * (signVal (s i) * a j i)) =
        𝔼 i, signVal (σ i) * c i + β * ⨆ j, 𝔼 i, signVal (σ i ^^ s i) * a j i := by
    have hbddβ : BddAbove (Set.range fun j => β * 𝔼 i, signVal (σ i ^^ s i) * a j i) := by
      obtain ⟨M, hM⟩ := hbdd fun i => σ i ^^ s i
      refine ⟨β * M, ?_⟩
      rintro _ ⟨j, rfl⟩
      exact mul_le_mul_of_nonneg_left (hM ⟨j, rfl⟩) hβ
    rw [Real.mul_iSup_of_nonneg hβ, add_ciSup hbddβ]
    refine iSup_congr fun j => ?_
    rw [Finset.mul_expect, ← Finset.expect_add_distrib]
    refine Finset.expect_congr rfl fun i _ => ?_
    rw [signVal_xor]
    ring
  have hinv : Function.Involutive fun (σ : Fin m → Bool) i => σ i ^^ s i :=
    fun σ => funext fun i => by simp
  rw [rademacherAverage_def, rademacherAverage_def, Finset.expect_congr rfl fun σ _ => hσ σ,
    Finset.expect_add_distrib, expect_expect_signVal_mul_eq_zero, zero_add, Finset.mul_expect]
  exact Fintype.expect_equiv (Function.Involutive.toPerm _ hinv)
    (fun σ => β * ⨆ j, 𝔼 i, signVal (σ i ^^ s i) * a j i)
    (fun σ => β * ⨆ j, 𝔼 i, signVal (σ i) * a j i) fun σ => rfl

/-- **Massart's lemma**, normalized [MohriRostamizadehTalwalkar2018, Theorem 3.7]: the Rademacher
average of finitely many vectors of Euclidean norm at most `r` is at most `r √(2 log N) / m`. -/
theorem rademacherAverage_le {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → Fin m → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (ha : ∀ j, ∑ i, a j i ^ 2 ≤ r ^ 2) :
    rademacherAverage a ≤ r * √(2 * Real.log (Fintype.card ι)) / m := by
  rw [rademacherAverage_eq_expect_ciSup_sum_div]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  exact div_le_div_of_nonneg_right (expect_ciSup_sum_mul_signVal_le a hr ha) (Nat.cast_nonneg m)

/-- Massart's lemma for vectors with entries bounded by `B`: their Euclidean norms are at most
`B √m`, so the Rademacher average of `N` of them is at most `B √(2 log N / m)`. -/
theorem rademacherAverage_le_mul_sqrt {ι : Type*} [Fintype ι] {m : ℕ} (a : ι → Fin m → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ j i, |a j i| ≤ B) :
    rademacherAverage a ≤ B * √(2 * Real.log (Fintype.card ι) / m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [rademacherAverage, Real.iSup_const_zero]
  have hm' : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have h := rademacherAverage_le a (r := B * √m) (by positivity) fun j => by
    calc ∑ i, a j i ^ 2 ≤ ∑ _i : Fin m, B ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (ha j i) 2
      _ = (B * √m) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
            Real.sq_sqrt hm'.le, mul_comm]
  refine h.trans_eq ?_
  rw [Real.sqrt_div' _ hm'.le]
  field_simp
  rw [Real.sq_sqrt hm'.le]
  ring

/-! ### Function classes -/

variable {Z : Type*}

/-- The **empirical Rademacher complexity** of a class `F` of real functions on a sample
`S : Fin m → Z` [MohriRostamizadehTalwalkar2018, Definition 3.1]:
`𝔼_σ ⨆ f ∈ F, (1 / m) ∑ i, σ_i f (S i)` for uniformly random signs `σ`. -/
noncomputable def empiricalRademacherComplexity (F : Set (Z → ℝ)) {m : ℕ} (S : Fin m → Z) : ℝ :=
  rademacherAverage fun (f : F) i => (f : Z → ℝ) (S i)

theorem empiricalRademacherComplexity_def (F : Set (Z → ℝ)) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity F S = rademacherAverage fun (f : F) i => (f : Z → ℝ) (S i) := by
  rw [empiricalRademacherComplexity]

/-- The empty class has empirical Rademacher complexity `0`. -/
theorem empiricalRademacherComplexity_empty {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity (∅ : Set (Z → ℝ)) S = 0 :=
  rademacherAverage_of_isEmpty _

/-- A single function has empirical Rademacher complexity `0`. -/
theorem empiricalRademacherComplexity_singleton (f : Z → ℝ) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity {f} S = 0 :=
  rademacherAverage_unique _

/-- A nonempty bounded class has nonnegative empirical Rademacher complexity. -/
theorem empiricalRademacherComplexity_nonneg {F : Set (Z → ℝ)} (hne : F.Nonempty) {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {m : ℕ} (S : Fin m → Z) :
    0 ≤ empiricalRademacherComplexity F S :=
  have : Nonempty F := hne.to_subtype
  rademacherAverage_nonneg fun f _ => hF f f.2 _

/-- The empirical Rademacher complexity is monotone in a bounded class. -/
theorem empiricalRademacherComplexity_mono {F G : Set (Z → ℝ)} (hFG : F ⊆ G) {B : ℝ}
    (hG : ∀ g ∈ G, ∀ z, |g z| ≤ B) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity F S ≤ empiricalRademacherComplexity G S :=
  rademacherAverage_le_of_forall_exists (fun g _ => hG g g.2 _) fun f => ⟨⟨f, hFG f.2⟩, rfl⟩

/-- **Massart's lemma through restriction patterns** [MohriRostamizadehTalwalkar2018, Corollary
3.8]: if the restrictions `(f (S 0), …, f (S (m - 1)))` of the functions `f ∈ F` to the sample
form a finite set of `P` vectors, then the empirical Rademacher complexity of a class bounded by
`B` is at most `B √(2 log P / m)`. The source states the case of `{-1, +1}`-valued classes, where
`P` is at most the growth function. -/
theorem empiricalRademacherComplexity_le_of_finite {F : Set (Z → ℝ)} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {m : ℕ} (S : Fin m → Z)
    (hP : ((fun f : Z → ℝ => fun i => f (S i)) '' F).Finite) :
    empiricalRademacherComplexity F S ≤
      B * √(2 * Real.log ((fun f : Z → ℝ => fun i => f (S i)) '' F).ncard / m) := by
  have hPa : ∀ p ∈ hP.toFinset, ∀ i, |p i| ≤ B := by
    intro p hp i
    obtain ⟨f, hf, rfl⟩ := hP.mem_toFinset.1 hp
    exact hF f hf _
  have h := rademacherAverage_le_mul_sqrt (fun (p : hP.toFinset) => (p : Fin m → ℝ)) hB
    fun p i => hPa p p.2 i
  rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card _ hP] at h
  rw [empiricalRademacherComplexity_def]
  exact (rademacherAverage_le_of_forall_exists
    (b := fun (p : hP.toFinset) => (p : Fin m → ℝ)) (fun p i => hPa p p.2 i)
    fun (f : F) => ⟨⟨_, hP.mem_toFinset.2 ⟨f, f.2, rfl⟩⟩, rfl⟩).trans h

/-- **Massart's lemma for a finite class** bounded by `B`: the empirical Rademacher complexity is
at most `B √(2 log |F| / m)`. -/
theorem empiricalRademacherComplexity_le_of_finset {F : Finset (Z → ℝ)} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) {m : ℕ} (S : Fin m → Z) :
    empiricalRademacherComplexity (F : Set (Z → ℝ)) S ≤ B * √(2 * Real.log F.card / m) := by
  have h := rademacherAverage_le_mul_sqrt (fun (f : (F : Set (Z → ℝ))) i => (f : Z → ℝ) (S i))
    hB fun f i => hF f f.2 _
  rw [empiricalRademacherComplexity_def]
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using h

variable [Fintype Z]

/-- The **Rademacher complexity** of a class `F` for samples of size `m` from a distribution `D`
on a finite type [MohriRostamizadehTalwalkar2018, Definition 3.2]: the expected empirical
Rademacher complexity over `m` independent draws from `D`. -/
noncomputable def rademacherComplexity (D : PMF Z) (F : Set (Z → ℝ)) (m : ℕ) : ℝ :=
  ∑ S : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S).toReal *
    empiricalRademacherComplexity F S

theorem rademacherComplexity_def (D : PMF Z) (F : Set (Z → ℝ)) (m : ℕ) :
    rademacherComplexity D F m =
      ∑ S : Fin m → Z, ((Probability.PMF.pi fun _ : Fin m => D) S).toReal *
        empiricalRademacherComplexity F S := by
  rw [rademacherComplexity]

/-- A bound on the empirical complexity of every sample bounds the Rademacher complexity. -/
theorem rademacherComplexity_le (D : PMF Z) {F : Set (Z → ℝ)} {m : ℕ} {c : ℝ}
    (h : ∀ S : Fin m → Z, empiricalRademacherComplexity F S ≤ c) :
    rademacherComplexity D F m ≤ c :=
  Probability.PMF.sum_mul_le _ _ _ h

/-- A single function has Rademacher complexity `0`. -/
theorem rademacherComplexity_singleton (D : PMF Z) (f : Z → ℝ) (m : ℕ) :
    rademacherComplexity D {f} m = 0 := by
  simp only [rademacherComplexity_def, empiricalRademacherComplexity_singleton, mul_zero,
    Finset.sum_const_zero]

/-- A nonempty bounded class has nonnegative Rademacher complexity. -/
theorem rademacherComplexity_nonneg (D : PMF Z) {F : Set (Z → ℝ)} (hne : F.Nonempty) {B : ℝ}
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (m : ℕ) : 0 ≤ rademacherComplexity D F m :=
  Finset.sum_nonneg fun S _ =>
    mul_nonneg ENNReal.toReal_nonneg (empiricalRademacherComplexity_nonneg hne hF S)

/-- **Massart's lemma for a finite class** bounded by `B`: the Rademacher complexity is at most
`B √(2 log |F| / m)`. -/
theorem rademacherComplexity_le_of_finset (D : PMF Z) {F : Finset (Z → ℝ)} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ f ∈ F, ∀ z, |f z| ≤ B) (m : ℕ) :
    rademacherComplexity D (F : Set (Z → ℝ)) m ≤ B * √(2 * Real.log F.card / m) :=
  rademacherComplexity_le D fun S => empiricalRademacherComplexity_le_of_finset hB hF S

end Cslib.MachineLearning
