/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
import CslibFrontier.Foundations.Order.UpperLower
import Mathlib.Data.Bool.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spread laws and integral/fractional small covers

Finite subsets represent the Boolean cube. The spread parameter is small: containing a fixed
set I has probability at most q^|I|. Smallness uses the source budget 1/2. Weak smallness uses
an actual probability witness and the factor 1/2 of Definition 6.1, not an integral cover.

## Main definitions

* `IsSpread`, `IsSpreadLaw`: finite real masses and probability laws with containment bounds.
* `IsSmall`, `IsWeaklySmall`: Talagrand's two distinct covering notions.
* `upperKernel`: the normalized principal-upper-set indicator, including the empty set.
* `productProb`, `theta`: product sampling and restriction to a deterministic parent.

## Main results

* `kernel_average_le_one`: spread laws have bounded normalized upper-set moments.
* `IsSmall.isWeaklySmall`: an integral cover supplies an actual fractional witness.
* `not_isWeaklySmall_of_spread`: a family carrying a spread law is not weakly small.
* `isSpreadLaw_pure_empty`: a nonvacuous spread law on every finite ground set.

## References

[Talagrand2010Small], Definition 5.5 and (5.12)–(5.15) (author PDF p.5),
Definition 6.1 and (6.1)–(6.3) (p.6), Definition 6.6 (p.7), and (7.8)–(7.10) (p.10).
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Containment bounds for finite real masses; the empty test bounds the total mass by one. -/
@[expose] def IsSpread (q : ℝ) (w : Finset ι → ℝ) : Prop :=
  ∀ I, (∑ J : Finset ι, if I ⊆ J then w J else 0) ≤ q ^ I.card

/-- A probability law is q-spread in Talagrand's small-parameter convention. -/
abbrev IsSpreadLaw (q : ℝ) (ν : PMF (Finset ι)) : Prop :=
  IsSpread q (fun J => (ν J).toReal)

/-- A finite integral cover by principal upper sets, of p-cost at most 1/2. -/
@[expose] def IsSmall (p : ℝ) (A : Set (Finset ι)) : Prop :=
  ∃ G : Finset (Finset ι), (∀ J ∈ A, ∃ I ∈ G, I ⊆ J) ∧
    ∑ I ∈ G, p ^ I.card ≤ 1 / 2

open Classical in
/-- Talagrand's h(I,J): normalized containment; h(empty,J)=1. Used only at positive q. -/
@[expose] noncomputable def upperKernel (q : ℝ) (I J : Finset ι) : ℝ :=
  if I ⊆ J then (q ^ I.card)⁻¹ else 0

/-- The normalized witness score; Talagrand's Psi is half this value. -/
@[expose] noncomputable def coverScore (p : ℝ) (η : PMF (Finset ι)) (J : Finset ι) : ℝ :=
  ∑ I : Finset ι, (η I).toReal * upperKernel p I J

/-- The probability witness of Definition 6.1 has normalized score at least two on A. This is
exactly the source's score Psi=(1/2) times that expectation being at least one. -/
@[expose] def IsWeaklySmall (p : ℝ) (A : Set (Finset ι)) : Prop :=
  ∃ η : PMF (Finset ι), ∀ J ∈ A, 2 ≤ coverScore p η J

open Classical in
/-- Product-Bernoulli probability of a family, using the existing Boolean-mask expectation. -/
@[expose] noncomputable def productProb (p : ℝ) (A : Set (Finset ι)) : ℝ :=
  BitString.bernoulliAverage p (fun x => A.indicator 1 (univ.filter fun i => x i))

open Classical in
/-- Independently retain each element of J with probability alpha, then test membership in A. -/
@[expose] noncomputable def theta (α : ℝ) (A : Set (Finset ι)) (J : Finset ι) : ℝ :=
  BitString.bernoulliAverage α (fun x => A.indicator 1 (J.filter fun i => x i))

omit [Fintype ι] in
/-- A normalized containment score is nonnegative at a nonnegative parameter. -/
theorem upperKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (I J : Finset ι) :
    0 ≤ upperKernel q I J := by
  unfold upperKernel
  split_ifs <;> positivity

omit [Fintype ι] in
/-- Containment of the empty set has normalized score one, with no exceptional convention. -/
@[simp] theorem upperKernel_empty (q : ℝ) (J : Finset ι) : upperKernel q ∅ J = 1 := by
  simp [upperKernel]

/-- Product event probabilities are nonnegative for an actual Bernoulli parameter. -/
theorem productProb_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (A : Set (Finset ι)) :
    0 ≤ productProb p A := by
  classical
  have h := BitString.bernoulliAverage_mono hp hp' (f := fun _ : ι → Bool => 0)
    (g := fun x => A.indicator 1 (univ.filter fun i => x i)) (fun x => by
      by_cases hx : univ.filter (fun i => x i) ∈ A <;> simp [hx])
  simpa only [BitString.bernoulliAverage_const, productProb] using h

/-- Restricted product event probabilities are nonnegative for a Bernoulli parameter. -/
theorem theta_nonneg {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 1) (A : Set (Finset ι))
    (J : Finset ι) : 0 ≤ theta α A J := by
  classical
  have h := BitString.bernoulliAverage_mono hα hα' (f := fun _ : ι → Bool => 0)
    (g := fun x => A.indicator 1 (J.filter fun i => x i)) (fun x => by
      by_cases hx : J.filter (fun i => x i) ∈ A <;> simp [hx])
  simpa only [BitString.bernoulliAverage_const, theta] using h

/-- Increasing the retention rate increases every upper-event thinning probability. -/
theorem theta_mono {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1)
    {A : Set (Finset ι)} (hA : IsUpperSet A) (J : Finset ι) :
    theta α A J ≤ theta β A J := by
  classical
  have hm : Monotone (fun x : ι → Bool => J.filter fun i => x i) := by
    intro x y hxy i hi
    obtain ⟨hiJ, hix⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hiJ, ?_⟩
    exact Bool.le_iff_imp.mp (hxy i) hix
  have hf : Monotone (fun x : ι → Bool => A.indicator (1 : Finset ι → ℝ) (J.filter fun i => x i)) :=
    hA.monotone_indicator_one.comp hm
  have h := BitString.bernoulliAverage_le_bernoulliAverage_of_antitone hf.neg hα hαβ hβ
  simpa only [theta, BitString.bernoulliAverage, mul_neg, sum_neg_distrib, neg_le_neg_iff] using h

/-- Exact normalization of the containment moment, before imposing spreadness. -/
theorem kernel_average_eq (q : ℝ) (ν : PMF (Finset ι)) (I : Finset ι) :
    (∑ J : Finset ι, (ν J).toReal * upperKernel q I J) =
      (∑ J : Finset ι, if I ⊆ J then (ν J).toReal else 0) / q ^ I.card := by
  rw [div_eq_mul_inv, sum_mul]
  apply sum_congr rfl
  intro J _
  by_cases hIJ : I ⊆ J <;> simp [upperKernel, hIJ]

/-- Spreadness is exactly the family of normalized upper-set moment bounds. -/
theorem isSpreadLaw_iff_kernel {q : ℝ} (hq : 0 < q) (ν : PMF (Finset ι)) :
    IsSpreadLaw q ν ↔ ∀ I, (∑ J : Finset ι, (ν J).toReal * upperKernel q I J) ≤ 1 := by
  constructor <;> intro h I
  · rw [kernel_average_eq]
    exact (div_le_one (pow_pos hq _)).mpr (h I)
  · have hh := h I
    rw [kernel_average_eq] at hh
    exact (div_le_one (pow_pos hq _)).mp hh

/-- Each normalized upper-set moment is bounded by one under an actual spread law. -/
theorem kernel_average_le_one {q : ℝ} (hq : 0 < q) {ν : PMF (Finset ι)}
    (hν : IsSpreadLaw q ν) (I : Finset ι) :
    ∑ J : Finset ι, (ν J).toReal * upperKernel q I J ≤ 1 :=
  (isSpreadLaw_iff_kernel hq ν).mp hν I

/-- A fractional witness has average normalized score at most one under a spread law. -/
theorem average_coverScore_le_one {q : ℝ} (hq : 0 < q) {ν : PMF (Finset ι)}
    (hν : IsSpreadLaw q ν) (η : PMF (Finset ι)) :
    ∑ J : Finset ι, (ν J).toReal * coverScore q η J ≤ 1 := by
  calc _ = ∑ I : Finset ι, (η I).toReal *
        (∑ J : Finset ι, (ν J).toReal * upperKernel q I J) := by
          simp only [coverScore, mul_sum]
          rw [sum_comm]
          apply sum_congr rfl
          intro I _
          apply sum_congr rfl
          intro J _
          ring
    _ ≤ ∑ I : Finset ι, (η I).toReal * 1 := sum_le_sum fun I _ =>
      mul_le_mul_of_nonneg_left (kernel_average_le_one hq hν I) ENNReal.toReal_nonneg
    _ = 1 := by simpa only [mul_one] using PMF.sum_toReal η

/-- Proposition 6.7(b): a family carrying a q-spread law cannot be weakly q-small. -/
theorem not_isWeaklySmall_of_spread {q : ℝ} (hq : 0 < q) {ν : PMF (Finset ι)}
    (hν : IsSpreadLaw q ν) {A : Set (Finset ι)} (hA : ∀ J ∈ ν.support, J ∈ A) :
    ¬ IsWeaklySmall q A := by
  rintro ⟨η, hη⟩
  have hl : (2 : ℝ) ≤ ∑ J : Finset ι, (ν J).toReal * coverScore q η J := by
    calc 2 = ∑ J : Finset ι, (ν J).toReal * 2 := by rw [← sum_mul, PMF.sum_toReal]; ring
      _ ≤ _ := sum_le_sum fun J _ => by
        by_cases hJ : ν J = 0
        · simp [hJ]
        · exact mul_le_mul_of_nonneg_left (hη J (hA J ((PMF.mem_support_iff _ _).mpr hJ)))
            ENNReal.toReal_nonneg
  have hu := average_coverScore_le_one hq hν η
  linarith

/-- The point mass at the empty set is spread at every nonnegative rate, including zero. -/
theorem isSpreadLaw_pure_empty {q : ℝ} (hq : 0 ≤ q) :
    IsSpreadLaw q (PMF.pure (∅ : Finset ι)) := by
  classical
  intro I
  by_cases hI : I = ∅
  · subst I
    simpa using (PMF.sum_toReal (PMF.pure (∅ : Finset ι))).le
  · have hsub : ¬ I ⊆ (∅ : Finset ι) := by simpa using hI
    have he : (∑ J : Finset ι, if I ⊆ J then
        ((PMF.pure (∅ : Finset ι)) J).toReal else 0) = 0 := by
      apply sum_eq_zero
      intro J _
      by_cases hJ : J = ∅
      · subst J
        simp [hsub]
      · simp [PMF.pure_apply, hJ]
    rw [he]
    positivity

/-- Proposition 6.2: an integral p-small cover supplies an actual fractional probability witness. -/
theorem IsSmall.isWeaklySmall {p : ℝ} (hp : 0 < p) {A : Set (Finset ι)}
    (hA : IsSmall p A) : IsWeaklySmall p A := by
  classical
  obtain ⟨G, hcover, hcost⟩ := hA
  let cost : ℝ := ∑ I ∈ G, p ^ I.card
  let w (I : Finset ι) : ℝ := (if I ∈ G then 2 * p ^ I.card else 0) +
    if I = ∅ then 1 - 2 * cost else 0
  have hw (I) : 0 ≤ w I := by
    have hh : 0 ≤ 1 - 2 * cost := by dsimp only [cost]; linarith
    dsimp only [w]
    split_ifs <;> positivity
  have hsum : ∑ I : Finset ι, w I = 1 := by
    simp only [w, sum_add_distrib]
    simp only [sum_ite_mem, univ_inter, sum_ite_eq', mem_univ, ↓reduceIte]
    dsimp only [cost]
    rw [← mul_sum]
    ring
  let η : PMF (Finset ι) := PMF.ofFintype (fun I => ENNReal.ofReal (w I)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun I _ => hw I), hsum, ENNReal.ofReal_one])
  have hη (I) : (η I).toReal = w I := by
    exact ENNReal.toReal_ofReal (hw I)
  refine ⟨η, ?_⟩
  intro J hJ
  obtain ⟨I, hIG, hIJ⟩ := hcover J hJ
  have hpow : 0 < p ^ I.card := pow_pos hp _
  have hweight : 2 * p ^ I.card ≤ (η I).toReal := by
    rw [hη]
    have hh : 0 ≤ 1 - 2 * cost := by dsimp only [cost]; linarith
    simp only [w, hIG, ↓reduceIte]
    split_ifs <;> linarith
  calc 2 = (2 * p ^ I.card) * (p ^ I.card)⁻¹ := by field_simp
    _ ≤ (η I).toReal * (p ^ I.card)⁻¹ :=
      mul_le_mul_of_nonneg_right hweight (inv_nonneg.mpr hpow.le)
    _ = (η I).toReal * upperKernel p I J := by rw [upperKernel, ite_eq_left hIJ]
    _ ≤ coverScore p η J := single_le_sum
      (fun K _ => mul_nonneg ENNReal.toReal_nonneg (upperKernel_nonneg hp.le K J)) (mem_univ I)

omit [Fintype ι] [DecidableEq ι] in
/-- The empty family has an empty integral cover. -/
theorem isSmall_empty (p : ℝ) : IsSmall p (∅ : Set (Finset ι)) := by
  refine ⟨∅, by simp, ?_⟩
  simp

end Cslib.Probability.Spread
