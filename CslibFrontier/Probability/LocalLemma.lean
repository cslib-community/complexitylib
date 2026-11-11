/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Product
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Measure.Real
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpOneSubInvPow
import CslibFrontier.Foundations.Probability.SecondMoment
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential

/-!
# The Lovász Local Lemma

Let `A i` be finitely many events in a probability space, and let `Γ i` be a set of indices such
that `A i` is (lopsidedly) independent of the events outside `Γ i ∪ {i}`: for every set `s` of
indices avoiding `Γ i` and `i`, the probability that `A i` occurs while no `A j` with `j ∈ s`
occurs is at most `μ (A i)` times the probability that no `A j` with `j ∈ s` occurs. This holds
with equality when `A i` is mutually independent of the events `A j` with `j ∉ Γ i ∪ {i}`, so `Γ`
may be the neighborhood map of a dependency graph [Alon and Spencer, Section 5.1][AlonSpencer2016];
the inequality is the lopsided condition of Erdős and Spencer [ErdosSpencer1991].

* **Asymmetric form** (`Cslib.Probability.prod_one_sub_le_measureReal_iInter_compl`): if
  `x i ∈ [0, 1]` and `μ (A i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` for every `i`, then no event occurs with
  probability at least `∏ i, (1 - x i)` [Alon and Spencer, Lemma 5.1.1][AlonSpencer2016].
* **Symmetric form** (`Cslib.Probability.measureReal_iInter_compl_pos`): if every event has
  probability at most `q`, every `Γ i` has at most `d` elements and `e q (d + 1) ≤ 1`, then with
  positive probability no event occurs [Alon and Spencer, Corollary 5.1.2][AlonSpencer2016],
  [ErdosLovasz1975]; quantitatively, with probability at least `(d / (d + 1)) ^ n` for `n` events
  (`Cslib.Probability.pow_le_measureReal_iInter_compl`).

The proof shows, by strong induction on `s`, that `μ (A i ∩ ⋂ j ∈ s, (A j)ᶜ)` is at most
`x i * μ (⋂ j ∈ s, (A j)ᶜ)` for `i ∉ s`; no conditional probabilities or divisions appear.

In a finite product space `Cslib.Probability.PMF.pi p`, events depending on disjoint sets of
coordinates (Mathlib's `DependsOn`) are independent
(`Cslib.Probability.PMF.toOuterMeasure_pi_inter_eq_mul`, the PMF form of
`ProbabilityTheory.indepSet_pi_of_dependsOn`). So if each event `A i` depends only on the
coordinates in a set `vbl i`, the events sharing no coordinate
with `A i` satisfy the hypothesis, giving the variable version of the local lemma used for
satisfiability and coloring problems (`Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl`,
`Cslib.Probability.PMF.pi_iInter_compl_pos`) [MoserTardos2010].

## Main results

* `Cslib.Probability.prod_one_sub_le_measureReal_iInter_compl`: the asymmetric (lopsided) local
  lemma for a probability measure.
* `Cslib.Probability.pow_le_measureReal_iInter_compl`,
  `Cslib.Probability.measureReal_iInter_compl_pos`: the symmetric local lemma.
* `Cslib.Probability.PMF.toOuterMeasure_pi_inter_eq_mul`: events on disjoint coordinates of a
  product are independent.
* `Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl`,
  `Cslib.Probability.PMF.pi_iInter_compl_pos`: the asymmetric and symmetric local lemmas for events
  depending on sets of independent coordinates.

## References

* [N. Alon, J. H. Spencer, *The Probabilistic Method*, Chapter 5][AlonSpencer2016]
* [P. Erdős, L. Lovász, *Problems and results on 3-chromatic hypergraphs and some related
  questions*][ErdosLovasz1975]
* [P. Erdős, J. Spencer, *Lopsided Lovász Local Lemma and Latin transversals*][ErdosSpencer1991]
* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory Finset

section Measure

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {A : ι → Set Ω}

/-- Adding an index `i` to `s` multiplies the probability that no event of `s` occurs by at least
`1 - x`, once `A i` occurs together with that event with probability at most `x` times it. -/
private theorem one_sub_mul_le_measureReal_insert [DecidableEq ι]
    (hA : ∀ i, MeasurableSet (A i)) {s : Finset ι} {i : ι} {x : ℝ}
    (h : μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ x * μ.real (⋂ j ∈ s, (A j)ᶜ)) :
    (1 - x) * μ.real (⋂ j ∈ s, (A j)ᶜ) ≤ μ.real (⋂ j ∈ insert i s, (A j)ᶜ) := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := ⋂ j ∈ s, (A j)ᶜ) (hA i)
  rw [Set.inter_comm, Set.sdiff_eq_compl_inter] at hsplit
  rw [set_biInter_insert]
  linarith

/-- Adding the indices of `u` one at a time to `t` multiplies the probability that no event
occurs by at least `∏ j ∈ u, (1 - x j)`, given the inductive bound for the intermediate sets. -/
private theorem prod_mul_le_measureReal_union [DecidableEq ι]
    (hA : ∀ i, MeasurableSet (A i)) (x : ι → ℝ) (hx : ∀ i, x i ≤ 1) {t u : Finset ι}
    (htu : Disjoint t u)
    (hP : ∀ s, t ⊆ s → s ⊆ t ∪ u → #s < #(t ∪ u) → ∀ i ∉ s,
      μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ x i * μ.real (⋂ j ∈ s, (A j)ᶜ)) :
    (∏ j ∈ u, (1 - x j)) * μ.real (⋂ j ∈ t, (A j)ᶜ) ≤ μ.real (⋂ j ∈ t ∪ u, (A j)ᶜ) := by
  induction u using Finset.induction_on with
  | empty => simp
  | insert a u ha ih =>
    have hat : a ∉ t := disjoint_left.1 htu.symm (mem_insert_self a u)
    have hau : a ∉ t ∪ u := by simp [hat, ha]
    have hsub : t ∪ u ⊆ t ∪ insert a u := union_subset_union_right (subset_insert a u)
    have hcard : #(t ∪ u) < #(t ∪ insert a u) := by
      rw [union_insert, card_insert_of_notMem hau]
      omega
    have ih' := ih (htu.mono_right (subset_insert a u))
      fun s hts hsu hs => hP s hts (hsu.trans hsub) (hs.trans hcard)
    have hstep := one_sub_mul_le_measureReal_insert hA
      (hP (t ∪ u) subset_union_left hsub hcard a hau)
    rw [union_insert, prod_insert ha, mul_assoc]
    exact (mul_le_mul_of_nonneg_left ih' (sub_nonneg.2 (hx a))).trans hstep

/-- The inductive bound of the local lemma: for `i ∉ s`, the event `A i` occurs while no event of
`s` occurs with probability at most `x i` times the probability that no event of `s` occurs. -/
private theorem measureReal_inter_iInter_compl_le
    (hA : ∀ i, MeasurableSet (A i)) (Γ : ι → Finset ι)
    (hΓ : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ.real (A i) * μ.real (⋂ j ∈ s, (A j)ᶜ))
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hAx : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) (s : Finset ι) :
    ∀ i ∉ s, μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ x i * μ.real (⋂ j ∈ s, (A j)ᶜ) := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  intro i hi
  set s₁ := s.filter (· ∈ Γ i)
  set s₂ := s.filter (· ∉ Γ i)
  have hunion : s₂ ∪ s₁ = s := by
    rw [union_comm]
    exact filter_union_filter_not_eq _ s
  have hchain := prod_mul_le_measureReal_union hA x (fun j => (hx j).2)
    (disjoint_filter_filter_not s s _).symm fun s' _ hs' hcard j hj =>
      ih s' (Finset.ssubset_iff_subset_ne.2 ⟨hunion ▸ hs', fun h => by
        rw [h, hunion] at hcard
        exact lt_irrefl _ hcard⟩) j hj
  rw [hunion] at hchain
  have hmono : A i ∩ ⋂ j ∈ s, (A j)ᶜ ⊆ A i ∩ ⋂ j ∈ s₂, (A j)ᶜ := by
    refine Set.inter_subset_inter_right _ fun ω hω => ?_
    simp only [Set.mem_iInter] at hω ⊢
    exact fun j hj => hω j (mem_filter.1 hj).1
  have hprod : ∏ j ∈ Γ i, (1 - x j) ≤ ∏ j ∈ s₁, (1 - x j) :=
    prod_le_prod_of_subset_of_le_one₀ (fun _ hj => (mem_filter.1 hj).2)
      (fun j _ => sub_nonneg.2 (hx j).2) fun j _ _ => sub_le_self _ (hx j).1
  calc μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ)
      ≤ μ.real (A i ∩ ⋂ j ∈ s₂, (A j)ᶜ) := measureReal_mono hmono
    _ ≤ μ.real (A i) * μ.real (⋂ j ∈ s₂, (A j)ᶜ) :=
        hΓ i s₂ (fun h => hi (mem_filter.1 h).1)
          (disjoint_left.2 fun _ hj => (mem_filter.1 hj).2)
    _ ≤ (x i * ∏ j ∈ s₁, (1 - x j)) * μ.real (⋂ j ∈ s₂, (A j)ᶜ) :=
        mul_le_mul_of_nonneg_right ((hAx i).trans
          (mul_le_mul_of_nonneg_left hprod (hx i).1)) measureReal_nonneg
    _ = x i * ((∏ j ∈ s₁, (1 - x j)) * μ.real (⋂ j ∈ s₂, (A j)ᶜ)) := mul_assoc _ _ _
    _ ≤ x i * μ.real (⋂ j ∈ s, (A j)ᶜ) := mul_le_mul_of_nonneg_left hchain (hx i).1

/-- **The Lovász Local Lemma**, asymmetric and lopsided form [Alon and Spencer, Lemma 5.1.1]
[AlonSpencer2016], [ErdosSpencer1991]: let `A i` be finitely many measurable events and let `Γ i`
be sets of indices such that `A i` is lopsidedly independent of the events outside `Γ i ∪ {i}`.
If `x i ∈ [0, 1]` and `μ (A i) ≤ x i ∏ j ∈ Γ i, (1 - x j)` for every `i`, then no event occurs with
probability at least `∏ i, (1 - x i)`, which is positive when every `x i < 1`. -/
theorem prod_one_sub_le_measureReal_iInter_compl [Fintype ι]
    (hA : ∀ i, MeasurableSet (A i)) (Γ : ι → Finset ι)
    (hΓ : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ.real (A i) * μ.real (⋂ j ∈ s, (A j)ᶜ))
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hAx : ∀ i, μ.real (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ μ.real (⋂ i, (A i)ᶜ) := by
  classical
  have h := prod_mul_le_measureReal_union hA x (fun i => (hx i).2) (disjoint_empty_left univ)
    fun s _ _ _ i hi => measureReal_inter_iInter_compl_le hA Γ hΓ x hx hAx s i hi
  simpa only [notMem_empty, Set.iInter_of_empty, Set.iInter_univ, probReal_univ,
    mul_one, empty_union, mem_univ, Set.iInter_true] using h

/-- `(d / (d + 1)) ^ d ≥ 1 / e`. -/
private theorem exp_one_inv_le_div_pow (d : ℕ) :
    (Real.exp 1)⁻¹ ≤ ((d : ℝ) / (d + 1)) ^ d := by
  have hsub : 1 - ((d : ℝ) + 1)⁻¹ = d / (d + 1) := by
    field_simp
    ring
  rw [← Real.exp_neg, ← hsub]
  exact Real.exp_neg_one_le_one_sub_inv_pow le_rfl

/-- The symmetric Local Lemma inequality `e * q * (d + 1) ≤ 1` implies the asymmetric weight bound
`q ≤ (1 / (d + 1)) * (1 - 1 / (d + 1)) ^ k` for every `k ≤ d`. -/
theorem le_inv_add_one_mul_one_sub_pow {d k : ℕ} {q : ℝ} (hk : k ≤ d)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    q ≤ (1 / ((d : ℝ) + 1)) * (1 - 1 / ((d : ℝ) + 1)) ^ k := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hsub : 1 - 1 / ((d : ℝ) + 1) = d / (d + 1) := by
    field_simp
    ring
  have hratio : (0 : ℝ) ≤ d / (d + 1) := by positivity
  have hratio₁ : (d : ℝ) / (d + 1) ≤ 1 := (div_le_one hd1).2 (by linarith)
  rw [hsub]
  calc q ≤ 1 / ((d + 1) * Real.exp 1) := by
        rw [le_div_iff₀ (by positivity)]
        calc q * ((d + 1) * Real.exp 1) = Real.exp 1 * q * (d + 1) := by ring
          _ ≤ 1 := hlll
    _ = 1 / (d + 1) * (Real.exp 1)⁻¹ := by rw [one_div, one_div, mul_inv]
    _ ≤ 1 / (d + 1) * ((d : ℝ) / (d + 1)) ^ d :=
        mul_le_mul_of_nonneg_left (exp_one_inv_le_div_pow d) (by positivity)
    _ ≤ 1 / (d + 1) * ((d : ℝ) / (d + 1)) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hratio hratio₁ hk) (by positivity)

/-- **The symmetric Lovász Local Lemma, quantitative form**: if each of `n` measurable events has
probability at most `q`, each `A i` is lopsidedly independent of the events outside `Γ i ∪ {i}`,
each `Γ i` has at most `d` elements, and `e q (d + 1) ≤ 1`, then no event occurs with probability
at least `(d / (d + 1)) ^ n`. This is positive when `d ≥ 1`. -/
theorem pow_le_measureReal_iInter_compl [Fintype ι]
    (hA : ∀ i, MeasurableSet (A i)) (Γ : ι → Finset ι)
    (hΓ : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ.real (A i) * μ.real (⋂ j ∈ s, (A j)ᶜ))
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d) {q : ℝ} (hq : ∀ i, μ.real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ((d : ℝ) / (d + 1)) ^ Fintype.card ι ≤ μ.real (⋂ i, (A i)ᶜ) := by
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hsub : 1 - 1 / ((d : ℝ) + 1) = d / (d + 1) := by field_simp; ring
  have h := prod_one_sub_le_measureReal_iInter_compl hA Γ hΓ (fun _ => 1 / ((d : ℝ) + 1))
    (fun _ => ⟨by positivity, (div_le_one hd1).2 (by linarith [d.cast_nonneg (α := ℝ)])⟩)
    fun i => by
      simpa only [prod_const] using (hq i).trans (le_inv_add_one_mul_one_sub_pow (hd i) hlll)
  simpa only [hsub, prod_const, card_univ] using h

/-- **The symmetric Lovász Local Lemma** [Alon and Spencer, Corollary 5.1.2][AlonSpencer2016],
[ErdosLovasz1975]: if each of finitely many measurable events has probability at most `q`, each
`A i` is lopsidedly independent of the events outside `Γ i ∪ {i}`, each `Γ i` has at most `d`
elements, and `e q (d + 1) ≤ 1`, then with positive probability no event occurs. -/
theorem measureReal_iInter_compl_pos [Finite ι]
    (hA : ∀ i, MeasurableSet (A i)) (Γ : ι → Finset ι)
    (hΓ : ∀ i (s : Finset ι), i ∉ s → Disjoint s (Γ i) →
      μ.real (A i ∩ ⋂ j ∈ s, (A j)ᶜ) ≤ μ.real (A i) * μ.real (⋂ j ∈ s, (A j)ᶜ))
    {d : ℕ} (hd : ∀ i, #(Γ i) ≤ d) {q : ℝ} (hq : ∀ i, μ.real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    0 < μ.real (⋂ i, (A i)ᶜ) := by
  have := Fintype.ofFinite ι
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · -- Without dependencies, take `x i = μ (A i) ≤ q ≤ 1 / e < 1`.
    have hq1 : q < 1 := by
      have he := Real.add_one_le_exp 1
      rw [Nat.cast_zero, zero_add, mul_one] at hlll
      by_contra h
      push Not at h
      nlinarith
    have hΓ0 (i : ι) : Γ i = ∅ := card_eq_zero.1 (Nat.le_zero.1 (hd i))
    refine lt_of_lt_of_le ?_ (prod_one_sub_le_measureReal_iInter_compl hA Γ hΓ
      (fun i => μ.real (A i)) (fun i => ⟨measureReal_nonneg, measureReal_le_one⟩)
      fun i => by simp [hΓ0 i])
    exact prod_pos fun i _ => sub_pos.2 ((hq i).trans_lt hq1)
  · exact lt_of_lt_of_le (pow_pos (by positivity) _)
      (pow_le_measureReal_iInter_compl hA Γ hΓ hd hq hlll)

end Measure

namespace PMF

section Product

variable {V : Type*} [Fintype V] {α : V → Type*} [∀ v, Finite (α v)]

/-- **Events on disjoint coordinates are independent**: in an independent product, an event
depending only on the coordinates in `S` and an event depending only on the coordinates in a
disjoint set `T` are independent. This is the finite-PMF form of
`ProbabilityTheory.indepSet_pi_of_dependsOn`. -/
theorem toOuterMeasure_pi_inter_eq_mul (p : ∀ v, PMF (α v)) {S T : Set V}
    (hST : Disjoint S T) {E F : Set (∀ v, α v)} (hE : DependsOn (· ∈ E) S)
    (hF : DependsOn (· ∈ F) T) :
    (pi p).toOuterMeasure (E ∩ F) = (pi p).toOuterMeasure E * (pi p).toOuterMeasure F := by
  let (v : V) : MeasurableSpace (α v) := ⊤
  have hmeas (B : Set (∀ v, α v)) : MeasurableSet B := (Set.to_countable B).measurableSet
  have hind := indepSet_pi_of_dependsOn (μ := fun v => (p v).toMeasure) (hmeas E) (hmeas F)
    hE hF hST
  rw [← toMeasure_pi] at hind
  simpa only [PMF.toMeasure_apply_eq_toOuterMeasure_apply _ (hmeas _)] using
    (indepSet_iff_measure_inter_eq_mul (hmeas E) (hmeas F) _).1 hind

/-- Under an independent product, an event `A i` depending only on the coordinates in `vbl i` is
independent of the event that no `A j` occurs, for indices `j ∉ Γ i ∪ {i}` sharing no coordinate
with `A i`. -/
private theorem pi_inter_iInter_compl_eq {ι : Type*} (p : ∀ v, PMF (α v))
    (A : ι → Set (∀ v, α v)) (vbl : ι → Finset V) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {i : ι} {s : Finset ι} (hi : i ∉ s) (hs : Disjoint s (Γ i)) :
    ((pi p).toOuterMeasure (A i ∩ ⋂ j ∈ s, (A j)ᶜ)).toReal =
      ((pi p).toOuterMeasure (A i)).toReal *
        ((pi p).toOuterMeasure (⋂ j ∈ s, (A j)ᶜ)).toReal := by
  classical
  have hdisj : Disjoint (vbl i) (s.biUnion vbl) := by
    refine (disjoint_biUnion_right _ _ _).2 fun j hj => ?_
    by_contra h
    exact disjoint_left.1 hs hj (hΓ i j (fun hji => hi (hji ▸ hj)) h)
  have hrest : DependsOn (· ∈ ⋂ j ∈ s, (A j)ᶜ) (s.biUnion vbl : Set V) := fun ω ω' h => by
    have hmem (j : ι) (hj : j ∈ s) : (ω ∈ A j) = (ω' ∈ A j) :=
      (hA j).mono (fun v hv => mem_coe.2 (mem_biUnion.2 ⟨j, hj, hv⟩)) h
    simp only [Set.mem_iInter, Set.mem_compl_iff]
    exact propext (forall₂_congr fun j hj => by rw [hmem j hj])
  rw [toOuterMeasure_pi_inter_eq_mul p (disjoint_coe.2 hdisj) (hA i) hrest, ENNReal.toReal_mul]

/-- **The Lovász Local Lemma for independent coordinates**, asymmetric form: let each event `A i`
of an independent product depend only on the coordinates in `vbl i`, and let `Γ i` contain every
other index whose event shares a coordinate with `A i`. If `x i ∈ [0, 1]` and
`Pr[A i] ≤ x i ∏ j ∈ Γ i, (1 - x j)` for every `i`, then no event occurs with probability at least
`∏ i, (1 - x i)`. -/
theorem prod_one_sub_le_pi_iInter_compl {ι : Type*} [Fintype ι] (p : ∀ v, PMF (α v))
    (A : ι → Set (∀ v, α v)) (vbl : ι → Finset V) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Icc 0 1)
    (hAx : ∀ i, ((pi p).toOuterMeasure (A i)).toReal ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i, (1 - x i) ≤ ((pi p).toOuterMeasure (⋂ i, (A i)ᶜ)).toReal := by
  let (v : V) : MeasurableSpace (α v) := ⊤
  have hreal (E : Set (∀ v, α v)) :
      (pi p).toMeasure.real E = ((pi p).toOuterMeasure E).toReal := by
    rw [measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
      ((Set.to_countable _).measurableSet)]
  have h := prod_one_sub_le_measureReal_iInter_compl (μ := (pi p).toMeasure)
    (fun i => (Set.to_countable (A i)).measurableSet) Γ
    (fun i s hi hs => by
      simp only [hreal]
      exact (pi_inter_iInter_compl_eq p A vbl hA Γ hΓ hi hs).le)
    x hx fun i => by simpa only [hreal] using hAx i
  simpa only [hreal] using h

/-- **The symmetric Lovász Local Lemma for independent coordinates**: let each event `A i` of an
independent product depend only on the coordinates in `vbl i`, let each event share coordinates
with at most `d` other events, and let each event have probability at most `q`. If
`e q (d + 1) ≤ 1`, then with positive probability no event occurs. -/
theorem pi_iInter_compl_pos {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
    (p : ∀ v, PMF (α v)) (A : ι → Set (∀ v, α v)) (vbl : ι → Finset V)
    (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V)) {d : ℕ}
    (hd : ∀ i, #{j | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d) {q : ℝ}
    (hq : ∀ i, ((pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    0 < ((pi p).toOuterMeasure (⋂ i, (A i)ᶜ)).toReal := by
  let (v : V) : MeasurableSpace (α v) := ⊤
  have hreal (E : Set (∀ v, α v)) :
      (pi p).toMeasure.real E = ((pi p).toOuterMeasure E).toReal := by
    rw [measureReal_def, PMF.toMeasure_apply_eq_toOuterMeasure_apply _
      ((Set.to_countable _).measurableSet)]
  let Γ (i : ι) : Finset ι := {j | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)}
  have h := measureReal_iInter_compl_pos (μ := (pi p).toMeasure)
    (fun i => (Set.to_countable (A i)).measurableSet) Γ
    (fun i s hi hs => by
      simp only [hreal]
      exact (pi_inter_iInter_compl_eq p A vbl hA Γ
        (fun i j hji hij => by simp [Γ, hji, hij]) hi hs).le)
    hd (fun i => by simpa only [hreal] using hq i) hlll
  simpa only [hreal] using h

end Product

end PMF

end Cslib.Probability
