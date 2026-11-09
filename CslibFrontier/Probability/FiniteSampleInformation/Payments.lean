/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteSampleInformation.Estimation
public import CslibFrontier.Probability.FiniteSampleInformation.AsymmetricPolynomialCorollary
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDegreeBound
public import CslibFrontier.Probability.FiniteSampleInformation.FinalPaperTheorems

/-!
# Sharp finite-task payment bounds

[Kong2027], Lemma 6.1 and Theorem 6.2 (PDF pp. 17–18).
A payment is an actual signed statistic on a vector of i.i.d. report pairs.
Every incentive condition holds uniformly over the closed probability simplex.
Channels use the same task-by-task randomization independently across tasks;
no claim about arbitrary joint-task deviations is made here.
-/

public section
noncomputable section
open scoped BigOperators

namespace Cslib.FiniteSampleInformation
open GeneralAsymmetricC1

/-- A signed payment depending on a fixed finite number of reports. -/
abbrev Payment (n m d : ℕ) := (Fin d → Fin n × Fin m) → ℝ

/-- Actual expected payment under `d` independent report pairs. -/
@[expose] def expectedPayment {n m d : ℕ} (M : Payment n m d) (U : Mat n m) : ℝ :=
  Estimation.expectation (fun ia => U ia.1 ia.2) d M

/-- Flattening a joint table identifies its simplex with the finite probability simplex. -/
theorem simplex_iff_isProbability {n m : ℕ} (U : Mat n m) :
    Simplex U ↔ Estimation.IsProbability (fun ia : Fin n × Fin m => U ia.1 ia.2) := by
  simp only [Simplex, Nonnegative, mass, Estimation.IsProbability,
    Fintype.sum_prod_type, Prod.forall]

/-- The expected-payment polynomial is obtained from the actual payment statistic. -/
@[expose] def paymentPolynomial {n m d : ℕ} (M : Payment n m d) :
    MvPolynomial (Fin n × Fin m) ℝ := Estimation.expectationPolynomial d M

/-- The probability of a report vector is the product of its task probabilities. -/
theorem expectedPayment_eq_sum {n m d : ℕ} (M : Payment n m d) (U : Mat n m) :
    expectedPayment M U = ∑ v : Fin d → Fin n × Fin m,
      M v * ∏ t, U (v t).1 (v t).2 :=
  Estimation.expectation_eq_sum _ _ _

/-- Every `d`-task expected payment has polynomial degree at most `d`. -/
theorem paymentPolynomial_totalDegree {n m d : ℕ} (M : Payment n m d) :
    (paymentPolynomial M).totalDegree ≤ d :=
  Estimation.expectationPolynomial_totalDegree d M

/-- The polynomial computes the payment expectation, with no assumptions on the table. -/
theorem eval_paymentPolynomial {n m d : ℕ} (M : Payment n m d) (U : Mat n m) :
    WidePolynomial.peval (paymentPolynomial M) U = expectedPayment M U :=
  Estimation.eval_expectationPolynomial _ _ _

/-- Truthful Alice cannot gain by a memoryless channel when Bob is truthful. -/
@[expose] def TruthfulAlice {n m d : ℕ} (M : Payment n m d) : Prop :=
  ∀ (T : Mat n n) (U : Mat n m), ColumnStochastic T → Simplex U →
    expectedPayment M (T * U) ≤ expectedPayment M U

/-- Independence-zero is a condition on expected, rather than realized, payments. -/
@[expose] def IndependenceZeroPayment {n m d : ℕ} (M : Payment n m d) : Prop :=
  RKO (expectedPayment M)

/-- Nontriviality refers to some truthful expected payment on the simplex. -/
@[expose] def NontrivialPayment {n m d : ℕ} (M : Payment n m d) : Prop :=
  ∃ U : Mat n m, Simplex U ∧ expectedPayment M U ≠ 0

/-- Lemma 6.1: actual expected payments, not arbitrary supplied polynomials,
are degree-bounded independence-zero monotones. -/
theorem paymentPolynomial_properties {n m d : ℕ} (M : Payment n m d)
    (hT : TruthfulAlice M) (hIZ : IndependenceZeroPayment M) :
    (paymentPolynomial M).totalDegree ≤ d ∧
      WidePolynomial.PolynomialDPI (paymentPolynomial M) ∧
      WidePolynomial.PolynomialRKO (paymentPolynomial M) := by
  refine ⟨paymentPolynomial_totalDegree M, ?_, ?_⟩
  · intro T U hT' hU
    simpa only [eval_paymentPolynomial] using hT T U hT' hU
  · intro x y hU
    simpa only [eval_paymentPolynomial] using hIZ x y hU

/-- Theorem 6.2(i): the larger-alphabet agent has zero expected payment
for every finite-task rule satisfying the stated incentives and normalization. -/
theorem larger_alphabet_payment_zero {n m d : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (M : Payment n m d) (hT : TruthfulAlice M) (hIZ : IndependenceZeroPayment M)
    {U : Mat n m} (hU : Simplex U) : expectedPayment M U = 0 := by
  have hprops := paymentPolynomial_properties M hT hIZ
  have hzero := general_asymmetric_simplex_C1 hm hnm
    (WidePolynomial.peval (paymentPolynomial M))
    (AsymmetricPolynomial.peval_contDiff (paymentPolynomial M)) hprops.2.1 hprops.2.2 U hU
  exact (eval_paymentPolynomial M U).symm.trans hzero

/-- Theorem 6.2(ii), necessity: a nontrivial truthful square payment uses at
least `2n` tasks. No degree bound is assumed of the payment. -/
theorem square_payment_task_lower_bound {n d : ℕ} (hn : 2 ≤ n)
    (M : Payment n n d) (hT : TruthfulAlice M) (hIZ : IndependenceZeroPayment M)
    (hNontrivial : NontrivialPayment M) : 2 * n ≤ d := by
  have hprops := paymentPolynomial_properties M hT hIZ
  apply (SquarePolynomial.square_simplex_totalDegree_lower_bound hn
    (paymentPolynomial M) hprops.2.1 hprops.2.2 ?_).trans hprops.1
  obtain ⟨U, hU, hMU⟩ := hNontrivial
  exact ⟨U, hU, by
    change WidePolynomial.peval (paymentPolynomial M) U ≠ 0
    simpa only [eval_paymentPolynomial] using hMU⟩

/-- Transposing the joint table exchanges the two agents. -/
@[expose] def swapAgents {n m : ℕ} (U : Mat n m) : Mat m n := fun a i => U i a

/-- Transposition preserves probability tables, including null rows and columns. -/
theorem swapAgents_simplex {n m : ℕ} {U : Mat n m} (hU : Simplex U) :
    Simplex (swapAgents U) := by
  refine ⟨fun a i => hU.1 i a, ?_⟩
  change (∑ a, ∑ i, U i a) = 1
  rw [Finset.sum_comm]
  exact hU.2

/-- Bob's memoryless report channel acts on the transposed table. -/
@[expose] def bobReports {n m : ℕ} (S : Mat m m) (U : Mat n m) : Mat n m :=
  swapAgents (S * swapAgents U)

/-- A fixed peer channel produces another valid joint law. -/
theorem bobReports_simplex {n m : ℕ} {S : Mat m m} {U : Mat n m}
    (hS : ColumnStochastic S) (hU : Simplex U) : Simplex (bobReports S U) :=
  swapAgents_simplex (stochastic_mul_simplex hS (swapAgents_simplex hU))

/-- Both agents' taskwise independent reporting rules give the same joint
law whichever channel is applied first. -/
theorem reports_commute {n m : ℕ} (T : Mat n n) (S : Mat m m) (U : Mat n m) :
    T * bobReports S U = bobReports S (T * U) := by
  ext i b
  simp only [mat_mul_apply, bobReports, swapAgents, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Dominance for a common payment to both agents, against every fixed
memoryless peer channel. Both report laws are actual independent channel actions. -/
@[expose] def DominantlyTruthful {n m d : ℕ} (M : Payment n m d) : Prop :=
  ∀ (T : Mat n n) (S : Mat m m) (U : Mat n m),
    ColumnStochastic T → ColumnStochastic S → Simplex U →
      expectedPayment M (T * bobReports S U) ≤ expectedPayment M (bobReports S U) ∧
      expectedPayment M (bobReports S (T * U)) ≤ expectedPayment M (T * U)

/-- A full-row-rank probability table witnessing sharpness in every non-tall
alphabet pair. Mass is distributed equally over distinct diagonal positions. -/
@[expose] def diagonalLaw {n m : ℕ} (hnm : n ≤ m) : Mat n m :=
  fun i a => if a = Fin.castLE hnm i then (n : ℝ)⁻¹ else 0

/-- The sharpness witness is a genuine probability law. -/
theorem diagonalLaw_simplex {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    Simplex (diagonalLaw hnm) := by
  constructor
  · intro i a
    simp only [diagonalLaw]
    split_ifs <;> positivity
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    simp [mass, diagonalLaw, hn']

/-- The Gram determinant is strictly positive at the sharpness witness. -/
theorem diagonalLaw_gramDet_pos {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) :
    0 < GramDependence.gramDet (diagonalLaw hnm) := by
  have hgram : Matrix.of (diagonalLaw hnm) * (Matrix.of (diagonalLaw hnm)).transpose =
      ((n : ℝ)⁻¹ ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, diagonalLaw,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp [pow_two]
    · have hcast : Fin.castLE hnm i ≠ Fin.castLE hnm j := by
        intro h
        exact hij (Fin.ext (congrArg (fun x : Fin m => x.val) h))
      simp [hij, Ne.symm hcast, pow_two]
  rw [GramDependence.gramDet, hgram, Matrix.det_smul, Matrix.det_one]
  positivity

/-- For square tables the Gram determinant is precisely squared DMI. -/
theorem gramDet_square {n : ℕ} (U : Mat n n) :
    GramDependence.gramDet U = Matrix.det (Matrix.of U) ^ 2 := by
  rw [GramDependence.gramDet, Matrix.det_mul, Matrix.det_transpose, pow_two]

/-- Squared DMI is unchanged by exchanging the agents. -/
theorem gramDet_swapAgents {n : ℕ} (U : Mat n n) :
    GramDependence.gramDet (swapAgents U) = GramDependence.gramDet U := by
  rw [gramDet_square, gramDet_square]
  exact congrArg (fun x : ℝ => x ^ 2) (Matrix.det_transpose (Matrix.of U))

/-- Every polynomial statistic on joint laws has an actual unbiased payment. -/
theorem exists_payment_of_polynomial {n m d : ℕ}
    (P : MvPolynomial (Fin n × Fin m) ℝ) (hd : P.totalDegree ≤ d) :
    ∃ M : Payment n m d, ∀ U, Simplex U →
      expectedPayment M U = WidePolynomial.peval P U := by
  obtain ⟨M, hM⟩ := Estimation.polynomial_unbiased P d hd
  exact ⟨M, fun U hU => hM _ ((simplex_iff_isProbability U).mp hU)⟩

/-- Theorem 6.2(ii), sufficiency: a genuine `2n`-task common payment gives
nontrivial expected rewards to both agents and is dominantly truthful against
all memoryless peer channels. The returned expectation is squared DMI. -/
theorem exists_optimal_square_payment {n : ℕ} (hn : 2 ≤ n) :
    ∃ M : Payment n n (2 * n), IndependenceZeroPayment M ∧
      DominantlyTruthful M ∧ NontrivialPayment M ∧
      ∀ U, Simplex U → expectedPayment M U = Matrix.det (Matrix.of U) ^ 2 := by
  obtain ⟨M, hM⟩ := exists_payment_of_polynomial (GramDependence.gramDetPoly n n)
    (le_of_eq (GramDependence.gramDetPoly_totalDegree (le_refl n)))
  have hexpect (U : Mat n n) (hU : Simplex U) :
      expectedPayment M U = GramDependence.gramDet U :=
    (hM U hU).trans (GramDependence.peval_gramDetPoly U)
  have hleft (T : Mat n n) (U : Mat n n) (hT : ColumnStochastic T) (hU : Simplex U) :
      expectedPayment M (T * U) ≤ expectedPayment M U := by
    rw [hexpect _ (stochastic_mul_simplex hT hU), hexpect U hU]
    exact GramDependence.gramDet_dpi T U hT hU
  refine ⟨M, ?_, ?_, ?_, fun U hU => (hexpect U hU).trans (gramDet_square U)⟩
  · intro x y hU
    rw [hexpect _ hU]
    exact GramDependence.gramDet_rko hn x y hU
  · intro T S U hT hS hU
    refine ⟨hleft T _ hT (bobReports_simplex hS hU), ?_⟩
    have hV := stochastic_mul_simplex hT hU
    rw [hexpect _ (bobReports_simplex hS hV), hexpect _ hV]
    change GramDependence.gramDet (swapAgents (S * swapAgents (T * U))) ≤ _
    rw [gramDet_swapAgents, ← gramDet_swapAgents (T * U)]
    exact GramDependence.gramDet_dpi S _ hS (swapAgents_simplex hV)
  · refine ⟨diagonalLaw (le_refl n), diagonalLaw_simplex (by omega) _, ?_⟩
    rw [hexpect _ (diagonalLaw_simplex (by omega) _)]
    exact (diagonalLaw_gramDet_pos (by omega) _).ne'

/-- Exchange report coordinates in a payment statistic. -/
@[expose] def swapPayment {n m d : ℕ} (M : Payment n m d) : Payment m n d :=
  fun v => M (fun t => ((v t).2, (v t).1))

/-- Exchanging reports and transposing the distribution preserve expected payment. -/
theorem expectedPayment_swapPayment {n m d : ℕ} (M : Payment n m d) (U : Mat m n) :
    expectedPayment (swapPayment M) U = expectedPayment M (swapAgents U) :=
  Estimation.expectation_comp_equiv (Equiv.prodComm (Fin m) (Fin n))
    (fun ia => U ia.2 ia.1) d M

/-- Independence-zero is preserved by exchanging the agents. -/
theorem swapPayment_independenceZero {n m d : ℕ} {M : Payment n m d}
    (h : IndependenceZeroPayment M) : IndependenceZeroPayment (swapPayment M) := by
  intro x y hU
  rw [expectedPayment_swapPayment]
  have heq : swapAgents (outer x y) = outer y x := by
    ext i a
    exact mul_comm _ _
  rw [heq]
  exact h y x (heq ▸ swapAgents_simplex hU)

/-- Theorem 6.2(i), both agents: unequal alphabets preclude nontrivial expected
payments to both agents. The two payments may be different signed statistics. -/
theorem unequal_alphabets_not_both_nontrivial {n m d : ℕ}
    (hn : 2 ≤ n) (hm : 2 ≤ m) (hne : n ≠ m)
    (MA MB : Payment n m d) (hA : TruthfulAlice MA)
    (hB : TruthfulAlice (swapPayment MB))
    (hIZA : IndependenceZeroPayment MA) (hIZB : IndependenceZeroPayment MB) :
    ¬(NontrivialPayment MA ∧ NontrivialPayment MB) := by
  rintro ⟨⟨U, hU, hMA⟩, ⟨V, hV, hMB⟩⟩
  rcases lt_or_gt_of_ne hne with hnm | hmn
  · apply hMB
    have hzero := larger_alphabet_payment_zero hn hnm (swapPayment MB) hB
      (swapPayment_independenceZero hIZB) (swapAgents_simplex hV)
    rw [expectedPayment_swapPayment] at hzero
    exact hzero
  · exact hMA (larger_alphabet_payment_zero hm hmn MA hA hIZA hU)

/-- A payment faithfully detects independence when its expected reward vanishes
exactly at the rank-one probability tables. -/
@[expose] def FaithfulPayment {n m d : ℕ} (M : Payment n m d) : Prop :=
  IndependenceFaithful (expectedPayment M)

/-- Every actual finite-task expected-payment functional has an ambient C¹ extension. -/
theorem expectedPayment_C1Extendable {n m d : ℕ} (M : Payment n m d) :
    C1Extendable (expectedPayment M) := by
  have heq : expectedPayment M = WidePolynomial.peval (paymentPolynomial M) := by
    funext U
    exact (eval_paymentPolynomial M U).symm
  rw [heq]
  exact ⟨Set.univ, isOpen_univ, fun _ _ => Set.mem_univ _,
    (AsymmetricPolynomial.peval_contDiff (paymentPolynomial M)).contDiffOn⟩

/-- Corollary 5.2, one-sided necessity: faithful finite-task payments can
process only a binary alphabet. -/
theorem faithful_payment_binary {n m d : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (M : Payment n m d) (hT : TruthfulAlice M) (hFaithful : FaithfulPayment M) : n = 2 :=
  (exists_C1Extendable_independenceFaithful_dpi_iff hn hm).mp
    ⟨expectedPayment M, expectedPayment_C1Extendable M, hT, hFaithful⟩

/-- A faithful payment is independence-zero in the rank-one/outer-product convention. -/
theorem FaithfulPayment.independenceZero {n m d : ℕ} {M : Payment n m d}
    (h : FaithfulPayment M) : IndependenceZeroPayment M := by
  intro x y hU
  apply (h _ hU).mpr
  have hle := rank_outer_le_one x y
  have hne := FrobeniusDependence.simplex_rank_ne_zero hU
  omega

/-- The binary Gram construction is an actual four-task faithful payment
for any size of the unprocessed alphabet. -/
theorem exists_four_task_faithful_payment {m : ℕ} (hm : 2 ≤ m) :
    ∃ M : Payment 2 m 4, TruthfulAlice M ∧ FaithfulPayment M := by
  obtain ⟨M, hM⟩ := exists_payment_of_polynomial (GramDependence.gramDetPoly 2 m)
    (by rw [GramDependence.gramDetPoly_totalDegree hm])
  have hexpect (U : Mat 2 m) (hU : Simplex U) :
      expectedPayment M U = GramDependence.gramDet U :=
    (hM U hU).trans (GramDependence.peval_gramDetPoly U)
  refine ⟨M, ?_, ?_⟩
  · intro T U hT hU
    rw [hexpect _ (stochastic_mul_simplex hT hU), hexpect U hU]
    exact GramDependence.gramDet_dpi T U hT hU
  · intro U hU
    rw [hexpect U hU]
    exact GramDependence.gramDet_eq_zero_iff_rank_eq_one U hU

/-- Corollary 5.2: finite-sample faithful left-DPI payments exist exactly for
a binary processed alphabet. -/
theorem exists_faithful_payment_iff {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ d, ∃ M : Payment n m d, TruthfulAlice M ∧ FaithfulPayment M) ↔ n = 2 := by
  constructor
  · rintro ⟨d, M, hT, hFaithful⟩
    exact faithful_payment_binary hn hm M hT hFaithful
  · intro h
    subst n
    obtain ⟨M, hM⟩ := exists_four_task_faithful_payment hm
    exact ⟨4, M, hM⟩

/-- Faithfulness is invariant under exchanging the two agents. -/
theorem swapPayment_faithful {n m d : ℕ} {M : Payment n m d}
    (h : FaithfulPayment M) : FaithfulPayment (swapPayment M) := by
  intro U hU
  rw [expectedPayment_swapPayment]
  have hrank : (Matrix.of (swapAgents U)).rank = (Matrix.of U).rank :=
    Matrix.rank_transpose (Matrix.of U)
  simpa only [hrank] using h (swapAgents U) (swapAgents_simplex hU)

/-- A faithful reward is nontrivial whenever a full-row-rank joint law exists. -/
theorem FaithfulPayment.nontrivial {n m d : ℕ} (hn : 2 ≤ n) (hnm : n ≤ m)
    {M : Payment n m d} (h : FaithfulPayment M) : NontrivialPayment M := by
  let U : Mat n m := diagonalLaw hnm
  have hU : Simplex U := diagonalLaw_simplex (by omega) hnm
  have hrank : (Matrix.of U).rank = n :=
    (GramDependence.gramDet_ne_zero_iff_rank_eq_height U).mp
      (diagonalLaw_gramDet_pos (by omega) hnm).ne'
  refine ⟨U, hU, fun hzero => ?_⟩
  have := (h U hU).mp hzero
  omega

/-- Corollary 5.2: four is the minimum sample count for faithful one-sided DPI,
with no restriction on the other alphabet beyond having at least two states. -/
theorem faithful_payment_sample_lower_bound {n m d : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (M : Payment n m d) (hT : TruthfulAlice M) (hFaithful : FaithfulPayment M) : 4 ≤ d := by
  have hn2 := faithful_payment_binary hn hm M hT hFaithful
  subst n
  have hNontrivial := hFaithful.nontrivial (by decide : 2 ≤ 2) hm
  by_cases hm2 : m = 2
  · subst m
    exact square_payment_task_lower_bound (by decide) M hT hFaithful.independenceZero hNontrivial
  · have hprops := paymentPolynomial_properties M hT hFaithful.independenceZero
    apply (WidePolynomial.wide_simplex_totalDegree_lower_bound (by decide) (by omega)
      (paymentPolynomial M) hprops.2.1 hprops.2.2 ?_).trans hprops.1
    obtain ⟨U, hU, hMU⟩ := hNontrivial
    exact ⟨U, hU, by simpa only [eval_paymentPolynomial] using hMU⟩

/-- Four actual tasks suffice for a two-sided faithful binary reward. -/
theorem exists_four_task_two_sided_faithful_payment :
    ∃ M : Payment 2 2 4,
      TruthfulAlice M ∧ TruthfulAlice (swapPayment M) ∧ FaithfulPayment M := by
  obtain ⟨M, hIZ, hDom, hNontrivial, hM⟩ := exists_optimal_square_payment (by decide : 2 ≤ 2)
  have hexpect (U : Mat 2 2) (hU : Simplex U) :
      expectedPayment M U = GramDependence.gramDet U :=
    (hM U hU).trans (gramDet_square U).symm
  refine ⟨M, ?_, ?_, ?_⟩
  · intro T U hT hU
    rw [hexpect _ (stochastic_mul_simplex hT hU), hexpect U hU]
    exact GramDependence.gramDet_dpi T U hT hU
  · intro S U hS hU
    rw [expectedPayment_swapPayment, expectedPayment_swapPayment,
      hexpect _ (swapAgents_simplex (stochastic_mul_simplex hS hU)),
      hexpect _ (swapAgents_simplex hU), gramDet_swapAgents, gramDet_swapAgents]
    exact GramDependence.gramDet_dpi S U hS hU
  · intro U hU
    rw [hexpect U hU]
    exact GramDependence.gramDet_eq_zero_iff_rank_eq_one U hU

/-- Corollary 5.2, two-sided version: faithful finite-sample DPI rewards exist
exactly when both alphabets are binary. -/
theorem exists_two_sided_faithful_payment_iff {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∃ d, ∃ M : Payment n m d,
      TruthfulAlice M ∧ TruthfulAlice (swapPayment M) ∧ FaithfulPayment M) ↔
      n = 2 ∧ m = 2 := by
  constructor
  · rintro ⟨d, M, hA, hB, hFaithful⟩
    exact ⟨faithful_payment_binary hn hm M hA hFaithful,
      faithful_payment_binary hm hn (swapPayment M) hB (swapPayment_faithful hFaithful)⟩
  · rintro ⟨rfl, rfl⟩
    obtain ⟨M, hM⟩ := exists_four_task_two_sided_faithful_payment
    exact ⟨4, M, hM⟩

end Cslib.FiniteSampleInformation
