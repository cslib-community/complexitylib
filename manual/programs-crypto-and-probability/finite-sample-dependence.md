# Finite-sample dependence measures and multi-task peer prediction

This page covers Kong's limits for dependence measures that satisfy the data processing
inequality (DPI) and admit an unbiased estimator from finitely many samples (STOC submission 152,
`[Kong2027]` in the bibliography; [source record](../sources.md#kong27)). It also covers their
consequences for multi-task peer prediction. The analytic and determinantal proofs port Yuqing
Kong's Apache-2.0 author formalization at
[`4e27ef9d`](https://github.com/yuqkong-1844/finite-sample-information-monotones/tree/4e27ef9d167be69902385307d40123ec665dc532),
with original authorship and port credit kept in each module header and in `NOTICE`. The
estimation, dimension-changing, payment and QMI bridges are local proofs.

## Setting

A joint law of two finite random variables is an `n × m` table `U` with nonnegative entries and
total mass one. Rows index the variable being processed. A functional `F` satisfies left
fixed-alphabet DPI when `F (T U) ≤ F U` for every column-stochastic `n × n` channel `T`, and is
independence-zero when it vanishes on rank-one (independent) laws.

In Lean, `GeneralAsymmetricC1.Mat n m` is the iterated function space `Fin n → Fin m → ℝ`, so
calculus uses its finite-product norm. `Simplex U` means entrywise nonnegativity and total mass
one. A `ColumnStochastic T` has nonnegative entries and column sums one, and acts by left
multiplication. `swapAgents` transposes a law; `bobReports S U` applies Bob's channel by right
multiplication with its transpose.

## Choosing an entry point

Import [FiniteSampleInformation.Rigidity](../../CslibFrontier/Probability/FiniteSampleInformation/Rigidity.lean)
for the polynomial, sample and task bounds. Import
[DimensionChanging](../../CslibFrontier/Probability/FiniteSampleInformation/DimensionChanging.lean)
alone for alphabet-changing collapse, and
[PeerPrediction.Quadratic](../../CslibFrontier/Probability/PeerPrediction/Quadratic.lean) for the
four-task QMI payment. The [checked clients](../../CslibFrontierTests/FiniteSampleInformation/Main.lean)
include a dependent zero-row law, a nonzero rectangular Gram law, an impossible five-task
three-symbol reward and an attaining eight-task four-symbol mechanism. The
[QMI clients](../../CslibFrontierTests/FiniteSampleInformation/QuadraticPayment.lean) check
correlated, independent and unequal-alphabet tables.

## Smooth functionals (Theorem A, Theorems 3.3 and 3.5)

Use `zero_row_vanishing_openNeighborhood` or `general_asymmetric_simplex_C1_openNeighborhood`
from `GeneralAsymmetricC1`. Supply an **open ambient neighborhood of the entire closed simplex**
and a `ContDiffOn ℝ 1` extension there, together with left DPI and rank-one vanishing. Interior
smoothness does not meet these hypotheses: Shannon mutual information escapes the theorem
through its boundary behavior. The zero-row theorem covers every `n ≥ 2`; with more rows than
columns the functional vanishes everywhere.

`dimensionChanging_collapse` (Corollary 5.3) applies to a family whose rectangular-channel DPI
and boundary regularity hold for every alphabet size at least two. The channels adding and
retracting an unused state are proved stochastic; the family is not assumed expansible.

## Polynomials (Theorem B, Theorem 4.1, Proposition 4.4, Corollary 4.5)

`determinantal_rigidity` proves membership in the square of the maximal-minor ideal modulo total
mass minus one, for `2 ≤ n ≤ m`. `polynomial_degree_lower_bound` gives degree at least `2n` for
a functional nonzero somewhere on the simplex. The Gram determinant `det (U Uᵀ)` attains the bound
for every `2 ≤ n ≤ m`, and `gramDetPoly_nonzero_on_simplex` supplies a normalized witness.
`SquarePolynomial.square_simplex_det_sq` gives the square-case factorization `F = (det U)² G`
on the simplex, and `asymmetric_polynomial_mem_simplex_ideal` is the tall-case Corollary 3.6.
The primaryness and cancellation used in the proof are proved in
[Foundations/Algebra/Polynomial/MaximalMinor](../../CslibFrontier/Foundations/Algebra/Polynomial/MaximalMinor/MaximalMinorWeight.lean),
not supplied as hypotheses.

## Samples and tasks (Proposition 2.4, Corollary 5.2, Lemma 6.1, Theorem 6.2)

`Estimation.unbiased_iff_polynomialOnSimplex` is the fixed-sample characterization: a signed
statistic on `Fin d → α` estimates a functional for every probability vector exactly when the
functional has a representative of degree at most `d` on the simplex. Zero probabilities and
unused samples are allowed.

A `Payment n m d` is a signed statistic of `d` report pairs. `expectedPayment_eq_sum` gives its
product-law expectation, and `memoryless_payoff_eq` identifies that with first drawing the
latent signals and then independently randomizing each agent's report on each task.
`square_payment_task_lower_bound` applies to any finite-task statistic, and
`exists_optimal_square_payment` returns a common `2n`-task payment for both agents with dominant
truthfulness against all fixed memoryless peer channels. `larger_alphabet_payment_zero` and
`unequal_alphabets_not_both_nontrivial` allow distinct signed payments to the two agents.
`exists_faithful_payment_iff`, `faithful_payment_sample_lower_bound` and
`exists_two_sided_faithful_payment_iff` give the binary/four-sample classifications. These results
concern the same channel applied independently on each task, not strategies that use the whole
signal vector.

## Restricted four-task QMI payment (Section 7)

`PeerPrediction.Quadratic` implements equation (8), Lemma 7.2 and Theorem 7.3. `IsJoint` means a
nonnegative finite probability table of total mass one; `reportedLaw` sums conditional reporting
probabilities over latent signals. `expectFour` uses four independent draws from the same report
law. `payment_unbiased` identifies the equality-only payment's expectation with QMI, and
`truthful_reward` characterizes independence. `truthful_alice` and `truthful_bob` allow an
arbitrary fixed memoryless peer channel; own deviations must have the form
$T=\lambda D+(1-\lambda)q\mathbf1^T$, with $D$ doubly stochastic and $0\le\lambda\le1$.
`centered_mixed` and `qmi_mixed_le` prove Proposition 7.1. There is no full-support or
equal-alphabet assumption. `FrobeniusDependence.fdi_not_full_dpi` shows with a `4 × 3` table
that QMI violates unrestricted DPI; it is not the paper's `3 × 2` example in Section 7.3. The
[QMI bridges](../../CslibFrontier/Probability/FiniteSampleInformation/QuadraticBridge.lean)
identify the two table and channel conventions.

## Limits

Appendix B's constant compensation (`exists_constantCompensation_dpi`) is ported. Appendix D's
copositivity reduction is ported only as a semantic equivalence
(`rationalRecognitionPoly_dpi_iff_copositive`); polynomial-time arithmetic-circuit construction
and coNP-hardness are not established here. Appendix C's unnormalized extensions
(Propositions C.1–C.2) and the remark that a minimum-degree square-case functional is a positive
multiple of `(det U)²` are open; issue
[2527](https://github.com/cslib-community/cslib-frontier/issues/2527) tracks them.
