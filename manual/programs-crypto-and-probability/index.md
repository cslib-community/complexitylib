# Probabilistic programs, cryptographic games, and privacy models

Complexitylib distinguishes an algorithm's syntax, its probability law, and its realization by a resource-bounded machine. The distinction is visible in the types: `OracleComp` and `ProbComp` are programs; `PMF` is an exact distribution; `IsPPTOn` and `IsOraclePPTOn` assert realization by one finite-control classical fair-coin machine. Security then quantifies over algorithms carrying the relevant realization certificate. Some finite cryptographic interfaces deliberately stay at the distributional or query-bounded level [complexitylib][complexitylib].

The survey baseline is `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. This section records inspected definitions and theorem statements, with deeper tracing of the HILL/GGM, GSW, chosen-message/CCA, and MPC endpoints. It does not report a new Lean build or a complete independent proof audit.

## Reading map

- [Programs, probability laws, and native realization](programs-and-realization.md): typed free programs, stateful oracles, sampling, cost bounds, and fair-coin machines.
- [Security games and primitive families](security-games-and-primitives.md): computational indistinguishability, hardness assumptions, generators/functions, encryption, authentication, signatures, and commitments.
- [Average-case heuristics and the Liu–Pass bridge](average-case-hardness.md): exact and approximate hardness, deterministic/PPT and eventual/infinitely-often variants, and polynomial-clock OWF equivalences.
- [Public-coin interactive reductions](interactive-reductions.md): message access, semantic and efficient security interfaces, sumcheck and GKR.
- [Homomorphic encryption](homomorphic-encryption.md): exact GSW parameters, native operations, circuit evaluation, leveled bootstrapping, and circular-security assumptions.
- [Protocols and privacy](protocols-and-privacy.md): Sigma protocols, random-oracle signatures, ideal permutations, zero knowledge, MPC, and upstream information-theoretic security.
- [Model map](../model-map.md): an index of semantic variants and their explanatory pages.

## Model families and ownership

| Family | Meaning of computation | Main resource or security convention | Representative endpoint |
|---|---|---|---|
| Typed free oracle programs | Well-founded adaptive query trees with dependent reply types | Explicit query/cost predicates; pure continuations have no intrinsic machine cost | Stateful interpretation and substitution laws |
| Finite sampling programs | `ProbComp = OracleComp unifSpec`, sampling `Fin (n+1)` | Exact finite uniform choices; no automatic fair-coin implementation | Sampling laws and quantitative game transformations |
| Native closed and open probabilistic programs | One finite-control fair-coin multitape machine realizes encoded laws | Strict polynomial time, unary security parameter; joint final oracle state preserved | Closed/open composition, adaptive iteration, clock normalization |
| Game specifications | Boolean PMFs and admissible adversary families | Exact advantage, negligible asymptotics, polynomial reduction loss | Uniform OWF–PRG equivalence and adaptive PRFs |
| Primitive security interfaces | Hardness, chosen-message, signing/tagging, commitment games | Stage/state/encoding restrictions vary and are explicit | Cramer–Shoup CCA2, Lamport one-time signatures, PRF MACs |
| Average-case heuristics | Uniform-input success events for Nat/ENat targets | Uniform strict PPT or deterministic polynomial time; eventual or infinitely-often hardness | Polynomial-threshold Liu–Pass equivalences |
| Public-coin interactive reductions | Fixed round shape, message oracles, shared oracle world | Semantic soundness; efficient extraction/simulation supplied separately | Sumcheck and GKR completeness/soundness |
| Homomorphic schemes | Bit encryption plus circuit evaluation | Fresh-input correctness, compact widths, native evaluation; LWE/circular assumptions separate | Leveled and full GSW-based endpoints |
| Sigma and ideal-oracle protocols | Three-message transcripts, explicit simulation/extraction, shared ideal oracles | Finite query security by default; native certificates separately added | Fiat–Shamir bounds, Luby–Rackoff, Even–Mansour |
| General zero knowledge | Native interactive verifier and simulator experiments | Uniform generable families versus arbitrary auxiliary-input families | OWF implies the library's generable ZK proof notion for NP |
| Synchronous MPC | Fixed typed message/oracle schedule, local views and joint output law | Perfect privacy for static coalitions; native joint runner at the efficient endpoint | Proper-coalition OT1-of-4 completeness |
| Upstream information-theoretic schemes | PMF encryption/commitment/sharing interfaces | Perfect/statistical distribution equality; no native-time claim | One-time-pad secrecy and Shamir secret sharing |

Circuit-bounded PRG tests are a different admissibility model from uniform PPT and belong in the [circuits section](../circuits-logic-and-other-models/index.md); the relevant interface is [IsCircuitTest](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Primitives/PRG/Circuit.lean#L74). Randomized Word-RAM's unit-cost finite uniform instruction belongs in [algorithms and memory](../algorithms-and-memory/index.md). The underlying parametric Turing machines and complexity classes belong in [machines and classes](../machines-and-classes/index.md).

## Design rationale

The common free-program layer permits the same syntax to be interpreted in independent probability, stateful probability, or another program language. Exact equality with an encoded machine run is then a separate bridge. **Inference:** this supports readable probability proofs while making machine efficiency an additional mathematical obligation, rather than a syntactic promise. It also permits ideal distributions that cannot be exactly sampled in a fixed finite fair-coin budget.

Uniformity is load-bearing. The native witnesses are chosen before all inputs, and a security adversary is chosen before the asymptotic security parameter. Auxiliary strings and public descriptions are encoded inputs. The higher-level APIs generally do not identify circuit families, freely supplied advice, and uniform Turing algorithms.

The formal contracts distinguish strict versus expected running time; exact uniform group laws versus approximate fair-coin samplers; fixed versus adaptive query selection; full versus proper MPC coalitions; and generable versus unrestricted auxiliary-input zero knowledge. These are properties of the formal statements, not incidental caveats.

## Coverage and evidence

The model map groups protocol constructions by their computational/security interface, rather than treating every named cipher as a new computational model. Sources covered include `Languages/Probabilistic`, `Computability/Probabilistic`, `Crypto/Game`, `Crypto/Computational`, `Crypto/Protocols`, and pinned cslib's cryptographic interfaces. The mathematical probability library supplies PMFs, couplings, distances, and concentration; these are semantic foundations, not additional execution machines.

A lexical search of local library, abstracts, and pinned cslib found no differential-privacy predicate or mechanism under `differential`, `differentially private`, `Renyi`, or the standard Laplace/Gaussian mechanism names. Thus this reference makes **no claim of differential-privacy support**. This is a documented search result, not a proof that no differently named equivalent definition exists.

Existing tests include [ComplexityTests/ProbabilisticComposition.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ProbabilisticComposition.lean), [ComplexityTests/ComputationalCrypto.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ComputationalCrypto.lean), [ComplexityTests/Crypto/AssumptionNonvacuity.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/AssumptionNonvacuity.lean), [ComplexityTests/Crypto/GSWFullyHomomorphic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/GSWFullyHomomorphic.lean), and [ComplexityTests/Crypto/MPC.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/MPC.lean). Their presence is source evidence; they were not rerun by this author.

## Source-review scope

The November 1–2 source review consulted Holenstein's definitions and construction overview,
GGM's adaptive function-testing definition, Liu–Pass's Definitions 2.4–2.5 and Theorem 3.1,
and Thaler's Section 4.6/Lemma 4.7. HILL and GSW checks were limited to abstracts or metadata;
Gentry, Boneh–Shoup, BCS, LFKN and the GKR version of record were not fully accessed.
Goldreich's chapter listing was checked, not the full published chapter. These limitations
remain relevant when reading the source-to-Lean comparisons in the detailed pages.

The six directly cited CSLib dependency files were byte-identical to independently retrieved
pinned blobs despite the live dependency-checkout drift. The chapters link those pinned
sources directly; copied files and generated audit reports are not maintained inputs.

## Adaptive policies and finite stochastic experiments

The work associated with STOC submissions 587, 191 and 152 includes the general
finite-horizon covariance identity and the bounded results below. The expanded
headline programme remains open in [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).
The information and auditing sample-complexity bounds, scheduling LP/FPTAS and
DPI rigidity theorems are not provided by these imports. There is no machine-runtime
or full-paper completion claim. The source
versions and PDF digests are recorded under `Aldridge2027`, `Wang2027` and `Kong2027`
in [the bibliography](../../references.bib). The checked clients are in
[Stoc2027BatchC.lean](../../ComplexityTests/Stoc2027BatchC.lean).

- [AdaptivePolicy.Covariance](../../Complexity/Probability/AdaptivePolicy/Covariance.lean)
  proves STOC submission 587, Lemma 3.3 and Theorem 3.4 (PDF p. 3), for every finite
  state/action space, finite horizon and randomized Markov policy. `FiniteMDP`
  supplies a normalized nonnegative initial law and controlled transition kernels,
  with arbitrary real costs; `MarkovPolicy` supplies conditional action probabilities.
  `stateLaw` propagates the evaluated policy through its own action-dependent dynamics.
  `value` and `actionValue` evaluate the comparison policy backward with zero terminal
  cost. `openLoop` uses the evaluated policy's action marginals at each time, then runs
  under its own trajectory law. Apply `performance_difference`,
  `covariance_characterization` or `joint_product_characterization` without proving
  a Bellman equation or an identity as a hypothesis. `traceCovariance_sub_state`
  permits any state-only baseline. Time indices start at zero and `totalCost π H`
  includes exactly the times in `Finset.range H`, including an empty horizon.
  [AdaptivePolicyCovariance.lean](../../ComplexityTests/AdaptivePolicyCovariance.lean)
  constructs the actual two-step investment MDP, independently calculates both
  trajectory costs and recovers their difference using the general theorem.
- [AdaptivePolicy.Information](../../Complexity/Probability/AdaptivePolicy/Information.lean)
  proves STOC submission 587, Theorem 4.2 (PDF p. 4). `jointLaw` is the actual
  state/action law and `productLaw` uses its original marginals. `mutualInformation`
  is their finite KL sum in **nats**, with support inclusion proved from the policy.
  `actionSpan` is the largest supported within-state action range: state-only offsets
  and impossible actions do not enlarge it. `information_bound` works for arbitrary
  real costs and endogenous transitions. For score bounds, use `actionSpan_le`;
  `sub_le_actionSpan` supplies the reverse inequality from a supported witness.
  The proof reuses the library's Pinsker inequality and bounded-score change-of-law API.
- [AdaptivePolicy.Sharpness](../../Complexity/Probability/AdaptivePolicy/Sharpness.lean)
  proves Proposition 4.3 (PDF p. 4). `sharpness_family` constructs the uniform binary
  mismatch-cost experiment with matching probability $(1+\epsilon)/2$, for every
  $0<\epsilon<1$. Its supported span is one, its absolute adaptivity cost is
  $\epsilon/2$, and its actual mutual information is `information ε`.
  `information_tendsto_zero` and `sharp_ratio` prove the vanishing-information and
  limiting-ratio claims by differentiation. This establishes optimality of the
  $1/\sqrt2$ coefficient in nats, rather than merely checking selected parameters.
- [AdaptivePolicy.Regret](../../Complexity/Probability/AdaptivePolicy/Regret.lean)
  proves Corollaries 3.6–3.7 and 4.4–4.5 (PDF pp. 3–4). `IsOptimal` compares actual
  total costs against every Markov policy; `IsOptimalOpenLoop` compares against every
  state-independent randomized policy. The three-part regret decomposition has
  nonnegative static allocation and adaptivity-gap terms. `optimal_gap_le_information`
  applies in particular to every optimizer, and `optimal_gap_eq_zero` uses its
  optimality to prove equality. Under unit costs, `rate_value_tradeoff` accepts
  individual information budgets; `constant_rate_value_tradeoff` gives exactly
  $H(H+1)\sqrt{R/2}/2$. These theorems quantify over optimizers; they do not construct
  an optimal-policy algorithm. `exogenous_covariance_characterization` justifies
  immediate-cost auditing when the supplied transitions are action independent.
- [AdaptivePolicy.Pathwise](../../Complexity/Probability/AdaptivePolicy/Pathwise.lean)
  proves Theorem 3.1 and Corollary 3.2 (PDF p. 3). The path index is any nonempty
  finite type, costs are arbitrary real vectors, and actions lie in a compact convex
  feasible set. `pathwise_decomposition` constructs an attained best fixed comparator,
  with the unnormalized sample covariance and nonnegative static gap.
  `pathwise_covariance_le_regret` gives the inequality and characterizes equality by
  global optimality of the empirical mean action. No stochastic model is assumed.
  [AdaptivePolicyInformation.lean](../../ComplexityTests/AdaptivePolicyInformation.lean)
  checks a negative-regret path, zero and nonzero information channels, and a supported
  span that ignores an impossible action with cost one million.
- [AdaptivePolicy.Nonidentifiability](../../Complexity/Probability/AdaptivePolicy/Nonidentifiability.lean)
  proves the finite-context case of STOC submission 587, Proposition 5.2 (PDF p. 5).
  `finite_nonidentifiability` takes a context set of positive initial probability and
  an action with positive marginal probability that is never played on that set.
  It constructs two deterministic binary loss tables with identical complete logged
  data laws for every sample count but different policy-minus-open-loop costs.
  `logLaw` is nonnegative and normalized; `sampleLaw` is the i.i.d. product, including
  the empty log. Logged propensities are functions of the recorded context, so adding
  them does not distinguish the instances. The checked client exhibits a gap change
  of $-1/4$. For arbitrary measurable context spaces, use the following module.
- [AdaptivePolicy.MeasurableNonidentifiability](../../Complexity/Probability/AdaptivePolicy/MeasurableNonidentifiability.lean)
  proves Proposition 5.2 (PDF p. 5) for arbitrary measurable contexts. Start with a
  probability context law `D` and Markov kernel `π`; `kernel_nonidentifiability`
  assumes a measurable positive-mass context set on which a positive-marginal action
  has probability zero. It constructs two measurable binary loss functions, proves
  equality of complete i.i.d. log laws for every sample count, and computes their
  nonzero adaptivity-cost difference. `measurableGap_eq_integral` identifies that gap
  with expected costs. `deterministic_nonidentifiability` covers every finite-action
  measurable deterministic policy that is not almost surely constant. The checked
  client uses a Gaussian/binary product context, so the API is exercised beyond
  finite context types. Logged propensities, as deterministic functions of context,
  cannot distinguish the equal log laws.
- [AdaptivePolicy.ContextualAudit](../../Complexity/Probability/AdaptivePolicy/ContextualAudit.lean)
  supplies Theorem 5.3 (PDF p. 5). Start with a probability law on a measurable
  context and a bounded potential-cost vector. The action probabilities depend only
  on context. `banditObservation` retains the context, propensities, selected action
  and its loss; `banditScore` reads only that record. `contextual_auditor_finite_divergence`
  derives overlap and square integrability from finite `averagePearson`, the extended
  average conditional chi-squared divergence. The context-marginal bridge proves that
  this parameter and the target frequencies do not depend on the potential costs.
  `contextual_auditor_ceiling` uses exactly $m=\lceil4\bar\chi^2/\delta^2\rceil$
  samples in each of $k=\lceil8\log(1/\eta)\rceil$ independent blocks for positive
  divergence, $\delta>0$ and $0<\eta<1$. The failure event is $|\widehat\Delta-\Delta|\ge\delta$.
  At zero divergence, `contextual_gap_eq_zero` makes output zero exact with no samples;
  the library explicitly totalizes empty block means to zero. Target marginal
  frequencies are known, as in Remark 5.1; estimating them is not part of the guarantee.
- [AdaptivePolicy.AuditLowerBound](../../Complexity/Probability/AdaptivePolicy/AuditLowerBound.lean)
  supplies Theorem 5.4 (PDF p. 5). `auditing_lower_bound` constructs a binary policy
  with exactly the prescribed $\Gamma\ge1/3$ and two actual bounded Bernoulli-cost
  instances. Their complete logged-data laws are `hardLaw`, with independent repeated
  samples. `hardMass_observation` verifies the potential-cost experiment and conditional
  independence before action selection. Every randomized auditor is a Markov kernel
  from all observed logs to a real estimate. Accuracy on both instances forces
  $T\ge9(\Gamma+1)\log(1/(4\eta))/(2048\delta^2)$ for $0<\delta\le1/32$ and
  $0<\eta\le1/8$. Logged propensities are deterministic functions of the retained
  context. The proof derives single-log KL, product additivity and the testing bound;
  no lower-bound or concentration premise is bundled into an instance.
- [AdaptivePolicy.EpisodicAudit](../../Complexity/Probability/AdaptivePolicy/EpisodicAudit.lean)
  supplies Theorem 5.5 (PDF pp. 5–6). `episodeLaw` follows the actual finite MDP
  transitions. `episodeLoss_integral` connects its total trajectory cost to `totalCost`;
  `episodeLaw_change` proves cancellation of transition factors in the likelihood
  ratio. Overlap is needed only at times below the horizon and behavior-supported
  states. Costs are in $[0,1]$ only during that horizon. `episodic_auditor_moments`
  proves unbiasedness and the $H^2\chi^2$ variance bound.
  `trajectoryChiSquared_product_bound` bounds $1+\chi^2$ by the product of
  $1+\texttt{maxStepChi}$ over times, taking each maximum only over supported states.
  `episodic_observed_auditor` applies to the actual observable episode records;
  the extra terminal state in the proof representation is discarded, and the score
  uses only recorded costs and propensities. `episodic_auditor_ceiling` gives the exact
  episode count with $H^2\chi^2$ in place of $\bar\chi^2$; `episodic_gap_eq_zero`
  handles the zero parameter, including horizon zero. Episodes are independent;
  successive time steps within an episode need not be independent.
  [AdaptivePolicyAuditing.lean](../../ComplexityTests/AdaptivePolicyAuditing.lean)
  checks outliers, even and empty blocks, a positive-divergence integer-sample
  auditor, a Gaussian context, binary hard-instance endpoints and actual two-step
  trajectories. The shared concentration, importance-sampling and testing proofs
  live in `Probability/MedianOfMeans`, `ImportanceSampling`, `Testing` and
  `ProductDivergence`. These are sample-complexity guarantees for mathematical
  estimators, with no certified machine runtime or empirical numerical claim.
- [AdaptivePolicy.SignReversal](../../Complexity/Probability/AdaptivePolicy/SignReversal.lean)
  realizes Aldridge's Proposition 3.8 (PDF p. 4) with Boolean states and actions. The
  initial state is uniform, investment costs $a(1+s)$, the transition is $s'=s\land a$,
  and the terminal cost is $-ms'$. `sign_reversal` gives myopic covariance $1/4$ and
  actual policy-minus-open-loop cost $(1-m)/4<0$ for every real $m>1$. The second
  action has no effect. Retaining only $s\land a$ preserves the two-state claim;
  the paper's stored pair contains redundant information.
- [StochasticOracle.FullCover](../../Complexity/Probability/StochasticOracle/FullCover.lean)
  implements Wang's Theorem 1 (PDF pp. 6–7) for failure-oblivious full-cover
  selection. `FullCoverInstance` has finitely many labeled call opportunities,
  strictly positive probabilities below one, positive expected token costs and
  positive cutoffs. Failures reveal only that no accepted cover was obtained;
  future batch laws are failure invariant, with independent call successes.
  A `Policy` can randomize before or after failed batches and remember its private
  choices. `execution` records the actual stopped trace, while `scheduleLaw`
  simulates the all-failure choices without querying an oracle.
  `cost_success_frontier` equates both coordinates with the finite LP;
  `target_feasible_iff_schedule` includes infeasibility, and `optimal_two_schedules`
  constructs an attained optimum with at most two positive schedule weights.
  `maximum_success_support` characterizes maximum success by using every call,
  and `deterministic_max_success` rules out an improvement from randomization at
  that endpoint. `one_batch_values` and `two_batch_values` give the exact costs.
  `Plan` has a parametric number of padded slots: empty batches issue no calls;
  erase them to obtain the paper's nonempty batch sequences. `Plan.Feasible`
  requires no reuse and bounds the sum of maximum batch cutoffs, excluding local
  computation. [ExecutionFeasibility](../../Complexity/Probability/StochasticOracle/ExecutionFeasibility.lean)
  proves this contract for every supported stopped execution.
  [RationalFullCover](../../Complexity/Probability/StochasticOracle/RationalFullCover.lean)
  supplies `optimal_rational_program`: all numerical inputs are rational but
  competitors may randomize with arbitrary real probabilities. The optimum has
  an exact finite-uniform `ProbComp` sampler and `ProbOracleComp` execution whose
  law is proved in [Programs](../../Complexity/Probability/StochasticOracle/Programs.lean).
  This certifies exact sampling, without a strict worst-case fair-coin time bound.
  [RandomCost](../../Complexity/Probability/StochasticOracle/RandomCost.lean)'s
  `billed_cost_eq` covers arbitrary probability spaces and integrable random bills,
  including correlation with the current batch's success. Its assumptions are the
  stopped-trace law and conditional expected costs per selected batch and slot;
  it derives the total expected cost. Import `RationalFullCover`,
  `ExecutionFeasibility` and `RandomCost`, and check the complete
  [StochasticOracleFullCover.lean](../../ComplexityTests/StochasticOracleFullCover.lean)
  client: heterogeneous deadlines, internal randomization after failure, a mixed
  optimum, exact non-dyadic sampling, zero/one endpoints, zero turns and
  success-correlated bills. The rational optimizer uses the generic
  [one-constraint LP](../../Complexity/Foundations/Optimization/OneConstraint.lean)
  support reduction and finite vertex enumeration; its schedule set can be
  exponential. The binary-input FPTAS, hardness, partial-cover and adaptive
  endpoints remain open under [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).
- [Submodular.OracleSavings](../../Complexity/Algorithms/Lean/Submodular/OracleSavings.lean)
  proves Wang's Theorem 2(1) (PDF p. 7). A finite type indexes all oracles;
  `savings p c A` is exactly $(1-\prod_{i\in A}(1-p_i))\sum_{i\notin A}c_i$.
  Use `savings_nonneg` and `savings_isSubmodular` with pointwise $0\le p_i\le1$
  and $c_i\ge0$. Submodularity reuses the library's `IsSubmodular`; savings need
  not be monotone (the test has singleton saving one and full-set saving zero).
  The scheduling theorem is supplied by `StochasticOracle`; the FPTAS remains open.
- [PeerPrediction.Quadratic](../../Complexity/Probability/PeerPrediction/Quadratic.lean)
  implements Kong's equation (8), Lemma 7.2 and Theorem 7.3 (PDF pp. 18–19).
  `IsJoint` means a nonnegative finite probability table of total mass one;
  `reportedLaw` sums conditional reporting probabilities over latent signals.
  `expectFour` uses four independent draws from the same report law. `payment_unbiased`
  identifies the equality-only payment's expectation with QMI, and `truthful_reward`
  characterizes independence. `truthful_alice` and `truthful_bob` allow an arbitrary
  fixed memoryless peer channel; own deviations must have the stated form
  $T=\lambda D+(1-\lambda)q\mathbf1^T$, with $D$ doubly stochastic and
  $0\le\lambda\le1$. `centered_mixed` and `qmi_mixed_le` prove Proposition 7.1's
  identity and contraction. There is no full-support or equal-alphabet assumption.
  This construction covers restricted own channels; it makes no general-channel
  QMI or history-dependent-strategy claim. The rigidity APIs are described next.
- [FiniteSampleInformation.Rigidity](../../Complexity/Probability/FiniteSampleInformation/Rigidity.lean)
  is the entry point for Kong's finite-sample information limits (STOC submission 152).
  Import it for the sharp polynomial/sample bounds and actual finite-task payments;
  import [DimensionChanging](../../Complexity/Probability/FiniteSampleInformation/DimensionChanging.lean)
  alone for alphabet-changing collapse. The
  [checked clients](../../ComplexityTests/FiniteSampleInformation/Main.lean) include a
  dependent zero-row law, nonzero rectangular Gram law, an impossible five-task
  three-symbol reward, and an attaining eight-task four-symbol mechanism.

  `GeneralAsymmetricC1.Mat n m` is the iterated function space
  `Fin n → Fin m → ℝ`, so calculus uses its finite-product norm. `Simplex U`
  means entrywise nonnegativity and total mass one. A `ColumnStochastic T`
  has nonnegative entries and column sums one, and Alice's channel acts by
  left multiplication. `swapAgents` transposes a law; `bobReports S U` applies
  Bob's channel by right multiplication with its transpose. The
  [QMI bridges](../../Complexity/Probability/FiniteSampleInformation/QuadraticBridge.lean)
  identify these tables and channels with the existing four-task API.

  For a smooth functional, use `zero_row_vanishing_openNeighborhood` or
  `general_asymmetric_simplex_C1_openNeighborhood` from `GeneralAsymmetricC1`.
  Supply an **open ambient neighborhood of the entire closed simplex** and a
  `ContDiffOn ℝ 1` extension there, in addition to left DPI and rank-one vanishing.
  Interior smoothness does not meet the hypotheses. With more rows than columns,
  the functional vanishes everywhere. The zero-row theorem also covers square
  and wide alphabets. `dimensionChanging_collapse` applies to a family whose
  rectangular-channel DPI and boundary regularity hold for every alphabet size
  at least two; its channels adding and retracting an unused state are proved
  stochastic.

  For polynomials, `determinantal_rigidity` proves membership in the square of
  the maximal-minor ideal modulo total mass minus one, and
  `polynomial_degree_lower_bound` gives degree at least $2n$ for a functional
  nonzero on the simplex. The Gram determinant attains this bound for every
  $2\le n\le m$; `gramDetPoly_nonzero_on_simplex` supplies a normalized witness.
  `SquarePolynomial.square_simplex_det_sq` gives the square-case factorization.
  The general generic-minor algebra is in
  [Foundations/Algebra/Polynomial/MaximalMinor](../../Complexity/Foundations/Algebra/Polynomial/MaximalMinor/MaximalMinorWeight.lean).
  The analytic and algebraic proofs port Yuqing Kong's Apache-2.0 author
  formalization at `4e27ef9d167be69902385307d40123ec665dc532`, with original
  authorship and port credit preserved.

  `Estimation.unbiased_iff_polynomialOnSimplex` is the fixed-sample characterization:
  a signed statistic on `Fin d → α` estimates a functional for every probability
  vector exactly when the functional has a degree-at-most-$d$ representative
  on the simplex. It permits zero probabilities and unused samples.
  `expectedPayment_eq_sum` gives the actual product-law payment expectation;
  `memoryless_payoff_eq` identifies it with first drawing the latent signal
  vector and then independently randomizing each agent’s report on each task.
  `square_payment_task_lower_bound` applies to any actual finite-task statistic;
  `exists_optimal_square_payment` returns a common $2n$-task payment for both
  agents with dominant truthfulness against all fixed memoryless peer channels.
  `unequal_alphabets_not_both_nontrivial` permits distinct signed payments to
  the two agents. `exists_faithful_payment_iff`,
  `faithful_payment_sample_lower_bound` and
  `exists_two_sided_faithful_payment_iff` give the binary/four-sample
  classifications. These results concern the same independently applied channel
  on each task, not arbitrary strategies using the whole signal vector.

  The port also includes Appendix B's compensation construction and Appendix D's
  semantic copositivity equivalence. The latter does **not** certify polynomial-time
  arithmetic-circuit construction or coNP-hardness. Appendix C's unnormalized
  consequences are outside the main-result API described here.

## Known Limitations

Primary-source verification was selective. HILL/Holenstein/GGM and selected RAM/algorithm sources were consulted; textbook locator claims and most construction proofs remain code-grounded rather than independently reconciled line by line with the literature. The section intentionally does not infer autonomous-development percentages from theorem counts or test files.

[complexitylib]: ../sources.md#complexitylib
