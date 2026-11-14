# Probabilistic programs, cryptographic games, and privacy models

cslib-frontier distinguishes an algorithm's syntax, its probability law, and its realization by a resource-bounded machine. The distinction is visible in the types: `OracleComp` and `ProbComp` are programs; `PMF` is an exact distribution; `IsPPTOn` and `IsOraclePPTOn` assert realization by one finite-control classical fair-coin machine. Security then quantifies over algorithms carrying the relevant realization certificate. Some finite cryptographic interfaces deliberately stay at the distributional or query-bounded level [cslib-frontier][complexitylib].

The survey baseline is `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. This section records inspected definitions and theorem statements, with deeper tracing of the HILL/GGM, GSW, chosen-message/CCA, and MPC endpoints. It does not report a new Lean build or a complete independent proof audit.

## Reading map

- [Programs, probability laws, and native realization](programs-and-realization.md): typed free programs, stateful oracles, sampling, cost bounds, and fair-coin machines.
- [Security games and primitive families](security-games-and-primitives.md): computational indistinguishability, hardness assumptions, generators/functions, encryption, authentication, signatures, commitments, and garbling schemes.
- [Average-case heuristics and the Liu–Pass bridge](average-case-hardness.md): exact and approximate hardness, deterministic/PPT and eventual/infinitely-often variants, and polynomial-clock OWF equivalences.
- [Distributional problems, AvgP, HeurP and Levin reductions](distributional-complexity.md): length-indexed ensembles, computable and samplable ensembles, errorless and heuristic schemes, dominating reductions and their closure properties.
- [Public-coin interactive reductions](interactive-reductions.md): message access, semantic and efficient security interfaces, sumcheck and GKR.
- [Homomorphic encryption](homomorphic-encryption.md): exact GSW parameters, native operations, circuit evaluation, leveled bootstrapping, and circular-security assumptions.
- [Protocols and privacy](protocols-and-privacy.md): Sigma protocols, random-oracle signatures, ideal permutations, zero knowledge, MPC, upstream information-theoretic security, and differential privacy.
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
| Differentially private mechanisms | Dataset-indexed output PMFs; finite `ProbComp` programs or ideal noise laws | `(ε, δ)` event bounds for an explicit adjacency relation; no sampling-cost or native-time claim | Randomized response is exactly `ln 3`-private; adaptive composition |

Circuit-bounded PRG tests are a different admissibility model from uniform PPT and belong in the [circuits section](../circuits-logic-and-other-models/index.md); the relevant interface is [IsCircuitTest](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Primitives/PRG/Circuit.lean#L74). Read-once branching-program tests (`IsReadOnceTest`, used for Nisan's generator) are described with the [read-once programs](../circuits-logic-and-other-models/networks-and-iteration.md#deterministic-read-once-programs-and-nisans-generator). Randomized Word-RAM's unit-cost finite uniform instruction belongs in [algorithms and memory](../algorithms-and-memory/index.md). The underlying parametric Turing machines and complexity classes belong in [machines and classes](../machines-and-classes/index.md).

## Design rationale

The common free-program layer permits the same syntax to be interpreted in independent probability, stateful probability, or another program language. Exact equality with an encoded machine run is then a separate bridge. **Inference:** this supports readable probability proofs while making machine efficiency an additional mathematical obligation, rather than a syntactic promise. It also permits ideal distributions that cannot be exactly sampled in a fixed finite fair-coin budget.

Uniformity is load-bearing. The native witnesses are chosen before all inputs, and a security adversary is chosen before the asymptotic security parameter. Auxiliary strings and public descriptions are encoded inputs. The higher-level APIs generally do not identify circuit families, freely supplied advice, and uniform Turing algorithms.

The formal contracts distinguish strict versus expected running time; exact uniform group laws versus approximate fair-coin samplers; fixed versus adaptive query selection; full versus proper MPC coalitions; and generable versus unrestricted auxiliary-input zero knowledge. These are properties of the formal statements, not incidental caveats.

## Coverage and evidence

The model map groups protocol constructions by their computational/security interface, rather than treating every named cipher as a new computational model. Sources covered include `Languages/Probabilistic`, `Computability/Probabilistic`, `Crypto/Game`, `Crypto/Computational`, `Crypto/Protocols`, and pinned cslib's cryptographic interfaces. The mathematical probability library supplies PMFs, couplings, distances, and concentration; these are semantic foundations, not additional execution machines.

Differential privacy is covered by `Privacy/DifferentialPrivacy` (added after the survey baseline): `(ε, δ)`-privacy of exact output laws for an explicit adjacency relation, post-processing, adaptive and advanced composition, Hamming group privacy, randomized response, the geometric/discrete Laplace mechanisms, the exponential mechanism, AboveThreshold/Sparse with discrete noise, and packing, reconstruction (from all subset counts or from random `±1` queries) and small-universe lower bounds; see [Protocols and privacy](protocols-and-privacy.md#differential-privacy). Rényi, concentrated and computational differential privacy, continuous Laplace/Gaussian mechanisms and sampling costs are not covered.

Existing tests include [CslibFrontierTests/ProbabilisticComposition.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ProbabilisticComposition.lean), [CslibFrontierTests/ComputationalCrypto.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/ComputationalCrypto.lean), [CslibFrontierTests/Crypto/AssumptionNonvacuity.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/AssumptionNonvacuity.lean), [CslibFrontierTests/Crypto/GSWFullyHomomorphic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/GSWFullyHomomorphic.lean), and [CslibFrontierTests/Crypto/MPC.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/MPC.lean). Their presence is source evidence; they were not rerun by this author.

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
finite-horizon covariance identity, information and auditing bounds, DPI rigidity
results, and scheduling policy–LP frontier documented below. The expanded
headline programme remains open in [issue 2527](https://github.com/cslib-community/cslib-frontier/issues/2527).
STOC submission 191’s binary-input two-batch FPTAS, exact-selection hardness and
integer-cost pseudopolynomial optimizer are proved; its partial/adaptive-cover main results
remain open. These imports
do not establish completion of the expanded programme. The source
versions and PDF digests are recorded under `Aldridge2027`, `Wang2027` and `Kong2027`
in [the bibliography](../../references.bib). The checked clients are in
[Stoc2027BatchC.lean](../../CslibFrontierTests/Stoc2027BatchC.lean).

- [AdaptivePolicy.Covariance](../../CslibFrontier/Probability/AdaptivePolicy/Covariance.lean)
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
  [AdaptivePolicyCovariance.lean](../../CslibFrontierTests/AdaptivePolicyCovariance.lean)
  constructs the actual two-step investment MDP, independently calculates both
  trajectory costs and recovers their difference using the general theorem.
- [AdaptivePolicy.Information](../../CslibFrontier/Probability/AdaptivePolicy/Information.lean)
  proves STOC submission 587, Theorem 4.2 (PDF p. 4). `jointLaw` is the actual
  state/action law and `productLaw` uses its original marginals. `mutualInformation`
  is their finite KL sum in **nats**, with support inclusion proved from the policy.
  `actionSpan` is the largest supported within-state action range: state-only offsets
  and impossible actions do not enlarge it. `information_bound` works for arbitrary
  real costs and endogenous transitions. For score bounds, use `actionSpan_le`;
  `sub_le_actionSpan` supplies the reverse inequality from a supported witness.
  The proof reuses the library's Pinsker inequality and bounded-score change-of-law API.
- [AdaptivePolicy.Sharpness](../../CslibFrontier/Probability/AdaptivePolicy/Sharpness.lean)
  proves Proposition 4.3 (PDF p. 4). `sharpness_family` constructs the uniform binary
  mismatch-cost experiment with matching probability $(1+\epsilon)/2$, for every
  $0<\epsilon<1$. Its supported span is one, its absolute adaptivity cost is
  $\epsilon/2$, and its actual mutual information is `information ε`.
  `information_tendsto_zero` and `sharp_ratio` prove the vanishing-information and
  limiting-ratio claims by differentiation. This establishes optimality of the
  $1/\sqrt2$ coefficient in nats, rather than merely checking selected parameters.
- [AdaptivePolicy.Regret](../../CslibFrontier/Probability/AdaptivePolicy/Regret.lean)
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
- [AdaptivePolicy.Pathwise](../../CslibFrontier/Probability/AdaptivePolicy/Pathwise.lean)
  proves Theorem 3.1 and Corollary 3.2 (PDF p. 3). The path index is any nonempty
  finite type, costs are arbitrary real vectors, and actions lie in a compact convex
  feasible set. `pathwise_decomposition` constructs an attained best fixed comparator,
  with the unnormalized sample covariance and nonnegative static gap.
  `pathwise_covariance_le_regret` gives the inequality and characterizes equality by
  global optimality of the empirical mean action. No stochastic model is assumed.
  [AdaptivePolicyInformation.lean](../../CslibFrontierTests/AdaptivePolicyInformation.lean)
  checks a negative-regret path, zero and nonzero information channels, and a supported
  span that ignores an impossible action with cost one million.
- [AdaptivePolicy.Nonidentifiability](../../CslibFrontier/Probability/AdaptivePolicy/Nonidentifiability.lean)
  proves the finite-context case of STOC submission 587, Proposition 5.2 (PDF p. 5).
  `finite_nonidentifiability` takes a context set of positive initial probability and
  an action with positive marginal probability that is never played on that set.
  It constructs two deterministic binary loss tables with identical complete logged
  data laws for every sample count but different policy-minus-open-loop costs.
  `logLaw` is nonnegative and normalized; `sampleLaw` is the i.i.d. product, including
  the empty log. Logged propensities are functions of the recorded context, so adding
  them does not distinguish the instances. The checked client exhibits a gap change
  of $-1/4$. For arbitrary measurable context spaces, use the following module.
- [AdaptivePolicy.MeasurableNonidentifiability](../../CslibFrontier/Probability/AdaptivePolicy/MeasurableNonidentifiability.lean)
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
- [AdaptivePolicy.ContextualAudit](../../CslibFrontier/Probability/AdaptivePolicy/ContextualAudit.lean)
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
- [AdaptivePolicy.AuditLowerBound](../../CslibFrontier/Probability/AdaptivePolicy/AuditLowerBound.lean)
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
- [AdaptivePolicy.EpisodicAudit](../../CslibFrontier/Probability/AdaptivePolicy/EpisodicAudit.lean)
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
  [AdaptivePolicyAuditing.lean](../../CslibFrontierTests/AdaptivePolicyAuditing.lean)
  checks outliers, even and empty blocks, a positive-divergence integer-sample
  auditor, a Gaussian context, binary hard-instance endpoints and actual two-step
  trajectories. The shared concentration, importance-sampling and testing proofs
  live in `Probability/MedianOfMeans`, `ImportanceSampling`, `Testing` and
  `ProductDivergence`. These are sample-complexity guarantees for mathematical
  estimators, with no certified machine runtime or empirical numerical claim.
- [AdaptivePolicy.SignReversal](../../CslibFrontier/Probability/AdaptivePolicy/SignReversal.lean)
  realizes Aldridge's Proposition 3.8 (PDF p. 4) with Boolean states and actions. The
  initial state is uniform, investment costs $a(1+s)$, the transition is $s'=s\land a$,
  and the terminal cost is $-ms'$. `sign_reversal` gives myopic covariance $1/4$ and
  actual policy-minus-open-loop cost $(1-m)/4<0$ for every real $m>1$. The second
  action has no effect. Retaining only $s\land a$ preserves the two-state claim;
  the paper's stored pair contains redundant information.
- [StochasticOracle.FullCover](../../CslibFrontier/Probability/StochasticOracle/FullCover.lean)
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
  computation. [ExecutionFeasibility](../../CslibFrontier/Probability/StochasticOracle/ExecutionFeasibility.lean)
  proves this contract for every supported stopped execution.
  [RationalFullCover](../../CslibFrontier/Probability/StochasticOracle/RationalFullCover.lean)
  supplies `optimal_rational_program`: all numerical inputs are rational but
  competitors may randomize with arbitrary real probabilities. The optimum has
  an exact finite-uniform `ProbComp` sampler and `ProbOracleComp` execution whose
  law is proved in [Programs](../../CslibFrontier/Probability/StochasticOracle/Programs.lean).
  This certifies exact sampling, without a strict worst-case fair-coin time bound.
  [RandomCost](../../CslibFrontier/Probability/StochasticOracle/RandomCost.lean)'s
  `billed_cost_eq` covers arbitrary probability spaces and integrable random bills,
  including correlation with the current batch's success. Its assumptions are the
  stopped-trace law and conditional expected costs per selected batch and slot;
  it derives the total expected cost. Import `RationalFullCover`,
  `ExecutionFeasibility` and `RandomCost`, and check the complete
  [StochasticOracleFullCover.lean](../../CslibFrontierTests/StochasticOracleFullCover.lean)
  client: heterogeneous deadlines, internal randomization after failure, a mixed
  optimum, exact non-dyadic sampling, zero/one endpoints, zero turns and
  success-correlated bills. The rational optimizer uses the generic
  [one-constraint LP](../../CslibFrontier/Foundations/Optimization/OneConstraint.lean)
  support reduction and finite vertex enumeration; its schedule set can be
  exponential. The source coverage inventory below records the partial-cover
  controllers and remaining unrestricted adaptive/native-specialization obligations
  under [issue 2527](https://github.com/cslib-community/cslib-frontier/issues/2527).
- [PartialCover](../../CslibFrontier/Probability/StochasticOracle/PartialCover.lean)
  proves submission 191, Lemma 1 (PDF pp. 9, 15). `Instance` supplies the finite
  universe, original weighted sets and a nonnegative feasible dual vector.
  `retain` processes returned subfamilies in order and accepts only a nonempty
  new cover whose weight passes `Certified`. Its invariant charges newly
  covered elements once; overlapping/repeated sets cannot increase the assembled
  cover's weight beyond that charge. `retain_cover_bound` compares every
  completed result with the dual objective and every integral cover.
  Import [PartialCoverRisk](../../CslibFrontier/Probability/StochasticOracle/PartialCoverRisk.lean)
  for Theorem 4's conditional-risk probability bound. `ResponseKernel` gives
  arbitrary real conditional laws on all original-set subfamilies, depending
  on the complete preceding response-subfamily history. `Admissible` requires
  joint local certification and coverage probability at least `p` for each
  eligible uncovered element, only at histories reached with positive mass.
  `law` executes the actual local tests. `certified_completion_bound` derives
  success at least `max 0 (1 - ∑ e, (1-p)^d_e)` for a certified completed cover;
  neither call independence nor element independence is required. `chances_batch`
  identifies `d_e` with the expanded call-count vector, and `multicover_risk_le`
  gives the uniform repetition bound. `repetitions` is the source’s logarithmic
  ceiling: `risk_implies_multicover`, `multicover_implies_risk` and
  `repetition_thresholds` prove necessity of `r₀`, sufficiency of `r₁` and
  `1 ≤ r₀ ≤ r₁` when the universe is nonempty and `0 < p, η < 1`.
  The finite observed-response alphabet
  allows arbitrary correlations and real probabilities; no finite underlying
  random-seed assumption is imposed. Token bills, latencies and a native
  sampler/runtime are not part of this response-law model.
  Import [PartialCoverGreedy](../../CslibFrontier/Probability/StochasticOracle/PartialCoverGreedy.lean)
  for the executable rational-cost selector in `Cslib.Algorithms.Lean.Multicover`. Its input is a
  list of `Oracle` values with finite eligibility sets and rational cost bounds.
  `choose_spec` proves exact minimum cost/gain selection among positive marginals;
  `batch_spec` and `batch_chances` derive full `r`-fold coverage within `n*r` calls
  when those eligibility sets cover the universe. The universe is the whole finite
  type; represent a restricted universe by a subtype. `run_bill_le` proves harmonic
  charging against every feasible benchmark; `greedy_risk_bill` combines the
  necessary/sufficient thresholds and ceiling repetition factor to derive the
  source's logarithmic bill bound against every risk-feasible batch. It does not
  assume an optimizer exists or supply greedy performance as an input.
  `greedy_certified_completion` proves success at least `1-δ` with the actual
  history-conditional response law. Costs must be nonnegative for the comparison;
  positive rational source bounds satisfy this condition. Duplicate calls are
  billed individually. Ties retain the earlier listed oracle and zero-gain
  oracles are skipped. `batch` accepts an integral demand. Import
  [PartialCoverThreshold](../../CslibFrontier/Probability/StochasticOracle/PartialCoverThreshold.lean)
  for `rationalRepetitions`, an exact rational-power search proved equal to the
  real-log ceiling, including equality at an integral threshold. `rationalBatch`
  uses that search and emits exactly the batch analyzed with real logarithms;
  for the sufficient demand pass the rational failure budget `(1-η)/n`.
  [PartialCoverThresholdNative](../../CslibFrontier/Probability/StochasticOracle/PartialCoverThresholdNative.lean)
  supplies `uniform_threshold`: a single native machine computes the exact least
  exponent on all valid runtime binary rational probability/budget inputs.
  Its multiplication/normalization, budget tests, unary counter and loop are charged.
  For binary input length $N$ and actual least exponent $r$, the derived bounds are
  $c(r+1)(r+N+1)^d$ time and $c(r+N+1)^d$ workspace, with constants independent
  of the inputs. No termination count or resource certificate is supplied as input.
  The valid domain is $0<q<1$ and $\delta>0$; budgets at least one return zero.
  `count_eq_repetitions` identifies the output with the exact logarithmic ceiling.
  Check the [native threshold client](../../CslibFrontierTests/StochasticOraclePartialCoverThresholdNative.lean)
  for exact-power, between-power and zero-repetition search-loop traces, counts
  and the shared native certificate.
  Check the complete
  [threshold client](../../CslibFrontierTests/StochasticOraclePartialCoverThreshold.lean)
  with `lake build CslibFrontierTests.StochasticOraclePartialCoverThreshold` for
  exact-power, between-power and zero-demand cases and compiled selector execution.
  `rationalBatch_execution` derives the emitted calls’ total realized bill cap
  and parallel completion by `D` from individual token caps and cutoffs at most `D`.
  Bills and latencies may depend arbitrarily on outcomes; using a full-measure
  outcome subtype gives the almost-sure interpretation. All calls start together,
  and local computation is excluded from this deadline. The client checks
  correlated outcome-dependent bills and latencies on a three-call batch.
  `rationalBatch_joint_execution` composes the actual greedy response law with a
  finite conditional resource table depending on the retained output. Its single
  event includes certified success, total token cap and every call’s deadline,
  with probability at least `1-δ`. The complete threshold client checks this
  joint law with random correlated bills and latencies. This finite-table model
  assumes individual caps at every resource outcome; it does not construct a
  native sampler or charge local computation.
  Import [PartialCoverAsymptotics](../../CslibFrontier/Probability/StochasticOracle/PartialCoverAsymptotics.lean)
  for `factor`, exactly the ceiling/logarithmic factor in `greedy_risk_bill`.
  `fixed_failure` proves $O(\log^2 n)$ for fixed $p,\eta\in(0,1)$;
  `polynomial_failure` proves $O(\log n)$ when $\log(1/\delta_n)$ lies eventually
  between fixed positive multiples of $\log n$, the source's
  $\delta_n=n^{-\Theta(1)}$ regime. The
  [asymptotic client](../../CslibFrontierTests/StochasticOraclePartialCoverAsymptotics.lean)
  checks fixed failure and the nonconstant budget $\delta_n=1/n$.
  [Multicover.Native](../../CslibFrontier/Algorithms/Lean/Multicover/Native.lean)
  now compiles the eligibility/cost scan, residual updates, repeated greedy loop,
  reversal and binary-label output. The generic input has unary ground size and
  repetition count, raw membership masks and binary rational costs; missing mask
  bits are false and excess bits are ignored. `batch_eq` identifies the actual
  output with the previously proved greedy batch. All scans, exact rational
  normalization/comparisons, list work and emitted words are charged.
  [PartialCoverGreedyNative](../../CslibFrontier/Probability/StochasticOracle/PartialCoverGreedyNative.lean)
  composes preprocessing of $\delta/n$, native threshold search and that whole planner.
  Its original input contains no repetition count. `uniform_plan` gives one native
  machine whose time and workspace have fixed polynomial bounds in $N+r_1$,
  with $N$ the encoded original-input length and $r_1$ the derived numerical
  threshold. This is the source's numerical-threshold convention; it does not
  assert polynomial time in the binary length of $r_1$.
  Source identifiers are computed from runtime table positions. `labels_lt`
  proves their range, and `decoded_labels_eq` decodes the emitted sequence against
  the original oracle table to exactly the source greedy batch (including repeated
  calls). `risk_bill` transports the risk and approximation bound against every
  risk-feasible benchmark to this same output, without an optimum premise.
  Check the complete [native greedy client](../../CslibFrontierTests/StochasticOracleGreedyNative.lean)
  with `lake build CslibFrontierTests.StochasticOracleGreedyNative`: it derives
  $r_1=3$ from $q=\delta=1/2$ over three elements, emits `[1,1,1,2,2,2]`, and
  applies the comparison to a five-cost feasible benchmark. Duplicate serialized
  row labels demonstrate that table-index construction is performed by the code.
  The [generic native planner client](../../CslibFrontierTests/StochasticOracleMulticoverNative.lean)
  also covers earlier-row ties, zero gains, repeated scans, empty ground, zero
  demand and short/excess masks.
  This closes native offline planning/resource composition for the stated finite
  binary-rational representation.
  [PartialCoverNativeExecution](../../CslibFrontier/Probability/StochasticOracle/PartialCoverNativeExecution.lean)
  now runs either the computed greedy batch or an arbitrary supplied count vector
  on the same finite-control program. Original input contains binary incidence
  masks, binary rational WSC weights/dual prices and opaque original query strings.
  [SourceEncoding](../../CslibFrontier/Probability/StochasticOracle/NativeRetention/SourceEncoding.lean)
  computes unary incidence lists during native startup and proves polynomial
  conversion, exact original incidences and preservation of finite source promises.
  Candidate positions remain the source output labels. The opportunity count is
  computed from the selected runtime batch; distinct occurrences permit concurrent
  repeated calls to the same original oracle.
  [SourceQuery](../../CslibFrontier/Probability/StochasticOracle/ConcurrentBatch/SourceQuery.lean)
  decodes binary configuration addresses and unmodified source-query payloads.
  `external_source_law` derives the named controller's full native tape/context/
  hidden-state/invoice/duration law from one original joint source oracle, with
  no assumed codec correspondence, independent responses or supplied realization.
  `admit_requests` and `source_label` derive nonempty preformation, fresh opportunities
  and original configuration addresses before any response. `completed_decodes`,
  `completed_certificate` and `report_provenance` connect completion to the decoded
  tape mask, local certificate and actual completed reports. Local instructions
  remain outside the source deadline (PDF p. 5).
  [PartialCoverNativeRisk](../../CslibFrontier/Probability/StochasticOracle/PartialCoverNativeRisk.lean)
  derives per-response kernels from actual joint trajectories and transfers reached
  local-certification/coverage envelopes to certified native tape success.
  `native_success` obtains $1-\delta$ in greedy mode. `startup_live` derives startup
  from source coverage and $\delta<1$; it is not an execution premise.
  [PartialCoverNativeVector](../../CslibFrontier/Probability/StochasticOracle/PartialCoverNativeVector.lean)
  supplies the every-$\zeta$ clause. `vectorCalls_count` proves exactly $\zeta_i$
  original-oracle occurrences. `vector_guarantee` assembles the native probability
  bound $\max(0,1-\sum_e(1-p)^{d_e(\zeta)})$, actual bill at most
  $\sum_i c_i\zeta_i$, and deadline, including the zero-call case. Its analytic
  caps $c_i$ may be real and need not be encoded or read by the program; nonnegative
  accrued-charge bounds apply to each possible call, including cancellation.
  [PartialCoverNativeOptimum](../../CslibFrontier/Probability/StochasticOracle/PartialCoverNativeOptimum.lean)
  defines `riskOptimum` over all risk-feasible repeated-call batches and bounds the
  same controller's greedy bill by the source factor times that infimum. No optimum,
  integrability, bounded-total-bill, desired-runtime or desired-success premise is used.
  The [complete native client](../../CslibFrontierTests/StochasticOraclePartialCoverNativeExecution.lean)
  derives two greedy calls from $q=1/2$, $\delta=1/4$ and proves exact certified
  tape success $3/4$ on a genuinely correlated oracle, including a derived posterior
  envelope and application of `native_success`. It also applies `vector_guarantee`
  to one supplied call (different from the two-call greedy plan), deriving a positive
  $1/2$ success bound with unit invoice/deadline bounds; checks zero-call stopping,
  arbitrary-length opaque queries and replies, an arbitrary query-dependent source
  adapter, incidence truncation, and accrued cancellation charges. Run
  `lake build CslibFrontierTests.StochasticOraclePartialCoverNativeExecution`.
  The concrete interfaces use nonempty finite WSC ground sets and discrete joint samples;
  they do not establish a universal conversion for arbitrary third-party serializers
  or noncomputable real-valued algorithmic inputs. Theorem 6's native specialization
  and the broader measurable/unbounded Theorem 5 remain separate.
  The constant-factor Set Cover hardness transfer after Theorem 4 is proved in
  `PartialCover.Hardness` (section below); the source's sharper
  $(1-\varepsilon)\ln n$ factor remains blocked on
  [#4335](https://github.com/cslib-community/cslib-frontier/issues/4335).
  Unrestricted Theorems 5–6 also remain open.
  From a configured checkout, check the complete
  [StochasticOracleMulticoverGreedy](../../CslibFrontierTests/StochasticOracleMulticoverGreedy.lean)
  client with `lake build CslibFrontierTests.StochasticOracleMulticoverGreedy` for
  exact rational choices, repeated calls, harmonic and risk comparisons,
  empty universes and inputs that fail to cover. For response-law examples,
  import `PartialCoverRisk` and check the complete
  [StochasticOraclePartialCover](../../CslibFrontierTests/StochasticOraclePartialCover.lean)
  client with `lake build CslibFrontierTests.StochasticOraclePartialCover`: it
  checks accepted/rejected overlaps, exact two-call probability `3/4`, a correlated
  response law, a failing conditional guarantee, zero calls and an empty universe.
- [TwoBatchMinimum](../../CslibFrontier/Probability/StochasticOracle/TwoBatchMinimum.lean)
  completes Proposition 1 (PDF pp. 6, 14): `one_turn_cost` gives the exact
  one-turn value; `two_batch_reduction` and `minimum_two_batch` prove the attained
  minimum over nonempty complementary first batches against every randomized
  maximum-success competitor. The two-turn minimum assumes a nonempty population
  and that querying every opportunity concurrently meets the deadline. Empty
  first slots in competing schedules are normalized, rather than excluded.
- [TwoBatchApproximation](../../CslibFrontier/Probability/StochasticOracle/TwoBatchApproximation.lean)
  supplies an executable rational-input selector indexed by `Fin k`. Starting
  from a `FullCoverInstance (Fin k) ℚ`, `choose I ε D` returns the best exact-saving
  candidate from cutoff families and rounded-product tables. It includes the
  full concurrent batch as fallback. `choose_feasible` needs `0 < k` and the
  original full-batch deadline; `choose_success` proves maximum success exactly.
  Check the complete
  [StochasticOracleApproximation.lean](../../CslibFrontierTests/StochasticOracleApproximation.lean)
  client: the heterogeneous example returns saving four at deadline three and
  saving zero at deadline two; its optimum lower bound covers arbitrary randomized
  policies. The client also checks zero-rounded-cost collisions and mandatory
  selections. Kernel evaluation uses `decide +kernel`, not `native_decide`.
  [CutoffFamilies](../../CslibFrontier/Probability/StochasticOracle/CutoffFamilies.lean)
  proves exact deadline soundness, coverage and at most $k(k+1)$ families.
  [MinProduct](../../CslibFrontier/Algorithms/Lean/DynamicProgramming/MinProduct.lean)
  proves table soundness, minimum-product dominance, reconstruction, state and
  operation bounds. Its operation count charges rational multiplication and
  comparison as single operations; it is **not a binary runtime certificate**.
  [RoundedProduct](../../CslibFrontier/Algorithms/Lean/DynamicProgramming/RoundedProduct.lean)
  derives the multiplicative product–sum guarantee for each maximum-cost-member
  branch. Scaling divides by the number of potentially selected branch members,
  including the mandatory member; this bounds the same total rounding loss as
  the manuscript's division by the full population size.
  `choose_approximation` now proves the global saving bound for every nonempty
  feasible comparison first batch. The product-minimizing witness remains
  nonempty: strict positivity of success makes the comparison first-batch failure
  product strictly smaller than one, whereas an empty first batch has product one.
  For rational $0<ε<1$, import
  [TwoBatchGuarantees](../../CslibFrontier/Probability/StochasticOracle/TwoBatchGuarantees.lean)
  and use `choose_real_policy_approximation` to compare with arbitrary real-randomized
  feasible maximum-success policies. `choose_optimum_guarantees` derives an attained
  optimum over those policies and both advertised savings/cost inequalities; it
  also supplies the exact selected-schedule success and deadline. No optimum or
  approximation inequality is a premise. The complete client above checks the
  real-policy bound and a three-opportunity rounding collision whose result must
  retain a nonempty first batch.

  [TwoBatchResources](../../CslibFrontier/Probability/StochasticOracle/TwoBatchResources.lean)
  defines `inputEncoding` using framed reduced signed binary numerators and positive
  binary denominators. `inputSize_bounds` bounds the population and each rational
  field by the full input length. `candidates_length_le` bounds the whole candidate
  list by a polynomial in $k$ and an integer $m$ with $1\le εm$; $m$ pays inverse
  tolerance and is not assumed polynomial in the binary tolerance length. The
  exact products, summed costs and savings comparisons have polynomial binary
  operand widths. Scaling and flooring operand bounds are in `RoundedProduct`.
  [PolyTime.Rat.Binary](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Rat/Binary.lean)
  supplies native multitape polynomial-time arithmetic, comparison, division and
  flooring under `encRatBin`, including binary gcd normalization and zero/negative
  cases. [DynamicProgramming.Native](../../CslibFrontier/Algorithms/Lean/DynamicProgramming/Native.lean)
  certifies insertion, pruning and the entire recurrence with runtime-computed
  populations, keys and probability fields. Table keys use unary because the
  rounded key budget is polynomial; probabilities and costs remain binary.
  Rational list sums/products charge traversal, operand copying and normalization.

  For the complete Theorem 2(2) algorithm, import
  [TwoBatchBinary](../../CslibFrontier/Probability/StochasticOracle/TwoBatchBinary.lean)
  and use `TwoBatchNative.runSchedule` on a `BinaryInput` to emit both batch index
  lists; `run` returns its first batch. The input fields are only `epsilon`,
  `deadline` and the ordered binary rational `calls` triples. `encBinaryInput`
  is exactly the earlier `inputEncoding` on `BinaryInput.ofInstance`.
  The algorithm computes `precision = floor (1 / epsilon) + 1` and writes it in
  unary using the existing charged binary-to-unary routine. For positive tolerance,
  `precision_bounds` proves $1\le εm$ and $m\le ε^{-1}+1$.
  `run_runtime` derives a single native multitape implementation with time and
  workspace polynomial in `runtimeSize`, the original input length plus this
  computed budget. `runtimeSize_ofInstance` gives its bound by input bit length
  plus inverse tolerance plus one. No unary budget, machine or runtime proof is
  required from the caller.

  [TwoBatchNative](../../CslibFrontier/Probability/StochasticOracle/TwoBatchNative.lean)
  implements all cutoff-family/maximum-member enumeration, input lookups, exact
  arithmetic, DP/pruning, reconstructed index lists, membership scans and final
  savings comparisons. `computable_schedule` also charges the final complement
  scan and emits both batches; no batch reconstruction is deferred to an uncharged
  output step. It saturates rounded keys on invalid data to keep the
  internal compiler total and polynomial. The
  [correctness bridge](../../CslibFrontier/Probability/StochasticOracle/TwoBatchNativeCorrectness.lean)
  proves that saturation is inactive on eligible valid-input items and that
  `decode (run (BinaryInput.ofInstance I ε D))` equals the original selector,
  including ordering and ties. `decode` interprets the emitted list of indices;
  no finite-set sorting or normalization is an uncharged runtime instruction.

  `TwoBatchNative.fptas` combines the derived uniform runtime with an attained
  optimum over real-randomized competitors, exact selected-schedule deadline and
  maximum success, and both source savings/cost inequalities. Its assumptions
  remain a nonempty population, $0<ε<1$, a feasible concurrent full batch and the
  original failure-oblivious/FICA model. Local selection time is excluded from
  the prescribed-cutoff deadline. `selectedProgram` follows the returned batches
  through actual concurrent-batch oracle calls; `selectedProgram_law` gives its
  stopped execution law. The complete client above checks the external algorithm's
  heterogeneous deadline, zero-saving fallback, rounding collision, derived budget,
  exact success probability and total behavior on empty/invalid data.
- For Theorem 3's exact decision problem, import
  [TwoBatchHardness](../../CslibFrontier/Probability/StochasticOracle/TwoBatchHardness.lean).
  `TwoBatchHardness.Input` contains the ordered rational probability/cost/cutoff triples,
  deadline and expected-cost threshold, with valid oracle parameters. `encInput` encodes
  only those numerical fields in binary. `Decision` asks for a feasible maximum-success
  two-turn policy of expected cost at most the threshold, allowing arbitrary real private
  randomization. `restrictedDecision_npHard` derives NP-hardness even with unit cutoffs
  and a common success/cost ratio. It reuses the binary `SubsetSum` hardness theorem and
  existing `SubsetSum.toPartition`. The reduction takes `SubsetSumInstance` with named
  `numbers` and `target` fields, encoded by `encSubsetSum`; it removes zero source weights
  and preserves repeated
  positive occurrences as distinct calls. `reduction_mem_iff` is both directions of the
  actual policy decision equivalence, rather than a deterministic-schedule surrogate.

  For exact optimization with positive integer costs, import
  [TwoBatchIntegralRuntime](../../CslibFrontier/Probability/StochasticOracle/TwoBatchIntegralRuntime.lean).
  Build a `TwoBatchIntegral.Input` with binary `calls : List (ℚ × ℕ × ℚ)` and
  `deadline`; `run` returns a feasibility flag and both batch-index lists. No budget
  or tolerance is supplied. `runtime` derives uniform native time and workspace
  polynomial in the binary input length plus the numerical cost sum. `admissible_ofInstance`
  checks the original deadline, and `infeasible` excludes every real-randomized
  maximum-success competitor when the flag is false. On true, `optimizer` proves
  exact deadline feasibility, maximum success and cost optimality for `selectedPlan`,
  including the empty instance. Apply it with `hc : I.cost = fun i => (c i : ℚ)`;
  `I.cost_pos` then ensures the integer costs are positive. `selectedProgram_law`
  relates the emitted batches to their actual stopped oracle execution.

  The implementation reuses the reconstructed minimum-product DP with tolerance
  $1/(C+1)$, where $C$ is the total integer cost. Equal refined keys imply equal
  original integer costs because the entire rounding loss is strictly below one;
  minimum-product dominance therefore preserves the exact objective. This uses
  polynomially many refined keys instead of the paper's unscaled subset-sum keys.
  Probabilities and cutoffs stay heterogeneous binary rationals. Empty input has cost
  zero and is feasible exactly for a nonnegative deadline; an infeasible flag does
  not claim that the accompanying batch lists meet the deadline. A single call
  has zero achievable saving. Local selection time is excluded from the cutoff deadline.
  From a configured checkout, run `lake env lean CslibFrontierTests/StochasticOracleExact.lean`
  to check the [complete client](../../CslibFrontierTests/StochasticOracleExact.lean),
  including both hardness answers, zeros, duplicate weights, exact output/cost/success,
  heterogeneous deadlines, impossible deadlines, empty input and a singleton.
- [Submodular.OracleSavings](../../CslibFrontier/Algorithms/Lean/Submodular/OracleSavings.lean)
  proves Wang's Theorem 2(1) (PDF p. 7). A finite type indexes all oracles;
  `savings p c A` is exactly $(1-\prod_{i\in A}(1-p_i))\sum_{i\notin A}c_i$.
  Use `savings_nonneg` and `savings_isSubmodular` with pointwise $0\le p_i\le1$
  and $c_i\ge0$. Submodularity reuses the library's `IsSubmodular`; savings need
  not be monotone (the test has singleton saving one and full-set saving zero).
  The scheduling theorem and binary-input FPTAS are supplied by `StochasticOracle`.
  Theorem 3's exact-selection results are described above. The source coverage
  inventory below distinguishes Theorem 4's covered model and the remaining
  unrestricted Theorem 5/6 obligations.
- [PeerPrediction.Quadratic](../../CslibFrontier/Probability/PeerPrediction/Quadratic.lean)
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
- [FiniteSampleInformation.Rigidity](../../CslibFrontier/Probability/FiniteSampleInformation/Rigidity.lean)
  is the entry point for Kong's finite-sample information limits (STOC submission 152).
  Import it for the sharp polynomial/sample bounds and actual finite-task payments;
  import [DimensionChanging](../../CslibFrontier/Probability/FiniteSampleInformation/DimensionChanging.lean)
  alone for alphabet-changing collapse. The
  [checked clients](../../CslibFrontierTests/FiniteSampleInformation/Main.lean) include a
  dependent zero-row law, nonzero rectangular Gram law, an impossible five-task
  three-symbol reward, and an attaining eight-task four-symbol mechanism.

  `GeneralAsymmetricC1.Mat n m` is the iterated function space
  `Fin n → Fin m → ℝ`, so calculus uses its finite-product norm. `Simplex U`
  means entrywise nonnegativity and total mass one. A `ColumnStochastic T`
  has nonnegative entries and column sums one, and Alice's channel acts by
  left multiplication. `swapAgents` transposes a law; `bobReports S U` applies
  Bob's channel by right multiplication with its transpose. The
  [QMI bridges](../../CslibFrontier/Probability/FiniteSampleInformation/QuadraticBridge.lean)
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
  [Foundations/Algebra/Polynomial/MaximalMinor](../../CslibFrontier/Foundations/Algebra/Polynomial/MaximalMinor/MaximalMinorWeight.lean).
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

### Submission 191: adaptive Theorem 5 inventory and partial accounting

The primary manuscript is [submission 191](https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/191.pdf),
SHA-256 `d7c07e91dc65c2dd29234b0edf05fe6bcfcbee569eb1a14c07b3e0f337ca7a48`.
Section 6, Theorem 5 (PDF page 12), and Appendix A.5 (PDF page 16) require all of
these obligations; the accounting lemma below does **not** complete the theorem.

- Fix integers $1\le a\le b\le n$, $p_-,p_+\in(0,1]$, costs
  $0<c_-\le c_+$ and latencies $0<\ell_-\le\ell_+$. Set
  $r_a=\lceil n/a\rceil$, $r_b=\lceil n/b\rceil$.
- There exists an adaptive selection-only upper policy. At every reached
  positive-probability history, conditional also on its selected batch, productive
  probability is at least $p_-$; productive turns retain locally dual-certified
  proposals covering at least $\min(a,|R|)$ new elements. Conditional expected
  token cost is at most $c_+$ and latency at most $\ell_+$ almost surely.
- For **every** integer $u$ with $u\ell_+\le D$, stop that policy at completion or
  $u$ turns. Certified success is at least $\Pr[\mathrm{Bin}(u,p_-)\ge r_a]$.
  Expected cost is at most
  $c_+\sum_{t=0}^{u-1}\Pr[\mathrm{Bin}(t,p_-)<r_a]$
  and hence at most $c_+\min(u,r_a/p_-)$. The finite-alphabet upper-policy
  stopping, physical deadline and certificate composition is now provided below;
  a universal selection-only machine realization remains separate.
- Universal lower assumptions quantify over every selection-only policy's reached
  histories and selected batches. Revealed progress means growth of the union of
  **all valid proposed sets**, including unretained proposals. Its conditional
  probability is at most $p_+$, size at most $b$, conditional expected batch cost
  at least $c_-$, and latency at least $\ell_-$ almost surely.
- Every deadline- and turn-feasible policy succeeding with probability at least
  $\eta$ has expected cost at least $\eta r_b c_-/p_+$. With
  $v=\min(u,\lfloor D/\ell_-\rfloor)$, necessarily
  $\eta\le\Pr[\mathrm{Bin}(v,p_+)\ge r_b]$. The matching-envelope consequence
  (equal $a,b$, probabilities and costs) compares bounds within $1/\eta$.

Import [AdaptiveLowerCost](../../CslibFrontier/Probability/StochasticOracle/AdaptiveLowerCost.lean)
and check the complete
[client](../../CslibFrontierTests/StochasticOracleAdaptiveLowerCost.lean).
`conditional_lower_cost` proves the finite-transcript expectation argument for the
universal cost bound. `history t` partitions transcripts by all information after
batch selection and before its response. The two conditional inequalities are
weighted by history mass, so zero-mass fibers are harmless. `hcount` is a
pathwise required-progress inequality; callers must derive it from revealed-set
cardinalities. The result assumes neither independence nor the aggregate desired
cost bound. The client has perfectly correlated progress events, records the
first bit in the second history, checks a valid conditional envelope and shows
that the two events fail the independence identity. A zero-turn edge is included.

For finite conditional response kernels, import
[AdaptiveComparison](../../CslibFrontier/Probability/StochasticOracle/AdaptiveComparison.lean)
and check its [complete client](../../CslibFrontierTests/StochasticOracleAdaptiveComparison.lean).
`progressExpectation` evaluates a terminal payoff of the progress count using a
conditional law indexed by the entire response transcript (newest response first).
`progressExpectation_le` and `le_progressExpectation` compare any increasing
payoff against `bernoulliExpectation`, the independent-trial recurrence. Supply
the conditional probability envelope at every history; the actual response laws
need not be independent or identical. A response may contain auxiliary information,
so the history need not consist only of progress bits. The client uses success
probability $1/4$ before any success and $3/4$ afterwards: its two-success
probability is $3/16$, between comparison values $1/16$ and $9/16$.

Import [AdaptiveBinomial](../../CslibFrontier/Probability/StochasticOracle/AdaptiveBinomial.lean)
for `bernoulliExpectation_eq_integral`, `progress_tail_le` and `le_progress_tail`.
The comparison recurrence is now identified with Mathlib's actual binomial law,
including both increasing count-tail comparisons. No independence of actual events
is used.

For actual proposals, import
[AdaptiveSelection](../../CslibFrontier/Probability/StochasticOracle/AdaptiveSelection.lean)
and check [the complete selection client](../../CslibFrontierTests/StochasticOracleAdaptiveSelection.lean).
`selected` decodes each response into a list of proposed subfamilies and runs the
existing local dual test in chronological order; `selected_bound` preserves its
certificate. `productive` computes the truncated additive decrease from actual
residual cardinalities, declaring success after completion. `residual_le` and
`count_completes` derive the count-to-cover bridge. `binomial_le_completion`
then gives the finite upper-policy coverage probability directly from the
full-history lower productivity envelope and the arithmetic threshold $ar\ge n$.
The envelope must include every history, including unreachable ones.

`revealed` accumulates all actual proposed sets, including rejected ones.
`revealed_card_le` derives the pathwise necessary progress count from a local
newly revealed cardinality cap. `revealed_completion_le_binomial` gives the
reverse probability bound under a full-history upper envelope. This observable
is coverage by all proposals; connection to a universal selection-only machine
and its returned output remains a separate obligation. The client instantiates
both directions with a nonempty positive-cost system and the correlated response
law above, computing actual retained completion probability $7/16$.

`reach_le_binomial_complement` bounds the probability of issuing turn $t+1$
by the complementary binomial tail after $t$ responses, when stopping at actual
retained completion. `executionCost` sums conditional mean bills recursively;
`executionCost_eq_sum` proves its finite tower-property expansion.
`stoppedCost_le_binomial_sum` derives the source's finite stopped-cost sum from
a per-history upper bill bound, zero after actual completion. It assumes neither
independent bills nor the desired expected total. The client computes stopped
unit cost $7/4$ for two turns of the same correlated execution.

These results cover finite response alphabets and finite horizons. `accruedBill` records actual response-dependent bills;
`historyExpectation_accruedBill` identifies their expectation with the recursion
using conditional mean bills. `accruedBill_le_binomial_sum` applies the same
bound directly to these actual accumulated bills, allowing response/cost
correlation. `binomialFailure` is a survival observable of the existing Mathlib
binomial law. For $p>0$, `sum_binomialFailure_le` bounds every finite tail sum by
$r/p$, and `tsum_binomialFailure` proves that the infinite series equals $r/p$.
Summability is proved first; no mean, limit or integrability target is assumed.
The endpoint $p=1$ and zero required successes are included; $p=0$ is excluded.
`accruedBill_le_mean` consequently bounds every finite actual response-bill
expectation by $cr/p$. The complete client above checks certain productivity,
a nontrivial two-success mean, and the correlated execution's bound for every horizon.

`summable_noncompletion` derives summability of actual finite-horizon failure
probabilities, hence convergence to zero via `Summable.tendsto_atTop_zero`.
For nonnegative response bills, `expectedBills_summable_le` proves summability of
the marginal expected charges and bounds their series by $cr/p$. Its partial
sums equal finite accrued-bill expectations by the tower identity and converge by
`Summable.hasSum`. These results establish a finite expected-charge series.

`CslibFrontier.Probability.StochasticOracle.AdaptivePath` constructs an infinite
response law `responseMeasure` using Mathlib's Ionescu–Tulcea theorem. The initial
response has table `law []`; `responseKernel` then reads every preceding response
in newest-first order, including auxiliary response data. The alphabet is finite
and has measurable singletons. `responseMeasure_prefix_joint` identifies each
prefix/next-response joint law as a measure-kernel product, and
`responseMeasure_condDistrib` identifies the conditional next-response law almost
surely under the actual prefix distribution. The latter uses a standard Borel
nonempty alphabet. The complete selection client above checks the Boolean
instance and chronological decoding. This constructor imposes no productivity or
cost envelope; existing finite comparison theorems still require their stronger
all-history envelopes. The source's almost-sure reachable-history conditions are
not yet sufficient inputs to those finite theorems.

`integral_responseMeasure_step` gives the real-valued cylinder tower identity,
including observables of both the full prefix and next response.
`integral_responseHistory` identifies every finite-history observable with
`historyExpectation`; the correlated client checks that the finite accrued-bill
bound therefore holds under the actual infinite law. No productivity or cost
hypotheses are needed for this exact identification. `measurable_responseHistory` supplies measurable finite cylinders.
`ae_eventually_complete` transfers the summable finite noncompletion probabilities
to the actual response measure and applies Borel–Cantelli: almost every trajectory
has a complete retained cover at every sufficiently late turn. Its positive
productivity bound is still required at every history. The complete correlated
Boolean client checks this conclusion without a termination premise. `stoppedBill` makes a raw response-dependent charge zero after retained completion.
`accruedBill_responseHistory` identifies each finite accrued bill with the partial
sum of actual pre-response-history charges. `totalBill` is the extended nonnegative
supremum of these accrued bills, retaining infinity on divergent trajectories.
`totalBill_integrable_le` uses monotone convergence and the finite cylinder bounds
to derive almost-sure finiteness, integrability of its real conversion, and
expectation at most `c*r/p`. Its inputs explicitly require nonnegative charges
and the all-history conditional mean envelope; no total-bill bound, integrability
or termination is assumed. The complete client checks response-dependent costs
under the correlated law and the empty-ground, `p=1` endpoint.

For the weaker source envelope, import
`CslibFrontier.Probability.StochasticOracle.AdaptiveReachable`.
`Reachable law h` means that every response in the transcript was sampled with
positive conditional probability from its preceding history.
`ae_responseHistory_reachable` proves that all prefixes of the original infinite
process satisfy this condition almost surely. The comparison recursion removes
zero-weight summands directly; kernels and the infinite process law are unchanged.
No desired equality with a replacement law is an input.
`binomial_le_completion_reachable` and `ae_eventually_complete_reachable` require
productivity only on supported histories where the retained cover is incomplete.
`totalStoppedBill_integrable_le_reachable` takes a nonnegative raw charge and its
conditional mean bound only on these issued histories, and stops billing pointwise
at completion. It derives actual total finiteness, real integrability and the same
`c*r/p` expectation bound.

`selectedBatchLaw` explicitly samples a batch from a history-dependent table and
then samples its response, retaining both in the transcript. Its joint weights
factor as selection mass times response mass; `selectedBatchLaw_conditional`
recovers the response table by conditioning on a positive-mass selected batch.
The proved tower identity and supported-batch mean bounds compose in
`selectedBatch_totalStoppedBill`. No condition is imposed on null batches. This is
finite discrete disintegration, not a general measurable-space disintegration theorem.

For arbitrary discrete response types at a finite horizon, import
`CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.Discrete`.
`responseStep law` runs a newest-first PMF response law through `PMF.seqProcess`;
`PMF.seqHistory` converts its chronological coordinates back to the actual transcript.
`incompletion_le_binomial_discrete` bounds the probability that the actual `selected`
family is incomplete by the binomial lower tail, and `binomial_le_completion_discrete`
gives the complementary success bound. Their productivity premise applies only at
supported, incomplete prefixes before the supplied horizon. No finite response alphabet,
terminal coverage premise or alteration of the actual law is needed. The count bridge
uses the deterministic `count_completes` invariant; `productive_of_complete` supplies
the post-completion successes for both the finite and arbitrary-PMF proofs.
The checked [discrete retention client](../../CslibFrontierTests/StochasticOracleDiscreteRetention.lean)
uses geometric responses with unbounded positive-probability support: zero proposes
the positive-cost singleton cover and positive responses propose nothing. It checks
the actual retention rule, productivity probability, finite-horizon coverage bound and
pathwise dual certificate.

Import `CslibFrontier.Probability.StochasticOracle.AdaptiveSelection.DiscreteCost`
for the same execution's finite stopped token bill. `accruedBill_eq_sum_discrete`
is exact tower accounting for the actual `accruedBill` of response-dependent charges.
`accruedBill_le_binomial_sum_discrete` applies it to `stoppedBill`, bounding expected
cost by `c` times the finite binomial survival sum. For positive `p`,
`accruedBill_le_mean_discrete` gives `c * min(n, r / p)`. Realized charges must be
nonnegative; only reached incomplete histories need the one-turn conditional mean
bound by finite `c`. Charges can be unbounded and correlated with progress. No
total-cost bound or integrability is assumed: the resulting finite bound controls
the nonnegative extended expectation. The same client uses invoice `x + 1`, proves
its geometric conditional mean is exactly two and its realized values are unbounded,
and checks both the survival sum and `2 * min(n, 2)` envelope.
This removes the finite-alphabet restriction for finite-horizon coverage and stopped
cost. Arbitrary-discrete infinite-path and native resource assembly remain separate.

For an actual stopped batch-selecting policy, import
`CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete` and use its
`SelectionPolicy.Discrete` namespace. `retainingLaw` samples the selected batch before
its response and retains both in an optional record. At retained completion, or after
a prior halt, every later record is `none`, with no proposals, charge or duration.
`UpperBounds` supplies primitive productivity, conditional invoice-mean and actual
duration envelopes only at reached incomplete histories and supported selected batches.
Batch and response types can be arbitrary discrete types; selection can depend on
the full transcript. No final coverage, latency, expected-cost or integrability claim
is supplied as a contract field.

`upper_conditional` derives the joint progress and invoice envelopes by averaging
the actual batch-then-response law. `certified_success` bounds the probability of
retained coverage, its dual weight certificate and actual deadline together. Physical
latency is proved pathwise from supported batch durations. `cost_le_binomial_sum`
and `cost_le_mean` bound the actual raw recorded invoices, using the proved equality
with coverage-stopped billing on supported executions. The separate
`SelectionPolicy.Discrete.FiniteTable` import proves `retainingLaw_toPMF`: the existing
finite-table retaining policy has exactly this next-record law at every history,
including unreachable prior-halt/incomplete histories. Both interfaces share the
record proposal and resource decoders.

The checked [adaptive batch client](../../CslibFrontierTests/StochasticOracleDiscreteBatches.lean)
has two singleton obligations and queries the first one still uncovered by actual
retention. A geometric zero response supplies that batch's singleton; other responses
supply nothing. The batch choice changes after the first retained success. Invoices
`x + 1` have unbounded positive-probability support and mean two, correlated with
progress, while physical duration is one. The client checks certified deadline success
and the actual stopped bill's `2 * min(u, 4)` envelope. This is a constructed finite-horizon
semantic policy; it does not assert native realization of arbitrary stochastic kernels.

The [complete reachable-history client](../../CslibFrontierTests/StochasticOracleAdaptiveReachable.lean)
uses a correlated response law with a null response that poisons subsequent kernels
and charges. It checks that both old all-history envelopes fail at that unreachable
history, while actual finite completion, a.s. completion and total-cost conclusions
hold. It also checks the selected-batch envelope and the full composed batch/response
total-cost theorem with a deliberately bad null batch.
Import `CslibFrontier.Probability.StochasticOracle.AdaptiveStopping` for actual stopping
and physical resources. `completionTime` reuses Mathlib's first hitting time of
zero residual, preserving infinity for a nonterminating path. It is measurable,
and `completionTime_le_iff` identifies each finite stopping event with the actual
completion cylinder. `completionTime_survival` identifies its real survival
probabilities with finite accounting. `cappedTime_mean` identifies the finite
expectation exactly with the truncated actual survival sum. `completionTime_mean` derives a.s. finiteness,
real integrability, the exact sum of actual survival probabilities and the mean
bound `r/p`. Its real representative uses `untopD 0` on the separately proved null
set of infinite indices; finiteness or a stopping mean is never an input.

`cappedTime` stops at completion or the turn budget. `stoppedOutput` is the retained
family at that index; `physicalDuration` adds the actual supplied turn durations
only up to it. `accruedBill_at_capped` identifies actual stopped execution with the
finite stopped-bill observable. `physicalDuration_le` derives the physical bound
from nonnegative per-response durations bounded by `ℓ` only on supported issued
responses. `selectedBatch_duration_bound` transfers per-selected-batch contracts
to the actual joint response law; it needs no constraint on null batches/responses.
No independence or desired total-duration bound is assumed.

`jointSuccess` is one measurable event: the actual stopped family covers the ground,
passes the local feasible-dual cost certificate, and is available by the physical
deadline. `binomial_le_jointSuccess` derives its probability lower bound from the
reachable productivity envelope, per-turn physical contract and budget condition
`u*ℓ ≤ D`. `stoppedOutput_approx` compares this certified output with every integral
cover when `ρ ≥ 0`. `integrable_cost_at_capped` and `expected_cost_at_capped` give
integrability and the finite binomial survival cost bound for that same execution.
These are semantic physical durations supplied by the turn model, without an encoded
machine runtime/space certificate. They do not require a deterministic stopping horizon
for the uncapped process. The complete client above checks a mean bound of four,
exact capped mean `7/4`, joint two-turn deadline/certification probability at least `7/16`, capped response
cost at most `7/2`, an actual early singleton output of duration two, zero turn
budget, empty ground and `p=1`. A full batch/response joint client retains the
selected batch and tolerates poisoned null histories and a null batch.

For universal comparisons, import
`CslibFrontier.Probability.StochasticOracle.SelectionOptimum`. `SelectionPolicy.Oracle`
fixes conditional responses, all valid proposed sets, token charges and physical
durations. An arbitrary `Policy` supplies randomized batch-or-halt choices and a
randomized terminal output kernel. `law` samples the selected batch then its response;
halt is absorbing and carries no extra oracle information. `Admissible` requires
each supported final output, including failed ones, to use previously proposed sets.
It allows buffering
locally uncertified proposals and extracting a certified subset later; it imposes no
local retention algorithm. `successProbability` integrates the actual conditional
randomized output's coverage/certificate/deadline indicator. `expectedCost` charges
only actual issued calls. Both are identified with cylinder expectations under the
constructed infinite process, without an assumed process-law equality.

`LowerBounds` contains supported per-selected-batch progress/size/token/latency
contracts. `UniversalBounds` quantifies those local contracts over every admissible
behavioral policy for the fixed oracle. `universal_lower_cost` derives the source
`eta*rb*c/p` token lower bound. `universal_lower_bounds` also derives the necessary
binomial tail with `v = min(u,floor(D/ℓ))`. Output provenance and the size cap prove
the success-to-revealed-count bridge. Supported latency lower bounds prove that a
successful deadline path has no issued call after that prefix; a halt cannot restart.
The progress comparison permits arbitrary full-history response correlations.
For a finite response table, import
[`AdaptiveSelection/FiniteTable.lean`](../../CslibFrontier/Probability/StochasticOracle/AdaptiveSelection/FiniteTable.lean)
to move between the recursive finite expectation and the actual sequential PMF law.
`historyExpectation_eq_sum_seqProcess` preserves arbitrary real transcript scores;
`historyExpectation_indicator_eq_seqProcess` exposes event probabilities, and
`reachable_seqHistory_iff_mem_support` identifies the positive paths. The existing finite
`revealed_tail_le` now applies the shared `count_tail_le_binomial` comparison through this
bridge. It no longer maintains its own stochastic-comparison induction.
`Distribution.mean_bool_eq_toPMF` converts local Boolean means to event probabilities;
`Distribution.mem_support_toPMF` in `Probability.FiniteTable.Support` characterizes positive
response weights. The checked
[finite-table client](../../CslibFrontierTests/StochasticOracleFiniteTable.lean)
computes a stateful score expectation of `17/4` in both representations and excludes a
poisoned impossible history whose probability envelope would otherwise fail.
The finite expectation tower used here and by the infinite-path semantics is shared in
`AdaptiveSelection.HistoryExpectation`. These bridges preserve the original semantic model
and resource bounds; they add no native realization theorem.
The shared `marginal_lower_cost` aggregates the actual derived marginals directly; no
aggregate expected-cost lower bound is a hypothesis.

For arbitrary discrete competitors and the source's weaker successful-only provenance,
import `CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete.Competitor` for
execution, actual observations and progress, `...Discrete.LowerCost` for tokens, or `...Discrete.Deadline` for
physical deadlines.
The shared `policyLaw` executes an arbitrary PMF choice of batch or halt, followed by
the fixed conditional response law. `outputLaw` then samples the returned family from
the actual transcript; no retention algorithm is imposed on the competitor. The same
`CertifiedOutput` predicate checks coverage, the dual weight certificate and accrued
physical duration in both representations. `policyLaw_toPMF` in the optional finite-table
bridge identifies the existing finite policy law with this shared execution at every
history. The retaining upper policy is a specialization of the same dispatcher.

`SelectionPolicy.Discrete.ProgressBounds` constrains revealed-progress probability and
newly revealed cardinality only for supported issued batches before halt.
`SelectionPolicy.Discrete.LowerBounds` extends it with nonnegative realized charges and a
conditional invoice-mean lower bound; these charges may be unbounded. The shared provenance
field applies only
when an actually sampled output is counted as a certified success; failed fabricated
masks remain allowed. `success_count` derives the required revealed-progress threshold
from coverage and the size cap, using all actual proposals, including locally rejected
ones. `lower_cost` proves that the actual extended nonnegative invoice expectation is
at least `eta * r * c / p` for positive `p` and the supplied achieved success level.
There is no integrability or finite-expected-bill premise: the common ordered-semiring
calculation `marginal_cost_mul_le` works directly for extended expectations, including
infinity, and also supplies the real finite-table accounting theorem.

The checked [discrete lower-cost client](../../CslibFrontierTests/StochasticOracleDiscreteLowerCost.lean)
buffers a bundle that local retention rejects and randomly extracts its cheap certified
singleton. It can halt before querying and return an expensive fabricated failed mask;
that mask really occurs on a supported history and violates all-output provenance.
With geometric response metadata and invoice `x + 1`, actual success is `1/4`, actual
expected bill is one, and the theorem supplies the nonzero `1/2` lower bound. A second
invoice `2^x` satisfies the same source contracts but has infinite actual expected bill.
This extends the finite-horizon **token lower bound** to arbitrary discrete semantic
competitors.

For the independent necessary deadline bound, `SelectionPolicy.Discrete.LatencyBound`
requires each supported issued batch/response to contribute at least `ell > 0` to actual
accounted duration. A model with cancellation must establish this bound for its recorded
durations.
`deadline_probability_le` combines this with `ProgressBounds` to bound actual certified
success by `binomial (min u floor(D/ell)) p` on `Set.Ici r`. It imposes no token-cost
hypothesis. The shared deterministic `count_eq_prefix_of_issued_bound` shows that an absorbing
transcript with at most `v` issued calls gains no additional revealed progress after prefix
`v`; the existing finite-table deadline proof uses the same lemma.
[`PMF/SequentialPrefix.lean`](../../CslibFrontier/Probability/PMF/SequentialPrefix.lean)
identifies that shorter prefix's marginal with the actual shorter process, so no path-law
or count comparison bridge is supplied by the caller.

The checked [discrete deadline client](../../CslibFrontierTests/StochasticOracleDiscreteDeadline.lean)
queries a geometric source until receiving a buffered bundle, then halts and randomly
extracts a singleton. Three decision turns with deadline one are bounded using the
one-trial binomial tail with parameter one-half. A supported certified output has positive
probability, and the response law has unbounded support. This extends the necessary
finite-horizon deadline comparison to arbitrary discrete semantic competitors; native
representation remains a separate obligation.

For instance-level cost comparisons in this semantic model, import
[`Discrete/Optimum.lean`](../../CslibFrontier/Probability/StochasticOracle/SelectionPolicy/Discrete/Optimum.lean).
`SelectionPolicy.Discrete.optimalCost` takes both an externally fixed turn budget and an
independent `allowed` policy-class predicate. The class can express opportunity-use or other
selection restrictions. `feasibleCosts` filters that class by successful-only `Admissible`
provenance, the actual success requirement and `DeadlineFeasible` at every supported prefix.
These feasibility predicates contain no progress or token-envelope assumption.
`expectedCost` integrates actual accrued invoices in `ENNReal`, permitting infinite means;
the infimum is infinity when the feasible class is empty. This fixed-budget class differs
from the earlier finite `SelectionPolicy.optimalCost`, whose documented infimum permits
all finite budgets.

`le_optimalCost` derives the universal lower bound from primitive limitations on the allowed
admissible competitors. `optimalCost_sandwich` constructs the retaining witness's feasibility
and actual expected-cost upper bound; the caller establishes that the witness belongs to
the chosen policy class and has successful-only provenance. The upper policy's chosen
retention decoder is separate from the complete oracle-proposal decoder used by all lower
competitors. Use
[`AdaptiveSelection/Provenance.lean`](../../CslibFrontier/Probability/StochasticOracle/AdaptiveSelection/Provenance.lean)
for per-response `ProposalsValid` compatibility: newly emitted retention candidates must
occur somewhere in the actual proposal history. This permits candidates buffered from an
earlier response. `retaining_admissible_of_valid` derives the upper witness's provenance
from that local contract. Direct successful-only admission remains available when failed
paths do not satisfy the stronger compatibility condition. The retention decoder is
deterministic on recorded history and response. Representing operational random retention
decisions as recorded metadata requires a proof that the actual joint law is preserved.
`optimalCost_sandwich_ceilDiv` supplies the source counts `ceil(n/a)` and `ceil(n/b)`
from the positive per-turn size bounds, using Mathlib's ceiling division. Callers need no
separate cardinality/count certificates. `matching_envelope_ratio` gives the `1/eta`
comparison under matching envelopes. `optimalCost_eq_top_of_deadline_bound` derives infeasibility from the necessary
binomial deadline bound, independently of token-cost envelopes. The accounted-duration and
native-model boundaries above still apply.

The checked [discrete optimum client](../../CslibFrontierTests/StochasticOracleDiscreteOptimum.lean)
uses one legal singleton opportunity, geometric responses and invoice `x + 1`. At budget and
deadline one, success one-half has optimum exactly two, attained by the actual retaining
policy. Invoices of arbitrarily large size occur on supported issued records. A target above
one-half has value infinity. Restricting the same source to policies that halt before querying
also gives infinity at target one-half, checking that the specified class changes the infimum.
This is a semantic optimum; equality with an infimum over native PTM implementations requires
a separate representation argument.

The [chosen-retention client](../../CslibFrontierTests/StochasticOracleChosenRetention.lean)
checks why the decoder distinction matters. A raw response lists a weight-one singleton
before a weight-two full cover, with unit dual prices. Processing both retains the singleton
and then rejects the full cover against the remaining dual charge. Choosing only the full
cover completes immediately. Its provenance is checked against both raw proposals, and the
sandwich derives optimum two for the complete raw-proposal problem. A separate compatibility
check retains a candidate on a later response after buffering it earlier.

`retainingPolicy` constructs an admissible upper policy from a randomized batch
selector; `UpperBounds` contains only its supported source contracts.
`retaining_guarantee` derives its actual certified deadline probability and stopped
finite token bound. `optimalCost` is the real infimum over **all** admissible policies and all finite
turn budgets achieving the deadline success level, including competitors using a
different turn budget from the upper witness. Competitors must satisfy
`DeadlineFeasible`, the physical deadline on every supported terminal transcript;
this is derived for the upper witness from its per-call contract, not assumed.
`optimalCost_sandwich` proves nonemptiness
from the constructed upper witness and boundedness from the universal lower theorem,
then sandwiches this infimum between the source lower bound and actual upper-policy
cost. `matching_envelope_ratio` derives the `1/eta` comparison with that universal
infimum for matching coverage/probability/cost envelopes and positive `eta`.
No optimum attainment, lower optimum bound or optimality certificate is assumed.

The [complete policy client](../../CslibFrontierTests/StochasticOracleSelectionPolicy.lean)
checks universal local contracts for every policy of a correlated oracle, randomized
early halt, randomized final output, the physical one-call deadline inside a two-turn
budget, and the matching comparison. Its second instance offers a costly bundle
rejected by local retention: an admissible buffering policy extracts the cheap
certified singleton and succeeds with probability one, and the universal lower
cost theorem still applies. This checks that the competing class includes policies
outside the constructive retention algorithm.

Theorem 5 remains incomplete at unrestricted source scope: the infinite-path
behavioral theorems still use finite response alphabets; finite-horizon retained
coverage and stopped token costs above permit arbitrary discrete PMFs. The development
does not supply a realization/representation theorem for every encoded
selection-only PTM or general measurable alphabets. Implemented native controllers
and their resource theorems are described below; unrestricted encoded-source
resource transfer remains open. The Poisson-binomial domination needed for Lemma 2 and for the
measurable or unbounded-horizon Theorem 5 is tracked in
[#4336](https://github.com/cslib-community/cslib-frontier/issues/4336). Theorem 4's native offline greedy runtime is now proved for the finite binary-rational
representation above. Its computed greedy controller has the native success/OPT
transfer and concrete incidence/query adapters above, including every call-count
vector. Its asymptotic factors are proved, and the constant-factor hardness
transfer is proved below; the $(1-\varepsilon)\ln n$ factor remains blocked on #4335.

### Submission 191: Set Cover hardness of one-turn partial-cover selection

The remark after Theorem 4's proof ([Wang2027], PDF p. 11) reduces unweighted Set
Cover to minimum-token one-turn partial-cover selection: oracle $i$ returns $V_i$
with certainty at unit token cost, and $p=\eta=1$, $y_e=1/n$, $\rho=n$.
`PartialCover.Hardness.Selection` is the binary input of this deterministic oracle
class (ground labels, the set each oracle returns, natural token costs).
`Selection.success` is the probability, under the same fixed-order retention law
`Instance.law` used for Theorem 4's probability bound, that the retained responses
cover the ground set; `success_eq` shows it is $1$ exactly when the queried sets
cover $U$ and $0$ otherwise, including repeated calls. `admissible` shows that these
oracles satisfy Theorem 4's conditional guarantee with $p=1$, so the instances lie
in the source's model rather than in a separate combinatorial problem.

`minSelection` minimizes the token bill $c(\zeta)=\sum_i c_i\zeta_i$ over call vectors
with success probability at least $\eta=1$.
`approxPreservingReducible_setCover_selection` reuses the library's
`ApproxPreservingReducible` interface with identity ratio. `optTokens_ofSetSystem`
proves that the optimum equals the minimum cover size, and the readback `queried`
keeps the oracles with positive call counts in polynomial time.
`P_eq_NP_of_selection_approx_const` combines this with `GapSetCover_npHard`: unless
$\mathrm{P}=\mathrm{NP}$, no polynomial-time algorithm approximates the selection
problem within any constant factor. Hardness on this subclass also rules out
algorithms for any broader input class that contains it.

The source states the sharper bound: no $(1-\varepsilon)\ln n$-approximation for any
constant $\varepsilon>0$ unless $\mathrm{P}=\mathrm{NP}$, citing Dinur and Steurer (2014). That bound needs
Dinur–Steurer low-soundness Label Cover, which the library does not have yet
([#4335](https://github.com/cslib-community/cslib-frontier/issues/4335)).
`P_eq_NP_of_selection_approx` accepts an `NP`-hard `GapSetCover r` only for a constant
ratio `r`. The reduction keeps the ground set and maps ratios by the identity, so it
would carry a $\ln n$ gap, but the hardness theorem and the `P = NP` wrapper would first
need instance-dependent (`GapSetCoverFn`) versions. Run
`lake build CslibFrontierTests.StochasticOracleSetCoverHardness` for the checked
clients: covering and non-covering batches, repeated calls, the readback, the
admissibility witness, optimum preservation and the consumer-facing hardness form.

### Submission 191: source coverage inventory

This table records the numbered results of [Wang2027] against the primary PDF,
including Appendix A. “Covered” means the stated finite/source-interface model
described in the linked sections, not an arbitrary external PTM serializer or
nonatomic oracle implementation. “Partial” identifies a remaining obligation even
when its numerical statement is already proved. The full objective in
[issue 2527](https://github.com/cslib-community/cslib-frontier/issues/2527) remains open.

| Source locator | Lean declarations (in `Probability.StochasticOracle` unless stated) | Status and scope |
| --- | --- | --- |
| Proposition 1, PDF p. 6; App. A.1, p. 14 | `one_turn_cost`, `two_batch_reduction`, `minimum_two_batch` | Covered: attained one/two-turn maximum-success costs, including randomized competitors, in the finite failure-oblivious/FICA model. |
| Theorem 1(1), PDF pp. 6–7 | `preselection_equivalent`, `policy_iff_lp`, `cost_success_frontier` | Covered: actual stopped policy law, all-failure schedule law and finite LP have the same frontier. |
| Theorem 1(2)–(3), PDF p. 7 | `target_feasible_iff_schedule`, `optimal_two_schedules`, `maximum_success_support`, `deterministic_max_success`; `optimal_rational_program` | Covered: feasibility, attained support at most two, maximum-success endpoint and exact rational-input sampling. Exact sampling is not a worst-case fair-coin runtime bound. |
| Theorem 2(1), PDF p. 7 | `Cslib.Algorithms.Lean.Submodular.OracleSavings.savings_nonneg`, `savings_isSubmodular` | Covered: the finite savings set function is nonnegative and submodular; the explicit namespace here is outside `StochasticOracle`. |
| Theorem 2(2), PDF pp. 7–8 | `TwoBatchNative.fptas`, `selectedProgram_law` | Covered: rational binary native FPTAS, both numerical approximation inequalities, original deadline/maximum success and stopped selected-program law. |
| Theorem 3(1), PDF p. 9; App. A.2, pp. 14–15 | `TwoBatchHardness.restrictedDecision_npHard`, `reduction_mem_iff` | Covered: actual randomized-policy decision hardness, unit cutoffs and common success/cost ratio. |
| Theorem 3(2), PDF p. 9 | `TwoBatchIntegral.runtime`, `optimizer`, `selectedProgram_law` | Covered: native exact optimizer with resource bound polynomial in input bits plus numerical integer cost sum. |
| Lemma 1, PDF p. 9; App. A.3, p. 15 | `PartialCover.Instance.retain_cover_bound`; `NativeRetention.certified_eq`, `retain_eq`, `completed_output` | Covered: local dual certification, overlap-aware retention and derived full-cover weight bound, with actual rational native tests. |
| Theorem 4, PDF pp. 10–11, arbitrary count vectors | `PartialCover.NativeExecution.vector_guarantee`, `external_source_law`; `NativeRetention.SourceEncoding.valid_toNative` | Covered: same native machine, original binary WSC/query interfaces, exact call multiplicities, certified tape-risk, sum-of-caps bill and oracle-only deadline, including zero calls and $q=0,1$. |
| Theorem 4, PDF pp. 10–11, greedy algorithm and approximation factor | `PartialCover.GreedyNative.uniform_plan`, `risk_bill`; `PartialCover.NativeExecution.native_success`, `native_bill_le_riskOptimum`; `PartialCover.Asymptotics.fixed_failure`, `polynomial_failure` | Covered: native threshold/eligibility/cost/output composition, success and OPT-risk comparison, and $O(\log^2 n)$ / $O(\log n)$ corollaries for nonempty finite binary-rational inputs. |
| Hardness remark after Theorem 4's proof, PDF p. 11 | `PartialCover.Hardness.success_eq`, `admissible`, `approxPreservingReducible_setCover_selection`, `optTokens_ofSetSystem`, `P_eq_NP_of_selection_approx`, `P_eq_NP_of_selection_approx_const` | Partial: the source's deterministic-oracle reduction ($p=\eta=1$, $y_e=1/n$, $\rho=n$, unit token costs) is formalized through the actual retention law, and unless $\mathrm{P}=\mathrm{NP}$ minimum-token one-turn selection has no polynomial-time constant-factor approximation. The source's $(1-\varepsilon)\ln n$ bound (Dinur–Steurer) needs low-soundness Label Cover and is blocked on [#4335](https://github.com/cslib-community/cslib-frontier/issues/4335); `P_eq_NP_of_selection_approx` transfers constant-ratio `GapSetCover` hardness; a $\ln n$ bound also needs instance-dependent (`GapSetCoverFn`) wrappers. |
| Lemma 2, PDF p. 11; App. A.4, pp. 15–16 | `AdaptiveSelection.binomial_le_completion` and finite conditional-history comparison APIs | Blocked on [#4336](https://github.com/cslib-community/cslib-frontier/issues/4336) for the source’s varying-$p_t$ Poisson-binomial guarantee, including its heterogeneous and measurable/unbounded comparison; finite homogeneous comparisons are present. |
| Theorem 5(1), PDF p. 12; App. A.5, p. 16 | `NativeRetention.BatchOutput.upper_controller`, `BatchUpper.stopping_controller`, `BatchPathCost.upper_controller` | Covered for the named finite-opportunity block controller: certified decoded tape success, binomial deadline, survival-sum/mean/budget real-integrable total path-bill bounds, same source oracle and actual receipts. Silent divergence retains earlier charges. Unrestricted source-policy realization remains partial. |
| Theorem 5(2) and consequence, PDF p. 12; App. A.5, p. 16 | `NativeRetention.BatchOptimum.lower`, `success_le`, `feasible_success_le`, `upper`, `competitive` | Covered for admitted finite-control native selection-only competitors on the same oracle and seed: expected-cost lower bound, effective-turn binomial deadline obstruction and OPT envelope. |
| Unrestricted Theorem 5 source coverage, PDF pp. 4–6, 11–12 | Native epoch/whole-policy representation; `NativeBatch.PathCost.lintegral_totalBill_complete`, `totalBill_integrable_budget`; preceding controller APIs | Partial: unrestricted source query/cutoff, external-machine realization and general measurable interfaces remain. Infinite discrete native paths, retained divergent-prefix costs and real integrability are now packaged for the finite source budget. Infinitely many source turns require a broader interface and remain an extension beyond the source’s finite-$u$ statement. Domination needed for measurable/unbounded progress is blocked on #4336; the other representation obligations are not blocked on that issue. |
| Theorem 6 construction and $L=\mathrm{OPT}=1$, PDF pp. 12–13 | `ResidualCover.coverInstance`, `primal_optimum`, `dual_optimum`, `responses_certified`, `decode_near_residual` | Covered mathematically for arbitrary promised finite X3C inputs, with hidden fixed exact covers and derived certificates. |
| Theorem 6 one/two-turn optima and ratio, PDF p. 13 | `ResidualCover.one_turn_optimum`, `two_turn_optimum`, `attained_ratio`, `attained_linear_ratio` | Covered for all finite behavioral policies, including randomized extraction and mixed concurrent first batches. |
| Theorem 6 native WSC/role/residual realization, PDF pp. 12–13 | `NativeResidualEncoding.source`, `source_valid`, `native_primal_optimum`, `native_dual_optimum`, `native_near_residual`, `native_responses_certified`; `NativeResidualSelector.computable_request`, `controller_law`; `NativeResidualReplies.observed_proposals`, `retained`, `near_residual`, `near_live`, `completed_output` | Covered in the documented native interface: arbitrary promised finite X3C inputs, original WSC labels, known role metadata, decoded raw residuals/local certificates, source batch admission, provenance, guarded native output and joint resources. The runtime-role controller removes the old least-element program's label-order restriction; the unused legacy specialization is not needed for these attainment results. |
| Theorem 6 universal native query-token optimum and optimal uniform selectors, PDF p. 13 | `NativeResidualInvoice.response_factor`, `expected_score_eq_charge`; `NativeResidualPolicies.policy_law`, `terminal_law`, `selection_success_one`, `native_two_lower`, `native_one_lower`; `NativeResidualOptimum.one_lower_of_mean`, `two_lower_of_mean`; `NativeResidualRealCost.hasMean`, `expected_finset`, `hasMean_bind`; `NativeResidualRealAdaptive.minimum_cost_mem`; `NativeResidualRealMinima.native_optimum`, `native_one_optimum`, `native_ratio`, `native_linear_ratio`; `NativeResidualCostChoice.native_expected_cost`, `native_optimum`; `NativeResidualRealChoice.native_cost_mem`, `native_optimum`; `NativeResidualPathCost.integrable_totalBill` | Partial at source scope: the documented native model proves the equalities for arbitrary positive real price parameters and every fixed invoice PMF with the source batch means (`HasMean`), such as `FixedMeanInvoice.law` and its mixtures with deterministic natural invoices. The PMF is drawn independently of residual index $J$ and the preceding history. Every admitted finite-control selection-only native competitor uses the same source oracle and seed, with unbounded local computation. Conditional mean accounting preserves accrued divergent prefixes; the two compiled strategies attain both minima, and the rational-table cost chooser is one optimal compiled program. No integer-price identity, integrability or target-cost premise is required. History-dependent or $J$-coupled invoice laws with the paper’s conditional means remain unproved. These are genuine source obligations, not blocked on #4336. External-machine representation remains separate. |

Not everything outside #4335/#4336 is present. The native real-price Theorem 6
minimum/ratio and rational uniform selector are proved for every fixed invoice PMF
with the source batch means, independently drawn from $J$ and history. Extending
attained equalities to history-dependent or $J$-coupled conditional-mean laws
remains a source obligation.
Unrestricted source-query/cutoff and external-machine realization for Theorem 5
remain material, not blocked on #4336. No ALL-main or unrestricted source-model
completion is claimed.


### Submission 191: fixed real expected costs with natural token reports

The source model (PDF p. 5) explicitly allows arbitrary real parameters in analytic
statements, while numerical algorithmic inputs are binary rationals. Token counts
are nonnegative natural random variables. Fixed per-call expected prices therefore
do not require a serializer for arbitrary real numbers. Response-dependent declared
prices would be an optional extension, not a missing source requirement.

Import [FixedMeanInvoice](../../CslibFrontier/Probability/FixedMeanInvoice.lean)
and [NativeResidualRealChoice](../../CslibFrontier/Probability/StochasticOracle/NativeResidualRealChoice.lean).
`FixedMeanInvoice.law` draws a concrete finite-support natural invoice vector with
any prescribed nonnegative real coordinate means. At most one coordinate is
charged in a draw, so within-batch invoices can be correlated. Its finite cap is
derived from the prices; no total-bill bound or integrability premise is supplied.
`NativeResidualInvoice.sample` draws a fresh vector from a fixed invoice PMF `ν`
after each admitted batch selection, followed by the original conditional residual
response. The invoice law is drawn independently of residual index $J$ and the
preceding history. All native competitors see that same oracle. Every theorem in
`NativeResidualRealCost`, `NativeResidualRealAdaptive`, `NativeResidualRealChoice`,
`NativeResidualRealMinima` and `NativeResidualPathCost` takes `ν` with
`HasMean P ν`; `NativeResidualRealCost.hasMean` instantiates it with
`FixedMeanInvoice.law (prices P)`, and `hasMean_bind` closes it under mixtures.
`expected_finset` gives the mean of every opportunity set, and
`batch_expected_cost` proves the selected-batch mean for every selected batch, hidden server history, cutoff and remaining deadline,
including cancellation.

`NativeResidualRealAdaptive.feedback_law` executes both response-dependent epochs
with independent fresh invoice draws, rather than assuming that an adaptive
policy preserves a once-for-all mixture. `native_resources` preserves their joint
bill and duration. The actual compiled all-specialist and near-then-specialist
programs have certified tape output with probability one and exact accrued costs
$$
\mathbb E[\mathrm{bill}_{\mathrm{all}}]=\sum_j c_j,\qquad
\mathbb E[\mathrm{bill}_{\mathrm{adaptive}}]=c_0+\sum_j p_jc_j.
$$
These formulas hold for arbitrary real positive expected prices. Termination and
terminal-to-whole-trace cost equality are derived from their actual execution laws.
`minimum_cost_mem` attains the smaller value in the existing native feasible-cost
class. The matching universal lower bound is now provided below.

`NativeResidualRealChoice.native_expected_cost`, `native_certified` and
`native_cost_mem` apply to the **same** compiled `NativeResidualCostChoice.controller`
with its original rational price-table input ABI. Only the primitive table reflects
the source prices and probabilities; no natural-price identity is required. The
[real-cost client](../../CslibFrontierTests/StochasticOracleNativeResidualRealCost.lean)
uses five nonempty overlapping-triple blocks and specialist mean $\sqrt 2$ for both
actual strategies. The [price-aware client](../../CslibFrontierTests/StochasticOracleNativeResidualRealChoice.lean)
uses near mean $1/4$ and specialist mean $1/2$, proves actual certified tape success
one and expected bill $3/4$, and places that attained value in the same native cost
class. Neither price can be identified with a constant natural invoice.

The native real-mean lower/OPT equality for this particular independent invoice law
is proved by the accounting below; arbitrary conditional-mean invoice laws remain a gap.
Import [NativeResidualInvoice](../../CslibFrontier/Probability/StochasticOracle/NativeResidualInvoice.lean)
and [NativeResidualRealMinima](../../CslibFrontier/Probability/StochasticOracle/NativeResidualRealMinima.lean).
`NativeResidualPolicies` now accepts a PMF of fresh natural invoices. A point mass
recovers the earlier fixed-invoice oracle; `NativeResidualOptimum.one_lower` and
`two_lower` retain their original public statements. The generalized posterior
construction retains arbitrary invoice-dependent local computation and hidden state,
selected-before-response actions and divergent mass. Primitive `HasMean` concerns
one selected batch, not total policy cost or success. `NativeResidualRealCost.hasMean`
derives it for the constructed real-mean oracle.

`NativeResidualInvoice.expected_score_eq_charge` proves that the declared-price
receipt ledger and actual accrued token ledger have equal expectations at every
finite epoch horizon, including paths that subsequently diverge. The behavioral
one/two-turn lower proofs therefore apply without an integer-price identity.
`NativeResidualOptimum.one_lower_of_mean` and `two_lower_of_mean` quantify over the
existing native competitor class; `NativeResidualRealMinima.native_optimum` and
`native_one_optimum` match those lower bounds with the actual attained strategies.
`native_ratio` and `native_linear_ratio` give the source ratio for arbitrary positive
real prices. `NativeResidualRealChoice.native_optimum` proves optimality of the same
single compiled cost-aware program on its rational-table input. The clients now
check the irrational-price optimum and ratio, plus both fractional-price branches:
minimum $3/4$ at near mean $1/4$, and minimum $5/2$ at near mean $4$.
`selectionOnly_of_output_memory_bind` shares the provenance support argument used
by both concrete real-mean strategies.

The lower accounting and the attained upper and optimum equalities hold for every
fixed invoice PMF satisfying `HasMean`, sampled independently of $J$ and history.
A client checks native OPT $2$ for a fair-coin mixture of the deterministic unit
invoice with `FixedMeanInvoice.law`. History-dependent or $J$-coupled invoice
laws with fixed conditional per-call means require further execution, posterior
and attainment proofs. These gaps are not blocked on #4336. The general native
path-cost construction below imposes no such invoice-independence restriction,
but by itself does not establish the missing optimum equalities.

The unrestricted source-query/cutoff interpreter and external-machine adapters
also remain unproved. `NativeUnboundedExecution.selectionOnly_of_output_memory`
reuses derived native output/memory laws for provenance; its concrete consumers
are the cost-table compiler, not an assumed representation of arbitrary machines.
No curated abstract or result is promoted to an
unrestricted Theorem 5/6 or ALL-main claim.

From a matching warm checkout, run:

```bash
lake build --wfail --iofail CslibFrontierTests.StochasticOracleNativeResidualRealCost \
  CslibFrontierTests.StochasticOracleNativeResidualRealChoice
```

### Submission 191: actual infinite native paths and real total bills

Import [PathCost](../../CslibFrontier/Computability/Probabilistic/NativeBatch/PathCost.lean)
and [BatchPathCost](../../CslibFrontier/Probability/StochasticOracle/NativeRetention/BatchPathCost.lean).
Use `open scoped Cslib.Probability.NativeBatch.PathCost` for the documented discrete
state sigma algebra. The path space has its product sigma algebra; hidden state,
reply packets and metadata need not range over a finite set. The adapter
`ObservedProcess.trajectory` applies the Ionescu--Tulcea construction to the actual
PMF transition. `map_coordinate` and `lintegral_coordinate` derive its original
finite execution laws, without a supplied representation identity. This handles
discrete PMF sources, not arbitrary nonatomic oracle kernels.

`pathMeasure` runs the actual native source-epoch transition forever.
`pathMeasureFrom` continues a retained trace prefix. `totalBill` includes the
initial accrued prefix plus the series of actual new nonnegative receipt scores.
`partialBill_eq_accrued_from` identifies its partial sums with the original accrued
ledger almost surely. Silent divergence appends zero-call decisions and never
erases the earlier bill. `lintegral_totalBill_from` uses monotone convergence to
identify the total expectation with the supremum of finite trace expectations.
`lintegral_totalBill_complete` proves that the source turn budget makes this equal
to the already defined complete native expectation. No termination, total-bill
bound or integrability premise is supplied.

`totalBill_integrable_budget` derives almost-sure finiteness, real integrability
and the budget cost bound from reached selected-batch conditional means. It allows
history-dependent/correlated charges and arbitrary hidden metadata. The same-code
`BatchPathCost.upper_controller` combines actual certified tape output with the
survival-sum, mean and budget bounds for this real-integrable **total path bill**,
under the existing primitive progress/cost/latency envelopes. It retains the fixed
block scheduler’s scope; no arbitrary source scheduler is assumed executable.
`NativeResidualPathCost.integrable_totalBill` gives the exact real minimum for the
same compiled rational-table residual selector and its constructed independent
invoice oracle, without an integrability or target-cost premise.

The [path-cost client](../../CslibFrontierTests/NativeBatchPathCost.lean) applies the
identity to the real native program with geometric, correlated unbounded invoices.
It also continues an actual charged concurrent receipt through a silent native
loop: the expected retained total is exactly eleven or three, while the suffix
diverges. The zero-score edge is zero. The existing correlated upper-controller
client now checks real total-bill integrability and bound four for the same single
program that supplies success and OPT bounds. The fractional price-aware client
checks real total expectations $3/4$ and $5/2$ for both branches of the same code.

This closes discrete finite-budget native divergent-path/real-cost packaging,
not unrestricted source query/cutoff or external-machine compilation. The paper
fixes finite opportunities and a finite turn limit $u$. An interface issuing
infinitely many source batches remains an additional requested extension; the
cost monotone-convergence step itself does not require #4336. General measurable
progress domination remains blocked on #4336. No abstract or ALL-main
completion claim is promoted.

### Submission 191: actual Theorem 6 residual construction and policy optima

The source setup (1)–(3), PDF pages 12–13, and Theorem 6/proof, PDF page 13, are
implemented in `CslibFrontier.Probability.StochasticOracle.ResidualCover` and
`CslibFrontier.Probability.StochasticOracle.ResidualPolicy`. Start with any $z\ge3$
nonempty promised X3C yes-inputs (`Block`). Each has an arbitrary family of triples
on `Fin (3*r)` and a disjoint exact-cover witness. That witness fixes the hidden
oracle answers; it is not a dual certificate, optimum value or input to the
residual-guided selector. Canonical labels represent finite disjoint universes.
`coverInstance` computes the triple weights $1/(zr_j)$, fallback weights $2/z$
and element duals $1/(3zr_j)$. `universe_card` gives $n=3\sum_jr_j$.

`dual_objective`, `primal_optimum` and `dual_optimum` derive objective one, an
actual weight-one full cover, the universal integral lower bound and the universal
feasible-dual upper bound. `same_block_iff_common_candidate` recovers the block
partition from incidence alone: fallbacks connect every pair in a block, and no
candidate crosses blocks. `near_specialist_properties` checks that neither answer
alone covers the instance and that their union does. `near_residual` computes the
actual uncovered subuniverse, `decode_near_residual` recovers its index, and
`responses_certified` proves both sequential local dual tests at $\rho=1$.

For the source's exactly-once opportunities, `Parameters` accepts arbitrary
positive costs and any positive full-support near-cover law. `OnePolicy` and
`TwoPolicy` range over arbitrary finite behavioral kernels for the first batch,
conditional second batch and final extraction. All near/specialist mixtures are
included. `Admissible` imposes only selection-only provenance from actual received
candidate indices and no opportunity reuse on supported branches. `run` constructs
the response/output law; `success` tests actual optimal coverage and `cost` charges
every issued call. `optimalOutput_eq_one_iff` identifies the success test with
actual minimum weight among all integral covers, using the derived primal optimum.
No coverage, optimum or lower-bound conclusion is part of admissibility. The source's probability-one optimal-output requirement is the
separate success premise of the universal lower bounds.

`one_turn_optimum` and `two_turn_optimum` exhibit admissible successful policies
and compare them with every admissible successful behavioral competitor. Their
costs are $\sum_jc_j$ and $\min\{\sum_jc_j,c_0+\sum_jp_jc_j\}$, respectively.
The proof derives coverage on every supported branch from actual probability-one
success. If the near call is delayed until turn two, its response cannot guide
another simultaneous call, so every specialist is necessary. If it is issued
first alongside any specialist subset, each still-missing positive-probability
residual forces its specialist in turn two. Averaging covers randomized policies.

`attained_ratio` compares these actual universally optimal policies: when all
$c_j=c>0$ and $c_0=\alpha c$, the ratio is
$z/\min\{z,\alpha+1\}$. The scalar $c$ may be any positive $c(n)$ evaluated at
`universe_card`; `attained_linear_ratio` gives $z/(\alpha+1)$ when $z>\alpha+1$.
The source specializes to $\alpha>1$. `batchLatency` charges one physical turn
for each nonempty concurrent batch; `unit_deadlines` gives the one/two-turn
bounds at $D=2$. `adaptiveTwo_residual` identifies the actual follow-up batch
with computation from the received near-cover residual.

The [complete residual client](../../CslibFrontierTests/StochasticOracleResidualCover.lean)
constructs five six-point X3C blocks with an overlapping unused triple. It derives
the dual/primal and residual/certificate claims, checks universal randomized
competitor bounds of five and three, constructs successful policies attaining
both, and obtains the strict ratio $5/3$ with the physical turn counts.

This proves the arbitrary finite X3C construction and universal behavioral
numerical endpoints, rather than only a singleton or supplied-certificate model.
The unrestricted encoded-PTM representation and realization bridge is still unproved; neither
unrestricted source Theorem 6 nor ALL-main is claimed complete. Theorem 5's
representation/general-alphabet gaps and Theorem 4's $(1-\varepsilon)\ln n$
hardness factor (#4335) remain material. No curated abstract changes: these modules are outside the
selected headline dependencies.


### Submission 191: compiled residual-directed source queries

Import [NativeResidualSelector](../../CslibFrontier/Probability/StochasticOracle/NativeResidualSelector.lean)
and [NativeResidualEncoding](../../CslibFrontier/Probability/StochasticOracle/NativeResidualEncoding.lean).
`NativeResidualEncoding.source` creates binary incidence and rational weights/dual
prices from arbitrary promised X3C blocks and explicit original point/candidate
enumerations. The hidden exact-cover witnesses are not serialized. `incidence`,
`weight_cast` and `dual_cast` preserve the original source quantities; `region`
derives component recovery for this source construction, using its whole-block
fallback sets rather than a supplied recovery certificate.

`source_valid` now derives every rational WSC promise from those X3C inputs;
clients do not supply a native validity or dual certificate. `nativeInstance`
is the actual decoded native WSC interpretation. `covered_label`, `cost_label`
and `certified_label` preserve the source semantics of arbitrary original
families, including overlapping unused triples. `native_near_residual` gives the
actual missing block, and `native_responses_certified` derives both chronological
local tests at $\rho=1$. `native_primal_optimum` constructs an original-label
native cover of weight one and bounds **every** native integral cover below by
one, including families with out-of-range labels. `native_dual_optimum` bounds
every nonnegative feasible dual above by one. Thus $L=\mathrm{OPT}=1$ is now
proved for the decoded native **WSC instance**; this does not yet establish the
optimal query-token cost over native policies. The larger client derives these
claims on five six-point blocks with overlapping unused triples, checks the
thirty-element native ground and all five six-element missing-block residuals.

`NativeResidualSelector.Query` pairs the original rational WSC input with original
point labels of the requested subuniverse. `Query.candidates` restricts to candidates
contained in that universe while retaining their global labels. `representatives`
computes component representatives from original incidence alone. The original
input to `controller` is `startupEncoding (source, z)`: the source instance is
framed first and the number of specialist roles is unary. One finite-control
program handles all these runtime data, including variable role counts and
arbitrary finite raw replies. Roles are ordered by increasing component minimum;
slot zero is the near cover and slot `j+1` is specialist `j`.

The first request asks the near cover. The guarded feedback loop parses and locally
certifies its actual raw report, computes `residual` from retained coverage, and
selects the specialist whose recovered representative is the least uncovered
point. The second query contains that actual residual WSC subinstance. The same
code performs both turns, cleanup and final mask emission. `request_eq` proves that
the runtime list implementation is exactly the concurrent source codec;
The original retention certificates `computable_rows`, `computable_dual`,
`computable_ground` and `computable_covered` are public and reused by this planner;
its incidence computation does not duplicate a private proof.
`controller_law` derives the complete joint native law, preserving source hidden
state, raw history, stopping, decoded tape output and resource metadata. No
separately compiled continuation or assumed scheduler-realization law is used.
`controller_protocol` also derives termination with the accepted source ledger
and exact bill/time/provenance meters on the guarded source environment; that
endpoint does not assert acceptance of malformed or unsupported queries.

Run `lake build CslibFrontierTests.StochasticOracleNativeResidualSelector` for the
[native residual client](../../CslibFrontierTests/StochasticOracleNativeResidualSelector.lean).
It uses three nonempty three-point X3C blocks, each with a triple and fallback. For
every missing component, it derives both source admissions, queries only its
matching specialist after the near reply, returns the actual weight-one cover mask,
and consumes exactly the two distinct opportunities with bill five and oracle
duration two. The original dual validity and the final computed family’s certificate
are derived, and the actual joint output/bill/duration marginal is a point mass. A full-support uniform hidden initial component gives the derived
joint mixture of these correlated native executions. The specialist checks the
actual query bytes against its own original labeled subinstance. This is a
nontrivial integrated client, not a universal native optimum theorem.

Import [NativeResidualReplies](../../CslibFrontier/Probability/StochasticOracle/NativeResidualReplies.lean)
for the general raw-response connection. `Answers` distinguishes inactivity from
cancellation, with an actual natural invoice in each active slot. `report` places
original-label family masks in the source concurrent codec. `observed_proposals`
derives the native parser’s output from actual `observe`/`replyOf` receipts of
preformed batches and unit-latency source trajectories; no parser agreement is
assumed. `observed_resources` derives the same receipt’s additive invoices and
maximum concurrent unit latency, including canceled calls. The statements are
pathwise and allow arbitrary correlated response vectors.

`retained` handles complete newest-first raw histories and identifies executable
rational retention with source chronological certification. `afterNear` and
`afterSpecialist` use the actual `RuntimeControl.afterReply` update, preserving
the original runtime instance and raw history. For every promised X3C family,
`near_residual` and `near_live` derive the missing block and a live guard after
its near-cover report. `completed_output` and `specialist_stopped` derive a
weight-one cover decoded from the updated runtime result and a stopped guard
after the specialist report. The
[raw-reply client](../../CslibFrontierTests/StochasticOracleNativeResidualReplies.lean)
checks all five six-point residuals, arbitrary invoice bit lengths, correlated
raw replies, a concurrent actual receipt with a billed canceled slot, and the
empty interface. Run
`lake build CslibFrontierTests.StochasticOracleNativeResidualReplies`.

The local endpoints above are composed downstream with source admission and
actual compiled execution by the runtime-role controllers in
`NativeResidualAttainment` and `NativeResidualAll`. `NativeResidualPolicies`
derives the one/two-turn native-to-behavioral laws for all admitted competitors;
`NativeResidualMinima` derives the attained native optima and ratio. The legacy
component-order controller still needs its own canonical-role specialization.
The natural-invoice results in this subsection do not assert arbitrary-real expected invoice realization; the real-mean construction above is separate.
`NativeResidualCostChoice` below provides compiled cost-aware choice for rational data. Source deadlines count oracle time only.

### Submission 191: unbounded native residual-policy tables

Import [NativeResidualOracle](../../CslibFrontier/Probability/StochasticOracle/NativeResidualOracle.lean)
and [NativeResidualPolicies](../../CslibFrontier/Probability/StochasticOracle/NativeResidualPolicies.lean).
The former constructs one source sampler from the original X3C inputs: zero is
the near-cover role and `j+1` is the specialist for original block `j`. A completed
batch is preformed before its near residual is sampled. Specialist answers are
fixed hidden exact covers. `query` encodes the original WSC and requested
subuniverse; `families` cancels incorrect subinstance bytes. The sampler is shared
by every native competitor. Natural invoices are supplied separately from the
real-valued analytic price fields in `ResidualCover.Parameters`; no equality of
those prices or expected native costs is asserted by the constructor.

`response_factor` derives the actual native source-response kernel from that
sampler. `NativeResidualPolicies.joint` instruments two genuine source epochs
and the following local-computation epoch. `joint_hidden` recovers the actual
three-epoch native trace, retaining hidden tapes, private coins, rejected-query
computation, invoices and divergent mass. `policy_law` derives finite behavioral
tables by posterior disintegration. Only the source actions/residuals and final
family are tabulated; hidden native state is not approximated by a finite type.
The residual label is latent instrumentation on an invalid-query cancellation,
not an assumption that native code observed it.

With two source turns, `terminal_law` identifies the family marginal with the
original unbounded stopped native tape output, under its original candidate
labels. Invalid/missing outputs map to the empty failure family. `policy_nonreuse`
derives disjoint reached action sets from the actual source ledger, excluding
null histories. `selectionPolicy` intersects output with the proposed source
family; `selection_admissible` proves this completed behavioral policy admissible
and `selection_cost` preserves its batch-cost score. `response_available` follows
actual raw masks through wrong-query and cutoff cancellation; no unreturned
candidate becomes available. `selection_success_one` uses successful-output-only
native provenance to prove that probability-one optimal output survives this
completion. The final local epoch cannot issue a third batch: its empty receipt
is derived from the actual source budget.

`response_charge` proves that an issued call adds its actual invoice even on
cancellation and that later divergence preserves prefix charges.
`batchCost_invoice` explicitly identifies each analytic source price with its
natural wire invoice. Under this per-call convention, `policy_cost_le_native`
compares the behavioral score to the actual whole-trace expectation, without an
integrability or bounded-total-bill premise. `native_two_lower` therefore derives
Theorem 6's universal two-turn lower bound for actual admitted native competitors.

Import [NativeResidualOptimum](../../CslibFrontier/Probability/StochasticOracle/NativeResidualOptimum.lean)
to specialize the existing Theorem 5 native optimum: `accept_eq` proves that the
decoded source WSC certificate is weight-one optimality, and `two_lower` proves
$$
\min\left\{\sum_j c_j,\ c_0+\sum_j p_jc_j\right\}\le\mathrm{OPT}_{\mathrm{native},2}.
$$
The competitor class, original runtime input, one shared sampler/seed and accrued
bills are exactly those of `BatchOptimum.optimum`; no finite hidden-state or local
clock bound is introduced. The source prices here are positive natural invoices
cast to reals. The downstream runtime-role variants derive source admission,
certified tape output and both attained native optima and their ratio; see
`NativeResidualMinima`. Arbitrary-real expected invoice realization remains open; a compiled rational
cost-aware chooser is provided downstream in `NativeResidualCostChoice`. The legacy component-order upper
program still needs its own canonical-role specialization.

The [native-policy client](../../CslibFrontierTests/StochasticOracleNativeResidualPolicies.lean)
uses the five overlapping-triple blocks and an actual full-reply native reader
starting with the original query on its input tape. Every missing block has
positive source probability; the stopped raw-output/shared-memory law is derived,
with exact bill two and oracle duration one. It also instantiates table
readback and behavioral completion/admission for that reader and for the same
named adaptive upper program, and checks billed wrong-subinstance and zero-deadline
cancellations. Its source invoice convention is instantiated, its constructed
weight-one cover is accepted, and the common-oracle native optimum has lower bound
three. This lower-bound client does not prove attainment or that the reader solves
the cover problem.
This does not prove that every computed upper-program query is source valid. Run
`lake build CslibFrontierTests.StochasticOracleNativeResidualPolicies`.
No curated abstract or result is promoted to an unrestricted
Theorem 5/6 or ALL-main claim.

### Submission 191: attained adaptive native optimum

Import [NativeResidualAttainment](../../CslibFrontier/Probability/StochasticOracle/NativeResidualAttainment.lean).
The new runtime-role routing variant uses the same approved clockless feedback
compiler and the exact `GuardedStartup.encoding` input used by `BatchOptimum`.
The source says the PTM knows the oracle roles and their guarantees (PDF p. 13).
`universes` and `input` encode those known subuniverses in a leading private
frame, alongside the original WSC data. They encode no hidden cover or prepared
runtime state. `roles_initial` and `roles_afterNear` derive actual decoding and
preservation of that metadata through arbitrary replies.

The legacy component-order selector assigns roles by least original point. The
routing variant compares the actual retained residual with the known role
subuniverses, so original point and candidate enumerations are arbitrary.
`second_slots`, `first_source` and `second_source` derive the exact preformed
near/specialist requests, source acceptance and response law. `native_law`
composes them with the original-input compiled controller and full reply reader;
`native_resources` preserves joint native tape output, memory, invoices and
oracle duration. Every missing block has its actual positive source mass.

For this **same named program** `native_selectionOnly` proves admission on all
finite halted executions, `native_certified` proves certified tape success one
by the oracle deadline two, and `native_expected_cost` proves
$$
\mathbb E[\mathrm{bill}]=c_0+\sum_j p_jc_j.
$$
Termination is derived from the concrete native law. The general
`NativeBatch.Quantitative.expected_charge_eq_terminal` then identifies terminal
invoices with the original whole-trace accrued-cost expectation, retaining the
trace convention for divergent prefixes. No termination, integrability,
bounded-total-bill or desired expected-cost premise is supplied to attainment.
The per-call prices are explicitly the positive natural wire invoices cast to
reals, as in the lower-bound convention.

`native_cost_mem` places this exact cost in the existing Theorem 5 native
competitor class; it is not a behavioral score or a fresh surrogate optimum.
`native_optimum_of_adaptive_le` combines the attained upper bound with the
universal lower bound, proving
$$
\mathrm{OPT}_{\mathrm{native},2}=c_0+\sum_jp_jc_j
\quad\text{when}\quad c_0+\sum_jp_jc_j\le\sum_jc_j.
$$
The proof-only reindexing of the decoded candidate count preserves the exact
source sampler, query bytes, masks and invoices (`source_reindex`,
`sample_reindex`). The adaptive program and all competitors use the same oracle and seed.

The [attainment client](../../CslibFrontierTests/StochasticOracleNativeResidualAttainment.lean)
uses five six-point overlapping-triple blocks and uniform near residuals, with
near invoice two and specialist invoices one through five. It derives certified
native success one, the response-dependent joint invoices and duration, exact
accrued expectation five, and attained native OPT five. Different residuals select
different actual requests and invoices. It also checks duplicate/order-insensitive
subuniverse comparison and preservation of the role frame under arbitrary replies.
Run `lake build CslibFrontierTests.StochasticOracleNativeResidualAttainment`.

The complementary all-specialist case is now provided by
[NativeResidualAll](../../CslibFrontier/Probability/StochasticOracle/NativeResidualAll.lean).
For every positive source turn budget, the fixed `NativeResidualRouting.controller false`
preforms all specialist requests from the original role metadata, before seeing
any reply. `source` derives the actual accepted batch transaction;
`completed_retained` proves certification and retention for distinct specialist
replies in their actual report order. `native_law` composes this transaction with
the original-input clockless native program. `native_certified` and
`native_selectionOnly` derive actual tape success and provenance. `native_resources`
and `native_expected_cost` give joint bill/duration and exact accrued expectation
$\sum_j c_j$; termination is derived, not assumed. `native_cost_mem` therefore
attains this value in the same native class for both one and two source turns.

Import [NativeResidualMinima](../../CslibFrontier/Probability/StochasticOracle/NativeResidualMinima.lean)
for `native_cost_mem` and `native_optimum`, which combine both concrete controllers
with the universal two-turn lower bound:
$$
\mathrm{OPT}_{\mathrm{native},2}
  =\min\left\{\sum_j c_j,\ c_0+\sum_jp_jc_j\right\}.
$$
This is equality for the original common-oracle native infimum, including the
case where all specialists are strictly cheaper. The proof selects between two
fixed compiled programs; it does not yet compile a uniform cost-comparison
procedure into one program.

The [all-specialist client](../../CslibFrontierTests/StochasticOracleNativeResidualAll.lean)
uses the same nontrivial five blocks, near invoice twenty and specialist invoices
one through five. It derives exact native OPT fifteen (the adaptive alternative
costs twenty-three), certified one-turn tape success, the one-turn native OPT
equality and joint bill fifteen/duration one. Its expected-cost check works for
every positive permitted turn budget.
Run `lake build CslibFrontierTests.StochasticOracleNativeResidualAll`.

`NativeResidualPolicies.one_policy_law` constructs the selected-before-response
one-epoch posterior; `one_terminal_law` identifies its output with the original
native stopped tape readback. The final epoch adds no query, as derived from the
one-turn budget. `one_success` transports sure success using actual successful-output
selection provenance, and `one_cost_le_native` retains billed prefixes even on
silent divergence. `native_one_lower` and `NativeResidualOptimum.one_lower`
therefore quantify over every admitted one-turn native competitor. The source
sum-of-specialists value is attained by the all-specialist program, so
`NativeResidualMinima.native_one_optimum` proves
$$
\mathrm{OPT}_{\mathrm{native},1}=\sum_j c_j.
$$
For $c_j=c>0$ and $c_0=\alpha c$, `native_ratio` and `native_linear_ratio`
transfer the source ratio to the real parts of these finite attained native optima:
$$
\frac{\mathrm{OPT}_{\mathrm{native},1}}{\mathrm{OPT}_{\mathrm{native},2}}
  =\frac{z}{\min\{z,\alpha+1\}}
  =\frac{z}{\alpha+1}\quad\text{if }z>\alpha+1.
$$
The same five-block client also checks a genuine native adaptivity gap $5/3$
with near invoice two and unit specialist invoices, against the same full-support
residual sampler. These are equalities of the existing native optima, not just
cost comparisons of two handpicked policies.

A compiled rational cost-aware strategy is now provided in the following section.
Arbitrary-real expected invoice realization and the separate unrestricted
Theorem 5 representation obligations remain outside the implemented model and
are not blocked on #4335 or #4336, so not everything outside those issues is present. The curated abstract/results inventory is not promoted.


### Submission 191: one runtime cost-aware native program

Import [NativeResidualCostChoice](../../CslibFrontier/Probability/StochasticOracle/NativeResidualCostChoice.lean).
`Prices` contains the near price and explicit rational probability/price rows.
`adaptive` computes both sums and compares them by native binary rational
arithmetic. It receives no cheaper-strategy bit. `Reflects` identifies the table's
primitive prices and probabilities with the source; `adaptive_iff` derives the
source comparison from those entries.

`packed` frames this table before the original private role word in the existing
`GuardedStartup.Input` ABI. The compiler extracts those operands and restores the
original role word before running the selected feedback. No prepared state or
hidden cover is installed. `controller` is one fixed program across both branches,
all role counts and original instances. `native_law` preserves its actual output
and complete oracle memory, including hidden state, arbitrary local computation,
divergent mass and joint receipts. It is derived from actual compiled startup and
feedback, not supplied as a representation hypothesis.

For the same program, `native_selectionOnly` proves successful-output provenance,
`native_certified` proves certified tape success by the oracle deadline, and
`native_expected_cost` proves the actual accrued expectation
$$
\mathbb E[\mathrm{bill}]
  =\min\left\{\sum_j c_j,\ c_0+\sum_jp_jc_j\right\}.
$$
Termination follows from the compiled law and the already proved source
transactions. `expected_charge_eq_of_output_memory` transports accrued bills
only after that termination proof; no total-bill boundedness or integrability is
assumed. `native_minimal` compares the same code with every admitted sure-success
native competitor on this input and oracle. `native_cost_mem` and `native_optimum`
place the one-program witness in the **existing** `BatchOptimum` class, on the
original ABI with explicit price metadata, and prove its attained minimum.

The [cost-choice client](../../CslibFrontierTests/StochasticOracleNativeResidualCostChoice.lean)
changes only the encoded near price, using the same five nontrivial blocks,
uniform residual probabilities and specialist prices one through five. This same
program chooses adaptation at near price two (bill five), all specialists at
near price twenty (bill fifteen), and adaptation on the exact tie at twelve.
It also checks certified tape success and the original native optimum for every
positive integral near price. Run
`lake build CslibFrontierTests.StochasticOracleNativeResidualCostChoice`.

Scope: decision operands have a finite rational encoding, and the actual source
receipt invoices here are natural token counts with the explicit price/invoice
identification. The paper's general cost model uses fixed per-call **expected**
costs, which need not be integers (model, PDF p. 5; Theorem 6, p. 13).
Real-valued fixed-mean invoice realization therefore remains a model limitation;
arbitrary reals are not claimed to have a finite exact serializer or decidable
order. Response-dependent prices are an optional extension, not a missing source
statement. Unrestricted Theorem 5 query/cutoff and external-machine adapters also
remain open; #4336 separately blocks measurable/unbounded domination. The Agent
Operator's Manual needs no edit: no workflow or human-direction changes occur.
The curated abstract/results are not promoted to unrestricted completion.


### Submission 191: a concrete native-to-behavioral bridge

Import `CslibFrontier.Computability.Probabilistic.NativeOneTurn` for a reusable
one-turn protocol with actual native fair-coin multi-tape machines, and
`CslibFrontier.Probability.StochasticOracle.NativeResidualOneTurn` for the residual
instance lower-bound corollary. The [complete native client](../../CslibFrontierTests/NativeOneTurn.lean)
includes its imports, actual transition tables, clocks, adapters and proofs.

`NativeOneTurn A R O` has finite observable action, response and output types.
Its first native machine emits a private packet. The driver retains that packet
and passes it, together with the entire response, through `prepare` to the native
continuation. The action observation must contain all request/query/cutoff data
on which the environment's response law can depend. A complete earlier transcript
can be encoded in the initial input; no history-independent oracle assumption is
made. A joint response table can include arbitrarily correlated responses within
that external batch. The protocol supplies explicit word observers and an input
adapter; this interface does not prove their compilation or native resources.

`run` constructs the actual native experiment from `runClosed` and the response
law. `actionTable` comes from exact saved-coin replay of the first native machine.
`outputTable` conditions those private coins on the action actually selected and
averages the actual continuation over that posterior. `Distribution.posterior`
uses normalized fibers at positive mass and the prior on null actions;
`posterior_factor` and `posterior_bind` prove the required identities, including
null actions. The table/PMF conversions in `FiniteTableOfPMF` are exact inverses.
No representation certificate or desired law equality is an input.

`behavioralRun_toPMF` proves equality of the entire observed joint law.
`mean_eq_native` therefore preserves every finite observable, including success,
issued token charge and physical duration. `OutputsEncoded` is the ordinary
supported raw-word encoding contract; `run_encoded` derives equality with
`rawRun` when that contract holds (`behavioralRun_encoded` is the direct behavioral corollary). It does not assume a distributional encoding
identity. `Halts` requires actual supported halting of both native phases;
`run_pad_first` and `run_pad_finish` prove stability under larger clocks. The
clocks measure local computation, which the source excludes from oracle tokens
and its response deadline. An exhausted nonhalting local run is not admitted by
`NativeAdmitted`.

For the Theorem 6 instance, `nativePolicy_law` identifies the raw behavioral
representation. Source admission requires provenance only for successful optimal
outputs. `normalizedNativePolicy` replaces unproposed failed families with the
empty family, derives supported provenance, and preserves success, issued
cost and physical duration (`normalized_success`, `normalized_cost`, `normalized_duration`). `native_one_turn_lower` then
proves the actual expected-token lower bound against every admitted native
protocol in this interface with actual probability-one optimal success. The
admission fields contain supported halting and source provenance, without a
representation law, optimum or lower-bound conclusion. `native_duration_le_one`
uses concurrent unit call latency and excludes both local clocks.

The native client draws two bits, chooses its public action by their conjunction,
then reads and emits the retained first bit. The false-action conditional output
probability is $1/3$, so replacing retained private coins by fresh independent
coins would give the wrong law. It proves actual halting, raw bit-encoding
correctness and padding invariance. Its residual-instance clients establish
source admission, probability-one success and the actual cost five, and also
admit a protocol with an unproposed fabricated family only on failure. The
failure normalization removes that family; no all-output provenance premise is
substituted for the paper's successful-output condition. The residual-family
observation adapter is explicit; this is not a uniform native implementation of
the residual upper algorithm or its original candidate encoding.

This is a concrete one-turn native packet-protocol bridge. It does not decompose
an arbitrary open PTM's query boundaries, retain arbitrary unexported work-tape
state, handle unbounded local stopping or prove the arbitrary-turn behavioral
representation required by Theorem 5 and the full two-turn lower optimum in
Theorem 6. Later sections derive native query epochs and the concrete block controller.
General response alphabets and external PTM/query encodings, canonical-label
recovery and arbitrary source-policy compilation remain open.
Theorem 4 now has concrete incidence/query adapters and native greedy/every-vector
execution guarantees above; its constant-factor hardness transfer is proved, while the
$(1-\varepsilon)\ln n$ factor remains blocked on #4335. ROADMAP preserves
these obligations; no unrestricted theorem or ALL-main completion is claimed.
No curated abstract depends on
these new modules or selects this bounded bridge as a headline.


### Submission 191: actual multi-query open execution and public path representation

Import `CslibFrontier.Computability.Probabilistic.NativeOpenExecution` for actual
open native execution and `CslibFrontier.Computability.Probabilistic.NativeOpenSelection`
for successful-output provenance. The complete [native open client](../../CslibFrontierTests/NativeOpenExecution.lean)
and [observed-process client](../../CslibFrontierTests/ObservedProcess.lean) include
all imports, state definitions, transition tables and local proofs.

`execute` interprets the existing `MultiTapePTM.runConfigFrom` against a stateful
history-dependent handler. `World` retains the actual native work tapes, control,
query buffers and answer heads, together with the oracle's private state and
complete raw query/reply/resource history. Private work-tape storage is not
exported as an output packet. The theorems apply to arbitrary native tables;
finite control and channels give the ordinary encoded-PTM instances, as in the
client. `Environment` can inspect all earlier events and shared private state.
Its jointly sampled `Reply` supplies the installed word, nonnegative token charge
and external duration. There is no response/charge independence premise or
finite-alphabet approximation. These are discrete PMF laws, including countably
supported infinite response or private-state spaces, rather than arbitrary
nonatomic measurable distributions.

`step` uses the actual transition table and a fresh private fair coin. An ordinary
instruction changes only native configuration; an actual query passes its real
buffer to the handler, installs that reply, and records exactly that observation.
`execute_one` proves equality with the native interpreter. `execute_add` proves
pause/resume of the entire correlated joint state, and `execute_eq_stateLaw`
identifies all finite native executions with the resulting hidden-state process.
No representation equality is supplied as a hypothesis.

For public conditioning, `PMF.posterior` reuses pinned cslib's positive-observation
`PMF.posteriorDist` and adds a harmless prior completion on null observations. `ObservedProcess.privateLaw`
retains the hidden state and complete observed prefix. `nextHistory` constructs
a kernel from the posterior on that complete prefix; `public_eq_observed` proves
equality of entire public path laws. Conditioning merely on the current observed
item can lose private correlations, so this API retains earlier observations.
`execute_public_paths` identifies entire public path laws with actual native
one-instruction checkpoints retaining full configurations and oracle memory.
`execute_history_law` connects their public process to the whole actual raw query
history. This process is indexed by native instructions and
includes silent local steps; it is not yet indexed by source oracle turns.

`tokenBill` and `elapsed` sum the charges and external durations on the same
recorded events. `execute_trace` proves that actual histories extend their
retained prefix and add at most one query per native instruction.
`execute_resources` derives the new bill/duration sums and their monotonicity;
no total-bill bound or integrability is assumed. If an external operation encodes
a whole concurrent batch, its reported duration is that batch's parallel duration.
A source application must still verify that batch/query/cutoff encoding contract.
Local native instructions contribute neither tokens nor external duration.
`execute_halted` and `execute_padding` stop all subsequent queries/resources once
native control actually halts. `execute_public_score` preserves extended
nonnegative expectations, which may be infinite.

`NativeOpenSelection.result` reads a decoded result only after actual native
halting, so exhausting a clock at a live configuration cannot accept an output
prefix. `View.halted` and `Outcome.halted` separately preserve actual native
stopping, so a live prefix differs from a halted failure even when both have
no accepted output. `proposals` parses valid candidates from actual answer words.
`SelectionOnly` imposes provenance only for successful outputs on supported native
runs. `normalized` discards unproposed failed families using `none`; it preserves
the distinction between failure and a successful `some empty` on an empty ground
instance. `normalized_provenance` derives provenance for retained outputs, and
`behavioral_outcome_law` proves the complete native/public joint law of query
history, stopping, acceptance, accumulated bill and physical duration after normalization.
Native parsers/codecs and the acceptance criterion remain explicit semantic
parameters; this result does not compile the source upper selector.

The native client keeps a sampled bit on a real work tape. The first call samples
a second hidden bit, and later replies repeat it from oracle private state.
Native control combines the work bit and first answer to choose an early halt
or the next query. The full configuration/oracle/history law is proved, including
work-tape retention across both calls. Actual expected bill is $5$ and physical
duration $19/4$, with supported native halting and stable larger clocks.
A decoder produces valid successful outputs on some paths and an unproposed
fabricated family only on failed paths; successful-output provenance and the
joint behavioral law are checked. Live prefixes and zero-query accepted empty
covers exercise the stopping/failure distinction. The second client uses an
infinite hidden type: an observed bit disappears and later reappears, with exact
correlated public path probabilities and harmless null-history completion.

### Removing a common native clock

Import `CslibFrontier.Computability.Probabilistic.NativeUnboundedExecution` to
observe actual open native execution without a uniformly sufficient instruction
bound. The complete [unbounded native client](../../CslibFrontierTests/NativeUnboundedExecution.lean)
executes a fair-coin local waiting loop, then queries and halts. Every finite
clock has positive live mass, but its terminal law and almost-sure termination
are proved, together with expected bill $4$ and physical duration $7/2$.
The returned bit, charge and duration are sampled jointly. A second native
machine diverges surely and its terminal result is `none` with probability one.

`StoppedProcess.terminalMass` takes the supremum of actual clocked halted
masses. Absorbing halting makes these masses monotone, and monotone convergence
proves their sum is at most one. `terminal` completes missing mass with explicit
divergence. It retains the full native world on termination, so its transcript,
private state and accumulated resources remain correlated. No uniform clock,
almost-sure halting, representation identity or finite-expectation premise is
required to construct it. The underlying state and observation types need not
be finite; the laws remain discrete PMFs.

Use the native API as follows:

1. Supply the actual `MultiTapePTM`, stateful `Environment` and initial `World`
   from the preceding section. `terminal machine env initial` is the unbounded
   native law on optional complete worlds. `some world` means actual halting;
   `none` means divergence, separately from a halted failed output.
2. Supply the proposal parser, output decoder and acceptance test.
   `SelectionOnly` requires successful-output provenance on every supported
   finite native run, with no common fuel bound. `terminal_support` identifies
   every supported terminal world with an actual halted state at some clock;
   `terminal_provenance` transfers this admission to terminal outputs.
3. `behavioral` constructs a stopped public law from the complete-history
   behavioral kernels and their increasing halted observation masses.
   `terminal_behavioral_law` proves equality with actual terminal public
   observations, including divergence. `behavioral_outcome_law` preserves the
   joint query path, stopping, success, bill and duration under successful-only
   provenance and failed-family normalization.
4. `terminal_score` gives monotone convergence for any nonnegative stopped
   score. For example, use `fun w => (tokenBill w.memory.events : ℝ≥0∞)` to
   obtain the actual stopped-bill expectation as the supremum of clocked
   halted-bill expectations. Infinite expectations are allowed.

`terminal_none_eq_zero` characterizes almost-sure termination by exhaustion of
actual halted mass: $\sup_N \Pr[\text{halted by instruction }N]=1$. The client
proves this condition from the actual native law while also proving that no
finite clock suffices on all positive-probability runs. This is a stopping-law
construction, rather than a choice of a larger deterministic clock.

Costs and durations on **divergent** paths are not encoded as terminal resource
values. A nonnegative terminal score explicitly excludes divergence; it must
not be advertised as the total resource cost of an arbitrary diverging machine.
For almost-surely terminating source policies, the terminal world records their
entire finite query trace and both accumulated resources. This module does not
construct or audit an infinite native trajectory with nonterminating-path bills.
The source's exact local-termination convention must be made explicit when
admitting machines to a quantitative turn/deadline theorem.

### Connecting actual native instructions and the response interface

Import `CslibFrontier.Computability.Probabilistic.NativeInterface` to expose the
query selected by the actual open native transition table before sampling its
response. The complete [interface client](../../CslibFrontierTests/NativeInterface.lean)
reuses the preceding actual native machines, including the work-tape bit shared
across correlated calls and the unbounded fair-coin waiting loop.

`instruction machine world bit` reads the current control and scanned input,
work-tape and answer symbols, then applies the actual transition table. Its
result is an already halted world, a local action, or a chosen channel with its
saved native world and continuation. `prepare` samples only the machine's
private fair bit. `dispatch` runs the external environment only for a query,
submits that world's actual query buffer, installs the exact raw reply, and
records the jointly sampled reply/bill/duration and oracle private state.
`prepare_dispatch` proves that composition is the original native step.

For random-tape semantics, `replay` interprets the original open native program
with saved private coins while retaining the same stateful external handler.
`execute_coins` proves that averaging a fair coin prefix of clock length gives
the actual complete native world law. `terminal_coins` connects these original
program executions directly to the unbounded stopped interface masses through
their clock limits. No uniformly sufficient tape length is required. These are
finite-prefix replay and stopped-limit laws; they do not construct a new
probability measure on infinite private tapes or a native replay compiler.

Use `signal` to observe a selected raw query, channel and previous actual
response/resource history without exporting private tapes or oracle state.
`selectedResponse` records this signal before dispatch, jointly with the actual
next hidden world. `conditionalResponse` is derived from the hidden selected
instruction posterior. `selectedResponse_disintegration` proves the complete
selected-signal/next-world law, with harmless prior completion on null signals;
`selectedResponse_native` recovers the actual native next-state law. The client
checks a query selected with probability $1/2$, derives its posterior, and
identifies its actual conditional raw reply and correlated resource law.

`Phase.ready` is an original instruction boundary; `Phase.pending` retains the
selected but unanswered instruction. `two_ticks` and `even_ticks` prove that
two interface ticks implement one original native instruction, preserving all
hidden state and observations. These ticks are mathematical bookkeeping, not
oracle turns or physical-time charges. Cofinality of the even clocks proves
`terminal_native`, equality of complete optional stopped interface and original
native world laws, including divergence. `worldOf` is for terminal readback;
a pending local instruction may carry a prospective halted configuration, so
this projection is not an acceptance observer for partial interface executions.
`terminal_behavioral` then identifies
the constructed unbounded behavioral stopped view, and `terminal_outcome`
preserves the actual joint path, halting, success, bill and duration under
successful-output-only provenance. The client checks the full correlated native
law, unbounded waiting, expected bill $4$ and sure divergence.

This connection uses the library's typed `MultiTapePTM` model; it does not decode
an arbitrary externally encoded PTM or prove a compiler/resource theorem for
that encoding. The raw interface is a channel plus a bit-string request. To use
the source's oracle-turn quantitative theorems, first use the stopping epochs
in the following sections, including the checked concurrent-batch protocol.
The finite behavioral Theorem 5/6 APIs cannot be applied directly to raw
instruction ticks. The later native selected-epoch APIs perform this transfer;
`BatchOutput` and `BatchOptimum` give the named controller's quantitative bounds.

### Stopping at the next query or halt

Import `CslibFrontier.Computability.Probabilistic.NativeEpoch`. The actual
[next-epoch client](../../CslibFrontierTests/NativeEpoch.lean) and
[quantitative policy client](../../CslibFrontierTests/NativeEpochPolicy.lean) check
unbounded silent waiting, response-dependent queries, silent halting and
probability-one silent divergence. These are actual stopping epochs, rather
than another instruction-level posterior.

`boundary` recognizes a committed native halt or a selected pending query.
`silentStep` executes the real interface transition everywhere else and holds
at the first boundary. `seek machine env world` is its actual unbounded stopped
law, with `none` for silent divergence and `some checkpoint` for a reached query
or halt. `seek_independent` proves that this law cannot sample the selected
query's response. `seek_memory` retains the exact previous oracle private state
and response/resource history while local native tapes may change.

`StoppedProcess.terminal_restart` proves a general first-boundary pause/resume
identity from actual stopped masses, without assuming almost-sure boundary reach
or a common clock. `seek_restart` applies it to the native interface, and
`native_epoch_equation` proves that seeking, dispatching the one selected query
and resuming original native execution leaves the entire terminal law unchanged.
Divergence is propagated, not conditioned away. Accepted-output provenance
continues to use the original native terminal law and its successful-only
normalization; no target representation identity is an admission hypothesis.

`nextEpoch` performs this seek and at most one dispatch. `nextEpoch_trace` and
`nextEpoch_resources` prove that a supported returned world either halts with no
new call or appends one actual response record with its joint bill/duration.
`epochs_trace` retains the original prefix and bounds new records by the number
of epoch decisions. A halt decision adds zero records: the epoch decision index
must not be reported as the number of issued oracle turns. `resume_after_epochs`
proves equality with original native termination after any finite actual epoch
prefix followed by its native continuation.

For conditional history analysis, use `historyPrior` at a complete observed
epoch prefix. `history_kernel` instantiates `ObservedProcess.nextHistory` with
the actual stopped epoch process and factors it into a selected raw query/halt
signal and `epochResponse`. This response kernel is derived by conditioning the
full hidden checkpoint, retaining private tape/oracle correlations. Null histories
and signals use harmless completion. `epoch_disintegration` and
`epochJoint_transition` prove the joint selected-before-response and hidden
transition laws. These kernels use the actual stopping construction, not an
instruction count substituted for an oracle turn.

The geometric waiting client derives probability one of reaching the first
query, even though every finite native clock leaves positive live mass. It then
returns a correlated bit/bill/duration and halts by silent native verification,
without issuing a second call. A second actual machine never reaches a query or
halt and gives probability-one silent divergence. The two-query client retains
a work-tape bit and first response across the next query and checks the actual
correlated second reply and charge.

The quantitative client supplies a concrete source interpretation for one fixed
opportunity: the actual empty raw request on the unit channel denotes the
nonempty preformed singleton batch. Its opportunity is used exactly once, its
singleton maximum duration is the call duration, and both possible responses
return by cutoff $5$. No cancellation is left unfinished in this client. The
existing finite `SelectionPolicy.Oracle`/`Policy` tables have exactly the actual
native epoch record and terminal output/bill/duration law. A checked feasible
dual and singleton cover give certified deadline success $1/2$; expected bill is
$4$. The existing `universal_lower_cost` theorem derives cost at least $4$ for
every admissible one-turn behavioral competitor at that success target, and
the actual unbounded native selector attains it. This is an end-to-end checked
client, not unrestricted Theorem 5 or 6.

### Checked concurrent batch packets and source epochs

Import `CslibFrontier.Computability.Probabilistic.NativeBatch` and
`CslibFrontier.Probability.StochasticOracle.ConcurrentBatch.FiniteOracle`. Start with
[the correlated batch client](../../CslibFrontierTests/ConcurrentBatch.lean) and
[the actual packet-writing PTM](../../CslibFrontierTests/NativeBatch.lean).
`ConcurrentBatch.Batch n` stores one optional preformed query word for each labeled
opportunity and proves that at least one is selected. `encodeBatch`/`decodeBatch`
use the existing self-delimiting word codec, reject malformed/noncanonical packets,
and round-trip the entire selection. Response packets distinguish cancellation
from a completed empty word, retain natural token invoices and decode completed
candidate families through checked fixed-length membership masks.

`Limits` fixes positive per-opportunity cutoffs, a nonnegative absolute oracle
deadline and a turn budget. `admit` checks bytes, remaining deadline/turn budget and
unused opportunities before invoking `Sampler`. Rejections are deterministic and
have no oracle charge or source turn. The sampler may depend on the complete
source history, whole selected batch and arbitrary private state; its joint vector
of potential call trajectories need not be independent across calls or batches.
Each `CallTrace` supplies a return time/word (or no return) and a monotone accrued
token function. `observe` truncates each active call at its own cutoff and the
remaining deadline. It charges through that actual return/cancellation, sums tokens,
and takes the maximum concurrent duration. An early acceptable reply does not cancel
another call. Sequential batch maxima add. Local native computation is excluded.

`NativeBatch.execute_invariant`, `seekSource_invariant` and `terminal_invariant`
derive source feasibility, matching native/source bills and duration, and candidate
provenance from actual execution. Successful-output-only `terminal_provenance`
uses the concrete candidate-mask parser and the original selection-only admission;
no parser-validity or representation identity supplies the source protocol checks.
Source subinstance semantics and role-specific encodings remain separate obligations.

`sourceBoundary` recognizes an actual halt or a query accepted by those concrete
guards. `sourceSilent` executes malformed/repeated/exhausted requests silently and
holds an accepted whole batch before sampling. `sourceSilent_independent` proves
that this kernel cannot consult the joint response sampler (import the small
`NativeBatch.Memory` module for this latent-transport specialization). `source_disintegration`
and `source_history_kernel` derive the actual selected-before-response conditional
law and full-history behavioral kernel while retaining hidden tapes/state and null
history completion. `source_restart` and `resume_source_prefix` preserve the complete
native terminal law through any finite prefix of these source epochs. Divergence
stays distinct from a halted failure; this is not an infinite macro-process fixed-point
uniqueness theorem or a resource definition on divergent infinite paths.

For a finite joint trajectory table, `FiniteProfile` constructs `oracleAt` at a
reached remaining-deadline snapshot. Its proposals, charges and durations are computed
from the actual receipt. `serve_observation_law` and `native_dispatch_law` derive
joint quantitative observation and complete next-world laws for the encoded selected
batch. The correlated client computes expected first-batch bill $7$ and latency $5$;
its two accepted batches have total duration $8$ and bills $20$ or $6$. The native
packet-writing PTM actually constructs and submits the two-call packet and retains
the same report, hidden bit and resource law, even though it copies no reply bits
onto its output tape. It is not the source's native upper selector.

### Whole-policy native traces and quantitative kernels

Import `CslibFrontier.Computability.Probabilistic.NativeBatch.Quantitative`. The
[complete two-batch native client](../../CslibFrontierTests/NativeBatchPolicy.lean) and
[unbounded metadata/divergence client](../../CslibFrontierTests/NativeBatchMetadata.lean)
use actual finite-control native code and the fixed concurrent handler. They do
not construct a finite `FiniteProfile` as a substitute for the native policy.

`NativeBatch.Trace.State` retains the actual optional native phase and every
source-epoch receipt. An issued batch appends its actual `Exchange`; halt or silent
divergence appends `none`. This record is not a zero-cost replacement for an earlier
bill: the previous receipt list persists. `seek_state` proves that silent native
computation and rejected requests leave the accepted oracle state unchanged.
`law_hidden`, `law_resume` and `law_valid` derive actual hidden-law correspondence,
finite-prefix resumption, ledger agreement and source/native invariants.
`law_ledger_bound` retains turn/deadline/nonreuse bounds even on divergent prefixes.

`law_done` uses the concrete turn guard: a still-live returned epoch world must
already have issued at least its epoch index's number of batches, so after
`limits.turns + 1` epochs the outcome is halted or divergent. No common native
instruction clock or almost-sure local termination is assumed. `law_terminal` and
`law_native_terminal` identify this whole-policy readback with the complete original
native terminal law. `terminal_resources` gives the identical bill and physical
duration on every terminating path from an empty accepted history.
`terminal_provenance` transfers the original successful-output-only SelectionOnly
admission through the concrete candidate codec. These are proved connections, not
representation premises. `step_done` cannot issue another batch or erase receipts.

For a sequential receipt/output representation, import
`CslibFrontier.Computability.Probabilistic.NativeBatch.RecordedObservation`.
`records_law` constructs its response kernel from the actual state posterior and
proves equality with the complete native receipt law. `joint_law` also extracts an
arbitrary final private-state observation, keeping its correlation with receipts;
optional observations can distinguish divergence from an output. `expected_accrued`
preserves extended invoice means even when a later silent computation diverges.
Its recorder starts empty at the supplied world and accounts for receipts collected
from there; pre-existing charges in that world are outside the new recorder.
`terminal_law` recovers the original native terminal-world law at
`limits.turns + 1` epochs. The extra finalization epoch does not add an issued call.

The underlying `RecordedProcess` API applies to any hidden process which prepends
one record per step. Its only structural premises are an empty initial record list
and the supported append rule. The
[recorded-process client](../../CslibFrontierTests/RecordedProcess.lean) checks a
private fair output correlated with an invoice of six or eight, followed by loss of
the optional hidden state:
the output becomes absent while the expected earlier invoice remains seven.
These posterior response kernels depend on the machine. Using one common kernel
for different competitors still requires a source-state filtering argument; this
representation alone does not identify a common-oracle optimum.
The [native private-coin client](../../CslibFrontierTests/NativeRecordedRetention.lean)
shares the [singleton source fixture](../../CslibFrontierTests/NativeBatchSingleton.lean)
with the deterministic successful native client. It uses the full-response reader
to issue an actual encoded batch and run a
private-coin continuation after its reply. It derives the same invoice and physical
duration for both retained and discarded outcomes. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.RecordedProcess CslibFrontierTests.NativeRecordedRetention
```

For a separated one-interaction source filter, import
`CslibFrontier.Probability.PMF.Interaction`. `queryResponse` samples the actual
query together with policy-private state, then a complete reply together with
source-private state from a kernel which sees only the query.
`conditionalSnd_queryResponse` derives the product of the two conditional private
laws after a supported query/reply observation. Its source marginal is independent
of the policy's private query sampler. `conditionalSnd_queryResponse_update` keeps
that product after randomized local processing which reads the query, reply and
policy-private state. It does not grant access to source-private state.

The [interaction-filter client](../../CslibFrontierTests/InteractionFilter.lean)
first derives a persistent source bit's posterior probability of one-third from a
noisy answer. Fair and deterministic private query choices give the same source
posterior on their common supported second branch. A fresh private retention coin
also preserves the full product law. The counterexample drops a readable invoice
from the observation: the advertised coarse source filter stays fair while a query
chosen from that invoice identifies the hidden bit. Complete replies must therefore
include every readable resource or usage field. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.InteractionFilter
```

This is a one-step invariant. An iterated or native application still has to show
that its actual state starts with the separated product and that each public
history retains all information available to the policy. The theorem does not
establish a common response kernel for arbitrary native competitors by itself.

The iterated discrete model is available from
`CslibFrontier.Probability.PMF.Interaction.Process`. Its `Policy.choose` returns
both the query and updated private storage, so fresh selection-time coins can be
retained. `Source.step` sees the complete history, source-private state and query;
local policy processing sees the complete reply. `initialLaw` actually samples the
two private states separately, and `law` runs the existing hidden-state process
from those samples. No desired posterior factorization is supplied as a premise.

`law_factorization` derives the full actual state law at every finite horizon;
`histories_law` identifies its complete query/reply history with the explicit
sequential process. `source_posterior` then shows that, at each supported actual
history, the remaining source law is `Source.filter` of that history, uniformly
over policies. The filter retains persistent source state and uses the same
source transition throughout. The one-step update proof is shared with
`queryResponse_update_disintegrate`, rather than repeated inside the induction.

The [iterated client](../../CslibFrontierTests/InteractionProcess.lean) starts from
independent actual private states. It proves reachability of a two-turn adaptive
history, then derives source probability one-third under both fair and deterministic
private query policies. A separate check starts with deterministic policy storage
and verifies that an actual fresh selection coin is retained in the next private
state. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.InteractionFilter CslibFrontierTests.InteractionProcess
```

These are finite discrete private interactions. Relating their separated transition
to arbitrary native silent execution and its stopping/source-epoch observations
remains a further proof obligation; the model alone does not supply that native
representation or the common-oracle optimum.

The instruction-clock native connection is available from
`CslibFrontier.Computability.Probabilistic.NativeInterface.Interaction`.
It fixes an actual `Environment` and initial source-memory PMF before choosing
the native machine. Its `source` kernel reads the real complete source memory and
returns the same complete `Reply` with its word, token charge and duration. The
policy retains actual native configurations and saved selections with `Unit`
oracle memory; source-private data stays in the separate source component.
Real-world readback uses the real source memory, including any pre-existing events.

`step_world` proves that one interaction is one original native instruction. It
uses actual instruction preparation and dispatch, with the same input, tape heads,
query buffers and answer positions. `execution_native` identifies the resulting
complete native-world marginal with the original clocked interpreter, including
an arbitrary initial source-memory PMF. `execution_pure` is the ordinary fixed-world
case. `world_posterior` derives the conditional product of private configuration
and real source memory at a reached complete instruction history.
`source_posterior` reads the resulting shared source filter; its target contains
no machine or private configuration parameter. A local or halted instruction emits
a `none` request and a zero reply. A genuine query remains `some` even when its
reply word, invoice and duration are all zero.

The [native interaction client](../../CslibFrontierTests/NativeInteraction.lean)
actually writes `[true]`, issues it, then stores a fresh private output coin.
An initially hidden source bit controls the invoice and duration while both answer
words stay empty. The complete three-tick joint law checks raw buffers, private
output, real memory and resources. Both source histories are reached; their derived
native memory posteriors agree with the common filter. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeInteraction
```

`ObservedProcess.stateLaw_map` supplies the finite-clock transport and also replaces
the existing local clock induction in `StoppedProcess.terminal_map`.
`PMF.conditionalSnd_map_snd` transports supported conditionals through a hidden-state
projection. Native instruction preparation commutes with arbitrary oracle-memory
maps; no corresponding arbitrary dispatch-memory claim is used.

The instruction-clock theorem by itself does not collapse unbounded private work.
The raw-epoch connection below handles those local stopping segments. Accepted-batch
guards and the source deadline/turn-budget optimum remain further obligations.

For unbounded local computation before each raw query, import
`CslibFrontier.Computability.Probabilistic.NativeEpoch.Interaction`.
The policy actually runs the existing `NativeEpoch.seekFrom` on dummy-memory native
checkpoints until it reaches a query or committed halt; its stopping law also
retains silent-divergence mass. `seek_mapMemory` proves this law commutes with
arbitrary replacement of source memory, across private-state types and unrelated
handlers. No handler is called before the raw-query boundary, so selection remains
private even without a common local instruction clock or almost-sure termination.

The real source kernel is the same fixed `NativeInterface.Interaction.source` as
before. A saved query is dispatched with its actual complete reply; a halt or
silent divergence issues no call. Each `Outcome` keeps optional native configuration
and real source memory in separate fields. `configuration = none` denotes private
divergence; an actually halted configuration remains present. `memory` retains
all earlier invoices in either case. Its `world` projection returns the ordinary
optional native world and therefore drops ledger access on divergence. Use the
retained `memory` field for accounting on such paths.

`execution_epochs` proves that optional-world readback is the original raw epoch
process. `execution_resume` composes every finite prefix with the existing native
terminal continuation. `outcome_posterior` derives the conditional product of
optional private configuration and retained source memory at reached complete
histories; `source_posterior` gives the shared source filter even when the private
checkpoint is absent. The padding fact `filter_none` preserves that filter on a
zero-reply no-call decision.

The [raw-epoch client](../../CslibFrontierTests/NativeRawEpochs.lean) checks the real
write/query/private-output program at two query epochs. Its divergent example
first issues a fee-bearing query and then executes an actual private loop forever.
The optional configuration disappears while the rich outcome keeps the paid
invoice and duration. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeInteraction CslibFrontierTests.NativeRawEpochs
```

`Phase.mapMemory` and `instruction_memory` provide shared memory facts used by the
raw selection proof and existing native clients. `ObservedProcess.stateLaw_map_pure`
replaces both repeated native inductions for an observation which stays fixed along
every step; the existing raw-memory and accepted-server-memory callers use it.

These epochs count actual raw requests. A request rejected by a source's batch
protocol is still a raw request here. Skipping such rejections, relating the
filtered private state to accepted-batch histories, and transferring the physical
source turn/deadline optimum remain separate obligations.

For transport through the actual accepted-batch selector, import
`CslibFrontier.Computability.Probabilistic.NativeBatch.Memory`.
`ServerState.mapPrivate` changes only latent source state and preserves the public
accepted history, used opportunities and elapsed time. `Memory.mapPrivate` also
preserves every raw event. Consequently `admit_mapPrivate` keeps the concrete
admission decision unchanged, and `sourceBoundary_mapPrivate` preserves the next
accepted-batch/halting boundary.

`sourceSilent_absorbs` names the selected-boundary holding law for stopping-process
reasoning. `sourceSilent_mapPrivate` commutes actual silent native steps with this latent-state
mapping, across private-state types and completely unrelated samplers. Admitted
queries are held before sampling; rejected queries receive the same deterministic
rejection on each side. A rejection appends a raw zero-charge event, so the entire
native memory is not invariant. The map preserves those events while the accepted
server state stays fixed. `seekSourceFrom_mapPrivate` lifts this one-step law to the
actual unbounded stopping distribution, including silent divergence, and
`sourceSignal_mapPrivate` preserves its selected accepted-history/batch signal.
The earlier `sourceSilent_independent` theorem now lives in this small module and
is derived from the identity-map case, replacing its separate case proof.

The [accepted-selector memory client](../../CslibFrontierTests/NativeBatchMemory.lean)
checks an actual malformed query and its rejected response, retained raw log and
unchanged accepted ledger, then transports the resulting stopping law between
latent-state types. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeBatchMemory
```

This transport does not yet give an accepted-epoch source posterior. In particular,
full source `Exchange` histories include per-call time vectors that native reply
bytes need not reveal. An enriched-history filter must justify its projection to
native observations; a native-visible filter must retain unrevealed data privately.

For a fixed discrete source across generated native accepted-batch policies, import
`CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction`.
The source stores real latent state. The native policy carries its full checkpoint
with dummy latent state and runs the actual unbounded accepted selector. Requests
contain only the accepted public snapshot and selected batch; they contain no native
tapes, raw event log or latent state. `ConcurrentBatch.Interaction.draw` samples
one joint trajectory vector and successor, and `draw_serve` recovers the original
guarded reply/server law for an admitted request. Both the receipt and successor
come from the same draw.

The analytical reply is the full `Exchange`, including its per-call stop times.
`advance` passes only `replyOf` to native channels and commits the full receipt in
the dummy accepted ledger. `step_trace` proves exact original native trace readback;
`execution_trace` lifts it to every finite accepted-epoch horizon. Earlier accepted
receipts remain in the analytical history when the private checkpoint diverges.
This retains their bills and durations without claiming to recover an infinite raw
log of rejected requests. `execution_terminal` recovers the original unbounded
native terminal law after the source turn budget plus one halt/divergence decision.

`execution_histories` uses one shared source filter in the explicit sequential
history law; only the generated private query policy depends on the machine.
`source_posterior` derives the retained latent-state posterior at supported complete
histories, including divergent private checkpoints. These histories are enriched
analytical observations. The theorem does not identify that posterior with a filter
conditioned only on the machine-readable reply bytes.

An arbitrary generic interaction policy could forge a request's snapshot.
`execution_ledger_bound` instead proves turn, deadline and nonreuse feasibility for
the generated actual native policies, using the existing native trace invariant.
This supplies a fixed-source realization for that class; the final source-envelope
and common-oracle optimum instantiation remain open.

The [accepted-interaction client](../../CslibFrontierTests/NativeAcceptedInteraction.lean)
uses the existing singleton source and the shared ordinary
[native packet-writing program](../../CslibFrontierTests/NativeBatchProgram.lean).
The actual program writes both packet bits, issues its admitted batch, then returns
the singleton family. A latent source bit selects invoices of two or four with the
same family word and duration. The checked complete histories distinguish those
invoices and recover the corresponding source posterior; native terminal readback
uses the original interpreter. The older successful-batch and retention/deadline
clients also use the extracted program. The existing `Trace.law_hidden` projection
uses `ObservedProcess.stateLaw_map`, matching the new full-trace transport and
removing its separate clock induction. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeAcceptedInteraction CslibFrontierTests.NativeBatchSuccess CslibFrontierTests.NativeRetentionDeadline
```

To transfer primitive bounds on that fixed source to actual native conditional
means, import
`CslibFrontier.Computability.Probabilistic.NativeBatch.Interaction.Envelopes`.
`selectionViews` retains each actually selected private checkpoint and enriched
history while erasing latent source state. `selection_trace` and
`selection_observations` recover the existing native selected checkpoint and
observation laws. `selectionViews_valid` derives the actual request and boundary
properties from execution; these are not caller-supplied admission identities.

`conditional_filteredSource` expresses native conditional dispatch as a mixture
over selected private views, followed by the same `source.filter` at each view's
enriched history. A coarse native observation may mix several such histories;
the theorem does not replace that mixture with a single history filter.
`conditional_reward` averages any history-dependent nonnegative receipt score
under these fixed-source response laws. It covers unbounded invoices, infinite
means and null-observation prior completion. `conditional_reward_le` and
`conditional_reward_ge` transfer upper and lower primitive means at positive-mass
native observations. `conditional_records` transfers supported receipt properties
and retains the exact preceding receipt history. The positive-mass premise is
needed to identify that history and the actual issued-source flag.

The general probability facts are in `PMF.Interaction.Selection` and
`PMF.Disintegration.Map`. The actual selected law preserves correlation between
the query and fresh private storage while keeping the source under its history
filter. Conditioning on any observation of that private view retains the attached
source filter. Deterministic state projections commute with the posterior, including
null completion; supported posterior states remain within prior support.
`Selected.checkpointState` forgets the old private configuration after selection,
retaining all checkpoint/receipt data used by native observation and response.

For the existing native token optimum, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.SourceEnvelopes`.
`SourceEnvelopes.LowerBounds` states primitive newly revealed-cardinality,
progress-probability and invoice-mean bounds under the one fixed source's
`draw` kernel. Its domain is the actual supported selections of the existing
finite-control, selection-only native class. It does not impose bounds on forged
snapshots, nor assume a native conditional mean or lower-optimum conclusion.
`LowerBounds.toNative` derives the existing native lower envelopes using the
transfer theorems; `SourceEnvelopes.lower` then applies the established native
optimum bound. The original issued-turn cap, optional failure readback and
successful-only provenance admission are preserved.

These are conditional resource theorems: privacy/filtering does not establish
numerical productivity or invoice envelopes for a source. Chosen-policy upper
productivity and retention, concrete source instantiation and the full common-oracle
comparison remain further work. The Operator's Manual's source-envelope API does
not expand the model to arbitrary measurable kernels or compile arbitrary PMFs.

`NativeBatch.Quantitative.select` executes silent native code and holds the entire
selected source batch. `Observation` retains its full receipt history and source
signal. `conditional` conditions the actual hidden checkpoint and then dispatches
the same oracle response; null observations use harmless completion.
`selection_factor` recovers the actual whole-policy transition. Positive conditional
support stays on the actual observation fiber, and `conditional_issued` proves one
issued batch for a query signal and zero for halt/divergence. The hidden tapes,
private oracle memory and auxiliary response/usage metadata need no finite alphabet.

`expected_accrued` proves that expected summed receipt resources equal the sum of
those selected-before-response conditional expectations. Expectations take values
in nonnegative extended reals, so unbounded or infinite expectations require no
integrability premise. `conditional_comparison` transfers supported local resource
comparisons. In particular, `cost_lower` and `cost_upper` derive
$c\,\mathbb E[T] \le \mathbb E[\mathrm{bill}]$ and
$\mathbb E[\mathrm{bill}] \le c\,\mathbb E[T]$ from the corresponding conditional
cost envelopes on positive-mass selected batches. `cost_upper_budget` derives
finite expected bill at most the finite conditional envelope times the actual source
turn budget, without counting the extra halting decision. It does not assume
integrability or a bounded total invoice. `complete_expected_step` checks
that another no-call decision after the full budget changes no such resource.

For universal accounting, use `Trace.startWorld` with a fixed oracle seed.
`universal_cost_lower` fixes `limits`, `sample` and that seed before quantifying
over native machines and inputs satisfying the original SelectionOnly admission.
It covers finite-control binary-tape competitors without needing finiteness in
the resource proof. The same hidden-state oracle is used across all
histories and competitors; different actual posteriors do not change that oracle.
Each competitor requires only its own reached conditional cost envelope; the API
does not demand envelopes on additional machines or null histories. No total
cost lower bound, finite sufficient abstraction or law equality is assumed.
`conditional_of_response_bound` is an optional sufficient rule for concrete oracles;
it does not strengthen the transfer theorem to require pointwise hidden-state bounds.

The native client actually writes both nonempty packets, retains a correlated bit
across two batches and performs local halting. Its complete law has three decisions,
two issued batches, expected bill $13$ and latency $8$. Conditional bill envelopes
$3$ and $11$ are proved for every reached selected-history signal and yield the
whole-policy comparisons. The metadata client samples a geometric natural number,
shares it across calls and retains it for later batches. Every invoice scale has
positive mass; no finite alphabet can losslessly preserve its invoice observations.
It proves a per-issued expected cost lower envelope $1$ for every admitted native
competitor against that fixed oracle. A genuine silent-loop suffix preserves an
already charged first receipt rather than turning its previous bill into zero.

### Native revealed progress, coverage and stopped costs

Start with `CslibFrontier.Computability.Probabilistic.NativeBatch.Retained`. The complete
[correlated native progress client](../../CslibFrontierTests/NativeBatchProgress.lean)
and [successful selection-only machine](../../CslibFrontierTests/NativeBatchSuccess.lean)
include their imports, concrete code, instances and envelope proofs. From a warm
checkout, build them with:

```bash
scripts/build.sh CslibFrontierTests.NativeBatchProgress CslibFrontierTests.NativeBatchSuccess
```

This is targeted development validation, not the full six integration gates. Each
example uses actual source packets and receipts.

`History.conditional_records` proves that responses at positive-probability selected
observations extend the entire observed receipt history. `History.expected_sum`
handles nonnegative rewards depending on that history, rather than only static
invoice scores. `ProgressComparison.count_upper` and `count_lower` compare all
nonnegative increasing count payoffs with independent Bernoulli comparison trials.
Only the exact Boolean progress indicator is pushed forward; the response law,
private storage and actual response correlations are preserved. Envelopes are needed
only at reached selected observations, including a harmless kernel completion at
null histories. `History.final_not_issued` and `final_records_mean` prove that the
extra silent completion epoch appends no issued receipt and preserves earlier
receipt resources and progress.

For a set-cover instance with candidate indices `Fin m`, `Coverage.proposal` decodes
all completed response proposals. `revealed_source` identifies its actual revealed
coverage with the provenance ledger. Use `revealed_card_bound` with a new-coverage
cap on positive selected-response supports; no cap on impossible histories is needed.
`success_count` then derives the number of revealed-progress epochs required by an
actually decoded native accepted output, using the original SelectionOnly admission.
Supply an acceptance predicate that counts only covers; it may additionally require
the source weight certificate. Admission is required only on that predicate, not on
covering outputs which fail the requested certificate.
`success_law` identifies that event with the original unbounded native terminal law.

`Coverage.success_cost_lower` proves
$\eta r_b c/p \le \mathbb E[\mathrm{bill}]$, where $\eta$ is the actual native
accepted-cover probability, including any requested weight certificate. Its inputs
are the local coverage cap, the per-issued
selected progress upper envelope, the per-issued conditional invoice lower envelope,
a positive finite $p$, and the original native admission. The required progress count
and cost lower conclusion are proved, not premises. `revealed_envelope` derives zero
progress on halt/divergence padding. `success_binomial` bounds actual native output
success by the binomial tail for `limits.turns`, with no extra trial for completion.
Import `CslibFrontier.Computability.Probabilistic.NativeBatch.Deadline` for the exact
physical deadline refinement described below.

`Retained.completion` takes an explicit receipt parser and uses the existing local
dual retention test and residual-count proof to obtain actual retained-cover
probability at least the binomial upper tail. Candidate indices need not form a
finite type: each proposal and the ground set are finite. Existing finite-mask
clients pass `Coverage.proposal m`; runtime row-index clients use
`NativeRetention.BatchReceipts.proposal x`.
`failure` gives its survival complement. `cost_tail_sum` uses the operational
stop-at-retained-cover contract and selected invoice upper envelope to bound the
actual accrued bill by $c$ times the binomial survival sum. `cost_mean` derives the
bound $c r_a/p$ from the proved finite tail-sum estimate. `complete_cost_mean`
transfers that bound to the complete actual receipt ledger, requiring envelopes for
only the issued-turn budget; `History.final_expected_static` removes the final silent
completion epoch. These results assume neither
an expected stopping mean nor an integrable/bounded total bill. The productivity
envelope includes no-call decisions: a native machine that halts or diverges before
completion generally fails it. For the constructed block selector,
`NativeRetention.BatchUpper.upper_controller` derives this no-call
extension from actual stopping and needs source productivity only on issued batches.
The final certified-output success-event transfer and common-oracle optimum
comparison remain separate assembly obligations.

The progress client derives its posterior envelope from a real concurrent batch,
with nonempty coverage probability $1/2$, shared private randomness, cancellation
charges and computed conditional mean cost. The success client writes its packet,
issues one opportunity, writes a covering output and halts. It proves its original
SelectionOnly admission for every finite clock and instantiates both positive cost
bounds and the single-trial native binomial bound at $p=1$. These clients establish
nonvacuity; they do not implement the source's uniform upper policy on all instances.

### Native physical deadline transfer

Import `CslibFrontier.Computability.Probabilistic.NativeBatch.Deadline` and use the
same actual machines, sampler and initial oracle state as above. The
[two-batch client](../../CslibFrontierTests/NativeBatchPolicy.lean) now proves its
latency envelope from real concurrent receipts, including the absolute-deadline
cancellation in its second batch. The
[successful native client](../../CslibFrontierTests/NativeBatchSuccess.lean) applies the
assembled guarantee to its proved admission and actual output code. Build both
from the warm checkout with:

```bash
scripts/build.sh CslibFrontierTests.NativeBatchPolicy CslibFrontierTests.NativeBatchSuccess
```

`Deadline.LowerLatency` is the source almost-sure batch lower envelope on positive
selected observations and supported conditional responses. Only issued batches
require a positive latency. It uses the actual maximum concurrent duration, not
an instruction count or a sum of concurrent call times. `latency_sum_lower` adds
this envelope along supported native histories; `issued_bound` combines it with
the concrete source deadline guard to bound actual issued count by
$v=\min(u,\lfloor D/\ell\rfloor)$, represented by `effectiveTurns` on nonnegative
real interface clocks.

`issued_live` proves that a source response resumes at the actual native query
continuation. A live epoch must already have issued at least its index's number
of batches. Combining these facts with the duration bound proves `no_call_after`:
no actual selected signal can issue a batch at or after $v$. This is a derived
execution constraint, not a supplied physical turn cap. `records_mean_stable`
then transfers all nonnegative receipt observables invariant under no-call padding
back to epoch $v$. In particular, earlier bills, durations and revealed progress
survive later silent halting or divergence; hidden local computation need not stop
by a common instruction clock.

Use `Deadline.lower_guarantees` for the assembled lower transfer. Its acceptance
predicate may require the desired weight certificate and must imply coverage.
The hypotheses are original native SelectionOnly admission, an empty initial
accepted ledger and its invariant, reached coverage/progress/cost envelopes,
and `LowerLatency`. It proves the success-level expected-bill lower bound and the
necessary binomial probability bound at $v$. `nativeByDeadline` explicitly tests
both decoded native acceptance and the original native elapsed resource.
`terminal_duration_le` and `deadline_success_law` prove from the actual protocol
that adding this deadline test loses no accepted terminal mass. Neither a desired
success/count implication nor deadline/truncation law is a premise.

`zero_deadline_failure` covers the boundary $D=0$ for every admitted native policy
on a nonempty ground set, without progress/cost/latency envelopes. Admission rejects
all batches before sampling, so no accepted nonempty cover is possible. This result
does not exclude a successful empty cover on empty ground. Floor-boundary clients
also check that a physical allowance can be smaller than the independent turn guard.
These deadlines exclude local computation time, as in the paper. Compiled physical
clock semantics and the infinite-instruction path-cost limit remain separate.

### Uniform native local certification and retention

Import `CslibFrontier.Probability.StochasticOracle.NativeRetention.Execution`. The
[complete local-phase client](../../CslibFrontierTests/NativeRetention.lean) contains
runtime data, checked dual feasibility, accepting/rejecting proposal cases and a
connection to an actual correlated source receipt. From a warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRetention CslibFrontierTests.StochasticOracleSelectionPolicy
```

`NativeRetention.Input` contains incidence rows, candidate weights, element dual
prices, the local factor and chronological decoded proposal lists. Its encoding
uses unary element/candidate indices and binary rationals. The dual vector's length
defines the finite ground; missing rows are empty and missing numeric entries are
zero. Normalization discards duplicate and out-of-range candidate indices. No
native machine, acceptance table, claimed output family or resource certificate is an
input field. `certified`, `step`, `retain`, `complete` and `output` compute the local
operations by list scans and exact rational arithmetic.

`computable_decision` compiles the completion decision and retained mask uniformly
for all runtime sizes. The fold's accumulator bound is derived from the enumerated
candidate universe. `compiled` extracts a fixed binary finite-control machine from
the proved native composition certificate; machine existence is proved, not an
assumption supplied by a caller. The executable list algorithm can be evaluated;
the proof-extracted machine is not an exported transition-table artifact. Its
polynomial local time and space are measured in the entire encoded local input,
including every proposal occurrence and rational bit. This is not a runtime bound
on a full oracle policy or on reading an unbounded oracle reply.

`Valid` expresses standard nonnegative-weight/dual and dual-feasibility promises,
not a desired output property. The native program does not read these proofs or
receive a precomputed local acceptance table. `instanceOf` interprets the runtime
rows as the real-valued set-cover instance. `certified_eq` and `retain_eq` prove
exact agreement with the original local dual test and retention operator.
`retained_provenance` proves that no unproposed candidate is introduced.
`complete_eq` derives ground coverage from the computed completion test, and
`completed_output` derives the actual family's dual-weight guarantee. The shared
`PartialCover.Instance.retain_subset` lemma is now reused by the behavioral
selection-policy admission proof rather than remaining private there.

`output_encode` and `decode_output` identify the emitted mask with the existing
source family codec. `native` embeds the compiled local code as an ordinary open
PTM. `terminal_local` proves actual unbounded native termination and decoded output
against any stateful oracle, without a termination premise. `terminal_cover`
assembles this execution with the coverage and certificate when the computed
completion decision is true. All existing oracle memory and both resource meters
remain exactly unchanged; no oracle call is issued by the local computation.

The source client serializes proposals from an actual canonical concurrent report,
excluding canceled calls. It checks the two correlated output/completion cases and
runs the generated local machine with the existing source memory, including its
cancellation invoice. This serialization is currently a semantic data conversion.
The local theorem starts with `encInput` already on its input tape. The native
reader copies the full reply to a work buffer. The later `BatchPlanner.controller`
composes original-input loading, parsing, runtime-context updates, source-batch
planning, local retention, repeated guarded execution and final tape output.
`BatchOutput.upper_controller` proves its certified success/deadline and bill
bounds. `BatchOptimum` proves lower/upper/competitive bounds for OPT over admitted
finite-control selection-only native machines sharing the oracle and seed.
The local phase alone is not the successful upper-policy witness; the complete
named implementation and its proved joint feedback law are used. No finite
response/metadata approximation or publicly available offline proposal list is
assumed.

The fixed block scheduler, original runtime codec and configured finite opportunity/
cutoff interface restrict the implemented model. Unrestricted source WSC subinstance/role and
residual-label codecs and unrestricted external PTM representation remain open.
A latent scenario is never assumed publicly visible.
Fixed finite call opportunities and external nonnegative real clocks remain interface
conventions; compiled physical timers and general measurable/nonatomic laws are not
established. The trace preserves divergent mass and its earlier receipts, but equality
with a cofinal infinite-instruction path-cost law and real integrability are separate
obligations. Divergence has no native terminal-world bill.

Theorem 4's concrete incidence/query adapters and native greedy/every-vector
execution guarantees are proved above, as is the constant-factor hardness transfer; the
$(1-\varepsilon)\ln n$ factor remains blocked on #4335. Neither unrestricted
Theorems 5/6 nor ALL-main is complete. No selected abstract model or statement
changes.


### Complete raw-interface adaptive retention program

Import `CslibFrontier.Probability.StochasticOracle.NativeRetention.Selector`. The
[complete two-turn client](../../CslibFrontierTests/NativeRetentionSelector.lean)
constructs the scheduler, original source batches and correlated oracle, then
checks the entire program's actual result and joint resources. From a matching
warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRetentionSelector CslibFrontierTests.NativeRetention
```

`NativeRetention.Selector.program choose input budget` is a `ProbOracleComp`
program on the original unit-channel bit-string interface. The scheduler is closed
randomized program code returning a nonempty preformed `ConcurrentBatch.Batch`
or an explicit halt. It receives the runtime rows, rational data and full visible
history, including prior requests and all invoice bits, and an unbounded word of
private scheduler storage. Its decision carries updated storage, so private random
choices remain available on later turns. It cannot inspect hidden oracle memory or
make additional external calls. The selector issues each query itself, decodes the
actual complete reply, recomputes local retention and tests completion before
selecting another batch. Caller-supplied `input.proposals` are ignored. A successful
result is the original family mask; incomplete termination returns `none`.

`run_joint` and `program_joint` derive the exact joint execution law with arbitrary
stateful oracles. They keep every response/private-state/resource correlation;
there is no finite metadata alphabet or independent-response assumption.
`run_invariant`, `run_resources` and `program_correct` apply the original guarded
source handler to derive feasibility, the exact source bill and duration ledger,
selection-only provenance and the feasible-dual certificate of successful output.
They require the usual input dual promises, not a supplied selector correctness or
success guarantee. Invalid/reused/deadline-exhausted source requests are rejected
by that handler, receive no proposals and consume no issued source turn. The
program's finite budget counts selection attempts, including rejected attempts.
A scheduler may also halt prematurely. Thus the code alone does not establish a
positive productivity envelope or the theorem's upper success probability.

In the checked client, the first batch reveals one of two proper partial covers
and bills a canceled companion. The next raw query asks for the missing part using
only the visible first response. The same hidden bit persists across both batches;
a wrong query would receive no valid proposal. Both branches produce the full cover
with bill 9 and external duration 3. Additional checks cover random initial hidden
state, cancellation, completed-state stopping, empty ground and ignored fabricated
initial proposals.

This is an executable program and source-semantics connection, not a compiled
native adaptive selector. `NativeRetention.compiled` still realizes only its local
phase. The strict oracle-PPT calculus only copies a supplied bounded reply prefix;
it cannot read an arbitrary invoice followed by later proposal slots under an
input-only polynomial clock. The unbounded native reader and sequential laws
below remove that common-clock obstruction. The later `BatchPlanner.controller`
composes the parser, local preparation, batch scheduler and full guarded loop for
the concrete supported scheduler. Its native upper probability/cost and optimum
results are proved in `BatchOutput`/`BatchOptimum`; they do not follow from an
assumed realization of the raw program. The source excludes local computation
from its deadline, so the stronger strict-PPT clock is not a source requirement.


### Native full replies and unbounded phase composition

Import `CslibFrontier.Computability.Probabilistic.NativeQueryAll`. It also exposes
`NativeSequential` and `NativeOutputBuffer`. The
[complete native source client](../../CslibFrontierTests/NativeQueryAll.lean) starts
from actual machine configurations and checks real concurrent response packets,
cancellation charges, unbounded geometric invoice metadata and native halting/
diverging continuations. From a matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeQueryAll CslibFrontierTests.NativeRetentionSelector
```

`NativeQueryAll.machine op k` is one binary finite-control machine. It scans the
request on its input tape, writes the selected query buffer, issues exactly one
call and copies answer cells until the actual blank boundary. `terminal_query`
identifies its whole unbounded native terminal law with the very same response,
private state and event/resource update. It neither bounds the response length nor
assumes a terminating clock. `query_readback` identifies its output/memory with the
original raw handler's joint query result. `terminal_from` runs the phase with
arbitrary retained work tapes, output prefix and other channels: control must be
`write`, the input cursor must be at position 1 and the selected query buffer empty.
It leaves other channels and work tapes unchanged. The returned cursor is at the
right input boundary; it is not a tidy input-head-restoration theorem.

`NativeOutputBuffer.execute_buffer` derives the existing native output compiler's
whole finite-clock law. `terminal_buffer` lifts it to unbounded stopping, preserving
all divergence, hidden state and joint resources. The general mathematical lemma
`StoppedProcess.terminal_map` derives this from exact one-step simulation and
matching halting predicates; injectivity, finite state and a common terminating
clock are unnecessary. A configuration map in this proof is a representation of
the compiled execution, not a free runtime copy operation.

For the reader, `buffered_start` proves that the actual output-buffered machine
starts with a blank buffer. `terminal_buffered` identifies its final real work
tape with the full raw reply. `NativeOutputBuffer.buffer_contents` locates the word
on `Fin.last k`, with its head at the write frontier and the ordinary output empty.
The compiler performs the writes: no response value is installed by a premise.
`finish_resources` adds exactly the actual response charge and duration to the
previous resource ledger; local reading does not add oracle resource charges.

`NativeSequential.terminal_seq` proves the exact law of the existing native `seq`
compiler. It transfers all tapes/channels and the same oracle memory to the second
machine. Either phase may diverge or take an unbounded response-dependent number of
instructions. `NativeQueryAll.terminal_then` specializes this to full-reply reading;
`terminal_buffered_then` passes the real work buffer to arbitrary actual native
continuation code. These are compiler theorems, not assumed source-validity or
machine-to-program representation contracts.

Import `CslibFrontier.Probability.StochasticOracle.NativeRetention.Packets` for
native processing of full raw histories. Its `Work` input contains original rational
rows/certificate data, a unary opportunity count and the newest-first raw response
words. It ignores any initial decoded proposal list. `computable_decision` compiles
slot scanning, source-mask validation, rational local certification/retention and
the computed completion flag/mask as one native algorithm. Local time and workspace
are polynomial in the encoded runtime bytes, including invoice metadata.
The original total self-delimiting decoder is computed by capping each numerical
length at the remaining payload: huge malformed headers require no huge unary
counter and do not change `take`/`drop` results.

`Packets.assemble_run` derives parser agreement on every supported actual guarded
program history, with arbitrary closed randomized scheduling and correlated oracle
state. It makes no claim of agreement on arbitrary malformed report words.
`terminal_run` proves actual unbounded native local stopping and the identical
computed flag/mask. `run_native_law` gives the exact joint law of actual raw program
execution followed by that native local computation, preserving all hidden state
and resource observations. The
[correlated two-query client](../../CslibFrontierTests/NativeRetentionSelector.lean)
checks both complementary-cover branches, cancellation billing, ignored fabricated
proposals, rejection and empty ground. From the same warm starting point, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRetentionSelector
```

There is a proved obstruction to applying the current clocked tidy-loop API here.
`NativeQueryAll.clocked_ne_query` uses the existing one-output-bit-per-instruction
bound: a genuinely supported response longer than `fuel` prevents **any** native
machine at that clock from emitting the exact joint raw query word/memory law.
This does not deny atomic installation of that word on a native answer channel;
the obstruction concerns copying the full word to ordinary output.
The test-local full-query obstruction rules out the unrestricted `ComputesTidily`
premise at every finite clock: that predicate quantifies all handlers. The complete native source client derives such responses for every `fuel` from
one fixed geometric-invoice oracle, not from a family of oracles chosen after the
clock. The actual guarded source still emits valid cover proposals.

Consequently `ComputesTidily.comp_of_le` and `ComputesTidily.iterateWhile` cannot
compose this full reader using one uniform finite local clock. Finite external
latency or a finite turn budget does not bound local packet-reading work; local
instructions are excluded from the source deadline. The existing unbounded reader
law remains valid. This is an obstruction to that clocked API route, not a theorem
that the native selector cannot be implemented. A stopped-law loop must establish
its actual word-buffer/cursor/workspace invariants at each restart without a common
clock. Also, `Selector.Scheduler` is an arbitrary input/history-to-closed-program
function: pointwise closed syntax does not supply uniform native scheduler code.
Do not infer such code from that type alone.

For an actual reader-to-continuation program, import
`CslibFrontier.Computability.Probabilistic.NativeResponseExecution`.
`NativeResponseExecution.machine continuation` sequences the full reader/output
buffer, real native marker/rewind code, and virtual-input continuation. The flag
tape starts blank; preparation takes the received word's length plus four local
instructions. `terminal_machine` derives the entire stopped native configuration
law from these instructions. It preserves arbitrary continuation divergence,
channels and shared memory. The continuation starts with its own work tapes blank,
the received word on its virtual input, and the real input head at the request's
right boundary. No caller supplies a prepared intermediate configuration.

For retained ordinary storage, use `Workspace`, `startFrom`, `localStartFrom` and
`terminal_from`. The same compiler now preserves arbitrary ordinary tape functions
and nonzero head positions; the fresh response/marker tapes alone start blank.
`localStartFrom_workspace` states that preservation directly. The old
`terminal_machine` remains the blank-storage entry, rather than silently changing
its initial-state convention.

Import `CslibFrontier.Computability.Probabilistic.NativeRuntimeContext` for a concrete
runtime transport client. `restoringProgram` is one finite-control program for all
context words, supplied once on its entry work tape: it issues the initial request,
receives the complete first reply,
appends its frame to the context on ordinary tape zero, submits that updated word
as its second request and receives the complete second reply. Native virtual-input
rewinding moves both inner heads back to zero, and native marker erasure leaves
the inner flag blank. `terminal_restoringProgram` gives the entire joint stopped
world law; `restoring_program_observation` reads the updated context tape, output,
head, reusable inner flag and the same oracle memory. Neither theorem assumes a
representation law, successful cover, finite reply alphabet or independent calls.
Local instructions add no oracle invoice or external duration. This is a native
resume-world entry, not a loader from the original instance encoding.

`Header` has an injective byte format for the original encoded instance, old raw
request/reply histories, private selector word, remaining turns/opportunities and
stop/output data. A framed header followed by framed replies has a checked byte
roundtrip. The concrete transducer appends the new reply trailer; it does not
interpret or update the header's control fields. The supported scheduler simply
submits the updated context word, which is not in general an admitted source batch
encoding. The outer first-response buffer/flag remain retained. General buffer
reuse, repeated adaptive selection, source admission and semantic budget/stopping
updates are still open; this is not a complete native selector or Theorem 5 upper
bound. See the [complete context client](../../CslibFrontierTests/NativeRuntimeContext.lean)
for one correlated geometric source, genuine unbounded reply lengths, both
context/reply-dependent second requests, unchanged joint invoices, empty words and
zero charges. From the same matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRuntimeContext
```

For initial loading, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.InitialContext`.
`Startup` encodes the original rational instance with runtime unary turn/opportunity
counts and a private selector word. It contains no precomputed context or machine
witness. The native initializer computes the header, clears scratch storage, writes
the reserved context tape, rewinds that head and restores the real input head before
entering the runtime carrier. Initial completion ignores caller-supplied proposals;
the stored stop bit also records zero turns or opportunities. This bit is computed
from the original input, rather than supplied as an input certificate.

`exists_original_input_runtime` constructs one finite native machine for all startup
inputs and all shared-state response kernels. Its execution starts at the ordinary
blank-work-tape `machine.initialConfig`, not `restoringEntry` with an installed
context. The actual two-query law and both invoices/durations remain unchanged.
The reusable `NativeContextLoader.exists_load_then` derives loading followed by
any actual four-tape consumer, including divergent consumers; its computational
premise concerns only the pure initializer. It assumes no consumer success or
representation law. The concrete initializer's computability is proved internally.

The [original-input client](../../CslibFrontierTests/NativeContextLoader.lean) checks one
machine for all runtime inputs against a fixed correlated geometric source with
unbounded reply lengths, original-instance readback in the actual second request,
a nonempty feasible-dual instance with ignored fabricated proposals, zero allowances
and empty ground. From the same matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeContextLoader
```

For initial stopping, use `exists_guarded_original_input`. It constructs one finite
native machine from the same original input, writes a dispatch bit and framed
output before the retained header, then reads that bit with native instructions.
A true computed bit emits the stored mask and halts without calling the oracle;
prior oracle memory and its resource ledger are unchanged. A false bit enters the
actual two-query carrier on unchanged context tapes, preserving its unbounded
execution and correlated joint resource law. `NativeStopGuard.terminal_stop` and
`terminal_go` provide the reusable transition-level branch laws without assuming
consumer termination or success.

The [native guard client](../../CslibFrontierTests/NativeStopGuard.lean) checks this
same blank-tape machine on zero turns, zero opportunities, and empty ground with
a nonempty candidate list (returning the all-false mask). Its live branch uses a
single correlated source with arbitrarily long positive-probability replies.
From the same matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeStopGuard
```

This closes initial stop enforcement for this binary startup ABI. The older
`exists_original_input_runtime` remains the unconditional transport API. Neither
API loads a conventional external source/PTM encoding or generates an admitted
batch from the original instance. After an initially live dispatch, the guarded
machine still makes two raw calls without checking completion or allowances
between them; even a one-turn allowance can therefore be exceeded. Semantic
post-response history/private-control/budget updates, deadline stopping, repeated
buffer cleanup/restart and the native quantitative upper/optimum endpoint remain
open.

For uniform semantic postprocessing, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.RuntimeControl`.
`RuntimeControl.State` stores the original rational input, total parser opportunity
count, stored raw histories, private word and remaining turn/planning/allotment
counts. `afterReply` appends the actual request/reply history, appends the framed
reply to the private word, decrements the three allowances, and recomputes rational
retention, completion and output from the full raw report. `process` produces the
updated guard bit, framed output mask and encoded next state.

`exists_native_processor` constructs one native local program before quantifying
over states or replies. Its instructions splice the retained tape context with the
actual complete reply, erase the old context, restore cursors, execute the uniform
parser/processor and write the updated guard packet back to tape zero. Local
scratch, temporary combined-input work tape and marker finish blank with heads
restored. The immutable input is preserved. These
are response-dependent terminating local computations, not a common clock for
copying every possible response.

`exists_native_phase` also constructs the input-loading/query/full-reader/local
composition. It starts at `program.initialConfig (frame (encoding state))` with
blank work tapes; no context is embedded in code or preinstalled on a work tape.
Its named `NativeReplyContext.Observation` retains the actual context tape, ordinary
output and complete shared oracle memory. Private context bytes are not emitted;
the ordinary output is empty, and the eventual mask is stored in the new packet.
The exact law preserves the sampled response, hidden-state transition, invoice and
oracle duration jointly.

The [runtime-control client](../../CslibFrontierTests/NativeRuntimeControl.lean)
checks a nonempty two-row locally certified cover, ignored fabricated proposals,
cancellation, correlated hidden state and unbounded invoice reports. It checks all
three exhausted counters and observes the recomputed stop bit on the actual native
tape. From the same matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRuntimeControl
```

This older API executes one post-response phase and always issues its one query,
even on already stopped input. To execute the initial guard and convert original
input to the runtime ABI, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.GuardedStartup`.
`GuardedStartup.Input` contains the original `Startup` and a reservation allowance,
with no supplied history or prepared State. `exists_guarded_phase` constructs one
program before quantifying over those inputs, the oracle and its hidden memory.
Starting with blank work tapes, it computes the guard packet. Initial completion
or zero turn/planning/reservation counts take the actual stopping branch, emitting
the computed output while preserving the entire prior oracle ledger. The live
branch clears the packet, computes the fresh State from the original input, and
uses native marker/virtual-input execution to run the full query/updater. The
returned observation contains the actual updated packet, ordinary output and
hidden oracle memory jointly. Its live branch now uses
`FinalizedResponse.exists_native_phase`, which executes the updated guard after
the full reply and uniform semantic update. The actual native reader checks the
new packet on retained response channels, emits the computed mask on stopping,
and otherwise enters a silent terminal continuation. It issues no second query.

`RuntimeControl.HistoryMatches` relates stored raw requests/replies/private bytes
to actual native events. `initial_history_matches` and
`afterReply_history_matches` establish initialization and preservation for the
actual framed-State request. The [guarded startup client](../../CslibFrontierTests/NativeGuardedStartup.lean)
checks the compiled code on initial completion, each exhausted allowance,
nonempty cover and a single hidden-state source with arbitrarily long correlated
reports, including the observed history invariant. The same compiled program
now emits the locally retained nontrivial cover mask on a successful report and
no mask on cancellation, keeping the actual unbounded invoice and duration jointly.
Exhausted turn/planning/reservation and empty-report cases exercise the final guard.
From the same warm checkout:

```bash
scripts/build.sh CslibFrontierTests.NativeGuardedStartup
```

This closes initial guarded ABI conversion and one-response final dispatch,
not repeated feedback. Its request remains framed runtime-state data, not a proved
source-admitted batch packet. The opportunity count is a
single-opportunity planning allowance, not a verified consumed-opportunity ledger
for arbitrary concurrent batches. Allotments reserve latency units; the native
interface does not expose the ledger's real elapsed time. A live final packet's
payload must still be handed to a source-valid next batch planner. These one-phase
APIs do not restart; the raw-State feedback controller below supplies native
cleanup/re-entry. Neither final emission nor raw feedback supplies source batch
admission or a native upper-policy/optimum theorem.

For actual same-code runtime feedback, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.Feedback`.
`Feedback.exists_native_controller` constructs one finite native program before
quantifying over original `GuardedStartup.Input`, environments and hidden memory.
It starts with blank work tapes, computes the fresh runtime packet, tests the
actual stopping bit before every query, and repeats on the updated State. Query
preparation copies bytes from the current tape packet; no state or continuation
is supplied between turns. Each round erases the full reply buffer and its marker
at cell $-1$, then the virtual query buffer and its marker, with every work head
and the real original-input cursor restored. Previous answer channels are retained;
the next query replaces its answer only after the new request is fully formed.

The theorem identifies the actual unbounded native terminal law with `Feedback.run`.
That recursion is a mathematical kernel used to state the correspondence, not the
execution implementation. The implementation is the finite native loop in
`NativeFeedbackLoop.machine`; its boundary law allows response-dependent local
clocks and divergence in a general body. The concrete turn-bounded controller
terminates almost surely under this total finite-word response interface, without
assuming termination or a common reply clock. `exists_round` states the complete
canonical storage invariant. `run_history_matches` authenticates raw histories
and private words against events from a matching initial ledger; fresh original
input matches an empty ledger, not arbitrary previous external events.
`run_call_bounds` bounds issued calls by each initial scalar allowance.

The [feedback client](../../CslibFrontierTests/NativeRetentionFeedback.lean) runs one
consistent source with correlated unbounded invoice reports. A first cancellation
updates the actual history/private word and therefore the second query. A second
accepted two-row cover emits `[true, true]` before a third still-allowed call.
The joint law retains both invoices and durations. The same code stops after a
first cover, on a last reservation, on zero initial turns and on initial empty-ground
completion; empty zero-bill replies exercise both cleanup layers. From the same
matching warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRetentionFeedback
```

This completes the concrete raw-State transport component. By itself its request
is framed State bytes, not a preselected source batch, and its scalar opportunity
count is not an exactly-once labeled used-set. The `BatchPlanner`/`BatchAdmission`
composition below adds actual batch planning, admission and authenticated history
for the named controller. `BatchOutput` and `BatchOptimum` then derive its native
success/deadline/bill and common-oracle lower/upper/competitive bounds.
Reservation exhaustion is not a physical clock. External encodings, general
measurable interfaces and broader divergent-path cost packaging remain open;
no unrestricted Theorem 5/6 or ALL-main completion is claimed.

For a constructed source-batch request planner, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchAdmission`.
`BatchPlanner.exists_native_controller n width` forms actual concurrent source
packets on a separate query tape, preserving the complete runtime State for the
same reader/update/cleanup/restart loop. Its code is fixed for a finite opportunity
interface and positive block width; original instances, histories, private words
and unbounded replies are runtime data. This is weaker than one size-uniform
machine reading arbitrary interface sizes, and does not compile arbitrary schedulers.

`BatchAdmission.admitted_controller` derives acceptance for every
live iteration from fitting original turn/block budgets, positive cutoff allotments
and a deadline covering those allotments. No batch validity, used-set, execution-law
or success witness is supplied. `Aligned` identifies actual accepted source history,
consumed labels, authenticated reply history and the joint bill/duration/provenance
ledger. `selectionOnly_controller` additionally derives the existing native
`SelectionOnly` predicate at every instruction prefix from the standard original
WSC promises and computed output provenance. Each scalar opportunity allowance now
counts one whole block; the source
used-set counts its labels. Cancellation still consumes those labels and charges
accrued tokens. The handler enforces cutoffs and the absolute oracle-time deadline;
the planner's fitting allotments prevent rejection before its last allowed turn.
Local native instructions are excluded from that duration, as in the paper.

To compare the executed guard with the mathematical progress process, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchStopping`.
`retained_eq` identifies packet parsing and rational local retention with
`AdaptiveSelection.selected` on the actual chronological raw history.
`count_completed` derives a computed stop, the actual output mask, full coverage
and its dual weight certificate from the productive-count threshold.
`Feedback.run_allowances` conserves each allowance plus the actual number of events.
With opportunity and reservation budgets covering the turn horizon,
`run_live_before_horizon` proves that the same feedback kernel stays live before
that horizon exactly when its retained sets are incomplete. The reservation
condition matters: zero reservations can stop an incomplete instance initially.
These are pathwise statements for the kernel in the proved native execution law.
`BatchReceipts.aligned_completion_eq` additionally identifies the guard with
`NativeBatch.Retained.complete` on exact authenticated source receipts, preserving
proposal order and canceled-call behavior. `Aligned.reports` records the complete
raw report history, rather than only its provenance union.

For numerical bounds for that same controller, import
`CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchUpper`.
`BatchPlanner.controller n width` fixes one compiled implementation, including its
finite control type, program, context tape and proved joint feedback law. The
admission, stopping, numerical and output APIs all refer to its `.program`;
separate existential witnesses are not used to assert their identity.
`stopping_controller` proves, at every
positive-probability selected epoch before its horizon, that issued batches have
incomplete retained coverage and no-call decisions have complete retained coverage.
This uses the actual joint terminal law and backward propagation of receipt-prefix
safety through native epochs; it assumes no runtime-state representation contract.
Initial reservations and opportunity allowances must cover the entire turn horizon.

`upper_controller` consequently needs productivity and conditional
mean invoice envelopes only on reached, issued batches. It derives binomial
retained-completion probability, the complete actual accrued-bill survival sum,
the bounds $c r_a/p$ and $cu$, and finite expected bill for finite $c$ and positive $p$.
It assumes neither integrability nor a bounded total bill. The source sampler,
private seed and native process are the same throughout. The candidate parser
embeds the source finite masks into the original natural row indices without
truncating the response alphabet or hidden metadata.

`BatchReceipts.aligned_completed_result` gives the pathwise output/deadline
implication: actual receipt completion decodes the runtime result to its original
family, proves the full-cover dual-weight certificate, and bounds actual source
elapsed time by the deadline. The correlated first-cover client checks this on
its real supported source reply. `BatchOutput.output_controller` proves the tape
implication for the named implementation; it is not an existence statement that
a never-halting witness could satisfy. `terminal_completion` identifies epoch
completion with terminal authenticated receipts, including the final silent epoch.
`BatchOutput.upper_controller` joins the binomial certified-output success bound
and all stopped-bill bounds for that one compiled program.

Import `CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum`
for the common-oracle comparison. `costs` ranges over all finite-control native
competitors admitted by `SelectionOnly` for `BatchOutput.accept`, the fixed input
cover/dual certificate criterion: provenance is
required only for counted certified successes, and failed decoded families may be
unsupported. The [admission client](../../CslibFrontierTests/NativeRetentionSuccessAdmission.lean)
executes a no-query native program on a satisfiable instance and proves this class
strictly includes policies excluded by all-output provenance. Competitors require
certified tape-output success at
least $\eta$ on the same sampler, seed and original encoded input. `optimum` is
the infimum of their actual extended expected bills; attainment and integrability
are not assumed. `LowerEnvelopes` quantifies the reached selected-epoch coverage,
progress and invoice conditions over every competitor. `lower` derives
$\eta r_b\underline c/\overline p$; `upper` uses the actual named controller to
bound the optimum by its survival sum, $\overline c r_a/\underline p$ and
$\overline c u$. With matching envelopes, `competitive` bounds the named
controller's bill by $\mathrm{OPT}/\eta$ for positive $\eta$.

`BatchOptimum.success_le` bounds the actual certified tape-success probability of
any admitted competitor by $P[\mathrm{Bin}(v,\overline p)\ge r_b]$, where
$v=\min(u,\lfloor D/\ell\rfloor)$. It uses the source's reached revealed-progress
and actual batch-latency envelopes. `feasible_success_le` gives the same necessary
bound on a feasible target $\eta$ under uniform latency envelopes over admitted
competitors. Neither a physical turn cap nor a success-law identity is a premise.
The [deadline client](../../CslibFrontierTests/NativeRetentionDeadline.lean) checks
positive certified tape readback against a real native terminal law and derives
empty feasibility/OPT infinity for positive success on nonempty ground at zero
oracle deadline, even with one advertised turn and arbitrary source randomness.
The separate [positive-duration native client](../../CslibFrontierTests/NativeBatchSuccess.lean)
discharges the underlying native deadline theorem's reached latency assumptions.
The [positive-deadline correlated client](../../CslibFrontierTests/NativeRetentionDeadlinePositive.lean)
uses a satisfiable singleton instance, two concurrent opportunities, deadline one,
latency one, and a shared fair bit controlling both coverage and invoices.
The named controller's actual certified tape-success probability is exactly $1/2$;
all admitted competitors on that same oracle have necessary target $\eta\le1/2$.
The client derives the reached source envelopes for arbitrary competitors using
[InitialEpoch](../../CslibFrontier/Computability/Probabilistic/NativeBatch/InitialEpoch.lean):
positive-probability first issued histories preserve the original selected-batch
joint law through arbitrary silent computation, hidden control and rejected requests.
It assumes neither a conditional representation identity nor competitor termination.


The source model (PDF p. 5) explicitly excludes local computation from deadline
$D$. Elapsed time here counts oracle batch maxima, cutoffs and cancellation.
Competitors share the configured finite opportunity/cutoff interface and original
runtime input codec. The upper implementation is the fixed block scheduler;
these are material restrictions, not unrestricted source Theorem 5 coverage.
In particular, the planner fixes label blocks and sends framed runtime contexts;
it is not an interpreter for an arbitrary source policy's adaptive opportunity,
query-string and cutoff choices. A source codec/interpreter must preserve the
same oracle's response law and accrued resources, rather than posit a transfer
contract. General measurable oracle laws and external PTM encodings remain open.

The [correlated numerical client](../../CslibFrontierTests/NativeRetentionUpperCorrelated.lean)
applies the same constructed numerical controller to two simultaneous calls.
One shared fair bit makes both invoices one or both two; their joint event has
probability $1/2$, whereas the product of the marginals is $1/4$.
Both calls return the covering singleton, so actual issued productivity is one and
the conditional batch invoice is at most four. The client derives these envelopes
from the supported joint sampler and concludes the first-batch retained-completion
bound on certified halted tape output (success probability at least one), expected
complete bill at most four, and native optimum between one and four. Its positive
lower invoice envelope is proved for every admitted competitor. No response
independence is assumed.

The [admitted batch client](../../CslibFrontierTests/NativeRetentionBatchAdmission.lean)
checks fresh concurrent pairs, shared unbounded hidden invoices, cancellation and
original-context/history-dependent next requests and actual selected-epoch stopping.
The [upper boundary client](../../CslibFrontierTests/NativeRetentionUpper.lean) checks
zero expected cost for the actual original-input program on empty ground and a
zero horizon, with arbitrary source sampler and hidden seed.
The [nonempty numerical client](../../CslibFrontierTests/NativeRetentionUpperNonempty.lean)
uses a positive-dual singleton cover and a sampler that returns that cover in its
first batch with invoice one. It derives both issued-batch envelopes from the
actual conditional law and instantiates the numerical theorem on the constructed
program, without a supplied cost or success conclusion. The admitted-batch client
has unbounded history-dependent invoices; the correlated numerical client instead
derives a finite conditional invoice envelope and instantiates the joint native
success/bill/optimum results. From the repository root:

```bash
scripts/build.sh CslibFrontierTests.NativeRetentionBatchAdmission \
  CslibFrontierTests.NativeRetentionUpper \
  CslibFrontierTests.NativeRetentionUpperNonempty \
  CslibFrontierTests.NativeRetentionUpperCorrelated \
  CslibFrontierTests.NativeRetentionDeadline \
  CslibFrontierTests.NativeRetentionSuccessAdmission --wfail --iofail
```

This establishes a concrete supported scheduler and source-admitted native loop.
The named controller has joint compiled-output success/bill bounds and a
common-oracle optimum comparison in this implemented model. Theorem 6's
WSC/subinstance/role/residual specialization, external encodings, general measurable interfaces, compiled physical clocks and divergent
path cost/integrability limits remain distinct obligations.

Import `CslibFrontier.Probability.StochasticOracle.NativeRetention.ResponseExecution`
for `exists_query_retention`. Its continuation code is derived from the existing
raw-parser/rational-retention computability proof. One complete native program
queries, copies the actual full report, prepares its buffer and computes the
retained source mask; it emits the mask on computed completion and `[]` otherwise.
The [complete source client](../../CslibFrontierTests/NativeRetentionResponse.lean)
checks two hidden response branches with a billed cancellation, one fixed source
with unbounded geometric invoice packets, original nonempty cover data, rejection,
empty ground, and the existing whole-policy native trace transfer. From a matching
warm checkout, run:

```bash
scripts/build.sh CslibFrontierTests.NativeRetentionResponse
```

The specialization fixes `Packets.Work` at code construction: its quantifiers are
one code for all replies at each fixed context, not one native loop over runtime
contexts. It still issues its one query on an already complete instance. The
previous uniform processor still starts from `encWork` on its input tape; this new
program does not construct a dynamic `encWork` history there. A complete selector
must retain runtime context/private state, compute subsequent requests, clear and
reuse its buffers/workspace, and implement post-response budget/deadline stopping
and repeated native restart. The initial guard above does not supply these loop
steps. Consequently these theorems do not yet supply the native upper success,
tail-sum cost or common-oracle optimum
comparison. An optional terminal value `none` records divergence; it is not a
halted failure and must not be assigned a zero accrued prefix bill. The existing
native whole-epoch trace retains such prefix resources, while cofinal path-cost
and real-integrability packaging remain separate obligations.
