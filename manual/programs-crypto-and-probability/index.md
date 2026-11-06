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
finite-horizon covariance identity, information and auditing bounds, DPI rigidity
results, and scheduling policy–LP frontier documented below. The expanded
headline programme remains open in [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).
STOC submission 191’s binary-input two-batch FPTAS, exact-selection hardness and
integer-cost pseudopolynomial optimizer are proved; its partial/adaptive-cover main results
remain open. These imports
do not establish completion of the expanded programme. The source
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
  exponential. The partial-cover selector and adaptive
  endpoints remain open under [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).
- [PartialCover](../../Complexity/Probability/StochasticOracle/PartialCover.lean)
  proves submission 191, Lemma 1 (PDF pp. 9, 15). `Instance` supplies the finite
  universe, original weighted sets and a nonnegative feasible dual vector.
  `retain` processes returned subfamilies in order and accepts only a nonempty
  new cover whose weight passes `Certified`. Its invariant charges newly
  covered elements once; overlapping/repeated sets cannot increase the assembled
  cover's weight beyond that charge. `retain_cover_bound` compares every
  completed result with the dual objective and every integral cover.
  Import [PartialCoverRisk](../../Complexity/Probability/StochasticOracle/PartialCoverRisk.lean)
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
  Import [PartialCoverGreedy](../../Complexity/Probability/StochasticOracle/PartialCoverGreedy.lean)
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
  [PartialCoverThreshold](../../Complexity/Probability/StochasticOracle/PartialCoverThreshold.lean)
  for `rationalRepetitions`, an exact rational-power search proved equal to the
  real-log ceiling, including equality at an integral threshold. `rationalBatch`
  uses that search and emits exactly the batch analyzed with real logarithms;
  for the sufficient demand pass the rational failure budget `(1-η)/n`.
  The search has no native binary resource bound. Check the complete
  [threshold client](../../ComplexityTests/StochasticOraclePartialCoverThreshold.lean)
  with `lake build ComplexityTests.StochasticOraclePartialCoverThreshold` for
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
  Native binary time/space and asymptotic approximation
  consequences and hardness transfer remain open, as do Theorems 5–6.
  From a configured checkout, check the complete
  [StochasticOracleMulticoverGreedy](../../ComplexityTests/StochasticOracleMulticoverGreedy.lean)
  client with `lake build ComplexityTests.StochasticOracleMulticoverGreedy` for
  exact rational choices, repeated calls, harmonic and risk comparisons,
  empty universes and inputs that fail to cover. For response-law examples,
  import `PartialCoverRisk` and check the complete
  [StochasticOraclePartialCover](../../ComplexityTests/StochasticOraclePartialCover.lean)
  client with `lake build ComplexityTests.StochasticOraclePartialCover`: it
  checks accepted/rejected overlaps, exact two-call probability `3/4`, a correlated
  response law, a failing conditional guarantee, zero calls and an empty universe.
- [TwoBatchMinimum](../../Complexity/Probability/StochasticOracle/TwoBatchMinimum.lean)
  completes Proposition 1 (PDF pp. 6, 14): `one_turn_cost` gives the exact
  one-turn value; `two_batch_reduction` and `minimum_two_batch` prove the attained
  minimum over nonempty complementary first batches against every randomized
  maximum-success competitor. The two-turn minimum assumes a nonempty population
  and that querying every opportunity concurrently meets the deadline. Empty
  first slots in competing schedules are normalized, rather than excluded.
- [TwoBatchApproximation](../../Complexity/Probability/StochasticOracle/TwoBatchApproximation.lean)
  supplies an executable rational-input selector indexed by `Fin k`. Starting
  from a `FullCoverInstance (Fin k) ℚ`, `choose I ε D` returns the best exact-saving
  candidate from cutoff families and rounded-product tables. It includes the
  full concurrent batch as fallback. `choose_feasible` needs `0 < k` and the
  original full-batch deadline; `choose_success` proves maximum success exactly.
  Check the complete
  [StochasticOracleApproximation.lean](../../ComplexityTests/StochasticOracleApproximation.lean)
  client: the heterogeneous example returns saving four at deadline three and
  saving zero at deadline two; its optimum lower bound covers arbitrary randomized
  policies. The client also checks zero-rounded-cost collisions and mandatory
  selections. Kernel evaluation uses `decide +kernel`, not `native_decide`.
  [CutoffFamilies](../../Complexity/Probability/StochasticOracle/CutoffFamilies.lean)
  proves exact deadline soundness, coverage and at most $k(k+1)$ families.
  [MinProduct](../../Complexity/Algorithms/Lean/DynamicProgramming/MinProduct.lean)
  proves table soundness, minimum-product dominance, reconstruction, state and
  operation bounds. Its operation count charges rational multiplication and
  comparison as single operations; it is **not a binary runtime certificate**.
  [RoundedProduct](../../Complexity/Algorithms/Lean/DynamicProgramming/RoundedProduct.lean)
  derives the multiplicative product–sum guarantee for each maximum-cost-member
  branch. Scaling divides by the number of potentially selected branch members,
  including the mandatory member; this bounds the same total rounding loss as
  the manuscript's division by the full population size.
  `choose_approximation` now proves the global saving bound for every nonempty
  feasible comparison first batch. The product-minimizing witness remains
  nonempty: strict positivity of success makes the comparison first-batch failure
  product strictly smaller than one, whereas an empty first batch has product one.
  For rational $0<ε<1$, import
  [TwoBatchGuarantees](../../Complexity/Probability/StochasticOracle/TwoBatchGuarantees.lean)
  and use `choose_real_policy_approximation` to compare with arbitrary real-randomized
  feasible maximum-success policies. `choose_optimum_guarantees` derives an attained
  optimum over those policies and both advertised savings/cost inequalities; it
  also supplies the exact selected-schedule success and deadline. No optimum or
  approximation inequality is a premise. The complete client above checks the
  real-policy bound and a three-opportunity rounding collision whose result must
  retain a nonempty first batch.

  [TwoBatchResources](../../Complexity/Probability/StochasticOracle/TwoBatchResources.lean)
  defines `inputEncoding` using framed reduced signed binary numerators and positive
  binary denominators. `inputSize_bounds` bounds the population and each rational
  field by the full input length. `candidates_length_le` bounds the whole candidate
  list by a polynomial in $k$ and an integer $m$ with $1\le εm$; $m$ pays inverse
  tolerance and is not assumed polynomial in the binary tolerance length. The
  exact products, summed costs and savings comparisons have polynomial binary
  operand widths. Scaling and flooring operand bounds are in `RoundedProduct`.
  [PolyTime.Rat.Binary](../../Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Rat/Binary.lean)
  supplies native multitape polynomial-time arithmetic, comparison, division and
  flooring under `encRatBin`, including binary gcd normalization and zero/negative
  cases. [DynamicProgramming.Native](../../Complexity/Algorithms/Lean/DynamicProgramming/Native.lean)
  certifies insertion, pruning and the entire recurrence with runtime-computed
  populations, keys and probability fields. Table keys use unary because the
  rounded key budget is polynomial; probabilities and costs remain binary.
  Rational list sums/products charge traversal, operand copying and normalization.

  For the complete Theorem 2(2) algorithm, import
  [TwoBatchBinary](../../Complexity/Probability/StochasticOracle/TwoBatchBinary.lean)
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

  [TwoBatchNative](../../Complexity/Probability/StochasticOracle/TwoBatchNative.lean)
  implements all cutoff-family/maximum-member enumeration, input lookups, exact
  arithmetic, DP/pruning, reconstructed index lists, membership scans and final
  savings comparisons. `computable_schedule` also charges the final complement
  scan and emits both batches; no batch reconstruction is deferred to an uncharged
  output step. It saturates rounded keys on invalid data to keep the
  internal compiler total and polynomial. The
  [correctness bridge](../../Complexity/Probability/StochasticOracle/TwoBatchNativeCorrectness.lean)
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
  [TwoBatchHardness](../../Complexity/Probability/StochasticOracle/TwoBatchHardness.lean).
  `TwoBatchHardness.Input` contains the ordered rational probability/cost/cutoff triples,
  deadline and expected-cost threshold, with valid oracle parameters. `encInput` encodes
  only those numerical fields in binary. `Decision` asks for a feasible maximum-success
  two-turn policy of expected cost at most the threshold, allowing arbitrary real private
  randomization. `restrictedDecision_npHard` derives NP-hardness even with unit cutoffs
  and a common success/cost ratio. It reuses the binary `SubsetSum` hardness theorem and
  existing `SubsetSum.toPartition`, removes zero source weights, and preserves repeated
  positive occurrences as distinct calls. `reduction_mem_iff` is both directions of the
  actual policy decision equivalence, rather than a deterministic-schedule surrogate.

  For exact optimization with positive integer costs, import
  [TwoBatchIntegralRuntime](../../Complexity/Probability/StochasticOracle/TwoBatchIntegralRuntime.lean).
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
  From a configured checkout, run `lake env lean ComplexityTests/StochasticOracleExact.lean`
  to check the [complete client](../../ComplexityTests/StochasticOracleExact.lean),
  including both hardness answers, zeros, duplicate weights, exact output/cost/success,
  heterogeneous deadlines, impossible deadlines, empty input and a singleton.
- [Submodular.OracleSavings](../../Complexity/Algorithms/Lean/Submodular/OracleSavings.lean)
  proves Wang's Theorem 2(1) (PDF p. 7). A finite type indexes all oracles;
  `savings p c A` is exactly $(1-\prod_{i\in A}(1-p_i))\sum_{i\notin A}c_i$.
  Use `savings_nonneg` and `savings_isSubmodular` with pointwise $0\le p_i\le1$
  and $c_i\ge0$. Submodularity reuses the library's `IsSubmodular`; savings need
  not be monotone (the test has singleton saving one and full-set saving zero).
  The scheduling theorem and binary-input FPTAS are supplied by `StochasticOracle`.
  Theorem 3's exact-selection results are described above; Theorems 4–6's partial
  and adaptive-cover endpoints remain open.
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
