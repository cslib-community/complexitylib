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

Import [AdaptiveLowerCost](../../Complexity/Probability/StochasticOracle/AdaptiveLowerCost.lean)
and check the complete
[client](../../ComplexityTests/StochasticOracleAdaptiveLowerCost.lean).
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
[AdaptiveComparison](../../Complexity/Probability/StochasticOracle/AdaptiveComparison.lean)
and check its [complete client](../../ComplexityTests/StochasticOracleAdaptiveComparison.lean).
`progressExpectation` evaluates a terminal payoff of the progress count using a
conditional law indexed by the entire response transcript (newest response first).
`progressExpectation_le` and `le_progressExpectation` compare any increasing
payoff against `bernoulliExpectation`, the independent-trial recurrence. Supply
the conditional probability envelope at every history; the actual response laws
need not be independent or identical. A response may contain auxiliary information,
so the history need not consist only of progress bits. The client uses success
probability $1/4$ before any success and $3/4$ afterwards: its two-success
probability is $3/16$, between comparison values $1/16$ and $9/16$.

Import [AdaptiveBinomial](../../Complexity/Probability/StochasticOracle/AdaptiveBinomial.lean)
for `bernoulliExpectation_eq_integral`, `progress_tail_le` and `le_progress_tail`.
The comparison recurrence is now identified with Mathlib's actual binomial law,
including both increasing count-tail comparisons. No independence of actual events
is used.

For actual proposals, import
[AdaptiveSelection](../../Complexity/Probability/StochasticOracle/AdaptiveSelection.lean)
and check [the complete selection client](../../ComplexityTests/StochasticOracleAdaptiveSelection.lean).
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

`Complexity.Probability.StochasticOracle.AdaptivePath` constructs an infinite
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
`Complexity.Probability.StochasticOracle.AdaptiveReachable`.
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
The [complete reachable-history client](../../ComplexityTests/StochasticOracleAdaptiveReachable.lean)
uses a correlated response law with a null response that poisons subsequent kernels
and charges. It checks that both old all-history envelopes fail at that unreachable
history, while actual finite completion, a.s. completion and total-cost conclusions
hold. It also checks the selected-batch envelope and the full composed batch/response
total-cost theorem with a deliberately bad null batch.
Import `Complexity.Probability.StochasticOracle.AdaptiveStopping` for actual stopping
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
`Complexity.Probability.StochasticOracle.SelectionOptimum`. `SelectionPolicy.Oracle`
fixes conditional responses, all valid proposed sets, token charges and physical
durations. An arbitrary `Policy` supplies randomized batch-or-halt choices and a
randomized terminal output kernel. `law` samples the selected batch then its response;
halt is absorbing and carries no extra oracle information. `Admissible` requires only
that each supported final output use previously proposed sets. It allows buffering
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
The existing `conditional_lower_cost` aggregates the derived marginal tables; no
aggregate expected-cost lower bound is a hypothesis.

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

The [complete policy client](../../ComplexityTests/StochasticOracleSelectionPolicy.lean)
checks universal local contracts for every policy of a correlated oracle, randomized
early halt, randomized final output, the physical one-call deadline inside a two-turn
budget, and the matching comparison. Its second instance offers a costly bundle
rejected by local retention: an admissible buffering policy extracts the cheap
certified singleton and succeeds with probability one, and the universal lower
cost theorem still applies. This checks that the competing class includes policies
outside the constructive retention algorithm.

Theorem 5 remains incomplete at unrestricted source scope: these are finite-alphabet
behavioral kernels, without a realization/representation theorem for every encoded
selection-only PTM or general measurable alphabets. Native encoded machine resources
also remain open. Theorem 4's native runtime/asymptotic/hardness claims remain open.

### Submission 191: actual Theorem 6 residual construction and policy optima

The source setup (1)–(3), PDF pages 12–13, and Theorem 6/proof, PDF page 13, are
implemented in `Complexity.Probability.StochasticOracle.ResidualCover` and
`Complexity.Probability.StochasticOracle.ResidualPolicy`. Start with any $z\ge3$
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

The [complete residual client](../../ComplexityTests/StochasticOracleResidualCover.lean)
constructs five six-point X3C blocks with an overlapping unused triple. It derives
the dual/primal and residual/certificate claims, checks universal randomized
competitor bounds of five and three, constructs successful policies attaining
both, and obtains the strict ratio $5/3$ with the physical turn counts.

This proves the arbitrary finite X3C construction and universal behavioral
numerical endpoints, rather than only a singleton or supplied-certificate model.
The unrestricted encoded-PTM representation and realization bridge is still unproved; neither
unrestricted source Theorem 6 nor ALL-main is claimed complete. Theorem 5's
representation/general-alphabet gaps and Theorem 4's resource/hardness gaps above
remain material. No curated abstract changes: these modules are outside the
selected headline dependencies. The Agent Operator's Manual requires no edit:
ownership, review, validation and human direction are unchanged.


### Submission 191: a concrete native-to-behavioral bridge

Import `Complexity.Computability.Probabilistic.NativeOneTurn` for a reusable
one-turn protocol with actual native fair-coin multi-tape machines, and
`Complexity.Probability.StochasticOracle.NativeResidualOneTurn` for the residual
instance lower-bound corollary. The [complete native client](../../ComplexityTests/NativeOneTurn.lean)
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
Theorem 6. General response alphabets, native query/output adapter realization,
canonical-label recovery and the upper-selector compiler also remain open.
The earlier Theorem 4 resource/asymptotic/hardness gaps remain. ROADMAP preserves
these obligations; no unrestricted theorem or ALL-main completion is claimed.
The Agent Operator's Manual needs no change because ownership, human direction,
review and validation procedures are unchanged. No curated abstract depends on
these new modules or selects this bounded bridge as a headline.


### Submission 191: actual multi-query open execution and public path representation

Import `Complexity.Computability.Probabilistic.NativeOpenExecution` for actual
open native execution and `Complexity.Computability.Probabilistic.NativeOpenSelection`
for successful-output provenance. The complete [native open client](../../ComplexityTests/NativeOpenExecution.lean)
and [observed-process client](../../ComplexityTests/ObservedProcess.lean) include
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

Import `Complexity.Computability.Probabilistic.NativeUnboundedExecution` to
observe actual open native execution without a uniformly sufficient instruction
bound. The complete [unbounded native client](../../ComplexityTests/NativeUnboundedExecution.lean)
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

Import `Complexity.Computability.Probabilistic.NativeInterface` to expose the
query selected by the actual open native transition table before sampling its
response. The complete [interface client](../../ComplexityTests/NativeInterface.lean)
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
in the following section. General batch-record identification, source call
opportunities, simultaneous preformed batches, turn bounds, deadlines and
accrued cancellation charges still need separate contracts. The finite behavioral
Theorem 5/6 APIs cannot be applied directly to raw instruction ticks.

### Stopping at the next query or halt

Import `Complexity.Computability.Probabilistic.NativeEpoch`. The actual
[next-epoch client](../../ComplexityTests/NativeEpoch.lean) and
[quantitative policy client](../../ComplexityTests/NativeEpochPolicy.lean) check
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

The general source adapter remains open. Raw native query epochs still need
source opportunity/batch/query/candidate/output codecs, nonempty simultaneous
preformed concurrent batches, exactly-once opportunities, maximum-latency and
cutoff/cancellation accounting and output extraction. The quantitative APIs
still use finite batch/response tables. General policies may read unbounded
response or usage metadata, so a sufficient finite record abstraction cannot
be assumed; either its sufficiency or a more general quantitative kernel API
needs proof.
Those contracts must be proved from actual code/interface behavior; a semantic
parser alone cannot supply source validity. The general finite quantitative
policy connection, fixed-oracle conditional laws across all admitted native
competitors, source epoch envelopes and uniform native upper selectors are not
established by the singleton client. External PTM encodings, canonical residual
recovery, general measurable responses and the exact local-termination convention
also remain open. Divergent-path resource costs are still outside terminal bill
values, as described above.

Theorem 4's native resource/asymptotic/hardness gaps remain. Neither unrestricted
Theorems 5/6 nor ALL-main is complete. No selected abstract model or statement
changes. The Agent Operator's Manual requires no edit because human direction,
ownership, review and validation procedures are unchanged.
