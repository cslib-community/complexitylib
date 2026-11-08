# Probabilistic programs, cryptographic games, and privacy models

Complexitylib distinguishes an algorithm's syntax, its probability law, and its realization by a resource-bounded machine. The distinction is visible in the types: `OracleComp` and `ProbComp` are programs; `PMF` is an exact distribution; `IsPPTOn` and `IsOraclePPTOn` assert realization by one finite-control classical fair-coin machine. Security then quantifies over algorithms carrying the relevant realization certificate. Some finite cryptographic interfaces deliberately stay at the distributional or query-bounded level [complexitylib][complexitylib].

The survey baseline is `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. This section records inspected definitions and theorem statements, with deeper tracing of the HILL/GGM, GSW, chosen-message/CCA, and MPC endpoints. It does not report a new Lean build or a complete independent proof audit.

## Reading map

- [Programs, probability laws, and native realization](programs-and-realization.md): typed free programs, stateful oracles, sampling, cost bounds, and fair-coin machines.
- [Security games and primitive families](security-games-and-primitives.md): computational indistinguishability, hardness assumptions, generators/functions, encryption, authentication, signatures, and commitments.
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

Circuit-bounded PRG tests are a different admissibility model from uniform PPT and belong in the [circuits section](../circuits-logic-and-other-models/index.md); the relevant interface is [IsCircuitTest](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Primitives/PRG/Circuit.lean#L74). Read-once branching-program tests (`IsReadOnceTest`, used for Nisan's generator) are described with the [read-once programs](../circuits-logic-and-other-models/networks-and-iteration.md#deterministic-read-once-programs-and-nisans-generator). Randomized Word-RAM's unit-cost finite uniform instruction belongs in [algorithms and memory](../algorithms-and-memory/index.md). The underlying parametric Turing machines and complexity classes belong in [machines and classes](../machines-and-classes/index.md).

## Design rationale

The common free-program layer permits the same syntax to be interpreted in independent probability, stateful probability, or another program language. Exact equality with an encoded machine run is then a separate bridge. **Inference:** this supports readable probability proofs while making machine efficiency an additional mathematical obligation, rather than a syntactic promise. It also permits ideal distributions that cannot be exactly sampled in a fixed finite fair-coin budget.

Uniformity is load-bearing. The native witnesses are chosen before all inputs, and a security adversary is chosen before the asymptotic security parameter. Auxiliary strings and public descriptions are encoded inputs. The higher-level APIs generally do not identify circuit families, freely supplied advice, and uniform Turing algorithms.

The formal contracts distinguish strict versus expected running time; exact uniform group laws versus approximate fair-coin samplers; fixed versus adaptive query selection; full versus proper MPC coalitions; and generable versus unrestricted auxiliary-input zero knowledge. These are properties of the formal statements, not incidental caveats.

## Coverage and evidence

The model map groups protocol constructions by their computational/security interface, rather than treating every named cipher as a new computational model. Sources covered include `Languages/Probabilistic`, `Computability/Probabilistic`, `Crypto/Game`, `Crypto/Computational`, `Crypto/Protocols`, and pinned cslib's cryptographic interfaces. The mathematical probability library supplies PMFs, couplings, distances, and concentration; these are semantic foundations, not additional execution machines.

Differential privacy is covered by `Privacy/DifferentialPrivacy` (added after the survey baseline): `(ε, δ)`-privacy of exact output laws for an explicit adjacency relation, post-processing, adaptive and advanced composition, Hamming group privacy, randomized response, the geometric/discrete Laplace mechanisms, the exponential mechanism, AboveThreshold/Sparse with discrete noise, and packing, reconstruction and small-universe lower bounds; see [Protocols and privacy](protocols-and-privacy.md#differential-privacy). Rényi, concentrated and computational differential privacy, continuous Laplace/Gaussian mechanisms and sampling costs are not covered.

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

## Known Limitations

Primary-source verification was selective. HILL/Holenstein/GGM and selected RAM/algorithm sources were consulted; textbook locator claims and most construction proofs remain code-grounded rather than independently reconciled line by line with the literature. The section intentionally does not infer autonomous-development percentages from theorem counts or test files.

[complexitylib]: ../sources.md#complexitylib
