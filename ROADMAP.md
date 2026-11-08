# Roadmap

The directions Complexitylib aims to cover, grouped by area. This file lists directions only:
status, progress and completion notes live on the linked issues and pull requests, module
docstrings describe what is proved, and the [README](README.md) and the curated formal abstracts
present completed results. A PR edits this file when it opens or closes a direction.

A direction is complete only when its machine, resource and quantitative conclusions are proved
for the actual algorithms, with explicit models, encodings and assumptions. An abstract algorithm,
a class definition or an assumed reconstruction theorem does not complete it. Search Mathlib,
CSLib and this library before starting, and check upstream work.

The [pre-rewrite roadmap][archive] is the archive of past detail and design records, including
the FHE industrial context, the first-order design decisions and the repository's history.

## Programs

| Program | Issues |
| --- | --- |
| Frontier program: ambitious theorems toward the research frontier | [#897]; its tracks are linked below |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798], audit [#884] |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862], from [#456] |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949], [#939] |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#1104] |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640], [#643] |
| Crypto frontier track: Kilian's succinct arguments | [#999] |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002] |
| STOC submission headline formalizations, including continuous mechanism verification, general least-squares stability and exact-one counting | [issue 2527](https://github.com/cslib-community/complexitylib/issues/2527) |
| A Verso guide with a chapter per area | [#585] |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124] |
| Proof automation: predictable polynomial-time certificate search | [#1155] |

STOC submission 1575 now has actual signed exact-one CNF compilation and
rank-derived two-query existence/correctness, including binary side constraints
and declared unused bits (`CNF/ExactOneCounting`). `CNF/VCOne` now derives
the VC-dimension-one table representation, its greedy signed separators and
the sharp equation deficit from the actual table and Mathlib VC/Sauer–Shelah
semantics. `CNF/VCOneTables` aligns arbitrarily overlapping scopes and proves
the all-cases global two-query budget on declared bits. Its equation enumeration
now uses a constructive pair-compatible prefix listing, with at most $w+1$
retained rows per stage and $2w(w+1)$ attempted extensions, rather than enumerating
the cube. Finite lookup aligns scope signs. `CNF/ExactOneElimination` and
`CNF/VCOneElimination` now execute materialized rational elimination, original-row
selection, direct cases and nonadaptive query assembly, including overlapping
tables. A proved compiler rewrite scans explicit table rows for binary restrictions
rather than all Boolean tuples. `PolyTime/Int/Cramer` independently certifies binary
square-system recovery. `PolyTime/Int/RowBasis` and `PolyTime/Int/Rectangular` now
supply a division-free greedy original-row basis, computed rank identity, general
rectangular consistency/candidate recovery and uniform binary polynomial runtime
with explicit coefficient-width bounds. `CNF/ExactOneBinary` now materializes signed integer rows and connects the binary
selector/candidate to every direct/query branch; `binaryTablePlan` composes this
backend with the actual closure equations, with exact counting and query budgets.
Uniform binary time/peak-space certification for the full closure, separator, equation,
branch and two-query assembly remain open, along with bounded-demand/graph
applications and the advertised sharper counting runtime, under
[issue 2527](https://github.com/cslib-community/complexitylib/issues/2527).
The existing rational elimination kernel's own coefficient-growth proof is also
not supplied by the new algorithm. This does not complete the paper's algorithmic
main results.
The closure resource bound requires the VC-one promise: the zero/one/unit-vector
table has only $w+2$ rows but a full $2^w$ closure. The resource theorem must
therefore restrict to promised inputs (as the source does), or validate them before listing. Explicit framed table/scope and tagged plan-output encodings now accompany
`tablePayload`, `equationPayload` and `binaryTableBits`; declarations and widths
are unary, rows literal bits and column numbers binary. Promise-restricted
frontier coordinate storage and full-frontier comparison volume are bounded.
The signed equation-to-consistency stage now has actual polynomial binary
execution (`payloadRows_polytime`, `payloadRhs_polytime`,
`payloadConsistent_polytime`) and correspondence to the actual table equations.
This is not a polynomial binary-machine realization of the full table compiler. Separator/projection execution, branch/candidate checking, query
writing and composed time/space remain open; the rectangular solver certificate
alone does not supply them.

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897].

1. [Completeness of oblivious transfer](#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886])
3. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889])
4. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity)
5. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891])
6. [MIP = NEXP](#interactive-proofs) ([#892])
7. [Regev's worst-case to average-case reduction](#cryptographic-landmarks)

## Cryptography

### Cryptographic landmarks

- **Completeness of oblivious transfer.** In the ideal OT-hybrid model, every polynomial-time
  multiparty functionality admits a protocol secure against static malicious corruptions, with
  real/ideal simulation and abort, under the standard communication assumptions.
- **Regev's worst-case to average-case reduction.** For suitable `q` and Gaussian noise rate
  `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time
  algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`. The noise distribution, modulus
  restrictions and quantum reduction are part of the theorem.
- **Kilian's succinct arguments** ([#999]). If collision-resistant hash families exist, every
  language in NP has an interactive argument with polylogarithmic communication, by committing
  to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle
  versions.

### Modern fully homomorphic encryption

Gentry's bootstrapping is instantiated with GSW ([#486]; formal abstract `gsw-fhe`), including
uniform compactness for the leveled wrapper decryption circuits and level-indexed multi-hop
evaluation. Its remaining follow-up ([#1104]) is Gentry's exact concrete-security loss together
with the `poly(ℓ, d)` running-time clause of his Theorem 4. Then develop these in reviewable
milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions
where their hypotheses match. The [pre-rewrite FHE section][archive-fhe] maps the schemes to
current libraries and workloads.

1. **Ring arithmetic and RLWE.** Polynomial-ring operations over `(Z/qZ)[X]/(X^d + 1)`, RNS/CRT
   conversions, rounding and modulus-switching error bounds, and negacyclic NTTs implementing
   ring multiplication, with native certificates. Define the RLWE secret and error laws and
   experiment separately; an ordinary-LWE reduction does not give them.
2. **FHEW/TFHE programmable bootstrapping**
   ([Ducas–Micciancio](https://eprint.iacr.org/2014/816);
   [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870)). Ring-GSW external
   products, blind rotation, sample extraction and key switching; prove the bootstrap decrypts
   to `f(m)` with its noise, failure, width and runtime bounds, including negacyclic lookup
   restrictions and torus representations; floating-point FFT implementations need their own
   rounding-error proof. Then the [smaller-key methods of Lee et al.](https://eprint.iacr.org/2022/198)
   and batched variants, preserving their exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV** ([Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277);
   [Fan–Vercauteren](https://eprint.iacr.org/2012/144)). Slot encoding,
   multiplication, relinearization, rotations and level management, with leveled evaluation
   before a separately proved refresh. Equality modulo the plaintext modulus differs from
   ordinary integer equality, which needs a range bound.
4. **Approximate packed CKKS and its bootstrap**
   ([Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421)), with an explicit
   approximate-correctness interface and a norm bound on decoded error covering rescaling,
   rounding, key switching and rotations.
5. **Scheme switching and threshold variants**, with explicit range/precision contracts,
   evaluation-key assumptions, corruption thresholds, interaction, robustness and
   decryption-query access, distinguishing honest-but-curious from malicious security.

For each scheme, prove chosen-plaintext security for the actual algorithms and public evaluation
keys; keep LWE/RLWE, circular/KDM assumptions and attack-cost estimates distinct; introduce a
decryption-failure game when correctness is not perfect; and require nonvacuous parameter
families and full-input native runtime.

### Public-key, lattice and symmetric constructions ([#640])

- **Sigma protocols and Fiat–Shamir** ([#581]): computational Schnorr signatures under discrete
  log against strict PPT forgers; eavesdropping security in the strict-PPT model, with the
  statistical-distance term from sampling `ZMod q`.
- **Chosen-ciphertext security** ([#1885]): multi-challenge CCA from the single-challenge
  Cramer–Shoup theorem.
- **Lattices**: Fiat–Shamir with aborts and signatures from SIS (Lyubashevsky 2009,
  2012); strict-PPT samplers for integer boxes; identification security under SIS; efficiency
  certificates for the simulator and extractor; full interactive-view simulation; SIS for
  general moduli; module SIS and module LWE toward Dilithium-style schemes, as theory.
- **General:** reusable adaptive reductions, public-key encryption, universal-instance zero
  knowledge, hard-core predicates and hardness amplification, and connections to learning and
  average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643])

In order:
- the `PublicCoin → IP` bridge, with a uniform word verifier and adversarial decoding;
- parallel and AND/OR composition, and round-by-round knowledge soundness;
- oracle statements, so a later phase can query an earlier phase's oracle message (virtual
  output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds;
- efficiency-certified simulators and extractors, and auxiliary-input zero knowledge on the core;
- polynomial commitment and evaluation-query reductions, and the Ligero IOP;
- the BCS transform to non-interactive arguments in the random-oracle model;
- VOLE as an ideal functionality, and VOLE-in-the-head;
- libzk's compositional structure as a composition of these components, without ciphersuites.

### Concurrent and quantum security

- **Concurrent composition:** extend the protocol semantics with environments, scheduling,
  session identifiers and concurrent executions; prove a composition theorem with efficient
  simulators and explicit setup, corruption and communication assumptions. Then develop
  selected adaptive-corruption and non-malleability applications, alongside the static-malicious
  OT target.
- **Quantum-secure cryptography:** uniform quantum-efficient distinguishers, computational
  indistinguishability with quantum side information, and security reductions for concrete
  constructions. Connect the quantum-computation and lattice tracks through these adversary
  models; justify each reduction in that model. Later targets include quantum oracle access,
  the quantum random-oracle model, and extraction or rewinding under their precise hypotheses.

## Complexity classes and reductions

### Coverage catalogue

Build an auditable coverage index spanning the [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo)
and the canonical problems and theorems that ECCC papers need, verified against primary sources.
Each entry records its source and aliases, precise model and conventions, Lean declarations,
missing prerequisites and level (definition, partial development, verified theorem). Track
containments, separations, closure properties, complete problems and reductions separately, and
cover decision, function, search, counting, promise, distributional and parameterized problems,
with uniformity, advice, oracle access, error gaps, resources and reduction types explicit. The
index links to canonical definitions rather than keeping a second set.

### Structure, time and space

- Time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes;
  completeness, padding, self-reducibility, relativization and oracle separations, preserving
  each reduction's resource bound.
- **Time hierarchies** ([#1572]): native polynomial padding separates every pair of integer
  degrees `1 ≤ a < b`, in deterministic and in nondeterministic time, and the `O(t log t)`
  universal simulation ([#800]) gives `DTIME f ⊂ DTIME g` for time-constructible `f ≥ n` once
  `(f + 1) * polylog f ≤ g`, with an absolute exponent (`Hierarchy/TimePolylog`). Composing it
  with the word-RAM simulations gives `RAMTIME T ⊂ RAMTIME T⁵` over `Basis.additive` for
  polynomial `T` (`Hierarchy/WordRAM`). For nondeterministic time, padding amplifies the coarse
  lazy-diagonal hierarchy, which separates degree `d` from degree `6 * d + 14`; lazy
  diagonalization also separates `NTIME (2 ^ (k * n))` from `NTIME (2 ^ ((8 * k + 16) * n))`, so
  `NE ⊄ NTIME (2 ^ (k * n))`. Remaining targets
  include the textbook `f log f = o(g)` hierarchy, which needs the diagonal to clock the universal
  machine's own steps, noninteger polynomial degrees, a word-RAM hierarchy by direct
  diagonalization with a smaller gap, and sharp nondeterministic and alternating time
  hierarchies with certified simulators.
- **Probabilistic time hierarchies** ([#2084]): the hierarchy for promise problems
  (`PromiseBPTIME`), by delayed diagonalization following He (ECCC TR25-004), and the
  one-bit-advice hierarchy for languages of van Melkebeek and Pervyshev. `PromiseBPTIME` and its
  explicit-time sample-and-verify characterization are in place (`Classes/Promise/Time` and
  `Classes/Promise/Time/Verifier`). The advice-free hierarchy for `BPTIME` itself is open and is
  not a target.
- The space hierarchy for `log n ≤ g n`, which needs a universal simulation that does not hold
  its input.
- **Space:** Savitch bounds for general space-constructible functions.
- **Randomized logspace** ([#459], [#474]): RL and BPL, `USTCON ∈ RL`, Nisan's generator,
  `BPL ⊆ L²` and Saks–Zhou. The preprint route to native `RL = L` remains open in
  [#1444](https://github.com/cslib-community/complexitylib/issues/1444). Its estimator work in
  [#1721](https://github.com/cslib-community/complexitylib/issues/1721) has an integer-grid slack
  schedule with endpointwise telescoping and summable available-scale precision payments.
  Actual correction iterates now supply product entry/row-mass bounds and their scheduled
  omitted-product norm sum. Product-seed correction/reward samples have proved true means,
  reaching the next actual hierarchy reward. The local pilot and actual-correction
  preparation/normalization families now share an expanded dependency order, including
  normalized children and an actual copy/reward projection client. Ranks are computed from
  finite iteration bounds; role/rate/suffix requests preserve the inherited source or reset it
  to the midpoint. Pilot steps use the current maximum; actual corrections and copy weights
  use the final pilot maximum. A bounded cross-stage hierarchy/reward client now connects
  the previous-reward and base-matrix leaves to actual earlier-stage constructors, with a
  computed decreasing global rank and nonconstant two-stage regression. Routed direct/residual
  bins now have a finite partition/true-mean client into the actual next matrix, primitive
  affine sampling instances, native copy-symbol suffix laws and whole-function role/rate/usage
  requests with computed rank payments. Signed residual evaluation now separates the negative
  endpoint correction from the midpoint product correction, with actual tuple-dependent sample
  means. Bounded top-bin routing and dense preparation/normalization accept arbitrary child
  functions, retain raw ranks, and agree with actual hierarchy bounds in a two-stage client.
  The residual-bin phase order is local; full global stochastic preparation/access enumeration,
  finite-accuracy ports, estimated copy/routing-fraction comparisons, and the complete scheduled
  mean-prefix bound remain open; range/true means do not establish root
  regularity or the error recurrence. Paired raw differences, full-coordinate conditional walks, summed noise, compression, strong recursive
  induction and native logarithmic workspace/class equality remain required.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a
  logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888]): implicit Tree Evaluation with the
  fan-in-`d` space bound and the native block-tree evaluator are developed in the stacked
  work tracked by the issue. The full `DTIME_subset_DSPACE_sqrt` inclusion is proved in
  `Complexity/Computability/Complexity/Classes/TimeSpace/Williams.lean` for arbitrary
  injective input encodings and every `t(n) ≥ n`, without time constructibility. Its fixed
  driver scans the original input, searches schedules and increases balanced time guesses.
  The stacked development still needs final CI and integration; the broad issue remains
  open until it lands. For Cook–Mertz itself: malformed-input handling
  and the refined `O(ℓ + H log(ℓ + 2))` parameter bound.
- Alternating time and space classes and bounded-alternation characterizations of PH; sharp
  bounds for sublinear space, distinct from polynomial-space simulation.
- **Deeper consequences of a Boolean-hierarchy collapse:** Kadin's sparse `S` with
  `coNP ⊆ NP^S`, and the collapse of `PH` into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, which follows from
  results of Wagner and of Chang and Kadin, not from Kadin's 1988 argument (see his erratum).
  `BooleanHierarchy/Kadin.lean` proves only `PH = Σ₃ᴾ ∩ Π₃ᴾ`.

- **Explicit universal SAT solver:** construct one fixed native algorithm, independent of an
  assumed fast SAT algorithm, and prove its worst-case running time is polynomial if and only if
  `P = NP`. Specify a total SAT decision procedure, including unsatisfiable inputs, separately
  from verified witness search; account for dovetailing, certificate checking and universal
  simulation overhead rather than relying only on the existing `SAT ∈ P ↔ P = NP` equivalence.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351]): logspace Turing reductions, in an oracle model whose query tape is
  not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of
  Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets:** `P/poly ⊆ P^SPARSE` (Meyer), the converse of
  `PWithOracle_subset_PPolyOn` in `Classes/Sparse/Turing.lean`. After Kadin's
  `PH ⊆ P^{NP[O(log n)]}` (`Classes/Sparse/Kadin.lean`, [#2062]): `P^{NP[O(log n)]} ⊆ Σ₂ᴾ ∩ Π₂ᴾ`,
  hence `PH = Θ₂ᴾ` under his hypothesis; his stronger form with a sparse `S ∈ NP` and
  `coNP ⊆ NP^S`; and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** p-isomorphism and paddability; paddable NP-complete sets are p-isomorphic,
  so the standard NP-complete problems are all p-isomorphic to SAT; the isomorphism conjecture as a
  hypothesis; every many-one complete set for EXP is complete under one-one, length-increasing
  reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal,
  Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so
  every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang);
  separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and
  Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468]): the full expanded 2013 paper of
  Glaßer, Nguyen, Reitwießner, Selman and Witek: native transfer from local self-reducibility
  (Lemma 3.3), including virtual-input/answer regeneration and adaptive-to-tt conversion.
  Uniform runtime initialization, virtual-word reads and a two-pass Boolean-state native
  evaluator are certified; arbitrary logspace query-generator/evaluator consumption, supplied
  header preparation, answer regeneration and the resource-certified suffix loop remain open;
  bounded and many-one self-reducibility specializations; concrete complete self-reducible
  problems (Theorem 3.5); Section 4
  bounded/logarithmic-query results and
  separations, and Section 5 mitoticity/diagonalization. The additional parity-logspace
  application needs a native path-counting class and complement closure.
- **Uniform diagonalization** (Schöning), which generalizes Ladner's theorem.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE.
  P-selective sets (Selman): a P-selective NP-complete set gives `P = NP`, P-selective sets lie in
  `P/poly` (Ko), and self-reducible P-selective sets lie in P.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and
  so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity:** immune and bi-immune sets, P-bi-immune sets in EXP (Balcázar and Schöning), and
  almost-everywhere hardness.

### Average-case complexity

- Distribution ensembles with computability and samplability certificates; distributional
  reductions with explicit domination and resource bounds; DistNP, errorless average-case
  classes and heuristic classes, keeping runtime tails and permitted error distinct. Reuse the
  specialized Liu–Pass hardness notions through proved bridges.
- **Levin completeness:** a distributional bounded-halting problem complete for the chosen
  polynomial-time computable-distribution class, followed by a separately scoped extension to
  samplable distributions. Connect the framework to one-way functions, learning and the
  metacomplexity track ([#798]), preserving the distribution and reduction conventions.

### Counting and modular classes

- The Another Solution Problem (ASP) framework: certify polynomial-time forward and inverse
  witness maps. The parsimonious reductions to positive exact-one SAT and its planar
  three-occurrence variants already preserve counts over occurring variables; the new local
  replacements have constant-factor growth and preserve the earlier linear grid sides and
  quadratic planar costs. See the [reduction catalogue](guide/ComplexityGuide/NPCompleteness.lean)
  for the completed NP-completeness and NP-hardness endpoints. Exact count preservation alone
  does not supply the ASP runtime certificates.
- Counting reductions and further oracle results preserving exact multiplicities; permanent
  #P-completeness; modular and counting hierarchies; the oracle-algorithm form of Stockmeyer's
  approximate counting.
- For composite moduli: the prime-power collapse `Mod_{p^e}P = Mod_pP` and union closure.
  Complement closure for moduli that are not prime powers is open, and relativizing proofs
  cannot give it (Barrington–Beigel–Rudich), so it is not a library direction.
- Target-relativized `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and
  UP-oracle containment.
- Native oracle counting machines: efficient encoded oracle checking, response-access costs and
  oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **MIP = NEXP** ([#892]): `NEXP ⊆ MIP₂` through the BFL multilinearity test and arithmetization
  of exponential-time tableaux; an efficient GKR verifier under log-space uniformity.
- Private-to-public-coin transformations, `AM[k] = AM`, interactive-machine characterizations
  of Arthur–Merlin classes, and statistical and perfect zero knowledge.

### Descriptive complexity and first-order reductions

Ordered first-order complexity follows Immerman: structures on `{0, …, n-1}` with `n ≥ 2`, FO
means FO(≤, BIT), and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings; the order-free
`FO.Reduces` and `FO.QFReduces` stay as a general layer. Numeric predicates are computed from the
universe size, not supplied as unverified input tables. In dependency order:

- **Ordered completeness.** SAT, 3SAT, 3COL, independent set, clique and vertex cover
  NP-complete under first-order or quantifier-free projections; REACH NL-complete under
  first-order reductions.
- **Projections:** projection reducibility on finite structure classes and the standard ordered
  machine-encoding bridge. The classical qfp convention excludes BIT (Immerman–Landau,
  Definition 3.6), and arbitrary quantifier-free combinations of input relations are not
  projections.
- **Circuit Value P-complete under first-order reductions**, via `REACHa → MCVP → CVP` (Immerman,
  Theorem 3.26 and Exercise 3.28), with the alternating-logspace simulation of polynomial-time
  machines and the translation to `encCircuitValue`.
- Numeric certificates for further restricted-domain families; canonical BIT on a restricted
  domain need not be first-order definable.
- Order-free: SAT-to-3SAT, graph-property hardness, and bridges to the separately encoded
  problems.
- Extend the synthesis rules to nested operator bodies and give regular-language quantifiers
  their ordered characteristic-word semantics.
- Further logical characterizations on ordered structures: FO(TC) = NL and FO(DTC) = L,
  SO-Horn = P (Grädel), and DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing);
  then order-invariant and fixed-point queries and uniform translations between syntax,
  structures and algorithms.
- A witness-carrying reduction structure once a client needs one, for example size bounds for
  Cook–Levin.
- **Logical lower-bound methods:** Ehrenfeucht–Fraïssé and pebble games with their logical
  equivalence theorems, locality and concrete nondefinability results; then counting and
  fixed-point expressiveness, including Cai–Fürer–Immerman-style separations. Reuse upstream
  model-theoretic foundations and connect the methods to the ordered capture theorems.
- **Dynamic descriptive complexity:** dynamic programs and update semantics with explicit
  initialization, auxiliary relations and domain conventions; invariant-preservation rules and
  reachability in DynFO as a target. Relate logical update restrictions to the stateful-algorithm
  interfaces through explicit translations.

### Uniform circuit families

Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and input
encodings; certify circuit generation, evaluation and the machine-to-circuit simulations,
preserving size, depth and construction resources; and prove FO with order and BIT equals
DLOGTIME-uniform AC⁰ under explicit conventions.

### Search, parameterized and fine-grained complexity

- **TFNP:** CLS, further local search, fixed-point and equilibrium problems.
- **Parameterized:** strongly uniform variants (computable `f`), further explicit polynomial
  kernels, the W and A hierarchies, and parameterized lower bounds; connect these to
  [structural graph algorithms](#structural-graph-algorithms) and their decomposition costs.
- **Exponential-time SAT** ([#894]): Schöning, PPZ and PPSZ run on the randomized word RAM with
  exact laws, amplification and time bounds (PPSZ's round count takes an input bound
  `a / b ≥ 1 - qbar k h`). Remaining: curated abstracts, and the uniform `o(n)` forms of the PPSZ
  bounds with `w` growing in `n`.
  Further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886]): for `0 < ε < 1/8`, NP-hardness of
  distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most
  `7/8 + ε` of the clauses. This needs Raz–Holenstein parallel repetition for small-soundness
  Label Cover and Håstad's separate perfect-completeness construction for MAX-E3SAT.
- The FGLSS clique-hardness reduction and its amplification, retaining the exact gap and
  reduction runtime.
- Gap and approximation-preserving reductions, APX/PTAS/FPTAS, inapproximability consequences of
  PCP, CSP classifications and relaxation gaps, with assumptions such as the Unique Games
  Conjecture stated explicitly. The 2-to-2 games theorem waits for [#886].
- **A practical PCP construction:** a reasonably runnable construction and its cost on complete
  reductions; rotation certificates polynomial in the bit length of a vertex name; machine-level
  error reduction and extractors from expander walks, with certified seed and evaluation costs.

### Proof complexity

- Proof-space lower bounds, Frege, cutting planes, polynomial calculus and sum-of-squares, and
  certified DPLL solver runtimes.
- **Feasible interpolation** ([#1817]): the transfer of communication lower bounds to proof-size
  lower bounds ([#2019]).
- **Proof search:** automatizability and weak automatizability with explicit encodings and
  runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow
  and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.

## Circuits and algebraic complexity

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889]): no polynomial-size,
  constant-depth circuits over AND, OR, NOT and fixed-modulus counting gates for some language in
  NEXP.
- **Circuit lower bounds from refuting ETH** ([#1539]): `E^NP ⊄ SIZE(O(n))`, and a language in
  `E^NP` whose fan-in-two circuits need more than `c n √log n` gates infinitely often, by
  Williams's witness-circuit argument with the library's #CircuitSAT counters. `E^NP` is defined,
  and the witness bits of formulas prepared in time `2^O(n)` are in `E^NP`.
  `FineGrained.CircuitLowerBoundBudget` proves the counter's quantitative budget for three
  circuits of size `n √⌊log₂(n+2)⌋ / (12(A+1))` plus linear overhead; the integer arithmetic,
  polynomial-time computation of this size cap, and rescaling to coefficient
  `1 / (24(A+1)d)` at framed lengths `d n` are checked. The exponential nondeterministic time
  hierarchy has landed. Still open are connecting its separating language to the framed witness
  preparation, uniformly constructing the linear-size decoder and checker, and completing the
  nondeterministic simulation for the full separation theorem.
- Uniform and nonuniform NC, AC and TC, circuit-to-machine bridges, algorithm-to-lower-bound
  arguments, and barriers such as natural proofs and algebrization. NC simulation of unrestricted
  `TCⁱ` needs Muroga's threshold weight-bounding theorem.
- Formula lower bounds beyond Andreev's, following Jukna; Raz–Wigderson's monotone depth bound for
  matching on general graphs.
- **Monotone circuits versus P:** Razborov's `n ^ Ω(log n)` monotone bound for bipartite perfect
  matching is proved ([#2063]); the separation also needs bipartite perfect matching in
  `Complexity.P`.
- **An explicit frontier extractor:** port v1's sumset-extractor construction with an explicit
  family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses. It would
  exceed the library's unconditional `3.5 N - o(N)` bound in P, so it needs an independent
  correctness review of the frontier core.
- **Weighted threshold representations:** v1's explicit source-reduction family, universal scalar
  circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting.
- **Depth-two threshold circuits for Andreev's function** ([#2347]): the exact quadratic
  `4 * 4 ^ b + b * m * 2 ^ b + 1` depth-two weighted threshold upper bound
  (`WeightedThreshold/Andreev.lean`), the windowed average-case `(1 - δ)`-agreement and
  `(1 / 2 + ε)`-correlation depth-two upper bounds (`WeightedThreshold/AndreevWindowed.lean` and
  `WeightedThreshold/AndreevAverage.lean`), Erdős–Littlewood–Offord anti-concentration
  (`Combinatorics/LittlewoodOfford.lean`) together with the repaired Kane–Williams gate and wire
  random restriction lemmas (`WeightedThreshold/RandomRestriction.lean`, Lemma 1.1 and Lemma 3.1 of
  arXiv:1511.07860v1), the `b`-variable LTF and depth-two threshold function counting bounds
  (`WeightedThreshold/ThresholdCounting.lean`, Theorem 2.3 and Section 4 of arXiv:1511.07860v1), and
  the fixed-weight quadratic-in-`ε` average-case `Ω(ε² n ^ (3 / 2) / log² n)` gate and
  `Ω(ε² n ^ (5 / 2) / log ^ (5 / 2) n)` active-wire lower bounds for
  `3 * (b + 2) / √(2 ^ b) ≤ ε ≤ 1 / 2` in the balanced regime
  (`WeightedThreshold/AndreevLowerBound.lean`, improving the
  `ε³` dependence in Theorem 1.1 and Section 5 of arXiv:1511.07860v1) are proved; closing the
  worst-case depth-two threshold gate gap between `Ω̃(n ^ (3 / 2))` and `O(n ^ 2)` remains open.
- **Construction runtimes**, certified separately from gate counts: the mass-production
  constructors, with constructive choices of information sets and line menus; the
  iterated-function preprocessing; and the bit complexity of formula evaluation on the rational
  hitting-list matrices.
- **Algebraic complexity** ([#891]): the rest of Limaye–Srinivasan–Tavenas. Proved: simple
  circuits (product gates reading distinct wires) of constant product-depth computing iterated
  matrix multiplication need superpolynomial size over any field, at `d = ⌊log₂ ⌊log₂ n⌋⌋`, from an
  explicit bound with exponent `d ^ (1 / (4 ^ Δ - 1))`. Remaining: their semantic set-multilinear
  model; growing `Δ` with exponent `d ^ exp(-O(Δ))`; the `√d` bound at `Δ = 1` (LST Lemma 13 and
  Corollary 4); the full range of `d`; and the `0/1`-substitution remark. Also the
  Kabanets–Impagliazzo theorem (a deterministic PIT algorithm implies NEXP ⊄ P/poly or the permanent
  has no polynomial-size arithmetic circuits); Valiant's VNP-completeness of the permanent over
  fields of characteristic other than two (membership now has an explicit Ryser witness over
  every commutative ring; VNP-hardness remains open); formula and branching-program models,
  identity testing, hitting sets, and tensor and rank methods, including partial-derivative
  measures (Nisan–Wigderson depth-3 bounds and shifted partials) and the depth-reduction chasms at
  depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform
  construction costs certified
  separately from gate counts.
- **Real-algebraic decision procedures:** port the Sturm–Tarski query evaluator, recursive
  evaluator, implicit arithmetic, native space certificates and the ETR upper bound from
  [lean-canny](https://github.com/SamuelSchlesinger/lean-canny).

### Jukna coverage

Formalize the established results, constructions and worthwhile exercises of
[Jukna's *Boolean Function Complexity* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html),
with the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html), auditing
each statement against the numbered result. Organize modules by subject, not chapter.

| Chapters | Next coverage work |
| --- | --- |
| 1–2: foundations and Boolean analysis | Counting, graph complexity, degree and approximation results; the partial-function circuit upper bounds that use Lemma 1.17. |
| 3–5: communication | Matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | Remaining formula and monotone bounds; span programs and negation complexity. |
| 11–13: depth restrictions and general gates | Depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | Bounded-read and bounded-time lower bounds and the remaining tree results. |
| 18–19: proof complexity | Proof-space and cutting-plane lower bounds. |
| 20: barriers and further methods | The book's generator, natural-proof, fusion and indirect lower-bound results. |

## Pseudorandomness, coding and Boolean analysis

- **Derandomization from hardness:** the infinitely-often variant, and the EXP ⊄ P/poly endpoint
  of Babai, Fortnow, Nisan and Wigderson.
- **Extractors** ([#895]) beyond Chor–Goldreich: two-source extractors for lower min-entropy,
  where the `t`-wise independent parts of Chattopadhyay–Zuckerman's Theorem 4.1 are formalized with
  exponent `O(d²)` in place of their `3 d + 6` (the almost `t`-wise independent parts are not), with
  Tribes as a small instance (coalitions of fewer than `w` bits only), and their resilient functions
  (Theorems 3 and 4) and extractor (Theorem 1) are not yet formalized;
  condensers, limited independence, explicit expanders and space-bounded generators, with finite
  guarantees separate from uniform construction and decoding costs.
- **Codes:** Guruswami–Sudan list decoding and local decoding, keeping interpolation,
  list-size/agreement guarantees and decoding runtime as separate obligations; concrete
  list-decodable codes for Nisan–Wigderson.
- **Boolean analysis:** hypercontractivity beyond `p ≤ 2 ≤ q` and its applications.
- **Resource-bounded measure and dimension:** martingales and gales with explicit computation
  budgets, their success sets, and measure and dimension within complexity classes; connect
  quantitative randomness to the Kolmogorov-complexity development. State the resource bounds
  and uniformity of the betting strategies separately from ordinary measure-theoretic facts.

## Communication, queries, learning and other models

- **Lifting** ([#890]): applications of deterministic lifting, such as partition-number
  separations, and randomized lifting.
- Multiparty protocols, discrepancy and information complexity, direct-sum and direct-product
  results, and reductions to streaming, sketching and cell-probe lower bounds.
- **Streaming and sketching:** native time and space bounds for Count-Min, including hash-seed
  storage and evaluation; AMS frequency moments, CountSketch, turnstile updates, and heavy-hitter
  recovery; communication-to-streaming transfers with explicit state encodings and pass counts.
- **Learning:** machine-certified running times for the LMN and Kushilevitz–Mansour learners;
  distributional problems and reductions, samplability, average-to-worst-case connections,
  PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Give the
  computational–statistical gap program concrete clients: an SQ oracle with tolerance and query
  costs, statistical-dimension lower bounds for a specified planted problem, and corresponding
  sample and runtime upper bounds. Develop low-degree likelihood-ratio and sum-of-squares
  comparisons where justified, distinguishing restricted-model bounds from unrestricted
  computational hardness. Use the [distributional framework](#average-case-complexity).
- **Property and distribution testing:** independent repetition of Boolean local tests and BLR
  linearity testing have explicit decision-tree query bounds. Remaining: further access models,
  tolerant and distribution testing, query and sample bounds, canonical testers and lower bounds.
- **Kolmogorov complexity and metacomplexity** ([#798], [#884]): the near-linear threshold regime
  of Liu–Pass Theorem 3.1 (c), hardness for every polynomial `t(n) ≥ (1 + ε)n` rather than above a
  polynomial threshold, which needs a rate-1 efficient conditional EP-PRG running in `n + O(n^c)`
  multi-tape steps for a constant `c < 1`; prefix-free complexity,
  resource-bounded MCSP variants and connections to learning, cryptography and lower bounds; the
  circuitized anti-checker with an efficient generator; the asymptotic parameter instantiation of
  Theorem 5 as a concrete rounded-threshold, ternary-device statement; and hardness results for
  `MINKT` and `MINcKT` (whose
  definitions, conditional `K^t` measure, and `NP` memberships are in `Kolmogorov/MINKT.lean`,
  `Kolmogorov/Conditional.lean`, and `Kolmogorov/MINcKT.lean`), as independently scoped
  developments; the reverse
  multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding.
- **Quantum computation** ([#896]): channel semantics and approximation costs alongside the
  circuit and measurement semantics, reusing suitable quantum foundations rather than
  incompatible models, and a bridge between the query and circuit models; complete problems for
  BQP; QMA and related query, communication and interactive classes, with amplification,
  containments and complete problems. Supply the
  [quantum adversary models](#concurrent-and-quantum-security) needed by cryptographic
  reductions.

- **Shor's algorithm:** bounded-error polynomial-time integer factoring and discrete logarithms
  in the native uniform quantum-circuit model, with explicit input/output encodings, success
  probabilities and gate-approximation costs. Develop quantum period/order finding and phase
  estimation, the quantum Fourier transform, reversible modular exponentiation, continued-fraction
  recovery and the classical reductions; certify uniform circuit generation and polynomial gate
  bounds alongside correctness.

### Differential privacy and adaptive data analysis

- Dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with
  postprocessing and adaptive composition. Start with a finite or discrete mechanism proving
  both privacy and utility, including sampling cost and finite-precision error.
- The exponential mechanism, private query answering and private learning; privacy–accuracy
  and sample-complexity lower bounds; then adaptive data-analysis and generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources
  explicit, reusing the probability, oracle-computation and learning APIs.

## Algorithms and optimization

### Optimization and duality

- **Linear programming:** rational input and output encodings, primal and dual certificates,
  weak and strong duality, and infeasible or unbounded outcomes. Reuse Mathlib's convexity and
  linear-algebra foundations; certify certificate checking and a polynomial-time LP algorithm
  with bit complexity and intermediate precision accounted for.
- **Separation and optimization:** a precise oracle interface and a separation–optimization
  equivalence with its representation, accuracy and well-boundedness hypotheses. Extend to
  convex optimization through explicit oracle and numerical-error contracts.
- **Primal–dual approximation and multiplicative weights:** reusable analyses with vertex cover
  and set cover as first primal–dual clients; multiplicative-weights regret and approximation
  bounds with finite-precision implementations, then applications to games, learning and
  optimization.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations),
reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** integral max-flow/min-cut and a native augmenting-path algorithm with
  charged runtime; then minimum-cost flow and weighted bipartite matching through common
  residual-network and duality machinery.
- **Matroids:** matroid intersection with explicit oracle and implementation costs, beyond the
  weighted greedy algorithm and its independence-oracle interface.
- **Submodular optimization:** further constraints and approximation bounds beyond the
  cardinality-constrained `1 - 1/e` greedy, charging value-oracle calls separately from their
  concrete realizations.

### Online algorithms and competitive analysis

- Request sequences, online strategies, offline optima and competitive ratios with additive
  constants; distinguish deterministic and randomized strategies and oblivious and adaptive
  adversaries. Compare algorithms in the same action and cost model, including initialization.
- **Adaptive search trees:** working-set and dynamic-finger bounds for splay trees, and a BST
  access-and-rotation model with Wilber-style lower bounds. State dynamic optimality as a
  conjectural research target with explicit strategy and sequence quantifiers.

### Structural graph algorithms

- Tree decompositions, width and normalization into a suitable decomposition form; a reusable
  dynamic-programming evaluator over a supplied decomposition, with state-space, transition,
  join and runtime bounds. Start with native independent-set, coloring and SAT/CSP decision and
  counting clients, specifying the graph whose width is measured.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style
  theorem with computable parameter dependence on width and formula size. Keep the supplied
  decomposition and its encoding explicit; certify decomposition finding separately. Connect
  the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Markov-chain sampling:** finite kernels, stationarity, reversibility and total-variation
  mixing; coupling, path coupling, conductance and canonical-path arguments. Implement
  Metropolis sampling for encoded rational target weights, charging initialization, arithmetic
  and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling:** interfaces separating relative error, failure
  probability, output-distribution error and runtime, including zero-count instances. Start
  with a complete DNF-counting FPRAS; prove sampling/counting reductions for suitably
  self-reducible relations, with the sampling and counting oracle costs included.
- Extend to randomized approximate counting for matchings and permanents of nonnegative
  rational matrices through explicit mixing and reduction theorems. Reuse the coupling and
  expander APIs and connect to the separate Stockmeyer oracle-counting track where their
  hypotheses agree.

### Constructive probabilistic methods

- **Moser–Tardos resampling:** an actual resampling program, its correctness and expected
  resampling bound, and native sampling and event-detection costs, building on the variable
  form of the Local Lemma.
- **Conditional expectations and pessimistic estimators:** certified choice and update rules,
  algorithmic alteration, and concrete coloring, satisfiability or combinatorial-construction
  clients. Preserve the quantitative guarantee when converting an existence argument into a
  deterministic or randomized algorithm.

## Machines, RAM and data structures

- **Efficient universal simulation** ([#800]): the clocked universal function runs in time
  `O(N + poly(D, M) · (t + 1) log(t + 2))`, for encoded input length `N`, description length `D`
  and largest input symbol `M`, by a divide-and-conquer windowed simulation
  (`computableInO_universal_nlogn`). Remaining: a source-space-sensitive storage bound (the
  space is currently bounded only by the time), and an unclocked form that runs until the
  simulated machine halts.
- **Plain computability** ([#862]): complete the plain calculus ([#608]), delete the tidy
  calculus, keeping only a machine-level kernel inside the Machines layer, and switch the
  abstract bridges to the shared predicate.
- **Certificate APIs and automation** ([#1155]): predictable search, with fixed heartbeat budgets
  on regression goals, failures that name the subterm lacking a certificate, and cheap
  syntax-directed composition for glue code. Infer encodings for ordinary functional expressions
  through constructor, projection, lookup and composition rules; generalize list, bounded-table,
  cache and nested-loop invariants where clients need them; keep separate time, workspace and
  output-size bounds through composition; apply cumulative streaming contracts to captured
  iteration and nested loops; certify PRG stretching with seed length, rounds and generator cost
  kept separate; and develop general open-program composition. Use Cook–Levin and GGM as
  regression clients. Improve configuration views, tape partitions and handoff identities only
  where several clients benefit, keeping machine transitions out of global simp.
- **Mathlib TM2:** sublinear work-space comparisons and a linear-space forward simulation.
- **Generic RAM:** uniform arbitrary-program dispatch and general width-selection and input-fit
  theorems; simulating operations by programs over smaller bases; structured programs and time
  classes over arbitrary value domains with weighted or bit costs; simulations between instances;
  the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Word RAM:** an AC⁰ basis; wider-fragment and Turing-machine simulations;
  transfer of Anthropic's modular machine and 3SUM/APSP algorithms; size-based width selection
  with an input-fit guarantee and explicit overhead;
  expected-time rules for unbounded almost-surely terminating structured loops; random-tape
  equivalence and BPP/RP/ZPP simulation bridges for the randomized word RAM ([#1124]); transfer
  of cell-probe lower bounds; and the Horn-SAT, 2SAT, matching and domino-tiling clients.
- **Sharper native Exact Triangle exponent** ([#2423]): the automatic box-backed Exact Triangle
  host runs in `Oκ(n^(3−33/20000))` (exponent 2.99835) after integer retuning; reaching the
  source's stated 2.9983 under the same native conventions remains open.
- **Memory-oracle realization** ([#2205], [#2213]): the foundational graded kernel certifies
  all four memory queries, register-word glue, native branches and binds with one fixed
  continuation emitter for all runtime replies. Its functional representation retains the
  complete memory and frontier, and its instruction currency adds local work to memory charges.
  Bounded runtime loops also charge local computation and every iteration, including query-free
  iterations. Fixed flat programs include the actual input-installation prefix and final halt,
  with explicit input layout, fits and safe-domain hypotheses. A separate operation-level
  memory implementation exposes body-only costs under delivered arguments. Existing framed
  Word-RAM certificates can be derived from semantic modules after discharging their local
  initialization, footprint and ABI conditions; a one-cell ADT checks that boundary. Multiword
  glue preserves full-word Option payloads, and the actual memory-stack size/push/pop methods
  have uniform native certificates over runtime layouts, with local work 0/10/19. The stack is
  migrated: `Stack.Native` and `Stack.Controller` replace its hand-stepped dispatcher, which
  remains only as the stepped component of Chan–He traversal (`Traversal.WordStack`). Backends of
  framed refinements export their frame (`modifies`, `frame`), run products over one memory,
  and allocate from arbitrary memory through `Memory.Allocator` (`Backend.Allocation`); the stack
  and a pair of stacks check all three. Queue operation calls now use one fixed native
  dispatcher over physical-array memory programs, with resident count words and paid commits.
  Its dynamic certificate preserves the original two-array space, dirty six-instruction
  initialization and adaptive-call bounds. The binary heap now realizes its original memory methods
  and allocator, retains compact local-zero initialization and a genuine linear dirty clear, and
  supplies the original log-linear Dijkstra endpoint through an actual initialized native program.
  The graph encoding and word envelope stay unchanged; one factor precedes all graphs and widths,
  and the clock includes the prefix, control and halt. The old hand-stepped binary execution is
  retired, while its pure model/order lemmas and source credit remain. Remaining are the full
  framed queue/faithful-allocation client, generic stateful and whole-client composition, Fibonacci
  execution migration and the full C2/M1b objective; arbitrary host continuations do not acquire
  runtime bounds.
  The Fibonacci method family ([#2290]) realizes all five original memory methods with one fixed
  native factor, exact typed-source/history transport and the existing nonzero amortized
  potential. The Fibonacci Dijkstra consumer now reserves the original zero tail without clearing,
  derives its reached callee domains from the shared framed history, and pays the nonzero heap
  potential through the existing amortized telescope. One actual initialized native program
  retains the original word envelope and sharper reachable-vertex bound, including its prefix,
  control and halt and the entire final memory/frontier. The old Dijkstra executor and its
  implementation-specific coefficient 640 are superseded; the original existential endpoints
  are unchanged. MinPQ migration and the execution core it still uses remain open, as do generic
  whole-client transfer and the abstract-space decision.
  The Karger–Stein specification bridge ([#2289]) gives the existing recursive native code the
  exact answer law of its contraction-oracle client, preserving pathwise instruction/random-call
  bounds, word fits and memory frames. Probability and amplification are proved at the
  specification layer. This does not complete its memory-oracle native realization: the
  randomized realization adapters, contraction implementation and recursive frame-stack
  migration remain part of [#2205].
- **Stateful algorithms and data structures:** Word-RAM controllers for larger adaptive and
  iterative clients, including the two-stack queue and timeline-editing controllers; reusable
  allocation and deallocation, shrinking, and live and peak space accounting; ownership and
  recursive procedures; model realizations for cell probes, caches and randomness; present and
  historical queries for the retroactive interface; balancing and heap or RAM representations of
  search trees; uniform preprocessing and dynamic updates for fusion trees; deletion and
  predecessor for van Emde Boas sets; and deallocation,
  shrinking and compiled client controllers for the doubling array.
- **A typed-call evaluator** for fixed-program Word-RAM clients, returning the typed observation,
  final state and halt-inclusive instruction cost, so the prefix-sum clients no longer
  assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#949]): lift operation-count helpers
  (`numQueries`, `numInserts`, `numDecreaseKeys`, `numExtractMins`) to `IndexedMinPQ`, parameterize
  flat-program operation-sequence execution (`RunsOps`) over `PQCode` in
  `DataStructure/PriorityQueue/WordRAM/Basic.lean`
  so `BinaryHeap` and `FibonacciHeap` share a generic `run_ops_exact` theorem, and factor a common
  `ShortestPathSpec p bound` predicate in `Dijkstra/HeapStatement.lean` across `LogLinearSpec`,
  `FibonacciSpec`, and `FibonacciLinearSpec`.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** work–span semantics and a processor-scheduling or simulation theorem,
  followed by prefix scan, sorting and graph primitives with both work and span bounds. State
  processor access, synchronization and scheduling overhead explicitly.
- **Memory hierarchies:** external-memory and ideal-cache models with explicit capacity and
  block-size parameters; scanning, B-tree operations, blocked matrix multiplication and
  cache-oblivious sorting as clients. Connect arithmetic-step, memory-access and cache-miss
  bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity:** LOCAL and CONGEST models with explicit identifiers, round,
  message-size and randomness conventions; locality lower bounds and communication-to-round
  reductions with corresponding algorithmic examples.

## Coverage and reuse

The long-term bar is to support formalizing every paper in the
[Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/),
with the additional work per paper increasingly its new mathematics: standard models,
representation changes, reductions, resource certificates and proof techniques come from the
library. Use a growing, source-pinned sample of papers, including some chosen after an API was
designed, as demanding clients, and promote recurring obligations into shared APIs only after
reuse is demonstrated.

- **One sensitivity API.** Define the sensitivity measures over any `Fintype` in CSLib and drop
  the separate measures of the sensitivity-separation development.
- **CNF evaluation certificates:** `fun_prop` certificates for evaluating literals, clauses and
  formulas under a polynomial-time assignment, so clients stop passing `CNF.eval`,
  `Clause.eval` and `Literal.eval` to `fun_prop` as unfolding hints.
- Factor indicator-expectation identities from PCP's second-moment calculation, and recurring
  cardinality and logarithm conversions, once a second client benefits.

### OpenAI math results ([#1002])

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI
math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the
openai/math release, and extract the results in scope: the headline theorems and also the minor
lemmas useful in their own right. Prove each against Complexitylib's own definitions, from the
cited manuscript's exact statement with its version pinned; a source formalization is a
reference, not evidence. Label unrefereed results as such. The openai/math formalizations are
Apache 2.0, as is Complexitylib, so adaptation with attribution is permitted. The practice is
still to read them for the mathematics and write proofs against Complexitylib's definitions; any
adapted code keeps its Apache 2.0 attribution. The rewrites state no license and are only read
and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/complexitylib/issues/1538)):
  `ContractionCounting.exists_modelCounter_fixedDensity` proves the fixed-density bound
  `2^{O_{k,D}(n / √log n)}` by tensor contraction (Theorem D.1 with `ℓ = 1`), and
  `DensityBranchCounting.exists_modelCounter` combines it with the interpolation-scale counter in
  one machine. `CountingSimulation.truncEntryContractionAlgorithm` now supplies polynomial
  truncation order and precision `O(s log s)`, with a linear vertex bound. The arbitrary-density
  bound `2^{O_k(n log log n / √log n)}` still needs the full Lemma D.2 branch/array
  composition and its application to parity queries. The incidence entry-resource link below
  now instantiates native truncated contraction on the constructed networks; #1538 remains open.
- **Exact optimization and large weights:** `MaxSAT.exists_histogram_algorithm` and
  `MaxSAT.exists_optimum_algorithm` compute the complete score distribution and optimum value in
  contraction time measured by literal occurrences plus clauses. Their sparse fixed-width
  specializations give `2^{O_{k,c}(n / √log n)}` time and polynomial space.
  `BinaryWeights.certificate` contracts natural tensor tables exactly when their bit lengths are
  polynomial in the structural size; `BinaryWeightedCounting.exists_partitionFunctionCounter`
  supplies the native weighted-CSP application. Remaining extensions are native optimizing
  assignment extraction and signed or rational weight interfaces. A variable-count rate for
  dense exact MAX-SAT is not established by these results or by ordinary SAT sparsification.

## Documentation and repository

- **The guide** ([#585]): a chapter per area, including Foundations (bit strings, Fourier
  analysis, PMF and `ProbComp`, codes), proof complexity, descriptive complexity, and Word RAM
  and algorithms, reusing checked examples.
- **Curated formal abstracts:** improve readability, and compare each changed abstract with its
  final source statements.
- **Archive `complexitylib-v1`** once its remaining work is dispositioned.

## Deferred scopes

These remain coverage targets but are deferred from the active queue; their issues were closed as
not planned, not as proved.

- The full VNP-completeness reduction for the permanent ([#321]). Arithmetic formulas now
  project to the permanent with dimension `Formula.size + 1` over every commutative semiring;
  a selector occurring in one permanent entry can be eliminated with one extra dimension when
  `2` is invertible. The conversion from VP witnesses to formulas, the two-entry gadget and
  general Boolean-sum elimination needed for VNP-hardness remain open.
- General auxiliary-input zero knowledge ([#324]); see the GMW theorem above.
- Williams's square-root-space simulation ([#361]) and implicit Tree Evaluation ([#367]), now the
  frontier track [#888].
- Vollmer's generalized-quantifier survey ([#399]): ordered leaf words, explicit uniformity and
  input-access models, finite-monoid classification and generalized logical quantifiers.

[archive]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md
[archive-fhe]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities
[#321]: https://github.com/cslib-community/complexitylib/issues/321
[#324]: https://github.com/cslib-community/complexitylib/issues/324
[#361]: https://github.com/cslib-community/complexitylib/issues/361
[#367]: https://github.com/cslib-community/complexitylib/issues/367
[#399]: https://github.com/cslib-community/complexitylib/issues/399
[#456]: https://github.com/cslib-community/complexitylib/issues/456
[#459]: https://github.com/cslib-community/complexitylib/issues/459
[#474]: https://github.com/cslib-community/complexitylib/issues/474
[#486]: https://github.com/cslib-community/complexitylib/issues/486
[#581]: https://github.com/cslib-community/complexitylib/issues/581
[#585]: https://github.com/cslib-community/complexitylib/issues/585
[#608]: https://github.com/cslib-community/complexitylib/issues/608
[#640]: https://github.com/cslib-community/complexitylib/issues/640
[#643]: https://github.com/cslib-community/complexitylib/issues/643
[#798]: https://github.com/cslib-community/complexitylib/issues/798
[#800]: https://github.com/cslib-community/complexitylib/issues/800
[#862]: https://github.com/cslib-community/complexitylib/issues/862
[#884]: https://github.com/cslib-community/complexitylib/issues/884
[#886]: https://github.com/cslib-community/complexitylib/issues/886
[#888]: https://github.com/cslib-community/complexitylib/issues/888
[#889]: https://github.com/cslib-community/complexitylib/issues/889
[#890]: https://github.com/cslib-community/complexitylib/issues/890
[#891]: https://github.com/cslib-community/complexitylib/issues/891
[#892]: https://github.com/cslib-community/complexitylib/issues/892
[#894]: https://github.com/cslib-community/complexitylib/issues/894
[#895]: https://github.com/cslib-community/complexitylib/issues/895
[#896]: https://github.com/cslib-community/complexitylib/issues/896
[#897]: https://github.com/cslib-community/complexitylib/issues/897
[#939]: https://github.com/cslib-community/complexitylib/issues/939
[#949]: https://github.com/cslib-community/complexitylib/issues/949
[#999]: https://github.com/cslib-community/complexitylib/issues/999
[#1002]: https://github.com/cslib-community/complexitylib/issues/1002
[#1104]: https://github.com/cslib-community/complexitylib/issues/1104
[#1124]: https://github.com/cslib-community/complexitylib/issues/1124
[#1155]: https://github.com/cslib-community/complexitylib/issues/1155
[#1351]: https://github.com/cslib-community/complexitylib/issues/1351
[#1539]: https://github.com/cslib-community/complexitylib/issues/1539
[#1572]: https://github.com/cslib-community/complexitylib/issues/1572
[#2468]: https://github.com/cslib-community/complexitylib/issues/2468
[#1817]: https://github.com/cslib-community/complexitylib/issues/1817
[#1885]: https://github.com/cslib-community/complexitylib/pull/1885
[#2019]: https://github.com/cslib-community/complexitylib/issues/2019
[#2062]: https://github.com/cslib-community/complexitylib/issues/2062
[#2063]: https://github.com/cslib-community/complexitylib/issues/2063
[#2205]: https://github.com/cslib-community/complexitylib/issues/2205
[#2213]: https://github.com/cslib-community/complexitylib/issues/2213
[#2289]: https://github.com/cslib-community/complexitylib/issues/2289
[#2145]: https://github.com/cslib-community/complexitylib/issues/2145
[#2084]: https://github.com/cslib-community/complexitylib/issues/2084
[#2290]: https://github.com/cslib-community/complexitylib/issues/2290
[#2423]: https://github.com/cslib-community/complexitylib/issues/2423

The STOC1575 weighted-row module now proves Theorem 7.1 equations (24)–(25)
assignment semantics for positive capped signed rows, per-row binomial counts,
and an existing-TwoBoundary count/width wrapper. Nontrivial weighted clients cover
both polarities, zero demand and unattainable demand. This does not complete the
bounded-demand endpoint: replacing the mathematical all-cases plan with a fully
encoded executable pipeline and proving composed runtime/space remain open, as do
graph endpoints. The separate executable row/query writer is described below.

Global weighted upper clauses now deduplicate across all retained rows as finite
sets of signed literals. Exact evaluation/count preservation, query width and an
explicit degree-d+1 base bound are proved; the attainment term alone carries the
row factor. This does not complete Theorem 7.1: the mathematical assembler still
uses this noncomputable listing, and composed runtime/space remain open.


The capped weighted-row affine bridge now materializes signed integer coefficients
and shifted right hand sides, preserving every Boolean assignment and keeping
rejection separate from deleted true rows. Computed original-row selection is
connected back to actual capped rows under the computed consistency test.
The all-cases mathematical assembler now normalizes the original occurrence input,
dispatches direct branches using computed tests, and composes selected actual capped
rows with global queries in positive deficient rank. Exact full-input count recovery,
the 2r-2 variable cap, width d+2 and a global polynomial clause budget are certified.
The binary construction continuation below supplies composed encoded construction
resources; counting-time and graph endpoints remain open. Theorem 7.1 and
ALL-main are not completed by this mathematical plan.

The bounded-list weighted query writer now executes equations (24)–(25) using
only bounded-length sublists of canonical finite supports. Exact binomial
candidate counts, fixed-bound polynomial domination, literal widths, global
list deduplication, pointwise correspondence to `globalQuery` and exact counting
are proved. The executable all-cases and complete binary construction
continuations are described below; counting-time
and graph endpoints remain open.
This continuation does not complete Theorem 7.1 or ALL-main.


The original-input bounded-demand dispatcher now executes normalization/capping,
computed Gram rank/consistency/candidate tests and every direct/query branch.
It reuses `CountingPlan` with exact full-variable count recovery, at most `2n-2`
query variables, width `d+2` and the sharp fixed-demand polynomial clause budget.
Canonical signed-list key injectivity supplies that budget for actual global
deduplication. Concrete clients inspect computed constructors and counts.
The binary construction continuation below resolves complete plan serialization
and construction resources. Advertised counting runtime, full table frontend
and graph endpoints remain open. No ALL-main completion or issue closure follows.


The binary original-occurrence normalizer/backend stage now has composed plain
multitape polynomial-time/space certificates on framed unary-index/width and
binary integer-weight/target inputs. Actual aggregation, interval rejection,
complementation, capping, affine matrix/RHS writing, computed Gram selection,
consistency and full-rank candidate testing are certified. The serialized stage
is proved equal to the actual original-input normalized/capped tables and
dispatcher diagnostics. Uncapped aggregation-prefix bit widths and post-cap
Gram/Bird/Cramer widths are derived; output storage follows the runtime proof.
The separate selected-query continuation below resolves its query branch.
The complete tagged construction continuation below composes small-variable
counting and direct/query output resources. The counting continuation below resolves whole-algorithm space;
sharper counting runtime, full table frontend and graph endpoints remain open; no
Theorem 7.1 or ALL-main completion is claimed.


The actual selected-query branch now has fixed-demand polynomial binary
time/space certificates, composed from original-occurrence normalization and
computed Gram selection through bounded sublists, signed weight filtering,
global encoded-clause deduplication and ordinary boundary CNF writing. Suffix
scan machines are proved to compute the exact existing enumeration/dedup lists;
combinatorial output bounds are not used as a substitute for runtime. The
selected-row and query outputs are connected to the reviewed executable
queries, including sharp width/clause budgets and declared-index bounds.
Candidate-prefix integer widths and machine-derived output storage are covered.
One composed stage machine returns backend diagnostics and both queries with
polynomial time and simultaneous stage workspace.
The complete tagged construction now composes this stage with small-dimension
scans, computed direct branches, binary `2^n` writing and declared query output.
`BinaryPlan.compile_polytime` certifies one actual output-producing machine,
with fixed-demand polynomial binary time and independent polynomial space.
`compile_original`, `compile_count` and `compile_withinBudget` connect its tagged
output to the reviewed original-input all-cases plan, exact count and sharp
query budget. Direct answers use at most `n+1` bits. No rank/basis/output advice
or exponential assignment enumeration is used. Construction output storage
follows the machine proof, rather than supplying its runtime bound.

Remaining: compose external CNF counting with this tagged construction at the
source's advertised sharper counting rate, and complete the table frontend
and graph endpoints. The continuation below resolves counting-algorithm space.
Raw malformed-list parser correctness is not proved. This construction milestone does not complete
Theorem 7.1 or ALL-main; #1575 and the broader objective remain open.


The actual tagged plan now composes with the proved native declared CNF counter
and binary answer reconstruction in polynomial space. `counterInput_polytime`
charges reading the tag/declaration and converting emitted unary indices to the
native counter's binary CNF encoding. `execute_polySpace` charges both sequential
calls, retained queries and answers, binary subtraction and output. The final
`exists_count_polySpace` derives the counter and its workspace from the proved
library machine theorem, with no supplied oracle or resource contract, and
recovers the original positive-occurrence equation count on all declared bits.
The direct branches avoid counter calls entirely. Tiny reconstruction clients
and a nonzero instance of the existential native machine are checked.

The source's sharper time is still missing: 1575 Lemma 3.2 (PDF p. 11),
Proposition 4.2 (p. 14) and Theorem 7.1 (pp. 23–24) use
`eta(N) = N log log N / sqrt(log N)`. The proved native endpoint instead uses
`interpolationScale(N) = N (log log (N+16))^2 / sqrt(log (N+16))`.
Its Proposition 6.4 interpolation route does not establish the sharper
Theorem 1.1/Appendix D rate. Removing the extra log-log factor requires a core
counter refinement, followed by time composition and variable rescaling; it is
not a consequence of polynomial-space closure or output-size bounds. No weaker
exponent is substituted for the source claim. Full malformed-input parsing,
table frontend, graph endpoints, Theorem 7.1 and ALL-main remain open.


A concrete core-counter resource link now supplies
`IncidenceNetwork.exists_entry_admissible` and `exists_contraction_bound` for the
actual incidence networks of OpenAI2026ETH Lemma D.2 (PDF pp. 54–56), at size
`s = n * ceil(log₂ ceil(log₂ n))` and precision/truncation order `n+1`.
The existing native row-entry machine has time polynomial in its encoded input
times `2^descInc`; the new bound derives `descInc ≤ ceil(s^(9/10))` from actual
test-group incidences and proves polynomial workspace against the actual network
encoding. The proved truncated contraction machine therefore has time
`poly(L) * 2^O(s/sqrt(log s))` and polynomial space on these networks, without a
supplied contraction/entry resource contract. The sparse-branch corollary
computes the source degree cap `k*(sys.length+2*n)` from the input.

Remaining core work: compose streaming degree-array summation and high-incidence
branching, prove their exact sparse-system reconstruction, and apply this solver
to every greedy parity query under the sharper sparsification schedule. Then
compose the resulting general-density counter and rescale its actual time through
the two weighted queries. The old interpolation counter's extra log-log factor
has not been removed from that end-to-end algorithm. The weighted original-input
correctness/space endpoints currently cover only serialized positive occurrence
rows with a common occurrence count `m`; arbitrary variable-length raw rows are
a material frontend gap, alongside table and graph endpoints. No Theorem 7.1 or
ALL-main completion is claimed.


The next entry-extraction correctness link is now proved.
`IncidenceNetwork.val_factorCoeffs` connects actual binary modular
lists to the source integer parity factors. `val_rowTerm` and `val_rowSum`
connect the existing modular multiplication and signed Boolean-word stream to
the subset Möbius coefficient of the test-group product (OpenAI2026ETH,
Lemma D.2, PDF p. 56). `IncidenceSelections` proves actual block selections are
sublists and constructed row blocks contain no duplicate incidence, even with
repeated raw variables/tests or invalid indices. Thus `val_rowVertex` has no
supplied distinctness or entry-correctness premise; `val_colEntry` gives the
unselected-bit weight. A checked constructed row has coefficient -6V modulo 16.
The native entry program and its already proved resource bounds are unchanged.

The old extra factor is algorithmic: `ReplacementParams.numGroups` uses
`floor(sqrt(lambda)/nu^2)`, so its division/interpolation charges retain `nu^2`.
The sharper route replaces that evaluator by truncated incidence networks at
size `n*nu`. The actual degree-array traversal and network writer are now certified below.
The next semantic stage is exact decomposition of the incidence sum into
the streamed contractions. Then assemble high-incidence branching, every greedy
parity query, sharper sparsification and final weighted time composition.
No single-log-log bound for the complete counting algorithm is claimed. Weighted
correctness/space still assumes positive serialized rows with a common occurrence
count `m`; arbitrary variable-length raw rows, table/graph endpoints, full
Theorem 7.1 and ALL-main remain open.


The computed degree-array traversal is now native-certified. `IncidenceArrays`
decodes one radix array from a binary index with unique bounded-array coverage,
including empty arrays/radix one, and proves the actual quarter-root traversal
bound `2^(4*sqrt(n)*(clog₂(k(c+2)+1)+clog₂(n)))`. `IncidenceNetworkPolyTime`
charges actual incidence discovery, binomial widths, port/descriptor writing and
padding. `IncidenceArraySum.buildArray_polytime` computes all parameters from the
original sparse system and index, including the source cap `k*(a+2*n)` and
quarter-root groups. `exists_sumArrays_certificate` composes this writer with the
proved native truncated contraction and modular accumulator, one network at a
time: actual array count times `poly(L)*2^O(s/sqrt(log₂ s))` time and polynomial
original-input peak workspace, where `s=n*clog₂(clog₂ n)`. Entry admissibility is
derived from `IsSparseBranch`, not supplied as an oracle or runtime budget.

This is a concrete algorithm/resource milestone, not the full sharper counter:
`sumArrays_eq` proves exactly the modular sum of constructed contractions, but
its equality with the sparse-system count remains unproved. Extra arrays now have zero-contribution proofs, and valid local ranks have unique
coverage as recorded below; the shared-wire/global-product correspondence remains. High-incidence branches, parity
queries, sharper sparsification and weighted time rescaling remain to compose.
No new eta-time bound is claimed for the old end-to-end interpolation program;
its extra log-log factor has not been removed. Common-occurrence positive
serialized rows, arbitrary variable-length raw rows, tables and graphs retain
the limitations above. Full Theorem 7.1 and ALL-main remain open.


The next reconstruction stages are now proved in `IncidenceBlockCoverage`,
`IncidenceArraySupport` and `IncidenceCountReconstruction`. The actual combination
unranker covers fixed-weight words and incidence sublists uniquely. A selected
incidence monomial of bounded total degree determines one actual decoded array
and one valid local rank per computed group pair, without supplied ranks or
incidence distinctness. Impossible local capacities are rejected even at width
zero. Both global-cap overflow and local-capacity overflow annihilate actual
padded network contractions before modular reduction. Thus the existing native
`sumArrays` output is exactly its sum over source-feasible arrays, with its
approved actual binary time and polynomial original-input space unchanged.

The exact count target is also derived from actual canonical sparse input:
`rootCount_eq_incidenceResidue` instantiates the incidence polynomial with the
computed cap `k*(a+2*n)`, derives finite degrees from listed monomial lengths,
and proves that its coefficient sum below `n+1`, modulo `2^(n+1)`, recovers the
declared-variable count. No supplied coefficient or answer congruence is assumed.
This is a mathematical reconstruction specification, not an exponential
monomial-enumeration implementation.

Still missing is the global equality between that polynomial and the supported
native contraction sum. Common-wire decoding, complete main-wire assignment
coverage, padding contribution one and actual group coefficient/weight
factorization are now proved below. Global reindexing into the original finite
per-test incidence families, invalid-rank removal and listed/finite coefficient
identification remain. High-incidence branches, parity queries, sharper
sparsification, actual eta-time absorption and weighted rescaling then remain.
These are stage-local limits; the later native general counter and parsed ragged weighted
continuation below resolve the counting-resource/frontend gaps. The old interpolation counter
retains its extra log-log factor, while table/graph and ALL-main endpoints remain open.


The physical-wire/global-product components are now proved. `IncidenceWireDecoding`
characterizes the actual sequential port reader at both endpoints, including
zero widths. `IncidenceWireRanks` uses prefix-sum coordinates to give a bijection
between all actual main-wire assignments and tuples of full-width binary ranks;
valid local ranks have one assignment and the full assignment sum reindexes
without multiplicity. `IncidencePadding` proves exact natural polynomial
contraction preservation for the actual forced-false padding, including dead
arrays, and transports it to the actual `sumArrays` output.

`IncidenceGroupCoefficients.val_rowVertex_prod` factors the actual whole-group
stream into individual test coefficients in the truncated ring, deriving its
scope conditions from the blocks. `IncidenceColumnWeights` proves common-wire
selection membership agrees at both endpoints and the actual column entries
multiply to two per declared variable unselected by all rows. Free variables
outside every scope are retained. These are semantic identities of the existing
certified machine; its actual binary resource bounds are unchanged and no
exhaustive-rank replacement algorithm is introduced.

The native fitting-rank finite-sum identity is now assembled below, including
unused binary-rank removal. The identification with the original equation/subset
families still needs the listed-test integer lifts and group-local coordinates
connected to the finite normalized equations. Then compose
high-incidence branches, every parity query, sharper sparsification, explicit
exponent absorption and weighted eta-time rescaling, as completed by the later continuation
below. The old interpolation counter is unchanged. The final status below records the parsed
ragged weighted frontend; table/graph and ALL-main endpoints remain open.


`IncidenceRankSum` now proves the actual finite-sum support/reconstruction
endpoint.
`polyContraction_eq_rankPolynomial` identifies every actual padded contraction
with its sum over fitting combination-rank tuples: unused binary ranks force an
actual zero row and are removed, and the physical-wire equivalence reindexes the
surviving assignments without multiplicity. Dead arrays, impossible capacities,
zero widths and the empty assignment are covered. The actual row coefficient
products and declared-variable weight then yield
`truncNatHom_polyContraction_eq_rankIncidencePolynomial` in the truncated ring.
`sumArrays_eq_rankIncidenceResidue` proves exact scalar native readback from the
global grouped incidence sum for n≥1. No desired output/coefficient congruence is
assumed, and no exhaustive evaluator replaces the certified native machine.
Its actual binary time and polynomial original-input peak space are unchanged.

`IncidenceSelectionSum` now removes all array and rank indices from that global
sum. `sum_rankIncidencePolynomial_eq_selectionPolynomial` is an exact integer
polynomial identity: actual fitting ranks select sublists, their lengths recover
the unique computed array, and unique sublist coverage proves a bijection onto
all block families of total size at most the cap. Dead arrays vanish before
reindexing. `sumArrays_eq_selectionResidue` connects this capped family sum to
the actual native scalar output, preserving its binary time and peak-space
certificate without executing the mathematical family enumeration.

`IncidenceOriginalCount` now proves that remaining original-coordinate bridge.
`selectionPolynomial_eq_incidenceSum` is an exact integer-polynomial identity,
transporting residue-class/local-test positions to original row indices,
canonical listed integer monomial counts to finite equation lifts, and the
incidence degree/coefficient products/declared-variable weights. It does not
assume the desired equality; the reviewed array/rank reindexing is reused.
`trunc_selectionPolynomial_eq_systemIncidencePolynomial` is the precise computed
truncated-ring equality, and `sumArrays_eq_rootCount` composes it with actual
native readback and source residue recovery for n≥1 under canonical equations,
declared variables and listed degree ≤k. Repeated equations retain their identity.

`IncidenceOriginalCounter.countOriginal` dispatches n=0 to the actual polynomial
binary evaluation of the unique empty assignment. It equals the original count
for every n under those semantic hypotheses; the bare zero-group contraction is
not used to decide zero-variable contradictions. `exists_countOriginal_certificate`
composes the actual branch test/direct output/native stream and bounds its binary
time by a fixed polynomial overhead plus the existing degree-count multiplier
and contraction bound, and its peak space by a polynomial, on all sufficiently
large admissible sparse branches and on the direct zero-variable branch.
The checked client now derives numeric original counts, including interleaved
and repeated rows, nonlinear/constant equations and declared free variables.

`IncidenceSharpResources` now absorbs the actual degree-array multiplier and
native padded-size exponent into the single-loglog scale, with explicit rounding
comparison to the unshifted real base-two `n loglog n / sqrt(log n)`.
`IncidenceSparseCounter.countSparse` composes the actual native solver with computed
high-incidence branching. A polynomial semantic guard derives its global output
bound from proved count correctness; no counter oracle or runtime premise is
supplied. `countSparse_eq_rootCount` is exact for every size on canonical,
declared, degree-bounded input. `exists_countSparse_real_sharp_certificate` proves
actual polynomial original-input space and `poly(L)*2^O_{k,c}(eta(n))` time for all
sufficiently large normalized sparse systems with at most c*n equations and
clog₂(n)^c monomials per equation, without an input occurrence bound. Branch
length/encoding transfer, all reduced solver costs and binary accumulation are
charged. General natural/real estimates also prove fixed linear query-variable
rescaling without adding an iterated-log factor.

The arbitrary explicit ragged weighted-row frontend is now implemented in
`WeightedRagged`/`WeightedRaggedResources`: canonical binary parsing, positive-weight/index and
computed-demand admission, safe binary-to-unary index conversion, exact dependent-family
refinement, and composed original-count correctness/sharp time/polynomial space. Empty rows,
repeated opposite literals, signed targets and unused declared variables are preserved. The
explicit encoding has a unary declaration, binary indices/weights/targets and framed variable-length
lists; no succinct binary declaration resource claim is made. Native word certificates charge
all parsing/construction/counting/output operations, with single-loglog eta and no counter advice.
`ComplexityTests.WeightedRagged` supplies mixed-length/empty/contradictory/large-weight clients.

The concrete table endpoint is now composed in `ExactOnePlan`/`ExactOnePathPlan`,
`VCOneDispatch`, `ExactOneCountingResources` and `VCOneCountingResources`, reusing the approved
`VCOneClosure`/`VCOneSeparator`/`VCOneFrontend` constructors. Actual side-CNF/direct/rank/candidate
branches, selected-row query writing and original assignment counts are proved, including empty
and overlapping tables and unused declared bits. The actual general-density native counter and
binary reconstruction give single-loglog sharp time and global polynomial peak space. Query
declarations are at most `2r-2`, widths at most three, and actual clause budgets are quadratic,
independent of input table count. This is the Theorem 6.3 table endpoint on the existing canonical
explicit relation-row encoding: unary declarations/local widths, literal bit rows and binary scope
columns, with individually injective scopes and local VC dimension at most one. Full binary
construction has polynomial resources for every raw input; correctness/sharp counting time use
the promise. Other table formats and parser/admission transfers remain separate. Certificates use
the existing native word/resource calculus, rather than a fresh bit-transition machine simulation.

The generic Theorem 1.1 frontend is now executable and composed in `TwoBoundaryFrontend`
(computability, correctness and fine-grained resource modules). Actual original term lists need
no VC-one assumption/conversion: a tautological DNF can realize the full cube. The one-query
empty-condition branch and two boundary writers preserve all declared counts and exact source
variable/width/clause budgets. Polynomial binary construction and native single-loglog sharp
counting/global polynomial space are proved with exponent parameter `n + number of conditions`,
without assuming a linear condition count. The explicit encoding has unary declarations, binary
literal indices and framed term lists; arbitrary untrusted-byte admission is separate.

`IndependentDomination` now supplies an actual explicit adjacency-matrix graph frontend and
complete original-selection counting/sharp-time/global-space composition. Edge exclusions and
closed-neighborhood coverage give width three, `2v-1` variables and at most `3v²` clauses; the
empty graph is retained. The continuation `IndependentDominationInterval` adds arbitrary signed
binary lower/upper/exact input cardinality tests, covering this fixed-rule specialization of
Corollary 7.2 and Proposition D.3's input upper-bound predicate/count. Actual capped threshold
circuit generation and full functional CNF writing introduce at most `952(v+1)` gate variables;
each accepted original selection has exactly one trace. Actual nonempty queries have width three,
`2v+a-1` variables and at most `3v²+2+2856(v+1)` clauses; empty signed inputs dispatch directly.
One complete native certificate composes signed normalization, construction, counting and
reconstruction with global polynomial workspace and original-vertex single-loglog sharp time.
Binary bounds vary with the input, and all their bits/writes are charged. This is not the general
fixed-rule corollary, a full size-distribution iterator, a witness/optimization algorithm or a fresh
bit-transition machine simulation. No marking multiplicity or assumed constructor/runtime is used.

Remaining STOC1575 objectives, keeping the original inventory open:

- Theorems 1.1–1.2: actual generic bounded-term DNF constructor/count/resource transfer and the
  signed-equation/side-2-CNF route are covered for the explicit encodings above. Alternative byte
  formats/admission and succinct declarations are separate, not implicit source promises.
- Theorem 1.3 / 6.3 tables: actual representation and complete original-count/sharp-time/global
  polynomial-space composition are covered under the explicit canonical promise/encoding above.
  Alternative raw table formats/parser/admission transfers remain separate.
- Theorem 7.1: the parsed ragged weighted-row counting/reduction is covered for the explicit
  nonsuccinct unary-declaration input encoding, with actual sharp time/polynomial space.
- Corollary 7.2 / Theorem 7.3: fixed finite/cofinite degree rules and fixed labeled partition
  matrices still need their actual local degree-rule/partition construction and complete resource/
  count transfer; q and cutoff D must remain fixed independently of the input. Functional linear
  input cardinality tests and complete signed size-constrained independent-domination counting
  are now implemented. General degree-rule/matrix construction remains open.
- Corollaries 7.4–7.5 / Proposition 7.6: graph decision/witness/optimum and induced-matching
  distribution endpoints remain open. Upper-domination width-3 differences count set–marking
  pairs, not original sets. Query budgets, directed/undirected promises, empty graphs and
  polynomially many distribution/threshold queries must be retained.

Remaining graph/general-rule and other-paper/ALL-main endpoints remain open; the generic DNF
and independent-domination milestones do not complete the original ALL-main objective.

The older interpolation counter is unchanged; its extra loglog and nu²-denominator schedule are
not relabeled. Graph endpoints and other-paper objectives remain open.
