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
| Crypto frontier tracks: Kilian's succinct arguments, chosen-ciphertext security, signatures from one-way functions | [#999], [#1000], [#1001] |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002] |
| A Verso guide with a chapter per area | [#585] |
| Planar SAT and geometric hardness: orthogonal planar 3SAT-3 with explicit grid bounds, parsimonious compilers | [#1079] |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124] |
| Proof automation: predictable polynomial-time certificate search | [#1155] |

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897].

1. [Goldreich–Micali–Wigderson zero knowledge in full](#cryptographic-landmarks)
2. [Rompel's signature theorem](#cryptographic-landmarks) ([#1001])
3. [Completeness of oblivious transfer](#cryptographic-landmarks)
4. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886])
5. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889])
6. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity)
7. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891])
8. [MIP = NEXP](#interactive-proofs) ([#892])
9. [Regev's worst-case to average-case reduction](#cryptographic-landmarks)
10. [The Immerman–Vardi theorem](#descriptive-complexity-and-first-order-reductions)

## Cryptography

### Cryptographic landmarks

- **Goldreich–Micali–Wigderson zero knowledge in full.** If one-way functions exist, every
  language in NP has a computational zero-knowledge proof in Goldreich's sense (Def. 4.3.10):
  for every `x ∈ L` and arbitrary auxiliary input `z`, against probabilistic polynomial-time
  verifiers. This needs a bridge between the security premise and a clock independent of an
  unbounded auxiliary word, witness-level Levin reductions, and sequential soundness
  amplification to negligible error. State it under nonuniformly one-way functions, as
  Goldreich does (*Foundations of Cryptography*, Vol. 1, Section 4.4), and derive the
  nonuniform (advice-secure) PRG premise of the auxiliary-input theorem from that; uniform
  one-wayness is not known to give such a generator.
- **Rompel's signature theorem** ([#1001]). One-way functions imply digital signatures that are
  existentially unforgeable under adaptive chosen-message attacks, for arbitrary
  polynomial-length messages. Authentication trees from one-time signatures and
  collision-resistant hashing are an intermediate development step; for the theorem itself,
  universal one-way hash functions replace the collision-resistance assumption.
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
- **Diffie–Hellman and ElGamal:** arbitrary-key-length standalone symmetric-cipher bridge for
  general-cipher Hashed ElGamal (Boneh–Shoup Theorem 11.5; the general-cipher construction,
  Game 0/1/2 hybrids, Equation `(11.14)` reductions, and normalized `n`-bit-key `DEMOneTimeINDCPAOn`
  / `linearHashKDF` endpoints have landed) ([#1047]).
- **Chosen-ciphertext security** ([#1000]): authenticated encryption by encrypt-then-MAC and
  Cramer–Shoup from DDH, with KEM–DEM hybrid encryption ([#881]) as the chosen-plaintext
  starting point (Boneh–Shoup Exercise 11.9).
- **Lattices** ([#645]): Fiat–Shamir with aborts and signatures from SIS (Lyubashevsky 2009,
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

- **PRIMES ∈ P** ([#893]): the polynomial-time AKS algorithm on binary inputs, on top of the
  proved criterion and small-`r` bound.
- Time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes;
  completeness, padding, self-reducibility, relativization and oracle separations, preserving
  each reduction's resource bound.
- **Time hierarchies** ([#1572]): native polynomial padding separates every pair of integer
  degrees `1 ≤ a < b`. Remaining targets include the general deterministic `f log f` hierarchy
  with its simulation bound ([#800]), noninteger polynomial degrees and finer logarithmic
  gaps, and sharp nondeterministic and alternating time hierarchies with certified simulators.
- The space hierarchy for `log n ≤ g n`, which needs a universal simulation that does not hold
  its input.
- **Space:** Savitch bounds for general space-constructible functions.
- **Randomized logspace** ([#459], [#474]): RL and BPL, `USTCON ∈ RL`, Nisan's generator,
  `BPL ⊆ L²` and Saks–Zhou.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a
  logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888]): implicit Tree Evaluation with the
  fan-in-`d` space bound, subroutine calls for implicit gates and leaves, and padding of
  non-perfect trees. For Cook–Mertz itself: malformed-input handling and the refined
  `O(ℓ + H log(ℓ + 2))` parameter bound.
- Alternating time and space classes and bounded-alternation characterizations of PH; sharp
  bounds for sublinear space, distinct from polynomial-space simulation.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351]): logspace Turing reductions, in an oracle model whose query tape is
  not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of
  Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets:** SPARSE and TALLY; `P/poly = P^SPARSE` (Meyer), extending
  `PPoly.of_sparse` in `Circuit/Boolean/Sparse.lean`; a sparse set that is NP-hard under many-one
  reductions gives `P = NP` (Mahaney), as does a sparse coNP-hard set (Fortune) and a sparse NP-hard
  set under bounded truth-table reductions (Ogihara and Watanabe).
- **Berman–Hartmanis:** p-isomorphism and paddability; paddable NP-complete sets are p-isomorphic,
  so the standard NP-complete problems are all p-isomorphic to SAT; the isomorphism conjecture as a
  hypothesis; every many-one complete set for EXP is complete under one-one, length-increasing
  reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal,
  Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so
  every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang);
  separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and
  Torenvliet).
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
- **The Immerman–Vardi theorem:** on ordered finite structures, first-order logic with least
  fixed points defines exactly the polynomial-time properties, with the machine side proved for
  actual native algorithms in both directions.
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
- **Exponential-time SAT** ([#894]): amplify Schöning's random walk, with a time bound, then
  PPSZ. Further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886]): for `0 < ε < 1/8`, NP-hardness of
  distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most
  `7/8 + ε` of the clauses. This needs the reduction to MAX-E3LIN and, through the 4-clause XOR
  gadget, to MAX-E3SAT; Raz–Holenstein parallel repetition for small-soundness Label Cover; and
  the perfect-completeness reduction.
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
- **Feasible interpolation:** from a Resolution refutation of `A(x,y) ∧ B(x,z)`, construct a
  circuit separating the `x` assignments extendible to `A` from those extendible to `B`, with
  proof-size and extraction-time bounds. Prove the monotone variant under its polarity
  hypotheses and transfer circuit and communication lower bounds to proof-size lower bounds.
- **Proof search:** automatizability and weak automatizability with explicit encodings and
  runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow
  and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.

## Circuits and algebraic complexity

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889]): no polynomial-size,
  constant-depth circuits over AND, OR, NOT and fixed-modulus counting gates for some language in
  NEXP.
- Uniform and nonuniform NC, AC and TC, circuit-to-machine bridges, algorithm-to-lower-bound
  arguments, and barriers such as natural proofs and algebrization. NC simulation of unrestricted
  `TCⁱ` needs Muroga's threshold weight-bounding theorem.
- Formula lower bounds beyond Andreev's, following Jukna; Raz–Wigderson's monotone depth bound for
  matching on general graphs.
- **An explicit frontier extractor:** port v1's sumset-extractor construction with an explicit
  family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses. It would
  exceed the library's unconditional `3.5 N - o(N)` bound in P, so it needs an independent
  correctness review of the frontier core.
- **Weighted threshold representations:** v1's explicit source-reduction family, universal scalar
  circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting.
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
  The first Count-Min milestone is scoped in [#1201](https://github.com/cslib-community/complexitylib/issues/1201).
- **Learning:** machine-certified running times for the LMN and Kushilevitz–Mansour learners;
  distributional problems and reductions, samplability, average-to-worst-case connections,
  PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Give the
  computational–statistical gap program concrete clients: an SQ oracle with tolerance and query
  costs, statistical-dimension lower bounds for a specified planted problem, and corresponding
  sample and runtime upper bounds. Develop low-degree likelihood-ratio and sum-of-squares
  comparisons where justified, distinguishing restricted-model bounds from unrestricted
  computational hardness. Use the [distributional framework](#average-case-complexity).
- **Property and distribution testing:** access models, one/two-sided and tolerant testing,
  query and sample bounds, canonical testers and lower bounds.
- **Kolmogorov complexity and metacomplexity** ([#798], [#884]): the near-linear threshold regime
  of Liu–Pass Theorem 3.1 (c), hardness for every polynomial `t(n) ≥ (1 + ε)n` rather than above a
  polynomial threshold, which needs a rate-1 efficient conditional EP-PRG running in `n + O(n^c)`
  multi-tape steps for a constant `c < 1`; prefix-free complexity,
  resource-bounded MCSP variants and connections to learning, cryptography and lower bounds; the
  circuitized anti-checker with an efficient generator; the asymptotic parameter instantiation of
  Theorem 5 in `MCSP/FormulaMagnification.lean`; and hardness results for `MINKT` and `MINcKT` (whose
  definitions, conditional `K^t` measure, and `NP` memberships are in `Kolmogorov/MINKT.lean`,
  `Kolmogorov/Conditional.lean`, and `Kolmogorov/MINcKT.lean`), as independently scoped
  developments; the reverse
  multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding.
- **Quantum computation** ([#896]): BQP ⊆ PP; reusable
  circuit, channel and measurement semantics with uniformity and approximation costs, reusing
  suitable quantum foundations rather than incompatible models; BQP, QMA and related query,
  communication and interactive classes, with amplification, containments and complete
  problems. Supply the [quantum adversary models](#concurrent-and-quantum-security) needed by
  cryptographic reductions.

### Differential privacy and adaptive data analysis

- Dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with
  postprocessing and adaptive composition. Start with a finite or discrete mechanism proving
  both privacy and utility, including sampling cost and finite-precision error.
- The exponential mechanism, private query answering and private learning; privacy–accuracy
  and sample-complexity lower bounds; then adaptive data-analysis and generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources
  explicit, reusing the probability, oracle-computation and learning APIs.

[#1459]: https://github.com/cslib-community/complexitylib/issues/1459
[#1463]: https://github.com/cslib-community/complexitylib/issues/1463
[#1481]: https://github.com/cslib-community/complexitylib/issues/1481
[#1482]: https://github.com/cslib-community/complexitylib/issues/1482

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
- **Spanning trees and matroids:** minimum spanning trees with sorting and disjoint-set costs;
  weighted matroid greedy optimality with an independence-oracle interface; then matroid
  intersection with explicit oracle and implementation costs.
- **Submodular optimization:** the `1 - 1/e` approximation for nonnegative monotone submodular
  maximization under a cardinality constraint, charging value-oracle calls separately from their
  concrete realizations; then further constraints and approximation bounds.

### Online algorithms and competitive analysis

- Request sequences, online strategies, offline optima and competitive ratios with additive
  constants; distinguish deterministic and randomized strategies and oblivious and adaptive
  adversaries. Compare algorithms in the same action and cost model, including initialization.
- **Paging:** an LRU competitive bound and a matching deterministic lower bound as the first
  clients. Reuse native amortized certificates and make adversarial request generation explicit.
- **Adaptive search trees:** a BST access-and-rotation model, the splay access lemma, static
  optimality, working-set and dynamic-finger bounds, and Wilber-style lower bounds. State dynamic
  optimality as a conjectural research target with explicit strategy and sequence quantifiers.

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

- **Native distinct-position frontend** ([#1482]): initialized signed input produces exact
  compact root descriptors, with derived logarithmic width and uniform
  `Oκ((n+1) log²(n+2))` charged cost. This frontend is composed into the complete native
  preprocessing and the conditional ordinary host described below.
- **Efficient universal simulation** ([#800]): realize the buffered Hennie–Stearns backend
  with time `O_M(t log(t + 2))`, together with a source-space-sensitive storage bound.
  The current interpreter has a stronger polynomial certificate and a streaming input lookup;
  the buffered representation, its native cleanup routines and their amortized bounds remain.
- **Plain computability** ([#862]): complete the plain calculus ([#608]), delete the tidy
  calculus, keeping only a machine-level kernel inside the Machines layer, and switch the
  abstract bridges to the shared predicate.
- **Logspace automation** ([#1449]): `fun_prop` rules for `ComputableInLogSpace` (composition,
  `ite`, word, arithmetic and list primitives), with the one-way transition from logspace to
  polynomial time.
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
- **Native cyclic coefficient kernel** ([#1701](https://github.com/cslib-community/complexitylib/issues/1701)):
  fixed standard native code computes signed cyclic convolution with explicit fits, frames and
  quadratic charged cost. This prerequisite does not complete the native Strassen modular
  counter, deterministic prime selection or the full [#1394] 1.9992 endpoint.
- **Native Chan–He components** ([#1446]): native parameter, collision-counting, prime-table,
  collision-tested minimum-search and complete two-prime modulus programs have explicit local
  fit/frame/cost contracts. The complete native distinct-position frontend ([#1482]) starts from
  initialized signed input and produces exact compact root descriptors with derived logarithmic
  width and uniform `Oκ((n+1) log²(n+2))` charged cost. The complete native one-node component
  ([#1481]) computes all residues/histograms, three compact heavy arrays and exact packed output
  in linear time. Native bounded recursive traversal ([#1512](https://github.com/cslib-community/complexitylib/issues/1512)) executes those components with an
  explicit stack, exact preorder output, polynomial local fit/frame contracts and charged
  ternary-tree bounds. Complete native preprocessing ([#1446]) composes every root from actual
  initialized input, returns the exact finite packed instances and derives positive logarithmic
  width, polynomial space/intermediates and an `Oκ(n^1.5 log¹³(n+2))` charged bound.
- **Conditional native ordinary host** ([#1559](https://github.com/cslib-community/complexitylib/issues/1559)):
  connects actual preprocessing output to caller-safe Convolution calls, proves the existing
  distinct-position verdict from `State.init`, derives logarithmic width and every-prefix
  polynomial words/space, and charges concrete callee work at the actual packed size. Its finite
  callee contract has a proved slow exhaustive native instance; no fast backend or final
  subquadratic bound is supplied. The native fast backend, Exact Triangle solver and final
  input/time/width/asymptotic composition, including exponent 1.9992, remain under #1394.
- **Mathlib TM2:** sublinear work-space comparisons and a linear-space forward simulation.
- **Generic RAM:** uniform arbitrary-program dispatch and general width-selection and input-fit
  theorems; simulating operations by programs over smaller bases; structured programs and time
  classes over arbitrary value domains with weighted or bit costs; simulations between instances;
  the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Native pruned-query evaluator** ([#1526](https://github.com/cslib-community/complexitylib/issues/1526)):
  fixed 96-register code computes distinct root/child queries, stack traversal and signed
  accumulators. Initialized flat runs preserve query order and duplicates, input and outside
  frame. Setup, sparse clearing, control/index work and halt fit
  `8192*(L+Q+1+(L+1)*|leaves(requested queries)|)` instructions, with widths derived from
  original magnitude/address bounds. A callable pointer/epoch kernel permits directory reuse.
  Query grouping, band/tile composition, sparse-product and Exact Triangle solving, and full
  input/time/width/asymptotic composition remain under #1394.

- **Shared native matrix encoders** ([#1493](https://github.com/cslib-community/complexitylib/issues/1493)): compute all `10^L` leaf values from `7^L`
  signed inputs within `240*(L+1)*10^L` standard WordRAM instructions, plus the final halt,
  with fixed code/registers and concrete initialized inputs, frames and explicit width bounds.
- **Native shared-band preparation** ([#1523](https://github.com/cslib-community/complexitylib/issues/1523)): computes deterministic subset tables and a valid
  layout, prepares padded signed matrix bands, invokes both shared encoders for every band, and
  restores the original initialized input. Fixed 96-register code has a charged bound, including
  halt, of `4096*(L+1)*(1+N*4^m+2^L+2*numBands*10^L)+1`; at `L=19m`, `N≥(4^m)^18`, it is at most
  `81920*(L+1)*N²/(4^m)^(1/18)`.
- **Native wanted-query routing**
  ([#1561](https://github.com/cslib-community/complexitylib/issues/1561)): computes the
  selected-subset table, tile keys, query codes, counts, prefix offsets and stable scatter from
  original raw coordinates. Its initialized run preserves every original occurrence and gives
  each tile exactly its finite `wantedStrings` code set, within
  `128*(L+1)*(Q+numBands²+2^L+1)` instructions including halt. It uses fixed 96-register code and
  an explicit positive sufficient-width threshold. Joining these groups to shared band encoders,
  invoking the pruned kernel and reconstructing queried products remain separate native work.
- **Native queried-product composition**
  ([#1581](https://github.com/cslib-community/complexitylib/issues/1581)): joins the actual router
  and band producers to the pointer/epoch kernel, restores the original input, and reconstructs
  every requested signed product in original order. It charges raw-entry conversion, all copies,
  dispatch, one shared directory initialization, epochs and reporting. At `L=19m`, `D=4^m`,
  `D^18≤N` and occurrence sparsity `Q*2^m≤N²`, its initialized fixed 160-register program uses at
  most `4325376*(19m+1)*N²/D^(1/18)` instructions including halt, with sufficient width
  `128*clog₂(N+Q+A+2)` for entry bound `A`. The distinct-set sparsity theorem instead retains an
  explicit additive charge for all `Q` occurrences. Native sparse-product and Exact Triangle
  solving, full input/time/width/asymptotic composition, and the improved Section 4 route to
  exponent 1.9992 remain under [#1394].
- **Word RAM:** an AC⁰ basis; wider-fragment and Turing-machine simulations;
  transfer of Anthropic's modular machine and 3SUM/APSP algorithms; direct 3SUM adaptation ([#1394])
  has the Convolution-3SUM/Exact Triangle correctness reduction, a charged native single-instance
  matrix builder and the complete finite mathematical Chan–He reduction ([#1435]), including
  ordinary distinct-position inputs and explicit size bounds. The finite lopsided matrix/counting
  interface ([#1438]) adds padding, detection and signed digit reconstruction. Modular counting
  and the selected-prime false-positive bound ([#1442]), finite residue/chunk/piece splitting and
  witness recovery ([#1447]) are proved mathematically. The tensor identity, full recursion,
  shared encodings and pruned-evaluation core ([#1459](https://github.com/cslib-community/complexitylib/issues/1459)) include exact visited-leaf and passed-set
  bounds, with the empty zero-depth root handled explicitly. The finite thin-product component
  ([#1463](https://github.com/cslib-community/complexitylib/issues/1463)) proves valid layouts, arbitrary-size padding/tiling, exact queried signed products and
  sparse encoding/leaf/passed-set totals. These counts are not native instruction costs. Complete
  native preprocessing and the conditional ordinary host with an exhaustive reference callee
  are available. Native pruned/sparse-query backend composition, a concrete fast Exact Triangle solver
  and the unconditional fast input/time/width/asymptotic bound remain, including the improved
  Section 4 route to exponent 1.9992;
  size-based width
  selection with an input-fit guarantee and explicit overhead; expected-time rules for unbounded
  almost-surely terminating structured loops; random-tape equivalence and BPP/RP/ZPP simulation
  bridges for the randomized word RAM ([#1124]); transfer of cell-probe lower bounds; and the
  Horn-SAT, 2SAT, matching and domino-tiling clients.
- **Caller-safe queried thin products** ([#1618](https://github.com/cslib-community/complexitylib/issues/1618)):
  actual memory operations are rebased above a runtime caller base, using a computed source
  modulus and charged load normalization. The initialized 163-register program restores local
  input, returns an absolute answer pointer and preserves the caller outside a polynomial window.
  Setup/return adds at most `2048*(N*D+Q+1)` to three times the original product charge. At
  `D=4^m`, `L=19m`, `D^18≤N` and `Q*2^m≤N²`, the full charge including halt is at most
  `17301504*(19m+1)*N²/D^(1/18)`. Distinct-set sparsity retains an additive occurrence charge.
  Every width at least `256*clog₂(base+N+Q+P+5)` suffices for initialized caller-word bound `P`.
  The reserved window is at most `(2*(N+Q+3))^128` and is not bulk-initialized.
- **Prepared ET-record product calls** ([#1626](https://github.com/cslib-community/complexitylib/issues/1626)):
  the native adapter reads the computed six-word record, recovers the depth with actual binary
  logarithm code, and copies raw matrices and query occurrences above the producer's heap.
  It invokes the complete callable product in a separate register bank and preserves the
  catalogue, sources and producer registers. The fixed 320-register initialized client runs
  the producer and consumes its first record; the caller interface supports every occupied
  ordinal. Original polynomial headers/weights give positive logarithmic admission and
  polynomial words/address support at every wider width. Adaptation costs `O(nD+Q)` beyond
  the actual callee; actual chunks derive `Q*2^m≤n²`, giving the per-record halt-inclusive bound
  `34603008*(19m+1)*n²/D^(1/18)` at `D=4^m`, `L=19m`, `D^18≤n`.
  The outer instance loop, aggregate subcubic ET bound, backend/witness reconstruction and
  the full [#1394] ordinary-3SUM 1.9992 endpoint remain open.
- **Per-record native witness recovery** ([#1639](https://github.com/cslib-community/complexitylib/issues/1639)):
  actual initialized producer/product calls now feed real answer/query loads and original signed
  weight verification. The fixed 400-register program returns original-coordinate witnesses and
  decides zeros in the selected existing chunk/piece. Its actual scan counter satisfies
  `S≤falsePositiveCount+returnedFlag`, so unsuccessful records have no successful-scan surplus.
  Root decoding, all control and original-weight scans are charged; positive logarithmic width
  and polynomial words/support hold at every wider admitted width. The outer instance loop,
  aggregate subcubic ET analysis and ordinary-3SUM 1.9992 composition remain open under [#1394].
- **Fixed-prime native catalogue decision** ([#1662](https://github.com/cslib-community/complexitylib/issues/1662)):
  the native continuation runs real preparation once and the actual product/witness callee
  over every computed occupied ordinal, stopping on the first original witness. Its initialized
  same-state prefix/halt verdict is equivalent to original ET, with dirty-workspace reuse and
  one global `S≤F(p)+returnedFlag` scan budget. All-instance product savings, all native control
  charges, original-input logarithmic admission and polynomial wider-prefix words/support are
  derived. Validation, independent review and integration are tracked in #1662. Global
  parameter/prime selection, unrestricted small geometry, the complete aggregate source exponent
  and the ordinary-3SUM 1.9992 endpoint remain open under [#1394].
- **Conditional Convolution-3SUM host** ([#1524]): the charged native host initializes from the
  ordinary input and runs every generated instance, conditional on a concrete solver's execution,
  correctness and frame theorem. This completes the conditional host milestone. Integrating the
  concrete fast Exact Triangle solver and the full input/time/width/asymptotic reduction remains
  open under [#1394].
- **Stateful algorithms and data structures:** Word-RAM controllers for larger adaptive and
  iterative clients, including the two-stack queue and timeline-editing controllers; reusable
  allocation and deallocation, shrinking, and live and peak space accounting; ownership and
  recursive procedures; model realizations for cell probes, caches and randomness; present and
  historical queries for the retroactive interface; balancing and heap or RAM representations of
  search trees; uniform preprocessing and dynamic updates for fusion trees; deletion and
  predecessor for van Emde Boas sets; and deallocation,
  shrinking and compiled client controllers for the doubling array.
- **A typed-call evaluator** for fixed-program Word-RAM clients, returning the typed observation,
  final state and halt-inclusive instruction cost, so the prefix-sum and stack clients no longer
  assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#1363]): lift operation-count helpers
  (`numQueries`, `numInserts`, `numDecreaseKeys`, `numExtractMins`) to `IndexedMinPQ`, parameterize
  flat-program operation-sequence execution (`RunsOps`) over `PQCode` in `PriorityQueue/Basic.lean`
  so `BinaryHeap` and `FibonacciHeap` share a generic `run_ops_exact` theorem, and factor a common
  `ShortestPathSpec p bound` predicate in `Dijkstra/HeapStatement.lean` across `LogLinearSpec`,
  `FibonacciSpec`, and `FibonacciLinearSpec`.

- **Native ExactTriangle preparation** ([#1532](https://github.com/cslib-community/complexitylib/issues/1532)):
  initialized execution computes the complete catalogue and raw zero/one instance matrices,
  with exact finite readback, logarithmic width, polynomial prefix words and address space,
  and a `690n²Dg` charged bound in the source's admissible parameter regime. Prime selection,
  solving the prepared instances, product/backend composition and the full #1394 endpoint remain.

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
- **Weighted multigraph cuts and two-branch probability recurrence** ([#1336]): extract
  `IsMultigraph` (renamed e.g. `IsSymmLoopless` or phrased via `Matrix.IsSymm` with zero diagonal),
  `IsNonTrivialCut`,
  `cutWeight`, `minCut`, `rowDeg`, `totalDoubledWeight`, `flattenMatrix`, and `IsContractionOf` from
  `Complexity/Algorithms/WordRAM/Karger/Graph.lean` (shared by `KargerMinCut` and `KargerStein`) into
  `Complexity/Foundations/Combinatorics/WeightedCut.lean` with a bridge lemma relating `cutWeight W C`
  to `(Cslib.Multigraph.edgeCut ends C).card`. Extract `two_branch_hit_prob_ge` from
  `Karger/FastCut.lean` into a shared probabilistic-program module; its `ProbComp` evaluation and
  support dependencies should stay above the `PMF` event layer.
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

- **Native declared-variable counting** ([#1226](https://github.com/cslib-community/complexitylib/issues/1226)):
  `CountingNativeEndpoint.exists_declaredCounter` supplies one native counter for each fixed width,
  exact on every valid declared-size/CNF input and zero otherwise. It has
  `2^{O_k(interpolationScale N)} * (L + 1)^{O_k(1)}` time and independent polynomial workspace in the
  original external encoded length `L`, with no supplier premises. The module derives
  subexponential-time `k`-SAT, zero SAT exponents, `¬ETH`, and `¬SETH`. This is the Sections 3–6 and
  Appendices A–B interpolation-scale bound, not the sharper Appendix D runtime. Integration,
  validation, and the curated formal abstract are tracked in #1226.

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

- The full VNP-completeness reduction for the permanent ([#321]).
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
[#645]: https://github.com/cslib-community/complexitylib/issues/645
[#798]: https://github.com/cslib-community/complexitylib/issues/798
[#800]: https://github.com/cslib-community/complexitylib/issues/800
[#862]: https://github.com/cslib-community/complexitylib/issues/862
[#881]: https://github.com/cslib-community/complexitylib/issues/881
[#884]: https://github.com/cslib-community/complexitylib/issues/884
[#886]: https://github.com/cslib-community/complexitylib/issues/886
[#888]: https://github.com/cslib-community/complexitylib/issues/888
[#889]: https://github.com/cslib-community/complexitylib/issues/889
[#890]: https://github.com/cslib-community/complexitylib/issues/890
[#891]: https://github.com/cslib-community/complexitylib/issues/891
[#892]: https://github.com/cslib-community/complexitylib/issues/892
[#893]: https://github.com/cslib-community/complexitylib/issues/893
[#894]: https://github.com/cslib-community/complexitylib/issues/894
[#895]: https://github.com/cslib-community/complexitylib/issues/895
[#896]: https://github.com/cslib-community/complexitylib/issues/896
[#897]: https://github.com/cslib-community/complexitylib/issues/897
[#939]: https://github.com/cslib-community/complexitylib/issues/939
[#949]: https://github.com/cslib-community/complexitylib/issues/949
[#999]: https://github.com/cslib-community/complexitylib/issues/999
[#1000]: https://github.com/cslib-community/complexitylib/issues/1000
[#1001]: https://github.com/cslib-community/complexitylib/issues/1001
[#1002]: https://github.com/cslib-community/complexitylib/issues/1002
[#1047]: https://github.com/cslib-community/complexitylib/issues/1047
[#1079]: https://github.com/cslib-community/complexitylib/issues/1079
[#1104]: https://github.com/cslib-community/complexitylib/issues/1104
[#1124]: https://github.com/cslib-community/complexitylib/issues/1124
[#1155]: https://github.com/cslib-community/complexitylib/issues/1155
[#1336]: https://github.com/cslib-community/complexitylib/issues/1336
[#1351]: https://github.com/cslib-community/complexitylib/issues/1351
[#1363]: https://github.com/cslib-community/complexitylib/issues/1363
[#1394]: https://github.com/cslib-community/complexitylib/issues/1394
[#1435]: https://github.com/cslib-community/complexitylib/issues/1435
[#1438]: https://github.com/cslib-community/complexitylib/issues/1438
[#1442]: https://github.com/cslib-community/complexitylib/issues/1442
[#1446]: https://github.com/cslib-community/complexitylib/issues/1446
[#1447]: https://github.com/cslib-community/complexitylib/issues/1447
[#1449]: https://github.com/cslib-community/complexitylib/issues/1449
[#1524]: https://github.com/cslib-community/complexitylib/issues/1524
[#1572]: https://github.com/cslib-community/complexitylib/issues/1572
