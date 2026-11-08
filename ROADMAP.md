# Roadmap

The directions Complexitylib aims to cover, grouped by area.
This file lists directions only: status, progress and completion notes live on the linked issues and pull requests, module docstrings describe what is proved, and the [README](README.md) and the curated formal abstracts present completed results.
A PR edits this file only when it opens or closes a direction.
Each entry states its direction's scope in at most a few sentences, one sentence per line.
A direction leaves this file only when it is completed or deliberately dropped, and there is no deferred tier.

A direction is complete only when its machine, resource and quantitative conclusions are proved for the actual algorithms, with explicit models, encodings and assumptions.
An abstract algorithm, a class definition or an assumed reconstruction theorem does not complete it.
Search Mathlib, CSLib and this library before starting, and check upstream work.

The [pre-rewrite roadmap](https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md) is the archive of past detail and design records, including the FHE industrial context, the first-order design decisions and the repository's history.
The [version before the scope-only rewrite of 2026-11-08](https://github.com/cslib-community/complexitylib/blob/9886447e2/ROADMAP.md) holds the progress notes removed in that rewrite.

## Programs

| Program | Issues |
| --- | --- |
| Frontier program: ambitious theorems toward the research frontier | [#897](https://github.com/cslib-community/complexitylib/issues/897); its tracks are linked below |
| Optional experiment: formalize unformalized STOC 2027 submission results, subject to independent source-correspondence review | [#2527](https://github.com/cslib-community/complexitylib/issues/2527) |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798](https://github.com/cslib-community/complexitylib/issues/798), audit [#884](https://github.com/cslib-community/complexitylib/issues/884) |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862](https://github.com/cslib-community/complexitylib/issues/862), from [#456](https://github.com/cslib-community/complexitylib/issues/456) |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949](https://github.com/cslib-community/complexitylib/issues/949), [#939](https://github.com/cslib-community/complexitylib/issues/939) |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#2585](https://github.com/cslib-community/complexitylib/issues/2585) |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640](https://github.com/cslib-community/complexitylib/issues/640), [#643](https://github.com/cslib-community/complexitylib/issues/643) |
| Crypto frontier track: Kilian's succinct arguments | [#999](https://github.com/cslib-community/complexitylib/issues/999) |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002](https://github.com/cslib-community/complexitylib/issues/1002) |
| A Verso guide with a chapter per area | [#585](https://github.com/cslib-community/complexitylib/issues/585) |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124](https://github.com/cslib-community/complexitylib/issues/1124) |
| Proof automation: predictable polynomial-time certificate search | [#1155](https://github.com/cslib-community/complexitylib/issues/1155) |

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897](https://github.com/cslib-community/complexitylib/issues/897).

1. [Completeness of oblivious transfer](#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886](https://github.com/cslib-community/complexitylib/issues/886))
3. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889](https://github.com/cslib-community/complexitylib/issues/889))
4. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity) ([#321](https://github.com/cslib-community/complexitylib/issues/321))
5. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891](https://github.com/cslib-community/complexitylib/issues/891))
6. [MIP = NEXP](#interactive-proofs) ([#892](https://github.com/cslib-community/complexitylib/issues/892))
7. [Regev's worst-case to average-case reduction](#cryptographic-landmarks)

### Optional landmark projects

These are optional coverage targets outside the priority queue above, each requiring substantial new proof infrastructure; a prerequisite milestone does not complete the landmark.
Choose a source version and proof route before implementation, and reassess scope against existing library and upstream developments.
The size labels describe prerequisite breadth, not staffing or calendar estimates.

- **Babai: graph isomorphism in quasipolynomial time — optional, very large**: Prove a deterministic `exp((log n)^O(1))` decision bound for the existing encoded graph-isomorphism problem, following the [manuscript](https://arxiv.org/abs/1512.03547v2) with its [January 2017 correction](https://people.cs.uchicago.edu/~laci/upcc-fix.pdf).
  It needs certified permutation-group algorithms, the Luks framework, local certificates and the full recursion with native quasipolynomial runtime.
  An NP verifier is not the required decision algorithm.
- **Bulatov–Zhuk: the finite-domain CSP dichotomy — optional, very large**: For every fixed finite constraint language, prove its CSP is in P or NP-complete, following the tractability route of either [Bulatov](https://arxiv.org/abs/1703.03021) or [Zhuk](https://arxiv.org/abs/1704.01914v11), not both.
  The tractability algorithm has a native polynomial bound, with template-dependent constants kept separate from instance size.
  Special cases and reductions are milestones, not the full dichotomy.
- **QIP = PSPACE — optional, large**: Following [Jain–Ji–Upadhyay–Watrous](https://cs.uwaterloo.ca/~watrous/Papers/QIPequalsPSPACE.pdf), prove both inclusions for polynomial-time quantum interactive proofs with a uniform verifier, unrestricted prover strategies and explicit completeness and soundness gaps.
  The upper bound needs a polynomial-space matrix multiplicative-weights argument with controlled precision; quantum circuit simulation alone does not provide it.
- **MIP\* = RE — optional, large integration project; exceptional if rebuilt from scratch**: Prove the characterization of RE in [Ji–Natarajan–Vidick–Wright–Yuen, v4](https://arxiv.org/abs/2001.04383v4) as a native class equality, with finite-dimensional tensor-product strategies, their supremum over unbounded finite dimensions and a uniform polynomial-time verifier.
  Distinguish classical MIP from commuting-operator models.
  Start by auditing reuse of the Apache-2.0 [MIPRE formalization](https://github.com/vidick/MIPRE-formalization) rather than duplicating its compression proof.

## Cryptography

### Cryptographic landmarks

- **Completeness of oblivious transfer** ([#1212](https://github.com/cslib-community/complexitylib/issues/1212)): In the ideal OT-hybrid model, every polynomial-time multiparty functionality admits a protocol secure against static malicious corruptions, with real/ideal simulation and abort, under the standard communication assumptions.
  The route needs ideal commitment realization from OT with efficient two-sided simulation, composition, a malicious compiler and MPC simulation.
- **Regev's worst-case to average-case reduction** ([#1213](https://github.com/cslib-community/complexitylib/issues/1213)): For suitable `q` and Gaussian noise rate `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`.
  The noise law, modulus restrictions and quantum reduction are part of the theorem.
  Its foundations are [#2573](https://github.com/cslib-community/complexitylib/issues/2573), [#2592](https://github.com/cslib-community/complexitylib/issues/2592), [#2608](https://github.com/cslib-community/complexitylib/issues/2608), [#2624](https://github.com/cslib-community/complexitylib/issues/2624), [#2646](https://github.com/cslib-community/complexitylib/issues/2646), [#2659](https://github.com/cslib-community/complexitylib/issues/2659), [#2681](https://github.com/cslib-community/complexitylib/issues/2681), [#2707](https://github.com/cslib-community/complexitylib/issues/2707), [#2734](https://github.com/cslib-community/complexitylib/issues/2734), [#2766](https://github.com/cslib-community/complexitylib/issues/2766) and, for Lemma 3.11, [#2767](https://github.com/cslib-community/complexitylib/issues/2767).
- **Kilian's succinct arguments** ([#999](https://github.com/cslib-community/complexitylib/issues/999)): If collision-resistant hash families exist, every language in NP has an interactive argument with polylogarithmic communication, by committing to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle versions.
  The target needs an honest prover efficient from an arbitrary NP witness, with the verifier's runtime and message truncation accounted for.

### Modern fully homomorphic encryption

Develop these in reviewable milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions where their hypotheses match.
The [pre-rewrite FHE section](https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities) maps the schemes to current libraries and workloads.

- **Gentry's exact loss and running time** ([#2585](https://github.com/cslib-community/complexitylib/issues/2585), [#2722](https://github.com/cslib-community/complexitylib/issues/2722)): For Gentry's bootstrapping instantiated with GSW ([#486](https://github.com/cslib-community/complexitylib/issues/486), [#1104](https://github.com/cslib-community/complexitylib/issues/1104)), prove his exact concrete-security loss and the `poly(ℓ, d)` running-time clause of his Theorem 4.
  This includes the literal source loss mapping, a multiplicative comparison of primitive costs with adversary runtime, and the complete modular-game time and space assembly with prepared-metadata accounting.

1. **Ring arithmetic and RLWE**: Natively certify ring operations over `(Z/qZ)[X]/(X^d + 1)`, RNS/CRT conversions, rounding and modulus switching with error bounds and parity-preserving variants, and negacyclic NTT multiplication.
   Define the RLWE secret and error laws and experiment separately, since an ordinary-LWE reduction does not give them.
   For Module-LWE encryption, add native encryption, seed codecs and small-secret security.
2. **FHEW/TFHE programmable bootstrapping** ([Ducas–Micciancio](https://eprint.iacr.org/2014/816); [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870)): Prove the bootstrap decrypts to `f(m)` with its noise, failure, width and runtime bounds, under negacyclic lookup restrictions and torus representations.
   Floating-point FFTs need rounding-error proofs.
   Then add [Lee et al.'s smaller-key methods](https://eprint.iacr.org/2022/198) and batched variants with exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV** ([Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277); [Fan–Vercauteren](https://eprint.iacr.org/2012/144)): Slot encoding, multiplication, relinearization, rotations and level management, with leveled evaluation before a separately proved refresh.
   Equality modulo the plaintext modulus differs from ordinary integer equality, which needs a range bound.
4. **Approximate packed CKKS and its bootstrap** ([Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421)): An explicit approximate-correctness interface and a norm bound on decoded error covering rescaling, rounding, key switching and rotations.
5. **Scheme switching and threshold variants**: Explicit range and precision contracts, evaluation-key assumptions, corruption thresholds, interaction, robustness and decryption-query access, distinguishing honest-but-curious from malicious security.

For each scheme, prove chosen-plaintext security for the actual algorithms and public evaluation keys; keep LWE/RLWE, circular/KDM assumptions and attack-cost estimates distinct; introduce a decryption-failure game when correctness is not perfect; and require nonvacuous parameter families and full-input native runtime.

### Public-key, lattice and symmetric constructions ([#640](https://github.com/cslib-community/complexitylib/issues/640))

- **Sigma protocols and Fiat–Shamir** ([#581](https://github.com/cslib-community/complexitylib/issues/581), [#2568](https://github.com/cslib-community/complexitylib/issues/2568)): Prove random-oracle EUF-CMA security of Schnorr signatures under discrete log against strict PPT forgers with encoded signing and hash access, by an efficient forking reduction for the actual key-generation and signing algorithms.
  Identification and eavesdropping security do not suffice.
  Its components are [#2672](https://github.com/cslib-community/complexitylib/issues/2672), [#2684](https://github.com/cslib-community/complexitylib/issues/2684), [#2696](https://github.com/cslib-community/complexitylib/issues/2696), [#2708](https://github.com/cslib-community/complexitylib/issues/2708), [#2724](https://github.com/cslib-community/complexitylib/issues/2724), [#2774](https://github.com/cslib-community/complexitylib/issues/2774), and forger replay in [#2579](https://github.com/cslib-community/complexitylib/issues/2579), [#2636](https://github.com/cslib-community/complexitylib/issues/2636) and [#2652](https://github.com/cslib-community/complexitylib/issues/2652).
- **Lattice signatures from SIS**: Prove random-oracle EUF-CMA security of Lyubashevsky's signatures (2009, 2012) from SIS by a native reduction that receives only `A`, with an efficient secret-free simulator and a security parameter family.
  The route covers forking ([#2620](https://github.com/cslib-community/complexitylib/issues/2620)), witness invariance ([#2642](https://github.com/cslib-community/complexitylib/issues/2642)), the ROM bridge ([#2661](https://github.com/cslib-community/complexitylib/issues/2661)), cache-hit bounds ([#2712](https://github.com/cslib-community/complexitylib/issues/2712)), oracle programming ([#2750](https://github.com/cslib-community/complexitylib/issues/2750)) and visible signing simulation ([#2788](https://github.com/cslib-community/complexitylib/issues/2788), [#2798](https://github.com/cslib-community/complexitylib/issues/2798)).
- **Lattice identification and Dilithium-style signatures**: Prove identification security under SIS, and the security of Dilithium-style signature schemes over module SIS and module LWE, as theory.
- **Hybrid encryption** ([#2725](https://github.com/cslib-community/complexitylib/issues/2725)): Prove adaptive CCA security of KEM–DEM hybrid encryption, with the factor-two bound of Boneh–Shoup Exercise 12.5(a) for `n`-bit messages, by native reductions to the KEM and one-time symmetric CCA games ([#2692](https://github.com/cslib-community/complexitylib/issues/2692), [#2694](https://github.com/cslib-community/complexitylib/issues/2694)).
  Then extend it to arbitrary message spaces, prechallenge KEM queries and multiple encapsulation challenges.
- **Paillier encryption and composite residuosity**: Prove IND-CPA security of Paillier encryption under Decisional Composite Residuosity (Katz–Lindell Theorem 15.13) for the actual word algorithms, with approximate unit sampling and native balanced-modulus generation.
  The homomorphic property of Definition 15.14 needs an exact or statistical-closeness formulation, since its exact distributional condition fails for the implemented sampler.
- **General**: Reusable adaptive reductions, public-key encryption, universal-instance zero knowledge, hard-core predicates and hardness amplification, and connections to learning and average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643](https://github.com/cslib-community/complexitylib/issues/643))

The libzk components are listed in build order, ending with libzk's compositional structure.
General auxiliary-input zero knowledge, the last entry, is independent of that order.

- **Public-coin to IP bridge**: Map public-coin protocols into IP with a uniform word verifier and adversarial message decoding.
- **Composition and round-by-round knowledge soundness**: Parallel and AND/OR composition of protocols and relations, with round-by-round knowledge soundness preserved under sequential, parallel and OR composition.
- **Oracle statements**: Let a later phase query an earlier phase's oracle message (virtual output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds.
- **Efficient simulators and auxiliary-input zero knowledge**: Efficiency-certified simulators and extractors, and auxiliary-input zero knowledge on the interactive core.
- **Polynomial commitments and Ligero**: Polynomial commitment and evaluation-query reductions, and the Ligero IOP.
- **BCS transform**: Compile IOPs into non-interactive arguments in the random-oracle model with soundness and knowledge-soundness bounds, machine-level verifier and extractor runtime, a polynomial-time encoding of NP witnesses into IOPs, and zero knowledge.
- **VOLE constraint reductions and VOLE-in-the-head**: Prove full zero-knowledge security of VOLE-based proofs for the arithmetic-circuit relation `∃ w, C.eval (x ++ w) = y`, with fresh-session amplification, scalar-challenge batching, growing fields, adversarial setup and scheduling, then VOLE-in-the-head.
  This includes a native circuit prover/verifier certificate with honest-sender realization ([#2765](https://github.com/cslib-community/complexitylib/issues/2765)) and raw-bit adversarial transport ([#2744](https://github.com/cslib-community/complexitylib/issues/2744)).
- **libzk composition**: Express libzk's compositional structure as a composition of these components, without ciphersuites.
- **General auxiliary-input zero knowledge** ([#324](https://github.com/cslib-community/complexitylib/issues/324)): If one-way functions secure against non-uniform adversaries exist, every language in NP has an interactive computational zero-knowledge proof system secure against PPT verifiers with arbitrary auxiliary input, following Goldreich–Micali–Wigderson with Naor's bit commitments.

### Concurrent and quantum security

- **Concurrent composition**: Extend the protocol semantics with environments, scheduling, session identifiers and concurrent executions, and prove a composition theorem with efficient simulators and explicit setup, corruption and communication assumptions.
  Then develop selected adaptive-corruption and non-malleability applications, alongside the static-malicious OT target.
- **Quantum-secure cryptography**: Define uniform quantum-efficient distinguishers and computational indistinguishability with quantum side information, and justify security reductions for concrete constructions in that model.
  Connect the quantum-computation and lattice tracks through these adversary models.
  Later targets include quantum oracle access, the quantum random-oracle model, and extraction or rewinding under their precise hypotheses.

## Complexity classes and reductions

### Coverage catalogue

Build an auditable coverage index of the [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo) and canonical problems and theorems ECCC papers need, verified against primary sources and linked to canonical definitions.
Each entry records source, aliases, model, conventions (uniformity, advice, oracle access, error gaps, resources, reduction type), Lean declarations, missing prerequisites and level, from definition to verified theorem.
Containments, separations, closure properties, complete problems and reductions are tracked separately across decision, function, search, counting, promise, distributional and parameterized problems.

### Structure, time and space

- **Planar Boolean CSP dichotomy** ([#3091](https://github.com/cslib-community/complexitylib/issues/3091)): extend the native Boolean classification to ordered planar instances of arbitrary fixed relation arity, preserving individual incidence occurrences and cyclic argument order.
  The endpoint proves the embedding and recognition interface, the cyclic-difference reduction, the even delta-matroid edge-CSP algorithm and planar hardness transfer internally, including the additional self-complementary tractable family.
  Supplied-embedding or matching-realizable-only milestones leave it open.
- **Boolean Schaefer dichotomy** ([#2822](https://github.com/cslib-community/complexitylib/issues/2822)): for every fixed finite Boolean constraint language of any fixed arity, native polynomial-time tractability in the six common-polymorphism cases and native NP-completeness otherwise, including empty and nullary relations.
  Hardness uses a native 3SAT reduction with `output.numVars + output.length ≤ C * input.length` for a language-dependent constant.
  Symmetric and larger-domain dichotomies are out of scope.
- **Structural classes and relativization:** time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes; completeness, padding, self-reducibility, relativization and oracle separations, preserving each reduction's resource bound.
- **Abstract (Blum) complexity** ([#2866](https://github.com/cslib-community/complexitylib/issues/2866)): Blum measures over Mathlib's `Nat.Partrec.Code`, with gap, speedup, union and compression theorems, recursive relatedness and arbitrarily complex functions.
  Compression is in running-time form, one computable `h` with `C_{Φ_i} ⊂ C_{n ↦ h n (Φ_i n)}` for every total `φ_i`; the value form is false by the gap theorem.
  Also McCreight–Meyer honesty and naming ([#3234](https://github.com/cslib-community/complexitylib/issues/3234)), `g`-honesty for partial functions (Odifreddi II, Exercises VII.2.14b–d), effective speedup (Blum's pseudo-speedup), and native multitape time and space as measures.
- **Time hierarchies** ([#1572](https://github.com/cslib-community/complexitylib/issues/1572)): native deterministic and nondeterministic time hierarchies, including separations of all polynomial degrees (noninteger ones too) and the textbook `f log f = o(g)` hierarchy from the `O(t log t)` universal simulation ([#800](https://github.com/cslib-community/complexitylib/issues/800)).
  Also a word-RAM hierarchy by direct diagonalization with a gap smaller than `T` versus `T⁵`, and sharp nondeterministic and alternating time hierarchies with certified simulators.
- **Probabilistic time hierarchies** ([#2084](https://github.com/cslib-community/complexitylib/issues/2084)): the `PromiseBPTIME` hierarchy for promise problems by delayed diagonalization, following He (ECCC TR25-004), and the one-bit-advice hierarchy for languages of van Melkebeek and Pervyshev.
  The advice-free hierarchy for `BPTIME` itself is open and is not a target.
- **Randomized primality tests** ([#2917](https://github.com/cslib-community/complexitylib/issues/2917)): the Euler-liar and strong-liar bounds `2 · #liars ≤ φ(n)` and the Rabin–Monier bound `4 · #strong liars ≤ φ(n)` (`n ≠ 9`) for odd composite `n`, and explicit Miller–Rabin and Solovay–Strassen verifiers putting the primes in `coRP` independently of AKS.
  The Solovay–Strassen verifier ([#2958](https://github.com/cslib-community/complexitylib/issues/2958)) uses the polynomial-time Jacobi symbol and a gcd step, since non-units can satisfy Euler's congruence.
- **Space hierarchy:** the space hierarchy for `log n ≤ g n`, which needs a universal simulation that does not hold its input.
- **Space:** Savitch bounds for general space-constructible functions.
- **Catalytic space and KMPS collapses** ([#2521](https://github.com/cslib-community/complexitylib/issues/2521)): native `CSPACE(s,c)` with nondeterministic and randomized variants, restoring the catalyst on every branch.
  Koucký–Mertz–Pyne–Sami's [*Collapsing Catalytic Classes*](https://arxiv.org/abs/2504.08444) with its parameter ranges and oracle promises: `CL = CNL = CPrL = CBPL`, compress-or-compute simulation, catalytic Savitch and complementation, randomized space–catalyst tradeoffs, hierarchy collapses and lossy-space consequences.
- **Robust catalytic extensions** ([#2521](https://github.com/cslib-community/complexitylib/issues/2521)): the Koucký–Mertz–Sami [robust catalytic extensions](https://arxiv.org/abs/2605.09648), tracked separately from KMPS.
  Their broader collapse is conditional on an explicit circuit-hardness assumption, and their resetting-error and time regimes are kept distinct from the unconditional KMPS results.
- **Randomized logspace** ([#459](https://github.com/cslib-community/complexitylib/issues/459), [#474](https://github.com/cslib-community/complexitylib/issues/474)): two-sided `BPL` amplification, the random-walk proof of `USTCON ∈ RL`, Nisan's generator with its read-once fooling theorem ([#3187](https://github.com/cslib-community/complexitylib/issues/3187)), space-efficient computation and configuration-graph bridge, `BPL ⊆ L²`, and Saks–Zhou's `BPL ⊆ L^{3/2}`.
  The Saks–Zhou iteration as pure mathematics is [#3247](https://github.com/cslib-community/complexitylib/issues/3247), a milestone of [#474](https://github.com/cslib-community/complexitylib/issues/474).
  The preprint route to native `RL = L` is [#1444](https://github.com/cslib-community/complexitylib/issues/1444), with its estimator in [#1721](https://github.com/cslib-community/complexitylib/issues/1721).
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888](https://github.com/cslib-community/complexitylib/issues/888)): the native inclusion for arbitrary injective input encodings and every `t(n) ≥ n`, without time constructibility, via Tree Evaluation.
  The paper's time–space separation corollaries (including for linear space), a curated headline abstract with independent review, Cook–Mertz malformed-input handling and the refined `O(ℓ + H log(ℓ + 2))` bound are [#2855](https://github.com/cslib-community/complexitylib/issues/2855).
- **Time–space lower bounds for nondeterministic linear time** ([#2896](https://github.com/cslib-community/complexitylib/issues/2896)): the Arora–Barak bound `NTIME(n) ⊄ TISP(n^1.2, n^0.2)` by virtual padding and the Lipton–Viglas `n^(√2 − ε)` form, from the speedup and slowdown lemmas for `TISP` and `Σ₂TIME`.
  Beyond these: the textbook `√(t·s)` speedup, the golden-ratio deterministic bound of Fortnow, Lipton, van Melkebeek and Viglas, and the transfer to SAT through a quasi-linear-size Cook–Levin reduction.
- **Alternating classes:** alternating time and space classes and bounded-alternation characterizations of PH; sharp bounds for sublinear space, distinct from polynomial-space simulation.
- **Alternating logspace, `P ⊆ AL`** ([#2873](https://github.com/cslib-community/complexitylib/issues/2873)): play the circuit-value game on the tableau of a polynomial-time machine in logarithmic space.
  This needs a word game machine whose round reads the input from the input tape and keeps only the `O(log n)`-bit wire claim on its work tape.
- **Pebble games and space lower bounds** ([#2995](https://github.com/cslib-community/complexitylib/issues/2995)): black, black-white and reversible pebbling on digraphs, with exact prices and register evaluation.
  The direction covers Bennett's game on paths ([#3163](https://github.com/cslib-community/complexitylib/issues/3163)), Li–Tromp–Vitányi's reachable-configuration characterization and erasure and time–space trade-offs ([#3199](https://github.com/cslib-community/complexitylib/issues/3199)), the Hopcroft–Paul–Valiant `O(n / log n)` bound with the matching Paul–Tarjan–Celoni family, and Gilbert–Tarjan and Lengauer–Tarjan trade-offs.
- **Deeper consequences of a Boolean-hierarchy collapse:** Kadin's sparse `S` with `coNP ⊆ NP^S`, and the collapse of `PH` into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, which follows from results of Wagner and of Chang and Kadin, not from Kadin's 1988 argument (see his erratum).
- **Explicit universal SAT solver:** one fixed native algorithm, independent of any assumed fast SAT algorithm, whose worst-case running time is polynomial if and only if `P = NP`.
  It is a total SAT decision procedure, also on unsatisfiable inputs, specified separately from verified witness search.
  The proof accounts for dovetailing, certificate checking and universal simulation overhead, not only the `SAT ∈ P ↔ P = NP` equivalence.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351](https://github.com/cslib-community/complexitylib/issues/1351)): logspace Turing reductions, in an oracle model whose query tape is not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets** ([#2062](https://github.com/cslib-community/complexitylib/issues/2062), [#3155](https://github.com/cslib-community/complexitylib/issues/3155)): Kadin's `PH = P^{NP[O(log n)]}` from a sparse Turing-complete set for NP, his stronger form with a sparse `S ∈ NP` and `coNP ⊆ NP^S`, and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** paddability of the standard NP-complete graph, number and set problems, hence their p-isomorphism to SAT; every many-one complete set for EXP is complete under one-one, length-increasing reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal, Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang); separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468](https://github.com/cslib-community/complexitylib/issues/2468)): the full expanded 2013 paper of Glaßer, Nguyen, Reitwießner, Selman and Witek: Lemma 3.3's transfer from local self-reducibility with answer regeneration and adaptive-to-tt conversion, its bounded and many-one cases, Theorem 3.5, and Sections 4 and 5 (query bounds, separations, mitoticity, diagonalization).
  The parity-logspace application needs native path counting and complement closure.
- **Uniform diagonalization** ([#3142](https://github.com/cslib-community/complexitylib/issues/3142)): Schöning's theorem for recursively presentable classes closed under finite variations, and a recursive presentation of the polynomial-time degree of a decidable set outside `P`, giving Ladner's density theorem and, if `P ≠ NP`, an `NP`-intermediate problem below every `NP`-complete one.
  Further presentable classes: `NP`, `PSPACE` and the levels of the polynomial hierarchy.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE, self-reducible P-selective sets lie in P, and P-selective sets are not `≤ₜₜᵖ`-hard for NP unless P = NP.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity** ([#2899](https://github.com/cslib-community/complexitylib/issues/2899)): `P`-bi-immune sets in `E`, Berman's theorem that `≤ᵖₘ`-complete sets for `E` and `EXP` are not `P`-immune ([#3002](https://github.com/cslib-community/complexitylib/issues/3002)), and complexity cores, from Lynch's lemma ([#3080](https://github.com/cslib-community/complexitylib/issues/3080)) and decidable cores ([#3182](https://github.com/cslib-community/complexitylib/issues/3182)) to `EXP` and `PSPACE` instances, core density (Orponen–Schöning) and core sizes (Juedes–Lutz).
  `DTIME(t)`-bi-immunity for constructible `t`, other Balcázar–Schöning results, almost-everywhere hardness, and Mayordomo's measure results.
- **Exponential-time complete problems** ([#3002](https://github.com/cslib-community/complexitylib/issues/3002)): bounded halting with a binary time bound as an `E`- and `EXP`-complete problem, Book's separations of `E` from `EXP`, `NP` and `PSPACE`, succinct circuit value for `EXP` and succinct SAT for `NEXP`, generalized games complete for `EXP`, nondeterministic bounded halting for `NE` and `NEXP`, and the isomorphism and density structure of `E`-complete sets.

### Average-case complexity

- **Distributional framework** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): length-indexed ensembles, `AvgP`, `HeurP`, `DistNP`, dominating reductions, samplability of polynomial-time computable ensembles, Levin's runtime-moment average polynomial time and its relation to errorless schemes, and randomized average-case classes.
  Probability-zero instances obstruct a literal equivalence with errorless schemes.
  Liu–Pass hardness notions should be reused through proved bridges.
- **Heuristic hierarchy and universal distributions** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): `(BH, U^BH) ∈ Heur_{1/n} P` gives `DistNP ⊆ HeurP`, with the `Avg` analogue (Bogdanov–Trevisan Prop. 21), via a fixed clocked universal program on inputs `(c, z, 1^t)`, since the source's padding can change `BH` membership.
  Also Levin, Li and Vitányi (Bogdanov–Trevisan Thm 16): under `K_n(x) ∝ 2^{-C(x)}` on each length, a decidable `L` with `(L, K) ∈ Heur_{1/n³} P` is in `P`.
- **Completeness beyond computable ensembles** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): extend bounded-halting completeness for `DistNP` to samplable distributions (Impagliazzo–Levin, `SampNP`), and bridge the verifier-form bounded halting problem to a nondeterministic machine model.
  Connect the framework to one-way functions, learning and the metacomplexity track ([#798](https://github.com/cslib-community/complexitylib/issues/798)), preserving the distribution and reduction conventions.

### Counting and modular classes

- **Another Solution Problem (ASP) framework:** ASP reductions with certified polynomial-time forward and inverse witness maps, starting from the parsimonious reductions to positive exact-one SAT and its planar three-occurrence variants.
  Exact count preservation alone does not supply the ASP runtime certificates.
- **Counting reductions and hierarchies:** counting reductions and further oracle results preserving exact multiplicities; permanent #P-completeness; modular and counting hierarchies; the oracle-algorithm form of Stockmeyer's approximate counting.
- **Exact counting by determinants** ([#3081](https://github.com/cslib-community/complexitylib/issues/3081)): polynomial-time counting through Kirchhoff's matrix-tree theorem for spanning trees, its weighted and directed (arborescence) forms, the BEST theorem for Eulerian circuits, and Kasteleyn's Pfaffian method for perfect matchings of planar graphs, in contrast with permanent #P-completeness.
- **Composite moduli:** the prime-power collapse `Mod_{p^e}P = Mod_pP` and union closure.
  Complement closure for moduli that are not prime powers is open, and relativizing proofs cannot give it (Barrington–Beigel–Rudich), so it is not a library direction.
- **Target-relativized counting classes:** `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and UP-oracle containment.
- **Native oracle counting machines:** efficient encoded oracle checking, response-access costs and oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **MIP = NEXP** ([#892](https://github.com/cslib-community/complexitylib/issues/892)): `NEXP ⊆ MIP₂` through the BFL multilinearity test and arithmetization of exponential-time tableaux; an efficient GKR verifier under log-space uniformity.
- **Goldwasser–Sipser** ([#2981](https://github.com/cslib-community/complexitylib/issues/2981)): `IP[k] ⊆ AM[k + 2]` for the private-coin games `IPk`, by the set lower bound protocol on the gap-amplified game.
- **Arthur–Merlin classes:** the Babai–Moran speedup `AM[2 t(n)] = AM[t(n)]` for polynomially many rounds (patterns that depend on the input length), interactive-machine characterizations of Arthur–Merlin classes, and statistical and perfect zero knowledge.
- **Statistical zero knowledge** ([#3205](https://github.com/cslib-community/complexitylib/issues/3205)): Sahai–Vadhan polarization as a polynomial-time map on encoded Statistical Difference instances with error `2^-(|x|+1)`, honest-verifier SZK containing `SD`, `SD` being SZK-complete, Entropy Difference (Goldreich–Vadhan), closure under complement (Okamoto), and `SZK ⊆ AM ∩ coAM` (Fortnow; Aiello–Håstad).
  Instances are pairs of De Morgan circuits, with general pairs padded to common input and output counts.

### Descriptive complexity and first-order reductions

Ordered first-order complexity follows Immerman: structures on {0, …, n-1} with n ≥ 2, FO means FO(≤, BIT), and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings; the order-free `FO.Reduces` and `FO.QFReduces` stay as a general layer.
Numeric predicates are computed from the universe size, not supplied as unverified input tables.
In dependency order:

- **Ordered completeness:** SAT, 3SAT, 3COL, independent set, clique and vertex cover NP-complete under first-order or quantifier-free projections; REACH NL-complete under first-order reductions.
- **Projections:** projection reducibility on finite structure classes and the standard ordered machine-encoding bridge.
  The classical qfp convention excludes BIT (Immerman–Landau, Definition 3.6), and arbitrary quantifier-free combinations of input relations are not projections.
- **Circuit Value P-completeness:** Circuit Value is P-complete under first-order reductions, via `REACHa → MCVP → CVP` (Immerman, Theorem 3.26 and Exercise 3.28), with the alternating-logspace simulation of polynomial-time machines (the machine-level `P ⊆ AL`, see [#2873](https://github.com/cslib-community/complexitylib/issues/2873)) and the translation to `encCircuitValue`.
- **Restricted-domain numeric certificates:** numeric certificates for further restricted-domain families; canonical BIT on a restricted domain need not be first-order definable.
- **Order-free reductions:** SAT-to-3SAT, graph-property hardness, and bridges to the separately encoded problems.
- **Synthesis rules and regular-language quantifiers:** extend the synthesis rules to nested operator bodies and give regular-language quantifiers their ordered characteristic-word semantics.
- **FO(TC) = NL on ordered structures** ([#1246](https://github.com/cslib-community/complexitylib/issues/1246)): both inclusions, with NL ⊆ FO(TC) via configuration-graph reachability under the ordered encoding.
  Separately, the native NL closure facts the in-compiler inductive counting bypasses: intersection, union, logspace reductions and NL^NL = NL.
- **Further logical characterizations:** on ordered structures, FO(DTC) = L, SO-Horn = P (Grädel), and DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing); then order-invariant and fixed-point queries and uniform translations between syntax, structures and algorithms.
- **Witness-carrying reductions:** a witness-carrying reduction structure once a client needs one, for example size bounds for Cook–Levin.
- **Logical lower-bound methods** ([locality track](https://github.com/cslib-community/complexitylib/issues/3015)): Ehrenfeucht–Fraïssé games (also with constants), pebble games with finite-variable equivalence, Hanf and Gaifman locality with Gaifman's normal form, and counting and fixed-point expressiveness with Cai–Fürer–Immerman separations, linked to the ordered capture theorems, where FO(≤, BIT) defines EVEN.
  Applications: Libkin's balanced binary trees and transitive closure, planarity, Hamiltonicity and `k`-colorability for `k ≥ 3`.
- **Undecidability in the finite** ([#2886](https://github.com/cslib-community/complexitylib/issues/2886)): Trakhtenbrot's theorem over any vocabulary with a binary relation symbol (Libkin, Theorem 9.2), transferred from raw relational sentences to Mathlib's `L.Sentence` through a computable `Primcodable` bridge.
- **Logic and automata on words** ([#2885](https://github.com/cslib-community/complexitylib/issues/2885)): Büchi–Elgot–Trakhtenbrot (MSO = regular on finite words), FO[<] ⊊ MSO, and FO[<] = star-free = aperiodic (McNaughton–Papert, Schützenberger; star-free ⇒ FO is [#3075](https://github.com/cslib-community/complexitylib/issues/3075)).
  Homomorphic-image closure of regular languages (upstream to cslib), the non-elementary formula-to-automaton lower bound, Büchi's theorem for ω-words (S1S), and MSO on finite trees (Thatcher–Wright, Doner) and infinite trees (Rabin, S2S).
- **Asymptotic probabilities** ([#2967](https://github.com/cslib-community/complexitylib/issues/2967)): 0-1 laws for `G(n, 1/2)` and for uniform structures over finite relational vocabularies, extended to constant edge probabilities, unlabelled structures and classes defined by parametric axioms such as the simple-graph axioms.
  Then the Kolaitis–Vardi laws for fixed-point and finite-variable infinitary logics, and the Shelah–Spencer laws for sparse random graphs.
- **Dynamic descriptive complexity:** dynamic programs and update semantics with explicit initialization, auxiliary relations and domain conventions; invariant-preservation rules and reachability in DynFO as a target.
  Relate logical update restrictions to the stateful-algorithm interfaces through explicit translations.

Independent of that order:

- **Color refinement and Weisfeiler–Leman** ([#3265](https://github.com/cslib-community/complexitylib/issues/3265)): stabilization, the coarsest equitable partition and soundness of the 1-WL test; equitable partitions as fractional automorphisms and isomorphisms (Tinhofer; Ramana–Scheinerman–Ullman; Grohe–Kersting–Mladenov–Selman, Theorems 4.1 and 5.2); a certified polynomial-time algorithm; and `k`-dimensional Weisfeiler–Leman.
  Also the Immerman–Lander correspondence with the counting logic C² and its finite-variable extensions, and Cai–Fürer–Immerman graphs.
- **Vollmer's generalized quantifier framework** ([#399](https://github.com/cslib-community/complexitylib/issues/399)): Vollmer's survey [*A Generalized Quantifier Concept in Computational Complexity Theory*](https://arxiv.org/abs/cs/9809115), covering ordered leaf words, explicit uniformity and input-access models, finite-monoid classification and generalized logical quantifiers.
  The formalization must keep the paper's resource models and quantifier bounds.

### Uniform circuit families

Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and input encodings; certify circuit generation, evaluation and the machine-to-circuit simulations, preserving size, depth and construction resources; and prove FO with order and BIT equals DLOGTIME-uniform AC⁰ under explicit conventions.

### Search, parameterized and fine-grained complexity

- **TFNP:** CLS, further local search, fixed-point and equilibrium problems.
- **Potential-line classes** ([#3206](https://github.com/cslib-community/complexitylib/issues/3206)): `PPADS`, `EOPL`, `SOPL` and `UEOPL` with their easy inclusions, `EOPL = SOPL ∩ PPAD` (Göös et al. 2022, Lemma 4), and `PLS ∩ PPADS ⊆ SOPL` (Lemmas 2–3), giving `SOPL = PLS ∩ PPADS` and `EOPL = PLS ∩ PPAD`.
- **Sperner's lemma** ([#2999](https://github.com/cslib-community/complexitylib/issues/2999)): the parity form on the triangulated square grid by door-following, with circuit `Sperner2D` in `PPAD` as the end-of-line relation of its door graph.
  Its hardness and higher-dimensional forms ([#3087](https://github.com/cslib-community/complexitylib/issues/3087)): `PPAD`-hardness of two-dimensional Sperner and Brouwer (Chen–Deng), `PPAD`-completeness of three-dimensional Sperner (Papadimitriou 1994), and the `d`-dimensional simplex form with general Sperner boundary conditions.
- **Parameterized:** strongly uniform variants (computable `f`), further explicit polynomial kernels, the W and A hierarchies, and parameterized lower bounds; connect these to [structural graph algorithms](#structural-graph-algorithms) and their decomposition costs.
- **Color coding** ([#2870](https://github.com/cslib-community/complexitylib/issues/2870)): the one-sided-error randomized fpt algorithm for `LongPath`, by dynamic programming over color sets for colorful k-paths and random colorings (a fixed `k`-set is colorful with probability `K.descFactorial k / K ^ k ≥ e ^ (-k)`), and its derandomization by perfect hash families.
- **W-hierarchy** ([#2966](https://github.com/cslib-community/complexitylib/issues/2966)): `W[t]` by fpt-reduction to weighted satisfiability of bounded-depth circuits of weft at most `t`, with `FPT ⊆ W[t] ⊆ W[t+1]` and `W[t] ⊆ XP`.
  It covers `IndependentSet` and `Clique` in `W[1]`, the W[1]-hardness of `Clique` by fpt-reduction from weighted circuit satisfiability, W[2]-completeness of Dominating Set, short Turing machine acceptance, `W[P]` and the A-hierarchy.
- **Exponential-time SAT** ([#894](https://github.com/cslib-community/complexitylib/issues/894)): Schöning, PPZ and PPSZ on the randomized word RAM with exact laws, amplification and time bounds, and a curated abstract for Schöning.
  PPZ and PPSZ abstracts and the uniform `o(n)` forms of the PPSZ bounds, with `w` growing in `n`, are optional.
  Also further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.
- **APSP class** ([#3076](https://github.com/cslib-community/complexitylib/issues/3076)): equivalences of APSP with the (min,+) product, negative triangle, minimum-weight cycle, replacement paths, metricity and (min,+) product verification (Vassilevska Williams–Williams), and with radius and median (Abboud–Grandoni–Vassilevska Williams, SODA 2015).
  Also word-RAM realizations with bit-length costs and Kerr's `Ω(n³)` bound for (min,+) straight-line programs; Bellman–Ford with negative-cycle reporting is [#3053](https://github.com/cslib-community/complexitylib/issues/3053).
- **Reductions from orthogonal vectors** ([#3037](https://github.com/cslib-community/complexitylib/issues/3037)): `OV` hardness of diameter two versus three (Roditty–Vassilevska Williams Theorem 9), its `(3/2 - ε)`-approximation corollary, and the sparse `m ^ (2 - ε)` bound from low-dimension `OVH` (dimension `c log N`, implied by `SETH` via sparsification).
  Quadratic dynamic programs for LCS and edit distance with `OV` hardness by alignment gadgets (Backurs–Indyk; Abboud–Backurs–Vassilevska Williams; Bringmann–Künnemann).

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886](https://github.com/cslib-community/complexitylib/issues/886)): for `0 < ε < 1/8`, NP-hardness of distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most `7/8 + ε` of the clauses.
  The route: parallel repetition with small-soundness Label Cover, the long-code 3-bit test for MAX-E3LIN hardness (Theorem 5.4), the four-clause reduction (Theorem 6.1, imperfect completeness), and the test for satisfiable formulas (Theorem 6.5).
- **FGLSS clique hardness:** the FGLSS clique-hardness reduction and its amplification, retaining the exact gap and reduction runtime.
- **Approximation classes and gap reductions:** gap and approximation-preserving reductions, APX/PTAS/FPTAS, inapproximability consequences of PCP, CSP classifications and relaxation gaps, with assumptions such as the Unique Games Conjecture stated explicitly.
  The 2-to-2 games theorem waits for [#886](https://github.com/cslib-community/complexitylib/issues/886).
- **Approximation algorithms:** a general interface for approximation ratios of optimization problems, under which polynomial-time algorithms such as Johnson's `7 / 8` algorithm for MAX-E3SAT meet matching hardness results such as Håstad's ([#886](https://github.com/cslib-community/complexitylib/issues/886)); LP and SDP rounding, such as Goemans–Williamson for MAX-CUT and MAX-SAT.
  Goemans–Williamson ([#3230](https://github.com/cslib-community/complexitylib/issues/3230)) needs polynomial-time SDP solving with precision accounting, a `ProbComp` realization of the Gaussian sample, the Feige–Schechtman tightness gap, the MAX-2SAT and MAX-DICUT extensions, and derandomization.
- **Packing approximation** ([#2964](https://github.com/cslib-community/complexitylib/issues/2964)): the asymptotic approximation scheme for bin packing of Fernandez de la Vega and Lueker, First Fit's `17/10` bound, First Fit Decreasing's `11/9` bound and Lawler's faster knapsack FPTAS, building on the knapsack FPTAS, Next Fit, First Fit and the `3/2` bin-packing hardness.
- **Scheduling** ([#2909](https://github.com/cslib-community/complexitylib/issues/2909)): Graham's list-scheduling, LPT and precedence bounds, extended to real-valued processing times with precedences; Graham's anomaly instances as checked examples, a general tight family for LPT, the Hochbaum–Shmoys PTAS for `P || C_max`, and runtime bounds for `listSchedule` and `lptSchedule`.
- **A practical PCP construction:** a reasonably runnable construction and its cost on complete reductions; rotation certificates polynomial in the bit length of a vertex name; machine-level error reduction and extractors from expander walks, with certified seed and evaluation costs.

### Proof complexity

- **Proof space** ([#3200](https://github.com/cslib-community/complexitylib/issues/3200)): clause, total and variable space for resolution, with the Atserias–Dalmau inequality, linear clause space for Tseitin formulas on expanders, tree-like space bounds (Esteban–Torán, [#3229](https://github.com/cslib-community/complexitylib/issues/3229)), and space lower bounds for the wide pigeonhole formula and random `k`-CNFs ([#3321](https://github.com/cslib-community/complexitylib/issues/3321)).
  Also Atserias–Dalmau Lemma 2 as a public `DuplicatorStrategy`.
  Also time–space trade-offs for pebbling formulas and degree versus space in polynomial calculus.
- **Polynomial calculus, sum-of-squares and DPLL:** polynomial calculus and sum-of-squares, and certified DPLL solver runtimes.
- **Frege** ([#3069](https://github.com/cslib-community/complexitylib/issues/3069)): implicational completeness of the Hilbert-style system (Kalmár); formula-size measures; the simulation of resolution as a p-simulation of Cook–Reckhow proof systems, with encodings and translation time; the mutual p-simulation of Frege systems; and Extended Frege.
- **Cutting planes:** the bounded-coefficient clique–colouring bound via Krajíček's feasible interpolation (Corollary 7.3, [#2019](https://github.com/cslib-community/complexitylib/issues/2019)), and monotone interpolation for shared variables with only nonpositive coefficients in `Γ_B`.
  Pudlák's unrestricted-coefficient lower bound via monotone real circuits, coefficient-size measures, Buss–Clote cutting planes with division by 2 only, and the p-simulation of resolution, with encodings and translation time.
- **Feasible interpolation** ([#1817](https://github.com/cslib-community/complexitylib/issues/1817)): further clients of Krajíček's interpolation theorem for semantic derivations ([#2019](https://github.com/cslib-community/complexitylib/issues/2019)), namely resolution through Theorem 6.1, the linear equational calculus, and the monotone case for the `ℬ` side.
  The cutting-planes work is under **Cutting planes**.
- **Proof search:** automatizability and weak automatizability with explicit encodings and runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.

## Circuits and algebraic complexity

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889](https://github.com/cslib-community/complexitylib/issues/889)): some language in NEXP, then NQP, has no polynomial-size `ACC⁰` circuits (AND, OR, NOT and `MOD_m` gates).
  This needs the Yao–Beigel–Tarui conversion to `SYM ∘ AND` circuits, computed in quasi-polynomial time, Williams's evaluation lemma ([#3023](https://github.com/cslib-community/complexitylib/issues/3023)) on a Turing machine or word RAM, an ACC-SAT algorithm, a fine nondeterministic time hierarchy, and the `E^NP` and NEXP lower bounds.
- **Circuit lower bounds from refuting ETH** ([#1539](https://github.com/cslib-community/complexitylib/issues/1539)): `E^NP ⊄ SIZE(O(n))`, and a language in `E^NP` whose fan-in-two circuits need more than `c n √log n` gates infinitely often, by Williams's witness-circuit argument with #CircuitSAT counters.
  It requires connecting the exponential nondeterministic time hierarchy to framed witness preparation, building the linear-size decoder and checker uniformly, and completing the nondeterministic simulation.
- **Circuit classes, bridges and barriers**: uniform and nonuniform NC, AC and TC, circuit-to-machine bridges, algorithm-to-lower-bound arguments, and barriers such as natural proofs and algebrization.
  NC simulation of unrestricted `TCⁱ` needs Muroga's threshold weight-bounding theorem.
- **Formula and monotone depth lower bounds**: formula lower bounds beyond Andreev's, following Jukna, and Raz–Wigderson's monotone depth bound for matching on general graphs.
- **Monotone circuits versus P** ([#2063](https://github.com/cslib-community/complexitylib/issues/2063), [#3147](https://github.com/cslib-community/complexitylib/issues/3147)): a monotone language in P whose monotone circuit complexity is superpolynomial, from Razborov's `n ^ Ω(log n)` monotone bound for bipartite perfect matching, and the exponential gap of É. Tardos (1988).
- **An explicit frontier extractor**: port v1's sumset-extractor construction with an explicit family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses.
  Because it would exceed the library's unconditional `3.5 N - o(N)` bound in P, it needs an independent correctness review of the frontier core.
- **Weighted threshold representations**: v1's explicit source-reduction family, universal scalar circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting.
- **Depth-two threshold circuits for Andreev's function** ([#2347](https://github.com/cslib-community/complexitylib/issues/2347)): upper bounds and average-case gate and wire lower bounds for depth-two weighted threshold circuits computing Andreev's function, following Kane–Williams (arXiv:1511.07860v1).
  Majority votes of depth-two circuits and the other Kane–Williams follow-ups are in [#2812](https://github.com/cslib-community/complexitylib/issues/2812); closing the worst-case gate gap between `Ω̃(n ^ (3 / 2))` and `O(n ^ 2)` is open.
- **Construction runtimes**: certified separately from gate counts, for the mass-production constructors with constructive choices of information sets and line menus, the iterated-function preprocessing, and the bit complexity of formula evaluation on the rational hitting-list matrices.
- **Algebraic complexity** ([#891](https://github.com/cslib-community/complexitylib/issues/891)): Limaye–Srinivasan–Tavenas superpolynomial lower bounds for constant-depth circuits computing iterated matrix multiplication over any field, including their semantic set-multilinear model, growing product-depth `Δ` with exponent `d ^ exp(-O(Δ))`, the `√d` bound at `Δ = 1` (LST Lemma 13 and Corollary 4), the full range of `d`, and the `0/1`-substitution remark.
- **Identity testing and hitting sets** ([#891](https://github.com/cslib-community/complexitylib/issues/891)): polynomial identity testing and hitting sets for arithmetic circuits.
  Also the Kabanets–Impagliazzo theorem: a deterministic PIT algorithm implies NEXP ⊄ P/poly or the permanent has no polynomial-size arithmetic circuits.
- **VNP-completeness of the permanent** ([#321](https://github.com/cslib-community/complexitylib/issues/321)): Valiant's theorem that the permanent is VNP-complete over fields of characteristic other than two.
  Membership goes through Ryser's formula, and hardness through formulas for VP witnesses, projection of arithmetic formulas to the permanent, and elimination of Boolean sums with one- and two-entry selector gadgets.
- **Arithmetic formulas and branching programs** ([#3198](https://github.com/cslib-community/complexitylib/issues/3198)): formula and algebraic branching-program models, including Nisan's exact size formula for homogeneous layered non-commutative ABPs, the `n^m` palindrome bound and the separation from non-commutative circuits, the reduction from general non-commutative ABPs, non-commutative formula lower bounds for the determinant and permanent, and ROABPs.
- **Tensor, rank and partial-derivative methods**: arithmetic lower bounds by tensor and rank methods and partial-derivative measures: the order-`k` measure with bounded-product-fan-in depth-three determinant and permanent bounds, Nisan–Wigderson's all-orders measure with their elementary symmetric polynomial and iterated matrix multiplication bounds, and shifted partial derivatives.
- **Depth-reduction chasms**: depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform construction costs certified separately from gate counts.
- **Strassen's degree bound**: Bézout's inequality and the `n log d` multiplication lower bound for the power map.
  With the Baur–Strassen transfer ([#2906](https://github.com/cslib-community/complexitylib/issues/2906)) this gives the `Ω(n log d)` bound for the single power sum `∑ xᵢ^(d+1)`.
- **Matrix inversion from the determinant**: inversion through the adjugate circuits of [`Arithmetic/Adjugate`](Complexity/Computability/Circuit/Arithmetic/Adjugate.lean), in a circuit model with division.
- **The matrix multiplication exponent**: the bound `ω ≤ 9/4` over every field, by exact bilinear algorithms, degenerations and block recursion, following Pass's constructive proof (arXiv:2610.28627v2) of OpenAI's bound.
  Also the rectangular and dual exponents, explicit sizes and constants, and the lower bound `ω ≥ 2` from the output count.
- **Fast integer and polynomial multiplication** ([#2923](https://github.com/cslib-community/complexitylib/issues/2923)): Karatsuba for polynomials in the arithmetic query model and for integers as Boolean circuits, with `O(n ^ log₂ 3)` bounds, smaller constants, logarithmic or polylogarithmic depth, uniform generation, and a native or word-RAM realization.
  Also Toom–Cook (`O(n ^ log₃ 5)` for Toom-3) and lower bounds such as rank `3` for the two-term product tensor.
- **Fast Fourier transform and FFT multiplication** ([#2979](https://github.com/cslib-community/complexitylib/issues/2979)): radix-2, mixed-radix and Bluestein FFTs and `O(n log n)` polynomial multiplication over commutative rings with suitable principal roots of unity, for every length and as arithmetic circuits of size `O(n log n)` and depth `O(log n)`.
  Without such roots, Schönhage–Strassen over `R[x] / (x ^ m + 1)` with the `O(n log n log log n)` integer bound; and lower bounds such as Morgenstern's `Ω(n log n)` for bounded-coefficient linear circuits.
- **Matrix rigidity and linear circuits** ([#3209](https://github.com/cslib-community/complexitylib/issues/3209)): Valiant's criterion for linear circuits, also for nonlinear gates over finite fields; rigidity of Cauchy and totally regular matrices, Shparlinsky's Vandermonde and Sylvester–Hadamard bounds, `R(r) ≤ (n - r)²`, near-maximally rigid random matrices over finite fields, and Alman–Williams non-rigidity of Walsh–Hadamard.
  An explicit `(εn, n ^ (1 + δ))`-rigid matrix is Valiant's open problem.
- **Real-algebraic decision procedures**: port the Sturm–Tarski query evaluator, recursive evaluator, implicit arithmetic, native space certificates and the ETR upper bound from [lean-canny](https://github.com/SamuelSchlesinger/lean-canny).

### Jukna coverage

Formalize the established results, constructions and worthwhile exercises of [Jukna's *Boolean Function Complexity* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html), with the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html), auditing each statement against the numbered result.
Organize modules by subject, not chapter.

| Chapters | Next coverage work |
| --- | --- |
| 1–2: foundations and Boolean analysis | Counting, graph complexity, degree and approximation results; the partial-function circuit upper bounds that use Lemma 1.17. |
| 3–5: communication | Matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | Formula and monotone bounds; span programs and negation complexity. |
| 11–13: depth restrictions and general gates | Depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | Bounded-read and bounded-time lower bounds and tree results. |
| 18–19: proof complexity | Proof-space and cutting-plane lower bounds. |
| 20: barriers and further methods | The book's generator, natural-proof, fusion and indirect lower-bound results. |

## Pseudorandomness, coding and Boolean analysis

- **Derandomization from hardness**: the infinitely-often variant, and the EXP ⊄ P/poly endpoint of Babai, Fortnow, Nisan and Wigderson.
- **Extractors** ([#895](https://github.com/cslib-community/complexitylib/issues/895)): beyond Chor–Goldreich, two-source extractors for lower min-entropy through Chattopadhyay–Zuckerman's Theorem 4.1, resilient functions (Theorems 3 and 4) and extractor (Theorem 1); condensers, limited independence, explicit expanders and space-bounded generators.
  Finite guarantees stay separate from uniform construction and decoding costs.
- **Explicit Ramsey graphs** ([#3041](https://github.com/cslib-community/complexitylib/issues/3041)): strongly explicit graphs with no `k`-clique or `k`-independent set on more than Nagy's `C(k - 1, 3)` vertices, toward Erdős's existential `2 ^ (k / 2)`: Frankl–Wilson's `k ^ Θ(log k / log log k)`, then the constructions of Cohen, Chattopadhyay–Zuckerman and Li.
  Keep these bounds separate from polynomial-time recognition and adjacency certificates.
  An explicit graph on `2 ^ Ω(k)` vertices is open.
- **Codes**: Guruswami–Sudan list decoding and local decoding, keeping interpolation, list-size/agreement guarantees and decoding runtime as separate obligations; concrete list-decodable codes for Nisan–Wigderson.
- **Expander codes** ([#3278](https://github.com/cslib-community/complexitylib/issues/3278)): Sipser–Spielman codes of bipartite vertex expanders with rate, distance and flip decoding; lossless expanders, probabilistic or explicit (Capalbo–Reingold–Vadhan–Wigderson), making expander codes asymptotically good; a machine-model linear-time decoder; Spielman's linear-time encodable codes; and Zémor's decoding of Tanner codes on spectral expanders.
- **Locally decodable codes** ([#2929](https://github.com/cslib-community/complexitylib/issues/2929)): query-bounded decoders, the Hadamard code, and lower bounds through Katz–Trevisan smoothing for every adaptive decoder and the matching/XOR normal form: the one-query bound, the Katz–Trevisan bound `n ≥ Ω(k^{q/(q-1)})` with explicit `(δ, ε, q)` dependence, and the Goldreich–Karloff–Schulman–Trevisan and Kerenidis–de Wolf exponential bounds for two-query codes.
- **Boolean analysis** ([#2131](https://github.com/cslib-community/complexitylib/issues/2131)): coverage of O'Donnell's *Analysis of Boolean Functions*, including the book-form statements of its Chapter 9 (the KKL edge-isoperimetric theorem, and Friedgut's junta theorem with its spectral concentration).
  Also hypercontractivity beyond `p ≤ 2 ≤ q` and its applications, such as small-set expansion and the Level-k inequalities.
- **Resource-bounded measure and dimension** ([#3139](https://github.com/cslib-community/complexitylib/issues/3139)): Lutz's p-measure in `E` with the quantitative Measure Conservation bound and countable p-unions (Lutz's Lemma 3.10(c)), measure in `EXP` (`p₂`), p-randomness, gales and resource-bounded dimension.
  State the budgets and uniformity of betting strategies separately from measure-theoretic facts, and connect quantitative randomness to Kolmogorov complexity.

## Communication, queries, learning and other models

- **Lifting** ([#890](https://github.com/cslib-community/complexitylib/issues/890)): applications of deterministic lifting, such as partition-number separations, and randomized lifting.
- **Randomized query complexity of game trees** ([#3060](https://github.com/cslib-community/complexitylib/issues/3060)): for the AND–OR (NAND) tree on `n = 4 ^ k` leaves, Snir's `R₀ = O(n ^ (log₂ α))`, `α = (1 + √33) / 4`, and the matching Saks–Wigderson lower bound via Yao's principle for expected cost.
  Also bounded-error bounds for the same trees, and Saks–Wigderson's results for general read-once formulas and MIN/MAX game trees over integer leaves.
- **Number-on-forehead multiparty protocols** ([#3197](https://github.com/cslib-community/complexitylib/issues/3197)): cylinder intersections and discrepancy, the Chung–Raz cube bound, Babai–Nisan–Szegedy's `Ω(n / 4 ^ k)` and a sharper `Ω(n / 2 ^ k)` (source unverified) for generalized inner product, Grolmusz's protocol, Raz's matrix multiplication and NOF disjointness bounds, and `ACC⁰` and branching-program applications.
  A two-party companion is the Aho–Ullman–Yannakakis bound `D(f) = O(N⁰(f) N¹(f))`.
- **Number-in-hand and information complexity**: multiparty number-in-hand protocols, information complexity, direct-sum and direct-product results, and reductions to streaming, sketching and cell-probe lower bounds.
- **Dynamic cell-probe lower bounds** ([#3207](https://github.com/cslib-community/complexitylib/issues/3207)): by the chronogram method, the Fredman–Saks bound `t_q = Ω(log n / log(t_u (w + 1)))` for dynamic prefix parity with deterministic worst-case update depth `t_u` and `S ≤ 2 ^ w` cells, then amortized updates and Las Vegas randomization through cell-probe Yao averaging.
  Also Pătraşcu–Demaine's trade-off `t_q lg(t_u / t_q) = Ω(lg n)` and reductions to dynamic connectivity.
- **Streaming and sketching**: native time and space bounds for Count-Min with hash-seed storage and evaluation; the AMS sketch for `F₀`, the AMS `F_k` estimator for streams of unknown length, and the `n^{Ω(1)}` lower bounds for `F_k` with `k ≥ 6`; `ProbComp` samplers and native realizations of the AMS sketches.
  Also CountSketch, turnstile updates, heavy-hitter recovery, and multi-pass communication-to-streaming transfers with pass counts.
- **Learning**: machine-certified running times for the LMN and Kushilevitz–Mansour learners; distributional problems and reductions, samplability, average-to-worst-case connections, PAC/agnostic learning, learning lower bounds, compression and refutation.
  Develop low-degree likelihood-ratio and sum-of-squares comparisons where justified, distinguishing restricted-model bounds from unrestricted hardness.
  Use the [distributional framework](#average-case-complexity).
- **Realizable PAC learning** ([#2868](https://github.com/cslib-community/complexitylib/issues/2868)): the VC ε-net upper bound `O((d log (1/ε) + log (1/δ))/ε)` for general well-behaved classes over measurable domains, beyond countable domains.
- **Agnostic learning of infinite classes** ([#3005](https://github.com/cslib-community/complexitylib/issues/3005)): uniform convergence from the growth function by symmetrization, then agnostic learnability of finite VC classes, first on countable domains, then at the sharp `O((d + log (1/δ))/ε²)` rate.
- **Statistical query learning** ([#2910](https://github.com/cslib-community/complexitylib/issues/2910)): the SQ model and its lower bounds, simulation from random examples, including under random classification noise of known and unknown rate (Kearns's Lemma 2 and Theorem 3), the single-sample form of Kearns's Theorem 1 and a distribution-free variant, and randomized SQ learners.
- **Statistical query dimensions** ([#2910](https://github.com/cslib-community/complexitylib/issues/2910)): the characterization of weak learning by SQ dimension ([#3204](https://github.com/cslib-community/complexitylib/issues/3204)), the Bshouty–Feldman transfer to correlational queries, the worst-case SQ dimension versus VC dimension (Reyzin's Observations 20 and 21), Feldman's strong SQ dimension, and his statistical dimension for a planted problem with matching sample and runtime upper bounds.
- **Online learning in the mistake-bound model** ([#2908](https://github.com/cslib-community/complexitylib/issues/2908)): the Littlestone dimension as the optimal mistake bound, WINNOW2 and attribute transformations (Littlestone 1988, Theorems 9 and 10), and optimal `Θ(√(Ldim(C) T))` agnostic regret ([#3120](https://github.com/cslib-community/complexitylib/issues/3120)) under adaptive adversaries and unknown horizons.
  Also multiclass and real-valued analogues, online-to-batch conversion into PAC learning, and running-time bounds for the standard optimal algorithm.
- **Testing Boolean functions**: independent repetition of local tests and BLR linearity testing with explicit decision-tree query bounds, and further query lower bounds.
- **Distribution testing** ([#2930](https://github.com/cslib-community/complexitylib/issues/2930), [#3017](https://github.com/cslib-community/complexitylib/issues/3017), [#3122](https://github.com/cslib-community/complexitylib/issues/3122)): uniformity testing with matching `Θ(√n / ε²)` sample bounds on every domain for `ε ≤ 1/2`, identity testing by reduction to uniformity, and closeness testing with matching `Θ(n^{2/3} ε^{-4/3} + √n ε^{-2})` bounds.
  Also instance-optimal identity testing, tolerant and structured-property testing, further access models, and sample lower bounds.
- **Dense graph property testing** ([#3036](https://github.com/cslib-community/complexitylib/issues/3036), [#3180](https://github.com/cslib-community/complexitylib/issues/3180), [#3118](https://github.com/cslib-community/complexitylib/issues/3118)): `H`-freeness through removal lemmas, bipartiteness (Goldreich–Goldwasser–Ron, then sharper bounds) and `k`-colourability with `poly(1/ε)` queries, and Goldreich–Trevisan canonical testers with `O(q)` sample vertices and `O(q²)` queries.
  Testers should decide by the property itself when it is closed under induced subgraphs (Proposition D.2, due to Alon) or is a graph partition property (Corollary 5.9).
- **Kolmogorov complexity and metacomplexity** ([#798](https://github.com/cslib-community/complexitylib/issues/798), [#884](https://github.com/cslib-community/complexitylib/issues/884)): Liu–Pass Theorem 3.1 (c) in the near-linear regime, hardness for every polynomial `t(n) ≥ (1 + ε)n`, which needs a rate-1 efficient conditional EP-PRG running in `n + O(n^c)` multi-tape steps for a constant `c < 1`.
  Also prefix-free complexity, and resource-bounded MCSP variants with their connections to learning, cryptography and lower bounds.
- **Further metacomplexity developments** ([#798](https://github.com/cslib-community/complexitylib/issues/798)): the circuitized anti-checker with an efficient generator; the asymptotic parameter instantiation of Theorem 5 as a concrete rounded-threshold, ternary-device statement; and hardness of `MINKT` and `MINcKT`, as independently scoped developments.
  Also the reverse multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding.
- **Quantum computation** ([#896](https://github.com/cslib-community/complexitylib/issues/896)): channel semantics and approximation costs alongside circuit and measurement semantics, reusing suitable quantum foundations rather than incompatible models; a query-to-circuit bridge; complete problems for BQP; related query, communication and interactive classes with amplification, containments and complete problems.
  Supply the [quantum adversary models](#concurrent-and-quantum-security) needed by cryptographic reductions.
- **QMA** ([#2876](https://github.com/cslib-community/complexitylib/issues/2876)): error reduction from an inverse-polynomial gap, strong error reduction that keeps the witness length, `QMA ⊆ A₀PP`, mixed witnesses, QCMA and the local Hamiltonian problem.
- **Quantum query separations** ([#2991](https://github.com/cslib-community/complexitylib/issues/2991)): Simon's problem in decision and search versions, with polynomial-time post-processing by Gaussian elimination over `ZMod 2`, separations in the value-query model, and then Forrelation and other optimal quantum–classical query separations.
  The value-query model needs quantum states over an arbitrary finite query index type rather than `Fin N`.
- **Promise problems in quantum query complexity** ([#3310](https://github.com/cslib-community/complexitylib/issues/3310)): Deutsch–Jozsa's exact one-query algorithm against the deterministic `N/2 + 1` and constant-query randomized bounds; exact quantum lower bounds for promise problems via polynomial degree (`Q_E ≥ deg/2` on the promise domain); a promise form of `randomizedComplexity`; and recursive Fourier sampling (Bernstein–Vazirani).
- **Quantum query lower bounds** ([#3239](https://github.com/cslib-community/complexitylib/issues/3239)): Ambainis's relational adversary (Theorems 2, 5 and 6 of the source), the Nayak–Wu promise-threshold bound with its approximate-median, approximate-count and `k`th-smallest consequences, and the weighted, spectral and negative-weight (general) adversaries for arbitrary relations.
  Non-Boolean input alphabets (permutation inversion, Theorem 7) need the value-query model above.
- **Shor's algorithm** ([#3252](https://github.com/cslib-community/complexitylib/issues/3252)): bounded-error polynomial-time integer factoring and discrete logarithms in the native uniform quantum-circuit model, with explicit encodings, success probabilities and gate-approximation costs.
  It needs the quantum Fourier transform with its circuits, period finding including `r ∤ N` by continued fractions and the `Ω(1 / log log r)` totient bound, phase estimation, reversible modular exponentiation and the classical reductions, certifying uniform generation and polynomial gate bounds.

### Differential privacy and adaptive data analysis

- **Differential privacy foundations** ([#2867](https://github.com/cslib-community/complexitylib/issues/2867)): dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with postprocessing and adaptive composition, including advanced composition ([#2977](https://github.com/cslib-community/complexitylib/issues/2977)).
  Mechanisms need both privacy and utility proofs with sampling cost and finite-precision error, covering exact sampling of discrete noise and continuous Laplace and Gaussian mechanisms.
  Also Rényi or concentrated privacy accounting.
- **Private query answering and learning** ([#2977](https://github.com/cslib-community/complexitylib/issues/2977)): private query answering and private learning, building on the exponential mechanism and the sparse vector technique; privacy–accuracy and sample-complexity lower bounds; then adaptive data-analysis and generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources explicit, reusing the probability, oracle-computation and learning APIs.
- **Privacy–accuracy lower bounds** ([#3178](https://github.com/cslib-community/complexitylib/issues/3178), [#3201](https://github.com/cslib-community/complexitylib/issues/3201)): the lower bounds of Dwork–Roth Chapter 8: the packing lemma, the `Ω(k / ε)` bound for one-way marginals, Dinur–Nissim reconstruction, reconstruction from `O(n)` random `±1` queries with `o(√n)` error (Theorem 8.2), and De's `Ω(min(k, d) / ε)` bound over a small universe (Theorem 8.8).
  Also `(ε, δ)` lower bounds via fingerprinting codes.

## Algorithms and optimization

### Optimization and duality

- **Linear programming** ([#2976](https://github.com/cslib-community/complexitylib/issues/2976)): Fourier–Motzkin, Farkas' lemma and LP duality over linearly ordered fields; rational input and output encodings with bit-size bounds on basic solutions and Farkas certificates (Cramer's rule, Hadamard bound), giving LP feasibility in NP ∩ coNP with machine-checked certificate verifiers.
  Then a polynomial-time LP algorithm (ellipsoid or interior point) accounting for bit complexity and intermediate precision.
- **Separation and optimization:** a precise oracle interface and a separation–optimization equivalence with its representation, accuracy and well-boundedness hypotheses.
  Extend to convex optimization through explicit oracle and numerical-error contracts.
- **Primal–dual approximation and multiplicative weights:** reusable primal–dual analyses with vertex cover and set cover as first clients, and multiplicative weights building on the experts regret bounds of [#2874](https://github.com/cslib-community/complexitylib/issues/2874).
  Targets include randomized weighted majority and sampled Hedge as probabilistic computations, the regret lower bound, charged finite-precision implementations, and applications to packing and covering LPs, boosting and learning.
- **Online convex optimization:** regret bounds from projected online gradient descent ([#2983](https://github.com/cslib-community/complexitylib/issues/2983)) to follow-the-regularized-leader and online mirror descent (recovering Hedge as the entropic case), the `Ω(GD√T)` lower bound, online Newton step for exp-concave losses, and Blackwell approachability and calibration.
  Finite-precision implementations are part of the direction.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations), reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** native augmenting-path algorithms with charged runtime, then weighted bipartite matching (including rectangular and sparse instances) and minimum-cost flow through common residual-network and duality machinery.
  Matching also covers the decomposition of `M ⊕ M*` into vertex-disjoint augmenting paths, weighted and unweighted general matching with blossoms, and a sparse Hopcroft–Karp entry point whose cost includes building the adjacency lists.
- **Algebraic matching** ([#3052](https://github.com/cslib-community/complexitylib/issues/3052)): Edmonds' and Tutte's determinant criteria with Lovász's randomized test, and the Mulmuley–Vazirani–Vazirani algorithm for bipartite and general graphs (the latter in its Pfaffian form).
  The algorithmic targets are a machine-level running-time certificate for the determinant test and an RNC implementation.
- **Graph search and shortest paths** ([#3053](https://github.com/cslib-community/complexitylib/issues/3053)): `TimeM` depth-first search, topological sort and Bellman–Ford with its predecessor tree, and linear-time strongly connected components with the linear-time 2-SAT algorithm as a client of the `TwoSAT` problem module.
  Bridge Bellman–Ford to Dijkstra's distances and to the matrix shortest-path model.
- **Matroids** ([#2018](https://github.com/cslib-community/complexitylib/issues/2018)): Edmonds' matroid intersection theorem with an exchange-graph augmenting-path solver, König's theorem via partition matroids, exact independence-oracle query counts, and `TimeM` costs for the solver's host computation kept separate from those counts.
  Extend to weighted matroid intersection.
- **Submodular optimization:** constraints and approximation bounds beyond the cardinality-constrained `1 - 1/e` greedy, charging value-oracle calls separately from their concrete realizations.
- **Stable matching** ([#2990](https://github.com/cslib-community/complexitylib/issues/2990)): deferred acceptance and its theory (stability, optimality, the lattice, strategy-proofness), extended to Roth's impossibility theorem for every `n ≥ 3`, incomplete lists and the rural hospitals theorem, many-to-one college admissions, ties, rotations and the stable-matching poset, and stable roommates.
  A charged native implementation should run in `O(n^2)` time.
- **Housing markets and top trading cycles** ([#3286](https://github.com/cslib-community/complexitylib/issues/3286)): the Shapley–Scarf model with TTC as the unique strict-core and competitive allocation, individually rational, Pareto efficient and strategy-proof; house allocation with existing tenants (Abdulkadiroğlu–Sönmez), Ma's characterization of TTC, group strategy-proofness, indifferences (top trading absorbing sets), and a charged `O(n^2)` TTC.
- **Classical approximation algorithms** ([#2869](https://github.com/cslib-community/complexitylib/issues/2869)): greedy set cover, maximal-matching vertex cover and the MST tour for metric TSP, with machine-level polynomial-time certificates for greedy set cover and for Kruskal-based TSP tours on encoded matrices, and Christofides' `3/2` for metric TSP ([#3055](https://github.com/cslib-community/complexitylib/issues/3055)) with a polynomial-time minimum-weight perfect matching (Edmonds' blossom) and a tightness family approaching `3/2`.
  Karlin–Klein–Oveis Gharan's `3/2 - 10^{-36}` is a long-range target.
  LP-based and primal–dual analyses belong to the primal–dual direction.

### Online algorithms and competitive analysis

- **Competitive-analysis framework:** request sequences, online strategies, offline optima and competitive ratios with additive constants, distinguishing deterministic and randomized strategies and oblivious and adaptive adversaries.
  Compare algorithms in the same action and cost model, including initialization.
- **Adaptive search trees:** working-set and dynamic-finger bounds for splay trees, and a BST access-and-rotation model with Wilber-style lower bounds.
  State dynamic optimality as a conjectural research target with explicit strategy and sequence quantifiers.
- **Beyond deterministic ski rental and list update** ([#3057](https://github.com/cslib-community/complexitylib/issues/3057)): the randomized `e/(e-1)` ski-rental bound against an oblivious adversary, randomized list update (BIT, COMB), list update with insertions and deletions, and the `k`-server problem, starting with Double Coverage on the line and on trees.
- **Optimal stopping:** from the rank-based secretary problem, the `½` prophet inequality ([#2913](https://github.com/cslib-community/complexitylib/issues/2913)) and the i.i.d. `1 - 1/e` bound ([#3092](https://github.com/cslib-community/complexitylib/issues/3092)) to the tight i.i.d. constant `≈0.745`, prophet secretary and random-order models, and matroid and multiple-choice prophet inequalities.
  Also the full-information secretary problem, a general mixtures theorem for randomized rules, and the posted-price mechanism corollary.

### Algorithmic game theory ([#2900](https://github.com/cslib-community/complexitylib/issues/2900))

- **Computing equilibria:** PLS-completeness of finding a pure Nash equilibrium of a congestion game (Fabrikant–Papadimitriou–Talwar) through an explicit local-search problem interface and succinct game encodings; polynomial-time algorithms for symmetric network congestion games; exponentially long better-response paths.
  Mixed Nash equilibria of finite games (Nash's theorem) and PPAD-completeness of computing them.
- **Equilibrium concepts and dynamics:** mixed and correlated equilibria between pure Nash and coarse correlated equilibria; swap regret and convergence to correlated equilibria, extending the Hedge dynamics of [#3034](https://github.com/cslib-community/complexitylib/issues/3034); last-iterate convergence of no-regret dynamics; bandit feedback and sampled play; convergence time of better-response dynamics in potential games.
- **Price of anarchy:** Wardrop equilibrium existence and essential uniqueness for continuous nondecreasing latencies (Beckmann's convex potential); the Pigou bound for general latency classes and polynomial latencies of bounded degree; Braess's paradox; weighted and mixed-strategy atomic congestion games.
- **Price of stability and potential games** ([#3035](https://github.com/cslib-community/complexitylib/issues/3035)): the price of stability by the potential method, including the `H_k` bound for network cost-sharing games, and the Monderer–Shapley characterization of potential games as congestion games.

### Mechanism design ([#2947](https://github.com/cslib-community/complexitylib/issues/2947))

The directions below extend the single-parameter, Groves/VCG, optimal-auction and Bayes–Nash foundations in `GameTheory/Mechanism`, including revenue equivalence and the first-price equilibrium for i.i.d. uniform values ([#3173](https://github.com/cslib-community/complexitylib/issues/3173)).

- **Single-parameter corollaries:** the sponsored-search payment formula (rank-by-bid allocation with slot click-through rates) and the greedy knapsack rule with its monotonicity and ½-approximation.
  State allocation algorithms with charged running time, so that approximation and truthfulness are both proved for an actual algorithm.
- **Revenue maximization beyond the regular DSIC case:** ironing for irregular distributions; regular distributions whose virtual valuation is unbounded below at `0`, like `f(v) = 2v` on `[0, 1]`, with explicit zero-bid treatment.
  Optimality over Bayesian incentive-compatible mechanisms (revelation principle), measurable virtual-welfare maximizers for finite feasible sets, and distributions without a bounded density (atoms, unbounded support).
- **Bayes–Nash equilibria of auctions:** the symmetric first-price equilibrium `b(v) = E[max of the other values | it is below v]` for general i.i.d. priors with densities and its uniqueness (Hartline, *Mechanism Design and Approximation*, §2.8–2.9); the all-pay auction; truthful bidding as a Bayes–Nash equilibrium of every DSIC mechanism.
  The exact optimal revenue `(n - 1 + 2^(-n)) / (n + 1)` for i.i.d. uniform values (`5/12` for two bidders).
- **Multi-parameter characterizations:** Groves mechanisms as the only DSIC welfare maximizers on rich valuation domains (Green–Laffont, Holmström), and limits of VCG such as revenue monotonicity and collusion.

### Social choice ([#3282](https://github.com/cslib-community/complexitylib/issues/3282))

Social welfare and social choice functions on strict rankings, from Arrow's impossibility theorem (Geanakoplos's pivotal-voter proof) onward.

- **Strategy-proofness:** the Gibbard–Satterthwaite theorem for social choice functions onto at least three alternatives, for example by Reny's side-by-side proof (Economics Letters 70, 2001), sharing the pivotal-voter infrastructure with Arrow's theorem.
- **Characterizations:** May's theorem (majority rule is the only anonymous, neutral, positively responsive rule on two alternatives), the individual-weak-order corollary of Arrow's theorem by an IIA reduction to strict profiles, and the infinite-electorate counterexample from a nonprincipal ultrafilter (Fishburn 1970).
- **Quantitative Arrow** ([#2131](https://github.com/cslib-community/complexitylib/issues/2131)): Kalai's Fourier-analytic bound on the probability of a Condorcet paradox and its robust version via FKN.
- **Computational social choice:** polynomial-time manipulation of greedy-manipulable rules, NP-hardness of manipulating second-order Copeland (Bartholdi–Tovey–Trick 1989), and the complexity of winner determination for Dodgson and Kemeny rules, with explicit profile encodings and charged running time.

### Structural graph algorithms

- **Dynamic programming over tree decompositions** ([#2927](https://github.com/cslib-community/complexitylib/issues/2927)): a reusable evaluator over a supplied rooted decomposition with state-space, transition, join and runtime bounds, and an executable FPT `TimeM` independent-set program charging its operations on materialized tables ([#3295](https://github.com/cslib-community/complexitylib/issues/3295)).
  Clients: coloring and SAT/CSP decision and counting, each naming the graph whose width is measured; runtimes are stated in the number of vertices.
- **Treewidth structure** ([#2927](https://github.com/cslib-community/complexitylib/issues/2927)): an encoded treewidth parameter connected to `FPT`, nice decompositions, treewidth under minors, and the grid and separator characterizations of treewidth.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style theorem with computable parameter dependence on width and formula size.
  Keep the supplied decomposition and its encoding explicit; certify decomposition finding separately.
  Connect the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Exact fixed-field sampling:** fair-bit samplers for fixed finite fields such as `F4`, with encoded arithmetic, certified circuit evaluation over finite semirings and gate-code validation ([#2770](https://github.com/cslib-community/complexitylib/issues/2770)), used by circuit-bound VOLE ([#2688](https://github.com/cslib-community/complexitylib/issues/2688)).
  Separate endpoints: output and count validation, native circuit-bound VOLE execution ([#2765](https://github.com/cslib-community/complexitylib/issues/2765), [#643](https://github.com/cslib-community/complexitylib/issues/643), [#2738](https://github.com/cslib-community/complexitylib/issues/2738)), growing extension-field arithmetic, raw-bit adversarial transport ([#2744](https://github.com/cslib-community/complexitylib/issues/2744)) and fresh-session amplification.
- **Markov-chain sampling** ([#2857](https://github.com/cslib-community/complexitylib/issues/2857)): total-variation mixing bounds by coupling, path coupling ([#2933](https://github.com/cslib-community/complexitylib/issues/2933)), conductance, canonical paths and spectral gaps, and an FPRAS for colorings in the sense of `Classes/FPRAS`, charging the estimator's Glauber updates.
  Implement Metropolis sampling for encoded rational target weights, charging initialization, arithmetic and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling** ([#3039](https://github.com/cslib-community/complexitylib/issues/3039)): the Jerrum–Valiant–Vazirani equivalence of FPRAS and FPAUS for self-reducible witness families, including the converse FPRAS ⇒ FPAUS by rejection sampling and self-reductions fixing several symbols per step.
  Instantiate both directions for concrete relations such as DNF assignments.
- **Approximate counting of matchings and permanents:** randomized approximate counting for matchings and permanents of nonnegative rational matrices through explicit mixing and reduction theorems.
  Reuse the coupling and expander APIs and connect to the separate Stockmeyer oracle-counting track where their hypotheses agree.

### Constructive probabilistic methods

- **Moser–Tardos resampling** ([#3096](https://github.com/cslib-community/complexitylib/issues/3096)): the algorithmic local lemma from Moser's `k`-SAT entropy compression ([#2879](https://github.com/cslib-community/complexitylib/issues/2879)) to the general variable form with parallel and derandomized versions (Theorems 1.2–1.4), the symmetric `e p (d + 1) ≤ 1` and `k`-SAT corollaries, the lopsided form, and native sampling and event-detection costs.
  Build the Kolmogorov form's decoder ([#3043](https://github.com/cslib-community/complexitylib/issues/3043)) as a multi-tape machine taking the formula, transferring it to `condPlain`.
- **Conditional expectations and pessimistic estimators:** algorithmic alteration, and coloring, MAX-CUT or combinatorial-construction clients of the certified greedy choice rule for pessimistic estimators.
  Preserve the quantitative guarantee when converting an existence argument into a deterministic or randomized algorithm.
- **Small sample spaces** ([#2935](https://github.com/cslib-community/complexitylib/issues/2935)): searching a `k`-wise independent sample space for an assignment as good as a uniformly random one on clauses of at least `k` distinct literals, with polynomial-time certificates for the search over the three-wise parity space and the trinomial-field space for fixed `k > 3`.
  Extend to small-bias and almost `k`-wise independent spaces and their clients.

### Randomized verification and fingerprinting

- **Fingerprinting** ([#2980](https://github.com/cslib-community/complexitylib/issues/2980)): Freivalds' matrix-product verifier, Karp–Rabin fingerprints (a random evaluation point over a finite field, or a random prime modulus with explicit prime-counting bounds), a rolling-hash pattern matcher with charged updates and a union bound over all windows, and the private-coin `O(log n)` equality protocol.
  Native machine or RAM realizations with bit-level arithmetic costs are a separate endpoint.

## Machines, RAM and data structures

- **Efficient universal simulation** ([#800](https://github.com/cslib-community/complexitylib/issues/800)): A universal function that runs in time `O(N + poly(D, M) · (t + 1) log(t + 2))`, for encoded input length `N`, description length `D` and largest input symbol `M`, with a storage bound in terms of the simulated machine's space rather than its time.
  Both a clocked form and an unclocked form that runs until the simulated machine halts are in scope.
- **Plain computability** ([#862](https://github.com/cslib-community/complexitylib/issues/862)): Complete the plain calculus ([#608](https://github.com/cslib-community/complexitylib/issues/608)), delete the tidy calculus, keeping only a machine-level kernel inside the Machines layer, and switch the abstract bridges to the shared predicate.
- **Certificate APIs and automation** ([#1155](https://github.com/cslib-community/complexitylib/issues/1155)): Predictable certificate search, with fixed heartbeat budgets on regression goals, failures that name the subterm lacking a certificate, and cheap syntax-directed composition for glue code, using Cook–Levin and GGM as regression clients.
  Improve configuration views, tape partitions and handoff identities only where several clients benefit, keeping machine transitions out of global simp.
- **Certificate coverage** ([#1155](https://github.com/cslib-community/complexitylib/issues/1155)): Infer encodings for ordinary functional expressions through constructor, projection, lookup and composition rules, and generalize list, bounded-table, cache and nested-loop invariants where clients need them.
  Keep time, workspace and output-size bounds separate through composition, apply cumulative streaming contracts to captured iteration and nested loops, and develop general open-program composition.
- **Certified PRG stretching** ([#2784](https://github.com/cslib-community/complexitylib/issues/2784)): Certify PRG stretching with seed length, rounds and generator cost kept separate.
  A related target is the adaptive arbitrary-word cipher with its hash-then-MAC/EtM construction ([#2749](https://github.com/cslib-community/complexitylib/issues/2749)).
- **Mathlib TM2:** Sublinear work-space comparisons and a linear-space forward simulation.
- **Single-tape lower bounds** ([#2884](https://github.com/cslib-community/complexitylib/issues/2884)): Crossing-sequence lower bounds for cslib `SingleTapeTM` deciders, including the quadratic palindrome lower bound with a matching `O(n²)` single-tape decider.
  A linear-time multi-tape palindrome decider gives the one-tape/two-tape time separation.
  The gap theorem that single-tape deciders in time `o(n log n)` accept only regular languages ([#2965](https://github.com/cslib-community/complexitylib/issues/2965)), and its nondeterministic analogue under the accept measure.
- **Generic RAM:** Uniform arbitrary-program dispatch with general width-selection and input-fit theorems, and simulation of operations by programs over smaller bases.
  Structured programs and time classes over arbitrary value domains with weighted or bit costs, simulations between instances, and the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Word RAM:** An AC⁰ basis, wider-fragment and Turing-machine simulations, transfer of Anthropic's modular machine and APSP algorithms, and size-based width selection with an input-fit guarantee and explicit overhead.
  Transfer of cell-probe lower bounds, and the Horn-SAT, 2SAT, matching and domino-tiling clients.
- **Randomized Word RAM** ([#1124](https://github.com/cslib-community/complexitylib/issues/1124)): Expected-time rules for unbounded almost-surely terminating structured loops, random-tape equivalence, and BPP/RP/ZPP simulation bridges for the randomized word RAM.
- **Sharper native Exact Triangle exponent** ([#2423](https://github.com/cslib-community/complexitylib/issues/2423)): Prove an `Oκ(n^2.9983)` bound, the source's stated exponent, for the automatic box-backed Exact Triangle host under the library's native conventions.
- **Memory-oracle realization** ([#2205](https://github.com/cslib-community/complexitylib/issues/2205), [#2213](https://github.com/cslib-community/complexitylib/issues/2213)): Verify Word-RAM algorithms as memory-oracle programs refined to native programs by game-hop proofs, replacing hand-stepped code proofs.
  Realization covers memory queries, certified word-sized glue, binds, branches and bounded loops, and charges local work and every loop iteration.
  A realized client is one initialized native program whose clock includes input installation, control and halt.
- **Memory-oracle clients** ([#2205](https://github.com/cslib-community/complexitylib/issues/2205), [#2290](https://github.com/cslib-community/complexitylib/issues/2290), [#2289](https://github.com/cslib-community/complexitylib/issues/2289)): Realize the stack, the framed queue with faithful allocation, the binary and Fibonacci heaps with their Dijkstra consumers, the indexed min-priority queue, and Karger–Stein, keeping each client's original word envelope and bounds.
  Karger–Stein also needs randomized realization adapters, its contraction implementation and a recursive frame stack.
  The direction also covers generic stateful and whole-client composition and the Fibonacci heap's execution migration.
- **Stateful Word-RAM algorithms:** Word-RAM controllers for larger adaptive and iterative clients, including the two-stack queue and timeline-editing controllers, with reusable allocation and deallocation, shrinking, and live and peak space accounting.
  Ownership and recursive procedures, and model realizations for cell probes, caches and randomness.
- **Data-structure extensions:** Present and historical queries for the retroactive interface, balancing and heap or RAM representations of search trees, uniform preprocessing and dynamic updates for fusion trees, deletion and predecessor for van Emde Boas sets, and deallocation, shrinking and compiled client controllers for the doubling array.
- **Typed-call evaluator:** An evaluator for fixed-program Word-RAM clients that returns the typed observation, final state and halt-inclusive instruction cost, so that the prefix-sum clients no longer assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#949](https://github.com/cslib-community/complexitylib/issues/949)): Lift the operation-count helpers to `IndexedMinPQ`, and parameterize flat-program operation-sequence execution (`RunsOps`) over `PQCode` so that `BinaryHeap` and `FibonacciHeap` share one generic `run_ops_exact` theorem.
  Factor a common `ShortestPathSpec p bound` predicate across `LogLinearSpec`, `FibonacciSpec` and `FibonacciLinearSpec`.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** Work–span semantics for a parallel language or PRAM model whose computation DAGs feed the unit-time DAG scheduling bounds of `Algorithms/Lean/Scheduling/Brent.lean`, followed by prefix scan, sorting and graph primitives with both work and span bounds.
  State processor access, synchronization and scheduling overhead explicitly, including work stealing (Blumofe–Leiserson).
- **Memory hierarchies:** External-memory and ideal-cache models with explicit capacity and block-size parameters, with scanning, B-tree operations, blocked matrix multiplication and cache-oblivious sorting as clients.
  Connect arithmetic-step, memory-access and cache-miss bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity:** LOCAL and CONGEST models with explicit identifiers, round, message-size and randomness conventions, with locality lower bounds, communication-to-round reductions and corresponding algorithmic examples.
  Targets include general graphs with port numbering, Linial's `O(Δ²)` colouring, `(Δ + 1)`-colouring and MIS on bounded-degree graphs, CONGEST message bounds, and randomized LOCAL algorithms such as Luby's MIS.
- **Locality on cycles and paths** ([#3009](https://github.com/cslib-community/complexitylib/issues/3009)): Cole–Vishkin colouring, Linial's `log*` lower bound, and round bounds of the form `(log* n) / 2 + c` for 3-colouring and MIS on cycles, with matching upper and lower constants.
  The Chang–Studený–Suomela `O(1)`/`Θ(log* n)`/`Θ(n)` classification of LCL problems on directed cycles, with the tight `½ log* n + O_|L|(1)` bound for flexible problems, extended to LCLs with inputs, paths and undirected cycles.
- **Fault-tolerant agreement** ([#3261](https://github.com/cslib-community/complexitylib/issues/3261)): Synchronous Byzantine agreement with the `n ≤ 3t` impossibility, the connectivity bound `κ ≥ 2t + 1` on general graphs (Fischer–Lynch–Merritt), protocols for all `n > 3t`, and the `t + 1` round lower bound (Fischer–Lynch).
  It also covers authenticated agreement for any `n > t`, weak agreement, the Byzantine firing squad, approximate-agreement and clock-synchronization bounds, and randomized agreement.

## Coverage and reuse

The long-term bar is to support formalizing every paper in the [Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/), with the additional work per paper increasingly its new mathematics: standard models, representation changes, reductions, resource certificates and proof techniques come from the library.
Use a growing, source-pinned sample of papers, including some chosen after an API was designed, as demanding clients, and promote recurring obligations into shared APIs only after reuse is demonstrated.

- **Measure postprocessing** ([#2732](https://github.com/cslib-community/complexitylib/issues/2732)): Canonical full-L1 total variation contracts under measurable maps of arbitrary finite measures, including unequal masses.
  Its consumer is the Gaussian projection and mod-one bound ([#2734](https://github.com/cslib-community/complexitylib/issues/2734)).
- **Finite weighted measure mixtures:** Bound the full-L1 distance when both the finite component measures and their nonnegative weights change, keeping the comparison components' total masses explicit so that neither probability normalization nor equal masses is required.
  The tagged finite-PMF form supplies the error-composition step for the Regev LWE experiment ([#2767](https://github.com/cslib-community/complexitylib/issues/2767)); identifying and bounding its conditional laws belongs to that issue.
- **Gaussian density and projection laws** ([#2733](https://github.com/cslib-community/complexitylib/issues/2733)): Identify the positive-width normalized Gaussian weight with a scaled standard Gaussian, whose scalar projections have variance `(s ‖z‖)² / (2π)`, including the zero vector and dimension zero.
  Prove the discrete-coset convolution projection and mod-one bound ([#2734](https://github.com/cslib-community/complexitylib/issues/2734)); efficient sampling and the quantum reduction belong to [#1213](https://github.com/cslib-community/complexitylib/issues/1213).
- **One sensitivity API:** Define the sensitivity measures over any `Fintype` in CSLib and drop the separate measures of the sensitivity-separation development.
- **CNF evaluation certificates:** `fun_prop` certificates for evaluating literals, clauses and formulas under a polynomial-time assignment, so that clients stop passing `CNF.eval`, `Clause.eval` and `Literal.eval` to `fun_prop` as unfolding hints.
- **Indicator-expectation and conversion lemmas:** Factor the indicator-expectation identities from PCP's second-moment calculation, and recurring cardinality and logarithm conversions, once a second client benefits.
- **Divide-and-conquer recurrences** ([#3042](https://github.com/cslib-community/complexitylib/issues/3042)): A master theorem over `ℕ` with explicit constants for inequality recurrences in all three polynomial cases, with `IsBigO` forms, matching `Θ` bounds for equality recurrences, and case 3 under the general regularity condition.
  Move hand-solved recurrences onto it where the generic constant suffices, keeping cslib's sharper merge-sort bound and the halving lemma, the sharp tool for `b = 2`.

### OpenAI math results ([#1002](https://github.com/cslib-community/complexitylib/issues/1002))

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the openai/math release, and extract the in-scope results, both headline theorems and minor lemmas useful in their own right.
Prove each against Complexitylib's definitions from the cited manuscript's exact statement with its version pinned, labelling unrefereed results; a source formalization is a reference, not evidence.
The openai/math formalizations are Apache 2.0, as is Complexitylib, so adaptation with attribution is permitted; the rewrites state no license and are only read and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/complexitylib/issues/1538)): A `#k`-SAT model counter running in time `2^{O_k(n log log n / √log n)}` at arbitrary density, by recursive tensor contraction.
  The intended route combines the fixed-density bound `2^{O_{k,D}(n / √log n)}` (Theorem D.1 with `ℓ = 1`) with the Lemma D.2 construction, applied natively to the model-counter interface.
- **Exact optimization:** Exact MAX-SAT score distributions and optima in contraction time measured by literal occurrences plus clauses, with `2^{O_{k,c}(n / √log n)}` time and polynomial space for sparse fixed-width instances, and native extraction of an optimizing assignment.
  Neither these bounds nor ordinary SAT sparsification gives a variable-count rate for dense exact MAX-SAT.
- **Large weights:** Exact contraction of natural tensor tables whose bit lengths are polynomial in the structural size, applied natively to weighted-CSP partition functions, and signed or rational weight interfaces.

## Documentation and repository

- **The guide** ([#585](https://github.com/cslib-community/complexitylib/issues/585)): A chapter per area, including Foundations (bit strings, Fourier analysis, PMF and `ProbComp`, codes), proof complexity, descriptive complexity, and Word RAM and algorithms, reusing checked examples.
- **Curated formal abstracts:** Improve readability, and compare each changed abstract with its final source statements.
- **Archive `complexitylib-v1`:** Archive the repository once its remaining work is dispositioned.
