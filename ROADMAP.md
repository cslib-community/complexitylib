# Roadmap

The directions cslib-frontier aims to cover, grouped by area.
This file lists directions only: status, progress and completion notes live on the linked issues and pull requests, module docstrings describe what is proved, and the [results inventory](results/README.md) collects completed named results.
A PR edits this file only when it opens or closes a direction.
Each entry states its direction's scope in at most a few sentences, one sentence per line.
A direction leaves this file only when it is completed or deliberately dropped, and there is no deferred tier.

A direction is complete only when its machine, resource and quantitative conclusions are proved for the actual algorithms, with explicit models, encodings and assumptions.
An abstract algorithm, a class definition or an assumed reconstruction theorem does not complete it.
Search Mathlib, CSLib and this library before starting, and check upstream work.

The [pre-rewrite roadmap](https://github.com/cslib-community/cslib-frontier/blob/c89dd48c/ROADMAP.md) is the archive of past detail and design records, including the FHE industrial context, the first-order design decisions and the repository's history.
The [version before the scope-only rewrite of 2026-11-08](https://github.com/cslib-community/cslib-frontier/blob/9886447e2/ROADMAP.md) holds the progress notes removed in that rewrite.

## Programs

| Program | Issues |
| --- | --- |
| Frontier program: ambitious theorems toward the research frontier | [#897](https://github.com/cslib-community/cslib-frontier/issues/897); its tracks are linked below |
| Optional experiment: formalize unformalized STOC 2027 submission results, subject to independent source-correspondence review | [#2527](https://github.com/cslib-community/cslib-frontier/issues/2527) |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798](https://github.com/cslib-community/cslib-frontier/issues/798), cleanup [#4644](https://github.com/cslib-community/cslib-frontier/issues/4644) |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862](https://github.com/cslib-community/cslib-frontier/issues/862), from [#456](https://github.com/cslib-community/cslib-frontier/issues/456) |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949](https://github.com/cslib-community/cslib-frontier/issues/949), [#939](https://github.com/cslib-community/cslib-frontier/issues/939) |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#2585](https://github.com/cslib-community/cslib-frontier/issues/2585) |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640](https://github.com/cslib-community/cslib-frontier/issues/640), [#643](https://github.com/cslib-community/cslib-frontier/issues/643) |
| Crypto frontier track: Kilian's succinct arguments | [#999](https://github.com/cslib-community/cslib-frontier/issues/999) |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002](https://github.com/cslib-community/cslib-frontier/issues/1002) |
| A Verso guide with a chapter per area | [#585](https://github.com/cslib-community/cslib-frontier/issues/585) |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124](https://github.com/cslib-community/cslib-frontier/issues/1124) |
| Proof automation: predictable polynomial-time certificate search | [#1155](https://github.com/cslib-community/cslib-frontier/issues/1155) |

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897](https://github.com/cslib-community/cslib-frontier/issues/897).

1. [Completeness of oblivious transfer](#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886](https://github.com/cslib-community/cslib-frontier/issues/886))
3. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889](https://github.com/cslib-community/cslib-frontier/issues/889))
4. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity) ([#321](https://github.com/cslib-community/cslib-frontier/issues/321))
5. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891](https://github.com/cslib-community/cslib-frontier/issues/891))
6. [MIP = NEXP](#interactive-proofs) ([#892](https://github.com/cslib-community/cslib-frontier/issues/892))
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

- **Completeness of oblivious transfer** ([#1212](https://github.com/cslib-community/cslib-frontier/issues/1212)): In the ideal OT-hybrid model, every polynomial-time multiparty functionality admits a protocol secure against static malicious corruptions, with real/ideal simulation and abort, under the standard communication assumptions.
  The route needs ideal commitment realization from OT with efficient two-sided simulation, composition, a malicious compiler and MPC simulation.
- **Regev's worst-case to average-case reduction** ([#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)): For suitable `q` and Gaussian noise rate `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`.
  The noise law, modulus restrictions and quantum reduction are part of the theorem.
  Its foundations are [#2573](https://github.com/cslib-community/cslib-frontier/issues/2573), [#2592](https://github.com/cslib-community/cslib-frontier/issues/2592), [#2608](https://github.com/cslib-community/cslib-frontier/issues/2608), [#2624](https://github.com/cslib-community/cslib-frontier/issues/2624), [#2646](https://github.com/cslib-community/cslib-frontier/issues/2646), [#2659](https://github.com/cslib-community/cslib-frontier/issues/2659), [#2681](https://github.com/cslib-community/cslib-frontier/issues/2681), [#2707](https://github.com/cslib-community/cslib-frontier/issues/2707), [#2734](https://github.com/cslib-community/cslib-frontier/issues/2734), [#2766](https://github.com/cslib-community/cslib-frontier/issues/2766) and, for Lemma 3.11, [#2767](https://github.com/cslib-community/cslib-frontier/issues/2767).
- **Kilian's succinct arguments** ([#999](https://github.com/cslib-community/cslib-frontier/issues/999)): If collision-resistant hash families exist, every language in NP has an interactive argument with polylogarithmic communication, by committing to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle versions.
  The target needs an honest prover efficient from an arbitrary NP witness, with the verifier's runtime and message truncation accounted for.

### Modern fully homomorphic encryption

Develop these in reviewable milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions where their hypotheses match.
The [pre-rewrite FHE section](https://github.com/cslib-community/cslib-frontier/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities) maps the schemes to current libraries and workloads.

- **Gentry's exact loss and running time** ([#2585](https://github.com/cslib-community/cslib-frontier/issues/2585), [#2722](https://github.com/cslib-community/cslib-frontier/issues/2722)): For Gentry's bootstrapping instantiated with GSW ([#486](https://github.com/cslib-community/cslib-frontier/issues/486), [#1104](https://github.com/cslib-community/cslib-frontier/issues/1104)), prove his exact concrete-security loss and the `poly(ℓ, d)` running-time clause of his Theorem 4.
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

### Public-key, lattice and symmetric constructions ([#640](https://github.com/cslib-community/cslib-frontier/issues/640))

- **Sigma protocols and Fiat–Shamir** ([#581](https://github.com/cslib-community/cslib-frontier/issues/581), [#2568](https://github.com/cslib-community/cslib-frontier/issues/2568)): Prove random-oracle EUF-CMA security of Schnorr signatures under discrete log against strict PPT forgers with encoded signing and hash access, by an efficient forking reduction for the actual key-generation and signing algorithms.
  Identification and eavesdropping security do not suffice.
  Its components are [#2672](https://github.com/cslib-community/cslib-frontier/issues/2672), [#2684](https://github.com/cslib-community/cslib-frontier/issues/2684), [#2696](https://github.com/cslib-community/cslib-frontier/issues/2696), [#2708](https://github.com/cslib-community/cslib-frontier/issues/2708), [#2724](https://github.com/cslib-community/cslib-frontier/issues/2724), [#2774](https://github.com/cslib-community/cslib-frontier/issues/2774), and forger replay in [#2579](https://github.com/cslib-community/cslib-frontier/issues/2579), [#2636](https://github.com/cslib-community/cslib-frontier/issues/2636) and [#2652](https://github.com/cslib-community/cslib-frontier/issues/2652).
- **Lattice signatures from SIS**: Prove random-oracle EUF-CMA security of Lyubashevsky's signatures (2009, 2012) from SIS by a native reduction that receives only `A`, with an efficient secret-free simulator and a security parameter family.
  The route covers forking ([#2620](https://github.com/cslib-community/cslib-frontier/issues/2620)), witness invariance ([#2642](https://github.com/cslib-community/cslib-frontier/issues/2642)), the ROM bridge ([#2661](https://github.com/cslib-community/cslib-frontier/issues/2661)), cache-hit bounds ([#2712](https://github.com/cslib-community/cslib-frontier/issues/2712)), oracle programming ([#2750](https://github.com/cslib-community/cslib-frontier/issues/2750)) and visible signing simulation ([#2788](https://github.com/cslib-community/cslib-frontier/issues/2788), [#2798](https://github.com/cslib-community/cslib-frontier/issues/2798)).
- **Lattice identification and Dilithium-style signatures**: Prove identification security under SIS, and the security of Dilithium-style signature schemes over module SIS and module LWE, as theory.
- **Hybrid encryption** ([#2725](https://github.com/cslib-community/cslib-frontier/issues/2725)): Prove adaptive CCA security of KEM–DEM hybrid encryption, with the factor-two bound of Boneh–Shoup Exercise 12.5(a) for `n`-bit messages, by native reductions to the KEM and one-time symmetric CCA games ([#2692](https://github.com/cslib-community/cslib-frontier/issues/2692), [#2694](https://github.com/cslib-community/cslib-frontier/issues/2694)).
  Then extend it to arbitrary message spaces, prechallenge KEM queries and multiple encapsulation challenges.
- **Paillier encryption and composite residuosity**: Prove IND-CPA security of Paillier encryption under Decisional Composite Residuosity (Katz–Lindell Theorem 15.13) for the actual word algorithms, with approximate unit sampling and native balanced-modulus generation.
  The homomorphic property of Definition 15.14 needs an exact or statistical-closeness formulation, since its exact distributional condition fails for the implemented sampler.
- **Garbled circuits and Yao's protocol** ([#3236](https://github.com/cslib-community/cslib-frontier/issues/3236)): Prove exact correctness and concrete simulation privacy of point-and-permute garbling for arbitrary-basis circuits, with privacy bounded by the sum of `n + size` PRF advantages.
  Prove semi-honest security of Yao's two-party protocol, with oblivious transfer realized by a protocol through an advantage-preserving composition theorem instead of an ideal batched OT oracle, and an asymptotic PPT statement from a word-level pseudorandom function.
  Extensions are output to both parties, and polynomial-time free-XOR and half-gates privacy.
- **General**: Reusable adaptive reductions, public-key encryption, universal-instance zero knowledge, hard-core predicates and hardness amplification, and connections to learning and average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643](https://github.com/cslib-community/cslib-frontier/issues/643))

The libzk components are listed in build order, ending with libzk's compositional structure.
General auxiliary-input zero knowledge, the last entry, is independent of that order.

- **Public-coin to IP bridge**: Map public-coin protocols into IP with a uniform word verifier and adversarial message decoding.
- **Composition and round-by-round knowledge soundness**: Parallel and AND/OR composition of protocols and relations, with round-by-round knowledge soundness preserved under sequential, parallel and OR composition.
- **Oracle statements**: Let a later phase query an earlier phase's oracle message (virtual output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds.
- **Efficient simulators and auxiliary-input zero knowledge**: Efficiency-certified simulators and extractors, and auxiliary-input zero knowledge on the interactive core.
- **Polynomial commitments and Ligero**: Polynomial commitment and evaluation-query reductions, and the Ligero IOP.
- **BCS transform**: Compile IOPs into non-interactive arguments in the random-oracle model with soundness and knowledge-soundness bounds, machine-level verifier and extractor runtime, a polynomial-time encoding of NP witnesses into IOPs, and zero knowledge.
- **VOLE constraint reductions and VOLE-in-the-head**: Prove full zero-knowledge security of VOLE-based proofs for the arithmetic-circuit relation `∃ w, C.eval (x ++ w) = y`, with fresh-session amplification, scalar-challenge batching, growing fields, adversarial setup and scheduling, then VOLE-in-the-head.
  This includes a native circuit prover/verifier certificate with honest-sender realization ([#2765](https://github.com/cslib-community/cslib-frontier/issues/2765)) and raw-bit adversarial transport ([#2744](https://github.com/cslib-community/cslib-frontier/issues/2744)).
- **libzk composition**: Express libzk's compositional structure as a composition of these components, without ciphersuites.
- **General auxiliary-input zero knowledge** ([#324](https://github.com/cslib-community/cslib-frontier/issues/324)): If one-way functions secure against non-uniform adversaries exist, every language in NP has an interactive computational zero-knowledge proof system secure against PPT verifiers with arbitrary auxiliary input, following Goldreich–Micali–Wigderson with Naor's bit commitments.

### Private information retrieval ([#3251](https://github.com/cslib-community/cslib-frontier/issues/3251))

Information-theoretic private information retrieval, following Chor–Goldreich–Kushilevitz–Sudan (CGKS).

- **Information-theoretic PIR** ([#3451](https://github.com/cslib-community/cslib-frontier/issues/3451)): one-round schemes with perfect correctness and single-server privacy: subcube schemes with the rows transformation, covering-code schemes and schemes from perfectly smooth decoders.
  The covering-code schemes of CGKS Section 3.3 include radius-`2` codes, the other dimensions of Figure 1, the asymptotic lower estimate and server time, and take variable-length answers so that unbalanced covers meet CGKS Theorem 1 exactly.
  Also `t`-private schemes against coalitions, block retrieval and the converse from schemes to smooth codes (Katz–Trevisan).
- **PIR lower bounds** ([#3426](https://github.com/cslib-community/cslib-frontier/issues/3426)): the single-server bound with and without interaction, the two-server linear-summation bound with its tight even-set scheme (CGKS Section 5), and lower bounds for general two-server schemes.

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

- **Planar Boolean CSP dichotomy** ([#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)): extend the native Boolean classification to ordered planar instances of arbitrary fixed relation arity, preserving individual incidence occurrences and cyclic argument order.
  The endpoint must prove the embedding and recognition interface, the cyclic-difference reduction, the even delta-matroid edge-CSP algorithm and planar hardness transfer internally, including the additional self-complementary tractable family.
  Supplied-embedding or matching-realizable-only milestones leave it open.
- **Boolean Schaefer dichotomy** ([#2822](https://github.com/cslib-community/cslib-frontier/issues/2822)): for every fixed finite Boolean constraint language of any fixed arity, native polynomial-time tractability in the six common-polymorphism cases and native NP-completeness otherwise, including empty and nullary relations.
  Hardness uses a native 3SAT reduction with `output.numVars + output.length ≤ C * input.length` for a language-dependent constant.
  Symmetric and larger-domain dichotomies are out of scope.
- **Context-free languages** ([#3303](https://github.com/cslib-community/cslib-frontier/issues/3303)): CYK membership for grammars in Chomsky normal form, correct against Mathlib's `ContextFreeGrammar.Derives` with exact `TimeM` cost `O(n³ · |G|)`, and conversion of an arbitrary grammar to Chomsky normal form with its size blow-up, giving decidability of every context-free language.
  Also a machine-level polynomial-time decider for each fixed grammar (CFL ⊆ P, Sipser Theorem 7.16), Valiant's subcubic parsing by Boolean matrix multiplication, the pumping lemma with non-context-freeness of `{aⁿbⁿcⁿ}`, and CFG emptiness in P versus undecidable universality.
- **Structural classes and relativization:** time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes; completeness, padding, self-reducibility, relativization and oracle separations, preserving each reduction's resource bound.
- **Abstract (Blum) complexity** ([#2866](https://github.com/cslib-community/cslib-frontier/issues/2866)): Blum measures over Mathlib's `Nat.Partrec.Code`, with gap, speedup, union and compression theorems, recursive relatedness and arbitrarily complex functions.
  Compression is in running-time form, one computable `h` with `C_{Φ_i} ⊂ C_{n ↦ h n (Φ_i n)}` for every total `φ_i`; the value form is false by the gap theorem.
  Also McCreight–Meyer honesty and naming ([#3234](https://github.com/cslib-community/cslib-frontier/issues/3234)), `g`-honesty for partial functions (Odifreddi II, Exercises VII.2.14b–d), effective speedup (Blum's pseudo-speedup), and native multitape time and space as measures.
- **Busy beaver** ([#3314](https://github.com/cslib-community/cslib-frontier/issues/3314)): the theorem that Radó's output and fuel busy beaver functions for `Nat.Partrec.Code` on input `0`, with codes measured by Gödel number, dominate every computable function, and that a computable upper bound on either would decide halting.
  Also Radó's `Σ(n)` and `S(n)` for Turing machines counted by states, with a simulation bridge to the code version and the known small values (`S(5) = 47,176,870`, from the bbchallenge Coq proof) as a cross-check.
  Beyond these: independence of busy beaver values from ZFC (Aaronson–Yedidia) and the connection to Chaitin's `Ω`.
- **Post's correspondence problem** ([#3387](https://github.com/cslib-community/cslib-frontier/issues/3387)): undecidability of PCP and MPCP over `Bool` and over every alphabet with two distinct letters by Sipser's computation-history reduction, from halting through a universal `TM0` machine and from the acceptance problem of an arbitrary machine.
  Also decidability of unary PCP and of PCP with two dominoes (Ehrenfeucht–Karhumäki–Rozenberg, 1982), undecidability with five dominoes (Neary, 2015), and the consequences for ambiguity, universality and intersection emptiness of context-free grammars and for mortality of 3×3 integer matrices (Paterson, 1970).
- **Degrees of unsolvability** ([#3379](https://github.com/cslib-community/cslib-frontier/issues/3379)): oracle codes for Mathlib's `RecursiveIn` with stage-bounded evaluation, the use principle, `f ≤ᵀ g ↔ ∃ c, Code.eval g c = f`, and the Kleene–Post theorem with incomparability by finite extension and the bound `A, B ≤ᵀ ∅′` (`KleenePost`, `KleenePostJump`).
  Beyond Kleene–Post: a general relativized jump operator (reconciled with [mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973)), the Friedberg–Muchnik theorem by finite injury, Sacks splitting and density of the c.e. degrees, and Spector's minimal degree.
- **Time hierarchies** ([#1572](https://github.com/cslib-community/cslib-frontier/issues/1572)): native deterministic and nondeterministic time hierarchies, including separations of all polynomial degrees (noninteger ones too) and the textbook `f log f = o(g)` hierarchy from the `O(t log t)` universal simulation ([#800](https://github.com/cslib-community/cslib-frontier/issues/800)).
  Also a word-RAM hierarchy by direct diagonalization with a gap smaller than `T` versus `T⁵`, and sharp nondeterministic and alternating time hierarchies with certified simulators.
  Also `(log t)^ε` gaps for every time-constructible `t` beyond `n^a` and `2^n`, and W. J. Paul's fixed-tape hierarchy (1979).
- **Probabilistic time hierarchies** ([#2084](https://github.com/cslib-community/cslib-frontier/issues/2084)): the `PromiseBPTIME` hierarchy for promise problems by delayed diagonalization, following He (ECCC TR25-004), and the one-bit-advice hierarchy for languages of van Melkebeek and Pervyshev.
  The advice-free hierarchy for `BPTIME` itself is open and is not a target.
- **Randomized primality tests** ([#2917](https://github.com/cslib-community/cslib-frontier/issues/2917)): the Euler-liar and strong-liar bounds `2 · #liars ≤ φ(n)` and the Rabin–Monier bound `4 · #strong liars ≤ φ(n)` (`n ≠ 9`) for odd composite `n`, and explicit Miller–Rabin and Solovay–Strassen verifiers putting the primes in `coRP` independently of AKS.
  The Solovay–Strassen verifier ([#2958](https://github.com/cslib-community/cslib-frontier/issues/2958)) uses the polynomial-time Jacobi symbol and a gcd step, since non-units can satisfy Euler's congruence.
- **Catalytic space and KMPS collapses** ([#2521](https://github.com/cslib-community/cslib-frontier/issues/2521)): native `CSPACE(s,c)` with nondeterministic and randomized variants, restoring the catalyst on every branch.
  Koucký–Mertz–Pyne–Sami's [*Collapsing Catalytic Classes*](https://arxiv.org/abs/2504.08444) with its parameter ranges and oracle promises: `CL = CNL = CPrL = CBPL`, compress-or-compute simulation, catalytic Savitch and complementation, randomized space–catalyst tradeoffs, hierarchy collapses and lossy-space consequences.
- **Robust catalytic extensions** ([#2521](https://github.com/cslib-community/cslib-frontier/issues/2521)): the Koucký–Mertz–Sami [robust catalytic extensions](https://arxiv.org/abs/2605.09648), tracked separately from KMPS.
  Their broader collapse is conditional on an explicit circuit-hardness assumption, and their resetting-error and time regimes are kept distinct from the unconditional KMPS results.
- **Classical randomized-space proof reuse** ([#1444](https://github.com/cslib-community/cslib-frontier/issues/1444)): audit and simplify the existing `RL ⊆ NL ⊆ DSPACE(log² n)` proof in [LogSpace/Savitch.lean](CslibFrontier/Computability/Complexity/Classes/LogSpace/Savitch.lean).
  Reuse support semantics, midpoint reachability, compact configuration graphs and native space simulation; share lemmas and refactor real clients while preserving encodings and workspace bounds.
  `RL = L` remains unresolved; this classical-first milestone has no preprint-estimator dependency.
- **Further classical randomized logspace** ([#459](https://github.com/cslib-community/cslib-frontier/issues/459)): two-sided `BPL` amplification, the random-walk proof of `USTCON ∈ RL`, Nisan's generator with its read-once fooling theorem ([#3187](https://github.com/cslib-community/cslib-frontier/issues/3187)), space-efficient computation and configuration-graph bridge, `BPL ⊆ DSPACE(log² n)`, and Saks–Zhou's `BPL ⊆ DSPACE(log^{3/2} n)`.
  The Saks–Zhou iteration as pure mathematics is [#3247](https://github.com/cslib-community/cslib-frontier/issues/3247); these two-sided results are separate from the one-sided Savitch milestone.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888](https://github.com/cslib-community/cslib-frontier/issues/888)): the native inclusion for arbitrary injective input encodings and every `t(n) ≥ n`, without time constructibility, via Tree Evaluation.
  The paper's time–space separation corollaries (including for linear space), Cook–Mertz malformed-input handling and the refined `O(ℓ + H log(ℓ + 2))` bound are [#2855](https://github.com/cslib-community/cslib-frontier/issues/2855).
- **Time–space lower bounds for nondeterministic linear time** ([#2896](https://github.com/cslib-community/cslib-frontier/issues/2896)): the Arora–Barak bound `NTIME(n) ⊄ TISP(n^1.2, n^0.2)` by virtual padding and the Lipton–Viglas `n^(√2 − ε)` form, from the speedup and slowdown lemmas for `TISP` and `Σ₂TIME`.
  Beyond these: the textbook `√(t·s)` speedup, the golden-ratio deterministic bound of Fortnow, Lipton, van Melkebeek and Viglas, and the transfer to SAT through a quasi-linear-size Cook–Levin reduction.
- **Alternating classes** ([#4086](https://github.com/cslib-community/cslib-frontier/issues/4086)): the remaining Chandra–Kozen–Stockmeyer bridges `ATIME t ⊆ DSPACE t`, `NSPACE s ⊆ ATIME (s ^ 2)` and `DTIME (2 ^ O(s)) ⊆ ASPACE s` (`ATIME`, `ASPACE` and `ASPACE s ⊆ DTIME (2 ^ O(s))` are done), and bounded-alternation characterizations of PH; sharp bounds for sublinear space, distinct from polynomial-space simulation.
- **Fast alternating counting simulation** ([#4728](https://github.com/cslib-community/cslib-frontier/issues/4728)): clocked bitwise accepting-path counting through tensor contraction in alternating time `O(n + t / sqrt(log(t+2)))`. Remaining work includes locally accessible contraction expressions, certified index and arithmetic costs, and the count-preserving machine reduction. Input access and clock computation must be charged explicitly.
- **Alternating logspace, `P ⊆ AL`** ([#2873](https://github.com/cslib-community/cslib-frontier/issues/2873)): play the circuit-value game on the tableau of a polynomial-time machine in logarithmic space.
  This needs a word game machine whose round reads the input from the input tape and keeps only the `O(log n)`-bit wire claim on its work tape.
- **Pebble games and space lower bounds** ([#2995](https://github.com/cslib-community/cslib-frontier/issues/2995)): black, black-white and reversible pebbling on digraphs, with exact prices and register evaluation.
  The direction covers Bennett's game on paths ([#3163](https://github.com/cslib-community/cslib-frontier/issues/3163)), Li–Tromp–Vitányi's reachable-configuration characterization and erasure and time–space trade-offs, including whether `3 ^ k` is optimal for `k + 1` pebbles ([#3199](https://github.com/cslib-community/cslib-frontier/issues/3199)), the Hopcroft–Paul–Valiant `O(n / log n)` bound with the matching Paul–Tarjan–Celoni family, and Gilbert–Tarjan and Lengauer–Tarjan trade-offs.
- **Deeper consequences of a Boolean-hierarchy collapse:** Kadin's sparse `S` with `coNP ⊆ NP^S`, and the collapse of `PH` into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, which follows from results of Wagner and of Chang and Kadin, not from Kadin's 1988 argument (see his erratum).
- **Explicit universal SAT solver:** one fixed native algorithm, independent of any assumed fast SAT algorithm, whose worst-case running time is polynomial if and only if `P = NP`.
  It is a total SAT decision procedure, also on unsatisfiable inputs, specified separately from verified witness search.
  The proof accounts for dovetailing, certificate checking and universal simulation overhead, not only the `SAT ∈ P ↔ P = NP` equivalence.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351](https://github.com/cslib-community/cslib-frontier/issues/1351)): logspace Turing reductions, in an oracle model whose query tape is not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets** ([#2062](https://github.com/cslib-community/cslib-frontier/issues/2062), [#3155](https://github.com/cslib-community/cslib-frontier/issues/3155)): Kadin's `PH = P^{NP[O(log n)]}` from a sparse Turing-complete set for NP, his stronger form with a sparse `S ∈ NP` and `coNP ⊆ NP^S`, and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** paddability of the standard NP-complete graph, number and set problems, hence their p-isomorphism to SAT; every many-one complete set for EXP is complete under one-one, length-increasing reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal, Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang); separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468](https://github.com/cslib-community/cslib-frontier/issues/2468)): the full expanded 2013 paper of Glaßer, Nguyen, Reitwießner, Selman and Witek: Lemma 3.3's transfer from local self-reducibility with answer regeneration and adaptive-to-tt conversion, its bounded and many-one cases, Theorem 3.5, and Sections 4 and 5 (query bounds, separations, mitoticity, diagonalization).
  The parity-logspace application needs native path counting and complement closure.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE, self-reducible P-selective sets lie in P, and P-selective sets are not `≤ₜₜᵖ`-hard for NP unless P = NP.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity** ([#2899](https://github.com/cslib-community/cslib-frontier/issues/2899)): `P`-bi-immune sets in `E`, Berman's theorem that `≤ᵖₘ`-complete sets for `E` and `EXP` are not `P`-immune ([#3002](https://github.com/cslib-community/cslib-frontier/issues/3002)), and complexity cores, from Lynch's lemma ([#3080](https://github.com/cslib-community/cslib-frontier/issues/3080)) and decidable cores ([#3182](https://github.com/cslib-community/cslib-frontier/issues/3182)) to `EXP` and `PSPACE` instances, core density (Orponen–Schöning) and core sizes (Juedes–Lutz).
  `DTIME(t)`-bi-immunity for constructible `t`, other Balcázar–Schöning results, almost-everywhere hardness, and Mayordomo's measure results.
- **Exponential-time complete problems** ([#3002](https://github.com/cslib-community/cslib-frontier/issues/3002)): bounded halting with a binary time bound as an `E`- and `EXP`-complete problem, Book's separations of `E` from `EXP`, `NP` and `PSPACE`, succinct circuit value for `EXP` and succinct SAT for `NEXP`, generalized games complete for `EXP`, nondeterministic bounded halting for `NE` and `NEXP`, and the isomorphism and density structure of `E`-complete sets.

### Average-case complexity

- **Distributional framework** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): length-indexed ensembles, `AvgP`, `HeurP`, `DistNP`, dominating reductions, samplability of polynomial-time computable ensembles, Levin's runtime-moment average polynomial time and its relation to errorless schemes, and randomized average-case classes.
  Probability-zero instances obstruct a literal equivalence with errorless schemes.
  Liu–Pass hardness notions should be reused through proved bridges.
- **Heuristic hierarchy and universal distributions** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): `(BH, U^BH) ∈ Heur_{1/n} P` gives `DistNP ⊆ HeurP`, with the `Avg` analogue (Bogdanov–Trevisan Prop. 21), via a fixed clocked universal program on inputs `(c, z, 1^t)`, since the source's padding can change `BH` membership.
  Also Levin, Li and Vitányi (Bogdanov–Trevisan Thm 16): under `K_n(x) ∝ 2^{-C(x)}` on each length, a decidable `L` with `(L, K) ∈ Heur_{1/n³} P` is in `P`.
- **Completeness beyond computable ensembles** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): extend bounded-halting completeness for `DistNP` to samplable distributions (Impagliazzo–Levin, `SampNP`), and bridge the verifier-form bounded halting problem to a nondeterministic machine model.
  Connect the framework to one-way functions, learning and the metacomplexity track ([#798](https://github.com/cslib-community/cslib-frontier/issues/798)), preserving the distribution and reduction conventions.

### Counting and modular classes

- **Another Solution Problem (ASP) framework:** ASP reductions with certified polynomial-time forward and inverse witness maps, starting from the parsimonious reductions to positive exact-one SAT and its planar three-occurrence variants.
  Exact count preservation alone does not supply the ASP runtime certificates.
- **Counting reductions and hierarchies:** counting reductions and further oracle results preserving exact multiplicities; permanent #P-completeness; modular and counting hierarchies; the oracle-algorithm form of Stockmeyer's approximate counting.
- **Exact counting by determinants** ([#3081](https://github.com/cslib-community/cslib-frontier/issues/3081)): Kasteleyn's Pfaffian method for counting perfect matchings of planar graphs in polynomial time, in contrast with permanent #P-completeness (polynomial-time counting for unweighted and weighted spanning trees, simple and multi-digraph arborescences, and BEST Eulerian circuits, along with root independence for balanced graphs, are formalized).
- **Target-relativized counting classes:** `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and UP-oracle containment.
- **Native oracle counting machines:** efficient encoded oracle checking, response-access costs and oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **MIP = NEXP** ([#892](https://github.com/cslib-community/cslib-frontier/issues/892)): `NEXP ⊆ MIP₂` through the BFL multilinearity test and arithmetization of exponential-time tableaux; an efficient GKR verifier under log-space uniformity.
- **Goldwasser–Sipser** ([#2981](https://github.com/cslib-community/cslib-frontier/issues/2981), [#3425](https://github.com/cslib-community/cslib-frontier/issues/3425)): `IP[k] ⊆ AM[k + 2]` for the private-coin games `IPk`, by the set lower bound protocol on the gap-amplified game.
  In the oracle model, oracle-PPT `IP` verifiers with at most `k` queries give exactly the count-based `IPk`, by coin fixing and padding to `k` rounds, which carries `IP[k] = AM` for constant `k ≥ 2` to that model.
  The inclusion extends to `IP[k(n)] ⊆ AM[k(n) + 2]` for round patterns that depend on the input length.
- **Arthur–Merlin classes:** the Babai–Moran speedup `AM[2 t(n)] = AM[t(n)]` for polynomially many rounds (patterns that depend on the input length), interactive-machine characterizations of Arthur–Merlin classes, and statistical and perfect zero knowledge.
- **Statistical zero knowledge** ([#3205](https://github.com/cslib-community/cslib-frontier/issues/3205)): Sahai–Vadhan polarization as a polynomial-time map on encoded Statistical Difference instances with error `2^-(|x|+1)`, honest-verifier SZK containing `SD`, `SD` being SZK-complete, Entropy Difference (Goldreich–Vadhan), closure under complement (Okamoto), and `SZK ⊆ AM ∩ coAM` (Fortnow; Aiello–Håstad).
  Instances are pairs of De Morgan circuits, with general pairs padded to common input and output counts.

### Descriptive complexity and first-order reductions

Ordered first-order complexity follows Immerman: structures on {0, …, n-1} with n ≥ 2, FO means FO(≤, BIT), and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings; the order-free `FO.Reduces` and `FO.QFReduces` stay as a general layer.
Numeric predicates are computed from the universe size, not supplied as unverified input tables.
In dependency order:

- **Projection refinements:** first-order and quantifier-free projection refinements (`≤_fop`, `≤_qfp`) of ordered `REACH` `NL`-completeness, and order-free projection reducibility on arbitrary finite structure classes.
- **Circuit Value P-completeness:** Circuit Value is P-complete under first-order reductions, via `REACHa → MCVP → CVP` (Immerman, Theorem 3.26 and Exercise 3.28), with the alternating-logspace simulation of polynomial-time machines (the machine-level `P ⊆ AL`, see [#2873](https://github.com/cslib-community/cslib-frontier/issues/2873)) and the translation to `encCircuitValue`.
- **Restricted-domain numeric certificates:** numeric certificates for further restricted-domain families; canonical BIT on a restricted domain need not be first-order definable.
- **Order-free reductions:** SAT-to-3SAT, graph-property hardness, and bridges to the separately encoded problems.
- **Synthesis rules and regular-language quantifiers:** extend the synthesis rules to nested operator bodies and give regular-language quantifiers their ordered characteristic-word semantics.
- **Native NL closure facts:** the closure properties that the in-compiler inductive counting of FO(TC) ⊆ NL bypasses: intersection, union, logspace reductions and NL^NL = NL.
- **Further logical characterizations:** on ordered structures, DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing); then order-invariant and fixed-point queries and uniform translations between syntax, structures and algorithms.
- **Witness-carrying reductions:** a witness-carrying reduction structure once a client needs one, for example size bounds for Cook–Levin.
- **Logical lower-bound methods** ([locality track](https://github.com/cslib-community/cslib-frontier/issues/3015)): Ehrenfeucht–Fraïssé games (also with constants), Hanf and Gaifman locality with Gaifman's normal form and the exact locality ranks `2 ^ (n - 1) - 1` and `2 ^ n - 1` (Libkin, Exercises 4.10 and 4.11), and counting and fixed-point expressiveness with Cai–Fürer–Immerman separations, linked to the ordered capture theorems, where FO(≤, BIT) defines EVEN.
- **Nondefinability applications** ([locality track](https://github.com/cslib-community/cslib-frontier/issues/3015), [#3483](https://github.com/cslib-community/cslib-frontier/issues/3483)): game-free locality proofs for connectivity, acyclicity and being a tree; transitive closure and reachability, with an exponential lower bound on the locality radius and FO ⊊ FO(TC) on unordered graphs; then Libkin's balanced binary trees and same generation, planarity, Hamiltonicity and `k`-colorability for `k ≥ 3`.
- **Undecidability in the finite:** Trakhtenbrot's theorem and the decidability dichotomy for Mathlib's `L.Sentence` beyond finite relational languages: infinite vocabularies (with a primitive recursive arity map) and languages with function symbols.
- **Logic and automata on words** ([#2885](https://github.com/cslib-community/cslib-frontier/issues/2885)): Büchi–Elgot–Trakhtenbrot (MSO = regular on finite words), FO[<] ⊊ MSO, and FO[<] = star-free = aperiodic (McNaughton–Papert, Schützenberger; star-free ⇒ FO is [#3075](https://github.com/cslib-community/cslib-frontier/issues/3075) and FO ⇒ star-free, by composition of rank-`k` types, is [#3469](https://github.com/cslib-community/cslib-frontier/issues/3469)), with decidability of first-order definability for regular languages.
  Homomorphic-image closure of regular languages (upstream to CSLib), the non-elementary formula-to-automaton lower bound, Büchi's theorem for ω-words (S1S), and MSO on finite trees (Thatcher–Wright, Doner) and infinite trees (Rabin, S2S).
- **Asymptotic probabilities** ([#4080](https://github.com/cslib-community/cslib-frontier/issues/4080)): beyond the first-order and `L^k_∞ω` 0-1 laws for graphs (`G(n, p)`) and finite relational vocabularies (`bernoulliStructu…14059 tokens truncated…n elimination over `ZMod 2`, separations in the value-query model, and then Forrelation and other optimal quantum–classical query separations.
  The value-query model needs quantum states over an arbitrary finite query index type rather than `Fin N`.
- **Promise problems in quantum query complexity** ([#3310](https://github.com/cslib-community/cslib-frontier/issues/3310)): Deutsch–Jozsa's exact one-query algorithm against the deterministic `N/2 + 1` and constant-query randomized bounds; exact quantum lower bounds for promise problems via polynomial degree (`Q_E ≥ deg/2` on the promise domain); a promise form of `randomizedComplexity`; and recursive Fourier sampling (Bernstein–Vazirani).
- **Quantum query lower bounds** ([#3239](https://github.com/cslib-community/cslib-frontier/issues/3239)): non-Boolean input alphabets (Ambainis Theorem 7, permutation inversion, over the value-query model), comparison-tree, approximate-mean and relative-counting variants of Nayak–Wu, and oracle-overlap deduplication (Ambainis's relational adversary, Nayak–Wu consequences, and weighted/spectral/`ADV±` adversaries have landed).
- **Shor's algorithm** ([#3252](https://github.com/cslib-community/cslib-frontier/issues/3252)): bounded-error polynomial-time integer factoring and discrete logarithms in the native uniform quantum-circuit model, with explicit encodings, success probabilities and gate-approximation costs.
  It needs the quantum Fourier transform with its circuits, period finding including `r ∤ N` by continued fractions and the `Ω(1 / log log r)` totient bound, phase estimation, reversible modular exponentiation and the classical reductions, certifying uniform generation and polynomial gate bounds.
- **Nonlocal games** ([#3313](https://github.com/cslib-community/cslib-frontier/issues/3313)): CHSH and Tsirelson's bound in the finite-dimensional tensor-product model; for general XOR games, Tsirelson's vector characterization and its semidefinite program (Cleve–Høyer–Toner–Watrous Theorem 4, Proposition 5) and the Grothendieck-constant bound on quantum advantage (Theorem 7).
  Also mixed shared states and the commuting-operator model, with the inclusion of the tensor-product value; parallel repetition of entangled games, beside the classical theorem ([#886](https://github.com/cslib-community/cslib-frontier/issues/886)); self-testing of the CHSH strategy; and the class `MIP*`, toward the optional [MIP* = RE](#optional-landmark-projects) project.

### Differential privacy and adaptive data analysis

- **Differential privacy foundations** ([#2867](https://github.com/cslib-community/cslib-frontier/issues/2867)): dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with postprocessing and adaptive composition, including advanced composition ([#2977](https://github.com/cslib-community/cslib-frontier/issues/2977)).
  Mechanisms need both privacy and utility proofs with sampling cost and finite-precision error, covering exact sampling of discrete noise and continuous Laplace and Gaussian mechanisms.
  Also Rényi or concentrated privacy accounting.
- **Private query answering and learning** ([#2977](https://github.com/cslib-community/cslib-frontier/issues/2977)): private query answering and private learning, building on the exponential mechanism and the sparse vector technique; privacy–accuracy and sample-complexity lower bounds; then adaptive data-analysis and generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources explicit, reusing the probability, oracle-computation and learning APIs.
- **Privacy–accuracy lower bounds** ([#3178](https://github.com/cslib-community/cslib-frontier/issues/3178), [#3201](https://github.com/cslib-community/cslib-frontier/issues/3201)): the lower bounds of Dwork–Roth Chapter 8: the packing lemma, the `Ω(k / ε)` bound for one-way marginals, Dinur–Nissim reconstruction, reconstruction from `O(n)` random `±1` queries with `o(√n)` error (Theorem 8.2), and De's `Ω(min(k, d) / ε)` bound over a small universe (Theorem 8.8).
  This includes settling whether the source's constant `(2 α / η) ^ 2` in Theorem 8.2 holds for `η / 2 ≤ α < 1 / 2`, and Theorem 8.8 for add/remove adjacency on histograms as well as row replacement.
  Also `(ε, δ)` lower bounds via fingerprinting codes.

## Algorithms and optimization

### Optimization and duality

- **Linear programming** ([#2976](https://github.com/cslib-community/cslib-frontier/issues/2976)): Fourier–Motzkin, Farkas' lemma and LP duality over linearly ordered fields; rational input and output encodings with bit-size bounds on basic solutions and Farkas certificates (Cramer's rule, Hadamard bound), giving LP feasibility in NP ∩ coNP with machine-checked certificate verifiers.
  Then a polynomial-time LP algorithm (ellipsoid or interior point) accounting for bit complexity and intermediate precision, and LP optimization as a search problem with rational outputs.
- **Simplex method** ([#3370](https://github.com/cslib-community/cslib-frontier/issues/3370)): the simplex method on dictionaries with Bland's rule, its no-cycling theorem and termination within `N.choose m - 1` pivots, optimality and unboundedness certificates, and an optimal dual solution read off the final dictionary.
  Also Phase I (an initial feasible dictionary or an infeasibility certificate), the Klee–Minty cube on which Dantzig's rule makes `2ⁿ - 1` pivots ([#3441](https://github.com/cslib-community/cslib-frontier/issues/3441)) and exponential lower bounds for other pivot rules such as Bland's (Avis–Chvátal 1978), smoothed analysis (Spielman–Teng), strongly polynomial special cases, and a costed implementation.
- **Ellipsoid method** ([#3240](https://github.com/cslib-community/cslib-frontier/issues/3240)): the central-cut ellipsoid method over exact reals, with half-ellipsoid containment, the volume ratio `exp (-1 / (2 (n + 1)))` and the iteration bound against a strong separation oracle.
  For a polynomial-time LP algorithm ([#2976](https://github.com/cslib-community/cslib-frontier/issues/2976)), also a finite-precision update with its rounding error, a volume lower bound for full-dimensional rational polytopes, the reduction of feasibility to that case, and a machine-level running-time bound.
- **Extension complexity** ([#3258](https://github.com/cslib-community/cslib-frontier/issues/3258)): nonnegative rank, slack matrices, extended formulations with free equations, Yannakakis's theorem `xc P = rank₊ S` for nontrivial polytopes and its facet form (an extension with `r` facets), and the rectangle-cover bound `N¹(supp M) ≤ ⌈log₂ rank₊ M⌉`.
  Then exponential lower bounds for the correlation, cut, stable-set and TSP polytopes ([#3611](https://github.com/cslib-community/cslib-frontier/issues/3611), Fiorini–Massar–Pokutta–Tiwary–de Wolf; remaining open: Theorem 3 (ii) facet-count extension, semidefinite and conic extensions, and Rothvoß's lower bound for the perfect matching polytope).
- **Lattice basis reduction** ([#3235](https://github.com/cslib-community/cslib-frontier/issues/3235)): `δ`-reduced bases and the LLL algorithm on integer bases, with the shortest-vector approximation `‖b₁‖² ≤ (4/(4δ-1))^{n-1} ‖x‖²` (LLL Proposition (1.11)), and Babai's nearest-plane algorithm for CVP within `2^{n/2}` ([#3486](https://github.com/cslib-community/cslib-frontier/issues/3486)).
  Costs cover the `O(n² log B)` bound on exchange steps, `O(n⁴ log B)` arithmetic operations and the `O(n log B)` bit-size bound of (1.26), giving polynomial-time statements for LLL and Babai; also `δ` near `1` and rational Babai targets.
  Applications include simultaneous Diophantine approximation and polynomial factorization over `ℚ`.
- **Separation and optimization:** a precise oracle interface and a separation–optimization equivalence with its representation, accuracy and well-boundedness hypotheses.
  Extend to convex optimization through explicit oracle and numerical-error contracts.
- **Lovász theta and perfect graphs** ([#2998](https://github.com/cslib-community/cslib-frontier/issues/2998)): Shannon capacity and the theta function `ϑ`, with the sandwich `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`, `Θ(G) ≤ ϑ(G)` and `Θ(C₅) = √5`, and the equivalent orthonormal-representation, SDP and eigenvalue formulations of `ϑ`.
  Then its polynomial-time approximation by the ellipsoid method (Grötschel–Lovász–Schrijver), which makes clique number and chromatic number of perfect graphs polynomial-time computable, building on the separation–optimization interface.
- **Primal–dual approximation and multiplicative weights:** reusable primal–dual analyses with vertex cover and set cover as first clients, and multiplicative weights building on the experts regret bounds of [#2874](https://github.com/cslib-community/cslib-frontier/issues/2874).
  Targets include randomized weighted majority and sampled Hedge as probabilistic computations, the regret lower bound, charged finite-precision implementations, and applications to packing and covering LPs, boosting and learning.
- **Online convex optimization:** regret bounds from projected online gradient descent ([#2983](https://github.com/cslib-community/cslib-frontier/issues/2983)) to follow-the-regularized-leader ([#3160](https://github.com/cslib-community/cslib-frontier/issues/3160)) and online mirror descent, the `Ω(GD√T)` lower bound, online Newton step for exp-concave losses, and Blackwell approachability and calibration.
  FTRL covers fixed strongly convex regularizers (the `L² / (2μ)` stability bound, Euclidean lazy projection), time-varying regularizers with local-norm bounds, and the entropic case recovering Hedge with `√(2T ln n)` regret; mirror descent covers Bregman divergences and agile OMD.
  Also finite-precision implementations.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations), reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** native augmenting-path algorithms with charged runtime, then weighted bipartite matching (including rectangular and sparse instances) and minimum-cost flow through common residual-network and duality machinery.
  Matching also covers the decomposition of `M ⊕ M*` into vertex-disjoint augmenting paths and a sparse Hopcroft–Karp entry point whose cost includes building the adjacency lists.
- **General matching** ([#3337](https://github.com/cslib-community/cslib-frontier/issues/3337)): unweighted and weighted matching in non-bipartite graphs with blossoms, through Berge's lemma, the Tutte–Berge formula and Edmonds' blossom-contraction lemma, with an executable blossom algorithm and its `O(|V|²|E|)` bound.
  Also the Gallai–Edmonds decomposition.
- **Chain decompositions** ([#3371](https://github.com/cslib-community/cslib-frontier/issues/3371)): for finite posets, Mirsky's theorem, Dilworth's theorem by Fulkerson's reduction to König's theorem, and a Hopcroft–Karp minimum chain cover with an `O(n^{5/2})` charged bound.
  Also the Greene–Kleitman theorem on `k`-chain and `k`-antichain families, Dilworth's theorem for infinite posets of finite width by compactness, the perfection of comparability graphs and their complements, weighted versions, a sparse entry point that charges building the comparability lists, and a RAM-model or Turing-machine realization of the chain-cover solver.
- **Global minimum cut** ([#3369](https://github.com/cslib-community/cslib-frontier/issues/3369)): Karger's and Karger–Stein's contraction algorithms with their per-cut bounds and the `C(n, 2)` bound on the number of minimum cuts ([#3489](https://github.com/cslib-community/cslib-frontier/issues/3489)), and Stoer–Wagner via maximum adjacency orderings in `O(n³)` and `O(n m + n² log n)` time and over real weights.
  Also Nagamochi–Ibaraki sparse certificates for `k`-edge-connectivity, Karger's near-linear algorithm, the `O((2n)^(2α))` bound on `α`-minimal cuts, the enumeration and cactus representation of all minimum cuts, and Queyranne's symmetric submodular minimization.
- **Gomory–Hu trees** ([#3422](https://github.com/cslib-community/cslib-frontier/issues/3422)): existence of cut-equivalent trees, flow-equivalence, the minimum-cut triangle inequality and the `n - 1` bound on distinct minimum-cut values, and Gusfield's construction with `n - 1` Edmonds–Karp calls returning both the parent array and edge weights `λ(u, p u)` with a charged running time ([#3285](https://github.com/cslib-community/cslib-frontier/issues/3285), [#3320](https://github.com/cslib-community/cslib-frontier/issues/3320)).
  The optional items of #3422 still need an executable maximum-flow or minimum-cut oracle over a computable ordered field such as `ℚ`, and charged time bounds for the push–relabel and Dinitz instances, which wait on charged versions of those algorithms.
- **Push–relabel maximum flow** ([#3373](https://github.com/cslib-community/cslib-frontier/issues/3373)): preflows, valid labelings, optimality at termination with a gap minimum cut, and the operation bounds of the generic Goldberg–Tarjan algorithm with an executable scheduler.
  Then a charged `TimeM` version with current-arc scanning (`O(|V|² |E|)`), the FIFO and relabel-to-front rules (`O(|V|³)`), highest-label selection (`O(|V|² √|E|)`), gap and global-relabelling heuristics, and dynamic trees (`O(|V| |E| log(|V|² / |E|))`).
- **Menger's theorem** ([#3409](https://github.com/cslib-community/cslib-frontier/issues/3409)): Menger for infinite graphs (the Erdős–Menger theorem, proved by Aharoni and Berger) and a native local or global `k`-connectivity test with a charged running-time bound.
- **Algebraic matching** ([#3052](https://github.com/cslib-community/cslib-frontier/issues/3052)): Edmonds' and Tutte's determinant criteria with Lovász's randomized test, and the Mulmuley–Vazirani–Vazirani algorithm for bipartite and general graphs (the latter in its Pfaffian form).
  The algorithmic targets are a machine-level running-time certificate for the determinant test and an RNC implementation.
- **Blocking-flow maximum flow** ([#3328](https://github.com/cslib-community/cslib-frontier/issues/3328)): level networks, the Dinitz phase lemma and the `|V| - 1` phase bound, with an executable Dinitz solver and a charged `TimeM` version using current-arc depth-first blocking-flow search (`O(|V| |E|)` per phase, `O(|V|^2 |E|)` overall).
  Also Sleator–Tarjan dynamic trees (`O(|V| |E| log |V|)`), the Even–Tarjan unit-capacity bounds `O(|E| · min(|V|^{2/3}, |E|^{1/2}))`, and Karzanov's `O(|V|^3)` preflows and push–relabel.
- **Auction algorithms** ([#3317](https://github.com/cslib-community/cslib-frontier/issues/3317)): Bertsekas's Gauss–Seidel auction for square, complete integer assignment instances, with `ε`-complementary slackness, termination within `n (C + ε) / ε + 1` bids, `n ε`-optimality and exact optimality after scaling by `n + 1`, then `ε`-scaling with its `O(n A log (n C))` bound and a charged `TimeM` implementation.
  Also the Jacobi, reverse and asymmetric auctions, sparse and rectangular instances, a bridge to the Hungarian method's potentials, and `ε`-relaxation for minimum-cost flow.
- **Graph search and shortest paths** ([#3053](https://github.com/cslib-community/cslib-frontier/issues/3053)): `TimeM` depth-first search, topological sort, Bellman–Ford distances, Kosaraju strongly connected components and linear-time 2-SAT (`TwoSAT ∈ P` witness included) are formalized.
  The Bellman–Ford predecessor tree, bridges and biconnectivity, linear-time acyclicity, bridges to Dijkstra and matrix shortest paths, and word-RAM realizations remain.
- **Minimum-cost arborescences** ([#3526](https://github.com/cslib-community/cslib-frontier/issues/3526)): the Chu–Liu/Edmonds contraction algorithm with its correctness theorem for costs in any linearly ordered additive commutative monoid ([#3491](https://github.com/cslib-community/cslib-frontier/issues/3491)), materialized `O(n³)` `TimeM` table solvers, Edmonds' optimum branchings (`IsBranching`, super-root reduction, Section 2 weight-shift reductions) and binary-weight polynomial-time certificates (`P`, Theorem 1).
  Sparse `O(n m)` implementations, Tarjan's `O(m log n)` and the Gabow–Galil–Spencer–Tarjan `O(m + n log n)` implementations, and Edmonds' branching polytope (Theorem 2) remain open.
- **Matroids** ([#2018](https://github.com/cslib-community/cslib-frontier/issues/2018)): Edmonds' matroid intersection theorem with an exchange-graph augmenting-path solver, König's theorem via partition matroids, exact independence-oracle query counts, and `TimeM` costs for the solver's host computation kept separate from those counts.
  Extend to weighted matroid intersection.
- **Submodular optimization** ([#3145](https://github.com/cslib-community/cslib-frontier/issues/3145)): constraints and approximation bounds beyond the cardinality-constrained `1 - 1/e` greedy: the Fisher–Nemhauser–Wolsey `1/(p+1)` greedy over `p`-systems (`1/2` over a matroid), the `α/(p+α)` bound for greedy with an `α`-approximate marginal-gain oracle, the continuous greedy with pipage rounding for `1 - 1/e` over a matroid, knapsack constraints and non-monotone objectives.
  Value-oracle and independence-oracle calls are charged separately from each other and from their concrete realizations.
- **Stable matching** ([#2990](https://github.com/cslib-community/cslib-frontier/issues/2990)): deferred acceptance and its theory (stability, optimality, the lattice, strategy-proofness), extended to Roth's impossibility theorem for every `n ≥ 3`, incomplete lists with unequal sides (the same theory and the rural hospitals theorem), many-to-one college admissions with the capacitated rural hospitals theorem, ties, rotations and the stable-matching poset, and stable roommates.
  A charged native implementation should run in `O(n^2)` time.
- **Housing markets and top trading cycles** ([#3286](https://github.com/cslib-community/cslib-frontier/issues/3286)): the Shapley–Scarf model with TTC as the unique strict-core and competitive allocation, individually rational, Pareto efficient and strategy-proof; house allocation with existing tenants (Abdulkadiroğlu–Sönmez), Ma's characterization of TTC, group strategy-proofness, indifferences (top trading absorbing sets), and a charged `O(n^2)` TTC.
- **Interval dynamic programming** ([#3357](https://github.com/cslib-community/cslib-frontier/issues/3357)): optimal binary search trees with Yao's quadrangle-inequality lemma, root monotonicity and Knuth's quadratic algorithm with candidate-scan counts in `TimeM`, and the Hu–Tucker and Garsia–Wachs `O(n log n)` algorithms for alphabetic trees.
  Also matrix-chain multiplication and optimal polygon triangulation as instances of the generic interval recurrence, which in general fail the quadrangle-inequality hypotheses, Knuth's sharper candidate count, SMAWK and Monge-matrix speedups, and a Word-RAM realization.
- **Classical approximation algorithms** ([#2869](https://github.com/cslib-community/cslib-frontier/issues/2869)): greedy set cover, maximal-matching vertex cover and the MST tour for metric TSP, with machine-level polynomial-time certificates for greedy set cover and for Kruskal-based TSP tours on encoded matrices, and Christofides' `3/2` for metric TSP ([#3055](https://github.com/cslib-community/cslib-frontier/issues/3055)) with a polynomial-time minimum-weight perfect matching (Edmonds' blossom) and a tightness family approaching `3/2`.
  Karlin–Klein–Oveis Gharan's `3/2 - 10^{-36}` is possibly a long-range target.
  LP-based and primal–dual analyses belong to the primal–dual direction.
- **Steiner tree** ([#3309](https://github.com/cslib-community/cslib-frontier/issues/3309)): the MST 2-approximation, metric and on graphs through the metric completion, with the sharp factor `2 (1 - 1/|R|)`; Kou–Markowsky–Berman's leaf bound `2 (1 - 1/ℓ)` and their pruning steps; Zelikovsky's `11/6` and Robins–Zelikovsky's `1.55` greedy algorithms; and the Byrka–Grandoni–Rothvoß–Sanità LP-rounding bounds (`1.694` and `ln 4 + ε`).
  Also NP-hardness of the decision version (Karp, within [#2904](https://github.com/cslib-community/cslib-frontier/issues/2904)), even with unit weights by reduction from vertex cover, and a polynomial-time certificate for the heuristic with an executable shortest-path oracle.
- **Metric k-center** ([#3281](https://github.com/cslib-community/cslib-frontier/issues/3281)): Gonzalez's farthest-first 2-approximation with a machine-level running time, and its matching hardness: the combinatorial dominating-set gap, NP-completeness of dominating set on encoded graphs ([#3416](https://github.com/cslib-community/cslib-frontier/issues/3416)), and that a polynomial-time `ρ`-approximation with `ρ < 2` implies `P = NP` ([#3515](https://github.com/cslib-community/cslib-frontier/issues/3515)).
  Also the Hochbaum–Shmoys threshold algorithm, k-supplier and k-median.
- **State-space search** ([#3669](https://github.com/cslib-community/cslib-frontier/issues/3669)): search problems and two-player games given implicitly by actions, results and goal or terminal tests, as in Russell and Norvig's *Artificial Intelligence: A Modern Approach*.
  Generic best-first search over an abstract frontier with its uninformed instances, A* with admissible and consistent heuristics, and minimax with alpha-beta pruning.
  Costs are node expansions and generations counted in CSLib's query model, including the bound that A* with a consistent heuristic expands each state at most once.

### Sorting and selection

- **Comparison selection** ([#3279](https://github.com/cslib-community/cslib-frontier/issues/3279)): median-of-medians selection in CSLib's comparison-query model, correct for total preorders, with at most `37 n` comparisons under every oracle for groups of five, then sharper constants (a six-comparison median of five, reusing the group comparisons in the partition) and group sizes such as three or seven.
  Also the `5.4305 n` bound for the refined `PICK` of Blum, Floyd, Pratt, Rivest and Tarjan, Dor and Zwick's `2.95 n` median bound, and a word-RAM implementation with charged instruction counts.
- **Comparison lower bounds for selection** ([#3279](https://github.com/cslib-community/cslib-frontier/issues/3279)): `n − 1` comparisons for the minimum and `⌈3n/2⌉ − 2` for the minimum and maximum together (Pohl's adversary), with algorithms that attain them, in the same comparison-query model.
  Also Kislitsyn's `n + ⌈log₂ n⌉ − 2` for the second smallest, and lower bounds for the median and for general ranks, such as Bent and John's `2n − o(n)`.

### Online algorithms and competitive analysis

- **Competitive-analysis framework:** request sequences, online strategies, offline optima and competitive ratios with additive constants, distinguishing deterministic and randomized strategies and oblivious and adaptive adversaries.
  Compare algorithms in the same action and cost model, including initialization.
- **Adaptive search trees** ([#3143](https://github.com/cslib-community/cslib-frontier/issues/3143)): for splay trees, the Access Lemma with arbitrary positive weights, the Balance, Static Optimality, Static Finger and Working Set theorems with explicit constants, the update bounds, Sleator–Tarjan's Unified Theorem and Cole's Dynamic Finger theorem; and a BST access-and-rotation model with Wilber-style lower bounds.
  State dynamic optimality as a conjectural research target with explicit strategy and sequence quantifiers.
- **Beyond deterministic ski rental and list update** ([#3057](https://github.com/cslib-community/cslib-frontier/issues/3057), [#3492](https://github.com/cslib-community/cslib-frontier/issues/3492), [#3552](https://github.com/cslib-community/cslib-frontier/issues/3552)): mixture and behavioural randomized strategies against oblivious and adaptive adversaries; discrete (`1/(1 - (1 - 1/B)^B) ≤ e/(e-1)`) and continuous-time randomized ski rental, plus the asymptotic `e/(e-1)` lower bound with an additive constant; randomized (BIT, COMB) and dynamic list update.
  Also randomized paging (marking's `2 H_k` bound, the `H_k` lower bound, and McGeoch–Sleator's `H_k` partitioning algorithm).
- **Optimal stopping:** from the rank-based secretary problem, the `½` prophet inequality ([#2913](https://github.com/cslib-community/cslib-frontier/issues/2913)) and the i.i.d. `1 - 1/e` bound ([#3092](https://github.com/cslib-community/cslib-frontier/issues/3092)) to the tight i.i.d. constant `≈0.745`, prophet secretary and random-order models, and matroid and multiple-choice prophet inequalities.
  Also the full-information secretary problem, a general mixtures theorem for randomized rules, and the posted-price mechanism corollary.
- **`k`-server** ([#3287](https://github.com/cslib-community/cslib-frontier/issues/3287)): the deterministic lower bound `k` on every metric with at least `k + 1` points and the `k / (k - h + 1)` bound against `h < k` offline servers (Manasse–McGeoch–Sleator), `k`-competitiveness of Double Coverage on the line (Chrobak–Karloff–Payne–Vishwanathan) and on trees (Chrobak–Larmore), and the work-function algorithm's `2k - 1` bound (Koutsoupias–Papadimitriou).
  Also the `k`-server conjecture as a research target with explicit quantifiers, the `k = 2` case on every metric, randomized `k`-server, and the offline optimum by min-cost flow.
- **Online bin packing** ([#2964](https://github.com/cslib-community/cslib-frontier/issues/2964)): deterministic online packers with Yao's `3/2` lower bound and First Fit's `17/10`, bracketing the deterministic asymptotic ratio; the stronger lower bounds of Brown–Liang (`1.536`), van Vliet (`1.5401`) and Balogh–Békési–Galambos (`248/161`) and the fully adaptive constructions; Harmonic-type upper bounds; and randomized lower bounds.
  Online bin packing should also be an instance of the competitive-analysis framework, charging `1` per opened bin, with online packers as deterministic strategies and a non-competitiveness corollary.

### Algorithmic game theory ([#2900](https://github.com/cslib-community/cslib-frontier/issues/2900))

- **Computing equilibria** ([#3149](https://github.com/cslib-community/cslib-frontier/issues/3149)): membership in `PLS` and PLS-completeness of finding a pure Nash equilibrium of a congestion game (Fabrikant–Papadimitriou–Talwar), including the symmetric case, by reduction from local Max-Cut (PLS-complete by Schäffer–Yannakakis or by reductions from `LocalOpt`), through an explicit local-search problem interface and succinct game encodings; polynomial-time algorithms for symmetric network congestion games; exponentially long better-response paths.
  PPAD-completeness of computing mixed Nash equilibria of finite games.
- **Bimatrix games and Lemke–Howson** ([#3334](https://github.com/cslib-community/cslib-frontier/issues/3334), [#3391](https://github.com/cslib-community/cslib-frontier/issues/3391)): extending the Lemke–Howson parity argument to degenerate bimatrix games by lexicographic perturbation; the Lemke–Howson path as a standalone algorithm; the Savani–von Stengel exponential lower bound (two-player Nash in `PPAD` via Shapley's orientation, rational vertex bit-size bounds and `BimatrixCode.BimatrixNash_mem_PPAD` is in `Bimatrix/PPAD.lean`, with `PPAD`-completeness tracked separately).
- **Equilibrium concepts and dynamics:** last-iterate convergence of no-regret dynamics; bandit feedback and sampled play; convergence time of better-response dynamics in potential games.
- **Price of anarchy:** Wardrop equilibrium existence and essential uniqueness for continuous nondecreasing latencies (Beckmann's convex potential); the Pigou bound for general latency classes and polynomial latencies of bounded degree; worst-case networks for latency classes without the constant functions (parallel links and unions of paths); the M/M/1 and M/G/1 delay bounds (Roughgarden 2003); Braess's paradox; weighted and mixed-strategy atomic congestion games.
- **Price of stability and potential games** ([#3035](https://github.com/cslib-community/cslib-frontier/issues/3035)): the price of stability by the potential method, including the `H_k` bound for network cost-sharing games, the tight price of stability of affine congestion games below the potential-method bound `2`, and price-of-stability bounds for undirected and weighted network design.
  Strong Nash equilibria of fair cost-sharing games, with their price of anarchy, their existence in special network classes (Epstein–Feldman–Mansour 2009) and a network without one; the Monderer–Shapley characterization of potential games as congestion games.

### Mechanism design ([#2947](https://github.com/cslib-community/cslib-frontier/issues/2947))

The directions below extend the single-parameter, Groves/VCG, optimal-auction and Bayes–Nash foundations in `GameTheory/Mechanism`, including revenue equivalence and the first-price equilibrium for i.i.d. uniform values ([#3173](https://github.com/cslib-community/cslib-frontier/issues/3173)).

- **Single-parameter corollaries:** the sponsored-search payment formula (rank-by-bid allocation with slot click-through rates) and the greedy knapsack rule with its monotonicity and ½-approximation.
  State allocation algorithms with charged running time, so that approximation and truthfulness are both proved for an actual algorithm.
- **Revenue maximization beyond the regular DSIC case:** ironing for irregular distributions; regular distributions whose virtual valuation is unbounded below at `0`, like `f(v) = 2v` on `[0, 1]`, with explicit zero-bid treatment.
  Optimality over Bayesian incentive-compatible mechanisms (revelation principle), measurable virtual-welfare maximizers for finite feasible sets, and distributions without a bounded density (atoms, unbounded support).
- **Bayes–Nash equilibria of auctions:** the symmetric first-price equilibrium `b(v) = E[max of the other values | it is below v]` for general i.i.d. priors with densities and its uniqueness (Hartline, *Mechanism Design and Approximation*, §2.8–2.9); the all-pay auction; truthful bidding as a Bayes–Nash equilibrium of every DSIC mechanism.
  The exact optimal revenue `(n - 1 + 2^(-n)) / (n + 1)` for i.i.d. uniform values (`5/12` for two bidders).
- **Multi-parameter characterizations:** Groves mechanisms as the only DSIC welfare maximizers on rich valuation domains (Green–Laffont, Holmström), and limits of VCG such as revenue monotonicity and collusion.

### Social choice ([#3282](https://github.com/cslib-community/cslib-frontier/issues/3282))

Social welfare and social choice functions on strict rankings, from Arrow's impossibility theorem (Geanakoplos's pivotal-voter proof) onward.

- **Strategy-proofness:** the Gibbard–Satterthwaite theorem for social choice functions onto at least three alternatives, for example by Reny's side-by-side proof (Economics Letters 70, 2001), sharing the pivotal-voter infrastructure with Arrow's theorem.
- **Strategy-proofness beyond the full domain:** the Gibbard–Satterthwaite theorem allowing individual indifference, Gibbard's 1977 theorem that strategy-proof random social choice functions are mixtures of unilateral and duple rules, and escape routes such as single-peaked domains, with the median voter rule and Moulin's characterization of strategy-proof rules there.
- **Characterizations:** May's theorem (majority rule is the only anonymous, neutral, positively responsive rule on two alternatives), the individual-weak-order corollary of Arrow's theorem by an IIA reduction to strict profiles, and the infinite-electorate counterexample from a nonprincipal ultrafilter (Fishburn 1970).
- **Quantitative Arrow** ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)): Kalai's Fourier-analytic bound on the probability of a Condorcet paradox and its robust version via FKN.
- **Computational social choice:** polynomial-time manipulation of greedy-manipulable rules, NP-hardness of manipulating second-order Copeland (Bartholdi–Tovey–Trick 1989), and the complexity of winner determination for Dodgson and Kemeny rules, with explicit profile encodings and charged running time.

### Structural graph algorithms

- **Dynamic programming over tree decompositions** ([#2927](https://github.com/cslib-community/cslib-frontier/issues/2927)): a reusable evaluator over a supplied rooted decomposition with state-space, transition, join and runtime bounds, and an executable FPT `TimeM` independent-set program charging its operations on materialized tables ([#3295](https://github.com/cslib-community/cslib-frontier/issues/3295)).
  Clients: coloring and SAT/CSP decision and counting, each naming the graph whose width is measured; runtimes are stated in the number of vertices.
- **Treewidth structure** ([#2927](https://github.com/cslib-community/cslib-frontier/issues/2927)): an encoded treewidth parameter connected to `FPT`, nice decompositions, treewidth under minors, and the grid and separator characterizations of treewidth.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style theorem with computable parameter dependence on width and formula size.
  Keep the supplied decomposition and its encoding explicit; certify decomposition finding separately.
  Connect the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Exact fixed-field sampling:** fair-bit samplers for fixed finite fields such as `F4`, with encoded arithmetic, certified circuit evaluation over finite semirings and gate-code validation ([#2770](https://github.com/cslib-community/cslib-frontier/issues/2770)), used by circuit-bound VOLE ([#2688](https://github.com/cslib-community/cslib-frontier/issues/2688)).
  Separate endpoints: output and count validation, native circuit-bound VOLE execution ([#2765](https://github.com/cslib-community/cslib-frontier/issues/2765), [#643](https://github.com/cslib-community/cslib-frontier/issues/643), [#2738](https://github.com/cslib-community/cslib-frontier/issues/2738)), growing extension-field arithmetic, raw-bit adversarial transport ([#2744](https://github.com/cslib-community/cslib-frontier/issues/2744)) and fresh-session amplification.
- **Entropy-optimal sampling from fair coins** ([#3360](https://github.com/cslib-community/cslib-frontier/issues/3360)): the Knuth–Yao bounds `H(p) ≤ E[T]` for every DDG tree generating `p` and `E[T] < H(p) + 2` with optimality for the Knuth–Yao tree, and the dyadic equality characterization, for distributions on a finite type and then with countable support and infinite entropy.
  For rational `p`, the Knuth–Yao sampler as a native fair-coin program with certified output law and expected time (an `IsPPTOn`-style certificate in expected time), as in the finite-precision entropy-optimal samplers of Saad, Freer, Rinard and Mansinghka.
- **Markov-chain sampling** ([#2857](https://github.com/cslib-community/cslib-frontier/issues/2857)): total-variation mixing bounds by coupling, path coupling ([#2933](https://github.com/cslib-community/cslib-frontier/issues/2933)), conductance, canonical paths and spectral gaps, and an FPRAS for colorings in the sense of `Classes/FPRAS`, charging the estimator's Glauber updates.
  Implement Metropolis sampling for encoded rational target weights, charging initialization, arithmetic and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling** ([#3039](https://github.com/cslib-community/cslib-frontier/issues/3039)): the Jerrum–Valiant–Vazirani equivalence of FPRAS and FPAUS for self-reducible witness families, including the converse FPRAS ⇒ FPAUS by rejection sampling and self-reductions fixing several symbols per step.
  Also Sinclair and Jerrum's reduction from polynomial-error counting.
  Instantiate both directions for concrete relations such as DNF assignments.
- **Approximate counting of matchings and permanents:** randomized approximate counting for matchings and permanents of nonnegative rational matrices through explicit mixing and reduction theorems.
  Reuse the coupling and expander APIs and connect to the separate Stockmeyer oracle-counting track where their hypotheses agree.
- **Permanent bounds** ([#3377](https://github.com/cslib-community/cslib-frontier/issues/3377)): Brégman's upper bound for 0/1 matrices and bipartite perfect matchings, with equality for disjoint unions of `K_{d,d}`, and its extensions to nonnegative real matrices (for example Soules 2000).
  The van der Waerden lower bound for doubly stochastic matrices (Egorychev–Falikman, or Gurvits's capacity proof), the Kahn–Lovász bound for perfect matchings of general graphs, and their use in approximate-counting analyses.

### Constructive probabilistic methods

- **Moser–Tardos resampling** ([#3096](https://github.com/cslib-community/cslib-frontier/issues/3096)): extend the formalized variable-form, symmetric `e p (d + 1) ≤ 1`, Section 6 lopsided and constructive `k`-SAT resampling bounds with parallel and derandomized versions (Theorems 1.3–1.4) and native sampling and event-detection costs.
  Build the Kolmogorov form's decoder ([#3043](https://github.com/cslib-community/cslib-frontier/issues/3043)) as a multi-tape machine taking the formula, transferring it to `condPlain`.
- **Conditional expectations and pessimistic estimators:** algorithmic alteration, and coloring, MAX-CUT or combinatorial-construction clients of the certified greedy choice rule for pessimistic estimators.
  Preserve the quantitative guarantee when converting an existence argument into a deterministic or randomized algorithm.
- **Small sample spaces** ([#2935](https://github.com/cslib-community/cslib-frontier/issues/2935)): searching a `k`-wise independent sample space for an assignment as good as a uniformly random one on clauses of at least `k` distinct literals, with polynomial-time certificates for the search over the three-wise parity space and the trinomial-field space for fixed `k > 3`.
  Extend to small-bias and almost `k`-wise independent spaces and their clients.

### Randomized verification and fingerprinting

- **Fingerprinting** ([#2980](https://github.com/cslib-community/cslib-frontier/issues/2980)): Freivalds' matrix-product verifier, Karp–Rabin fingerprints (a random evaluation point over a finite field, or a random prime modulus with explicit prime-counting bounds), a rolling-hash pattern matcher with charged updates and a union bound over all windows, and the private-coin `O(log n)` equality protocol.
  Native machine or RAM realizations with bit-level arithmetic costs are a separate endpoint.

### String algorithms

- **Burrows–Wheeler transform** ([#3354](https://github.com/cslib-community/cslib-frontier/issues/3354)): the rotation-sort transform with its index, the LF-mapping, the decoding formula, invertibility and a table-driven `TimeM` decoder with exactly `|w|` LF steps, with charged construction of the rank tables and of the forward transform, counting the rotation sort's comparisons.
  Move-to-front and entropy coding of the last column, compression bounds in the empirical entropy `H_k` (Manzini), FM-index backward search and rank/select structures, and the link to suffix arrays for sentinel-terminated words ([#3331](https://github.com/cslib-community/cslib-frontier/issues/3331)).
- **Suffix arrays** ([#3331](https://github.com/cslib-community/cslib-frontier/issues/3331)): the suffix-array specification, a sort-based reference construction with counted comparisons, Kasai's LCP construction with at most `2|w|` comparisons, and binary-search matching with at most `2|p|(⌊log₂ n⌋ + 1)` comparisons.
  Charged linear-time construction for integer alphabets (SA-IS or Kärkkäinen–Sanders DC3), Manber–Myers `O(|p| + log n)` search using precomputed LCP values, suffix trees (Ukkonen or McCreight) and their equivalence to suffix arrays with LCP arrays, and applications such as longest repeated substring and the Burrows–Wheeler transform.
- **Z-algorithm** ([#3516](https://github.com/cslib-community/cslib-frontier/issues/3516)): the Z-function specification and Gusfield's Z-algorithm with exact values and at most `2|s| - 3` character comparisons on every input, a bound that `a ^ (n - 1) b` attains for every `n`, and exact matching through the Z-function of `p ++ t`, equal to the KMP output, with at most `2(|p| + |t|) - 3` comparisons.
  Linear conversions between Z-values and the KMP prefix function, applications such as Main–Lorentz repetition finding, and a shared string module for the common-prefix extension used by Kasai's construction and the Z-algorithm.
- **Multi-pattern matching** ([#3358](https://github.com/cslib-community/cslib-frontier/issues/3358)): Aho–Corasick with valid failure and output tables from the level-order construction, exact reporting of all occurrences, and the scan bound and transition count of Aho and Corasick's paper.
  An explicit integer-state trie with a charged goto table and its linear construction, linear charged level and queue bookkeeping in the failure construction, a construction that charges each shared trie state once, the deterministic automaton without failure transitions, and machine-level or RAM realizations.
- **Edit distance and longest common subsequence** ([#3472](https://github.com/cslib-community/cslib-frontier/issues/3472)): Wagner–Fischer edit distance under arbitrary letter costs and the LCS length, each with an optimal witness and exact `(|x| + 1)(|y| + 1)` `TimeM` cost, related through the insertion–deletion distance.
  For unit costs, the metric axioms and equality with the least number of single-letter edits; Wagner–Fischer's trace equivalence for general costs; Hirschberg's linear-space alignment; a machine-level polynomial-time computation; Ukkonen's and Myers' `O((|x| + |y|) d)` algorithms; the Masek–Paterson speedup; and `OV` hardness ([#3037](https://github.com/cslib-community/cslib-frontier/issues/3037)).
- **Palindromes** ([#3372](https://github.com/cslib-community/cslib-frontier/issues/3372)): the maximal palindromic radii at all `2|w| + 1` centers, the characterization of palindromic factors and prefixes by the radii, a longest palindromic factor, and Manacher's algorithm with exact radii and at most `3|w|` character comparisons.
  Also Manacher's on-line formulation, reporting palindromic prefixes as letters arrive with a per-letter amortized bound; palindromic trees (eertrees) and counting distinct palindromic factors, of which there are at most `|w| + 1`; and the parallel algorithms of Apostolico, Breslauer and Galil.

## Machines, RAM and data structures

- **Efficient universal simulation** ([#800](https://github.com/cslib-community/cslib-frontier/issues/800)): A universal function that runs in time `O(N + poly(D, M) · (t + 1) log(t + 2))`, for encoded input length `N`, description length `D` and largest input symbol `M`, with a storage bound in terms of the simulated machine's space rather than its time.
  Both a clocked form and an unclocked form that runs until the simulated machine halts are in scope.
- **Plain computability** ([#862](https://github.com/cslib-community/cslib-frontier/issues/862)): Complete the plain calculus ([#608](https://github.com/cslib-community/cslib-frontier/issues/608)) and delete the tidy calculus, keeping only a machine-level kernel inside the Machines layer.
- **Certificate APIs and automation** ([#1155](https://github.com/cslib-community/cslib-frontier/issues/1155)): Predictable certificate search, with fixed heartbeat budgets on regression goals, failures that name the subterm lacking a certificate, and cheap syntax-directed composition for glue code, using Cook–Levin and GGM as regression clients.
  Improve configuration views, tape partitions and handoff identities only where several clients benefit, keeping machine transitions out of global simp.
- **Certificate coverage** ([#1155](https://github.com/cslib-community/cslib-frontier/issues/1155)): Infer encodings for ordinary functional expressions through constructor, projection, lookup and composition rules, and generalize list, bounded-table, cache and nested-loop invariants where clients need them.
  Keep time, workspace and output-size bounds separate through composition, apply cumulative streaming contracts to captured iteration and nested loops, and develop general open-program composition.
- **Certified PRG stretching** ([#2784](https://github.com/cslib-community/cslib-frontier/issues/2784)): Certify PRG stretching with seed length, rounds and generator cost kept separate.
  A related target is the adaptive arbitrary-word cipher with its hash-then-MAC/EtM construction ([#2749](https://github.com/cslib-community/cslib-frontier/issues/2749)).
- **Mathlib TM2:** Sublinear work-space comparisons and a linear-space forward simulation.
- **Single-tape lower bounds** ([#2884](https://github.com/cslib-community/cslib-frontier/issues/2884)): Crossing-sequence lower bounds for CSLib `SingleTapeTM` deciders, including the quadratic palindrome lower bound with a matching `O(n²)` single-tape decider.
  A linear-time multi-tape palindrome decider gives the one-tape/two-tape time separation.
  The gap theorem that single-tape deciders in time `o(n log n)` accept only regular languages ([#2965](https://github.com/cslib-community/cslib-frontier/issues/2965)), and its nondeterministic analogue under the accept measure.
- **Generic RAM:** Uniform arbitrary-program dispatch with general width-selection and input-fit theorems, and simulation of operations by programs over smaller bases.
  Structured programs and time classes over arbitrary value domains with weighted or bit costs, simulations between instances, and the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Word RAM:** An AC⁰ basis, wider-fragment and Turing-machine simulations, transfer of Anthropic's modular machine and APSP algorithms, and size-based width selection with an input-fit guarantee and explicit overhead.
  Transfer of bounded-error (Monte Carlo) and adaptive-adversary cell-probe lower bounds, and the Horn-SAT, 2SAT, matching and domino-tiling clients.
- **Randomized Word RAM** ([#1124](https://github.com/cslib-community/cslib-frontier/issues/1124)): Expected-time rules for unbounded almost-surely terminating structured loops, random-tape equivalence, and BPP/RP/ZPP simulation bridges for the randomized word RAM.
- **Sharper native Exact Triangle exponent** ([#2423](https://github.com/cslib-community/cslib-frontier/issues/2423)): Prove an `Oκ(n^2.9983)` bound, the source's stated exponent, for the automatic box-backed Exact Triangle host under the library's native conventions.
- **Memory-oracle realization** ([#2205](https://github.com/cslib-community/cslib-frontier/issues/2205), [#2213](https://github.com/cslib-community/cslib-frontier/issues/2213)): Verify Word-RAM algorithms as memory-oracle programs refined to native programs by game-hop proofs, replacing hand-stepped code proofs.
  Realization covers memory queries, certified word-sized glue, binds, branches and bounded loops, and charges local work and every loop iteration.
  A realized client is one initialized native program whose clock includes input installation, control and halt.
- **Memory-oracle clients** ([#2205](https://github.com/cslib-community/cslib-frontier/issues/2205), [#2290](https://github.com/cslib-community/cslib-frontier/issues/2290), [#2289](https://github.com/cslib-community/cslib-frontier/issues/2289)): Realize the stack, the framed queue with faithful allocation, the binary and Fibonacci heaps with their Dijkstra consumers, the indexed min-priority queue, and Karger–Stein, keeping each client's original word envelope and bounds.
  Karger–Stein also needs randomized realization adapters, its contraction implementation and a recursive frame stack.
  The direction also covers generic stateful and whole-client composition and the Fibonacci heap's execution migration.
- **Stateful Word-RAM algorithms:** Word-RAM controllers for larger adaptive and iterative clients, including the two-stack queue and timeline-editing controllers, with reusable allocation and deallocation, shrinking, and live and peak space accounting.
  Ownership and recursive procedures, and model realizations for cell probes, caches and randomness.
- **Data-structure extensions:** Present and historical queries for the retroactive interface, balancing and heap or RAM representations of search trees, uniform preprocessing and dynamic updates for fusion trees, deletion and predecessor for van Emde Boas sets, and deallocation, shrinking and compiled client controllers for the doubling array.
- **Typed-call evaluator:** An evaluator for fixed-program Word-RAM clients that returns the typed observation, final state and halt-inclusive instruction cost, so that the prefix-sum clients no longer assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#949](https://github.com/cslib-community/cslib-frontier/issues/949)): Lift the operation-count helpers to `IndexedMinPQ`, and parameterize flat-program operation-sequence execution (`RunsOps`) over `PQCode` so that `BinaryHeap` and `FibonacciHeap` share one generic `run_ops_exact` theorem.
  Factor a common `ShortestPathSpec p bound` predicate across `LogLinearSpec`, `FibonacciSpec` and `FibonacciLinearSpec`.
- **Perfect hashing** ([#3276](https://github.com/cslib-community/cslib-frontier/issues/3276)): the static FKS two-level table over typed cells, with 3-probe lookups, at most `5n + 2` cells, and construction in expected `O(n)` seed draws and hash evaluations.
  Its word-RAM realization with `w`-bit seeds and headers, charged bucketing and layout, an unbounded Las Vegas construction and a bridge to `w`-bit cell probes.
  FKS's `k x mod p mod s` family with its `n + o(n)` refinement and deterministic construction, dynamic perfect hashing (Dietzfelbinger et al.), and the Fredman–Komlós lower bound on the description size of perfect hash families.
- **Ropes** ([#3670](https://github.com/cslib-community/cslib-frontier/issues/3670)): a persistent sequence over an arbitrary element type, stored as an AVL-balanced binary tree with bounded non-empty chunks at its leaves and verified against `List`.
  Indexing, concatenation by join and positional splitting, with insertion, range erasure, extraction and replacement derived from split and join.
  Explicit cost bounds in `TimeM` on the same definitions, counting internal nodes inspected and elements copied: join linear in the height difference and split logarithmic in the length.
- **B-trees** ([#3674](https://github.com/cslib-community/cslib-frontier/issues/3674)): comparison bounds for B-tree operations in CSLib's query model, with linear and binary in-node search, and the `⌈log₂(n + 1)⌉` comparison lower bound for search.
  Read-only operations behind a node-access oracle, whose query counts equal the node-visit counts.
  B+-trees, with only separator keys in interior nodes and every entry in a leaf: structure, queries, updates, bulk loading and the same cost bounds.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** Work–span semantics for a parallel language or PRAM model whose computation DAGs feed the unit-time DAG scheduling bounds of `Algorithms/Lean/Scheduling/Brent.lean`, followed by prefix scan, sorting and graph primitives with both work and span bounds.
  State processor access, synchronization and scheduling overhead explicitly, including work stealing (Blumofe–Leiserson).
- **Memory hierarchies:** External-memory and ideal-cache models with explicit capacity and block-size parameters, with scanning, B-tree operations, blocked matrix multiplication and cache-oblivious sorting as clients.
  Connect arithmetic-step, memory-access and cache-miss bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity:** LOCAL and CONGEST models with explicit identifiers, round, message-size and randomness conventions, with locality lower bounds, communication-to-round reductions and corresponding algorithmic examples.
  Targets include general graphs with port numbering, Linial's `O(Δ²)` colouring, `(Δ + 1)`-colouring and MIS on bounded-degree graphs, CONGEST message bounds, and randomized LOCAL algorithms.
- **Luby's MIS** ([#3270](https://github.com/cslib-community/cslib-frontier/issues/3270)): the random-priority variant of Luby's algorithm with Las Vegas correctness, the half-edge removal lemma, `O(log n)` phases except with probability `n^-c`, the expected phase count, and a LOCAL message-passing formalization with `O(log n)` rounds.
  Luby's original marking algorithm with its pairwise-independent analysis and NC derandomization, Ghaffari's `O(log Δ) + poly(log log n)` bound, and the Kuhn–Moscibroda–Wattenhofer lower bounds.
- **Locality on cycles and paths** ([#3009](https://github.com/cslib-community/cslib-frontier/issues/3009)): Cole–Vishkin colouring, Linial's `log*` lower bound, and round bounds of the form `(log* n) / 2 + c` for 3-colouring and MIS on cycles, with matching upper and lower constants.
  The Chang–Studený–Suomela `O(1)`/`Θ(log* n)`/`Θ(n)` classification of LCL problems on directed cycles, with the tight `½ log* n + O_|L|(1)` bound for flexible problems, extended to LCLs with inputs, paths and undirected cycles.
- **Fault-tolerant agreement** ([#3261](https://github.com/cslib-community/cslib-frontier/issues/3261), [#3494](https://github.com/cslib-community/cslib-frontier/issues/3494)): Synchronous Byzantine agreement with the `n ≤ 3t` impossibility, the connectivity bound `κ ≥ 2t + 1` on general graphs (Fischer–Lynch–Merritt), protocols for all `n > 3t`, and the `t + 1` round lower bound (Fischer–Lynch).
  It also covers authenticated agreement for any `n > t`, protocols with polynomially many messages, weak agreement, the Byzantine firing squad, approximate-agreement and clock-synchronization bounds, and randomized agreement.

## Coverage and reuse

The long-term bar is to support formalizing every paper in the [Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/), with the additional work per paper increasingly its new mathematics: standard models, representation changes, reductions, resource certificates and proof techniques come from the library.
Use a growing, source-pinned sample of papers, including some chosen after an API was designed, as demanding clients, and promote recurring obligations into shared APIs only after reuse is demonstrated.

- **Arora–Barak coverage** ([#4711](https://github.com/cslib-community/cslib-frontier/issues/4711)): audit the draft against library statements and track remaining endpoints, including formal-measure density amplification with the additive loss in Razborov–Rudich Theorem 5.1(b) (omitted in draft Theorem 22.3).
- **Measure postprocessing** ([#2732](https://github.com/cslib-community/cslib-frontier/issues/2732)): Canonical full-L1 total variation contracts under measurable maps of arbitrary finite measures, including unequal masses.
  Its consumer is the Gaussian projection and mod-one bound ([#2734](https://github.com/cslib-community/cslib-frontier/issues/2734)).
- **Finite weighted measure mixtures:** Bound the full-L1 distance when both the finite component measures and their nonnegative weights change, keeping the comparison components' total masses explicit so that neither probability normalization nor equal masses is required.
  The tagged finite-PMF form supplies the error-composition step for the Regev LWE experiment ([#2767](https://github.com/cslib-community/cslib-frontier/issues/2767)); identifying and bounding its conditional laws belongs to that issue.
- **Gaussian density and projection laws** ([#2733](https://github.com/cslib-community/cslib-frontier/issues/2733)): Identify the positive-width normalized Gaussian weight with a scaled standard Gaussian, whose scalar projections have variance `(s ‖z‖)² / (2π)`, including the zero vector and dimension zero.
  Prove the discrete-coset convolution projection and mod-one bound ([#2734](https://github.com/cslib-community/cslib-frontier/issues/2734)); efficient sampling and the quantum reduction belong to [#1213](https://github.com/cslib-community/cslib-frontier/issues/1213).
- **One sensitivity API:** Define the sensitivity measures over any `Fintype` in CSLib and drop the separate measures of the sensitivity-separation development.
- **Indicator-expectation and conversion lemmas:** Factor the indicator-expectation identities from PCP's second-moment calculation, and recurring cardinality and logarithm conversions, once a second client benefits.
- **Divide-and-conquer recurrences** ([#3042](https://github.com/cslib-community/cslib-frontier/issues/3042)): A master theorem over `ℕ` with explicit constants for inequality recurrences in all three polynomial cases, with `IsBigO` forms, matching `Θ` bounds for equality recurrences, and case 3 under the general regularity condition.
  Move hand-solved recurrences onto it where the generic constant suffices, keeping CSLib's sharper merge-sort bound and the halving lemma, the sharp tool for `b = 2`.

### OpenAI math results ([#1002](https://github.com/cslib-community/cslib-frontier/issues/1002))

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the openai/math release, and extract the in-scope results, both headline theorems and minor lemmas useful in their own right.
Prove each against cslib-frontier's definitions from the cited manuscript's exact statement with its version pinned, labelling unrefereed results; a source formalization is a reference, not evidence.
The openai/math formalizations are Apache 2.0, as is cslib-frontier, so adaptation with attribution is permitted; the rewrites state no license and are only read and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/cslib-frontier/issues/1538)): A `#k`-SAT model counter running in time `2^{O_k(n log log n / √log n)}` at arbitrary density, by recursive tensor contraction.
  The intended route combines the fixed-density bound `2^{O_{k,D}(n / √log n)}` (Theorem D.1 with `ℓ = 1`) with the Lemma D.2 construction, applied natively to the model-counter interface.
- **Exact optimization:** Exact MAX-SAT score distributions and optima in contraction time measured by literal occurrences plus clauses, with `2^{O_{k,c}(n / √log n)}` time and polynomial space for sparse fixed-width instances, and native extraction of an optimizing assignment.
  Neither these bounds nor ordinary SAT sparsification gives a variable-count rate for dense exact MAX-SAT.
- **Large weights:** Exact contraction of natural tensor tables whose bit lengths are polynomial in the structural size, applied natively to weighted-CSP partition functions, and signed or rational weight interfaces.

## Documentation and repository

- **The guide** ([#585](https://github.com/cslib-community/cslib-frontier/issues/585)): A chapter per area, including Foundations (bit strings, Fourier analysis, PMF and `ProbComp`, codes), proof complexity, descriptive complexity, and Word RAM and algorithms, reusing checked examples.
- **Archive `complexitylib-v1`:** Archive the repository once its remaining work is dispositioned.
