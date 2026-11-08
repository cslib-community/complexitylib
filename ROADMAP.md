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
| Optional experiment: formalize unformalized STOC 2027 submission results, subject to independent source-correspondence review | [#2527] |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798], audit [#884] |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862], from [#456] |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949], [#939] |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#2585] |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640], [#643] |
| Crypto frontier track: Kilian's succinct arguments | [#999] |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002] |
| A Verso guide with a chapter per area | [#585] |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124] |
| Proof automation: predictable polynomial-time certificate search | [#1155] |

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897].

1. [Completeness of oblivious transfer](#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](#approximation-and-pcp) ([#886])
3. [Williams's NEXP ⊄ ACC⁰](#circuits-and-algebraic-complexity) ([#889])
4. [Valiant's VNP-completeness of the permanent](#circuits-and-algebraic-complexity) ([#321])
5. [The Kabanets–Impagliazzo theorem](#circuits-and-algebraic-complexity) ([#891])
6. [MIP = NEXP](#interactive-proofs) ([#892])
7. [Regev's worst-case to average-case reduction](#cryptographic-landmarks)

### Optional landmark projects

These are optional coverage targets, outside the priority queue above. Each requires substantial
new proof infrastructure; a useful prerequisite milestone does not complete the landmark.
Choose a source version and proof route before implementation, and reassess scope against
existing library and upstream developments. The size labels describe prerequisite breadth,
not staffing or calendar estimates.

- **Babai: graph isomorphism in quasipolynomial time — optional, very large.** Prove a
  deterministic `exp((log n)^O(1))` decision bound for the existing encoded graph-isomorphism
  problem, following the [manuscript](https://arxiv.org/abs/1512.03547v2) together with the
  [January 2017 correction](https://people.cs.uchicago.edu/~laci/upcc-fix.pdf).
  Reuse the graph encoding, indexed-permutation characterization and native verification API.
  Develop encoded permutation groups with certified orbit/stabilizer and membership algorithms;
  the Luks string-isomorphism/coset framework; canonical partition, Johnson-configuration and
  local-certificate arguments; then the full recursion, termination and native quasipolynomial
  runtime. Those four stages are independently reviewable projects; an NP verifier is not the
  required decision algorithm.
- **Bulatov–Zhuk: the finite-domain CSP dichotomy — optional, very large.** For every fixed
  finite constraint language, prove its CSP is in P or NP-complete, following either
  [Bulatov](https://arxiv.org/abs/1703.03021) or
  [Zhuk](https://arxiv.org/abs/1704.01914v11). Choose one tractability proof route rather than
  formalizing both. Bridge fixed-arity finite templates to the existing CSP semantics and
  CNF-compilation APIs; develop polymorphisms and primitive-positive reductions; prove the
  core/idempotent reductions and algebraic hardness criterion; then the chosen tractability
  algorithm and its native polynomial bound. Keep template-dependent constants separate from
  instance size. Special cases and reductions are useful milestones, not the full dichotomy.
- **QIP = PSPACE — optional, large.** Following
  [Jain–Ji–Upadhyay–Watrous](https://cs.uwaterloo.ca/~watrous/Papers/QIPequalsPSPACE.pdf),
  characterize polynomial-time quantum interactive proofs using a uniform verifier, unrestricted
  prover strategies and explicit completeness/soundness gaps. Reuse quantum circuit and
  measurement foundations and the classical IP/PSPACE development where their models agree.
  Supply mixed-state/channel and interactive-strategy semantics, the protocol normal form,
  the semidefinite optimization and matrix multiplicative-weights argument, and a polynomial-space
  implementation with controlled precision; prove both inclusions through model bridges.
  Quantum circuit simulation alone does not provide the interactive upper bound.
- **MIP* = RE — optional, large integration project; exceptional if rebuilt from scratch.**
  Target the entangled-multiprover characterization of recursively enumerable languages in
  [Ji–Natarajan–Vidick–Wright–Yuen, v4](https://arxiv.org/abs/2001.04383v4). Start with an audit
  and reuse assessment of the Apache-2.0
  [MIPRE formalization](https://github.com/vidick/MIPRE-formalization), including its low-degree-test
  dependency, rather than duplicating the compression proof. Pin its source and dependencies;
  check theorem assumptions, entangled-value semantics, toolchain compatibility and the bridge
  from its verifier-cost model to this library's native resource conventions. Then integrate
  compatible operator/game foundations, transfer the halting-to-game reduction and RE upper
  bound, and establish the native class equality. Preserve finite-dimensional tensor-product
  strategies, their supremum over unbounded finite dimensions and a uniform polynomial-time
  verifier; distinguish classical MIP and commuting-operator models. If reuse fails, rigidity,
  low-degree testing and recursive compression are separate major projects to scope before
  attempting the endpoint.

## Cryptography

Shared statistical infrastructure now propagates all-state, joint reply/state replacement
bounds through an adaptive oracle program using its existing query-cost budget
([#2724](https://github.com/cslib-community/complexitylib/issues/2724)). Zero-cost cache operations
retain their state effects. Applying this composition law to the actual Schnorr signing game,
transporting key-generation error, and realizing the efficient forking reduction remain [#2568].

### Cryptographic landmarks

- **Completeness of oblivious transfer.** In the ideal OT-hybrid model, every polynomial-time
  multiparty functionality admits a protocol secure against static malicious corruptions, with
  real/ideal simulation and abort, under the standard communication assumptions.
  `Crypto/Protocols/MPC/OTCommitment` supplies the Crépeau commitment ingredient: perfect hiding
  against adaptive receiver queries and a `2⁻ᵏ` malicious double-opening bound in ideal OT.
  `OTCommitment/Extraction` adds a stand-alone corrupted-sender output/state simulation with
  majority extraction error `2⁻⌈k/2⌉`. `OTCommitment/Equivocation` proves the exact joint law of
  the receiver's transcript, state and later opening from a bit-independent commit prefix.
  `OTCommitment/PolyTime` certifies only the deterministic extraction and equivocation maps on
  explicit lists. `OTCommitment/Opening/PolyTime` adds a total list opening checker with
  exact-length rejection and a native polynomial-time certificate. Full ideal commitment
  realization, unrestricted efficient simulation, composition, the malicious compiler,
  and MPC simulation remain open in
  [#1212](https://github.com/cslib-community/complexitylib/issues/1212).
  `Crypto/Protocols/Commitment/World` supplies an original single-session phased abort
  functionality with receiver-poll secrecy and an immutable committed bit.
  `OTCommitment/World` connects both corruption-specific laws to its actual transitions,
  including prefix-dependent withholding, in semantic `StateT PMF` drivers.
  `OTCommitment/Program` realizes the receiver driver with exactly four public calls and its
  honest-OT joint law. `Program/PolyTime` gives uniform strict PPT for supplied efficient
  callbacks with supported additive growth of both intermediate and final receiver states;
  the unary count, initial state and all list outputs are charged.
  `OTCommitment/SenderProgram/PolyTime` gives the corrupted-sender counterpart under combined
  supported round-growth bounds, with actual-world coupling and negligible error at `k = 2n`.
  `OTCommitment/CompleteSender/PolyTime` removes callback growth assumptions for one complete
  globally oracle-PPT sender over an explicit single-session command interface. Its input charges
  unary `k`; actual OT rows, seal-time ideal commitment, terminal first opening attempts and abort
  retain the same majority-extraction coupling, including `2^-n` at `k = 2n`. A globally polynomial
  private-buffer client lies outside the old constant-growth premise. This does not supply a
  universal two-sided realization. `OTCommitment/Serial` supplies a common role-local OT world:
  one pending row is consumed once, and the first terminal attempt freezes further selections.
  Its explicit honest-party schedulers reproduce both existing real experiments, retaining the
  receiver's raw opening as well as transcript, state and continuation. This connects those
  executions under their stated serial schedules; a global receiver-program adapter, uniform
  native contracts for the common execution, arbitrary two-sided scheduling and composition
  remain open.
- **Regev's worst-case to average-case reduction.** For suitable `q` and Gaussian noise rate
  `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time
  algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`. The noise distribution, modulus
  restrictions and quantum reduction are part of the theorem.
  The discrete Gaussian foundation proves convergence, positive normalization and translation
  laws on shifted discrete lattices ([#2573](https://github.com/cslib-community/complexitylib/issues/2573));
  finite exponential moments and normalizer-ratio tails are proved in
  [#2592](https://github.com/cslib-community/complexitylib/issues/2592).
  Local normal convergence and continuous lattice periodization, including Schwartz and
  Gaussian clients, are proved in
  [#2608](https://github.com/cslib-community/complexitylib/issues/2608).
  `Foundations/Analysis/Lattice/Fourier` identifies the unnormalized Fourier coefficients of
  integrable lattice periodizations at dual frequencies, including arbitrary sheared bases.
  Full arbitrary-lattice Poisson summation for Schwartz functions and shifted positive-width
  Gaussians, including the covolume normalization, is proved in
  [#2624](https://github.com/cslib-community/complexitylib/issues/2624).
  Centered Gaussian mass scaling and the strict radius-`s√n` tail bound of Regev’s
  Lemmas 2.4–2.5 are proved in
  [#2646](https://github.com/cslib-community/complexitylib/issues/2646). Uniform shifted-mass
  control by the actual nonzero dual Gaussian mass, with a quantitative sufficient width
  criterion and eventual satisfiability, is proved in
  [#2659](https://github.com/cslib-community/complexitylib/issues/2659).
  `Foundations/MeasureTheory/Group/QuotientDensity` folds arbitrary measurable nonnegative
  densities onto countable subgroup quotients, with no finite-mass assumption. The actual
  normalized continuous Gaussian and fundamental-domain quotient measures are probabilities;
  their density identity gives full-L1 distance at most the actual nonzero dual Gaussian mass,
  with eventual small error, in [#2681](https://github.com/cslib-community/complexitylib/issues/2681).
  This is a precise quotient consequence of Claim 3.8. The actual arbitrary-width
  coset discrete-Gaussian convolution density and Claim 3.9 full-L1 bound, with a sufficient
  dual-gap width criterion, are proved in
  [#2707](https://github.com/cslib-community/complexitylib/issues/2707). The actual scalar and
  canonical mod-one pushforward bounds of Corollary 3.10, including a discharged dual-gap
  criterion (covering `z = 0` under the same dual-mass or gap premise), are proved in
  [#2734](https://github.com/cslib-community/complexitylib/issues/2734). An attained minimum
  smoothing parameter, the periodic-density series, arbitrary-modulus search-LWE sampling
  experiment, efficient finite-precision sampling and quantum reduction remain open in
  [#1213](https://github.com/cslib-community/complexitylib/issues/1213).
  `Foundations/MeasureTheory/Group/ConvolutionDensity` proves the convolution density formula
  for an arbitrary s-finite first measure, including singular inputs. Its actual shifted
  discrete-Gaussian convolution consumer is the Claim 3.9 bound of
  [#2707](https://github.com/cslib-community/complexitylib/issues/2707); the shared measure
  identity alone does not establish a sampler.
  Exact coefficient-fiber disintegration is proved in
  [#2766](https://github.com/cslib-community/complexitylib/issues/2766): reducing integer basis
  coordinates modulo any positive integer, including composite moduli, gives actual positive
  residue masses and filtered coset Gaussians. Tagged samples reconstruct with the actual
  marginal weights. The joint LWE sample bound of Lemma 3.11 remains separate in
  [#2767](https://github.com/cslib-community/complexitylib/issues/2767); no uniform-residue or
  efficient-sampling claim follows from disintegration alone.
- **Kilian's succinct arguments** ([#999]). If collision-resistant hash families exist, every
  language in NP has an interactive argument with polylogarithmic communication, by committing
  to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle
  versions. `exists_kilianSound_of_mem_NP` and `exists_micaliCSProof_of_mem_NP` prove these with
  honest provers that hold an accepted PCP table; efficient honest provers from arbitrary NP
  witnesses and the verifier's runtime and message-truncation accounting remain.

### Modern fully homomorphic encryption

Gentry's bootstrapping is instantiated with GSW ([#486];
[theorems](Complexity/Crypto/Computational/Homomorphic/GSW/FullyHomomorphic.lean)), including
uniform compactness for the leveled wrapper decryption circuits and level-indexed multi-hop
evaluation. After the bounded unified reduction in [#1104], the remaining objective ([#2585])
is Gentry's exact concrete-security loss together with the `poly(ℓ, d)` running-time clause
of his Theorem 4. The complete existing modular reduction game now has an exact saved-tape law
in both challenge worlds, with a native evaluator and polynomial allocated coin budget derived
from strict-PPT components. Its original selector bias, message swap, tagged state and zero-link
fallback are preserved; supports are derived inside the game. Bit-encryption replay also retains
linear dependence on participating callback time, with independent workspace and supported
ciphertext-size bounds and a callback-independent preparation polynomial. This component bound
does not compare primitive costs with adversary runtime. A separate
[flattened reduction](Complexity/Crypto/Computational/Homomorphic/Leveled/FlatSecurity.lean)
uses a finite-attempt selector over `2 * depth * capacity + 1` signed hybrid steps, retaining
failure mass and improving the original selector loss without additive error. The literal
source loss mapping and multiplicative machine-runtime comparison remain open. Develop these in reviewable
milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions
where their hypotheses match. The [pre-rewrite FHE section][archive-fhe] maps the schemes to
current libraries and workloads.

The actual buffered probabilistic compiler now has an all-prefix workspace bound with an
explicit intermediate-word buffer charge, independent of component runtime. The complete
modular-game time/space assembly and prepared-metadata accounting remain
[#2722](https://github.com/cslib-community/complexitylib/issues/2722).

1. **Ring arithmetic and RLWE.** The coefficient `negacyclicMul` and Module-SIS map now have
   a canonical `AdjoinRoot (X^d + 1)` interpretation in `SIS/Polynomial`, for positive dimension
   over a nontrivial commutative coefficient ring. `SIS/Native` now bridges a certified list
   product to the existing negacyclic multiplication, uniformly over unary dimension and binary
   modulus/coefficients, with a rank-one key-generation client. Full native scheme execution
   still needs native encryption and seed codecs.
   Remaining: further certified polynomial-ring operations over `(Z/qZ)[X]/(X^d + 1)`, RNS/CRT
   conversions, rounding and modulus-switching error bounds, and negacyclic NTTs implementing
   ring multiplication, with native certificates. Define the RLWE secret and error laws and
   experiment separately; an ordinary-LWE reduction does not give them. Module-LWE sampling now
   permits explicit small-secret laws, with a native centered-binomial instance.
   `SIS/ModuleEncryption/Native` realizes deterministic key generation in `ModuleLWE.encodeSample`
   and deterministic decryption (`exists_computableInPolyTime_moduleLWEDecrypt`) uniformly with
   unary rank/degree and binary modulus/coefficients, given the expanded structured matrix or
   ciphertext word. `SIS/Module/MatrixSampling` natively constructs the existing rectangular rotation
   blocks and exactly samples their encoded law from independent power-of-two polynomial
   coefficients, uniformly in unary dimensions/width. `SIS/Module/ApproximateSampling` uses the
   existing bounded modular sampler for arbitrary positive binary moduli, with actual structured
   law error at most `d*k*n*q/2^width`, or `d*k*n/2^precision` at width `q.size+precision`.
   Independent uniform scalar entries do not give this law. `ModuleEncryption/Sampling/Native`
   composes exact CBD secret/error draws with the matrix sampler and existing keygen, returning
   the same signed secret and public key with ideal joint/public-law error `k*k*n/2^precision`.
   Native encryption, seed codecs and small-secret security remain open.
   `SIS/ModulusSwitch/Failure` bounds randomized switched-decryption failure by the actual noise
   tail under explicit secret-support and decoding margins; small-secret security remains open.
   Nearest-integer coefficient conversion and the Module-LWE phase-error bound are available in
   `SIS/ModulusSwitch`; `SIS/ModulusSwitch/Correctness` gives sufficient decryption-preserving
   margins including odd-modulus message scaling. Parity-preserving switching variants remain
   open. `SIS/ModulusSwitch/Native` certifies exact coefficient conversion
   uniformly over binary moduli and framed runtime row lists; subsequent scheme operations
   still need native certificates. The actual centered-binomial sampler now has a shared
   scalar concentration bound in `Languages/Probabilistic/CenteredBinomial/Concentration`;
   `SIS/ModulusSwitch/CenteredBinomial` instantiates a growing-rank/degree family with cubic
   moduli and negligible actual switched-decryption failure. It proves the coordinate union,
   strict no-wrap and rounding margins; small-secret security and full native scheme
   certificates remain open.
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

- **Fiat–Shamir query representations**: the finite theorem permits an injective hash-point
  embedding into an arbitrary query domain, retaining every out-of-image query and the same bound
  ([#2684](https://github.com/cslib-community/complexitylib/issues/2684)). The canonical word Schnorr
  instance is recorded below; explicit key-generation/signing approximation transport remains open.
- **Fiat–Shamir reduction failure output** ([#2774](https://github.com/cslib-community/complexitylib/issues/2774)):
  the existing reduction and quantitative bound accept an explicit fallback; Schnorr uses zero.
  Native fork execution, transcript/answer nonexhaustion and actual simulator-sampling transport
  remain prerequisites for [#2568].
- **Sigma protocols and Fiat–Shamir** ([#581]): computational Schnorr signatures under discrete
  log against strict PPT forgers. Word verification now enforces canonical commitments for canonical
  public keys ([#2672](https://github.com/cslib-community/complexitylib/issues/2672)).
  The arithmetic algorithms and exact typed ROM reduction are
  proved; strict-PPT identification and eavesdropping results do not discharge this signature
  endpoint. Remaining work includes shared encoded signing/hash access, final-message freshness,
  and an efficient realization of the full forking reduction ([#2568]).
- **Oracle forger replay**: the private-coin replay prerequisite now includes a full-input
  oracle-PPT certificate, tape preparation, and joint external-state preservation ([#2579]).
  Shared replacement laws derive a key-independent tape from actual PPT key-generation support
  and transport joint-state mixtures through the existing
  ROM game ([#2652]). The word-forger adapter ([#2636]) now has an efficient full-input guarded
  replay and exact shared-world/EUF-CMA equality with separate signing/hash channels. Applying it
  to Schnorr's encoded query space and realizing the complete efficient reduction remain open.
- **Lattices**: full random-oracle EUF-CMA signatures from SIS (Lyubashevsky 2009,
  2012) remain open. Strict-PPT box sampling, bounded signing and negligible availability are
  proved. The public-key-only fork milestone ([#2620]) bounds accepting-fork probability by
  actual homogeneous SIS success plus `k*q^n/(2η+1)^m`, for independent uniform box secrets
  and an arbitrary kernel receiving only `(A,T)`. This joint-law extraction uses the sampled
  secret; an `A`-only native reduction and the actual signing/fork distribution bridge remain
  open. Full-view witness invariance ([#2642]) retains aborted commitments for common
  commitment-dependent challenges and finite independent attempt histories. The canonical ROM
  bridge ([#2661]) extends this to sequential shared-cache signing and adaptive forger views,
  retaining abort queries and later attempts after success. Average-key cache-hit bounds for
  actual box commitments and the simulator's published commitments follow from matrix
  universality and the joint leftover-hash bound
  ([#2712](https://github.com/cslib-community/complexitylib/issues/2712)), for ideal uniform
  prime-modulus matrices and histories sampled before fresh masks. The one-call all-attempt
  read-to-program hop ([#2750](https://github.com/cslib-community/complexitylib/issues/2750))
  retains the complete cache, with an unconditional finite sum of collision bounds. The one-attempt
  visible simulation milestone ([#2788](https://github.com/cslib-community/complexitylib/issues/2788))
  bounds the statistical distance between the one-attempt programmed signing hybrid (which prepends
  a fresh challenge even on an abort) and simulated signing with accepted-transcript caching under
  any query-bounded visible continuation by `R / q^n + sqrt(q^n / (2γ + 1)^m) / 2`, with exact
  visible equality for zero-read continuations. Full executions retaining the final cache
  verify the 0 vs 24/49 empty-cache divergence on the canonical q=17 counterexample.
  For `K`-attempt visible simulation, `lyubashevskySimAttempts`,
  `lyubashevskySignAttemptsVisibleProg`, and `lyubashevskySignAttemptsVisibleSim` define the
  stopping secret-free simulator and visible experiments, with `K ≤ 1` reductions to the
  single-attempt bridge (`lyubashevskySignAttemptsVisibleProg_zero_eq_sim`,
  `lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_le_one`,
  `closeTo_lyubashevskySignAttempts_simulate_le_one`); the `K ≥ 2` visible simulation induction
  ([#2798](https://github.com/cslib-community/complexitylib/issues/2798)), adaptive multiple-call
  replacement, an efficient secret-free simulator, paired same-coins fork equality, native
  shared-oracle reduction and a security parameter family remain open. Other endpoints include
  identification security under SIS and Dilithium-style
  signature schemes over module SIS and module LWE, as theory.
- **Hybrid encryption:** the `n`-bit-message modular KEM–DEM adaptive CCA endpoint
  ([#2725](https://github.com/cslib-community/complexitylib/issues/2725), Boneh–Shoup
  Exercise 12.5(a)) now proves both KEM hops and the factor-two bound with native reductions
  into the existing KEM and one-time symmetric CCA games. It reuses canonical Option-valued
  decryption ([#2692](https://github.com/cslib-community/complexitylib/issues/2692)) and the
  actual-key DEM leg ([#2694](https://github.com/cslib-community/complexitylib/issues/2694)).
  A native key postprocessor must map uniform seeds exactly to the actual DEM key sampler;
  saved-coins and PRF Encrypt-then-MAC `3*n`-bit clients are checked. Perfect correctness
  separately requires supported postprocessed real keys. Arbitrary message-space extension,
  prechallenge KEM queries and multiple encapsulation challenges remain open; this endpoint
  does not claim unrestricted word-message CCA security.
- **Canonical word Schnorr ROM** ([#2696](https://github.com/cslib-community/complexitylib/issues/2696)):
  completeness, special soundness on all word transcripts, perfect HVZK, commitment
  unpredictability and the finite ROM bound retain every word hash query. Public keys remain
  actual group elements and scalar sampling is ideal; native adapter composition,
  key-generation/signing approximation transport and the complete efficient forking reduction
  remain open under [#2568].
- **Native Schnorr ROM algorithms** ([#2708](https://github.com/cslib-community/complexitylib/issues/2708)):
  actual sampled signing and verification have full-input oracle-PPT certificates with bounded
  hash-reply reads. Joint signature/cache realization under typed `m`-bit replies is exact after
  retaining the actual scalar-sampling law; replacing that law by ideal signing costs at most
  `2⁻ⁿ` per signature. The actual key-generation error is a separate `2⁻ⁿ` bound. Adaptive signing
  composition, native forger transport and efficient forking still belong to [#2568].
- **Paillier encryption and composite residuosity:** `Crypto/Computational/Paillier` certifies
  word key generation, dyadic-sampled encryption, decryption, perfect correctness and
  plaintext-addition preservation under decryption over a supplied balanced-modulus generator,
  alongside the Decisional Composite Residuosity assumption (`DCR`) in
  `Crypto/Computational/CompositeResiduosity`. The second condition of Katz–Lindell
  Definition 15.14 (exact distributional equality of multiplied ciphertexts with fresh
  encryptions) fails for the implemented dyadic `unitOrOne` sampler and needs an exact or
  statistical-closeness formulation. The IND-CPA security reduction under `DCR` (Theorem 15.13,
  accounting for approximate unit sampling) is proved as `DCR.indcpaOn_paillier` for a supplied
  generator whose primes have at least `n` bits (hypothesis `hsize`); native balanced-modulus
  generation remains open.
- **Garbled circuits and Yao's protocol**
  ([#3236](https://github.com/cslib-community/complexitylib/issues/3236)): point-and-permute
  garbling of arbitrary-basis circuits with exact correctness and concrete simulation privacy is
  in `Crypto/Primitives/Garbling`. The bound is the sum of `n + size` PRF advantages, and each
  reduction makes at most one query per table slot. Yao's semi-honest two-party protocol with an
  ideal batched OT oracle is in `Crypto/Protocols/MPC/Yao`. It has exact correctness, perfect
  privacy against the garbler, and a concrete `semiHonestAdvantage` bound against the evaluator.
  Next: replace the ideal OT by a protocol through an advantage-preserving composition theorem,
  and give the asymptotic PPT statement from the word-level `PseudorandomFunction`. After that:
  output to both parties, free-XOR and half-gates.
- **General:** reusable adaptive reductions, public-key encryption, universal-instance zero
  knowledge, hard-core predicates and hardness amplification, and connections to learning and
  average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643])

In order:
- the `PublicCoin → IP` bridge, with a uniform word verifier and adversarial decoding
  (`Verifier.wordVerifierWith`, `Verifier.Sound.acceptProb_wordVerifier`, `Reduction.mem_IP` in
  `Interactive/ToIP.lean`);
- parallel and AND/OR composition (`Verifier.seqProd`, `Reduction.seqProd`, `relProd`, `relDisj`
  in `Interactive/AuxZK.lean`) and round-by-round knowledge soundness (`Verifier.RbrKnowledgeSound`,
  `Verifier.RbrKnowledgeSound.append`, `Verifier.RbrKnowledgeSound.seqProd`,
  `Verifier.RbrKnowledgeSound.iterate`, `Verifier.RbrKnowledgeSound.bundle` in
  `Interactive/RbrKnowledge.lean`; parallel and OR protocol composition remain);
- oracle statements, so a later phase can query an earlier phase's oracle message (virtual
  output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds;
- efficiency-certified simulators and extractors (`Interactive/Efficient.lean`), and
  auxiliary-input zero knowledge on the core (`Reduction.AuxHVZK`, `Reduction.ZK`,
  `Reduction.EfficientAuxHVZK`, `Reduction.ComputationalAuxHVZK` in `Interactive/AuxZK.lean`);
- polynomial commitment and evaluation-query reductions, and the Ligero IOP;
- the BCS transform to non-interactive arguments in the random-oracle model (`BCS/Basic.lean`;
  `bcsROMSoundness_bound` and `bcsROMKnowledgeSoundness_bound` in `BCS/ROM.lean`; machine-level
  verifier and extractor runtime, polynomial-time NP-witness-to-IOP encoding and zero knowledge
  remain);
- VOLE constraint reductions and VOLE-in-the-head: `VOLE/Basic.lean` supplies ideal correlations,
  and `VOLE/MulCheck.lean` bounds arbitrary single-gate affine claims by `2 / |F|` with an
  independent secret key. `VOLE/BatchMulCheck.lean` batches constraints using a public vector of
  independent weights and an adaptive affine reply, with error at most
  `1 / |F| + (1 - 1 / |F|) * (2 / |F|)`. `VOLE/MaskedMulCheck.lean` executes the check
  in a cached ideal `World` with separate role interfaces and one fresh affine mask, proving
  completeness and exact simulation of the full honest receiver view (private key/tags and
  public transcript). `VOLE/AdaptiveMulCheck.lean` extends the exact full-view law to arbitrary
  receivers in that fixed schedule, retaining private coins, state and repeated setup reads.
  `VOLE/NativePPT.lean` certifies a list simulator for variable-size batches and supplied encoded-state
  receiver callbacks over one fixed ring with a certified exact-uniform sampler (with an F2 client).
  Its generalized input/first-message adapters charge the full encoded public input, layout and
  conversion; the raw-view law alone does not assert sender realizability of transformed messages.
  `VOLE/Circuit.lean`, `CircuitSound.lean` and `CircuitPrivacy.lean` bind the session to the existing
  arithmetic-circuit relation `∃ w, C.eval (x ++ w) = y`: public input/output, constant and addition
  rows join the multiplication batch. Actual role-local soundness has the same mixture bound
  (5/8 over the fixed F4), and satisfying traces retain exact full-view simulation. Fresh-session
  amplification, scalar-challenge batching, a complete native circuit prover/verifier certificate
  (including honest-sender realization, #2765), raw-bit adversarial transport (#2744), growing-field
  arithmetic, adversarial setup and scheduling, full zero-knowledge protocol security and
  VOLE-in-the-head remain (#643);
- libzk's compositional structure as a composition of these components, without ciphersuites.

### Private information retrieval ([#3251](https://github.com/cslib-community/complexitylib/issues/3251))

- **Information-theoretic PIR:** `Crypto/Protocols/PIR` covers one-round schemes with perfect
  correctness and single-server privacy, the subcube schemes with the rows transformation, the
  covering-code schemes for balanced covers (CGKS Section 3.3,
  [#3451](https://github.com/cslib-community/complexitylib/issues/3451)), and schemes from
  perfectly smooth decoders. It also has the single-server bound with and without interaction,
  and the two-server linear-summation bound with its tight even-set scheme (CGKS Section 5,
  [#3426](https://github.com/cslib-community/complexitylib/issues/3426)). Next targets:
  - variable-length answers, so that unbalanced covers meet CGKS Theorem 1 exactly;
  - the rest of CGKS Section 3.3: radius-`2` covering codes, the other dimensions of Figure 1,
    the asymptotic lower estimate and server time;
  - `t`-private schemes against coalitions;
  - block retrieval;
  - the converse from schemes to smooth codes (Katz–Trevisan);
  - lower bounds for general two-server schemes.

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

- **Planar Boolean CSP dichotomy** ([#3091](https://github.com/cslib-community/complexitylib/issues/3091)):
  extend the native Boolean classification to ordered planar instances of arbitrary fixed
  relation arity. Preserve individual incidence occurrences and cyclic argument order; prove
  the embedding/recognition interface, cyclic-difference reduction, even delta-matroid
  edge-CSP algorithm and planar hardness transfer. The full endpoint must discharge these
  ingredients internally, including the additional self-complementary tractable family.
  Supplied-embedding or matching-realizable-only milestones leave this objective open.

- **Boolean Schaefer dichotomy** ([#2822](https://github.com/cslib-community/complexitylib/issues/2822)):
  the stack proves native polynomial-time tractability for all six common-polymorphism cases
  and native NP-completeness outside them, for each fixed finite Boolean constraint language
  of arbitrary fixed arities. `CSPSAT.schaefer_dichotomy` assembles the actual solvers, fixed
  compilers, clone classification and gadgets under binary labels and exact-arity rejection,
  including empty/nullary relations. The hard branch has a native 3SAT reduction with
  `output.numVars + output.length ≤ C * input.length`, for a language-dependent constant.
  Symmetric and larger-domain dichotomies are outside the current scope.

- **Context-free languages** ([#3303](https://github.com/cslib-community/complexitylib/issues/3303)):
  CYK decides membership for grammars already in Chomsky normal form, correct against Mathlib's
  `ContextFreeGrammar.Derives`, with exact `TimeM` cost `O(n³ · |G|)`
  (`Algorithms/Lean/CYK`). Next: conversion of an arbitrary `ContextFreeGrammar` to Chomsky
  normal form with its size blow-up, giving decidability of every context-free language; a
  machine-level `ComputableInPolyTime` decider for a fixed grammar, completing CFL ⊆ P (Sipser,
  Theorem 7.16); Valiant's subcubic parsing via Boolean matrix multiplication; the pumping
  lemma for context-free languages and non-context-freeness of `{aⁿbⁿcⁿ}`; and CFG emptiness
  (in P) versus universality (undecidable).

- Time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes;
  completeness, padding, self-reducibility, relativization and oracle separations, preserving
  each reduction's resource bound.
- **Abstract (Blum) complexity** ([#2866]): Blum complexity measures over Mathlib's
  `Nat.Partrec.Code`, with the `evaln` fuel instance, Borodin's gap theorem for the
  almost-everywhere classes (also with a two-argument stretch), recursive relatedness, Blum's
  speedup theorem, arbitrarily complex functions with the resulting strict hierarchy of
  classes, the McCreight–Meyer union theorem, and the naming and honesty theorems (a measured
  family naming every class `C_t`, and one computable `g` giving every `C_t` a `g`-honest name;
  [#3234](https://github.com/cslib-community/complexitylib/issues/3234)), are in
  `Computability/BlumComplexity`.
  Remaining: Blum's compression theorem in its running-time form (a single computable `h` such
  that every total `φ_i` has `C_{Φ_i} ⊂ C_{n ↦ h n (Φ_i n)}`; the value form with `φ_i` in place
  of `Φ_i` is false, by the gap theorem); `g`-honesty for partial functions and the related
  exercises on honest and measured sets (Odifreddi, *Classical Recursion Theory* II, Exercises
  VII.2.14b–d); effective forms of speedup such as Blum's
  pseudo-speedup, which computes a
  faster program for a finite variant of `f` (M. Blum, *On effective procedures for speeding up
  algorithms*, J. ACM 18(2), 1971), and Blum measures for
  native multitape time and space through a Gödel-numbering bridge from native descriptions.
- **Busy beaver** ([#3314](https://github.com/cslib-community/complexitylib/issues/3314)):
  Radó's output and fuel busy beaver functions for `Nat.Partrec.Code` on input `0`, with codes
  measured by Gödel number, dominate every computable function, and a computable upper bound on
  either would decide halting (`Computability/BusyBeaver/Partrec`). Remaining: Radó's `Σ(n)` and
  `S(n)` for Turing machines counted by states, with a simulation bridge to the code version (to
  live beside it under `Computability/BusyBeaver/`) and the known small values
  (`S(5) = 47,176,870`, verified by the bbchallenge Coq proof) as a cross-check;
  independence of busy beaver values from ZFC (Aaronson–Yedidia); and the connection to Chaitin's
  `Ω`.
- **Post's correspondence problem** ([#3387](https://github.com/cslib-community/complexitylib/issues/3387)):
  PCP and MPCP are undecidable over `Bool` and over every alphabet with two distinct letters,
  as `¬ComputablePred` predicates on `Primcodable` instances
  (`Computability/PostCorrespondence`). The proof reduces `ComputablePred.halting_problem` through
  a universal `TM0` machine, Sipser's computation-history MPCP instance, and MPCP → PCP with a
  start marker. Remaining: decidability of unary PCP and of PCP with two dominoes
  (Ehrenfeucht–Karhumäki–Rozenberg, 1982); undecidability with a bounded number of dominoes (five,
  Neary, 2015); a reduction from the acceptance problem of an arbitrary machine as in Sipser; and
  consumers: ambiguity of context-free grammars, emptiness of the intersection of two context-free
  languages, CFG universality, and mortality of 3×3 integer matrices (Paterson, 1970).
- **Degrees of unsolvability** ([#3379](https://github.com/cslib-community/complexitylib/issues/3379)):
  oracle codes for Mathlib's `RecursiveIn` with stage-bounded evaluation, the use principle and
  the equivalence `f ≤ᵀ g ↔ ∃ c, Code.eval g c = f`, and the incomparability part of the
  Kleene–Post theorem by finite extension, are in `Foundations/Computability`.
  Remaining: the Kleene–Post bound `A, B ≤ᵀ ∅′` (a primitive recursive oracle `evaln` on encoded
  codes, typed `RecursiveIn` combinators, the halting set and the jump; merged Mathlib lacks
  these, and the open
  [mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973) proposes an
  oracle `evaln` code and the jump, a possible route); the Friedberg–Muchnik
  theorem (incomparable computably enumerable degrees, by finite injury); Sacks splitting and
  density of the c.e. degrees; and Spector's minimal degree.
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
- **Randomized primality tests**
  ([#2917](https://github.com/cslib-community/complexitylib/issues/2917)): the Euler-liar
  (Solovay–Strassen) and strong-liar (Miller–Rabin) bounds `2 · #liars ≤ φ(n)` for odd composite
  `n` are in `Foundations/NumberTheory/Primality`, together with the Rabin–Monier bound
  `4 · #strong liars ≤ φ(n)` for odd composite `n ≠ 9` (`Primality/RabinMonier`), and an explicit
  Miller–Rabin verifier puts the primes in `coRP` independently of AKS
  (`Problems/Primes/MillerRabin`). The Jacobi symbol is computable in polynomial time on binary
  inputs (`PolyTime/Nat/Jacobi`). Remaining
  ([#2958](https://github.com/cslib-community/complexitylib/issues/2958)): the Solovay–Strassen
  verifier stated as a `coRP` membership (with its gcd step, since non-units can satisfy Euler's
  congruence).
- The space hierarchy for `log n ≤ g n`, which needs a universal simulation that does not hold
  its input.
- **Space:** Savitch bounds for general space-constructible functions.
- **Catalytic space and KMPS collapses** ([#2521]): define native `CSPACE(s,c)` and its
  nondeterministic/randomized variants, with exact restoration for every initial catalyst and
  every computation branch; existing `Catalytic/Comparison` routines are only algebraic tools.
  Formalize Koucký–Mertz–Pyne–Sami, [*Collapsing Catalytic Classes*](https://arxiv.org/abs/2504.08444):
  `CL = CNL = CPrL` (hence `CBPL = CL`), the general compress-or-compute oracle simulation,
  catalytic Savitch/complementation and randomized space–catalyst tradeoffs, preserving the
  paper's parameter ranges, oracle promises and restoration conventions. Include its catalytic
  hierarchy collapses and lossy-space consequences with their stated resource bounds.
  Track the newer Koucký–Mertz–Sami [robust catalytic extensions](https://arxiv.org/abs/2605.09648)
  separately: their broader collapse is conditional on the explicit circuit-hardness assumption,
  with resetting-error and time regimes distinguished from KMPS's unconditional results.
- **Randomized logspace** ([#459], [#474]): two-sided `BPL` amplification, the random-walk proof
  of `USTCON ∈ RL` (membership already follows from `L_subset_RL` and `USTCON_mem_L`), the
  space-efficient computability of Nisan's generator and the bridge from configuration graphs to
  read-once programs (its fooling theorem for read-once branching programs is
  [#3187](https://github.com/cslib-community/complexitylib/issues/3187)), `BPL ⊆ L²` and
  Saks–Zhou. The preprint route to native `RL = L` remains open in
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
  The Saks–Zhou iteration as pure mathematics (random-shift rounding, Lemmas A.3 and A.4 of
  Chattopadhyay–Liao in exact density form) is
  [#3247](https://github.com/cslib-community/complexitylib/issues/3247). It is a milestone of
  [#474](https://github.com/cslib-community/complexitylib/issues/474). Still open: instantiating
  its offline power with Nisan's generator, and the space-bounded realization giving
  `BPL ⊆ L^{3/2}`.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a
  logspace reduction.
- **Williams's `TIME[t] ⊆ SPACE[√(t log t)]`** ([#888]): the native implicit
  Tree Evaluation/block-tree evaluator, complete Hopcroft–Paul–Valiant block-simulation driver
  and final
  [`DTIME_subset_DSPACE_sqrt`](Complexity/Computability/Complexity/Classes/TimeSpace/Williams.lean)
  inclusion have landed, together with the [checked registry entry](ComplexityResults/Entries.lean)
  ([#2142](https://github.com/cslib-community/complexitylib/pull/2142),
  [#2143](https://github.com/cslib-community/complexitylib/pull/2143)). The inclusion covers
  arbitrary injective input encodings and every `t(n) ≥ n`, without time constructibility;
  its fixed driver scans the original input, searches schedules and increases balanced time
  guesses. The paper's time–space separation corollaries (including for linear space) and a
  curated headline abstract with independent review remain open in [#2855]; landing the inclusion
  and registry does not complete that broader scope.
  For Cook–Mertz itself: malformed-input handling and the refined
  `O(ℓ + H log(ℓ + 2))` parameter bound remain open ([#2855]).
- **Time–space lower bounds for nondeterministic linear time**
  ([#2896](https://github.com/cslib-community/complexitylib/issues/2896)): simultaneous
  `TISP(t, s)`, two-quantifier alternating time `Σ₂TIME(t)` (bridged to `Σ₂ᵖ`) and the slowdown
  lemma `NTIME(n) ⊆ DTIME(t') ⇒ Σ₂TIME(t) ⊆ NTIME(t'(O(t)))` are in
  [`TimeSpace/Slowdown.lean`](Complexity/Computability/Complexity/Classes/TimeSpace/Slowdown.lean).
  The speedup lemma, in the weaker form `TISP(t, s) ⊆ Σ₂TIME(√t · (s + n log² n + log² t))` for a
  machine on an oracle-described input, and the instance `TISP(n¹², n²) ⊆ Σ₂TIME(n⁸)` are in
  [`TimeSpace/Speedup.lean`](Complexity/Computability/Complexity/Classes/TimeSpace/Speedup.lean).
  Still open: the Arora–Barak lower bound `NTIME(n) ⊄ TISP(n^1.2, n^0.2)` by virtual padding, with
  the Lipton–Viglas `n^(√2 − ε)` form. Beyond these: the textbook `√(t·s)` speedup, which needs
  amortized `O(1)` simulation steps rather than copying a configuration per step, the golden-ratio
  deterministic bound of Fortnow, Lipton, van Melkebeek and Viglas, and the transfer to SAT. The
  transfer needs a quasi-linear-size Cook–Levin reduction.
- Alternating time and space classes and bounded-alternation characterizations of PH; sharp
  bounds for sublinear space, distinct from polynomial-space simulation.
- **Alternating logspace, `P ⊆ AL`**
  ([#2873](https://github.com/cslib-community/complexitylib/issues/2873)): play the circuit-value
  game on the tableau of a polynomial-time machine (`Tableau.ValueGame`, which gives
  `APSPACE = EXP`) in logarithmic space. This needs a word game machine whose round reads the
  input from the input tape and keeps only the `O(log n)`-bit wire claim on its work tape. Once it
  is proved, add `AL = P` to the
  [alternation abstract](abstracts/ComplexityAbstracts/AlternationAbstract.lean), which states
  `AP = PSPACE` and `APSPACE = EXP`, as part of
  [#2873](https://github.com/cslib-community/complexitylib/issues/2873).
- **Pebble games and space lower bounds**
  ([#2995](https://github.com/cslib-community/complexitylib/issues/2995)): the black pebble game
  on a `Digraph`, the path-blocking lower-bound engine, and the exact prices `h + 2` of the
  complete binary tree and the pyramid (Cook) are in `Complexity/Computability/Pebbling`, and
  `Complexity/Computability/Circuit/Pebbling.lean` identifies `s`-register evaluation of
  `Cslib.Circuits.Program` straight-line programs with `s`-pebble black pebbling. Bennett's
  reversible game and its exact prices on the path, `⌈log₂ (v + 2)⌉` (visiting) and
  `⌈log₂ (v + 1)⌉ + 1` (persistent), are in `Pebbling/ReversiblePath.lean`
  ([#3163](https://github.com/cslib-community/complexitylib/issues/3163)), and the
  Li–Tromp–Vitányi characterization of every reachable configuration (their Theorem 1 and
  Corollary 1) is in `Pebbling/ReversiblePathReachable.lean`. Next: black-white pebbling; the
  reversible time–space trade-offs (is `3 ^ k` optimal for `k + 1` pebbles?) and the erasure
  trade-off of Li–Tromp–Vitányi
  ([#3199](https://github.com/cslib-community/complexitylib/issues/3199));
  the Hopcroft–Paul–Valiant `O(n / log n)` pebbling of bounded-indegree DAGs and the matching
  Paul–Tarjan–Celoni `Ω(n / log n)` family; Gilbert–Tarjan and Lengauer–Tarjan time–space
  trade-offs, including for register evaluation.
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
- **Sparse and tally sets:** after Kadin's
  `PH = P^{NP[O(log n)]}` (`Classes/Sparse/Kadin.lean`, [#2062],
  [#3155](https://github.com/cslib-community/complexitylib/issues/3155)): his stronger form with a
  sparse `S ∈ NP` and `coNP ⊆ NP^S`; and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** paddability of the standard NP-complete graph, number and set problems,
  hence their p-isomorphism to SAT; every many-one complete set for EXP is complete under one-one,
  length-increasing reductions (Berman); and the isomorphism theorem for sets complete under AC⁰
  reductions (Agrawal, Allender and Rudich).
- **Autoreducibility and mitoticity:** for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so
  every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang);
  separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and
  Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468]): the full expanded 2013 paper of
  Glaßer, Nguyen, Reitwießner, Selman and Witek: native transfer from local self-reducibility
  (Lemma 3.3), including virtual-input/answer regeneration and adaptive-to-tt conversion.
  Uniform runtime initialization and generic virtual-input simulation of component-certified
  query machines are proved, with arbitrary saved outer state/output continuations and an additive
  native space bound. Generic extraction from existing native machines and ordinary logspace
  word-function certificates is proved, with streaming output and workspace-derived saved-state
  bounds. Preparing supplied headers from live query generators, regenerating answer words and
  the resource-certified suffix loop remain open;
  bounded and many-one self-reducibility specializations; concrete complete self-reducible
  problems (Theorem 3.5); Section 4
  bounded/logarithmic-query results and
  separations, and Section 5 mitoticity/diagonalization. The additional parity-logspace
  application needs a native path-counting class and complement closure.
- **Uniform diagonalization** ([#3142](https://github.com/cslib-community/complexitylib/issues/3142)):
  after Schöning's theorem for recursively presentable classes closed under finite variations, with
  the reductions of the mixed set and `P` as an instance (`Classes/UniformDiagonalization.lean`):
  a recursive presentation of the polynomial-time degree of a decidable set outside `P`, hence
  Ladner's density theorem and an `NP`-intermediate problem below every `NP`-complete one if
  `P ≠ NP`; other presentable classes (`NP`, `PSPACE`, the polynomial hierarchy levels).
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE,
  self-reducible P-selective sets lie in P, and P-selective sets are not `≤ₜₜᵖ`-hard for NP unless
  P = NP.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and
  so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity** ([#2899](https://github.com/cslib-community/complexitylib/issues/2899)): after
  `IsImmune`/`IsBiImmune`, a `P`-bi-immune set in `E` (`Classes/Immune/Construction.lean`) and
  Berman's theorem that `≤ᵖₘ`-complete sets for `E`/`EXP` are not `P`-immune
  (`Classes/Immune/Complete.lean`), witnessed by bounded halting with a binary time bound
  (`Problems/BoundedHalting.lean`, [#3002](https://github.com/cslib-community/complexitylib/issues/3002)),
  and complexity cores, with Lynch's lemma that problems outside `P` have infinite polynomial cores
  (`Classes/Immune/Core.lean`, `Classes/Immune/PolyTimeCore.lean`,
  [#3080](https://github.com/cslib-community/complexitylib/issues/3080)), decidable ones inside
  decidable problems on bit strings (`Classes/Immune/RecursiveCore.lean`,
  [#3182](https://github.com/cslib-community/complexitylib/issues/3182)):
  a SAT-free home for the machine enumeration of `Ladner/Basic.lean` shared by Ladner and the
  immunity modules;
  decidable cores for general encodings with a decidable range; `EXP`
  and `PSPACE` instances of the class-generic core theorem (`exists_infinite_isComplexityCore_subset`
  needs only countability, finite sets and closure under unions); core density for intractable
  sets (Orponen and Schöning) and core sizes for hard sets (Juedes and Lutz);
  `DTIME(t)`-bi-immune sets in larger time classes for general constructible `t`, the remaining
  Balcázar–Schöning results, almost-everywhere hardness, and measure strengthenings (almost every
  set in `E` is `P`-bi-immune, Mayordomo).
- **Exponential-time complete problems**
  ([#3002](https://github.com/cslib-community/complexitylib/issues/3002)): after bounded halting
  with a binary time bound (`E`- and `EXP`-complete, `Problems/BoundedHalting.lean`) and Book's
  separations (`E ⊊ EXP`, `E ≠ NP`, `E ≠ PSPACE`, `Classes/EXP/Separation.lean`): succinct
  versions of `P`- and `NP`-complete problems (succinct circuit value for `EXP`, succinct SAT for
  `NEXP`), generalized games complete for `EXP`, nondeterministic bounded halting for `NE`/`NEXP`,
  and the isomorphism and density structure of `E`-complete sets.

### Average-case complexity

- **Distributional framework** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): extend the length-indexed ensembles, `AvgP`/`HeurP`,
  `DistNP` and dominating reductions with polynomial-time computable ensembles being samplable,
  Levin's runtime-moment definition of average polynomial time and its relation to errorless
  schemes (instances of probability zero obstruct a literal equivalence), and randomized
  average-case classes. Reuse the specialized Liu–Pass hardness notions through further proved
  bridges.
- **Heuristic hierarchy and universal distributions** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): prove that
  `(BH, U^BH) ∈ Heur_{1/n} P` gives `DistNP ⊆ HeurP`, and the `Avg` analogue
  (Bogdanov–Trevisan Prop. 21). The source pads instances to `(M, x, 1^{t + ⌈1/δ⌉})`, which can
  change `BH` membership, so the proof should route through a fixed clocked universal program
  whose input carries `(c, z, 1^t)`. Also prove the theorem of Levin, Li and Vitányi
  (Bogdanov–Trevisan Thm 16): under the ensemble `K_n(x) ∝ 2^{-C(x)}` on each length, a decidable
  `L` with `(L, K) ∈ Heur_{1/n³} P` is in `P`.
- **Completeness beyond computable ensembles** ([#2865](https://github.com/cslib-community/complexitylib/issues/2865)): extend the bounded-halting completeness for
  `DistNP` to samplable distributions (Impagliazzo–Levin, `SampNP`), and bridge the verifier-form
  bounded halting problem to a nondeterministic machine model. Connect the framework to one-way
  functions, learning and the metacomplexity track ([#798]), preserving the distribution and
  reduction conventions.

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
- **Exact counting by determinants**
  ([#3081](https://github.com/cslib-community/complexitylib/issues/3081)): Kirchhoff's
  matrix-tree theorem (with polynomial-time spanning-tree counting), its weighted form and Tutte's
  directed (arborescence) form are done. Remaining: the BEST theorem for Eulerian circuits,
  polynomial-time counting of arborescences and of weighted spanning trees, and Kasteleyn's
  Pfaffian method for perfect matchings of planar graphs, in contrast with permanent
  #P-completeness.
- For composite moduli
  ([#3495](https://github.com/cslib-community/complexitylib/issues/3495)): the prime-power
  collapse `Mod_{p^e}P = Mod_pP` is done. Remaining: union closure for every modulus through
  Hertrampf's characterization of `Mod_{jk}P` for coprime `j, k` (Beigel–Gill, Theorem 32 and
  Corollary 35).
  Complement closure for moduli that are not prime powers is open, and relativizing proofs
  cannot give it (Barrington–Beigel–Rudich), so it is not a library direction.
- Target-relativized `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and
  UP-oracle containment.
- Native oracle counting machines: efficient encoded oracle checking, response-access costs and
  oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **MIP = NEXP** ([#892]): `NEXP ⊆ MIP₂` through the BFL multilinearity test and arithmetization
  of exponential-time tableaux; an efficient GKR verifier under log-space uniformity.
- **Oracle-model `IP[k]`** ([#3425](https://github.com/cslib-community/complexitylib/issues/3425)):
  oracle-PPT `IP` verifiers with at most `k` queries give exactly the count-based `IPk` (coin
  fixing and padding to `k` rounds), which carries `IPk_eq_AM` to the oracle model;
  `IP[k(n)] ⊆ AM[k(n) + 2]` for patterns that depend on the input length.
- The Babai–Moran speedup `AM[2 t(n)] = AM[t(n)]` for polynomially many rounds (patterns that
  depend on the input length), interactive-machine characterizations of Arthur–Merlin classes, and
  statistical and perfect zero knowledge.
- **Statistical zero knowledge** ([#3205](https://github.com/cslib-community/complexitylib/issues/3205)):
  the Sahai–Vadhan polarization of statistical distance is available on explicit finite
  distributions, and on pairs of circuit samplers as a polynomial-time map on encoded Statistical
  Difference instances, with error `2^-(|x|+1)`. It gives polynomial-time reductions from every
  `SD^{α,β}` with `β < α²` to every `SD^{α',β'}` with `0 < β' < α' < 1`
  (`Problems/StatisticalDifference/PolyTime.lean`), for constant thresholds. Instances are pairs
  of De Morgan circuits with a common input count and a common output count; padding general
  pairs to that form is open. Next come honest-verifier SZK with `SD` in it, `SD` being
  SZK-complete, Entropy Difference (Goldreich–Vadhan), closure under complement (Okamoto), and
  `SZK ⊆ AM ∩ coAM` (Fortnow; Aiello–Håstad).

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
  machines (the machine-level `P ⊆ AL`, see
  [#2873](https://github.com/cslib-community/complexitylib/issues/2873)) and the translation to
  `encCircuitValue`.
- Numeric certificates for further restricted-domain families; canonical BIT on a restricted
  domain need not be first-order definable.
- Order-free: SAT-to-3SAT, graph-property hardness, and bridges to the separately encoded
  problems.
- Extend the synthesis rules to nested operator bodies and give regular-language quantifiers
  their ordered characteristic-word semantics.
- **FO(TC) = NL** on ordered structures
  ([#1246](https://github.com/cslib-community/complexitylib/issues/1246)): NL ⊆ FO(TC) via
  configuration-graph reachability under the ordered encoding (FO(TC) ⊆ NL is done). Separately,
  the native NL closure facts the in-compiler inductive counting bypasses: intersection, union,
  logspace reductions and NL^NL = NL.
- Further logical characterizations on ordered structures: FO(DTC) = L,
  SO-Horn = P (Grädel), and DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing);
  then order-invariant and fixed-point queries and uniform translations between syntax,
  structures and algorithms.
- A witness-carrying reduction structure once a client needs one, for example size bounds for
  Cook–Levin.
- **Logical lower-bound methods:** building on the Ehrenfeucht–Fraïssé games for relational
  vocabularies and the nondefinability of
  [connectivity](Complexity/Logics/FirstOrder/EhrenfeuchtFraisse/Connectivity.lean),
  [bipartiteness and acyclicity](Complexity/Logics/FirstOrder/EhrenfeuchtFraisse/GraphProperties.lean)
  by interpretation from finite linear orders, and on [Hanf and Gaifman locality](Complexity/Logics/FirstOrder/Locality/Hanf.lean)
  with its [game-free proofs](Complexity/Logics/FirstOrder/Locality/GraphProperties.lean) that
  connectivity, acyclicity and being a tree are not definable
  ([locality track](https://github.com/cslib-community/complexitylib/issues/3015)), and the
  [Gaifman-locality proofs](Complexity/Logics/FirstOrder/Locality/Reachability.lean) that
  transitive closure and reachability are not definable, with an exponential lower bound on the
  locality radius and FO ⊊ FO(TC) on unordered graphs
  ([#3483](https://github.com/cslib-community/complexitylib/issues/3483)), add Gaifman's normal
  form theorem, the exact locality ranks `2 ^ (n - 1) - 1` and `2 ^ n - 1` (Libkin, Exercises 4.10
  and 4.11), further nondefinability applications of locality (Libkin's balanced binary trees and
  same generation, then planarity, Hamiltonicity and `k`-colorability for `k ≥ 3`),
  games for vocabularies with constants, and pebble games with their finite-variable equivalence
  theorems; then counting and fixed-point expressiveness, including Cai–Fürer–Immerman-style
  separations. Connect the methods to the ordered capture theorems, where FO(≤, BIT) defines EVEN.
- **Color refinement and Weisfeiler–Leman:** building on
  [color refinement](Complexity/Foundations/Combinatorics/SimpleGraph/ColorRefinement.lean)
  (stabilization, the coarsest equitable partition and soundness of the 1-WL isomorphism test,
  [#3265](https://github.com/cslib-community/complexitylib/issues/3265)), add the correspondence
  between equitable partitions and fractional automorphisms and isomorphisms (Tinhofer;
  Ramana–Scheinerman–Ullman; Grohe–Kersting–Mladenov–Selman, Theorems 4.1 and 5.2), a certified
  polynomial-time color refinement algorithm, `k`-dimensional Weisfeiler–Leman, the
  Immerman–Lander correspondence with the counting logic C² and its finite-variable extensions,
  and Cai–Fürer–Immerman graphs.
- **Undecidability in the finite:** Trakhtenbrot's theorem holds for raw relational sentences
  over any vocabulary with a binary relation symbol (Libkin, Theorem 9.2,
  [Binary](Complexity/Logics/FirstOrder/Trakhtenbrot/Binary.lean)). Next, add a computable
  `Primcodable` bridge from Mathlib `L.Sentence` that transfers the results to Mathlib syntax
  ([#2886](https://github.com/cslib-community/complexitylib/issues/2886)).
- **Logic and automata on words**, after Büchi–Elgot–Trakhtenbrot for finite words (MSO =
  regular), FO[<] ⊊ MSO via EVEN
  ([#2885](https://github.com/cslib-community/complexitylib/issues/2885)) and star-free ⇒ FO[<]
  ([#3075](https://github.com/cslib-community/complexitylib/issues/3075)): the converse FO[<] ⇒
  star-free over a finite alphabet (McNaughton–Papert,
  [#3469](https://github.com/cslib-community/complexitylib/issues/3469)), by composition of
  rank-k types, and star-free = aperiodic (Schützenberger), from cslib's syntactic monoid, with
  decidability of first-order definability for regular languages;
  closure of regular languages under homomorphic images, upstream to cslib; the non-elementary
  lower bound on formula-to-automaton translation; Büchi's theorem for ω-words (S1S) over
  cslib's ω-regular languages; and MSO on trees: finite trees and tree automata
  (Thatcher–Wright, Doner) and Rabin's theorem for infinite trees (S2S).
- **Asymptotic probabilities:** extend the 0-1 laws for `G(n, 1/2)` and for uniform structures
  over finite relational vocabularies
  ([#2967](https://github.com/cslib-community/complexitylib/issues/2967)) to constant edge
  probabilities, unlabelled structures and classes defined by parametric axioms such as the
  simple-graph axioms; then the Kolaitis–Vardi laws for fixed-point and finite-variable infinitary
  logics, and the Shelah–Spencer laws for sparse random graphs.
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
- **Potential-line classes** ([#3206](https://github.com/cslib-community/complexitylib/issues/3206)):
  `PPADS`, `EOPL` and `SOPL` with their easy inclusions and `EOPL = SOPL ∩ PPAD` (Göös et al. 2022,
  Lemma 4) are in place. Next: `PLS ∩ PPADS ⊆ SOPL` (Lemmas 2–3), giving `SOPL = PLS ∩ PPADS` and
  `EOPL = PLS ∩ PPAD`; also `UEOPL`.
- **Sperner's lemma** ([#2999](https://github.com/cslib-community/complexitylib/issues/2999)):
  the parity form on the triangulated square grid by door-following, and circuit `Sperner2D` in
  `PPAD` as the end-of-line relation of its door graph. The `d`-dimensional parity form on the
  Kuhn-triangulated hypergrid (Chen–Deng–Teng 2009, Corollary 4.3) is in place. Remaining
  ([#3087](https://github.com/cslib-community/complexitylib/issues/3087)): `PPAD` membership of
  circuit `d`-dimensional Sperner/Brouwer (needs an oriented door graph), `PPAD`-hardness of
  two-dimensional Sperner/Brouwer (Chen–Deng), and `PPAD`-completeness of three-dimensional
  Sperner (Papadimitriou 1994). Optional: the classical form on a triangulated `d`-simplex (not
  formalized), and a bridge identifying `Cslib.Sperner.triangles` with the two-dimensional Kuhn
  triangulation.
- **Brouwer's fixed-point theorem** ([#3514](https://github.com/cslib-community/complexitylib/issues/3514)):
  the unit cube in `Fin n → ℝ` via hypergrid Sperner and compactness, with the weak
  approximation (a grid point displaced by at most `(K + 1)/N` for `K`-Lipschitz maps), is in
  place. Remaining: arbitrary compact convex sets (by retraction onto the cube or a simplex), and
  the computational problem Brouwer^f with its `PPAD` membership and hardness
  ([#3087](https://github.com/cslib-community/complexitylib/issues/3087)).
- **Parameterized:** strongly uniform variants (computable `f`), further explicit polynomial
  kernels, the W and A hierarchies, and parameterized lower bounds; connect these to
  [structural graph algorithms](#structural-graph-algorithms) and their decomposition costs.
- **Crown decompositions** ([#3378](https://github.com/cslib-community/complexitylib/issues/3378)):
  crowns, the crown reduction rule, the crown lemma and the combinatorial `3k`-vertex (and `2k`)
  kernel for vertex cover on `SimpleGraph`. Remaining: a polynomial-time crown finder (maximum
  matching or Kőnig cover in the machine model) and the resulting `IsKernelization` of the encoded
  `VertexCover` with `O(k)` vertices, the LP-based `2k` kernel by Nemhauser–Trotter, and the
  expansion lemma (`q`-expansions) with its kernels.
- **Kernelization lower bounds**
  ([#3210](https://github.com/cslib-community/complexitylib/issues/3210)): `NP/poly`, and the
  Fortnow–Santhanam theorem that an OR-distillation of an `NP`-hard problem gives
  `coNP ⊆ NP/poly`, in the class-wise form over a polynomial equivalence relation; polynomial
  compressions, OR-cross-composition and the Bodlaender–Jansen–Kratsch theorem ruling out
  polynomial kernels and compressions unless `coNP ⊆ NP/poly`; k-Path has no polynomial kernel
  or compression unless `coNP ⊆ NP/poly`, by an OR-cross-composition from Hamiltonian path.
  Remaining ([#3266](https://github.com/cslib-community/complexitylib/issues/3266)): further
  concrete lower bounds (Clique parameterized by vertex cover); k-Path in `NP`; moving the
  single-copy pendant gadget and `LongPath_npHard` from `Parameterized/LongPathKernel.lean` to a
  `Problems/LongPath` hardness module beside the other `NP`-hardness results;
  cross-compositions of bounded cost and the complementary witness lemma; Yap's collapse
  `coNP ⊆ NP/poly → PH = Σ₃`; AND-composition (Drucker).
- **Color coding** ([#2870](https://github.com/cslib-community/complexitylib/issues/2870)):
  colorful k-Path is in `FPT` by the dynamic programming over color sets. Remaining: random
  colorings (a fixed `k`-set is colorful with probability `K.descFactorial k / K ^ k ≥ e ^ (-k)`)
  and the one-sided-error randomized fpt algorithm for `LongPath`; derandomization by perfect hash
  families.
- **W-hierarchy** ([#2966](https://github.com/cslib-community/complexitylib/issues/2966)):
  `W[t]` by fpt-reduction to weighted satisfiability of circuits of weft at most `t` and bounded
  depth, with `FPT ⊆ W[t] ⊆ W[t+1]`; `IndependentSet` and `Clique` are `W[1]`-complete, and
  `W[1] = FPT` exactly when `Clique` is in `FPT`. Remaining
  ([#3256](https://github.com/cslib-community/complexitylib/issues/3256)): `W[t] ⊆ XP`,
  W[2]-completeness of Dominating Set, short Turing machine acceptance, `W[P]` and the A-hierarchy.
- **Exponential-time SAT** ([#894]): Schöning, PPZ and PPSZ run on the randomized word RAM with
  exact laws, amplification and time bounds (PPSZ's round count takes an input bound
  `a / b ≥ 1 - qbar k h`); Schöning has a curated abstract. Optional remainder: PPZ and PPSZ
  abstracts, and the uniform `o(n)` forms of the PPSZ bounds with `w` growing in `n`.
  Further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.
- **APSP class** ([#3076](https://github.com/cslib-community/complexitylib/issues/3076)): APSP and
  the (min,+) product reduce to each other in the query model (repeated squaring costs
  `⌈log₂ (n - 1)⌉` products, the tripartite graph one APSP call on `3 n` vertices), with
  Floyd–Warshall and schoolbook products as instances. The (min,+) product reduces to negative
  triangle detection (Vassilevska Williams–Williams Lemma 4.1, Lemma 4.2 in its pairs form and
  Theorem 4.2, weights `ℤ ∪ {∞}`): an `n ^ (3 - δ)` detector gives an `n ^ (3 - δ / 3) log W`
  product, and one product decides negative triangle. Remaining: `-∞` weights and general (min,⊙) structures; the
  output-sensitive listing bound (Theorem 4.3); the other APSP-equivalent problems of Vassilevska
  Williams and Williams (minimum-weight cycle, replacement paths, metricity, (min,+) product
  verification); the radius and median equivalences of Abboud, Grandoni and Vassilevska Williams
  (SODA 2015); a bridge from vertex-list walks to `Quiver.Path` weights; word-RAM realizations
  with bit-length costs; Kerr's `Ω(n³)` bound for (min,+) straight-line programs. Bellman–Ford
  with negative-cycle reporting is
  [#3053](https://github.com/cslib-community/complexitylib/issues/3053).
- **Reductions from orthogonal vectors**
  ([#3037](https://github.com/cslib-community/complexitylib/issues/3037)): diameter two versus
  three is done for general `m` (`FineGrained.Diameter`, the `OV` form of Roditty–Vassilevska
  Williams Theorem 9). Remaining: the `(3/2 - ε)`-approximation corollary for diameter; the
  sparse-graph `m ^ (2 - ε)` statement, which needs the low-dimension form of `OVH` (dimension
  `c log N`, from `SETH` with sparsification); the `OV` hardness of longest common subsequence
  and edit distance by alignment gadgets (Backurs–Indyk; Abboud–Backurs–Vassilevska Williams;
  Bringmann–Künnemann). Their quadratic dynamic programs are in `Algorithms/Lean/EditDistance`
  ([#3472](https://github.com/cslib-community/complexitylib/issues/3472)).

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886]): for `0 < ε < 1/8`, NP-hardness of
  distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most
  `7/8 + ε` of the clauses. Holenstein's parallel repetition theorem for two-prover games is
  proved (`TwoProverGame.value_pow_le`), and so is parallel repetition for Label Cover instances
  without parallel edges (`LabelCoverRepetition.one_sub_unsatVal_pow_le`), and Label Cover is
  NP-hard with perfect completeness and every soundness `δ ∈ (0, 1)`
  (`exists_GapLabelCover_npHard`, with `128^{2k}` and `128^k` labels for `k` depending on `δ`).
  The completeness and soundness of Håstad's 3-bit test on folded long-code tables are proved
  (Lemmas 5.1 and 5.2, `Hastad.gapLabelCover_dichotomy_lt_one`, with the threshold uniform in the
  label sets), and so is the four-clause reduction from three-variable XOR to exact three-CNF
  (`ThreeXOR`). What remains is the polynomial-time MAX-E3LIN instance built from folded long-code
  tables and its composition with that lemma and with `exists_GapLabelCover_npHard` (Theorem 5.4),
  the composition with the four-clause reduction (Theorem 6.1, imperfect completeness), and
  Håstad's separate test for satisfiable formulas (Theorem 6.5).
- **MAX 2-SAT** ([#3481](https://github.com/cslib-community/complexitylib/issues/3481)): the
  decision problem is NP-complete by the Garey–Johnson–Stockmeyer ten-clause gadget
  (`Problems/MaxTwoSAT`). Remaining: APX-hardness with explicit inapproximability constants,
  and a reduction from MAX 2-SAT to unweighted MAX CUT (the library's `MaxCut` is weighted and
  reduces from `Partition`).
- **Unique Games with perfect completeness**
  ([#3363](https://github.com/cslib-community/complexitylib/issues/3363)): label propagation
  decides satisfiable unique games (`Cslib.Complexity.solvedBy_gapUniqueGames_one`), with
  an `O(L · (N + E))` step bound in an explicit `TimeM` cost model (`solveM_time_le`). Remaining:
  `GapUniqueGames (Fin L) 1 s ∈ PromiseP` under the encoding of `UniqueGamesConjecture`, through
  the plain polynomial-time framework.
- The FGLSS clique-hardness reduction and its amplification, retaining the exact gap and
  reduction runtime.
- Gap and approximation-preserving reductions, APX/PTAS/FPTAS, inapproximability consequences of
  PCP, CSP classifications and relaxation gaps, with assumptions such as the Unique Games
  Conjecture stated explicitly. The 2-to-2 games theorem waits for [#886].
- **Approximation algorithms:** a general interface for approximation ratios of optimization
  problems, under which polynomial-time algorithms such as Johnson's `7 / 8` algorithm for
  MAX-E3SAT meet matching hardness results such as Håstad's ([#886]); LP and SDP rounding. The
  Goemans–Williamson analysis of random-hyperplane rounding for weighted MAX-CUT, with
  `0.87856 < α`, is in `Algorithms/Lean/MaxCut/GoemansWilliamson`. It is stated against every cut
  for given `ε`-optimal unit vectors under an exact Gaussian. Remaining
  ([#3230](https://github.com/cslib-community/complexitylib/issues/3230)): polynomial-time SDP
  solving with precision accounting, a `ProbComp` realization of the Gaussian sample, tightness
  (the Feige–Schechtman integrality gap), the MAX-2SAT and MAX-DICUT extensions and
  derandomization.
- **Packing approximation**
  ([#2964](https://github.com/cslib-community/complexitylib/issues/2964)): the asymptotic
  approximation scheme for bin packing of Fernandez de la Vega and Lueker, Dósa and Sgall's
  absolute bound `FF ≤ ⌊17/10 * OPT⌋` for First Fit and their matching lower-bound instances,
  First Fit Decreasing's `11/9` bound and Lawler's faster knapsack FPTAS, building on the knapsack
  FPTAS, Next Fit, First Fit's `17/10 * OPT + 4/5` bound
  (`Algorithms/Lean/{Knapsack,BinPacking}`) and the `3/2` bin-packing hardness
  (`PCP/Approximation/BinPacking`).
- **Scheduling:** beyond Graham's list-scheduling, LPT and precedence bounds in
  `Algorithms/Lean/Scheduling`: real-valued processing times with precedences, Graham's anomaly
  instances as checked examples, a general tight family for LPT, the Hochbaum–Shmoys PTAS for
  `P || C_max`, and runtime bounds for `listSchedule` and `lptSchedule`
  ([#2909](https://github.com/cslib-community/complexitylib/issues/2909)).
- **A practical PCP construction:** a reasonably runnable construction and its cost on complete
  reductions; rotation certificates polynomial in the bit length of a vertex name; machine-level
  error reduction and extractors from expander walks, with certified seed and evaluation costs.

### Proof complexity

- **Proof space** ([#3200](https://github.com/cslib-community/complexitylib/issues/3200)):
  `Resolution/Space.lean`, `SpaceWidth.lean` and `TseitinSpace.lean` cover configuration-style
  clause space, the Atserias–Dalmau inequality (Atserias–Dalmau Theorem 3) with the constant
  `W ≤ s + k - 3` of Filmus–Lauria–Mikša–Nordström–Vinyals Theorem 1, and linear clause space for
  Tseitin formulas on expanders. `TreeLikeSpace.lean`
  ([#3229](https://github.com/cslib-community/complexitylib/issues/3229)) bounds clause space by
  the Strahler number and the logarithm of tree-like size (Esteban–Torán), and by `n + 2` on `n`
  variables. `ExistentialPebble.lean` and `PigeonholeSpace.lean`
  ([#3321](https://github.com/cslib-community/complexitylib/issues/3321)) add Duplicator
  strategies (Atserias–Dalmau Lemma 3) and width and clause space at least `n` for the extended
  `3`-CNF pigeonhole formula with `n` holes. The converse, Atserias–Dalmau Lemma 2
  ([#3375](https://github.com/cslib-community/complexitylib/issues/3375)), gives their Theorem 2
  for formulas without clauses of width exactly `w + 1`, and the space–width inequality is proved
  from any Duplicator strategy. `WidePigeonholeSpace.lean`
  ([#3498](https://github.com/cslib-community/complexitylib/issues/3498)) gives Torán's exact clause
  space `n + 2` of the wide pigeonhole formula with `0 < n < m`, whatever the number of pigeons.
  Next:
  - space lower bounds for random `k`-CNFs;
  - total and variable space;
  - time–space trade-offs for pebbling formulas, building on `Complexity/Computability/Pebbling`;
  - degree versus space in polynomial calculus.
- **Sum-of-squares** ([#3260](https://github.com/cslib-community/complexitylib/issues/3260),
  [#3423](https://github.com/cslib-community/complexitylib/issues/3423)):
  `Algebraic/SumOfSquares/` has degree-`d` refutations and pseudo-expectations with the easy
  duality direction, Schoenebeck's pseudo-expectation for parity systems with no width-`d`
  derivation of `0 = 1` (Schoenebeck Lemma 13), and Grigoriev's bound `e(G) ≤ d` for Tseitin
  parity systems, with a linear-degree expander family. It also has Positivstellensatz
  refutations with inequality constraints and products of constraints, the cutting-planes
  encoding of CNFs, and degree `2` exactly for the pigeonhole principle (Grigoriev–Hirsch–Pasechnik
  Example 2.1). Next:
  - the converse duality, by hyperplane separation, and the Lasserre/Sherali–Adams hierarchies with
    a bridge to the proof system;
  - Grigoriev's `Ω(n)` bound for random `3`-XOR (Barak–Steurer Theorem 2): first the deterministic
    half, that `3`-XOR systems on expanding hypergraphs have no narrow derivation of `0 = 1`, then
    expansion of random hypergraphs, and Schoenebeck's gaps for CSPs implied by XOR;
  - the `0/1` encoding and Grigoriev's knapsack bound, through pseudo-expectations;
  - the dynamic Positivstellensatz calculus and the Lovász–Schrijver systems of
    Grigoriev–Hirsch–Pasechnik, compared with the static form here;
  - size–degree relations for sum-of-squares, and size lower bounds.
- **Tree-like resolution** ([#3499](https://github.com/cslib-community/complexitylib/issues/3499)):
  `Resolution/ProverDelayer.lean` turns splitting potentials (asymmetric Prover–Delayer games,
  Beyersdorff–Galesi–Lauria Theorem 1) into tree-like size lower bounds, and
  `TreeLikePigeonhole.lean` gives `(n + 1 - h) ^ h` nodes for `PHP^m_n`, `m > n`, which is
  `2 ^ Ω(n log n)` at `h = n / 2`. Next:
  - the asymptotic statement and the matching `2 ^ O(n log n)` upper bound (Dantchev–Riis);
  - the functional pigeonhole principle, for which BGL note that the same strategy works;
  - a tree-like versus general resolution separation (Ben-Sasson–Impagliazzo–Wigderson).
- Polynomial calculus, and certified DPLL solver runtimes.
- **Frege** ([#3069](https://github.com/cslib-community/complexitylib/issues/3069)): implicational
  completeness of the Hilbert-style system (Kalmár); formula-size measures; the simulation of
  resolution as a p-simulation of Cook–Reckhow proof systems, with encodings and translation
  time; the mutual p-simulation of Frege systems; and Extended Frege.
- **Cutting planes:** the clique–colouring lower bound for cutting planes with bounded
  coefficients from Krajíček's feasible interpolation, Corollary 7.3
  ([#2019](https://github.com/cslib-community/complexitylib/issues/2019), M4b), and the
  monotone case of the interpolation theorem in which the shared variables occur in `Γ_B` with
  nonpositive coefficients only; Pudlák's
  lower bound for unrestricted coefficients via monotone real circuits (untracked);
  coefficient-size measures; Buss–Clote cutting planes with division by 2 only; and the
  simulation of resolution as a p-simulation of Cook–Reckhow proof systems, with encodings and
  translation time.
- **Feasible interpolation** ([#1817]): further clients of Krajíček's interpolation theorem for
  semantic derivations ([#2019]): resolution through Theorem 6.1, the linear equational calculus,
  and the monotone case for the `ℬ` side. The remaining cutting-planes work is under **Cutting
  planes**.
- **Proof search:** automatizability and weak automatizability with explicit encodings and
  runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow
  and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.

## Circuits and algebraic complexity

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889]): no polynomial-size,
  constant-depth circuits over AND, OR, NOT and fixed-modulus counting gates for some language in
  NEXP. `SymAnd/ACC0.lean` defines the `SYM ∘ AND` circuit `Circuit.toSymAnd` of every circuit
  with `MOD_m` gates, `m > 0`, and proves that it computes the same function with polylogarithmic
  fan-in and quasi-polynomial size, with explicit bounds (Yao; Beigel–Tarui, Theorem 1.1); every
  language of `AC0Mod m` (any `m`) and of `ACC0` follows. `SymAnd/Evaluate.lean` proves Williams's
  Evaluation Lemma in the unit-cost `TimeM` model: Yates's fast zeta transform gives the truth
  table of a `SYM ∘ AND` circuit with `s` gates, whose symmetric gate costs `T`, in
  `(n + 2)(2^n + (s + 1)(T + 1))` ticks
  ([#3023](https://github.com/cslib-community/complexitylib/issues/3023)). Still open: a machine
  computing that circuit in quasi-polynomial time, a Turing-machine or word-RAM evaluator, the
  ACC-SAT algorithm, a fine nondeterministic time hierarchy, and the `E^NP` and NEXP lower bounds.
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
  matching ([#2063]) and bipartite perfect matching in `Complexity.P encBits` now give a monotone
  language in P whose monotone circuit complexity is superpolynomial
  ([#3147](https://github.com/cslib-community/complexitylib/issues/3147)). An exponential gap
  (É. Tardos 1988) remains open.
- **An explicit frontier extractor:** port v1's sumset-extractor construction with an explicit
  family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses. It would
  exceed the library's unconditional `3.5 N - o(N)` bound in P, so it needs an independent
  correctness review of the frontier core.
- **Weighted threshold representations:** v1's explicit source-reduction family, universal scalar
  circuit synthesis, entropy and asymptotic activity bounds, and geometric cutting.
- **Depth-two threshold circuits for Andreev's function** ([#2347]): the exact quadratic
  `2 * 4 ^ b + b * m * 2 ^ b + 1` depth-two weighted threshold upper bound
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
  `ε³` dependence in Theorem 1.1 and Section 5 of arXiv:1511.07860v1) are proved. Averaging
  extends these bounds to `ε`-approximate majorities of depth-two circuits, so a majority vote of
  `t` depth-two circuits with at most `s` gates each needs top fan-in
  `t = Ω(n ^ (3 / 4) / (log n · √s))` once `t ≤ √(2 ^ b) / (6 (b + 2))`
  (`WeightedThreshold/AndreevApproxMajority.lean`, [#2812]; Kane–Williams, Corollary 1.1, have
  `Ω̃(n ^ (1 / 2) / s ^ (1 / 3))`). The vote is stated through its number of correct members rather
  than as a depth-three circuit model. Closing the worst-case depth-two threshold gate gap between
  `Ω̃(n ^ (3 / 2))` and `O(n ^ 2)` remains open, as do the other [#2812] milestones.
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
  fields of characteristic other than two ([#321]; membership has an explicit Ryser witness over
  every commutative ring, and arithmetic formulas project to the permanent with dimension
  `Formula.size + 1` over every commutative semiring; a selector occurring in one permanent entry
  can be eliminated with one extra dimension when `2` is invertible; the conversion from VP
  witnesses to formulas, the two-entry gadget and the general Boolean-sum elimination needed for
  VNP-hardness remain open); formula and branching-program models (proved in
  [`Arithmetic/Noncommutative`](Complexity/Computability/Circuit/Arithmetic/Noncommutative/):
  Nisan's exact size formula for homogeneous layered non-commutative ABPs, the `n ^ m` lower bound
  for the palindrome and the double, and the separation from non-commutative circuits, exponential
  for `n ≥ 2`
  ([#3198](https://github.com/cslib-community/complexitylib/issues/3198)); open there: the
  reduction from general non-commutative ABPs, non-commutative formula lower bounds for the
  determinant and permanent, and ROABPs), identity testing, hitting sets, and tensor and rank
  methods, including partial-derivative
  measures (the order-`k` measure and bounded-product-fan-in depth-three determinant and permanent
  lower bounds, covering homogeneous depth-three circuits, are proved in
  [`Arithmetic/DepthThree`](Complexity/Computability/Circuit/Arithmetic/DepthThree.lean);
  Nisan–Wigderson's all-orders measure, their elementary symmetric polynomial and iterated matrix
  multiplication bounds, and shifted partial derivatives remain open) and the depth-reduction chasms at
  depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform
  construction costs certified
  separately from gate counts. Also Strassen's degree bound (Bézout's inequality and the
  `n log d` multiplication lower bound for the power map), which through the proved Baur–Strassen
  transfer in [`Arithmetic/Gradient`](Complexity/Computability/Circuit/Arithmetic/Gradient.lean)
  ([#2906](https://github.com/cslib-community/complexitylib/issues/2906)) would give the
  `Ω(n log d)` bound for the single power sum `∑ xᵢ^(d+1)`; and matrix inversion from the
  determinant through the adjugate circuits of
  [`Arithmetic/Adjugate`](Complexity/Computability/Circuit/Arithmetic/Adjugate.lean), which needs
  a circuit model with division.
- **Determinantal complexity**
  ([#3384](https://github.com/cslib-community/complexitylib/issues/3384),
  [#3476](https://github.com/cslib-community/complexitylib/issues/3476)): the Mignon–Ressayre
  bound `n² ≤ 2 · dc(perm_n)` is proved in
  [`Arithmetic/DeterminantalComplexity`](Complexity/Computability/Circuit/Arithmetic/DeterminantalComplexity.lean)
  over every field of characteristic zero or of characteristic at least `n`, and Grenet's upper
  bound `dc(perm_n) ≤ 2ⁿ - 1` over every commutative ring. Remaining: Valiant's universality
  (every polynomial is a projection of a determinant of size linear in its formula size), which
  can reuse the branching-program step
  [`Matrix/BranchingProgramDeterminant`](Complexity/Foundations/LinearAlgebra/Matrix/BranchingProgramDeterminant.lean);
  the Cai–Chen–Li extension to every
  characteristic other than two; Yabe's real bound `dc(perm_n) ≥ (n - 1)² + 1` through
  Sylvester's law of inertia; and border determinantal complexity in the geometric complexity
  theory programme (Landsberg–Manivel–Ressayre).
- **The matrix multiplication exponent** (ω ≤ 9/4): Pass's constructive proof
  (arXiv:2610.28627v2) of OpenAI's bound is formalized over every field of characteristic zero:
  for every `τ > 9/4` an exact bilinear algorithm for some `v × v` multiplication with fewer than
  `v ^ τ` multiplications (`Foundations/LinearAlgebra/Tensor/Round.lean`), hence circuits of size
  `O(n ^ τ)` by block recursion and `omega K ≤ 9/4`
  (`Circuit/Arithmetic/MatrixMultiplication/NineQuarters.lean`). The tensor framework
  (`Foundations/LinearAlgebra/Tensor/`: restrictions, degenerations over `K[ε]`, Bini's
  conversion, rank) is general. Open: every field (the interpolation nodes are the integers of
  characteristic zero), the rectangular and dual exponents, explicit sizes and constants (the
  algorithm is galactic), and the lower bound `omega K ≥ 2` only as the trivial output count.
- **Fast integer and polynomial multiplication**
  ([#2923](https://github.com/cslib-community/complexitylib/issues/2923)): Karatsuba on coefficient
  lists in the arithmetic query model, with exact counts and `O(n ^ log₂ 3)` bounds, is in
  `Algorithms/Lean/Query/Arith/Karatsuba`. Integer Karatsuba as De Morgan circuits for the full
  `2w`-bit product, with `O(w ^ log₂ 3)` gates, is in `Circuit/Boolean/Karatsuba`. Open: smaller
  constants, logarithmic or polylogarithmic depth, uniform generation, and a native or word-RAM
  realization; Toom–Cook (`O(n ^ log₃ 5)` for Toom-3); and lower bounds such as rank `3` for the
  two-term product tensor.
- **Fast Fourier transform and FFT multiplication**
  ([#2979](https://github.com/cslib-community/complexitylib/issues/2979)): the radix-2
  Cooley–Tukey transform over any commutative ring with `ω ^ (2 ^ k) = -1`, with exactly
  `(n / 2) log₂ n` multiplications and `n log₂ n` additions, its inverse, the convolution theorem
  and `O(n log n)` polynomial multiplication, is in `Algorithms/Lean/Query/Arith/FFT` and
  `Foundations/Algebra/DFT`. Open: arbitrary lengths on coefficient lists (zero padding to a power
  of two) with a list-level `UpperBound`; the transform as an arithmetic circuit of size
  `O(n log n)` and depth `O(log n)`; rings without suitable roots of unity (Schönhage–Strassen over
  `R[x] / (x ^ m + 1)` and the `O(n log n log log n)` integer bound); mixed-radix and Bluestein
  transforms; and lower bounds such as Morgenstern's `Ω(n log n)` for bounded-coefficient linear
  circuits.
- **Matrix rigidity and linear circuits**
  ([#3209](https://github.com/cslib-community/complexitylib/issues/3209)): rigidity
  (`Foundations/LinearAlgebra/Matrix/Rigidity.lean`) and Valiant's criterion
  (`Circuit/Arithmetic/Rigidity.lean`) are proved: a fan-in-2 affine circuit of size `s` and depth
  below `2 ^ D` computing `A x` gives `R_A(2 t s / D) ≤ m 2 ^ (2 ^ (D - t))` for every `t ≤ D`, so a
  matrix with `R_A(n / e) > n 2 ^ (log₂ n / k)` needs `Ω(n log log n)` gates in depth `O(log n)`.
  The criterion also covers polynomial gates over infinite fields. The explicit lower bound
  `R(r) ≥ n² / (4 (r + 1)) · log₂(n / r)` for Cauchy and other totally regular matrices, for
  `n ≤ 2 ^ r` and `2 r ≤ n`, is proved (`Matrix/Rigidity/TotallyRegular.lean`; Lokam, Theorem 2.5,
  states it for `log² n ≤ r ≤ n / 2`), through the Kővári–Sós–Turán bound
  (`Combinatorics/KovariSosTuran.lean`) and the untouched-minor lemma. Open:
  Shparlinsky's Vandermonde and the Sylvester–Hadamard bounds; the upper bound `R(r) ≤ (n - r)²`
  and the counting proof that random matrices over finite fields are nearly maximally rigid;
  Alman–Williams non-rigidity of the Walsh–Hadamard matrix; the criterion for nonlinear gates over
  finite fields; and, as Valiant's open problem, an explicit `(εn, n ^ (1 + δ))`-rigid matrix.
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
- **Random graph connectivity** ([#3485](https://github.com/cslib-community/complexitylib/issues/3485)):
  for Mathlib's binomial random graph `G(n, p)`, connectivity with high probability when
  `n p - log n → ∞` (union bound over cuts, explicit bound `35 n exp (-(n p))`) is in
  `Foundations/Probability/Combinatorics/BinomialRandomGraph/Connectivity.lean`. Remaining: the
  lower half (`n p - log n → -∞`, isolated vertices by the second moment), the limit
  `e ^ (-e ^ (-c))` at `p = (log n + c) / n`, and the hitting-time theorem.
- **Explicit Ramsey graphs** ([#3041](https://github.com/cslib-community/complexitylib/issues/3041)):
  strongly explicit graphs with no `k`-clique and no `k`-independent set, on more vertices than
  Frankl–Wilson's `k ^ Θ(log k / log log k)`, toward Erdős's existential `2 ^ (k / 2)`: the
  two-source disperser and extractor constructions of Barak–Rao–Shaltiel–Wigderson, Cohen,
  Chattopadhyay–Zuckerman and Li, with the disperser connection of
  [#895](https://github.com/cslib-community/complexitylib/issues/895). Also open here: Frankl and
  Wilson's modular intersection theorem in its inclusion-matrix form (reportedly `|L| ≤ d`),
  beyond the restricted form `|L| ≤ d mod p` of the triangular polynomial argument. Keep the
  clique and independence bounds separate from the polynomial-time recognition and adjacency
  certificates on vertex names. An explicit graph on `2 ^ Ω(k)` vertices is open.
- **Codes:** Guruswami–Sudan list decoding and local decoding, keeping interpolation,
  list-size/agreement guarantees and decoding runtime as separate obligations; concrete
  list-decodable codes for Nisan–Wigderson.
- **Upper bounds on code size** ([#3280](https://github.com/cslib-community/complexitylib/issues/3280)):
  the Singleton, Hamming, Plotkin (with its asymptotic form), alphabet-free and q-ary Johnson,
  and finite Elias–Bassalygo bounds are in place. Remaining: the asymptotic Elias–Bassalygo bound
  `R ≤ 1 - H_q(J_q(δ)) + o(1)`, which needs the lower bound `q ^ (H_q(e / n) n - o(n))` on the
  volume of a q-ary Hamming ball, and the McEliece–Rodemich–Rumsey–Welch linear-programming bound
  (Delsarte's linear program and Krawtchouk polynomials).
- **Expander codes** ([#3278](https://github.com/cslib-community/complexitylib/issues/3278)):
  Sipser–Spielman codes of bipartite vertex expanders already have rate, distance and flip
  decoding (correctness, with the number of flips bounded by the violated checks). Still missing:
  lossless expanders themselves, either by the probabilistic method or explicitly
  (Capalbo–Reingold–Vadhan–Wigderson), so that expander codes become an `IsAsymptoticallyGood`
  family; a machine-model linear-time implementation of the decoder; Spielman's linear-time
  encodable codes; and Zémor's decoding of Tanner codes on spectral expanders, building on the
  Tanner-code distance bound in `Complexity/Foundations/Combinatorics/Expander/TannerCode.lean`.
- **Channel coding** ([#3304](https://github.com/cslib-community/complexitylib/issues/3304)):
  for the binary symmetric channel, the following are in place:
  - achievability (random codes with nearest codeword decoding at every rate below `1 - h₂(p)`,
    maximal error `≤ 10 exp (-δ n)`);
  - the weak converse, via Fano's inequality;
  - the strong converse (above capacity, the average error of every code is
    `≥ 1 - 2 exp (-δ n)`);
  - the capacity theorem (`1 - h₂(p)` is the supremum of achievable rates, for every `p`).

  Remaining: the behaviour at rate exactly `1 - h₂(p)` (second-order, dispersion terms),
  general discrete memoryless channels with mutual-information capacity (the chain
  rule for `n` channel uses and the data-processing inequality), channels with feedback,
  explicit and efficiently decodable capacity-achieving codes (Forney concatenation, polar
  codes), and the link to list decoding.
- **Locally decodable codes** ([#2929](https://github.com/cslib-community/complexitylib/issues/2929)):
  query-bounded decoders, the Hadamard code, Katz–Trevisan smoothing for oblivious-read decoders
  and the one-query bound are in place. Remaining: the adaptive-to-non-adaptive reduction (so that
  smoothing covers every adaptive decoder), the matching/XOR normal form and the Katz–Trevisan bound
  `n ≥ Ω(k^{q/(q-1)})` with explicit `(δ, ε, q)` dependence, and the Goldreich–Karloff–Schulman–
  Trevisan and Kerenidis–de Wolf exponential bounds for two-query codes.
- **Lempel–Ziv compression** ([#3312](https://github.com/cslib-community/complexitylib/issues/3312)):
  LZ78 incremental parsing, its lossless pair and bit codes, the distinct-parsing bound and the
  worst-case length `⌈log₂ k⌉ n (1 + o(1))` are in `Algorithms/Lean/LempelZiv`. So are LZ77
  sliding-window parsing with its lossless triple code, the optimality and uniqueness of the
  exhaustive history (Lempel–Ziv complexity) and `#LZ77 ≤ #LZ78`
  ([#3518](https://github.com/cslib-community/complexitylib/issues/3518)). Remaining: asymptotic
  optimality for stationary ergodic sources (Ziv's inequality, compression ratio tending to the
  entropy rate, which needs stationary-process infrastructure), bit-level LZ77 codes with a bounded
  lookahead, and the links to Kolmogorov complexity and finite-state compressibility. Machine-level
  or `TimeM` costs of the parsers are a separate endpoint.
- **Boolean analysis:** hypercontractivity beyond `p ≤ 2 ≤ q` and its further applications
  (small-set expansion, the Level-k inequalities); coverage of O'Donnell's *Analysis of Boolean
  Functions* ([#2131](https://github.com/cslib-community/complexitylib/issues/2131)), including the
  book-form statements of its Chapter 9 (the KKL edge-isoperimetric theorem, and Friedgut's junta
  theorem with its spectral concentration). For Chapter 11, the Basic Invariance Principle under
  Hypothesis 11.65 and Corollary 11.67 are in place
  ([#3242](https://github.com/cslib-community/complexitylib/issues/3242)). Remaining: Corollary 9.6
  for general `B`; the Invariance Principle for `(2, 3, ρ)`-hypercontractive ensembles
  (Remark 11.66); the step from smooth test functions to the Lipschitz form (Corollary 11.68) and
  the Lévy-distance form (Corollary 11.70); the forms for functions with small high-degree tails,
  including noise-stable functions (Corollary 11.69), and cdf-closeness to Gaussians through the
  Carbery–Wright theorem (Theorem 11.71); and Majority Is Stablest through Borell's isoperimetric
  theorem.
- **Resource-bounded measure and dimension:** martingales and gales with explicit computation
  budgets, their success sets, and measure and dimension within complexity classes; connect
  quantitative randomness to the Kolmogorov-complexity development. State the resource bounds
  and uniformity of the betting strategies separately from ordinary measure-theoretic facts.
  Beyond Lutz's p-measure in `E`
  ([#3139](https://github.com/cslib-community/complexitylib/issues/3139)): the quantitative
  Measure Conservation bound, countable p-unions (Lutz's Lemma 3.10(c)), measure in `EXP` (`p₂`),
  p-randomness, gales and resource-bounded dimension.

## Communication, queries, learning and other models

- **Lifting** ([#890]): applications of deterministic lifting, such as partition-number
  separations, and randomized lifting.
- **Randomized query complexity of game trees**
  ([#3060](https://github.com/cslib-community/complexitylib/issues/3060)): the AND–OR tree on
  `n = 4 ^ k` leaves is evasive, and the directional algorithm gives Motwani–Raghavan's
  `R₀ ≤ n ^ (log₄ 3)` and Snir's sharp `R₀ = O(n ^ (log₂ α))`, `α = (1 + √33) / 4`, `≈ n ^ 0.7537`.
  Remaining: the Saks–Wigderson lower bound `R₀ = Ω(n ^ (log₂ α))` for the NAND tree, which would
  match the upper bound, via Yao's principle for expected cost; Monte Carlo (bounded-error) bounds
  for the same trees; and Saks–Wigderson's general read-once formula and game-tree (MIN/MAX over
  integer leaves) results.
- **Information complexity**
  ([#3243](https://github.com/cslib-community/complexitylib/issues/3243)): internal and external
  information cost of deterministic, private-coin and public-coin protocols, with
  `IC ≤ IC^ext ≤ CC` and equality on product inputs. Remaining: distributional-error information
  complexity; additivity and the direct-sum theorem `IC_{μⁿ}(fⁿ) = n · IC_μ(f)`
  (Braverman–Rao), whose embedding needs private sampling from conditional marginals of `μ`,
  beyond the uniform dyadic tapes of `PrivateCoin`; information equals amortized communication;
  and the Bar-Yossef–Jayram–Kumar–Sivakumar `Ω(n)` disjointness lower bound via the information
  cost of AND, which needs conditional information cost under a non-product `μ` with an auxiliary
  variable that makes the inputs conditionally independent.
- **Number-on-forehead multiparty protocols**
  ([#3197](https://github.com/cslib-community/complexitylib/issues/3197)): `NOF.Protocol`,
  public-coin NOF protocols, cylinder intersections and the multiparty discrepancy bound
  `2 γ ≤ 2 ^ c disc_ν(f)`, with the two-player case matching the two-party discrepancy; the cube
  bound `disc(f) ^ (2 ^ k) ≤ E(f)` and the Babai–Nisan–Szegedy lower bound `Ω(n / 4 ^ k)` for
  generalized inner product; leaves as cylinder intersections (the star lemma) and the
  Chandra–Furst–Lipton lower bound `D(Exactly-N) → ∞` for three players via Mathlib's corners
  theorem ([#3424](https://github.com/cslib-community/complexitylib/issues/3424)); Grolmusz's
  `O(k n / 2 ^ k + k)` protocol for generalized inner product
  ([#3453](https://github.com/cslib-community/complexitylib/issues/3453)). Remaining: the sharper
  `Ω(n / 2 ^ k)` bound for generalized inner product (source to be verified before citing), and
  Grolmusz's protocol for an arbitrary finite player type; for Exactly-N, the converse from
  corner-free colorings,
  upper bounds from Behrend's construction, quantitative corners bounds and the `k`-player version;
  matrix multiplication (Raz) and NOF disjointness lower bounds; and applications to
  `ACC⁰` and branching-program lower bounds. A two-party companion is the Aho–Ullman–Yannakakis bound
  `D(f) = O(N⁰(f) N¹(f))` relating deterministic and nondeterministic communication.
- Multiparty number-in-hand protocols, direct-product results, and reductions to streaming,
  sketching and cell-probe lower bounds.
- **Sign-rank and unbounded error**
  ([#3262](https://github.com/cslib-community/complexitylib/issues/3262)): the Paturi–Simon
  characterization and Forster's spectral lower bound (with approximate isotropic position) are
  done, giving `signRank(IPₙ) ≥ 2^{n/2}` and `UPP(IPₙ) ≥ ⌈n / 2⌉`. Remaining: Forster's exact
  isotropic-position lemma, the Alon–Frankl–Rödl counting bound, `signRank(EQ) = 3` on four or
  more inputs, and the Razborov–Sherstov exponential sign-rank bound for an AC⁰ function,
  separating `Σ₂^cc` from `UPP^cc`.
- **Dynamic cell-probe lower bounds**
  ([#3207](https://github.com/cslib-community/complexitylib/issues/3207)): the Fredman–Saks
  chronogram bound for dynamic prefix parity, `log_β n ≤ 128 t_q + 1` with
  `β = max 4 (8 t_u (2 w + 1))`, i.e. `t_q = Ω(log n / log(t_u (w + 1)))`, holds for deterministic
  step-indexed schemes with worst-case update depth `t_u` and `S ≤ 2 ^ w` cells. Remaining:
  amortized updates; Las Vegas randomization through the cell-probe Yao averaging; Pătraşcu–Demaine's
  `t_q lg(t_u / t_q) = Ω(lg n)` information-transfer trade-off; and reductions to dynamic
  connectivity.
- **Streaming and sketching:** native time and space bounds for Count-Min, including hash-seed
  storage and evaluation; the AMS sketch for `F₀`; for distinct elements
  ([#3340](https://github.com/cslib-community/complexitylib/issues/3340)), the median amplification
  and `Solves` statement for the k-minimum-values sketch, the space-optimal `F₀` estimators
  (Bar-Yossef et al. Theorems 2–3, Kane–Nelson–Woodruff `O(ε⁻² + log n)`) and the
  `Ω(ε⁻²)` and `Ω(log n)` lower bounds for approximate `F₀`; the AMS `F_k` estimator for
  streams of unknown
  length (reservoir sampling), and the `n^{Ω(1)}` lower bounds for `F_k` with `k ≥ 6`; `ProbComp`
  samplers and native realizations of the AMS sketches and the Count-Sketch; turnstile updates as
  stream items (the Count-Sketch row analysis already allows real weights), merging of Misra–Gries
  summaries, heavy-hitter recovery over the whole universe (dyadic or group-testing schemes) and
  space lower bounds for heavy hitters; multi-pass communication-to-streaming transfers with pass
  counts.
- **Locality-sensitive hashing**
  ([#3361](https://github.com/cslib-community/complexitylib/issues/3361)): the following are in
  place: Broder's MinHash theorem, sensitive families, exact AND/OR/banding collision laws, the
  S-curve gap, bit sampling for the Hamming distance, and the `(c, r)`-approximate
  near-neighbour structure: failure at most `e⁻¹ + 1/3` with `k = ⌈log n / log(1/p₂)⌉`,
  `L = ⌈n^ρ/p₁⌉` and the stop rule after `3L` candidates, with `ρ ≤ 1/c` for bit sampling. Only
  `k`, `L`, `ρ` and the number of inspected candidates are bounded; no operation counts or time
  are formalized. Next: a word-RAM realization with hashed buckets, seed storage and native
  `n^ρ` query and preprocessing time. Remaining: SimHash, p-stable LSH for `ℓ_p` distances,
  MinHash over min-wise independent families smaller than the symmetric group, and LSH lower
  bounds (O'Donnell–Wu–Zhou; source to be verified before citing).
- **Dimension reduction** ([#2996](https://github.com/cslib-community/complexitylib/issues/2996)):
  extend the Johnson–Lindenstrauss lemma for dense `±1` sign matrices to Achlioptas's sparse
  `{-√3, 0, √3}` distribution, Gaussian and spherical projections, and fast and sparse JL
  transforms; prove the Larsen–Nelson lower bound `k = Ω(ε⁻² log n)`; give JL maps as streaming
  sketches with `ProbComp` samplers and native costs for applying the projection.
- **Learning:** machine-certified running times for the LMN and Kushilevitz–Mansour learners;
  distributional problems and reductions, samplability, average-to-worst-case connections,
  PAC/agnostic learning, learning lower bounds, compression and refutation. For realizable
  PAC learning ([#2868](https://github.com/cslib-community/complexitylib/issues/2868)), extend
  the countable-domain VC ε-net upper bound `O((d log (1/ε) + log (1/δ))/ε)` to general
  well-behaved classes over measurable domains. Agnostic PAC learning of finite classes by ERM is
  in place. For infinite classes
  ([#3005](https://github.com/cslib-community/complexitylib/issues/3005)), prove uniform
  convergence from the growth function by symmetrization, then agnostic learnability of finite
  VC classes, first on countable domains, then at the sharp `O((d + log (1/δ))/ε²)` rate.
  Rademacher complexity
  ([#3297](https://github.com/cslib-community/complexitylib/issues/3297)): Massart's lemma,
  symmetrization, the McDiarmid generalization bounds with expected and empirical complexity,
  the growth-function and VC bounds for `{-1, +1}` classes, the 0-1 loss relation, and the
  resulting growth-function, VC and agnostic ERM bounds for binary classification are in place
  on finite domains. Remaining: Talagrand's contraction lemma, margin bounds, local Rademacher
  complexity, and general measurable domains.
  Statistical queries
  ([#2910](https://github.com/cslib-community/complexitylib/issues/2910)): the deterministic SQ
  model has correlational and SQ-dimension query lower bounds, including parities, the
  noise-free block simulation from random examples with a fixed-distribution PAC corollary,
  the low-degree algorithm as a non-adaptive SQ learner, and the characterization of weak
  learning under a fixed distribution by the absolute-correlation SQ dimension, polynomially
  related to the one-sided variant
  ([#3204](https://github.com/cslib-community/complexitylib/issues/3204)). Remaining: simulation
  under random classification noise of known and of unknown rate (Kearns's Lemma 2 and
  Theorem 3); the single-sample form of Kearns's Theorem 1 (finite query space and finite VC
  dimension) and a distribution-free variant; the Bshouty–Feldman transfer from statistical to
  correlational queries for a fixed distribution; the worst-case SQ dimension and its comparison
  with the VC dimension (Reyzin's Observations 20 and 21); Feldman's strong SQ dimension
  characterizing strong learning; randomized SQ learners; and Feldman's statistical dimension for
  a specified planted problem, with matching sample and runtime upper bounds. Develop low-degree
  likelihood-ratio and sum-of-squares comparisons where justified, distinguishing restricted-model
  bounds from unrestricted computational hardness. Use the
  [distributional framework](#average-case-complexity).
- **Online learning in the mistake-bound model**
  ([#2908](https://github.com/cslib-community/complexitylib/issues/2908)): the realizable model,
  the halving algorithm, the Littlestone dimension with the standard optimal algorithm (optimal
  mistake bound equals Littlestone dimension), the VC comparison with the threshold gap,
  Novikoff's perceptron bound, WINNOW1 for monotone disjunctions with Littlestone's matching
  `k ⌊log₂ (n / k)⌋` lower bound, and the agnostic upper bound (expected regret
  `2 √(T d log (T + 1))` for Littlestone dimension `d`, Hedge over SOA experts,
  Ben-David–Pál–Shalev-Shwartz 2009, [#3120](https://github.com/cslib-community/complexitylib/issues/3120))
  with Cover's linear lower bound for deterministic learners are in
  `MachineLearning/OnlineLearning/MistakeBound`. Remaining: WINNOW2 for linearly separable Boolean
  functions with separation `δ` and Littlestone's attribute transformations (Littlestone 1988,
  Theorems 9 and 10); the agnostic lower bound `Ω(√(Ldim(C) T))`, adaptive adversaries against
  randomized learners, an unknown horizon (the doubling trick) and the optimal `Θ(√(Ldim(C) T))`
  regret; multiclass and real-valued analogues; online-to-batch conversion into the PAC framework;
  and running-time bounds, since the standard optimal algorithm is a noncomputable specification.
- **Property and distribution testing:** independent repetition of Boolean local tests and BLR
  linearity testing have explicit decision-tree query bounds. Uniformity testing has matching
  `Θ(√n / ε²)` sample bounds for `ε ≤ 1/2` on even domains: the collision tester and Paninski's
  lower bound. Identity testing to any fixed distribution reduces to uniformity on `4n` points
  through Goldreich's kernel, which gives `O(√n / ε²)` samples
  ([#2930](https://github.com/cslib-community/complexitylib/issues/2930)). Closeness testing has
  the two-sample model and the collision-based tolerant `ℓ₂` tester with `O(√b / ε²)` samples
  when both squared `ℓ₂` norms are at most `b`, hence `O(n / ε²)` samples in statistical distance
  ([#3017](https://github.com/cslib-community/complexitylib/issues/3017)). Flattening (split
  distributions along samples of both distributions) gives the optimal closeness tester with
  `m + k ≤ 520 max(n^{2/3} ε^{-4/3}, √n ε^{-2}) + 3` samples of each distribution
  ([#3122](https://github.com/cslib-community/complexitylib/issues/3122)). In the dense graph
  (adjacency-matrix) model, triangle-freeness has a one-sided tester whose query bound depends
  only on `ε`, through Mathlib's triangle removal lemma
  ([#3036](https://github.com/cslib-community/complexitylib/issues/3036)), and bipartiteness has a
  one-sided tester with `O(ε⁻³)` queries following Goldreich–Goldwasser–Ron
  ([#3118](https://github.com/cslib-community/complexitylib/issues/3118)). Every one-sided tester
  with `q` queries for a property closed under relabelling becomes a canonical one-sided tester
  that samples at most `2q` vertices and decides on the induced subgraph (Goldreich–Trevisan,
  one-sided half; [#3180](https://github.com/cslib-community/complexitylib/issues/3180)).
  Monotonicity of Boolean functions on the hypercube `{0,1}ⁿ` has the
  Goldreich–Goldwasser–Lehman–Ron–Samorodnitsky edge tester: by squashing along each coordinate, a
  function ε-far from monotone violates at least an `ε / n` fraction of the edges, so `⌈2n / ε⌉`
  edge trials (`2⌈2n / ε⌉` queries) reject with probability at least `2/3`, and monotone functions
  always pass ([#3257](https://github.com/cslib-community/complexitylib/issues/3257)).
  Remaining: the matching `Ω(n^{2/3} ε^{-4/3} + √n ε^{-2})` closeness lower bound, further access
  models, the odd-domain lower bound, instance-optimal identity testing, tolerant and
  structured-property distribution testing; in the dense graph model, `H`-freeness for general `H`
  (it needs a general removal lemma), sharper query bounds for bipartiteness, `k`-colourability
  with `poly(1/ε)` queries, the two-sided half of Goldreich–Trevisan (canonical testers with `O(q)`
  sample vertices and `O(q²)` queries), and deciding by the property itself when it is closed
  under induced subgraphs (their Proposition D.2, due to Alon) or is a graph partition property
  (Corollary 5.9); for monotonicity, the `Ω(√n)` lower bound for non-adaptive one-sided testers
  (Fischer et al. 2002), larger ranges and hypergrids, and the directed-isoperimetry path testers
  with `Õ(√n / ε²)` queries (Khot–Minzer–Safra); further query and sample lower bounds.
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
  multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding. Beyond
  Chaitin's incompleteness theorem for plain complexity
  ([#3323](https://github.com/cslib-community/complexitylib/issues/3323)): the same theorem for
  the multi-tape `plain` complexity (needs compiling partial recursive functions to `universalTM`
  programs), a prefix-free version, Chaitin's halting probability `Ω` and its randomness,
  Solovay's refinements, and the Kritchman–Raz proof of Gödel's second incompleteness theorem.
  Beyond the plain Kolmogorov–Levin symmetry of information for the Partrec universal method
  ([#3324](https://github.com/cslib-community/complexitylib/issues/3324)): the exact symmetry
  `K(x, y) = K(x) + K(y | x, K(x)) + O(1)` of prefix complexity (Gács, Chaitin); symmetry of
  information for the binary-string models (`condUniversalTM`) and for time-bounded complexity,
  with its connection to one-way functions (Liu–Pass, Hirahara).
- **Quantum computation** ([#896]): channel semantics and approximation costs alongside the
  circuit and measurement semantics, reusing suitable quantum foundations rather than
  incompatible models, and a bridge between the query and circuit models; complete problems for
  BQP; for QMA ([#2876](https://github.com/cslib-community/complexitylib/issues/2876)), error
  reduction from an inverse-polynomial gap, strong error reduction that keeps the witness length,
  `QMA ⊆ A₀PP`, mixed witnesses, QCMA and the local Hamiltonian problem; related query,
  communication and interactive classes, with amplification, containments and complete problems.
  Supply the
  [quantum adversary models](#concurrent-and-quantum-security) needed by cryptographic
  reductions.

- **Quantum information primitives**
  ([#3329](https://github.com/cslib-community/complexitylib/issues/3329)): beyond pure-state,
  ancilla-free no-cloning, single-qubit teleportation and superdense coding, prove the
  Wootters–Zurek form of no-cloning with an input-dependent apparatus register (by the same
  linearity argument) and teleportation of one half of an entangled state, as in entanglement
  swapping (a pure-state statement). Prove Holevo's bound (in particular, superdense coding is
  optimal) and Nayak's bound for quantum random access codes; both need density matrices, von
  Neumann entropy and mutual information. With channel semantics, prove no-cloning for mixed
  states and no-broadcasting.

- **Quantum query separations**
  ([#2991](https://github.com/cslib-community/complexitylib/issues/2991)): beyond the decision
  and search versions of Simon's problem, give the search version polynomial-time
  post-processing (Gaussian elimination over `ZMod 2` in place of the exhaustive `simonSolve`),
  and prove separations in the value-query model. The latter needs quantum states over an
  arbitrary finite query index type rather than `Fin N`; generalizing `State N W` affects
  `Quantum/Search.lean`, `Quantum/Composition.lean`, `Quantum/Grover.lean`,
  `Quantum/UnknownSearch.lean`, `Quantum/Polynomial.lean` and `Quantum/Adversary.lean`. Natural
  later targets are Forrelation and other optimal quantum–classical query separations.
  Deutsch–Jozsa
  ([#3310](https://github.com/cslib-community/complexitylib/issues/3310)) has the exact
  one-query algorithm, the deterministic bound `N/2 + 1` and the constant-query randomized
  algorithm. Next: exact quantum query lower bounds for promise problems via polynomial degree
  (`Q_E ≥ deg/2` on the promise domain), a promise-problem form of `randomizedComplexity`, and
  recursive Fourier sampling (Bernstein–Vazirani's superpolynomial separation).

- **Quantum query lower bounds**
  ([#3239](https://github.com/cslib-community/complexitylib/issues/3239)): Ambainis's relational
  adversary bound (Theorems 2 and 6 of the source) gives the bounded-error parity, majority,
  threshold, Tribes and `AND`-of-`OR`s lower bounds, including promise versions. The containment
  relation between two weight layers gives the Nayak–Wu promise-threshold bound
  `Ω(√(N/Δ) + √(m(N − m))/Δ)` and the `Ω(1/ε)` bound for weight `N/2` against `(1 + ε)N/2`
  (Ambainis, Theorem 5). Next: the approximate-median, approximate-count and `k`th-smallest
  consequences of Nayak–Wu, which need reductions from the weight-layer promise problem, and the
  weighted, spectral and negative-weight (general) adversaries for arbitrary relations.
  Non-Boolean input alphabets (permutation inversion, Theorem 7) need the value-query model
  above.

- **Shor's algorithm** ([#3252](https://github.com/cslib-community/complexitylib/issues/3252)):
  bounded-error polynomial-time integer factoring and discrete logarithms
  in the native uniform quantum-circuit model, with explicit input/output encodings, success
  probabilities and gate-approximation costs. The quantum Fourier transform over `ZMod N` (as a
  unitary matrix) and the exact period-finding measurement for periods `r ∣ N`, with `gcd`
  recovery succeeding with probability `φ(r)/r`, are available at the state level. Remaining:
  the general case `r ∤ N` with continued-fraction recovery, the `Ω(1 / log log r)` totient
  bound, phase estimation, QFT circuits with gate and approximation costs, reversible modular
  exponentiation, and the classical reductions from factoring and discrete logarithms;
  certify uniform circuit generation and polynomial gate bounds alongside correctness.

- **Nonlocal games** ([#3313](https://github.com/cslib-community/complexitylib/issues/3313)):
  beyond CHSH and Tsirelson's bound in the finite-dimensional tensor-product model, give general
  XOR games Tsirelson's vector characterization and its semidefinite program (Cleve–Høyer–Toner–
  Watrous, Theorem 4 and Proposition 5) and the Grothendieck-constant bound on the quantum
  advantage (Theorem 7); mixed shared states and the commuting-operator model, with the inclusion
  of the tensor-product value; parallel repetition of entangled games, alongside the classical theorem
  ([#886](https://github.com/cslib-community/complexitylib/issues/886)); rigidity (self-testing)
  of the CHSH strategy; and the entangled-prover class `MIP*`, toward the optional
  [MIP* = RE](#optional-landmark-projects) project.

### Differential privacy and adaptive data analysis

- Dataset adjacency and `(ε, δ)`-differential privacy for probabilistic programs, with
  postprocessing and adaptive composition. Start with a finite or discrete mechanism proving
  both privacy and utility, including sampling cost and finite-precision error. The foundations
  ([#2867](https://github.com/cslib-community/complexitylib/issues/2867)) and advanced
  composition ([#2977](https://github.com/cslib-community/complexitylib/issues/2977)) leave
  exact-sampling costs for discrete noise, continuous Laplace/Gaussian mechanisms with their
  finite-precision analysis, and Rényi or concentrated privacy accounting.
- Private query answering and private learning, building on the exponential mechanism and the
  sparse vector technique ([#2977](https://github.com/cslib-community/complexitylib/issues/2977));
  privacy–accuracy and sample-complexity lower bounds; then adaptive data-analysis and
  generalization guarantees.
  Keep the adjacency relation, interaction model, privacy parameters and computational resources
  explicit, reusing the probability, oracle-computation and learning APIs.
- **Privacy–accuracy lower bounds**
  ([#3178](https://github.com/cslib-community/complexitylib/issues/3178)): the packing lemma, the
  `Ω(k / ε)` bound for one-way marginals and the Dinur–Nissim reconstruction attack, with its
  consequence that the distortion a private mechanism can guarantee on every database for all
  subset-count queries is linear in the number of rows, are in `Privacy/DifferentialPrivacy`
  (Dwork–Roth Chapter 8), and so is De's `Ω(min(k, d) / ε)` bound over a small universe
  (Theorem 8.8) for row-replacement adjacency. So is the reconstruction attack from `O(n)` random
  `±1` queries (Theorem 8.2), which rules out private error `o(√n)` on a `1 / 2 + η` fraction; its
  constant `((⌊α⌋₊ + 1) / η) ^ 2` gives the source's `(2 α / η) ^ 2` for `α ≥ 1 / 2`, and the
  source's constant fails for `2 α < η ≤ 1 / 5`; `η / 2 ≤ α < 1 / 2` is open. Remaining
  ([#3201](https://github.com/cslib-community/complexitylib/issues/3201)): `(ε, δ)` lower
  bounds via fingerprinting codes. The transfer of Theorem 8.8 to add/remove adjacency on
  histograms is a small open follow-up: group privacy doubles `ε` (covering Dwork–Roth's
  `ε ≤ 1 / 40` with noise `min(k, d) / (2048 ε)`), and the query must be extended from weight-`n`
  histograms to `ℕ ^ d` (McShane in `ℓ₁` with constant `1 / 2`). Small cleanups: move `signDot`
  next to `Cslib.BitString.signVal` with its Hamming-distance identity, and expose the
  window-counting anti-concentration lemma in `Combinatorics/LittlewoodOfford`.

## Algorithms and optimization

### Optimization and duality

- **Linear programming** ([#2976](https://github.com/cslib-community/complexitylib/issues/2976)):
  Fourier–Motzkin elimination, Farkas' lemma, weak and strong duality, the unbounded and
  infeasible outcomes and complementary slackness over any linearly ordered field are in
  `Foundations/LinearAlgebra/Matrix/{FourierMotzkin,Farkas,LinearProgramming}`. The simplex
  method on dictionaries with Bland's rule, its no-cycling theorem, termination within
  `N.choose m - 1` pivots, the optimality and unboundedness certificates and an optimal dual
  solution read off the final dictionary are in `Algorithms/Lean/Simplex`
  ([#3370](https://github.com/cslib-community/complexitylib/issues/3370)). Remaining:
  rational input and output encodings; bit-size bounds on basic solutions and Farkas
  certificates (Cramer's rule with the Hadamard bound), giving LP feasibility in NP ∩ coNP with
  machine-checked certificate verifiers; and a polynomial-time LP algorithm (ellipsoid or
  interior point) with bit complexity and intermediate precision accounted for. For the simplex
  method: Phase I (an initial feasible dictionary or an infeasibility certificate); the
  Klee–Minty cube on which Dantzig's rule makes `2ⁿ - 1` pivots; smoothed analysis
  (Spielman–Teng); strongly polynomial special cases; and a costed implementation.
- **Lattice basis reduction** ([#3235](https://github.com/cslib-community/complexitylib/issues/3235)):
  `δ`-reduced bases, the LLL approximation `‖b₁‖² ≤ (4/(4δ-1))^{n-1} ‖x‖²` (paper indexing,
  `n` vectors) to the shortest vector (Lenstra–Lenstra–Lovász Proposition (1.11)), the potential
  argument bounding the number of exchange steps by `O(n² log B)` for integral Gram matrices, and
  an executable LLL (`δ = 3/4`, exact rational Gram–Schmidt) on integer bases whose output is
  reduced and spans the same lattice are in `Algorithms/LatticeReduction`, over Gram–Schmidt
  facts in `Foundations/Analysis/InnerProductSpace/GramSchmidtOrtho`. Babai's nearest-plane
  algorithm ([#3486](https://github.com/cslib-community/complexitylib/issues/3486)) is there too:
  the abstract bound `‖x - y‖² ≤ (∑_{i<n} (4/(4δ-1))ⁱ) ‖x - v‖²` for `δ`-reduced bases, and an
  executable LLL-then-round algorithm on integer bases and targets that solves CVP within `2^{n/2}`.
  Remaining: a cost model for the executable LLL with the `O(n⁴ log B)` arithmetic-operation bound
  (the current version recomputes Gram–Schmidt every round) and the `O(n log B)` bit-size bound of
  (1.26), then `ComputableInPolyTime` statements for LLL and Babai; an executable reduction with
  `δ` near `1` (at `δ = 1` the abstract bound already gives Babai's factor `2 (2/√3)ⁿ⁻¹` for
  `1`-reduced bases, but `lll` fixes `δ = 3/4`) and rational targets for Babai; then applications
  (simultaneous Diophantine approximation, polynomial factorization over `ℚ`).
- **Separation and optimization:** a precise oracle interface and a separation–optimization
  equivalence with its representation, accuracy and well-boundedness hypotheses. Extend to
  convex optimization through explicit oracle and numerical-error contracts.
- **Lovász theta and perfect graphs** ([#2998](https://github.com/cslib-community/complexitylib/issues/2998)):
  Shannon capacity, the orthonormal-representation theta function, the sandwich
  `α(G) ≤ ϑ(G) ≤ χ(Ḡ)`, `Θ(G) ≤ ϑ(G)` and `Θ(C₅) = √5` are in
  `Foundations/Combinatorics/SimpleGraph`. Remaining: the equivalent SDP and eigenvalue
  formulations of `ϑ`, and its polynomial-time approximation by the ellipsoid method
  (Grötschel–Lovász–Schrijver), which makes clique number and chromatic number of perfect graphs
  polynomial-time computable. This waits on the separation–optimization interface.
- **Primal–dual approximation and multiplicative weights:** reusable analyses with vertex cover
  and set cover as first primal–dual clients. Real-valued regret bounds for weighted majority,
  multiplicative weights and Hedge (with tuned learning rates), and the algorithmic minimax
  theorem for zero-sum games, are in `MachineLearning/OnlineLearning`
  ([#2874](https://github.com/cslib-community/complexitylib/issues/2874)). Remaining:
  randomized weighted majority and sampled Hedge as probabilistic computations, the regret lower
  bound, finite-precision implementations with charged running time, and applications to packing
  and covering LPs, boosting and learning.
- **Online convex optimization:** projected online gradient descent and its `O(GD√T)` and
  strongly convex `O(log T)` regret bounds (Zinkevich; Hazan Theorems 3.1 and 3.3), over the
  metric projection onto complete convex sets, are in `MachineLearning/OnlineLearning`
  ([#2983](https://github.com/cslib-community/complexitylib/issues/2983)). Remaining:
  follow-the-regularized-leader and online mirror descent (recovering Hedge as the entropic
  case), the `Ω(GD√T)` lower bound, online Newton step for exp-concave losses, Blackwell
  approachability and calibration, and finite-precision implementations.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations),
reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** a native augmenting-path algorithm with charged runtime (integral
  max-flow/min-cut, a `TimeM` Edmonds–Karp solver, Hopcroft–Karp bipartite matching and the
  `O(n³)` Hungarian method with Egerváry duality for the assignment problem are in
  `Algorithms/Lean/MaxFlow`); then minimum-cost flow on the residual network, reusing the
  potential, weak-duality and complementary-slackness lemmas of `WeightedMatching`. Remaining
  matching directions: the decomposition of `M ⊕ M*` into vertex-disjoint augmenting paths,
  rectangular and sparse weighted bipartite matching, and a sparse Hopcroft–Karp entry point that
  also charges construction of the adjacency lists. General (non-bipartite) matching with
  blossoms (weighted and unweighted;
  [#3337](https://github.com/cslib-community/complexitylib/issues/3337)): Berge's lemma and the
  Tutte–Berge formula are proved in `Foundations/Combinatorics/SimpleGraph/{Berge,TutteBerge}`;
  still open are Edmonds' blossom-contraction lemma, an executable blossom algorithm with its
  `O(|V|²|E|)` bound, weighted general matching, and the Gallai–Edmonds decomposition.
- **Global minimum cut** ([#3369](https://github.com/cslib-community/complexitylib/issues/3369)):
  beyond Karger's and Karger–Stein's randomized algorithms (`Algorithms/WordRAM/Karger`) and the
  deterministic Stoer–Wagner algorithm with the maximum adjacency ordering lemma and an `O(n³)`
  `TimeM` bound on natural-number weights (`Algorithms/Lean/StoerWagner`,
  `WeightedCut/MAOrdering`), both built on the probability-free contraction API of
  `WeightedCut/Contraction`, and the per-cut bound `1 / C(n, 2)` of the contraction algorithm with
  the `C(n, 2)` bound on the number of minimum cuts (`Algorithms/Lean/Karger/MinCutCount`,
  `WeightedCut/Blocks`, [#3489](https://github.com/cslib-community/complexitylib/issues/3489)):
  the `O(n m + n² log n)` priority-queue version, real weights,
  Nagamochi–Ibaraki sparse certificates for `k`-edge-connectivity,
  Karger's near-linear minimum cut algorithm, the `O((2n)^(2α))` bound on `α`-minimal cuts, the
  enumeration and cactus representation of all minimum cuts, the per-cut bound for recursive
  Karger–Stein, deriving the untracked Karger theorems from the block-tracking ones
  ([#3539](https://github.com/cslib-community/complexitylib/issues/3539)), and Queyranne's
  minimization of symmetric submodular
  functions (which generalizes the maximum adjacency argument to hypergraph cuts).
- **Gomory–Hu trees** ([#3422](https://github.com/cslib-community/complexitylib/issues/3422)):
  remaining after the existence theorem for cut-equivalent trees, flow-equivalence, the
  minimum-cut triangle inequality, the `n - 1` bound on distinct minimum cut values, and Gusfield's
  construction with `n - 1` Edmonds–Karp calls and its `TimeM` bound (`Algorithms/Lean/GomoryHu`,
  [#3285](https://github.com/cslib-community/complexitylib/issues/3285),
  [#3320](https://github.com/cslib-community/complexitylib/issues/3320)): returning the tree's
  edge weights from the maximum flow values, and real-valued capacities.
- **Push–relabel maximum flow** ([#3373](https://github.com/cslib-community/complexitylib/issues/3373)):
  remaining after preflows, valid labelings, optimality at termination with a gap minimum cut, the
  operation bounds of the generic Goldberg–Tarjan algorithm and a verified executable scheduler
  (`Algorithms/Lean/MaxFlow/{Preflow,PushRelabel}`): a charged `TimeM` version with current-arc
  scanning (`O(|V|² |E|)`), the FIFO and relabel-to-front rules (`O(|V|³)`), highest-label
  selection (`O(|V|² √|E|)`), gap and global-relabelling heuristics, and dynamic trees
  (`O(|V| |E| log(|V|² / |E|))`).
- **Menger's theorem** ([#3409](https://github.com/cslib-community/complexitylib/issues/3409)):
  remaining after the two-terminal arc, edge and vertex forms for finite digraphs and simple
  graphs, derived from integral max-flow/min-cut via flow decomposition
  (`Algorithms/Lean/MaxFlow/Menger`, `MaxFlow/Decomposition`,
  [#3380](https://github.com/cslib-community/complexitylib/issues/3380)): the directed-multigraph
  (capacity) form, the `A`–`B` set version and the global `k`-connectivity form, Menger for
  infinite graphs (the Erdős–Menger conjecture, proved by Aharoni and Berger), and a native
  `k`-connectivity test with a charged running-time bound.
- **Algebraic matching** ([#3052](https://github.com/cslib-community/complexitylib/issues/3052)):
  remaining after Edmonds' determinant criterion and Lovász's randomized test for bipartite
  graphs (`Algorithms/Matching/Edmonds`), the bipartite Mulmuley–Vazirani–Vazirani core
  (`Algorithms/Matching/MVV`), and Tutte's determinant criterion with the same test for general
  graphs (`Algorithms/Matching/Tutte`): MVV for general graphs (its Pfaffian form), a machine-level
  running-time certificate for the determinant test, and an RNC implementation.
- **Blocking-flow maximum flow** ([#3328](https://github.com/cslib-community/complexitylib/issues/3328)):
  after level networks, the Dinitz phase lemma, the `|V| - 1` phase bound and a verified executable
  Dinitz solver with a greedy blocking-flow search (`Algorithms/Lean/MaxFlow/{LevelGraph,Dinitz}`),
  a charged `TimeM` version with the current-arc depth-first blocking-flow search (`O(|V| |E|)`
  per phase, `O(|V|^2 |E|)` overall); Sleator–Tarjan dynamic trees (`O(|V| |E| log |V|)`); the
  Even–Tarjan unit-capacity bounds `O(|E| · min(|V|^{2/3}, |E|^{1/2}))`; Karzanov's `O(|V|^3)`
  preflows and push–relabel.
- **Auction algorithms** ([#3317](https://github.com/cslib-community/complexitylib/issues/3317)):
  remaining after Bertsekas's Gauss–Seidel auction for square, complete integer assignment
  instances (`Algorithms/Lean/Assignment`: `ε`-complementary slackness, termination within
  `n (C + ε) / ε + 1` bids, `n ε`-optimality and exact optimality after scaling by `n + 1`):
  `ε`-scaling and its `O(n A log (n C))` bound, a charged `TimeM` implementation, the Jacobi,
  reverse and asymmetric auctions, sparse and rectangular instances, a bridge to the Hungarian
  method's potentials, and `ε`-relaxation for minimum-cost flow.
- **Graph search and shortest paths** ([#3053](https://github.com/cslib-community/complexitylib/issues/3053)):
  after `TimeM` depth-first search, topological sort and Bellman–Ford
  (`Algorithms/Lean/{DFS,BellmanFord}`), strongly connected components in linear time with the
  linear-time 2-SAT algorithm as a client of the `TwoSAT` problem module; the Bellman–Ford
  predecessor tree; and bridges from Bellman–Ford to Dijkstra's distances and to the matrix
  shortest-path model.
- **Matroids:** Edmonds' matroid intersection theorem, the exchange-graph augmenting-path step,
  König's theorem via partition matroids and a verified executable solver with exact
  independence-oracle query counts are in `Algorithms/Lean/Matroid/Intersection` and
  `Algorithms/Lean/Query/Matroid/Intersection`. Remaining: `TimeM` costs for the solver's host
  computation, kept separate from the query counts
  ([#2018](https://github.com/cslib-community/complexitylib/issues/2018)); then weighted matroid
  intersection.
- **Submodular optimization:** further constraints and approximation bounds beyond the
  cardinality-constrained `1 - 1/e` greedy and the Fisher–Nemhauser–Wolsey `1/(p+1)` greedy over
  `p`-systems (`1/2` over a matroid, with separately charged value and independence queries;
  [#3145](https://github.com/cslib-community/complexitylib/issues/3145)): the continuous greedy
  with pipage rounding for `1 - 1/e` over a matroid, the `α/(p+α)` bound for greedy with an
  `α`-approximate marginal-gain oracle, knapsack constraints and non-monotone objectives, charging
  value-oracle calls separately from their concrete realizations.
- **Stable matching** ([#2990](https://github.com/cslib-community/complexitylib/issues/2990)):
  beyond the one-to-one, complete-list deferred-acceptance development in
  `Algorithms/Lean/StableMatching` (stability, the `n^2 - n + 1` proposal bound, optimality, the
  lattice, the blocking lemma, strategy-proofness, and Roth's impossibility theorem for three
  agents per side) and its incomplete-list extension in `StableMatching/Incomplete` (unequal
  sides, deferred acceptance, optimality, and the one-to-one rural hospitals theorem): Roth's
  theorem for every `n ≥ 3` by padding the witness, the lattice, blocking lemma and incentive
  (strategy-proofness) results for incomplete lists, many-to-one college admissions with the
  capacitated rural hospitals theorem, ties, rotations and the stable-matching poset, stable
  roommates, and a charged native implementation in `O(n^2)` time.
- **Housing markets and top trading cycles** ([#3286](https://github.com/cslib-community/complexitylib/issues/3286)):
  beyond the Shapley–Scarf development in `Algorithms/Lean/HousingMarket` (TTC as the unique
  strict-core and competitive allocation, individual rationality, Pareto efficiency and
  strategy-proofness): house allocation with existing tenants (Abdulkadiroğlu–Sönmez's
  you-request-my-house-I-get-your-turn), Ma's characterization of TTC by individual rationality,
  Pareto efficiency and strategy-proofness, group strategy-proofness, indifferences (top trading
  absorbing sets), and a charged implementation of TTC in `O(n^2)` time.
- **Classical approximation algorithms** ([#2869](https://github.com/cslib-community/complexitylib/issues/2869)):
  remaining after greedy set cover, maximal-matching vertex cover, the MST tour and Christofides'
  `3/2` bound for metric TSP (`Algorithms/Lean/{SetCover,VertexCover,TSP}`): machine-level
  polynomial-time certificates for greedy set cover and for Kruskal-based TSP tours on encoded
  matrices. Christofides' algorithm
  ([#3055](https://github.com/cslib-community/complexitylib/issues/3055)) currently matches by
  exhaustive search; it still needs a polynomial-time minimum-weight perfect matching (Edmonds'
  blossom algorithm) for an end-to-end polynomial-time statement, a tightness family approaching
  `3/2`, and possibly the Karlin–Klein–Oveis Gharan `3/2 - 10^{-36}` improvement as a long-range
  target. LP-based and primal–dual analyses of the same problems belong to the primal–dual
  approximation direction under Optimization and duality.
- **Steiner tree** ([#3309](https://github.com/cslib-community/complexitylib/issues/3309)):
  remaining after the MST 2-approximation, both metric and on graphs through the metric completion,
  with the sharp factor `2 (1 - 1/|R|)` (`Algorithms/Lean/SteinerTree`). Next: Kou–Markowsky–Berman's
  leaf bound `2 (1 - 1/ℓ)` and their pruning steps; Zelikovsky's `11/6` and Robins–Zelikovsky's
  `1.55` greedy algorithms; the Byrka–Grandoni–Rothvoß–Sanità LP-rounding bounds (`1.694` in
  Williamson–Shmoys Section 12.3, and `ln 4 + ε`); NP-hardness of the decision version (Karp, within
  [#2904](https://github.com/cslib-community/complexitylib/issues/2904)), already with unit
  weights by reduction from `VertexCover` (Garey and Johnson ND12, locator from secondary sources:
  a root adjacent to every vertex and one terminal per edge, adjacent to its endpoints); and a
  polynomial-time
  certificate for the heuristic with an executable shortest-path oracle.
- **Metric k-center** ([#3281](https://github.com/cslib-community/complexitylib/issues/3281)):
  remaining after Gonzalez's farthest-first 2-approximation, the combinatorial dominating-set
  gap (`Algorithms/Lean/KCenter`), NP-completeness of dominating set on the encoded `Graph`
  problems ([#3416](https://github.com/cslib-community/complexitylib/issues/3416),
  `Problems/DominatingSet`) and Theorem 2.4, that a polynomial-time `ρ`-approximation with
  `ρ < 2` implies `P = NP`
  ([#3515](https://github.com/cslib-community/complexitylib/issues/3515),
  `PCP/Approximation/KCenter`): a machine-level running time for Gonzalez's algorithm; the
  Hochbaum–Shmoys threshold algorithm; and k-supplier and k-median.

### Sorting and selection

- **Comparison selection** ([#3279](https://github.com/cslib-community/complexitylib/issues/3279)):
  groups-of-five median-of-medians selection in cslib's comparison-query model, correct for
  total preorders and making at most `37 n` comparisons under every oracle, is in
  `Algorithms/Lean/Query/Select`. Remaining: sharper constants for the same algorithm (a
  six-comparison median of five, and reusing the group comparisons in the partition); the
  `5.4305 n` bound of Blum, Floyd, Pratt, Rivest and Tarjan for their refined `PICK` and Dor and
  Zwick's `2.95 n` median bound; group-size variants such as groups of three or seven;
  comparison lower bounds (`n − 1` for the minimum, `⌈3n/2⌉ − 2` for the minimum and maximum
  together, and lower bounds for the median); and a word-RAM implementation with charged
  instruction counts.

### Online algorithms and competitive analysis

- Request sequences, online strategies, offline optima and competitive ratios with additive
  constants; distinguish deterministic and randomized strategies and oblivious and adaptive
  adversaries. Compare algorithms in the same action and cost model, including initialization.
- **Adaptive search trees:** working-set and dynamic-finger bounds for splay trees, and a BST
  access-and-rotation model with Wilber-style lower bounds. State dynamic optimality as a
  conjectural research target with explicit strategy and sequence quantifiers.
- **Beyond deterministic ski rental and list update:** randomized strategies against an oblivious
  adversary (`Online/Randomized`) and the tight discrete randomized ski-rental ratio
  `1/(1 - (1 - 1/B)^B) ≤ e/(e-1)`, with upper and lower bounds, are in
  `Online/SkiRental/Randomized`
  ([#3492](https://github.com/cslib-community/complexitylib/issues/3492)), extending deterministic
  ski rental and move-to-front
  ([#3057](https://github.com/cslib-community/complexitylib/issues/3057)). Remaining (no tracking
  issue yet): adaptive adversaries for randomized strategies, continuous-time ski rental, the
  asymptotic `e/(e-1)` lower bound with an additive constant, randomized list update (BIT, COMB),
  randomized paging (marking, `H_k`; needs a behavioural or bounded-horizon variant of the
  countably supported `RandStrategy`), and list update with insertions and deletions.
- **Optimal stopping:** `Probability/OptimalStopping/*` covers the rank-based secretary problem
  (exact cutoff-rule success, optimality among all rank-based rules, `1/e` bounds and limit), the
  single-threshold `½` prophet inequality for independent discrete (`PMF`) laws with tightness
  and Samuel-Cahn's median threshold without hypotheses
  ([#2913](https://github.com/cslib-community/complexitylib/issues/2913)), and the i.i.d.
  `1 - (1 - 1/n)ⁿ ≥ 1 - 1/e` bound for one randomized threshold and for the optimal gambler
  ([#3092](https://github.com/cslib-community/complexitylib/issues/3092)). Extend to the tight
  i.i.d. constant `≈0.745`, prophet secretary and random-order models, matroid and
  multiple-choice prophet inequalities, the full-information secretary problem, a general
  mixtures theorem for randomized rules (only the coin-tie threshold case,
  `tieExpectedReward_le_valueFrom`, is proved), and the posted-price mechanism corollary.
- **`k`-server** ([#3287](https://github.com/cslib-community/complexitylib/issues/3287)):
  `DataStructure/KServer/*` covers the deterministic lower bound `k` on every metric with at least
  `k + 1` points (Manasse–McGeoch–Sleator) and the `k`-competitiveness of Double Coverage on the
  integer line (Chrobak–Karloff–Payne–Vishwanathan). Remaining: the Manasse–McGeoch–Sleator bound
  `k / (k - h + 1)` against `h < k` offline servers, Double Coverage on trees (Chrobak–Larmore),
  the work-function algorithm's `2k - 1` bound (Koutsoupias–Papadimitriou), the `k`-server
  conjecture as a research target with explicit quantifiers, the `k = 2` case on every metric,
  randomized `k`-server, and the offline optimum by min-cost flow.
- **Online bin packing** ([#2964](https://github.com/cslib-community/complexitylib/issues/2964)):
  `Algorithms/Lean/BinPacking/{Online,OnlineLowerBound}` covers deterministic online packers and
  Yao's `3/2` lower bound, which with First Fit's `17/10` brackets the deterministic asymptotic
  ratio in `[3/2, 17/10]`. Remaining: the stronger lower bounds of Brown–Liang (`1.536`), van Vliet
  (`1.5401`), Balogh–Békési–Galambos (`248/161`) and the fully adaptive constructions; Harmonic-type
  upper bounds; randomized lower bounds; and an `Online.Problem` instance (a bin-packing problem
  charging `1` per opened bin, `OnlinePacker` as a `DetStrategy`, and a `not_isCompetitive_of_lt`
  corollary).

### Algorithmic game theory ([#2900](https://github.com/cslib-community/complexitylib/issues/2900))

- **Computing equilibria:** finding a pure Nash equilibrium of an explicit congestion game is in
  `PLS` (`GameTheory/Congestion/PLS.lean`,
  [#3149](https://github.com/cslib-community/complexitylib/issues/3149)). Extend to
  PLS-completeness (Fabrikant–Papadimitriou–Talwar) by a reduction from local Max-Cut, which itself
  needs Schäffer–Yannakakis PLS-completeness or a chain from `LocalOpt`; the symmetric case;
  succinct game encodings; polynomial-time algorithms for symmetric network congestion games;
  exponentially long better-response paths. Mixed Nash equilibria of finite games
  (Nash's theorem) and PPAD-completeness of computing them.
- **Bimatrix games and Lemke–Howson:** `GameTheory/Bimatrix/*` proves the undirected parity
  argument, so a nondegenerate bimatrix game has an odd number of Nash equilibria
  ([#3334](https://github.com/cslib-community/complexitylib/issues/3334)). Remaining, tracked in
  [#3391](https://github.com/cslib-community/complexitylib/issues/3391): two-player Nash in PPAD.
  This needs an orientation of the Lemke–Howson paths (Shapley's index), bit-size bounds on the
  rational vertices, an encoding of games as a TFNP search problem, and a polynomial-time pivoting
  map into the end-of-line principle. Also remaining: degenerate games (lexicographic
  perturbation, giving Nash's theorem for all bimatrix games), the Lemke–Howson path as an
  algorithm, and the Savani–von Stengel exponential lower bound. Infrastructure: move
  `IsMixedStrategy` and its simplex lemmas to a game-agnostic `GameTheory/MixedStrategy` module
  shared with `Strategic/Mixed`, and relate `Matrix.IsVertex` to `Set.extremePoints`.
- **Equilibrium concepts and dynamics:** mixed and correlated equilibria between pure Nash and
  coarse correlated equilibria; swap regret and convergence to correlated equilibria, extending
  the Hedge dynamics of [#3034](https://github.com/cslib-community/complexitylib/issues/3034);
  last-iterate convergence of no-regret dynamics; bandit feedback and sampled play; convergence
  time of better-response dynamics in potential games.
- **Price of anarchy:** Wardrop equilibrium existence and essential uniqueness for continuous
  nondecreasing latencies (Beckmann's convex potential); beyond the Pigou bound, worst-case
  networks for latency classes without the constant functions (parallel links and unions of paths)
  and the M/M/1 and M/G/1 delay bounds (Roughgarden 2003, Theorems 4.5 and 4.9 and Section 5); the
  tight price of stability of affine congestion games, below the potential-method bound `2`;
  strong Nash equilibria of fair cost-sharing games and their price of anarchy; price-of-stability
  bounds for undirected and weighted network design; Braess's paradox; weighted and mixed-strategy
  atomic congestion games; the Monderer–Shapley characterization of potential games as congestion
  games.

### Mechanism design ([#2947](https://github.com/cslib-community/complexitylib/issues/2947))

Single-parameter mechanisms with Myerson's Lemma for arbitrary monotone allocation rules, the
Vickrey auction, knapsack auctions with welfare-maximizing rules, Groves/VCG mechanisms over
finite outcome sets, Myerson's optimal auction for independent regular distributions with
densities (expected revenue equals expected virtual welfare; Vickrey with a reserve price), and the
Bayes–Nash characterization with revenue equivalence and the symmetric first-price equilibrium
`b(v) = (n - 1) v / n` for i.i.d. uniform values
([#3173](https://github.com/cslib-community/complexitylib/issues/3173)) are in
`GameTheory/Mechanism`. Remaining directions:

- **Single-parameter corollaries:** the sponsored-search payment formula (rank-by-bid
  allocation with slot click-through rates) and the greedy knapsack rule with its monotonicity
  and ½-approximation. State allocation algorithms with charged running time, so that
  approximation and truthfulness are both proved for an actual algorithm.
- **Revenue maximization beyond the regular DSIC case:** ironing for irregular distributions;
  regular distributions (Lecture 5, Definition 3.1) whose virtual valuation is unbounded below at
  `0`, such as `f(v) = 2v` on `[0, 1]`, which the endpoint convention of `IsRegular` excludes (this
  needs an explicit treatment of zero bids);
  optimality among Bayesian incentive-compatible mechanisms (the revelation principle, on top of
  the interim rules of `Mechanism.Bayesian`); a measurable virtual-welfare maximizer for a finite
  feasible set, removing the measurability hypothesis; and distributions without a bounded
  density (atoms, unbounded support).
- **Bayes–Nash equilibria of auctions:** the symmetric first-price equilibrium
  `b(v) = E[max of the other values | it is below v]` for general i.i.d. priors with densities and
  its uniqueness (Hartline, *Mechanism Design and Approximation*, §2.8–2.9); the all-pay auction;
  truthful bidding as a Bayes–Nash equilibrium of every DSIC mechanism; and the exact optimal
  revenue `(n - 1 + 2^(-n)) / (n + 1)` for i.i.d. uniform values (`5/12` against the
  second-price `1/3` for two bidders).
- **Multi-parameter characterizations:** Groves mechanisms as the only DSIC welfare maximizers
  on rich valuation domains (Green–Laffont, Holmström), and limits of VCG such as revenue
  monotonicity and collusion.

### Social choice ([#3282](https://github.com/cslib-community/complexitylib/issues/3282))

Social welfare functions on strict rankings and Arrow's impossibility theorem (Geanakoplos's
pivotal-voter proof) are in `GameTheory/SocialChoice`, with social choice functions, the
equivalence of strategy-proofness and Maskin monotonicity, and the Gibbard–Satterthwaite and
Muller–Satterthwaite theorems for a range of at least three alternatives (Nisan's reduction to
Arrow's theorem). Remaining directions:

- **Strategy-proofness beyond the full domain:** the Gibbard–Satterthwaite theorem allowing
  individual indifference, Gibbard's 1977 theorem on random social choice functions (strategy-proof
  lotteries are mixtures of unilateral and duple rules), and escape routes such as single-peaked
  domains (the median voter rule, Moulin's characterization of strategy-proof rules there).
- **Characterizations:** May's theorem (majority rule is the only anonymous, neutral, positively
  responsive rule on two alternatives); derive the individual-weak-order corollary of Arrow's
  theorem (by an IIA reduction to strict profiles); the infinite-electorate counterexample from a
  nonprincipal ultrafilter (Fishburn 1970).
- **Quantitative Arrow:** Kalai's Fourier-analytic bound on the probability of a Condorcet
  paradox and its robust version via FKN, tracked under
  [#2131](https://github.com/cslib-community/complexitylib/issues/2131).
- **Computational social choice:** polynomial-time manipulation of greedy-manipulable rules and
  NP-hardness of manipulating second-order Copeland (Bartholdi–Tovey–Trick 1989), and the
  complexity of winner determination for Dodgson and Kemeny rules, with explicit profile
  encodings and charged running time.

### Structural graph algorithms

- **Dynamic programming over tree decompositions**
  ([#2927](https://github.com/cslib-community/complexitylib/issues/2927)): a reusable evaluator
  over a supplied rooted decomposition
  (`Foundations/Combinatorics/SimpleGraph/TreeDecomposition`), with state-space, transition, join
  and runtime bounds, generalizing the mask-indexed tables and charged loops of the executable
  independent-set program `mwisFPT`; coloring and SAT/CSP decision and counting clients that
  specify the graph whose width is measured; normalizing the node count so runtimes are stated in
  the number of vertices; and an encoded treewidth parameter connected to `FPT`. Also: nice
  decompositions, treewidth under minors, and its grid and separator characterizations.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style
  theorem with computable parameter dependence on width and formula size. Keep the supplied
  decomposition and its encoding explicit; certify decomposition finding separately. Connect
  the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Exact fixed-field sampling:** `Languages/Probabilistic/Sampling/F4.lean` samples Mathlib's
  four-element quadratic field using two fair bits, with encoded arithmetic and sampler
  certificates in `Computability/Probabilistic/Sampling/F4.lean`.
  `Circuit/Arithmetic/EvaluationTime.lean` certifies the full existing code trace uniformly in the
  runtime circuit and input over any fixed finite semiring, with binary indices and an F4 client.
  The public circuit-bound VOLE session (#2688) consumes F4 and gives single-copy error 5/8.
  The shared `Circuit/Encoding/Check.lean` validates the existing gate-code predicate with
  certified binary arity, including arithmetic codes and malformed huge indices/arity (#2770).
  Output/count validation and complete native circuit-bound VOLE execution (#2765; #643;
  prerequisite #2738), growing extension-field arithmetic, raw-bit adversarial transport (#2744)
  and fresh-session amplification remain separate endpoints.
- **Entropy-optimal sampling from fair coins:** `Probability/DDGTree` and
  `Probability/DDGTree/KnuthYao` prove the Knuth–Yao bound `H(p) ≤ E[T]` for every DDG tree
  generating `p`, and `E[T] < H(p) + 2` with optimality for the Knuth–Yao tree. They also prove
  the dyadic equality characterization, all for distributions on a finite type
  ([#3360](https://github.com/cslib-community/complexitylib/issues/3360)). Extend to countable
  support and infinite entropy. For rational `p`, implement the Knuth–Yao sampler as a native
  fair-coin program whose output law and expected time are certified (an `IsPPTOn`-style
  certificate in expected time), as in Saad–Freer–Rinard–Mansinghka's finite-precision
  entropy-optimal samplers.
- **Markov-chain sampling:** `Probability/MarkovChain/*` provides discrete kernels,
  stationarity, reversibility, total-variation mixing times, Markovian couplings, reversible
  Metropolis chains and path coupling, with the lazy hypercube walk
  (`Probability/BitString/LazyRandomWalk`, #2857) and Glauber dynamics for `q > 2Δ` colorings
  (`Probability/MarkovChain/Coloring`, #2933) as clients. Extend with conductance,
  canonical-path and spectral-gap arguments. Approximate counting of colorings from samples
  (`Probability/MarkovChain/Coloring/Count`, with the generic product estimator in
  `Probability/Product/Estimator`) is in place as a distributional statement; charge its
  `n t a` Glauber updates in a cost model to obtain an FPRAS in the sense of `Classes/FPRAS`.
  Implement Metropolis sampling for encoded rational target weights, charging initialization,
  arithmetic and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling:** `Classes/FPRAS` and `Classes/FPAUS` give the two
  interfaces, and `Classes/FPAUS/FPRAS` proves FPAUS ⇒ FPRAS for one-bit self-reducible
  witness families ([#3039](https://github.com/cslib-community/complexitylib/issues/3039)).
  `Classes/FPAUS/Sampler` proves the output-law half of the converse: the Jerrum–Valiant–Vazirani
  sampler built from an approximate counter is within statistical distance `2 ^ (-q)` of uniform.
  Certify that sampler as strict PPT when the counter is an FPRAS, giving the class inclusion
  FPRAS ⇒ FPAUS. Allow self-reductions fixing several symbols per step, and instantiate both
  directions for concrete relations such as DNF assignments.
- Extend to randomized approximate counting for matchings and permanents of nonnegative
  rational matrices through explicit mixing and reduction theorems. Reuse the coupling and
  expander APIs and connect to the separate Stockmeyer oracle-counting track where their
  hypotheses agree.
- **Permanent bounds** ([#3377](https://github.com/cslib-community/complexitylib/issues/3377)):
  Brégman's upper bound for 0/1 matrices and bipartite perfect matchings, with equality for
  disjoint unions of `K_{d,d}`, is in `Foundations/Combinatorics/Bregman`. Remaining: extensions
  of the bound to nonnegative real matrices (e.g. Soules 2000), the van der Waerden lower bound
  for doubly stochastic matrices (Egorychev–Falikman, or Gurvits's capacity proof), the
  Kahn–Lovász bound for perfect matchings of general graphs, and their use in
  approximate-counting analyses.

### Constructive probabilistic methods

- **Moser–Tardos resampling:** `Logics/Propositional/CNF/Moser*` runs Moser's `k`-SAT
  resampling algorithm on an explicit tape and bounds its resamplings by entropy compression when
  every clause shares a variable with fewer than `2 ^ (k - 3)` others
  ([#2879](https://github.com/cslib-community/complexitylib/issues/2879)).
  `Probability/MoserTardos` proves the general variable form (Moser–Tardos Theorem 1.2): under the
  asymmetric local-lemma hypothesis, every valid selection rule resamples `A` at most
  `x(A) / (1 - x(A))` times in expectation, and the algorithm terminates almost surely
  ([#3096](https://github.com/cslib-community/complexitylib/issues/3096)). Derive the symmetric
  `e p (d + 1) ≤ 1` form and the `k`-SAT instance from it, prove the parallel and derandomized
  versions (Theorems 1.3–1.4) and the lopsided form, and add native sampling and event-detection
  costs. The Kolmogorov form of the argument
  is relative to an explicit decoder
  ([#3043](https://github.com/cslib-community/complexitylib/issues/3043)); implement the decoder
  as a multi-tape machine taking the formula to transfer it to the conditional universal
  complexity `condPlain`.
- **Conditional expectations and pessimistic estimators:** algorithmic alteration, and coloring,
  MAX-CUT or combinatorial-construction clients of the certified greedy choice rule
  (`Cslib.PessimisticEstimator.greedy_spec`). Preserve the quantitative guarantee when converting
  an existence argument into a deterministic or randomized algorithm.
- **Small sample spaces** ([#2935](https://github.com/cslib-community/complexitylib/issues/2935)):
  searching a `k`-wise independent space finds an assignment as good as a uniformly random one on
  clauses of at least `k` distinct literals (`exists_two_pow_mul_countUnsat_le`). The
  polynomial-time search is certified only for the three-wise parity space. Remaining: a runtime
  certificate for searching the trinomial-field space
  (`exists_assignments_two_pow_mul_countUnsat_le`) for fixed `k > 3`. Further directions are
  small-bias and almost `k`-wise independent spaces and their clients.

### Randomized verification and fingerprinting

- **Fingerprinting** ([#2980](https://github.com/cslib-community/complexitylib/issues/2980)):
  Freivalds' matrix-product verifier with exact `TimeM` operation counts and `(1/|S|)^k`
  soundness for admissible random-vector encodings is in `Algorithms/Lean/Freivalds` and
  `Probability/Freivalds`. Remaining: Karp–Rabin fingerprints (random evaluation point over a
  finite field, and random prime modulus with explicit prime-counting bounds), a rolling-hash
  pattern matcher with charged updates and a union bound over all windows, and the private-coin
  `O(log n)` equality protocol in `Communication/Randomized`. Native machine or RAM realizations
  with bit-level arithmetic costs are a separate endpoint.

### String algorithms

- **Suffix arrays** ([#3331](https://github.com/cslib-community/complexitylib/issues/3331)):
  `Algorithms/Lean/SuffixArray` has the suffix-array specification with uniqueness, a sort-based
  reference construction, Kasai et al.'s LCP construction with at most `2|w|` character
  comparisons, and plain binary-search pattern matching with at most `2|p|(⌊log₂ n⌋ + 1)`
  comparisons. Remaining: linear-time construction (SA-IS of Nong, Zhang and Chan, or the DC3
  skew algorithm of Kärkkäinen and Sanders) with a charged cost model for integer alphabets; a
  comparison-count bound for the sort-based reference construction (through `mergeSortM` with a
  charged suffix comparator);
  Manber–Myers `O(|p| + log n)` search with precomputed LCP information; suffix trees (Ukkonen or
  McCreight construction) and their equivalence with suffix arrays plus LCP arrays; and
  applications such as longest repeated substring and the Burrows–Wheeler transform.
- **Z-algorithm** ([#3516](https://github.com/cslib-community/complexitylib/issues/3516)):
  `Algorithms/Lean/ZFunction` has the Z-function specification, Gusfield's Z-algorithm with exact
  values and at most `2|s| - 3` character comparisons on every input, and exact matching through
  the Z-function of `p ++ t`, equal to the KMP output with at most `2(|p| + |t|) - 3` comparisons.
  Remaining: a general proof that `a ^ (n - 1) b` attains `2n - 3` (checked for small `n`); the
  linear conversions between Z-values and the KMP prefix function; applications such as
  Main–Lorentz repetition finding; and moving the common-prefix extension `extendM`, now shared
  by Kasai and the Z-algorithm, from `SuffixArray/Kasai` to a small shared string module.
- **Multi-pattern matching** ([#3358](https://github.com/cslib-community/complexitylib/issues/3358)):
  Aho–Corasick with states represented by their strings, valid failure and output tables from
  the level-order construction, exact reporting of all occurrences, the scan bound of the
  paper's Theorem 2 and the transitions counted in its Theorem 4 is in
  `Algorithms/Lean/AhoCorasick`. Remaining: an explicit integer-state trie with a charged goto
  table and its linear construction (Algorithm 2, Theorem 3), linear charged level/queue
  bookkeeping in the failure construction (currently an uncharged scan of all keywords per
  depth), a construction that charges each shared trie state once, the deterministic automaton
  of Section 6, and machine-level or RAM realizations.
- **Edit distance and longest common subsequence**
  ([#3472](https://github.com/cslib-community/complexitylib/issues/3472)):
  `Algorithms/Lean/EditDistance` has the Wagner–Fischer table under arbitrary letter costs. It is
  the least cost of an edit script (alignment, trace), with an optimal script by traceback. It
  also has the LCS table, the greatest length of a common subsequence, with a witness. The two
  are related by `editDist indel + 2 · lcsLength = |x| + |y|`, and `editDist indel` is the
  insertion–deletion distance. Both cost exactly `(|x| + 1)(|y| + 1)` in `TimeM`. Remaining: for
  unit costs, the metric axioms and the equivalence with the least number of single-letter edits
  at arbitrary positions (and, for general costs, Wagner–Fischer's equivalence of traces with edit
  sequences under their cost conditions); Hirschberg's linear-space recovery of an optimal
  alignment with `O(|x| |y|)` cost (Kleinberg–Tardos §6.7); a machine-level polynomial-time
  computation; Ukkonen's and Myers' `O((|x| + |y|) d)` algorithms for distance `d`; the
  Masek–Paterson four-Russians speedup; and `OV` hardness
  ([#3037](https://github.com/cslib-community/complexitylib/issues/3037)).

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
  kept separate; and develop general open-program composition. Emitted PRG prefixes now have
  exact length, prefix consistency, a full-input native certificate and security at every native
  polynomial output schedule ([#2784](https://github.com/cslib-community/complexitylib/issues/2784)).
  The adaptive arbitrary-word cipher and hash-then-MAC/EtM construction remains open
  ([#2749](https://github.com/cslib-community/complexitylib/issues/2749)). Use Cook–Levin and GGM as
  regression clients. Improve configuration views, tape partitions and handoff identities only
  where several clients benefit, keeping machine transitions out of global simp.
- **Mathlib TM2:** sublinear work-space comparisons and a linear-space forward simulation.
- **Single-tape lower bounds**
  ([#2884](https://github.com/cslib-community/complexitylib/issues/2884)): crossing sequences,
  translation invariance, cut-and-paste across boundaries at different positions (with the
  crossing sequences on the kept sides), the quadratic palindrome lower bound for cslib
  `SingleTapeTM` deciders that answer under the head, the fact that bounded crossing sequences
  at the input boundaries force `Language.IsRegular`, and the gap theorem that single-tape
  deciders running in time `o(n log n)` accept only regular languages
  ([#2965](https://github.com/cslib-community/complexitylib/issues/2965)) are proved.
  Remaining: an explicit single-tape palindrome decider in time `O(n²)`, which shows the bound is
  tight and gives a positive instance of `DecidesPalindromesInTime`; a linear-time multi-tape
  palindrome decider, which gives the one-tape/two-tape time separation; and the nondeterministic
  analogue of the gap theorem under the accept measure.
- **Generic RAM:** uniform arbitrary-program dispatch and general width-selection and input-fit
  theorems; simulating operations by programs over smaller bases; structured programs and time
  classes over arbitrary value domains with weighted or bit costs; simulations between instances;
  the typed core proposed in [CSLib #1158](https://github.com/leanprover/cslib/pull/1158).
- **Word RAM:** an AC⁰ basis; wider-fragment and Turing-machine simulations;
  transfer of Anthropic's modular machine and APSP algorithms (3SUM is native:
  `uniformDecidableInO_one9992`); size-based width selection
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
- **Perfect hashing** ([#3276](https://github.com/cslib-community/complexitylib/issues/3276)):
  the static FKS two-level table, following the CLRS universal-family account, is proved over
  typed cells with an abstract cost model of seed draws and hash evaluations
  (`DataStructure/Dictionary/PerfectHashing`). It gives 3-probe lookups (hash evaluation
  uncharged), at most `5n + 2` cells (`O(n)` words only for `O(1)`-word seeds),
  a fuel-truncated construction with geometric failure, and expected `O(n)` draws and
  evaluations. Remaining:
  - a word-RAM realization with `w`-bit seeds and headers, charged bucketing and layout, an
    unbounded Las Vegas form, and a bridge to `w`-bit cell probes;
  - FKS's `k x mod p mod s` family, its `n + o(n)` refinement, and the deterministic
    construction;
  - dynamic perfect hashing (Dietzfelbinger et al.);
  - the Fredman–Komlós lower bound on the description size of perfect hash families.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** work–span semantics for a parallel language or PRAM model whose
  computation DAGs feed the unit-time DAG scheduling bounds (work and span laws, greedy bound and
  Brent's lemma are in `Algorithms/Lean/Scheduling/Brent.lean`), followed by prefix scan, sorting
  and graph primitives with both work and span bounds. State processor access, synchronization and
  scheduling overhead explicitly, including work stealing (Blumofe–Leiserson).
- **Memory hierarchies:** external-memory and ideal-cache models with explicit capacity and
  block-size parameters; scanning, B-tree operations, blocked matrix multiplication and
  cache-oblivious sorting as clients. Connect arithmetic-step, memory-access and cache-miss
  bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity:** LOCAL and CONGEST models with explicit identifiers, round,
  message-size and randomness conventions; locality lower bounds and communication-to-round
  reductions with corresponding algorithmic examples. The deterministic LOCAL model on oriented
  cycles, Cole–Vishkin and Linial's `log*` bound, the bridge to Mathlib's `cycleGraph` colourings
  and the `Θ(log* n)` bounds for maximal independent sets on cycles exist
  (`Complexity/Computability/Distributed/OrientedCycle/`). For LCL problems without inputs on
  directed cycles (Chang–Studený–Suomela, Table 1), the full `O(1)`/`Θ(log* n)`/`Θ(n)`
  classification exists (`OrientedCycle/LCL/`,
  [#3009](https://github.com/cslib-community/complexitylib/issues/3009)). Open: a tight
  `½ log* n + O_|L|(1)` upper bound for flexible problems, LCLs with inputs, on paths (directed
  or undirected) and on undirected cycles, general graphs with port numbering, Linial's `O(Δ²)` colouring and
  `(Δ + 1)`-colouring/MIS on bounded-degree graphs, CONGEST message bounds, randomized LOCAL
  algorithms, and closing the additive gaps between the
  `⌈(log* n) / 2⌉ + 3` and `(log* n) / 2 - 1` round bounds for 3-colouring cycles and between
  `⌈(log* n) / 2⌉ + 5` and `(log* n) / 2 - 2` for MIS on cycles. A centralized simulation of the
  random-priority variant of Luby's MIS algorithm exists (`Algorithms/Lean/LubyMIS.lean`,
  [#3270](https://github.com/cslib-community/complexitylib/issues/3270)): Las Vegas correctness,
  the half-edge removal lemma and an `O(log n)` phase bound with failure `n^-c` via Markov. Open
  there: a LOCAL message-passing formalization with `O(log n)` rounds, the expected phase count,
  Luby's original marking algorithm with its pairwise-independent analysis and NC
  derandomization, Ghaffari's `O(log Δ) + poly(log log n)` bound, and the
  Kuhn–Moscibroda–Wattenhofer lower bounds.
- **Fault-tolerant agreement:** synchronous Byzantine agreement on the complete graph, the
  `n ≤ 3t` impossibility and the single-fault protocol exist
  (`Complexity/Computability/Distributed/Byzantine/`,
  [#3261](https://github.com/cslib-community/complexitylib/issues/3261)). Open: the connectivity
  bound `κ ≥ 2t + 1` on general graphs (Fischer–Lynch–Merritt §3.2), the upper bound for all
  `n > 3t` (`OM(t)` or exponential information gathering), the `t + 1` round lower bound
  (Fischer–Lynch), authenticated (signed-message) agreement for any `n > t`, weak agreement,
  the Byzantine firing squad (Fischer–Lynch–Merritt §5), approximate agreement and clock
  synchronization bounds, and randomized agreement.

## Coverage and reuse

The long-term bar is to support formalizing every paper in the
[Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/),
with the additional work per paper increasingly its new mathematics: standard models,
representation changes, reductions, resource certificates and proof techniques come from the
library. Use a growing, source-pinned sample of papers, including some chosen after an API was
designed, as demanding clients, and promote recurring obligations into shared APIs only after
reuse is demonstrated.

- **Measure postprocessing.** Canonical full-L1 total variation contracts under measurable
  maps of arbitrary finite measures, including unequal masses
  ([#2732](https://github.com/cslib-community/complexitylib/issues/2732)). The actual Gaussian
  projection/mod-one consumer is proved in
  [#2734](https://github.com/cslib-community/complexitylib/issues/2734).
- **Finite weighted measure mixtures.** `Foundations/MeasureTheory/Measure/TotalVariation/Mixture`
  bounds the existing full-L1 distance when both finite component measures and their nonnegative
  weights change. It keeps the comparison components' total masses explicit, so neither
  probability normalization nor equal masses are required. The tagged finite-PMF client supplies
  the error-composition step for [#2767](https://github.com/cslib-community/complexitylib/issues/2767);
  identifying and bounding the actual Regev conditional laws remains that separate consumer.

- **Gaussian density and projection laws (available):** the positive-width normalized
  Gaussian weight is proved equal to a scaled standard Gaussian, and its actual scalar
  projection has variance `(s ‖z‖)² / (2π)`, including the zero vector and dimension zero
  (#2733). The discrete-coset convolution projection and mod-one bound are proved in #2734;
  efficient sampling and the quantum reduction remain #1213.
- **One sensitivity API.** Define the sensitivity measures over any `Fintype` in CSLib and drop
  the separate measures of the sensitivity-separation development.
- **CNF evaluation certificates:** `fun_prop` certificates for evaluating literals, clauses and
  formulas under a polynomial-time assignment, so clients stop passing `CNF.eval`,
  `Clause.eval` and `Literal.eval` to `fun_prop` as unfolding hints.
- Factor indicator-expectation identities from PCP's second-moment calculation, and recurring
  cardinality and logarithm conversions, once a second client benefits.
- **Divide-and-conquer recurrences**
  ([#3042](https://github.com/cslib-community/complexitylib/issues/3042)): the master theorem
  for inequality recurrences over `ℕ`, with explicit constants for all three polynomial cases and
  `IsBigO` forms, is in `Foundations/Data/Nat/MasterTheorem`. Open: matching lower bounds
  (`Θ`) for equality recurrences; case 3 under the general regularity condition; and moving
  hand-solved recurrences onto it where the generic constant suffices (for example recurrences
  currently solved by a direct induction on the recursion level). cslib's merge-sort bound
  `n ⌈log₂ n⌉` is sharper, and the halving lemma's subtracted-term form is needed by
  `addCount_add_le_pow_clog`; the halving lemma stays as the sharp tool for `b = 2`.

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
  bound `2^{O_k(n log log n / √log n)}` still needs the Lemma D.2 construction and its native
  application to this interface; #1538 remains open.
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

- General auxiliary-input zero knowledge ([#324]); the GMW protocol's auxiliary-input results and
  their limits are in [`GMW/Simulator.lean`](Complexity/Crypto/Computational/GMW/Simulator.lean).
- Vollmer's generalized-quantifier survey ([#399]): ordered leaf words, explicit uniformity and
  input-access models, finite-monoid classification and generalized logical quantifiers.

[archive]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md
[archive-fhe]: https://github.com/cslib-community/complexitylib/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities
[#321]: https://github.com/cslib-community/complexitylib/issues/321
[#324]: https://github.com/cslib-community/complexitylib/issues/324
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
[#2019]: https://github.com/cslib-community/complexitylib/issues/2019
[#2062]: https://github.com/cslib-community/complexitylib/issues/2062
[#2063]: https://github.com/cslib-community/complexitylib/issues/2063
[#2205]: https://github.com/cslib-community/complexitylib/issues/2205
[#2213]: https://github.com/cslib-community/complexitylib/issues/2213
[#2289]: https://github.com/cslib-community/complexitylib/issues/2289
[#2145]: https://github.com/cslib-community/complexitylib/issues/2145
[#2084]: https://github.com/cslib-community/complexitylib/issues/2084
[#2290]: https://github.com/cslib-community/complexitylib/issues/2290
[#2347]: https://github.com/cslib-community/complexitylib/issues/2347
[#2423]: https://github.com/cslib-community/complexitylib/issues/2423

[#2521]: https://github.com/cslib-community/complexitylib/issues/2521

[#2527]: https://github.com/cslib-community/complexitylib/issues/2527

[#2568]: https://github.com/cslib-community/complexitylib/issues/2568

[#2579]: https://github.com/cslib-community/complexitylib/issues/2579
[#2585]: https://github.com/cslib-community/complexitylib/issues/2585

[#2620]: https://github.com/cslib-community/complexitylib/issues/2620
[#2636]: https://github.com/cslib-community/complexitylib/issues/2636
[#2642]: https://github.com/cslib-community/complexitylib/issues/2642
[#2652]: https://github.com/cslib-community/complexitylib/issues/2652

[#2661]: https://github.com/cslib-community/complexitylib/issues/2661
[#2812]: https://github.com/cslib-community/complexitylib/issues/2812
[#2855]: https://github.com/cslib-community/complexitylib/issues/2855
[#2866]: https://github.com/cslib-community/complexitylib/issues/2866
