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

- **Boolean Schaefer dichotomy** ([#2822](https://github.com/cslib-community/complexitylib/issues/2822)):
  the stack proves native polynomial-time tractability for all six common-polymorphism cases
  and native NP-completeness outside them, for each fixed finite Boolean constraint language
  of arbitrary fixed arities. `CSPSAT.schaefer_dichotomy` assembles the actual solvers, fixed
  compilers, clone classification and gadgets under binary labels and exact-arity rejection,
  including empty/nullary relations. The hard branch has a native 3SAT reduction with
  `output.numVars + output.length ≤ C * input.length`, for a language-dependent constant.
  Symmetric and larger-domain dichotomies are outside the current scope.

- Time, space and exponential hierarchies; oracle, advice, unambiguous and promise classes;
  completeness, padding, self-reducibility, relativization and oracle separations, preserving
  each reduction's resource bound.
- **Abstract (Blum) complexity** ([#2866]): Blum complexity measures over Mathlib's
  `Nat.Partrec.Code`, with the `evaln` fuel instance, Borodin's gap theorem for the
  almost-everywhere classes and recursive relatedness, are in `Computability/BlumComplexity`.
  Remaining: Blum's speedup theorem, the McCreight–Meyer union theorem, the compression theorem
  and honesty, and Blum measures for native multitape time and space through a Gödel-numbering
  bridge from native descriptions.
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
  of `USTCON ∈ RL` (membership already follows from `L_subset_RL` and `USTCON_mem_L`), Nisan's
  generator, `BPL ⊆ L²` and Saks–Zhou. The preprint route to native `RL = L` remains open in
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
- **Uniform diagonalization** (Schöning), which generalizes Ladner's theorem.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE,
  self-reducible P-selective sets lie in P, and P-selective sets are not `≤ₜₜᵖ`-hard for NP unless
  P = NP.
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
  `a / b ≥ 1 - qbar k h`); Schöning has a curated abstract. Optional remainder: PPZ and PPSZ
  abstracts, and the uniform `o(n)` forms of the PPSZ bounds with `w` growing in `n`.
  Further fine-grained reductions and consequences of ETH, SETH and other named hypotheses.

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#886]): for `0 < ε < 1/8`, NP-hardness of
  distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most
  `7/8 + ε` of the clauses. Holenstein's parallel repetition theorem for two-prover games is
  proved (`TwoProverGame.value_pow_le`). What remains is small-soundness Label Cover through
  parallel repetition and Håstad's separate perfect-completeness construction for MAX-E3SAT.
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
  NEXP. `SymAnd/Collapse.lean` collapses towers of prime-modulus polynomial layers into `SYM ∘ AND`
  (Beigel–Tarui, Lemma 2.8). Still open: compiling `AC0Mod` circuits into such towers (composite
  moduli through prime-power digits, AND/OR through small-bias tests), the quasi-polynomial-time
  construction, Williams's fast `SYM ∘ AND` evaluation and ACC-SAT algorithm, a fine
  nondeterministic time hierarchy, and the `E^NP` and NEXP lower bounds.
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
  VNP-hardness remain open); formula and branching-program models,
  identity testing, hitting sets, and tensor and rank methods, including partial-derivative
  measures (the order-`k` measure and bounded-product-fan-in depth-three determinant and permanent
  lower bounds, covering homogeneous depth-three circuits, are proved in
  [`Arithmetic/DepthThree`](Complexity/Computability/Circuit/Arithmetic/DepthThree.lean);
  Nisan–Wigderson's all-orders measure, their elementary symmetric polynomial and iterated matrix
  multiplication bounds, and shifted partial derivatives remain open) and the depth-reduction chasms at
  depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform
  construction costs certified
  separately from gate counts.
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

- **Quantum query separations** ([#2918]): beyond the decision version of Simon's problem, prove
  the search version (sample rows orthogonal to `s` and recover `s` by Gaussian elimination over
  `ZMod 2` with constant probability), the classical `n`-query lower bound for
  Bernstein–Vazirani, and separations in the value-query model. The latter needs quantum states
  over an arbitrary finite query index type rather than `Fin N`; generalizing `State N W` affects
  `Quantum/Search.lean`, `Quantum/Composition.lean`, `Quantum/Grover.lean`,
  `Quantum/UnknownSearch.lean`, `Quantum/Polynomial.lean` and `Quantum/Adversary.lean`. Natural
  later targets are Forrelation and other optimal quantum–classical query separations.

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

- **Flows and matching:** a native augmenting-path algorithm with charged runtime (integral
  max-flow/min-cut and a `TimeM` Edmonds–Karp solver are in `Algorithms/Lean/MaxFlow`); then
  minimum-cost flow and weighted bipartite matching through common residual-network and duality
  machinery.
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
  kept separate; and develop general open-program composition. Emitted PRG prefixes now have
  exact length, prefix consistency, a full-input native certificate and security at every native
  polynomial output schedule ([#2784](https://github.com/cslib-community/complexitylib/issues/2784)).
  The adaptive arbitrary-word cipher and hash-then-MAC/EtM construction remains open
  ([#2749](https://github.com/cslib-community/complexitylib/issues/2749)). Use Cook–Levin and GGM as
  regression clients. Improve configuration views, tape partitions and handoff identities only
  where several clients benefit, keeping machine transitions out of global simp.
- **Mathlib TM2:** sublinear work-space comparisons and a linear-space forward simulation.
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
[#2918]: https://github.com/cslib-community/complexitylib/issues/2918
