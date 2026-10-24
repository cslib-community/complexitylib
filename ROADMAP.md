# Development roadmap

Outstanding work and the rationale needed to guide it. See the [README](README.md) for
completed reference developments.

## Deferred issue scopes

The following broad projects remain mathematical coverage targets, but are deferred from the
active implementation queue. Their issues were closed as not planned, not as proved results;
existing developments, source credit and saved branches remain available for a future bounded task.

* [Valiant permanent completeness (#321)](https://github.com/cslib-community/complexitylib/issues/321):
  the full VNP-completeness reduction remains open.
* [General auxiliary-input zero knowledge (#324)](https://github.com/cslib-community/complexitylib/issues/324):
  the uniform polynomial-time-family milestone is proved; the stronger endpoint below remains open.
* [Williams's square-root-space simulation (#361)](https://github.com/cslib-community/complexitylib/issues/361)
  and [implicit Tree Evaluation (#367)](https://github.com/cslib-community/complexitylib/issues/367):
  existing algebraic and query-machine results remain proved, while the implicit evaluator and
  full simulation are deferred.
* [Vollmer's generalized-quantifier survey (#399)](https://github.com/cslib-community/complexitylib/issues/399):
  source and dependency mapping is available, but the paper has not been formalized as a whole.
  Faithful treatment requires ordered leaf words, explicit uniformity and input-access models,
  finite-monoid classification and generalized logical quantifiers.

## Highest priorities

1. **Goldreich–Micali–Wigderson zero knowledge.** If one-way functions exist, every language in NP
   has an interactive computational zero-knowledge proof system, secure against probabilistic
   polynomial-time verifiers with auxiliary input.
   - *Partial:* [Commitment](Complexity/Crypto/Computational/Commitment.lean) proves Naor's
     two-message bit commitment scheme (`naorCommit`, `naorBitCommitment`,
     `OneWay.exists_bitCommitmentScheme`) with statistical binding and computational hiding against
     randomized stateful PPT receivers (`CommitmentReceiver`, `commitmentHidingGame`,
     `StatefulHiding`, `PseudorandomGenerator.naorStatefulHiding`, with
     `StatefulHiding.computational_hiding` bridging to deterministic polynomial-time receiver-string
     and bit families), and
     [ZeroKnowledge](Complexity/Crypto/Computational/ZeroKnowledge.lean)
     ([GMW/Protocol](Complexity/Crypto/Computational/GMW/Protocol.lean),
     [GMW/Soundness](Complexity/Crypto/Computational/GMW/Soundness.lean),
     [GMW/PolyTime](Complexity/Crypto/Computational/GMW/PolyTime.lean),
     [GMW/Simulator](Complexity/Crypto/Computational/GMW/Simulator.lean)) proves a two-round
     3-copy masked-3SAT truth-table commitment zero-knowledge proof system for `ThreeSAT` and every
     `A ∈ NP` (`ZeroKnowledgeProof`, `zeroKnowledgeProofThreeSAT`,
     `OneWay.exists_zeroKnowledgeProof_of_mem_NP`) from any uniform one-way function via HILL and
     Cook–Levin, with uniform zero knowledge (`GenerableZeroKnowledge`,
     `ZeroKnowledgeProof.generableZeroKnowledge`) over deterministic polynomial-time-generable
     instance/witness/auxiliary-input families `(x n, w n, z n)` (and fixed-instance security via
     `zero_knowledge_const`) at soundness error `1 / 3` (the proof bounds it by `1 / 8 + 2^{-(n+8)}`). Because the
     auxiliary input is a deterministic polynomial-time function of `1^n`, this does not reach the
     general auxiliary-input statement above.
   - *Pointwise reduction and auxiliary-input interface milestones (#427, #698):*
     `GMW.gmwView_advantage_le` bounds every valid instance/witness/auxiliary tuple by
     `(7/8)^(n+1)` plus `dyadicSize(n+1) * dyadicSize(totalLen(f a))` times one concrete
     PRG-challenge advantage at seed size `n+7`. The final test receives `(n,a,z,view)`;
     `isPPTOn_gmwViewReduction` charges the complete encoded tuple and challenge, including
     adaptive queries and retained verifier randomness/state. `AuxiliaryInputZeroKnowledge`
     (`ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`) states the general auxiliary-input notion
     for arbitrary polynomially bounded valid families against full-input uniform strict PPT
     distinguishers, with the stronger-to-restricted bridge
     `AuxiliaryInputZeroKnowledge.generableZeroKnowledge`. Under the explicit advice-PRG premise
     `GMW.AdvicePRG` (`gmwView_negligible_of_advice_prg`), the GMW proof systems satisfy
     `ZeroKnowledgeProof.AuxiliaryInputZeroKnowledge`
     (`PseudorandomGenerator.auxiliaryInputZeroKnowledge_zeroKnowledgeProofOfReduction`,
     `PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_mem_NP`).
     No implication from current uniform one-wayness/HILL to `GMW.AdvicePRG` is proved. The direct
     pad-replacement proof does not require the separate Naor commitment-hiding theorem.
   - *Open (this priority):* zero knowledge in Goldreich's sense (Def. 4.3.10), for every
     `x ∈ L` with arbitrary auxiliary input `z` against probabilistic polynomial-time verifiers;
     witness-level Levin reductions; and sequential soundness amplification to negligible error.
     The full auxiliary-input convention still needs a formal security-premise/clock bridge:
     polynomial time in total encoded input, used in #427, differs from a clock independent
     of an unbounded auxiliary word. The pointwise milestone does not complete this objective.
2. **Rompel’s signature theorem.** One-way functions exist if and only if digital signature schemes
   exist that are existentially unforgeable under adaptive chosen-message attacks by probabilistic
   polynomial-time adversaries.
   - *Partial:* [Signature](Complexity/Crypto/Computational/Signature.lean) defines uniform strict
     PPT signature schemes for exactly `n`-bit messages at security parameter `n`, adaptive EUF-CMA
     and one-time EUF-CMA, and proves full security implies one-time security.
     [OneWayToSignature](Complexity/Crypto/Computational/OneWayToSignature.lean) proves secure
     signatures imply one-way functions and constructs Lamport one-time signatures from any
     one-way function, giving `exists_oneWay_iff_exists_oneTimeSignature`.
   - *Open:* the many-time sufficiency direction from arbitrary one-way functions, including
     universal one-way hash functions and authentication trees. The one-time equivalence does not
     establish Rompel's full theorem or security for arbitrary polynomial-length messages.
3. **Gentry’s bootstrapping theorem.** A semantically secure, bootstrappable encryption scheme
   yields compact leveled fully homomorphic encryption for every polynomially bounded circuit
   depth. Here bootstrappability requires homomorphic evaluation of suitably augmented decryption
   circuits. With an appropriate additional circular-security assumption, the construction yields a
   fixed-key fully homomorphic scheme without a predetermined depth bound.
   *Recovery milestones:* [refresh](Complexity/Crypto/Computational/Homomorphic/Refresh.lean)
   constructs identity and NAND refresh from actual decryption circuits and proves correctness
   for arbitrary well-sized old ciphertexts, including prior evaluation outputs, with fixed
   output width. [Efficiency](Complexity/Crypto/Computational/Homomorphic/Efficiency.lean)
   derives strict PPT refresh from base encryption/evaluation certificates and a uniform
   decryption-circuit generator; construction of the NAND augmentation is also certified.
   [KeyChain](Complexity/Crypto/Computational/Homomorphic/KeyChain.lean) constructs the actual
   sampler with `L + 1` independent key pairs and `L` adjacent encrypted links, with exact support
   and native PPT certificates. The [layered evaluator](Complexity/Crypto/Computational/Homomorphic/Layered.lean)
   uses only public keys and encrypted links. Its
   [correctness theorem](Complexity/Crypto/Computational/Homomorphic/Layered/Correctness.lean)
   covers every well-formed consecutive-layer program and every supported key chain and output,
   preserving exact wire counts and ciphertext widths through one key transition per layer.
   Its [PPT certificate](Complexity/Crypto/Computational/Homomorphic/Layered/PolyTime.lean)
   charges the complete public encoding, including binary wire indices, and bounds execution
   even on malformed keys, links and references.
   The [circuit compiler](Complexity/Computability/Circuit/Boolean/Layered/Compile.lean)
   turns a shared De Morgan circuit with `s` gates, `n` inputs and designated-output depth `d`
   into exactly `2d` layers, each of width `n + 3s`, followed by ordered output wiring.
   [Correctness](Complexity/Computability/Circuit/Boolean/Layered/Compile/Correctness.lean)
   preserves its semantics, including unused gates, repeated outputs and depth-zero wiring;
   [size bounds](Complexity/Computability/Circuit/Boolean/Layered/Compile/Size.lean) charge
   every binary reference and encoding delimiter. Its
   [native certificate](Complexity/Computability/Circuit/Boolean/Layered/Compile/PolyTime.lean)
   computes the depth table and schedule uniformly across arities, including malformed raw codes.
   [Ordinary encrypted evaluation](Complexity/Crypto/Computational/Homomorphic/Evaluation.lean)
   composes the compiler and layered evaluator along a generated chain of `2d + 1` keys, retaining
   exact ciphertext width. Its
   [PPT certificate](Complexity/Crypto/Computational/Homomorphic/Evaluation/PolyTime.lean)
   covers the complete public input without correctness or validity assumptions.
   The [depth-budgeted scheme](Complexity/Crypto/Computational/Homomorphic/Leveled/Basic.lean)
   generates `2B + 1` base keys for budget `B`. It uses
   [identity-layer padding](Complexity/Computability/Circuit/Boolean/Layered/Padding.lean) so every
   circuit of designated-output depth at most `B` finishes under the same final key. Its public
   artifact contains public keys and adjacent encrypted links; its private artifact retains the
   initial and final secrets. A tag distinguishes fresh from evaluated ciphertexts, adapting the
   two endpoints to the existing `Scheme.Correct` interface. There is no circular encrypted link.
   [Correctness](Complexity/Crypto/Computational/Homomorphic/Leveled/Correctness.lean) proves this
   interface for the actual algorithms on fresh inputs. Exact secret-key and ciphertext lengths
   are `3 * secretWidth n + 1` and `ciphertextWidth n + 1`, independent of `B`. This does not
   promise that evaluated wrapper ciphertexts can be reused as fresh inputs to another call.
   [Native certificates](Complexity/Crypto/Computational/Homomorphic/Leveled/PolyTime.lean)
   cover serialization, total decoding, compilation, padding and tagged decryption on all inputs,
   uniformly in unary `(n, B)`. They yield efficient schemes for efficiently computed unary budget
   families. The decryption-circuit generator also supplies polynomial bounds on both derived
   widths; decryption itself has no budget parameter.
   [Compactness](Complexity/Crypto/Computational/Homomorphic/Leveled/Compactness.lean) gives one
   polynomial-size circuit family and common polynomial time and space bounds in the security
   parameter for the complete tagged decryption algorithm, including endpoint decoding and tag
   selection. The circuit family and resource bounds are independent of every budget and requested
   depth family and cover all inputs of the prescribed widths, including malformed secrets. The
   circuit result proves nonuniform existence; it does not provide a generator for these wrapper
   circuits.
   [Refresh tests](ComplexityTests/Crypto/HomomorphicRefresh.lean),
   [layered tests](ComplexityTests/Crypto/HomomorphicLayered.lean), and
   [ordinary-circuit tests](ComplexityTests/Crypto/HomomorphicEvaluation.lean) instantiate the
   construction and runtime hypotheses in an explicitly insecure scheme whose base evaluator
   rejects evaluated inputs. They exercise key switching, repeated refresh, shared wires, constants,
   empty layers and zero depth. [Compiler tests](ComplexityTests/CircuitLayering.lean) also cover
   dead gates, empty outputs, shared OR gates, skipped depths, and malformed binary references.
   [Leveled tests](ComplexityTests/Crypto/HomomorphicLeveled.lean) check budgets zero, one and two,
   distinct initial/final secrets at positive budgets, and circuits of different actual depths
   under the same endpoint, malformed inputs and nonconstant efficient budget families.
   The [IND-CPA reduction](Complexity/Crypto/Computational/Homomorphic/Leveled/Security.lean)
   proves security of the actual serialized leveled scheme against uniform native two-stage
   adversaries. It assumes base IND-CPA security, native key generation and encryption, fixed
   supported secret length, and an efficient unary budget. The adversary chooses its messages
   after seeing the entire public artifact and retains its exact saved state. The
   [key-chain reduction](Complexity/Crypto/Computational/Homomorphic/KeyChain/Security.lean)
   erases links in reverse order with uniform link/bit sampling and an executable polynomial
   cap derived from native key generation; no circular-security or efficient-width premise is
   used. The [combined theorems](Complexity/Crypto/Computational/Homomorphic/Leveled/Bootstrapping.lean)
   give correctness, exact polynomial widths independent of the budget, and IND-CPA for the
   same constructed scheme. `Leveled.exists_scheme_of_polynomiallyBounded` covers every
   `PolynomiallyBounded` requested depth family by selecting a computable unary budget
   `c * (n + 1)^d` that dominates it at every parameter, including its finite prefix. The requested
   family need not be computable: the algorithms execute the majorant. The theorem supplies native
   certificates for all four algorithms and permits every circuit within the requested depth.
   [Endpoint tests](ComplexityTests/Crypto/Bootstrapping.lean) cover arbitrary predicate-dependent
   depth families, large finite-prefix spikes, and the full tagged decoder's compactness, while
   retaining the security assumptions explicitly.
   [Key-chain tests](ComplexityTests/Crypto/KeyChainSecurity.lean) and
   [leveled security tests](ComplexityTests/Crypto/LeveledSecurity.lean) exercise repeated random
   keys, retained encryption randomness, adaptive saved state, empty secrets, zero links and padding.
   This is a qualitative single-challenge security transfer, not Gentry's exact
   concrete-security bound.
   The [fixed-key construction](Complexity/Crypto/Computational/Homomorphic/FixedKey/Basic.lean)
   samples one base key and encrypts its secret bits under that same public key. Key generation
   has no circuit or depth parameter; the public artifact is reused at every compiled layer.
   [Correctness](Complexity/Crypto/Computational/Homomorphic/FixedKey/Correctness.lean) covers
   all finite Boolean circuits and arbitrary well-sized decrypting inputs, including prior
   evaluation outputs. Secret and ciphertext widths are exactly the original base widths.
   [Native certificates](Complexity/Crypto/Computational/Homomorphic/FixedKey/PolyTime.lean)
   cover all four actual algorithms and the complete encoded circuit and input data, including
   malformed artifacts. The uniform decryption-circuit generator bounds both widths and the
   unchanged decryption-circuit size polynomially in the security parameter.
   [Security](Complexity/Crypto/Computational/Homomorphic/FixedKey/Security.lean) assumes base
   IND-CPA and the explicit [one-key circular experiment](Complexity/Crypto/Computational/Encryption/Circular.lean):
   the public key and complete vector of secret-bit encryptions must be jointly indistinguishable
   from the corresponding zero encryptions. This fixed-query assumption does not assert general
   adaptive KDM security. The [combined theorem](Complexity/Crypto/Computational/Homomorphic/FixedKey/Bootstrapping.lean)
   proves correctness, compactness, native efficiency and IND-CPA for the same fixed-key scheme.
   [Construction tests](ComplexityTests/Crypto/HomomorphicFixedKey.lean) check repeated evaluation
   under one key, even though the explicitly insecure base fixture rejects evaluated inputs.
   [Security tests](ComplexityTests/Crypto/FixedKeySecurity.lean) reject joint leakage hidden by
   identical ciphertext marginals and keep a security-only fixture's failed correctness explicit.
   Together these establish the generic qualitative conditional bootstrapping theorem tracked in
   [#322](https://github.com/cslib-community/complexitylib/issues/322). A concrete LWE-based
   cryptosystem satisfying its correctness, security, bootstrappability and native efficiency
   hypotheses remains open in [#486](https://github.com/cslib-community/complexitylib/issues/486).
   The insecure construction fixtures and security-only fixtures do not supply that joint
   instantiation. The reductions do not claim Gentry's exact concrete-security loss.
   The [deterministic GSW core](Complexity/Crypto/Computational/Homomorphic/GSW/Basic.lean)
   constructs the public matrix, encryption with explicit binary coins, NAND and decryption for
   modulus `q = 2^w` and Boolean ciphertext matrices of dimension `N = (n + 1) * w`.
   It proves the exact integer error equations and correctness under the strict margin
   `4 * |error| < q`. The [noise bounds](Complexity/Crypto/Computational/Homomorphic/GSW/Noise.lean)
   are `m * β` for fresh encryption and `B₁ + N * B₂` for NAND.
   [Tests](ComplexityTests/Crypto/GSW.lean) exercise both messages and all NAND inputs with nonzero
   noise, including negative wraparound and decoder boundaries. This is the power-of-two
   specialization of Gentry--Sahai--Waters (2013), omitting its redundant top digit.
   The [finite samplers](Complexity/Crypto/Computational/Homomorphic/GSW/Sampling.lean)
   instantiate actual key generation and encryption with uniform power-of-two residues,
   independent binary coins and errors given by the difference of two independent `η`-bit counts.
   Every supported error lies in `[-η, η]`. Fresh encryption and NAND of two fresh ciphertexts
   are correct under the respective strict margins
   `4*m*η < 2^w` and `4*(1+N)*m*η < 2^w`, respectively, with `w > 0`.
   A [flat-tape identity](Complexity/Crypto/Computational/Homomorphic/GSW/Sampling/Randomness.lean)
   preserves the full joint public-key, secret-key and ciphertext law using
   `n*w + m*n*w + 2*m*η + N*m` fair bits.
   [Serialized random-input samplers](Complexity/Crypto/Computational/Homomorphic/GSW/Sampling/Serialized.lean)
   have uniform native PPT certificates and exact typed-distribution bridges, with unary
   dimensions, binary residues and signed binary errors.
   [Sampling tests](ComplexityTests/Crypto/GSWSampling.lean) include nonzero signed errors,
   actual generated keys, both messages, NAND, empty dimensions and growing native inputs.
   These results do not identify the finite noise with a Gaussian or assert its hardness.
   The [complete serialized algorithms](Complexity/Crypto/Computational/Homomorphic/GSW/Serialized.lean)
   compute actual public keys and ciphertexts using binary modular arithmetic and explicit unary
   dimensions. Their [native certificates](Complexity/Crypto/Computational/Homomorphic/GSW/Serialized/PolyTime.lean)
   establish strict PPT for key generation and encryption on arbitrary encoded inputs.
   [Exact bridges](Complexity/Crypto/Computational/Homomorphic/GSW/Serialized/Correctness.lean)
   preserve the typed joint key law and encryption law, with public/secret word lengths
   `m*(n+1)*w` and `n*w`, and all `N^2` ciphertext bits.
   [Runtime tests](ComplexityTests/Crypto/GSWNative.lean) cover signed wraparound, ragged and
   truncated inputs, zero dimensions, bit order and growing-parameter clients.
   [Serialized decryption and NAND](Complexity/Crypto/Computational/Homomorphic/GSW/Serialized/Evaluation.lean)
   agree with the typed operations on every raw word, padding missing bits with zero and ignoring
   excess bits. NAND retains modular integer counts and produces exactly `N^2` bits. Their
   [native certificates](Complexity/Crypto/Computational/Homomorphic/GSW/Serialized/Evaluation/PolyTime.lean)
   charge the full inputs and output with uniformly varying unary dimensions and binary arithmetic.
   Correctness transports the existing strict noise margins, including every supported actual
   key and encryption draw. [Regressions](ComplexityTests/Crypto/GSWEvaluation.lean) check small
   widths, negative wraparound, asymmetric NAND products, positive noise and a native client
   composing key generation, encryption, NAND and decryption.
   The [statistical hiding theorem](Complexity/Crypto/Computational/Homomorphic/GSW/Hiding.lean)
   proves the uniform-public-matrix step of their security argument. For `d = n + 1` and
   `N = d * w`, the actual ciphertext gives any randomized two-stage adversary acceptance
   probabilities differing by at most `N * sqrt(2^(w*d) / 2^m)`. The adversary sees the public
   matrix before choosing its messages and retains arbitrary state. The underlying
   [shared-matrix bound](Complexity/Probability/BitString/SubsetSum/Matrix.lean) works for every
   positive modulus, with loss linear in the number of independently sampled binary rows;
   it neither assumes whole-matrix two-universality nor gives a bound for every fixed matrix.
   [Regressions](ComplexityTests/Crypto/GSWHiding.lean) include a composite-modulus counterexample
   to whole-matrix universality and an adaptive game with exact nonzero advantage.
   The [generated-key security theorem](Complexity/Crypto/Computational/Homomorphic/GSW/Security.lean)
   proves single-challenge IND-CPA for the actual serialized key generator and encryption program
   against uniform classical strict PPT adversaries. Its
   [decision-LWE assumption](Complexity/Crypto/Computational/LWE/Basic.lean) compares the public
   word `[B*t+e | B]` with a uniform matrix of the same shape; the
   [distribution bridge](Complexity/Crypto/Computational/Homomorphic/GSW/LWE.lean) supplies exactly
   the sampled centered-binomial error law, without exposing the secret or errors.
   One uniform hidden-bit reduction preserves the adversary's full saved state and bounds its
   chosen-message advantage by twice its decision-LWE advantage plus the statistical term above.
   The [positive-noise parameter family](Complexity/Crypto/Computational/Homomorphic/GSW/Parameters.lean)
   takes `n = η = λ+1`, `w = 16+8*ceil(log₂(λ+1))` and `m = (n+1)*w+2λ`.
   It proves the entropy surplus, uniform native parameter routines and strict fresh/one-NAND
   correctness margins simultaneously; the security theorem leaves only the specified LWE
   hypothesis. [Regression clients](ComplexityTests/Crypto/GSWSecurity.lean) check saved-state
   preservation, the attained factor-two loss, adaptive message choice and actual algorithm
   certificates. A [checked formal abstract](abstracts/ComplexityAbstracts/GSWSecurityAbstract.lean)
   spells out both algorithms, their native efficiency and this precise conditional security
   result. It remains outside the curated headline catalogue while the full FHE recovery is open.
   Hardness for the specified noise family is assumed; no worst-case lattice reduction is supplied.
   A separate [depth-margin family](Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters.lean)
   takes `t = 1+ceil(log₂(λ+2))`, `n = η = λ+1`, `w = 16384*t²`, `N = (n+1)*w`,
   `m = N+2λ` and `L = 512*t`. It proves `4*m*η*(N+1)^L < 2^w` for every parameter,
   including zero, together with the entropy surplus, polynomial bounds and uniform native
   unary parameter routines. Only the modulus is returned in binary.
   Its [security corollary](Complexity/Crypto/Computational/Homomorphic/GSW/DepthParameters/Security.lean)
   assumes decision LWE for this exact new family; the earlier family's hardness premise is
   insufficient. The [actual selected-row decryptor](Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit.lean)
   computes total serialized decryption on every well-sized raw secret/ciphertext pair, including
   widths zero and one. Its depth is at most `28 + 18*clog₂(w+1) + 12*clog₂(n)` and its gate
   count at most `131*(n+1)*(w+1)²`. The [native generator](Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/PolyTime.lean)
   charges all arithmetic, indexing, wiring and complete layered NAND augmentation.
   The [parameter fit](Complexity/Crypto/Computational/Homomorphic/GSW/DecryptionCircuit/Parameters.lean)
   proves that the actual augmented circuit, with two NAND microlevels per De Morgan level,
   fits `L` at every security parameter. [Checked clients](ComplexityTests/Crypto/GSWDecryptionCircuit.lean)
   include both decoder ties, negative wraparound, boundary widths and a uniform family generator.
   These circuit results do not establish bootstrappability or transfer a hardness premise.
   Full native circuit evaluation, bootstrappability with compatible parameters and the concrete
   FHE instantiation remain open in #486. The earlier parameter family
   proves fresh and one-NAND correctness; it does not yet supply the augmented-decryption circuit
   or the separate joint circular-security assumption needed for the fixed-key endpoint.
   The [code-composition API](Complexity/Computability/Circuit/Boolean/CodeComposition.lean)
   provides a native polynomial-time constructor for shared-input blocks with different gate
   counts, checked against the existing carry-save circuit without padding. This supports the
   complete shallow-decryption generator in #528.
   [Native carry-save generators](Complexity/Computability/Circuit/Boolean/CarrySave/PolyTime.lean)
   construct the exact existing three-to-two and four-to-two reducers from unary width,
   including all binary references and the unequal carry-bit blocks.
   The [balanced-code generator](Complexity/Computability/Circuit/Boolean/BalancedCode.lean)
   constructs the exact existing half-split tree from the complete native leaf-code list,
   binary input arity and native operator/fallback codes. Its polynomial certificate charges
   all interval-table rows and wire encodings, including dead gates and malformed raw data.
   This completes the balanced-construction prerequisite #543 used by the complete #528 decryptor.
4. **Completeness of oblivious transfer.** In the ideal oblivious-transfer hybrid model, every
   polynomial-time multiparty functionality admits a protocol secure against static malicious
   corruptions, with security defined by real/ideal simulation and allowing abort, under the
   standard communication assumptions. This does not guarantee fairness or delivery of outputs.
5. **Håstad’s optimal MAX-E3SAT hardness.** For every fixed ε with 0 < ε < 1/8, it is NP-hard to
   distinguish satisfiable E3-CNF formulas from E3-CNF formulas for which every assignment
   satisfies at most a 7/8 + ε fraction of clauses. *Partial:*
   [Hastad](Complexity/Computability/PCP/Approximation/Hastad.lean) proves the analytic core:
   completeness and soundness of Håstad's noisy 3-bit linear test on folded Long Code tables
   against `GapLabelCover` with a uniform threshold `0 < η < 1`
   (`Cslib.PCP.Hastad.gapLabelCover_dichotomy_lt_one`), exercised on genuine parallel-edge
   no-instances in [the tests](ComplexityTests/Hastad.lean), and
   [MaxExactThreeSAT](Complexity/Computability/PCP/Approximation/MaxExactThreeSAT.lean) proves the
   easy `7 / 8` random-assignment bound. The reduction to MAX-E3LIN/MAX-E3SAT and NP-hardness of
   Label Cover (PCP theorem with parallel repetition) remain open.
6. **Williams’s ACC lower bound.** NEXP ⊄ ACC⁰: some language in nondeterministic exponential time
   has no polynomial-size, constant-depth nonuniform circuit family over unbounded-fan-in AND, OR,
   NOT and modular-counting gates with fixed moduli.
7. **Valiant’s algebraic completeness theorem.** Over every field of characteristic different from
   two, the permanent polynomial family is VNP-complete under polynomially bounded projections:
   every VNP family is obtained from a polynomially larger permanent by substituting variables and
   field constants.
8. **Kabanets–Impagliazzo derandomization-to-lower-bounds theorem.** If polynomial identity testing
   for arithmetic circuits over the integers has a deterministic polynomial-time algorithm, then
   either NEXP ⊄ P/poly or the permanent family has no polynomial-size arithmetic circuits over the
   integers.
9. **Babai–Fortnow–Lund multiprover theorem.** MIP = NEXP: a language has a classical multiprover
   interactive proof with a probabilistic polynomial-time verifier and constant
   completeness–soundness gap if and only if it belongs to nondeterministic exponential time. The
   provers cannot communicate during the protocol. *Partial:*
   [MIP](Complexity/Computability/Complexity/Classes/MIP.lean) defines classical multiprover
   proofs with a constant number of provers per language and a strict polynomial-time fair-coin
   verifier. It proves `IP ⊆ MIP₂ ⊆ MIP`, closure under Karp reductions, deterministic prover
   optimality, and the unconditional upper bound `MIP ⊆ NEXP`. The reverse direction
   `NEXP ⊆ MIP₂`, requiring the BFL multilinearity test and arithmetization of exponential-time
   tableaux, is deferred; the full characterization is not claimed.
10. **Regev’s worst-case-to-average-case reduction.** For suitable modulus q and Gaussian noise
    rate α satisfying αq > 2√n, an efficient algorithm for search-LWE in dimension n yields a
    quantum polynomial-time algorithm for worst-case GapSVP and SIVP with approximation factor
    Õ(n/α). The noise distribution, modulus restrictions and quantum reduction are part of the
    theorem.

## Modern FHE methods and deployment priorities

The planning update is tracked in
[#513](https://github.com/cslib-community/complexitylib/issues/513). The targets below remain
unimplemented; the generic Gentry theorem and current GSW development do not establish them.
First complete [#486](https://github.com/cslib-community/complexitylib/issues/486): actual GSW
algorithms, the exact chosen-noise decision-LWE reduction, admissible parameters, and shallow
augmented decryption connected to the leveled/fixed-key endpoints. The current native
key-generation/encryption and security milestones are
[#500](https://github.com/cslib-community/complexitylib/issues/500) and
[#501](https://github.com/cslib-community/complexitylib/issues/501); completing them still leaves
decryption/evaluation runtime and bootstrappability obligations.

**Industrial context, checked 2026-10-23.** Current FHE libraries serve distinct workloads:

| Workload | Methods and current implementation evidence |
| --- | --- |
| Exact modular arithmetic and packed integer computations | BFV/BGV are supported by [Microsoft SEAL](https://github.com/microsoft/SEAL) and [OpenFHE](https://github.com/openfheorg/openfhe-development). |
| Approximate vector arithmetic, including numerical inference | CKKS is supported by SEAL and OpenFHE; its numerical approximation is part of the result contract. |
| Boolean/integer operations, comparisons and lookup tables | [TFHE-rs](https://docs.zama.org/tfhe-rs/get-started) implements TFHE with programmable bootstrapping; OpenFHE also implements FHEW/TFHE-family methods. |

There is commercial use beyond library availability: [Duality states that its secure data
collaboration platform is built with OpenFHE](https://dualitytech.com/platform/open-source/), and
[Zama documents TFHE-rs execution in its confidential-blockchain coprocessors](https://docs.zama.org/protocol/protocol/overview/coprocessor).
These are vendor descriptions, not market-share measurements or independent deployment audits.
Bounded-depth arithmetic can use leveled evaluation without bootstrapping; a bootstrap is a
separate algorithmic capability, not something every workload invokes.

Develop the following in reviewable milestones, reusing existing finite sampling, gadget algebra,
native certificates and game reductions where their hypotheses match:

1. **Shared ring arithmetic and precise RLWE experiments.** Construct the actual polynomial-ring
   operations, starting with `R_q = (Z/qZ)[X]/(X^d + 1)` for power-of-two `d`. Prove residue-number
   (RNS/CRT) conversions, rounding and modulus-switching error bounds; prove that forward/inverse
   negacyclic NTTs implement ring multiplication under explicit modulus/root conditions. Give
   native certificates for the serialized algorithms, including malformed inputs. The
   [Intel HEXL kernels](https://github.com/IntelLabs/hexl) provide a concrete implementation target.
   Define the exact RLWE secret/error distributions and distinguishing experiment separately:
   an ordinary-LWE reduction for #486 does not establish this RLWE claim.
2. **FHEW/TFHE programmable bootstrapping.** Follow
   [Ducas–Micciancio](https://eprint.iacr.org/2014/816) and
   [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870), a close next use of the
   GSW gadget work. Construct ring-GSW external products, blind rotation, sample extraction and
   key switching. For an explicit plaintext domain and admissible lookup table `f`, prove that
   the actual bootstrap decrypts to `f(m)`, with its noise and failure bounds, output width and
   total runtime. Account for negacyclic lookup restrictions and finite torus representations;
   floating-point FFT implementations need their own rounding-error proof. Then assess
   [smaller-key methods of Lee et al.](https://eprint.iacr.org/2022/198) and batched variants,
   preserving their exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV.** Formalize the constructions of
   [Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277) and
   [Fan–Vercauteren](https://eprint.iacr.org/2012/144), including slot encoding, multiplication,
   relinearization, rotations and level/modulus management. For permitted arithmetic circuits,
   prove decryption equals evaluation in the stated plaintext ring, with explicit depth, noise,
   modulus and packing conditions. Distinguish equality modulo the plaintext modulus from
   ordinary integer equality; the latter needs a range bound. Establish leveled evaluation
   before adding a separately proved refresh algorithm.
4. **Approximate packed CKKS and its bootstrap.** Follow
   [Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421). Define finite message encodings and the
   complex-slot interpretation, then prove an explicit norm bound on decoded evaluation error
   for bounded inputs and specified scales, levels and circuits. Include rescaling, rounding,
   key switching and rotations in that bound. A bootstrap must prove its precision after modulus
   raising, coefficient/slot transforms and approximate modular reduction; use the
   [OpenFHE bootstrap description](https://github.com/openfheorg/openfhe-development/blob/main/src/pke/examples/CKKS_BOOTSTRAPPING.md)
   as a concrete implementation reference. Approximate arithmetic requires an explicit
   approximate-correctness interface, not the current exact Boolean equality contract.
5. **Scheme switching and multiparty extensions.** OpenFHE's CKKS/FHEW switching, vectorized
   functional bootstrapping and threshold variants motivate later targets. Prove each conversion
   preserves the intended value within its range/precision contract and state the joint
   evaluation-key security assumption. For threshold key generation/decryption, fix corruption
   thresholds, interaction, robustness and decryption-query access explicitly; distinguish
   honest-but-curious security from malicious security. These are protocol theorems beyond
   single-key IND-CPA.

For every scheme, specify whether encryption is public-key or symmetric and prove the matching
chosen-plaintext security reduction for the actual algorithms and public evaluation keys. Keep
ordinary LWE/RLWE assumptions, circular/KDM assumptions and concrete attack-cost estimates distinct.
If correctness permits a nonzero decryption-failure probability, introduce that game explicitly
and relate it to the current perfect-support interface. Require nonvacuous parameter families,
composed error bounds, full-input native runtime and independent source/statement review before
claiming an endpoint. Hardware acceleration benchmarks do not replace any of these proofs.

## Long-term coverage and reuse

The long-term bar is to support formalizing every paper appearing in the
[Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/).
Across successive papers, the additional work should increasingly be their new mathematics:
standard models, representation changes, reductions, resource certificates and proof techniques
should come from the library. This is an amortized goal. A new method may require substantial
infrastructure once; later developments should reuse it instead of rebuilding it. Count that
infrastructure's implementation and maintenance cost when assessing the improvement.

The reusable-API placement audit [#404](https://github.com/cslib-community/complexitylib/issues/404)
follows the space/constructibility extraction in #402. It tracks generic time-class, encoding,
bit-string and NP helpers still located in specialized theorem modules; each proposed extraction
needs an import-boundary review and preserves existing public interfaces and resource conventions.

### Catalogue the classes and theorems

Build an auditable coverage index spanning the complete
[Complexity Zoo](https://complexityzoo.net/Complexity_Zoo), including its hierarchies, nonuniform
and communication classes, and extend it with the canonical problems and theorems needed by ECCC
papers. The Zoo supplies a catalogue and references; verify definitions and results against their
primary sources. This is a coverage target, not a claim that the catalogue is already formalized.

Each entry should record its source and aliases, precise model and conventions, existing Lean
declarations, missing prerequisites, and status: unassessed, definition only, partial development,
or verified theorem. Track containments, separations, closure properties, complete problems and
reductions separately. A defined class or a combinatorial lemma does not establish its advertised
machine characterization, completeness theorem or efficient construction.

Cover decision, function, search, counting, promise, distributional and parameterized problems.
Keep uniformity, advice, oracle access, error gaps, resource measures and reduction types explicit.
Share class operators and their closure theorems where they derive families of variants. Keep
canonical definitions in their mathematical modules; the index should link to them rather than
maintain a second set of definitions. Existing module docstrings, source markers and the detailed
milestones below remain the authority for their respective facts.

### Next steps after basic class closure

The verifier-based `UP` and `CeqP` developments, basic Boolean closures, exact-count
polynomial-time precomposition, and generic DP/SAT–UNSAT completeness are implemented.
The forward machine-to-verifier direction is proved for `#P` and `GapP`: accepting and
rejecting terminal counts of fixed finite-control list-choice machines under polynomial clocks
have actual certified binary verifiers. The actual reverse guess-and-verify construction and
[#P machine characterization](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean)
are now proved. The [signed GapP construction and characterization](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean)
are also proved, using balanced verdict routing and an actual selector between independent witness
families. The [UP](Complexity/Computability/Complexity/Classes/UP/Machine.lean) and
[FewP](Complexity/Computability/Complexity/Classes/FewP/Machine.lean) native characterizations
are also proved: the exact #P bridge preserves the bound of one or a polynomial on accepting
occurrence traces, independently of the all-branches clock. SPP, FewP, fixed-modulus ModP, coUP and coC=P
now have verifier-based definitions and basic closure/containment developments. FewP ⊆ SPP and
PH ⊆ P^#P = P^PP are proved, with uniform simulations under the function-bit oracle convention.
Exact #P/GapP counts now have certified binary-output polynomial-space evaluators, yielding
PP ⊆ PSPACE and P^PP = P^#P ⊆ PSPACE, including arbitrary injective oracle encodings via
total clocked counting-machine extensions
([counting space](Complexity/Computability/Complexity/Classes/Counting/OracleSpace.lean)).
Extend these with counting reductions and further oracle results, preserving exact
multiplicities when required. The current modular Boolean closures require a prime modulus. The complementary modular class is
implemented, with equality to ModP for prime moduli. Fixed positive moduli admit GapP
zero/nonzero-residue characterizations; SPP (hence FewP) is in both modular classes for every
modulus at least two, including composite moduli. Both modular classes lie in PSPACE for every
fixed natural modulus. US, coDP, the finite Boolean
hierarchy (`BH` and `coBH`, base-class Boolean operations on `BH`, and the finite-hierarchy
level-collapse equivalences `BH_{k+1} = BH_k ↔ BH_k = coBH_k ⇒ BH = BH_k`), WPP and LWPP now have
definitions and elementary containments/closures. Full Boolean-hierarchy Boolean closure is
proved with explicit finite-level upper bounds, as is BH ⊆ Σ₂ ∩ Π₂ using same-level union and
intersection closure of every Σₖ and Πₖ
([hierarchy connection](Complexity/Computability/Complexity/Classes/BooleanHierarchy/PH.lean)),
and Kadin's polynomial-hierarchy collapse (`coBH k ⊆ BH k → PH = Σ₃ᴾ`, `BH (k + 1) = BH k → PH = Σ₃ᴾ`,
`DP = coDP → PH = Σ₃ᴾ`, and `SATUNSAT ∈ coDP → PH = Σ₃ᴾ`) is proved in
[BooleanHierarchy.Kadin](Complexity/Computability/Complexity/Classes/BooleanHierarchy/Kadin.lean).
Further proved results include LWPP many-one
reduction closure, unary-indexed target normalization, and full one-sided polynomial-family
multiple-target robustness: Poly-WPP = WPP and Poly-LWPP = LWPP, and the full two-sided
(Poly,Poly)-WPP/WPP and (Poly,Poly)-LWPP/LWPP characterizations with disjoint uniformly computed
accepting/rejecting binary target lists. Original targets may be zero; neither index must be
computable ([WPP.TwoSided](Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean)).
Uniform bounded conjunction and disjunction also preserve both classes for a single jointly
uniform language on instances and unary indices, with any polynomial-time unary input-dependent
bound. The LWPP proof normalizes all possible prefix targets at each length
([WPP.Bounded](Complexity/Computability/Complexity/Classes/WPP/Bounded.lean)); it does not
establish adaptive oracle closure. Polynomial-time truth-table reductions now preserve both
WPP and LWPP, using an arbitrary polynomial-time Boolean combiner on a uniform batch of
queries ([WPP.TruthTable](Complexity/Computability/Complexity/Classes/WPP/TruthTable.lean)).
Query lengths and unary query counts may vary at fixed input length; LWPP normalizes both.
Adaptive WPP closure and UP-oracle containment are not claimed by this result.
Oracle lowness of SPP (`GapPWithOracle_eq_GapP_of_mem_SPP`, hence lowness for `SPP`, `C=P`, `PP`,
and the unrelativized-`FP`-target classes `LWPPWithFixedTarget` and `WPPWithFixedTarget`), LWPP
(`exists_mul_mem_GapP_of_mem_LWPP`, hence lowness for `C=P`, `PP`, and the unrelativized-`FP`-target
classes `LWPPWithFixedTarget` and `WPPWithFixedTarget`), and WPP (`PPWithOracle_eq_PP_of_mem_WPP`)
is proved in [WPP.Lowness](Complexity/Computability/Complexity/Classes/WPP/Lowness.lean), and
[SharpP.Lowness](Complexity/Computability/Complexity/Classes/SharpP/Lowness.lean) proves
precomposition of `#P` and `GapP` with `FP^(UP ∩ coUP)` functions, the exact lowness
characterizations `Low(#P) = UP ∩ coUP` (`SharpPWithOracle_eq_SharpP_iff`), `Low(UP ∩ coUP) = UP ∩ coUP`
(`UPWithOracle_inter_coUPWithOracle_eq_iff`), `Low(GapP) = SPP` (`GapPWithOracle_eq_GapP_iff`),
and `Low(SPP) = SPP` (`SPPWithOracle_eq_SPP_iff`), `UP ∩ coUP` lowness for `UP`, `coUP`, `FewP`,
`US`, and `SBPWithFixedTarget`, and `SPP`/`FewP`/`UP ∩ coUP` lowness for relativized modular
counting classes (`ModPWithOracle_eq_ModP_of_mem_SPP`, `coModPWithOracle_eq_coModP_of_mem_SPP`,
`ParityPWithOracle_eq_ParityP_of_mem_SPP`);
target-relativized `LWPP^A` / `WPP^A` / `SBP^A` definitions and lowness with `FP^A` targets are not claimed.
[Oracle lowness of `NP ∩ coNP` and `UP ∩ coUP`](Complexity/Computability/Complexity/Classes/Oracle/Lowness.lean)
proves `P^(NP ∩ coNP) = NP ∩ coNP`, `P^(UP ∩ coUP) = UP ∩ coUP`, `NP^(NP ∩ coNP) = NP`, the
characterization `NP^A = NP ↔ A ∈ NP ∩ coNP` (`NPWithOracle_eq_NP_iff`), and
`NP = coNP ↔ ∀ A ∈ NP, NP^A = NP` (`NP_eq_coNP_iff_forall_NPWithOracle_eq_NP`).
PP is closed under polynomial-time truth-table reductions (Fortnow–Reingold), hence under
intersection, union, difference, symmetric difference (Beigel–Reingold–Spielman) and
polynomial-time bounded quantifiers ([PP.TruthTable](Complexity/Computability/Complexity/Classes/PP/TruthTable.lean)).
The proof uses Newman's sign-approximating polynomial on GapP. P is closed under the same
reductions. Closure of PP under adaptive polynomial-time Turing reductions (`P^PP = PP`) would
give `PH ⊆ PP` by Toda's theorem; it is open and not claimed.
The binary-output FP-to-#P/GapP bridge is available. Parsimonious Cook–Levin gives #P-completeness of #SAT and SAT-based complete problems for ⊕P, US, ModₖP/coModₖP, PP (both threshold #SAT and MAJSAT) and C=P/coC=P ([CountingSAT](Complexity/Computability/Complexity/Problems/CountingSAT.lean)). Remaining extensions include
permanent completeness and target-relativized WPP/LWPP oracle classes with `FP^A` targets.
SBP and AWPP now have verifier-based definitions, the elementary NP/BPP/SPP-to-PP
containments, many-one reduction closure, SBP union closure and AWPP Boolean closure.
WPP ⊆ AWPP is proved, including signed binary-output targets. Uniform AWPP
amplification achieves error at most `2^(-r(x))` for every requested exponent polynomially
bounded in encoded input length, using one GapP numerator and a length-polynomial
dyadic denominator. The requested rate need not be computable: the construction
uses a fixed dominating polynomial. The explicit construction uses `12q(n)` majority
trials and denominator exponent `12q(n)p(n)`; see
[AWPP amplification](Complexity/Computability/Complexity/Classes/AWPP/Amplification.lean).
[Uniform SBP amplification](Complexity/Computability/Complexity/Classes/SBP/Amplification.lean)
achieves multiplicative gap `2^r(x)` for every polynomially bounded requested exponent,
with a #P count and positive binary-output polynomial-time threshold. Intersecting an SBP
language with a BPP language stays in SBP. MA ⊆ SBP is proved with the Arthur–Merlin classes.
The [set lower bound protocol](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean)
already proves SBP ⊆ AM. [Uniform indexed #P/GapP products](Complexity/Computability/Complexity/Classes/SharpP/Products.lean)
provide a counting-algebra foundation for future oracle simulations.
[Relativized counting and majority verifiers](Complexity/Computability/Complexity/Classes/PP/Oracle.lean)
provide the positive-GapP characterization and elimination of P-decidable oracles.
[AWPP PP-lowness](Complexity/Computability/Complexity/Classes/AWPP/Lowness.lean) is proved for
the strict adaptive oracle-verifier model: every AWPP word oracle satisfies
`PPWithOracle A enc = PP enc`, with arbitrary injective input encodings and exact ties rejecting.
These definitions retain the verifier-model boundary stated above.

### Extend the mathematical canon

This map adds long-term directions to the concrete developments below. It follows the breadth of
[ECCC's scope](https://eccc.weizmann.ac.il/colloquium/call_for_papers/) and the Zoo, rather than the
contents of the original port. Entries are targets for coverage audits and substantial theorem
developments, not assertions that every prerequisite is missing or assignments to current workers.

| Area | Coverage to establish or extend |
| --- | --- |
| Structural complexity | Time/space and exponential hierarchies; oracle and advice classes; unambiguous and promise classes; completeness, padding, self-reducibility, Ladner's theorem, relativization and oracle separations. Preserve each reduction's resource bound. |
| Space and alternation | Build on native `NPSPACE = PSPACE`, TQBF completeness, `NL ⊆ P`, [PH ⊆ PSPACE](Complexity/Computability/Complexity/Classes/Inclusions.lean) and [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean). Extend the [machine-class milestones](#machine-class-milestones), alternating time/space classes and bounded-alternation characterizations of PH. Distinguish polynomial-space simulation from sharp bounds for sublinear space. |
| Counting and modular classes | Build on `#P`, `GapP`, `PP`, [parity-P](Complexity/Computability/Complexity/Classes/ParityP.lean) and [Toda's PH ⊆ P^#P theorem](Complexity/Computability/Complexity/Classes/Toda.lean), with a fixed polynomial-time program correct against every oracle answering the counting function's bits. Extend counting reductions and machine characterizations, permanent completeness, modular/counting hierarchies and the oracle-algorithm form of Stockmeyer approximate counting. |
| Interactive and probabilistic proofs | [IP ⊆ PSPACE](Complexity/Computability/Complexity/Classes/IP/PSPACE.lean) is proved for the strict polynomial-time, private-coin verifier model. [IP = PSPACE](Complexity/Computability/Complexity/Classes/IP/Shamir.lean) is proved, with a machine-certified Shamir–Shen-style verifier for TQBF, and [computational zero-knowledge proofs for NP](Complexity/Crypto/Computational/ZeroKnowledge.lean) (via a 3-copy masked-3SAT truth-table commitment protocol following Goldreich–Micali–Wigderson) are proved from one-way functions for uniform polynomial-time-generable instance/witness/auxiliary-input families at soundness error `1 / 3`. [Arthur–Merlin classes](Complexity/Computability/Complexity/Classes/ArthurMerlin.lean) are defined, with amplification, `AM ⊆ Π₂`, the set lower bound protocol and graph non-isomorphism in AM; develop public/private-coin transformations, the deferred BFL reverse inclusion, universal-instance and arbitrary-auxiliary-input zero knowledge, witness-level Levin reductions, statistical/perfect zero knowledge and sequential soundness amplification. [Classical MIP](Complexity/Computability/Complexity/Classes/MIP.lean) with a constant number of provers satisfies `IP ⊆ MIP₂ ⊆ MIP ⊆ NEXP`, with deterministic prover optimality and Karp-reduction closure. Reuse the existing PCP and probabilistic foundations. |
| Boolean circuits and parallel computation | Build on the `3.5n - o(n)` general-circuit lower bound for affine dispersers of dimension `o(n)` ([AffineDisperser](Complexity/Computability/Circuit/Boolean/AffineDisperser.lean)) and the De Morgan cover-complexity transfer ([Fusion/DeMorgan](Complexity/Computability/Circuit/Fusion/DeMorgan.lean)). Complete the [Jukna coverage](#jukna-coverage), uniform/nonuniform NC/AC/TC and related classes, circuit-to-machine bridges, algorithm-to-lower-bound arguments and barriers such as natural proofs and algebrization. |
| Algebraic and arithmetic complexity | Build on [VP and p-projections](Complexity/Computability/Circuit/Arithmetic/VP.lean), [VNP and VP ⊆ VNP](Complexity/Computability/Circuit/Arithmetic/VNP.lean), [determinant ∈ VP](Complexity/Computability/Circuit/Arithmetic/Determinant.lean) over commutative rings, and [Laplace expansion of the permanent](Complexity/Foundations/Data/Matrix/Permanent.lean). Prove permanent VNP-completeness with its characteristic assumptions, prove the Kabanets–Impagliazzo theorem, extend formula/branching-program models, identity testing, hitting sets, tensor and rank methods, and certify uniform construction costs separately from gate counts. |
| Approximation and constraint satisfaction | [Random assignment](Complexity/Computability/PCP/Approximation/MaxExactThreeSAT.lean) proves the `7 / 8` random-assignment bound for exact 3-CNF with three distinct variables per clause (`CNF.IsExactThreeDistinct`), and [Håstad's 3-bit test](Complexity/Computability/PCP/Approximation/Hastad.lean) proves completeness and soundness of Håstad's 3-bit linear test against `GapLabelCover` (`1 - δ` vs `1 / 2 + 4 * ε`). Build the reduction to MAX-E3LIN and, via the 4-clause XOR gadget, to MAX-E3SAT on clauses with three distinct variables, Raz's parallel repetition theorem, and the perfect-completeness `(1, 7 / 8 + ε)` reduction; develop further gap and approximation-preserving reductions, APX/PTAS/FPTAS, canonical inapproximability consequences of PCP, CSP classifications and relaxation gaps. State assumptions such as the Unique Games Conjecture explicitly. |
| Pseudorandomness and coding | Build on [conditional `P = BPP` from exponential worst-case hardness in `E` (Impagliazzo–Wigderson)](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean) via Nisan–Wigderson and Sudan–Trevisan–Vadhan, [Sudan's Reed–Solomon list decoding](Complexity/Foundations/Data/Code/Sudan.lean) (decoder correctness only: the decoder is noncomputable and no running time is claimed), and [expander-walk hitting bounds](Complexity/Foundations/Combinatorics/Expander/Hitting.lean). Extend space-bounded generators, extractors/condensers, limited independence, explicit expanders, and Guruswami–Sudan / local decoding. Separate finite combinatorial guarantees from uniform construction and decoding costs. |
| Complexity-theoretic cryptography | One-way functions imply SAT ∉ P and SAT ∉ BPP, and MCSP ∈ BPP rules them out (Kabanets–Cai; [OneWay/MCSP](Complexity/Crypto/Computational/OneWay/MCSP.lean)). [Naor bit commitments](Complexity/Crypto/Computational/Commitment.lean) (with hiding against randomized stateful PPT receivers and deterministic polynomial-time receiver-string/bit families), [Goldreich–Micali–Wigderson zero knowledge for NP](Complexity/Crypto/Computational/ZeroKnowledge.lean) (uniform zero knowledge over deterministic polynomial-time instance/witness/auxiliary-input families via a 3-copy masked-3SAT truth-table commitment protocol), [uniform symmetric MACs and PRF-based MACs](Complexity/Crypto/Computational/MAC.lean) (`SUFCMA`, `EUFCMA`, `OneTimeEUFCMA`, quantitative `EUF-CMA ≤ SUF-CMA`, unique-tag equivalence, and the Boneh–Shoup Theorem 6.2 PRF-to-SUF-CMA/EUF-CMA reduction), and [keyed collision-resistant hash families and the Merkle–Damgård transform](Complexity/Crypto/Computational/CollisionResistant.lean) are proved. Uniform one-way functions are also equivalent to one-time secure digital signatures for `n`-bit messages, via [Lamport's construction](Complexity/Crypto/Computational/OneWayToSignature.lean); full EUF-CMA security implies one-way functions. [Carter–Wegman MACs](Complexity/Crypto/Protocols/MAC/CarterWegman.lean) formalize unconditional one-time and adaptive multi-query issued-counter EUF-CMA/SUF-CMA security (`≤ ε`) from `ε`-almost-Δ-universal hash families together with the arbitrary-pad hybrid bound, the exact single-query fixed-nonce reduction to `prfRealGame`/`prfIdealGame` (`prfOneTimeGame_le`, `prfOneTimeGame_ofProbComp_le`), and `xpolyHash`/Boolean-matrix/subset-sum instantiations (`IsOraclePPT` admissibility of the PRF-pad reduction, uniform word-level forger/hash families, the asymptotic `PseudorandomFunction` corollary, and fresh-counter nonces remain open). Extend the existing OWF/PRG/PRF/MAC/CRHF/commitment/ZK results with reusable adaptive reductions, many-time digital signatures, encryption, universal-instance zero knowledge, hard-core and hardness-amplification methods, and connections to learning and average-case hardness. |
| Communication, queries and data structures | Build on the `Ω(n)` bounded-error randomized disjointness lower bound ([Disjointness](Complexity/Computability/Communication/Disjointness.lean)), Karchmer–Wigderson ([Boolean](Complexity/Computability/Circuit/Boolean/KarchmerWigderson.lean), [monotone](Complexity/Computability/Circuit/Monotone/KarchmerWigderson.lean)), and Raz–Wigderson's monotone depth bound for bipartite matching ([BipartiteMatching](Complexity/Computability/Circuit/Monotone/BipartiteMatching.lean)). Extend multiparty protocols, discrepancy and information complexity, direct-sum/product results, lifting theorems, and reductions to streaming, sketching and cell-probe lower bounds. Reuse upstream query models. |
| Proof complexity | Build on [Cook–Reckhow systems and simulations](Complexity/Computability/Complexity/ProofSystem.lean), including the polynomially bounded-system characterization of NP = coNP, the [resolution size–width tradeoff](Complexity/Logics/Propositional/Resolution/SizeWidth.lean), [tree-like resolution/DPLL search-tree certificates](Complexity/Logics/Propositional/Resolution/TreeLike.lean), [Tseitin formulas on expanders](Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) and [Haken's pigeonhole lower bound](Complexity/Logics/Propositional/Resolution/Pigeonhole.lean). Extend proof-space lower bounds, Frege, cutting planes, polynomial calculus and sum-of-squares. The certificate correspondence does not certify a DPLL solver's runtime. |
| Average-case complexity and learning | Uniform-distribution learning on CSLib's PAC API, the LMN low-degree algorithm and Kushilevitz–Mansour with membership queries are [proved](Complexity/MachineLearning/UniformLearning/KushilevitzMansour.lean); running times are not machine-certified. Distributional problems and reductions, samplability, average-to-worst-case connections, PAC/agnostic/SQ learning, learning lower bounds, compression and refutation. Existing cryptographic learners are starting points, not coverage of learning theory. |
| Property and distribution testing | Distance and access models, one/two-sided and tolerant testing, query/sample bounds, canonical graph/algebraic/distribution testers and lower bounds. |
| Fine-grained and parameterized complexity | Under ETH, 3-coloring, independent set, vertex cover and Hamiltonian cycle and path have no 2^{o(\|V\|+\|E\|)} algorithms and clique none in 2^{o(\|V\|)} ([GraphProblems](Complexity/Computability/Complexity/FineGrained/GraphProblems.lean)); the Hamiltonian bounds (directed and undirected) use linear-size diamond reductions. [FPT and XP](Complexity/Computability/Complexity/Parameterized.lean) are defined with arbitrary (not necessarily computable) `f`; `P ⊆ FPT ⊆ XP`, Boolean closure of FPT (complement for XP), closure under fpt-reductions and `FPT = XP = P` for bounded parameters are proved, and SAT is in FPT for the number of variables. [Kernelization](Complexity/Computability/Complexity/Parameterized/Kernelization.lean) (`IsKernelization`, `HasKernel`, `HasPolyKernel`) and the Cai–Chen–Downey–Fellows equivalence (`A ∈ FPT enc κ ↔ HasKernel enc κ A` for `A ∈ DTIME enc t` over a nonempty instance type) are proved, and [VertexCover](Complexity/Computability/Complexity/Parameterized/VertexCover.lean) is in FPT parameterized by target size `k` in time `O(2^k (|x|+1)^e)` by a bounded search tree and has [Buss's polynomial kernel](Complexity/Computability/Complexity/Parameterized/VertexCover/BussKernel.lean) with at most `k(k+2)` vertices and encoded length at most `40(k+1)^6` (`VertexCover_hasPolyKernel`). Further fine-grained reductions and consequences conditional on ETH/SETH and other named hypotheses; strongly uniform (computable `f`) variants, further explicit polynomial kernels, W/A hierarchies and parameterized lower bounds. |
| Total search and computational games | Build on [FNP, FP and TFNP with search reductions](Complexity/Computability/Complexity/Classes/TFNP.lean), including `FP = FNP` exactly when `P = NP` ([search to decision](Complexity/Computability/Complexity/Classes/TFNP/SearchToDecision.lean)), `TFNP ⊆ FP → NP ∩ coNP ⊆ P`, and the canonical subclasses [PLS, PPP, PPAD and PPA](Complexity/Computability/Complexity/Classes/TFNP/Subclasses.lean) with their combinatorial totality principles ([Principles](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Principles.lean)), inclusions `PLS, PPP, PPAD, PPA ⊆ TFNP`, `PPAD ⊆ PPP`, and `PPAD ⊆ PPA`, and De Morgan circuit problems (`LocalOpt ∈ PLS`, `Pigeon ∈ PPP`, `EndOfLine ∈ PPAD`, `Leaf ∈ PPA`). Their [completeness](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean) now follows from polynomial-time construction of function-family circuit codes, preserving binary local-search costs. Develop CLS, further local search, fixed-point and equilibrium problems. |
| Logic and descriptive complexity | Building on [Fagin's theorem](Complexity/Computability/Complexity/Fagin/Converse.lean): logical characterizations of additional resource classes, fixed-point and order-invariant queries, and uniform translations between syntax, structures and algorithms. |
| Kolmogorov complexity and metacomplexity | Build on [plain Kolmogorov uncomputability](Complexity/Computability/Kolmogorov/Uncomputability.lean), [single-tape and Post–Turing (`TM0`/`TM1`) description methods and simulations](Complexity/Computability/Kolmogorov/SingleTape.lean), and [multi-tape description methods and `Partrec` optimality](Complexity/Computability/Kolmogorov/MultiTape.lean) (#318): `ofTM0` and `ofTM1` are defined through the `SingleTapeTM` embeddings of Mathlib's `TM0`/`TM1`; `ofSingleTapeTM` (and `ofTM0`) are simulated by `ofMultiTapeTM` with zero program overhead and linear time overhead (single-tape → multi-tape only; the reverse simulation is not formalized); and each of `ofSingleTapeTM`, `ofTM0`, `ofTM1` and `ofMultiTapeTM`, pushed forward along a computable decoder, is simulated by the universal partial-recursive description method `universal` with additive overhead. Extend prefix-free complexity, resource-bounded MCSP variants and connections to learning, cryptography and lower bounds. |
| Quantum complexity | Reusable circuit/channel/measurement semantics, uniformity and approximation costs, BQP/QMA and related query, communication and interactive classes, amplification, containments and complete problems. Reuse suitable quantum foundations rather than create incompatible models. |

### Measure reuse across papers

Use a growing, source-pinned sample of papers across these areas as demanding clients, including
papers chosen after an API was designed. For each, identify the exact claims and assumptions,
reused declarations, genuinely new mathematics, missing standard dependencies, and representation
or automation friction. Promote recurring obligations into shared APIs only after demonstrating
reuse; a framework is not successful merely because its first client compiles.

Measure the whole sequence of developments: shared code plus clients, proof and interface size,
elaboration/checking cost, and remaining manual machine or encoding work. The desired trend is
less repeated foundational work per paper while preserving readable proofs and exact quantitative
statements. Novel arguments will still require novel proofs. Keep this catalogue and evidence
linked to declarations and reviewed revisions, rather than adding parallel narrative inventories.

## Repository identity and home

This library is **Complexitylib**: computational complexity theory built on CSLib. The temporary
name `complexitylib2` distinguished the CSLib-based rewrite while both implementations were active;
it is not a lasting project identity. The canonical repository is
[`cslib-community/complexitylib`](https://github.com/cslib-community/complexitylib). The original,
pre-CSLib implementation remains available at the renamed historical repository
[`complexitylib-v1`](https://github.com/SamuelSchlesinger/complexitylib-v1), with archival pending
disposition of remaining work there.

Moving the repository to CSLib Community is an owner and name change for continuing development,
not a handover of Samuel's editorial direction and not acceptance into upstream CSLib. AI
assistance is a development method, and community participation includes mathematical review, API
design, documentation and maintenance as well as proving new theorems.

The repository consolidation has these maintenance requirements:

* **Auditable claims.** Check each README result against its public statement, definitions,
  assumptions, encodings and resource model. Preserve nonconstructive and conditional boundaries;
  passing Lean does not establish that a statement matches its prose or literature source.
* **Reproducible validation and review.** Run all six checks on the migration revision, retain the
  full-library axiom audit and representative clients, and record independent review with that
  revision in the PR or commit description, following
  [CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).
* **A usable contribution path.** A new contributor can find a bounded task, the relevant APIs,
  source references, validation commands and review expectations without private conversation
  history or a maintainer's agent installation.
* **One active project.** Preserve this repository's issues, pull requests, releases and history
  through a repository transfer; archive V1 rather than maintaining two active libraries. Verify
  redirects, CI, release assets and repository links after the move.

Completing every V1 port, Jukna chapter, or future resource-bound improvement is not a condition
of the repository move. The work below remains available for subsequent, independently reviewed
batches.

## Continuing priorities

1. **First-order reductions and projections, with machine and uniformity bridges.** Complete
   these milestones in order of their dependencies. Each requires public Lean results, a
   nonvacuous client, a headline-abstract assessment, and independent mathematical, API and
   formal-abstract reviews of the completed revision.

   - [ ] **Ordered first-order complexity, in standard terminology.** Decided 2026-10-19: the
     library's first-order complexity follows the usual convention of descriptive complexity
     [Immerman][Immerman1999]. Structures are ordered, on `{0, …, n-1}` with `n ≥ 2`, and FO
     means FO(≤, BIT). The lower bound follows
     [Proviso 1.15, p. 16](https://people.cs.umass.edu/~immerman/pub/ch0_1_2.pdf):
     the numeric constants 0 and 1 are distinct. This corrects the handoff's `n ≥ 1`.
     First-order reductions are first-order queries on lexicographically
     ordered k-tuples, and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings. The
     order-free `FO.Reduces`, `FO.QFReduces` and `FO.Definable` remain as a general layer of
     interpretations without built-in order. The ordered notions get their own names. Restate
     the headline results in the ordered setting: SAT, 3SAT, 3COL, IS, clique and VC
     NP-complete under first-order or quantifier-free projections; FO(≤, BIT) ⊆ L; first-order
     reductions are logspace reductions; REACH NL-complete; Circuit Value P-complete under
     first-order reductions. The order-free versions cannot reach several of these: SAT → 3SAT
     appears to need an order, and SAT-hardness without order needs an empty-structure
     hypothesis.
     The ordered query layer allows dependence on the canonical order; it does not impose
     invariance under arbitrary permutations of the input relations. Numeric predicates are
     computed from the universe size, not supplied as unverified input tables.
     **Canonical-structure prerequisite completed (#33):**
     [Ordered/Basic](Complexity/Logics/FirstOrder/Ordered/Basic.lean) supplies canonical
     `≤`/`BIT` and numeric `0`/`1`/`max` on `Fin n`, `n ≥ 2`, using native Mathlib
     terms/formulas and language sums. Input formulas, including constants and quantifiers,
     preserve truth. [Ordered/Interpretation](Complexity/Logics/FirstOrder/Ordered/Interpretation.lean)
     realizes forgetting the numeric expansion through the existing relational interpretation
     API, with an isomorphism to the input.
     **Target-constant prerequisite completed (#38):**
     [Interpretation/Constants](Complexity/Logics/FirstOrder/Interpretation/Constants.lean)
     adds finitely many formula-defined target constants, with explicit existence and uniqueness
     inside the interpreted domain, and native formula/sentence truth-preserving pullback.
     [Ordered/Constants](Complexity/Logics/FirstOrder/Ordered/Constants.lean) supplies valid
     target `0`/`1`/`max` for every canonical structure with `n ≥ 2`.
     **Full-domain tuple-order prerequisite completed (#43):**
     [Ordered/Tuple](Complexity/Logics/FirstOrder/Ordered/Tuple.lean) gives the arbitrary-base
     lexicographic rank bijection and exact first-difference order, reusing the existing
     colexicographic index by coordinate reversal.
     [Ordered/TupleInterpretation](Complexity/Logics/FirstOrder/Ordered/TupleInterpretation.lean)
     defines quantifier-free strict/weak order and the canonical full-domain constants, with
     proved unique selection and ranks `0`, `1`, `n^k - 1` for positive dimension.
     **Full-domain successor prerequisite completed (#54):**
     [Ordered/TupleSuccessor](Complexity/Logics/FirstOrder/Ordered/TupleSuccessor.lean)
     proves that the carry formula holds exactly at consecutive arbitrary-base lexicographic
     ranks, with explicit zero-dimension and maximum/no-wrap boundaries. Its generic compiler
     preserves quantifier-freeness when the supplied source successor is quantifier-free.
     The canonical `≤`/BIT instance uses a universal adjacency formula; no unconditional
     quantifier-free successor claim is made for this basis.
     **Canonical addition prerequisite completed (#64):**
     [Ordered/Addition](Complexity/Logics/FirstOrder/Ordered/Addition.lean) defines one native
     formula over `≤` and BIT whose semantics on every `Fin n`, `n ≥ 2`, is exact natural-number
     addition `x + y = z`. Out-of-range sums have no satisfying result; this is not modular
     addition. It formalizes the PLUS part of Immerman's Theorem 1.17(1), using the carry
     characterization of Proposition 1.9.
     **Canonical Bit Sum prerequisite completed (#91):**
     [Ordered/BitSum](Complexity/Logics/FirstOrder/Ordered/BitSum.lean) defines one native
     formula whose semantics on every `Fin n`, `n ≥ 2`, is `y = x.bitIndices.length`, with
     exactly one output for each input. This proves Immerman's Lemma 1.18, historically due to
     Barrington, Immerman and Straubing, using a balanced addition-tree variant of the source's
     packed running-sum proof. Eight bounded words encode all node bits; their native decoder
     uses exact shifts and fixed PLUS chains, with no assumed semantic certificate or variable
     multiplication predicate. A fixed finite disjunction handles small numerals.
     **Canonical multiplication completed (#102):**
     [Ordered/Multiplication](Complexity/Logics/FirstOrder/Ordered/Multiplication.lean) defines
     one native TIMES formula with exact ordinary-product semantics `x * y = z` on every
     canonical `Fin n`, `n ≥ 2`. Every candidate is rejected on overflow. This completes the
     PLUS/TIMES endpoint of Immerman's Theorem 1.17(1), using the proved native Bit Sum and
     a carry-table variant of the source's packed short sums. Eight words store global
     boundary carries; sixteen words store each local block. Both block endpoints agree with
     the global words, all decoders constrain high bits, and the final carry vanishes from the
     input-width bound. The witnesses fit for arbitrary universe sizes; a fixed finite branch
     handles small inputs. No multiplication relation or semantic certificate is assumed.
     **Full-tuple BIT lifting completed (#112):**
     [Ordered/TupleBit](Complexity/Logics/FirstOrder/Ordered/TupleBit.lean) supplies an actual
     native formula for every fixed dimension `k`, with exact `lexRank x`/`lexRank y` BIT
     semantics on every canonical `Fin n`, `n ≥ 2`. It handles arbitrary bases, indices larger
     than the source universe, high-index rejection and explicitly false dimension zero.
     Native affine word arithmetic, multiplication and radix conversion represent the source
     cardinality in seven digits and each tuple rank in `7k` digits. The formula witnesses a
     positive binary radix with its cube below `n`; no out-of-domain scalar or supplied numeric
     certificate is assumed. A fixed finite disjunction covers sizes two through eight.
     This proves the full-domain BIT endpoint of Immerman's Exercise 1.33(3), with no
     formula-size efficiency claim.
     **Numeric-preserving full-tuple composition completed (#121):**
     [Ordered/FullTuple](Complexity/Logics/FirstOrder/Ordered/FullTuple.lean) constructs the
     actual canonical numeric interpretation from the proved native order, BIT and constant
     formulas; clients supply only the target input-relation definitions. For `n ≥ 2` and
     positive dimension `k`, ranking is an isomorphism of the entire ordered language to
     `Fin (n^k)`, including genuine numeric constants, and native pullback preserves every
     formula and sentence. Source input vocabularies may have functions; target input
     vocabularies are relational.
     [Ordered/FullTuple/Composition](Complexity/Logics/FirstOrder/Ordered/FullTuple/Composition.lean)
     composes positive dimensions `k` and `l` with coordinate `(j,i)` mapped to `j*k+i`.
     The proved rank identity compares the flattened base-`n` tuple with the outer base-`n^k`
     tuple of inner ranks. The composite is isomorphic to the successive canonical targets,
     and all formula/sentence pullbacks agree. No full-tuple numeric certificate is assumed.
     This is the full-domain case of Immerman's Proposition 1.28 for relational intermediate
     and output input vocabularies, with Remark 1.32's canonical numerics. It does not identify
     base-`n` digits with binary strings.
     **Native ordered model checking completed (#128):**
     [FirstOrder/Ordered](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean)
     proves that every fixed sentence over a finite relational input vocabulary expanded by
     canonical `0`, `1`, `max`, order and BIT has its actual encoded query language in L.
     Numeric atoms, including quantified ones, use proved native expressions; the input retains
     unary cardinality and the existing framed input tables in `tupleIndex` order. Invalid table
     shapes and sizes zero/one reject. Work space is logarithmic in the full encoded input length,
     with no combined-complexity or arbitrary-raw-word claim. This is the relational-input case
     of Immerman's Theorem 3.1. The original order-free empty-universe behavior is preserved.
     **Canonical full-tuple interpretation transducer completed (#137):**
     [Ordered/FullTuple/Encoding](Complexity/Logics/FirstOrder/Ordered/FullTuple/Encoding.lean)
     and
     [FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean)
     prove that every fixed canonical full-tuple interpretation between finite relational
     input vocabularies computes its encoded target structure in logarithmic space. Admissible
     sources of size `n ≥ 2` map to the canonical rank universe `Fin (n^k)` numbered by
     `lexRank`, serializing only the target input relations in `tupleIndex` order; invalid
     shapes and sizes zero and one map to a fixed malformed target outside every target query
     language. For positive dimension `k > 0`, the decoded target with its own canonical
     numerics is isomorphic to the interpreted full ordered structure preserving every
     natural rank, and `encodedMap` is a logspace many-one reduction from the pulled-back
     ordered query language to the target ordered query language. This is the full-domain
     canonical transducer of Immerman's Proposition 3.5; restricted domains and class-level
     closure are now covered by the #309 entry below. Projections and NL/P completeness remain
     open.
     **Ordered NP-to-ESO converse recovered (#173):**
     [Fagin/Ordered](Complexity/Computability/Complexity/Fagin/Ordered.lean) defines every
     arbitrary ordered query whose source-only encoding language is in NP by one ESO sentence
     over the current canonical language. It retains the fixed `Fin n` order, requires `n ≥ 2`,
     rejects malformed source tables, and imposes no permutation-invariance hypothesis.
     The existing strict-verifier/tableau construction is reused through a shared power-sentence
     lemma; the order-free characterization is unchanged. The ordered ESO-to-NP direction
     remains open.
     **Next milestones:** projections and NL/P completeness. These remain open.
     The full-domain hypothesis matters: the paragraph after Exercise 1.33 warns that canonical
     BIT on an arbitrary definable restricted domain need not be first-order definable.
     Restricted-domain numeric preservation therefore requires its own explicit definitions
     and certificate.
     **Ordered `≤_fo` with domain formulas (#309, semantic layer):**
     [Ordered/DomainInterpretation](Complexity/Logics/FirstOrder/Ordered/DomainInterpretation.lean)
     maps a source to the tuples satisfying a domain formula, renumbered by lexicographic rank
     (admissible when every source has at least two such tuples, the library's convention after
     Proviso 1.15); its
     [Encoding](Complexity/Logics/FirstOrder/Ordered/DomainInterpretation/Encoding.lean) gives
     `encodedMap`, partial decoding `decode?` and the commutation lemma consumed by
     `ManyOneReducibleBy.lift`. A numeric
     [Certificate](Complexity/Logics/FirstOrder/Ordered/DomainInterpretation/Certificate.lean)
     defines the target order, BIT and constants on domain tuples (Immerman's Remark 1.32
     requirement), yielding sentence pullback;
     [Composition](Complexity/Logics/FirstOrder/Ordered/DomainInterpretation/Composition.lean)
     pulls outer certificates back through inner ones, and
     [Ordered/Reduction](Complexity/Logics/FirstOrder/Ordered/Reduction.lean) defines
     `Ordered.Reduces` with `refl`, `trans`, `compl` and `Definable.of_reduces`.
     [FullTuple/DomainInterpretation](Complexity/Logics/FirstOrder/Ordered/FullTuple/DomainInterpretation.lean)
     embeds full-tuple interpretations with their native certificate and proves the encoded maps
     agree. **First-order reductions are logspace reductions (#309):** one domain-counting
     [transducer](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Transducer.lean),
     parametrized by the formula compiler, computes order-free interpretations and
     [ordered interpretations with a domain formula](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean)
     in logarithmic space; the full-tuple transducer is its `domain = ⊤` instance.
     `DomainInterpretation.logSpaceReducible` needs no certificate, and
     `Ordered.Reduces.logSpaceReducible` gives `≤_fo ⇒ ≤_log` with L/P closure (Immerman's
     Proposition 3.10). Open: certificates for further restricted-domain families.
     **Many-one core (#309, #314):** `PolyTimeReducible`, `LogSpaceReducible`,
     `Ordered.Reduces`, `MappingReducible` and `FPTReducible` are instances of
     [ManyOneReducibleBy](Complexity/Computability/Complexity/Reduction/ManyOne.lean), and
     polynomial-time, logspace, `#P` (`SharpPHard`/`SharpPComplete`), search
     (`SearchHard`/`SearchComplete`) and promise (`PromiseProblem.NPHard`) hardness/completeness
     are instances of polymorphic `HardUnder` and `CompleteUnder`; only structurally distinct
     reductions (`FO.Reduces`/`QFReduces`/`ReducesNontrivial`, two-condition promise
     `PolyTimeReducible`, and `ParsimoniousReducible` on `α → ℕ`) remain outside
     `ManyOneReducibleBy`. A witness-carrying reduction structure is deferred until a client
     needs one (e.g. size bounds for Cook–Levin).

   - [x] **Order-free SAT reductions.** [SAT completeness](Complexity/Computability/Complexity/Fagin/SAT.lean)
     is proved for isomorphism-closed classes in NP containing every empty structure, with a
     nonempty-input variant. Order-free 3SAT and 3COL are interreducible; SAT reduces to
     independent set on universes of at least two elements, and independent set, clique and
     vertex cover are ESO-definable. The singleton obstruction to unrestricted SAT-to-independent-set
     reducibility is proved. SAT-to-3SAT, graph-property hardness in this framework, and bridges
     to the separately encoded problems remain outstanding. These are order-free variants;
     the standard ordered completeness statements above remain open.

   - [ ] **FO reductions and projections.** The vocabulary-parametric, relativized core is
     implemented in [ProjectionFormula](Complexity/Logics/FirstOrder/ProjectionFormula.lean) and
     [Projection](Complexity/Logics/FirstOrder/Projection.lean): selection of one literal before
     quantifying over input structures, mutually exclusive numeric cases, truth-preserving
     substitution, identity/composition isomorphisms, and quantifier-free composition. The
     [graph-complement client](Complexity/Logics/FirstOrder/Projection/Graph.lean) and tests cover
     nonvacuity, empty universes, nullary relations and the failure of two-bit conjunction to be
     a projection. Quantifier-free reducibility
     ([QFReduces](Complexity/Logics/FirstOrder/Reduction/QuantifierFree.lean)), full-domain tuple
     interpretations ([Interpretation/Tuple](Complexity/Logics/FirstOrder/Interpretation/Tuple.lean))
     and the tactics `fo_qf`, `fo_iso_closed`, `fo_simp` and `fo_reduction`
     ([Tactic/FirstOrder](Complexity/Tactic/FirstOrder.lean)) are implemented, simplifying
     composite and higher-dimensional interpretations and composite projections, with independent
     set, clique and vertex cover as quantifier-free reducible
     [structure classes](Complexity/Logics/FirstOrder/Problems/SizedGraph.lean).
     **Still outstanding:** the classical positive-dimensional full-universe
     specialization and canonical numeric preservation, projection reducibility on finite
     structure classes, and the standard ordered machine encoding bridge. Reuse
     [FO.Interpretation](Complexity/Logics/FirstOrder/Interpretation.lean) and
     [FO.Reduces](Complexity/Logics/FirstOrder/Reduction.lean) for the semantic interfaces. State
     the canonical order/`BIT` convention on `Fin n` explicitly; the classical qfp convention
     excludes BIT ([Immerman–Landau, Definition 3.6](https://people.cs.umass.edu/~immerman/pub/mult.pdf)).
     Arbitrary quantifier-free Boolean combinations of input relations are not projections.
     [First-order model checking in L](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder.lean)
     is proved for relational FO without order or BIT, and
     [canonical ordered model checking](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered.lean)
     now includes genuine numeric constants, order and BIT for source sizes at least two.

   - [x] **Order-free interpretations as logspace reductions.** The
     [machine-certified transducer](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Reduction.lean)
     streams interpreted relation tables using tuple ranks. Every order-free interpretation
     reduction to an isomorphism-closed target induces a logspace many-one reduction of encoded
     query languages, with L/P closure. Empty universes and domains, nullary relations,
     dimension zero, and invalid parsed table shapes are handled. Canonical full-tuple ordered
     interpretations, with or without a domain formula, are instances of the same
     [transducer](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Transducer.lean),
     and ordered first-order reductions are logspace reductions
     ([FirstOrder/Ordered/Reduction](Complexity/Computability/Complexity/Classes/LogSpace/FirstOrder/Ordered/Reduction.lean), #309).

   - [x] **Circuit Value logspace completeness.** [Circuit Value is P-complete](Complexity/Computability/Complexity/Problems/CircuitValue/Completeness.lean)
     under logarithmic-space many-one reductions, via a machine-certified tableau writer.
     The theorem covers every injective instance encoding and implies membership in L exactly
     when P equals L for every encoding. Work space excludes read-only input and write-only
     output, and correctness is required on encoded instances.

   - [x] **Monotone Circuit Value logspace completeness.**
     [Monotone Circuit Value is P-complete](Complexity/Computability/Complexity/Problems/MonotoneCircuitValue/Completeness.lean)
     under logarithmic-space many-one reductions, using a dual-rail tableau and a shared
     streaming writer. General Circuit Value reduces to it. No planarity restriction or
     first-order completeness theorem is established by this construction.

   - [ ] **Circuit Value completeness under first-order reductions.** Prove P-hardness under
     the standard ordered reduction via `REACHa → MCVP → CVP`, following
     [Immerman, Chapter 3, Theorem 3.26 and Exercise 3.28](https://people.cs.umass.edu/~immerman/book/ch3.pdf).
     Supply the alternating-logspace simulation of polynomial-time machines and the translation
     from relational circuits to `encCircuitValue`. The logspace tableau theorem above does not
     supply this stronger reduction or the ordered relational-to-machine encoding bridge.

   - [ ] **Uniform circuit families.** The current
     [NC/AC/TC hierarchies](Complexity/Computability/Circuit/Boolean/DepthClasses.lean),
     [ACⁱ[q] ⊆ TCⁱ](Complexity/Computability/Circuit/Boolean/ModMajority.lean) and
     [carry-save threshold/majority simulation in NC¹ and NCⁱ⁺¹](Complexity/Computability/Circuit/Boolean/ThresholdNC1.lean)
     (for polynomially fan-in-bounded threshold and majority circuits; eliminating unbounded
     repeated-wire multiplicities in unrestricted `TCⁱ` requires Muroga's threshold
     weight-bounding theorem) are
     nonuniform, and [FO model checking in AC⁰](Complexity/Computability/Circuit/Boolean/FirstOrder.lean)
     constructs nonuniform circuits over relational atomic inputs, without order/`BIT`.
     [Polynomial-time function-family compilation](Complexity/Computability/Complexity/Problems/CircuitValue/Compilation.lean)
     now certifies construction of circuit codes from encoded instances, with separately
     prescribed unary input/output widths. Its proof reuses the uniform tableau writer,
     prefix hardwiring and shared-input circuit composition; it establishes no depth bound.
     The [carry-lookahead adder](Complexity/Computability/Circuit/Boolean/CarryLookahead.lean)
     computes exact unsigned addition with carry-in and carry-out at every width, including zero.
     Its depth is at most `7 + 2*ceil(log₂(w+1))`, with polynomial size and every gate charged.
     The modular version has depth at most `8 + 2*ceil(log₂(w+1))`; a carry-save finishing client
     preserves the existing 4-to-2 reducer's value modulo `2^w` and clears its second word.
     The [native generators](Complexity/Computability/Circuit/Boolean/CarryLookahead/PolyTime.lean)
     construct the complete binary gate/output codes from unary width, reusing fixed formula
     templates and shared-input code assembly. This establishes polynomial-time uniformity for
     these arithmetic circuits. The complete GSW shallow-decryption circuit and native constructor
     are described above; stronger logspace and DLOGTIME uniformity remain open.
     Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and
     input encodings. Certify circuit generation and evaluation and the relevant machine-to-
     circuit simulations, preserving size, depth and construction-resource bounds. Prove
     FO with order and `BIT` equals DLOGTIME-uniform AC⁰ under explicit input-access and encoding
     conventions; an unqualified
     nonuniform class definition or simulation is insufficient.

   - [ ] **Counting-machine characterizations.** The current
     [#P/GapP definitions](Complexity/Computability/Complexity/Classes/SharpP.lean) use verifier
     witness counts and differences of such counts. The
     [occurrence-labelled terminal branch semantics](Complexity/Computability/Machines/Turing/MultiTape/Counting.lean)
     and [canonical index-certificate bijection](Complexity/Computability/Machines/Turing/MultiTape/Counting/Certificate.lean)
     now preserve accepting and rejecting counts separately, including equal-effect choices and
     early halting. Increasing a sufficient all-branches clock preserves the counts; the time
     predicate explicitly excludes stuck states (#93). The
     [actual binary checker](Complexity/Computability/Machines/Turing/MultiTape/Counting/Checker.lean)
     now has a tidy polynomial-time proof through existing finite storage and the loop calculus.
     Its exact binary/index correspondence proves
     [both terminal counts in #P and their difference in GapP](Complexity/Computability/Complexity/Classes/SharpP/Machine.lean)
     for every polynomial clock (#92). With fixed finite control, a fixed number of tapes and
     Boolean alphabet, the certificate length is `b * p(|enc a|)` for a machine-dependent fixed
     width `b > 0`; invalid codes contribute to neither verdict. This counts only branches
     halted by the clock. `HaltsWithin` additionally supplies full termination without stuck
     branches. Runtime is polynomial in the input/certificate pair, with the machine fixed,
     not uniform in a supplied machine description.
     The [binary-guess scanner](Complexity/Computability/Machines/Turing/MultiTape/Counting/Guess.lean)
     supplies one terminal branch per Boolean word of the input length, with an exact `n + 1`
     clock and singleton halt. Its shared FreeM/List execution preserves each word's multiplicity.
     The [List/native execution bridge](Complexity/Computability/Machines/Turing/MultiTape/Counting/Execution.lean),
     [singleton deterministic lift](Complexity/Computability/Machines/Turing/MultiTape/Counting/Deterministic.lean)
     and [shared-tape sequencing laws](Complexity/Computability/Machines/Turing/MultiTape/Counting/Sequential.lean)
     now preserve exact occurrence multiplicities and add actual all-branches clocks (#110).
     The sequencing bound explicitly assumes nonempty transition lists at every local view;
     the actual scanner and singleton lift satisfy this condition. This is shared-tape
     sequencing, without preparing or resetting a continuation's input. The
     [closed buffered compiler](Complexity/Computability/Machines/Turing/MultiTape/Counting/Composition.lean)
     now feeds each source output to a consumer with separately reserved blank work tapes,
     retaining source scratch and the real input head (#113). Output redirection emits into
     the buffer in each source transition; singleton deterministic preparation rewinds and
     marks it in `word.length + 4` transitions, including the empty word. Exact full-configuration
     and native count laws preserve every List occurrence. From initialized empty output,
     nonblocking components with clocks `T₀` and `T₁` have native composite clock
     `T₀ + (T₀ + 4 + T₁)`; the consumer bound must hold for every produced word.
     The [actual guess-and-verify pipeline](Complexity/Computability/Machines/Turing/MultiTape/Counting/Verifier.lean)
     now computes the witness length in unary, generates each witness once, retains the framed
     instance, and runs the singleton-lifted tidy verifier (#116). Its fixed finite machine has
     a polynomial all-branches clock in the original encoded input length, including framing,
     both buffers and workspace restoration. The output List retains one occurrence per witness,
     even when Boolean outcomes coincide. The
     [#P characterization](Complexity/Computability/Complexity/Classes/SharpP/Characterization.lean)
     combines this construction with the forward checker and preserves accepting and rejecting
     counts separately. All constructed transition tables are globally nonblocking; the halting
     contract is on encoded instances, hence all binary inputs when the encoding is `encBits`.
     The [signed construction and GapP characterization](Complexity/Computability/Complexity/Classes/SharpP/GapMachine.lean)
     now realize every difference of two #P counts by one native machine (#120, completing the
     endpoint of #106). The [one-step verdict router](Complexity/Computability/Machines/Turing/MultiTape/Counting/Verdict.lean)
     gives a successful witness one chosen-sign leaf and an unsuccessful witness one accepting
     plus one rejecting leaf. A [two-occurrence selector](Complexity/Computability/Machines/Turing/MultiTape/Counting/Alternative.lean)
     adds independently prepared families, with disjoint reserved work tapes and their original,
     possibly unequal witness lengths. Routing a verifier of clock `T` costs `T + (T + 4 + 1)`;
     combining routed clocks `S₊, S₋` costs `S₊ + S₋ + 1`. Extra clock time uses first-halt stability,
     not extra choices. Zero, odd and negative gaps are included, with no oracle channels or
     input-dependent machine advice.
     The [UP](Complexity/Computability/Complexity/Classes/UP/Machine.lean) and
     [FewP](Complexity/Computability/Complexity/Classes/FewP/Machine.lean) native iff endpoints
     now transport their accepting-count bounds through the actual parsimonious #P bridge (#131).
     Fixed finite parameters and a polynomial all-branches clock precede every encoded input;
     the ambiguity bound is one for UP and a separate polynomial in encoded input length for
     FewP. Rejecting and total branch counts are not bounded by the ambiguity polynomial.
     Duplicate accepting occurrences remain distinct, while first-halt clock padding preserves
     their multiplicities.
     [Native oracle occurrence replay](Complexity/Computability/Machines/Turing/MultiTape/Counting/Oracle/Replay.lean)
     now gives exact ordered equality between the shared FreeM run and canonical fixed-clock
     index certificates (#136), under an explicit positive uniform local-list length bound.
     It retains consumed indices, complete configurations and branch-local private oracle state;
     live cutoffs are retained, with terminal filtering and both verdict counts proved separately.
     Trace erasure recovers the ordinary shared interpretation, and the Empty-channel cases
     recover raw closed List execution and the existing terminal certificate decoder.
     This is semantic replay, without a nonblocking or halting hypothesis. A later oracle clock
     contract must be nonvacuous and uniform over admissible handlers; the generic total-PMF
     predicate cannot be instantiated blindly at an occurrence interface containing `Fin 0`.
     Closed counting clocks and characterizations are unaffected. Efficient encoded oracle
     checking, response-access costs, and native oracle-machine characterizations remain open;
     resource bounds must be uniform over admissible oracles, while correctness may specialize
     to one fixed language oracle.

2. **Complete theorem ports using the existing certificate APIs.** Extend automation when a
   concrete port is blocked or several clients repeat the same proof burden. Constructor, projection,
   lookup and composition rules should infer encodings for ordinary functional expressions.
   Test equivalent spellings and alternative encodings before adding tactic cases. Generalize
   reusable list, bounded-table, cache and nested-loop invariants where clients need them;
   callers supply the meaningful invariant, and automation handles routine encoding arithmetic.
   Use Cook–Levin and GGM as demanding regression clients. General open-program composition
   remains separate from the implemented
   [closed stateful substitution](Complexity/Computability/Probabilistic/OracleSimulation.lean).
   Extend quantitative certificates to retain separate time, workspace and output-size bounds
   through composition. Apply cumulative streaming contracts to captured iteration and nested
   loops, discharging routine encoding arithmetic automatically. Certify PRG stretching with
   seed length, round count and generator cost kept separate.

3. **Practical PCP and expander constructions.** The
   [PCP theorem](Complexity/Computability/PCP/Completeness.lean) includes certified construction
   and verification, but the fixed parameters are enormous. Develop a reasonably runnable
   construction and measure complete reductions. The
   [six-query tester](Complexity/Computability/PCP/SelectedComposition.lean) now feeds the shared
   executable composition compiler and the full reduction, with a 128-symbol output alphabet and
   a certified amplification gap of `2^-61`. The final binary verifier also encodes labels and
   repeats its check, so it does not have a six-query bound. The existing rotation certificate is
   polynomial in the number of vertices; polynomial time in the bit length of a vertex name
   remains a stronger, separate target. The [expander-walk hitting bound](Complexity/Foundations/Combinatorics/Expander/Hitting.lean)
   now gives a finite probability estimate for avoiding sets, including changing sets along the
   walk. Derive machine-level error reduction and extractor guarantees with certified seed and
   evaluation costs; the hitting estimate alone does not supply those algorithms.

4. **Reduce repeated proof bookkeeping.** Improve configuration views, tape partitions, handoff
   identities and preservation rules when they simplify multiple clients. Keep simplification
   narrowly oriented and machine transitions out of global simp. Share mathematical bookkeeping
   only with demonstrated reuse, counting helper proofs as part of the total cost.

5. **Curated formal abstracts and PDFs.** The selection in
   [abstracts/catalogue.json](abstracts/catalogue.json) replaces the former paper/TeX index.
   Each promoted group has a checked Abstract/Bridge pair, explicit model and scope notes, and
   a generated individual PDF. Selection requires a substantial full endpoint rather than broad
   coverage of every library theorem. Continue to improve readability and independently compare
   changed abstracts with their final source statements. `#check_abstract` inspects elaborated
   dependencies; notation, macros and local instances are excluded by the skill's rules rather
   than mechanically. Generated PDFs are review and dissemination artifacts, not additional proofs.

6. **Plain computability in definitions and public results (#456).** Plain
   `ComputableInPolyTime` and its tidy bridges are in place, together with plain space, big-O and
   FPT notions (#551). `P`, `NP`, `FNP` and the polynomial-time reductions (#546), the
   probabilistic, counting and hierarchy classes (#547), the `TFNP` subclasses (#548), FPT
   reductions, kernels and proof systems (#549) and the cryptographic primitives (#550, including
   deterministic families in commitment hiding and zero-knowledge) use it, and the WPP/LWPP
   robustness results expose plain certificates (#562). Remaining: isolating tidy computability
   to proofs everywhere, by mechanically mirroring the calculus in plain form (#608), sweeping
   the remaining public tidy statements and guarding the result in CI (#456), and switching the
   abstract bridges to the shared predicate.

## Remaining theorem developments

The port still includes substantial mathematical developments beyond the completed reference
results. Track these by their public theorems, rather than by source-file counts.
Jukna coverage below is an additional target beyond the V1 port:

* **Real-algebraic decision procedures.** The [sign-query counting identity](Complexity/Foundations/Data/Polynomial/SignQueries.lean)
  expresses scaled finite sign-pattern counts through integer product-sign queries, including
  distinct real roots. Porting the Sturm–Tarski query evaluator, native space certificates and
  ETR upper bound from [lean-canny](https://github.com/SamuelSchlesinger/lean-canny) remains open.
* **Mass-production constructor runtime.** Certify runtime separately from the native gate-cost
  bounds in [Uhlig](Complexity/Computability/Circuit/Boolean/MassProduction/Uhlig.lean) and
  [fine mass production](Complexity/Computability/Circuit/Boolean/MassProduction/Fine.lean).
  The current constructions choose information sets and line menus nonconstructively.
* **Iterated-function circuits.** Port the
  [existing Lean development](https://github.com/SamuelSchlesinger/iterating-functions/blob/main/lean/README.md):
  input-time and batched iteration, navigation and hitting times, sparse-counter and
  affine-controller bounds, and hard-power counting. It already uses CSLib
  circuits and some mass-production infrastructure. The
  [functional-graph foundations](Complexity/Foundations/Combinatorics/FunctionalGraph.lean)
  (transient and cycle structure, checkpoint packing, exact distinct-power counts,
  [cycle-spectrum reduction and canonical hitting-time identities](Complexity/Foundations/Combinatorics/FunctionalGraph/Spectrum.lean),
  [min-max duality for required paths in in-forests](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestDuality.lean),
  [semantic correctness of the six-step distinguished-point procedure](Complexity/Foundations/Combinatorics/FunctionalGraph/DistinguishedPoints.lean),
  [checkpoint forests](Complexity/Foundations/Combinatorics/FunctionalGraph/CheckpointForest.lean),
  [interval labels](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestIntervals.lean),
  [compressed segments](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestSegments.lean)
  and [compressed-forest navigation](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestNavigation.lean)) and
  [native circuit iteration](Complexity/Computability/Circuit/Iteration.lean) with retained
  orbits are in place, as are the [fixed-power theorem](Complexity/Computability/Circuit/Boolean/Iteration.lean),
  its encoded and burn-in forms, the optimized square-root bounds and permutation inversion; the
  [input-time](Complexity/Computability/Circuit/Boolean/Iteration/InputTime.lean) and
  [batched iteration](Complexity/Computability/Circuit/Boolean/Iteration/Batch.lean), cycle labels,
  transient depths, additive long-time bounds,
  [compressed-forest reachability](Complexity/Computability/Circuit/Boolean/Iteration/ForestCircuits.lean),
  [hitting-time navigation](Complexity/Computability/Circuit/Boolean/Iteration/NavigationCircuits.lean),
  [complete visit-schedule circuits](Complexity/Computability/Circuit/Boolean/Iteration/VisitScheduleCircuits.lean),
  [sparse-counter navigation, visit schedules and hitting-time bounds](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean),
  [autonomous-controller / affine-payload iteration bounds](Complexity/Computability/Circuit/Boolean/Iteration/AffineController.lean),
  [universal-map simulation and hardwiring](Complexity/Computability/Circuit/Boolean/Iteration/UniversalMap.lean),
  [in-place multi-head machine bounds](Complexity/Computability/Circuit/Boolean/Iteration/InPlace.lean),
  [sequential-squaring exponent reduction](Complexity/Computability/Circuit/Boolean/Iteration/SequentialSquaring.lean),
  [hard-power counting, modular-counter lower bounds, and prime-cycle permutations](Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter.lean),
  and [batched modular-counter upper and lower bounds](Complexity/Computability/Circuit/Boolean/Iteration/CounterBatch.lean)
  are also implemented. Nonuniform circuit
  existence does not certify the preprocessing algorithm's runtime.
* **Rational hitting-list runtime.** The [rational-matrix hitting lists](Complexity/Computability/Circuit/Rational.lean)
  are ported, and the complete polynomial-time generator runtime is proved:
  [generator parameter certificates](Complexity/Computability/Circuit/Rational/Runtime/Parameters.lean),
  [binary integer arithmetic](Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Int/Binary.lean),
  polynomial-time staged division-free integer determinant `detRows_polytime`
  ([Runtime/Determinant](Complexity/Computability/Circuit/Rational/Runtime/Determinant.lean)),
  [binary division and remainder](Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/BinaryDiv.lean)
  (`binary_divMod`, `binary_div`, `binary_mod`),
  [Euclidean GCD](Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Gcd.lean)
  (`binary_gcd`),
  [canonical natural and reduced-rational encoding certificates](Complexity/Computability/Circuit/Rational/Runtime/Encode.lean)
  (`encodeNat_polytime`, `encodeDivInt_polytime`),
  [integer lift tables](Complexity/Computability/Circuit/Rational/Runtime/Lift.lean)
  (`liftRows_polytime`),
  [per-point Cramer normalization and tuple encoding](Complexity/Computability/Circuit/Rational/Runtime/Point.lean)
  (`pointWord_polytime`), and
  [grid enumeration, unary input parsing, and the standalone generator](Complexity/Computability/Circuit/Rational/Runtime.lean)
  (`hittingList_polytime`, `hittingGenerator_polytime`, `hittingGenerator_spec`), charging all
  arithmetic and storage growth. Polynomial bit complexity of formula evaluation on the emitted
  matrices remains separate.
* **Explicit frontier extractor.** Port v1's explicit sumset-extractor construction
  (`Complexitylib/Algebraic/LowerBound/Cutwidth/Extractor`) together with its instantiation:
  an explicit family in `Complexity.P encBits` that discharges the hypotheses of the worst-case or
  average-case [frontier lower bounds](Complexity/Computability/Circuit/Frontier/FanInTwo.lean).
  Such a port needs an independent correctness review of the frontier core, since it would exceed
  the library's unconditional `3.5 N - o(N)` bound in `P`
  (`AffineDisperser.exists_mem_P_eventually_le_size`). The earlier conditional sumset-extractor
  layer was withdrawn (#391).
* **Weighted threshold representations.** Complete the remaining results in
  [Threshold Circuits as Decision Trees and Finite-State Programs](https://github.com/SamuelSchlesinger/threshold-circuits).
  The [separable and bi-monotone comparison tree rectangle bounds](Complexity/Computability/DecisionTree/Separable.lean),
  [decision-tree node-count, rank, decision-list, and energy bounds for inner product](Complexity/Computability/DecisionTree/InnerProduct.lean),
  exact [inner-product and rectangle-density activity bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/InnerProduct.lean)
  (including [shifted-baseline activity](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activity.lean)
  and [decision-tree affine leaf scores](Complexity/Computability/DecisionTree/AffineScore.lean)),
  [native scalar-capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/CapacityCircuit.lean)
  (including the single-direction, direction-run, and multilevel threshold capacity corollaries),
  [mixed-activation capacity bound](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Activation.lean),
  [median-cut rectangle and cut bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Cut.lean),
  [fan-in-two component and block-excess bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Components.lean),
  [direction-menu capacity bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Menus.lean)
  (including bounded internal fan-in and bounded integer internal-weight corollaries),
  [pending-bias state simulation and input-summary / phased-cut lower bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/PendingBias.lean),
  [scalar query-activity run capacity and Cover enumerative coding bounds](Complexity/Computability/Circuit/Boolean/WeightedThreshold/ScalarActivity.lean),
  and [unambiguous transcript cells and quadratic-potential unique-sink representations](Complexity/Computability/Circuit/Boolean/WeightedThreshold/Potential.lean)
  are proved. Port v1's explicit source-reduction family.
  Further manuscript work includes universal scalar circuit synthesis,
  entropy and asymptotic activity bounds, and geometric cutting.

* **Worst-case hardness and derandomization.** The
  [worst-case-hardness implication P = BPP](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean)
  is proved for hardness at all large lengths, by the Sudan–Trevisan–Vadhan encoding and
  Nisan–Wigderson. Remaining: the infinitely-often variant and the EXP ⊄ P/poly endpoint of
  Babai, Fortnow, Nisan and Wigderson.
* **Further PCP consequences.** Constant-factor NP-hardness of approximating Independent Set,
  Clique and Vertex Cover is [proved](Complexity/Computability/PCP/Approximation/IndependentSet.lean)
  via Karp's occurrence graph. Build the FGLSS clique-hardness reduction and amplification on the existing
  [gap-preserving reductions](Complexity/Computability/Complexity/Classes/Promise/Reduction.lean) and certified PCP
  construction; retain the exact gap and reduction runtime.
* **Randomized communication and information.** The `Ω(n)` bounded-error randomized disjointness
  lower bound is [proved](Complexity/Computability/Communication/Disjointness.lean); Raz–Wigderson's
  monotone depth bound is [proved](Complexity/Computability/Circuit/Monotone/BipartiteMatching.lean)
  for bipartite matching (general graphs remain). Develop
  information complexity and its reductions to streaming and sketching lower bounds.
* **List decoding.** Extend [Sudan's Reed–Solomon list-decoding theorem](Complexity/Foundations/Data/Code/Sudan.lean)
  to Guruswami–Sudan list decoding. Keep interpolation, list-size/agreement guarantees and
  uniform decoding runtime as separate obligations.
* **Hypercontractivity and formula lower bounds.** KKL, Talagrand's inequality and Friedgut's junta
  theorem are [proved](Complexity/Foundations/BooleanAnalysis/KahnKalaiLinial.lean). Extend the existing
  [hypercontractivity results for p ≤ 2 ≤ q](Complexity/Foundations/BooleanAnalysis/Hypercontractivity.lean)
  and their Boolean-analysis applications. Continue formula lower bounds beyond the existing
  [Khrapchenko bound](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean),
  [Subbotovskaya shrinkage](Complexity/Computability/Circuit/Boolean/Formula/Subbotovskaya.lean) and
  [Andreev's `n^(5/2 - o(1))` lower bound](Complexity/Computability/Circuit/Boolean/Formula/Andreev.lean),
  following the Jukna coverage below.
* **Search and parameterized complexity.** [FNP, FP and TFNP](Complexity/Computability/Complexity/Classes/TFNP.lean)
  are defined with polynomial-time search reductions, `FP = FNP` exactly when `P = NP` is
  [proved](Complexity/Computability/Complexity/Classes/TFNP/SearchToDecision.lean), and `TFNP ⊆ FP`
  implies `NP ∩ coNP ⊆ P`. PLS, PPP, PPAD and PPA and their
  [canonical complete circuit problems](Complexity/Computability/Complexity/Classes/TFNP/Subclasses/Completeness.lean)
  are proved (#151, #168). Develop CLS and further complete search problems. Building on
  [FPT, XP and fpt-reductions](Complexity/Computability/Complexity/Parameterized.lean), the
  kernelization characterization of FPT, a bounded-search-tree algorithm for vertex cover (#152),
  and [Buss's polynomial kernel for vertex cover](Complexity/Computability/Complexity/Parameterized/VertexCover/BussKernel.lean)
  (#270) are proved; develop strongly uniform variants and the W hierarchy.
  The long-term coverage table identifies the broader class families.
* **Universal hashing (#640, track D).** Proved (#663): one definition each of
  [`ε`-universal and `ε`-Δ-universal](Complexity/Probability/HashFamily.lean) families;
  pairwise independent families are
  [universal and Δ-universal](Complexity/Probability/PairwiseIndependentHash/Universal.lean), the
  Boolean-matrix and subset-sum families are Δ-universal, and the
  [Carter–Wegman polynomial](Complexity/Probability/HashFamily/Polynomial.lean) and
  [multiply-shift](Complexity/Probability/HashFamily/MultiplyShift.lean) families are proved.
  [Feistel networks and the Luby–Rackoff theorem](Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean)
  (#748, #834, Boneh–Shoup Section 4.4 / Luby–Rackoff 1988), backed by the shared
  [lazy bidirectional random-permutation sampler](Complexity/Languages/Probabilistic/RandomPermutation.lean)
  (#834), prove the `Q.choose 2 * ε + Q.choose 2 / |G|`
  3-round adaptive CPA bound with Δ-universal Round 1
  (`advantage_feistel3HashIdealGame_randomFunctionGame_le`), the `2 * Q.choose 2 / |G|`
  uniform-random-round corollary (`advantage_feistel3RandomRoundsGame_randomFunctionGame_le`), the
  3-round and 4-round PRF-to-Feistel hybrid bounds
  (`advantage_feistel3KeyedGame_randomFunctionGame_le`,
  `advantage_feistel4StrongKeyedGame_feistel4StrongRandomRoundsGame_le`), the PRP-PRF switching
  bound `Q.choose 2 / |G|²` and 3-round PRP bounds against a uniform random permutation
  (`advantage_idealPermGame_randomFunctionGame_le`,
  `advantage_feistel3RandomRoundsGame_idealPermGame_le`,
  `advantage_feistel3KeyedGame_idealPermGame_le`), and the 3-query
  chosen-ciphertext attack against 3-round Feistel (`eval_feistel3_feistel3CCAAttack`, with the
  equal-input sanity check `advantage_feistel3CCAAttack_self`, the finite positive gap
  `(|Equiv.Perm (G × G)|)⁻¹ ≤ advantage` against the true bidirectional random-permutation game
  `idealStrongGame` for `|G| ≥ 3` in `le_advantage_feistel3CCAAttack_idealStrongGame`, the
  quantitative nonnegligible lower bound `1 - |G|⁻¹ - 4 / |G|² ≤ advantage` against
  `idealStrongGame` for any `l₀ ≠ l₁` in `le_advantage_feistel3CCAAttack_idealStrongGame_of_ne`,
  and the separate exact `1 - |G|⁻¹` bound against the independent-table benchmark
  `independentTableStrongGame` in `advantage_feistel3CCAAttack_independentTable`). Open in #748:
  the 4-round information-theoretic bidirectional random-round collision bound.
  Open: the leftover hash lemma stated over `ε`-universal families, with `IsTwoUniversal` as its
  `1 / |Y|` case and the pseudoentropy clients updated.
* **Sigma protocols, Schnorr identification and Fiat–Shamir (#581).** Boneh–Shoup Chapter 19.
  The exact algebraic core is proved:
  [Sigma protocols](Complexity/Crypto/Protocols/SigmaProtocol/Basic.lean) with explicit
  extractors and perfect simulators, the
  [linear-preimage protocol](Complexity/Crypto/Protocols/SigmaProtocol/Linear.lean) over prime
  order `q` with Schnorr, Okamoto, Chaum–Pedersen and linear systems as instances, and
  [AND/OR composition](Complexity/Crypto/Protocols/SigmaProtocol/Composition.lean). The exact
  [rewinding lemma](Complexity/Probability/Rewinding.lean), the extraction bound
  `ε ≤ 1/N + √ε'` and HVZK ⇒ eavesdropping security are proved for
  [identification from Sigma protocols](Complexity/Crypto/Protocols/SigmaProtocol/Identification.lean)
  and [Schnorr identification](Complexity/Crypto/Protocols/SigmaProtocol/SchnorrIdentification.lean).
  The [discrete-log assumption](Complexity/Crypto/Computational/DiscreteLog.lean) is stated for
  a family of prime-order groups with plain polynomial-time operations, instantiated by
  [Schnorr groups](Complexity/Crypto/Computational/DiscreteLog/SchnorrGroup.lean), and
  [Schnorr identification](Complexity/Crypto/Computational/SchnorrIdentification.lean) is secure
  against direct attacks by uniform strict PPT impersonators under it. The general
  [forking lemma](Complexity/Probability/Forking.lean) (Bellare–Neven) is proved, also for
  [oracle programs](Complexity/Languages/Probabilistic/Forking.lean) with explicit coins and
  presampled answers. [Fiat–Shamir signatures](Complexity/Crypto/Protocols/SigmaProtocol/FiatShamir.lean)
  in the [random-oracle model](Complexity/Crypto/Protocols/Signature/RandomOracle.lean) are
  correct and, exactly, EUF-CMA secure with the bound
  `Qs · (Qs + Qro) · δ + (Qro + 1)/N + √((Qro + 1) · ε')` of Theorem 19.16 and Equation 19.21,
  by the
  [difference lemma](Complexity/Languages/Probabilistic/UntilBad.lean), presampling and forking;
  [Schnorr signatures](Complexity/Crypto/Protocols/SigmaProtocol/SchnorrSignature.lean) have
  `1/q`-unpredictable commitments and the exact bound with `δ = 1/q`.
  Open (see #640): computational Schnorr signatures under discrete log for strict PPT forgers,
  and security against eavesdropping in the strict-PPT model, where simulating transcripts needs
  approximately uniform `ZMod q` samples and hence an explicit statistical-distance term.
* **Lattice identification and signatures (#640, track B).** The short-integer-solution
  hypothesis, exact box rejection sampling and Lyubashevsky identification are in review (#660).
  Open: Fiat–Shamir with aborts and signatures from SIS [Lyubashevsky 2009, 2012]; efficiency
  certificates for the identification simulator and extractor; SIS for a general (prime) modulus;
  module SIS and module LWE over polynomial rings, and Dilithium-style signatures as theory, not a
  parameter set or ciphersuite.
* **Zero-knowledge proof systems toward libzk (#643, #640).** The
  [interactive-reduction core](Complexity/Computability/Interactive/Basic.lean) has typed
  public-coin protocols with oracle access to the prover's messages, worlds for the oracle model,
  and named extractors and simulators. It defines completeness, soundness, straight-line knowledge
  soundness, round-by-round soundness and HVZK; knowledge soundness and HVZK are stated in the
  plain model. In the plain model,
  [sequential composition](Complexity/Computability/Interactive/Sequential.lean) is proved for
  completeness, soundness, knowledge soundness and round-by-round soundness, and so is per-stage
  iteration. [Round-by-round soundness implies soundness](Complexity/Computability/Interactive/Plain.lean).
  [Sumcheck with a final evaluation check](Complexity/Computability/Interactive/Sumcheck.lean),
  the first client, is perfectly complete and has soundness error `n · d / |F|`; both follow from
  the one-round theorems by composition. Open, in order:
  - the `PublicCoin → IP` bridge, with a uniform word verifier and adversarial decoding;
  - parallel and AND/OR composition, and round-by-round knowledge soundness;
  - oracle statements. Today a later phase cannot query an earlier phase's oracle message,
    because `Verifier.append` routes the second verifier's queries only to its own messages.
    Sumcheck followed by an evaluation query on a committed polynomial needs this, and so do FRI
    and Ligero. The design item is virtual output oracles, as in ArkLib's
    `OracleOutputSimulation`. Knowledge soundness and zero knowledge in oracle worlds go with it:
    extractors that see the prover's queries, and simulators that program the world;
  - efficiency-certified simulators and extractors, and auxiliary-input zero knowledge (#704)
    on the core;
  - polynomial commitment and evaluation-query reductions, and the Ligero IOP;
  - the BCS transform from public-coin IOPs to non-interactive arguments in the random-oracle
    model;
  - VOLE as an ideal functionality and VOLE-in-the-head;
  - the compositional structure of libzk (Shelat's IETF draft) as a composition of these
    components, stated as theory without concrete ciphersuites.

  The design is on #643, and the TQBF, PCP and GMW bridges are recorded there.
* **Classic symmetric constructions (#640, track D).** Proved: PRF-based MACs (#677), keyed
  collision-resistant hash families and Merkle–Damgård (#678), universal hashing (#663),
  [Carter–Wegman MACs from Δ-universal hashing](Complexity/Crypto/Protocols/MAC/CarterWegman.lean)
  (#736, including one-time, adaptive multi-query issued-counter, arbitrary-pad hybrid, and exact
  single-query fixed-nonce `prfRealGame`/`prfIdealGame` reduction bounds), and the Even–Mansour
  cipher in the ideal-permutation model (algebraic permutations, one-query secrecy, one-sided query
  security, 2-query breaks when omitting either whitening key, the Boneh–Shoup Theorem 4.10
  bad-key transcript intersection bound `2 * Q_e * Q_π / |G|`, exact equivalence of the two-sided
  ideal and fixed-key real games with lazy bidirectional random-permutation samplers in
  `evenMansourIdealGame_eq_lazy` and `realGameForKey_eq_lazy`, the key-shifted lazy permutation
  coupling inequality `run_idealLazyHandler_good_le_realLazyHandler`, and the full two-sided PRP
  `Game.advantage` bounds `2 * Q_e * Q_π / |G|` in
  `advantage_evenMansourRealGame_evenMansourIdealGame_le` and
  `advantage_singleKeyEvenMansourRealGame_evenMansourIdealGame_le`, #761, #834).
  Open: `IsOraclePPT` admissibility, uniform word-level forger/hash families, the asymptotic
  `PseudorandomFunction` corollary, and fresh-nonce multi-query Carter–Wegman MAC security;
  the 4-round strong Feistel information-theoretic collision bound (#748); and the Naor–Reingold
  PRF from the decisional Diffie–Hellman assumption.

* **Lattice Sigma protocols and post-quantum signatures (#640, track B).** Proved (#645): the
  [SIS hypothesis](Complexity/Crypto/Computational/SIS/Basic.lean) for power-of-two moduli, exact
  [box rejection sampling](Complexity/Probability/RejectionSampling.lean),
  [Sigma protocols with aborts](Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean), and
  [Lyubashevsky identification](Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky.lean) with
  completeness up to aborts and its exact abort probability, special soundness extracting a short
  integer solution of `[A | T]`, and exact HVZK for the erased-abort projection. Full interactive-view simulation remains open
  (#680/#643). Open: Fiat–Shamir with
  aborts and its signatures (after track A's random-oracle Fiat–Shamir), strict-PPT samplers for
  integer boxes, identification security under SIS, general moduli, module SIS and module
  lattices toward Dilithium-style schemes.

The current V1 port excludes the circuitized anti-checker, hardness-magnification argument and
MINKT/MINCKT developments. The long-term canon above includes metacomplexity; those results should
return as independently scoped, reviewed developments rather than automatic legacy ports. Retain
existing checked [MCSP definitions](Complexity/Computability/MCSP/Basic.lean),
[succinct variants](Complexity/Computability/MCSP/Succinct.lean),
[Shannon bounds](Complexity/Computability/MCSP/Shannon.lean) and
[anti-checker existence](Complexity/Computability/MCSP/AntiChecker.lean).
These do not include an efficient anti-checker generator or a hardness-magnification theorem.

## Finishing the recovered developments

Complete bounded endpoints on ordinary branches, with the six checks and independent API,
correctness and formal-abstract reviews before closing a milestone. Retain the FO-reduction
and machine-characterization priorities above. The native NL complement theorem is proved below.
The Arthur–Merlin and hardness-amplification developments have their own prerequisites and should be split at the
following endpoints, rather than submitted as class definitions or conditional wrappers alone.

| Development | First independently useful endpoint | Remaining endpoint and dependencies |
| --- | --- | --- |
| Iterated functions M2b | Sparse-counter centralizers and signed fixed powers are in [SparseDisplacement](Complexity/Computability/Circuit/Boolean/Iteration/SparseDisplacement.lean). Interval charts, encoding/decoding, canonical labels and additive variable-time circuits are in [SparseTime](Complexity/Computability/Circuit/Boolean/Iteration/SparseTime.lean), including both charged coordinate conversions. General compressed-forest reachability, first-hitting-time navigation, and complete visit-schedule circuits are in [ForestCircuits](Complexity/Computability/Circuit/Boolean/Iteration/ForestCircuits.lean), [NavigationCircuits](Complexity/Computability/Circuit/Boolean/Iteration/NavigationCircuits.lean), and [VisitScheduleCircuits](Complexity/Computability/Circuit/Boolean/Iteration/VisitScheduleCircuits.lean), with combinatorial checkpoint forests, interval labels, nonmerging segments, and compressed-forest navigation in [CheckpointForest](Complexity/Foundations/Combinatorics/FunctionalGraph/CheckpointForest.lean), [ForestIntervals](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestIntervals.lean), [ForestSegments](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestSegments.lean) and [ForestNavigation](Complexity/Foundations/Combinatorics/FunctionalGraph/ForestNavigation.lean), and sparse-counter specializations in [SparseNavigation](Complexity/Computability/Circuit/Boolean/Iteration/SparseNavigation.lean), [ResidueAdd](Complexity/Computability/Circuit/Boolean/Iteration/ResidueAdd.lean) and [HittingTime](Complexity/Foundations/Combinatorics/FunctionalGraph/HittingTime.lean). Autonomous controllers and affine-payload iteration bounds are in [AffineController](Complexity/Computability/Circuit/Boolean/Iteration/AffineController.lean). Universal-map simulation, product/group-action hardwiring, in-place multi-head machine bounds, and sequential-squaring reduction are in [UniversalMap](Complexity/Computability/Circuit/Boolean/Iteration/UniversalMap.lean), [InPlace](Complexity/Computability/Circuit/Boolean/Iteration/InPlace.lean) and [SequentialSquaring](Complexity/Computability/Circuit/Boolean/Iteration/SequentialSquaring.lean). Ordered circuit-description counting, modular-counter $\tilde\Omega(2^{n/2})$ power lower bounds, remainder reductions, subexponential-horizon barriers, hash-class prime-cycle permutations, and batched modular-counter upper and lower bounds are in [CircuitCounting](Complexity/Computability/Circuit/Boolean/Iteration/CircuitCounting.lean), [ModulusCounter](Complexity/Computability/Circuit/Boolean/Iteration/ModulusCounter.lean), [PrimeCycles](Complexity/Computability/Circuit/Boolean/Iteration/PrimeCycles.lean) and [CounterBatch](Complexity/Computability/Circuit/Boolean/Iteration/CounterBatch.lean). All ports follow source `c4cfa198`. | Done: all M2b iteration endpoints are proved. Nonuniform circuit existence does not certify preprocessing runtime. |
| NL = coNL | Done: [streaming inductive counting](Complexity/Algorithms/Reachability/InductiveCounting/Bounds.lean), with exact acceptance semantics, logarithmic-size registers and bounded termination on every branch. Certificates are checked without retaining paths or a reachable set. | Done: [native complement decider](Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/InductiveCounting.lean) and [NL = coNL](Complexity/Computability/Complexity/Classes/LogSpace/Complement.lean), for arbitrary injective instance encodings. Compact configuration IDs and read-only input queries are compiled to finite-state native NTMs, with every-prefix logarithmic workspace and every-branch halting. The source may be a `RecognizesInSpace` recognizer with looping branches; these recognize exactly the native `NL` problems. General space-constructible Savitch bounds remain separate. |
| Arthur–Merlin | Done: verifier-based MA and AM, error reduction, NP ∪ BPP ⊆ MA ⊆ AM ⊆ Π₂ᵖ, MA ⊆ Σ₂ᵖ ∩ Π₂ᵖ and MA ⊆ SBP ([ArthurMerlin](Complexity/Computability/Complexity/Classes/ArthurMerlin.lean)); the [set lower bound protocol and SBP ⊆ AM](Complexity/Computability/Complexity/Classes/ArthurMerlin/SetLowerBound.lean), [public-coin GNI in AM](Complexity/Computability/Complexity/Classes/ArthurMerlin/GraphNonIsomorphism.lean), and [PH = Σ₂ᵖ from coNP ⊆ AM for every encoding](Complexity/Computability/Complexity/Classes/ArthurMerlin/Collapse.lean). | Interactive-machine characterizations, AM[k] = AM and private-to-public-coin transformations remain separate endpoints. |
| Worst-case-hardness derandomization | Done for eventual hardness: [P = BPP from 2^(γn) De Morgan circuit hardness of a language in E](Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean), with the explicit field, the encoding in E and the parameter schedule certified. | The infinitely-often variant; the EXP-not-in-P/poly endpoint of Babai, Fortnow, Nisan and Wigderson. |

Do not mark these endpoints complete from an abstract algorithm, a class definition, or an
assumed reconstruction theorem: their machine/resource and quantitative conclusions are part of
acceptance. The curated formal abstracts record selected completed statements with their assumptions and scope.

## Jukna coverage

Formalize the established theorems, lemmas, constructions and exercise results throughout
[Jukna's *Boolean Function Complexity: Advances and Frontiers* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html),
using the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html).
The target is all useful established results and constructions, including supporting lemmas and
worthwhile exercises. Open problems are separate research opportunities, not completion
requirements. Reuse Mathlib and CSLib for the supporting mathematics.

Complete and review developments individually; book-wide coverage is a long-term program, not
a prerequisite for using the library. Organize modules by mathematical subject rather than book
chapter.

The [almost-injective binary linear map](Complexity/Probability/BitString/LinearHash/Collisions.lean)
implements Lemma 1.17, including its unordered-pair collision bound and an injective-map
corollary. Its matrix selection is existential; the partial-function circuit upper bounds that
use it remain outstanding.

This initial map follows the [contents](https://web.vu.lt/mif/s.jukna/boolean/TOC.pdf).
The linked modules are starting points, not evidence of complete chapter coverage. Audit exact
statements and hypotheses against each numbered result, including circuit bases, cost conventions,
uniformity, explicitness and quantitative strength; a citation or related theorem is insufficient.

| Chapters | Existing entry points | Next coverage work |
| --- | --- | --- |
| 1–2: foundations and Boolean analysis | [Circuit hierarchy](Complexity/Computability/Circuit/Boolean/Hierarchy.lean), [Shannon synthesis](Complexity/Computability/Circuit/Boolean/ShannonSynthesis.lean), [Fourier analysis](Complexity/Foundations/BooleanAnalysis/Fourier.lean) | Audit counting, graph complexity, degree and approximation results. |
| 3–5: communication | [Protocols](Complexity/Computability/Communication/Protocol.lean), [Karchmer–Wigderson](Complexity/Computability/Communication/KarchmerWigderson.lean) | Complete matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | [Spira](Complexity/Computability/Circuit/Boolean/Spira.lean), [Khrapchenko](Complexity/Computability/Circuit/Boolean/Khrapchenko.lean), [Subbotovskaya](Complexity/Computability/Circuit/Boolean/Formula/Subbotovskaya.lean), [Andreev](Complexity/Computability/Circuit/Boolean/Formula/Andreev.lean), [monotone clique](Complexity/Computability/Circuit/Monotone/Clique/LowerBound.lean) | Audit remaining formula and monotone bounds; develop span programs and negation complexity. |
| 11–13: depth restrictions and general gates | [Håstad](Complexity/Computability/Circuit/Boolean/Hastad.lean), [Smolensky](Complexity/Computability/Circuit/Boolean/Smolensky.lean), [symmetric gates](Complexity/Computability/Circuit/Boolean/ShallowSymmetric.lean) | Audit depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | [Decision-tree certificates](Complexity/Computability/DecisionTree/Certificate.lean), [Barrington](Complexity/Computability/Circuit/Boolean/BarringtonClass.lean) | Complete bounded-read and bounded-time lower bounds and remaining tree results. |
| 18–19: proof complexity | [Resolution size–width](Complexity/Logics/Propositional/Resolution/SizeWidth.lean), [tree-like resolution](Complexity/Logics/Propositional/Resolution/TreeLike.lean), [Tseitin](Complexity/Logics/Propositional/Resolution/TseitinExpander.lean), [pigeonhole](Complexity/Logics/Propositional/Resolution/Pigeonhole.lean), [Cook–Reckhow systems](Complexity/Computability/Complexity/ProofSystem.lean) | Develop proof-space and cutting-plane lower bounds. |
| 20: barriers and further methods | [Fusion API](Complexity/Computability/Circuit/Fusion/Basic.lean), [Nisan–Wigderson core](Complexity/Computability/Kolmogorov/NisanWigderson.lean) | Match the book's generator, natural-proof, fusion and indirect lower-bound results. |
| Appendix A: mathematical prerequisites | Mathlib and `Complexity/Foundations/` | Reuse existing statements and fill dependencies as clients require them. |

## Approximation and Fusion milestones

These milestones extend the existing [semifilter covers](Complexity/Computability/Circuit/Fusion/Semifilter.lean)
and [cyclic characterization](Complexity/Computability/Circuit/Fusion/Cyclic/Compiler.lean)
using [Oliveira's approximation-method notes (2018)](https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/approximation-method-fusion-note.pdf)
and [Cavalar–Oliveira, ECCC TR25-033 (2025)](https://eccc.weizmann.ac.il/report/2025/033/).
Credit the earlier results of Razborov, Karchmer, Wigderson, and Nakayama–Maruoka where used.
The issues carry ownership and review history. Circuit bounds use the native basis with free
constants and binary unions; the source docstrings record the precise scope of each result.

| Milestone | Proved result and scope |
| --- | --- |
| [Quadratic completeness #12](https://github.com/cslib-community/complexitylib/issues/12) | **Proved:** [quadratic compiler](Complexity/Computability/Circuit/Fusion/Quadratic.lean) uses exactly `t²` AND gates for a `t`-pair cover and gives the minimum source-cost bound, including arbitrary carriers, empty input families and trivial targets (TR25-033, Theorem 24; PR #19). |
| [Approximation bridge and counting barrier #13](https://github.com/cslib-community/complexitylib/issues/13) | **Proved:** [exact consistency and local observation errors](Complexity/Computability/Circuit/Fusion/Consistency.lean), the [fixed pair sampler, weighted averaging and `8n + 8` certificate barrier](Complexity/Computability/Circuit/Fusion/Sampling.lean) (Oliveira, Lemma 3 and Theorem 6; PRs #20 and #22). This is a local observation bridge, not a formal equivalence of all approximation models. |
| [Graph transfer and inequality #14](https://github.com/cslib-community/complexitylib/issues/14) | **Proved:** [row/column-to-literal transfer](Complexity/Computability/Circuit/Fusion/Graph.lean) for any admissible witness subclass, including semi-ultrafilters, and [exact canonical/full cover and intersection cost `n`](Complexity/Computability/Circuit/Fusion/Graph/Inequality.lean) for inequality on `2^n` vertices per side (TR25-033, Lemmas 39/48 and Proposition 40; PR #21). |
| [Random graph covers #15](https://github.com/cslib-community/complexitylib/issues/15) | **Proved:** [finite inclusion-pattern counting](Complexity/Computability/Circuit/Fusion/Encoding.lean) and [random graph hardness](Complexity/Computability/Circuit/Fusion/Graph/Random.lean): for `N ≥ 16`, probability at least `1 - 2⁻ᴺ` of `⌊N/16⌋ < ρ(G) ≤ N` under the uniform distribution on all labelled bipartite graphs (TR25-033, Theorem 37; PR #23). |
| [Conondeterministic complexity #16](https://github.com/cslib-community/complexitylib/issues/16) | **Proved:** [universal-verifier cover extraction](Complexity/Computability/Circuit/Fusion/Conondeterministic.lean) and the [converse compiler](Complexity/Computability/Circuit/Fusion/Converse.lean) give `ρ_ultra(f) ≤ C_forall,AND(f) ≤ 5ρ_ultra(f)`. The [extended-natural circuit measure](Complexity/Computability/Circuit/Boolean/Conondeterministic.lean) minimizes over all finite auxiliary counts and verifiers; a `t`-pair cover gives exactly `3t` auxiliary bits and `5t` AND gates, including zero and constant cases (TR25-033, Theorem 45, credited there to Karchmer; PRs #25 and #28). The explicit factor five comes from the formalized certificate construction. The graph transfer above specializes to semi-ultrafilters (Lemma 48). |
| [De Morgan circuit size #334](https://github.com/cslib-community/complexitylib/issues/334) | **Proved:** [De Morgan transfer](Complexity/Computability/Circuit/Fusion/DeMorgan.lean) of unrestricted cover complexity `ρ(f)` from literals: `ρ(f) ≤ C_AND(f) ≤ ρ(f)²` for monotone AND complexity from literals, and `ρ(f) ≤ 2C(f)`, `C(f) ≤ 4(ρ(f)+1)²(2n+ρ(f)+1) + n` for De Morgan circuit size `C(f)`, negations anywhere and every gate charged. The lower bound uses the existing [dual-rail translation](Complexity/Computability/Circuit/Monotone/DualRail.lean) and holds for any admissible witness class; the upper bound adds a [total-size bound](Complexity/Computability/Circuit/Fusion/Quadratic.lean) `4(t+1)²(n+t+1)` for the quadratic compiler. The formalized upper bound is cubic in the cover size when it exceeds `n`, not quadratic, because unions are charged; this is a property of the construction. |

Keep the source models explicit: constants, zero-gate constructions, exact versus one-sided
literal consistency, and AND versus total gate costs. The counting barrier requires a capacity
bound over every pair; it does not apply to a bound restricted to a particular circuit's gate
pairs and is not an upper bound on unrestricted cover complexity. The sampling and reconstruction
lemmas are proved, not assumed. These are
formalizations of established results, not claims of new explicit superlinear circuit lower bounds.

## Stateful algorithms and data structures prototype

The [stateful interface calculus](Complexity/Foundations/Semantics/Stateful/Basic.lean) separates
mathematical operations, [semantic modules](Complexity/Foundations/Semantics/Stateful/Composition.lean),
[native realizations](Complexity/Foundations/Semantics/Stateful/Realization.lean), and
[resource certificates](Complexity/Foundations/Semantics/Stateful/Resource.lean). Adaptive client proofs,
semantic Hoare rules, module substitution and hidden-state potentials compose without choosing
a backend. The [two-stack queue](Complexity/Algorithms/Lean/Queue.lean) and
[reset-and-replay timeline editing](Complexity/Algorithms/Lean/Retroactive.lean) are
checked constructions, with explicit primitive-cost assumptions; their pure client controllers
do not yet have total Word-RAM time certificates.

The shared [ordered-set interface](Complexity/Foundations/Semantics/Stateful/OrderedSet.lean)
and [optional-minimum contract](Complexity/Foundations/Data/OrderedSet.lean) are independent of
representations and costs. The interface admits arbitrary linearly ordered keys and is total;
a bounded-key implementation may restrict insertion admissibility separately. The
[unbalanced binary search tree](Complexity/Algorithms/Lean/SearchTree/Basic.lean) implements
membership, insertion, minimum and strict successor over any linear order, preserving a strict
BST invariant and finite-set semantics. Duplicate insertion preserves the tree; missing successors
and empty queries return `none`. Its [native realization](Complexity/Algorithms/Lean/SearchTree/Stateful.lean)
transfers correctness and additive node-visit bounds to adaptive clients. Each operation visits
at most the initial height, bounded by set cardinality; this is not a logarithmic or RAM-time
claim. [Checked examples](ComplexityTests/SearchTree.lean) contrast height-three and height-seven
representations of the same seven keys and execute an answer-dependent two-minimum query.
[Deletion](Complexity/Algorithms/Lean/SearchTree/Erase.lean) replaces a matching node by its left
subtree when the right one is empty and otherwise splices in the successor from the right subtree,
with finite-set semantics, invariant preservation, unchanged trees for absent keys,
and node visits and resulting height bounded by the initial height
([examples](ComplexityTests/SearchTreeErase.lean)). Adding deletion to the shared stateful
ordered-set interface, balancing, and concrete heap/RAM representations remain open.

[Static fusion trees #443](https://github.com/cslib-community/complexitylib/issues/443)
have a [finite-set endpoint](Complexity/Algorithms/WordRAM/FusionTree/Static.lean) proving
worst-case inclusive predecessor in `O(1 + log_w n)` actual standard-basis RAM instructions
and `O(n)` words for nonempty sets (`O(n + 1)` including empty sets).
The [query program](Complexity/Algorithms/WordRAM/FusionTree/Query.lean) charges initialization,
node search, checked multiword arithmetic, pointer traversal, and halt. Explicit bounds are
`3100000 * (Nat.log w n + 1)` instructions and `126n + 1042` data/register words, uniformly
for `w ≥ 2`. Presence and value occupy separate registers, so key zero remains distinct from
absence. The entire allocation frontier must fit an address word separately from the keys.
The bounded-size code family contains width-dependent constants; static preprocessing uses
classical witnesses and has no RAM running-time certificate. Uniform preprocessing and dynamic
updates remain open. The checked-overflow
[multiword multiplication dependency #444](https://github.com/cslib-community/complexitylib/issues/444)
provides reusable arithmetic. Shared workspace initialization now accompanies the canonical
`WordRAM/Multiword/Digits` module, letting Transfer, Bitwise and Shift import digit infrastructure
without depending on multiplication.
The shared child-height lemmas in `Algorithms/Lean/FusionTree/Tree` support both
`Model.decode_rep` and `QueryProgram.exec_loop_height` without duplicate proofs.

[Client resource contracts](Complexity/Foundations/Semantics/Stateful/CostHoare.lean) combine
admissibility, postconditions and initial-state-dependent operation budgets. Their sequencing
rules retain answer-dependent costs; separate method budgets transport contracts through
successive semantic modules and then to additive native execution measures. The `stateful`
tactic uses local contracts and structural rules, with intermediate assertions and implementation
choices supplied explicitly. A two-layer adaptive counter example checks both execution branches
and rejects an insufficient budget.

[RAM controller certificates](Complexity/Computability/WordRAM/Controller.lean) now connect a
fixed machine fragment to an admissible client, charging its control flow and register preparation.
Sequencing uses one fixed continuation fragment for all represented answers; pure semantic results
require actual execution evidence. Named certificates are reused by `stateful`, while `polytime`
can retrieve the distinct uniform RAM function-time predicate. The
[adaptive stack controller](Complexity/Algorithms/WordRAM/Stack/Controller.lean) starts from the
standard singleton input, installs an empty stack at address two, pushes and pops the input, and
uses the observed answer to replace zero through another pair of stack calls. It returns
`max n 1` in exactly 49 instructions for zero and 29 otherwise, including setup, argument writes,
control flow and halt. All inputs fit its logarithmic numerical-magnitude width threshold.
This does not certify arbitrary Lean continuations or a conversion to Turing-machine time.

The [fixed-program bridge](Complexity/Computability/WordRAM/Dynamic.lean) has concrete bounded
[stack](Complexity/Algorithms/WordRAM/Stack.lean) and
[prefix-sum](Complexity/Algorithms/WordRAM/PrefixSums/Dynamic.lean) clients. These certify persistent
operation execution, word-fit conditions, instruction costs including halt, and arbitrary
admissible adaptive histories. Finite-footprint assertions and faithful probe transcripts supply
frame rules. Prefix sums use a balanced aggregation tree for a power-of-two number of entries,
not a Fenwick layout. Machine costs exclude initial representation construction and external argument
encoding/delivery and result decoding; the stated storage bounds concern reserved representation regions.

The [shared-memory RAM queue](Complexity/Algorithms/WordRAM/Queue/Dynamic.lean) now realizes
FIFO enqueue and dequeue with one fixed eleven-register dispatcher. Two reserved arrays hold
at most `capacity` live values in `2 * capacity` reserved word cells. An empty-front dequeue
executes a real rear-to-front transfer loop. Eight credits per rear element give at most
fourteen amortized instructions per queue call, including halt, with initial and final credit
retained. Six actual register instructions initialize the empty representation without clearing
memory. The worked adaptive client reinserts an observed dequeued value and checks FIFO order,
zero-valued observations, full/zero capacity and instruction-budget rejection. This direct
implementation shares the FIFO specification with the abstract two-stack construction above;
it is not a compilation of that construction's free-monad methods. Arbitrary external client
computation and argument delivery remain outside the per-operation bound.

The [recursive van Emde Boas set](Complexity/Algorithms/Lean/VanEmdeBoas/Basic.lean)
supports bounded insertion, membership and strict successor for the universe
`U(d) = 2^(2^d)`. Its minimum-excluded cluster representation has checked
[invariant preservation and exact insertion semantics](Complexity/Algorithms/Lean/VanEmdeBoas/Insert.lean),
[least-successor and absence theorems](Complexity/Algorithms/Lean/VanEmdeBoas/Successor.lean),
and a [finite-set abstraction](Complexity/Algorithms/Lean/VanEmdeBoas/Elements.lean).
The [contiguous layout arithmetic](Complexity/Algorithms/Lean/VanEmdeBoas/Layout.lean)
has nonoverlapping recursive records and an explicit bound of ten words per universe element.
The [recursive memory refinement](Complexity/Algorithms/WordRAM/VanEmdeBoas/Model.lean)
interprets actual memory, including stale empty extrema and arbitrary surrounding memory.
[Fixed-program native calls](Complexity/Algorithms/WordRAM/VanEmdeBoas/Call.lean)
certify insertion (`39*(d+1)+16`), membership (`28*(d+1)+18`), and strict successor
(`65*(d+1)+22`, using a `4*d`-word scratch stack) on one 213-instruction 32-register dispatcher
independent of depth and word width, charging setup, dispatch, loop control, and halt, with
exact GenericRAM transfers and logarithmic `log₂(log₂ U)` bounds
([Insert](Complexity/Algorithms/WordRAM/VanEmdeBoas/Insert.lean),
[Member](Complexity/Algorithms/WordRAM/VanEmdeBoas/Member.lean),
[Successor](Complexity/Algorithms/WordRAM/VanEmdeBoas/Successor.lean)).
A separate [uniform 32-register initializer](Complexity/Algorithms/WordRAM/VanEmdeBoas/Init.lean)
constructs the empty represented tree and scratch stack pointer from arbitrary bounded memory
in at most `8 * span d + 20 * d + 25 ≤ 80 * U + 20 * d` instructions within a total footprint
of `span d + 4 * (d + 1) ≤ 10 * U + 4 * (d + 1)` words. The operations are packaged as a
`DynamicCertificate` for the finite-set `Stateful.Spec` on `[0, U)`, with combined
initialization-and-adaptive-client execution (`run_initialized`) charging at most
`65*(d+1)+22` instructions per operation while preserving all memory outside
`[base, base + span d + 4 * (d + 1))`. External client computation and argument register writes
between calls are not charged to individual operations; deletion and predecessor remain future
work. The recursive minimum-excluded variant is credited to Demaine's exposition, separately
from the original van Emde Boas--Kaas--Zijlstra stratified representation.

The [doubling array](Complexity/Algorithms/WordRAM/DynamicArray.lean) implements dynamic append
and indexed read with one fixed twelve-register dispatcher using the bump allocator and array-copy
loop. Fifteen instructions initialize the empty array by allocating and zeroing a one-word block at
address zero. Appending writes in place in seven instructions when spare capacity remains and
doubles capacity in `15 * cap + 19` instructions when full. Potential `15 * (2 * |vs| - cap)`
bounds every append by `49` amortized instructions before dispatch (`52` including dispatch and
halt) and every indexed read by `6` instructions including dispatch and halt, retaining initial
and final credit across arbitrary admissible adaptive clients. Old blocks remain allocated, so the
space bound `frontier < 4 * |vs|` for nonempty arrays limits total words ever allocated rather than
reclaimed live storage; deallocation, shrinking, and compiled client controllers remain open.

Outstanding: controllers for larger adaptive and iterative clients;
reusable allocation and deallocation, shrinking and live/peak space accounting,
richer ownership and recursive procedures; independent model
realizations for cell probes, caches and randomness; and present/historical queries for the
retroactive interface. Upstream API coordination and coordinator review remain prerequisites
for integration.

## Machine-class milestones

Polynomial efficiency is sufficient for many reductions, but does not establish tight time or
space bounds. Further class-level work needs resource certificates for the actual algorithms:

* Binary-counted space loops: the [native `Nat.fold` certificate](Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolySpace/Fold.lean)
  ports lean-canny's indexed fold and adds a prefix-invariant rule. The child and seed may use
  arbitrary polynomial space; every accumulator prefix must have polynomially bounded encoded
  length. Extracting lean-canny's recursive evaluator, implicit arithmetic and ETR algorithm
  remains separate work; this fold establishes none of their algebraic or class-level results.
* Mathlib TM2 compatibility: the [polynomial-time bridge](Complexity/Computability/Machines/Turing/TM2/PolyTime.lean)
  transfers typed computations with finite working alphabets to the tidy multi-tape calculus
  under standard binary word encodings. The [polynomial-space bridge](Complexity/Computability/Machines/Turing/TM2/PolySpace.lean)
  transfers terminating computations with polynomially bounded stacks without a runtime bound.
  The [reverse compiler](Complexity/Computability/Machines/Turing/TM2/Reverse/Bounds.lean)
  constructs finite-alphabet stack machines with time
  `n + (k + 1) * (t + 1) + o + 3` and total reachable stack length at most `n + s + o`, including
  initialization and canonical cleanup. The [transfer API](Complexity/Computability/Machines/Turing/TM2/Reverse/Transfer.lean)
  proves polynomial-time computation and PSPACE decision equivalence under the original binary
  encodings, without polynomial runtime assumptions for space. Input storage adds linear space;
  sublinear work-space comparisons and a linear-space forward simulation remain open;
* Tree Evaluation: the [Cook–Mertz machine](Complexity/Computability/TreeEval/Space.lean)
  has a proved parameterized space bound on valid encoded instances and an
  `O(log n · log log n)` input-size space corollary on nontrivial instances (`1 ≤ ℓ` and
  `1 ≤ H`); malformed-input handling and the refined `O(ℓ + H log(ℓ + 2))` parameter bound
  remain outstanding. Toward Williams's `TIME[t] ⊆ SPACE[√(t log t)]` (#361), the
  [fan-in-`d` procedure](Complexity/Computability/TreeEval/Ary/CookMertz.lean) is proved correct
  over `d + 1` registers when `d · ℓ < |K| - 1` (milestone M1); at `d = 2` it is the binary
  procedure step for step, whose correctness is derived from it
  ([`Ary.proc_ofBinary`](Complexity/Computability/TreeEval/CookMertz.lean)). Implicit Tree
  Evaluation (#367) starts from
  [query machines in the space of their states](Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/QueryMachine.lean),
  which charge neither the input nor the output; the fan-in-`d` space bound, subroutine calls for
  implicit gates and leaves, padding of non-perfect trees, and the remaining milestones are open;
* the space hierarchy below linear space: the
  [space hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Space.lean) and
  `L ⊊ PSPACE` are proved for space-constructible bounds `g` with `n ≤ g n`, and the textbook
  form for `log n ≤ g n` needs a universal simulation that does not hold its input; the
  [time hierarchy](Complexity/Computability/Complexity/Classes/Hierarchy/Time.lean) and `P ⊊ EXP`
  are proved with a polynomial simulation gap, so a tight tape-indexed hierarchy needs a
  linear-overhead simulation and an `f log f` time hierarchy the corresponding simulation bound;
* Reingold's theorem: [USTCON ∈ L and SL = L](Complexity/Computability/Complexity/Classes/LogSpace/USTCON.lean)
  are proved for the adjacency-matrix encoding (with `SL` defined by logspace many-one reducibility
  to `USTCON`, completeness of `USTCON` for `SL` and `L`, and the unary-header injectivity lemma
  shared with `TreeEval` in [List/Append.lean](Complexity/Foundations/Data/List/Append.lean)); a
  symmetric-Turing-machine model of `SL` and an edge-list variant of `USTCON` by a logspace
  reduction remain;
* Native [NL = coNL](Complexity/Computability/Complexity/Classes/LogSpace/Complement.lean) is
  proved by streaming inductive counting, including complement deciders for recognizers with
  looping branches. `PH ⊆ PSPACE` is also proved by evaluating quantified predicates in
  [polynomial space](Complexity/Computability/Complexity/Classes/Inclusions.lean);
* alternating time/space classes and bounded-alternation characterizations of `PH`, beyond the
  proved [AP = PSPACE](Complexity/Computability/Complexity/Classes/Alternation/Savitch.lean);
* the ordered logarithmic-space FO encoding bridge and first-order Circuit Value completeness in the
  [first continuing priority](#continuing-priorities), together with uniform circuit-family and
  counting-machine characterizations;
* RAM value domains: the [generic core](Complexity/Computability/GenericRAM/Defs.lean) now permits
  arbitrary value, address, configuration and constant-symbol types, partial operations/tests,
  and model-specific fault policies. The [WordRAM adapter](Complexity/Computability/WordRAM/Generic.lean)
  preserves every step, fault, output and instruction count for every basis and arbitrary state.
  Instances cover the [signed bounded integer model](Complexity/Computability/GenericRAM/Signed.lean)
  of lean-trominoes and [exact reals and prime fields](Complexity/Computability/GenericRAM/Algebraic.lean)
  with separate tagged natural address words. Real semantics is noncomputable; prime fields are
  executable. The algebraic variant has checked word arithmetic and rational constants with
  nonzero field denominators; no field-to-word conversion is provided. The
  [native scalar interface](Complexity/Computability/GenericRAM/Native.lean) separately certifies
  checked literals/operations, tests, address extraction and move/control validation with arbitrary
  native TM time/space bounds; it is equivalent to native computability when bounds are unrestricted.
  Polynomial bounds yield native polynomial time. A
  [bounded-natural addition model](Complexity/Computability/GenericRAM/Native/Nat.lean) supplies every
  scalar certificate, and [WordRAM native primitives](Complexity/Computability/WordRAM/Native.lean)
  supply complete polynomial-time `NativePrimitives` bundles for `Basis.standard`, `Basis.additive`,
  `Basis.arithmetic`, and `Basis.exact` (plus restricted sub-bases and homomorphic preimages) across
  all unary-encoded widths with binary operands (#489). The native tidy calculus has
  [fixed finite tuple rules](Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/Pi.lean)
  with linear access/gather/update and arbitrary summed construction bounds,
  [retained-input option elimination](Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/Option.lean)
  charging extraction, repeated option computation, input retention, and the selected handler
  (#301), [sum injections and projections](Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/Sum.lean),
  and [native certificate combinators](Complexity/Computability/GenericRAM/Native/Combinators.lean).
  The [finite-state step representation](Complexity/Computability/GenericRAM/Simulation/Finite.lean),
  [certified native step simulator](Complexity/Computability/GenericRAM/Simulation/Turing.lean),
  and [clocked multi-step simulator and whole-run transport](Complexity/Computability/GenericRAM/Simulation/Run.lean)
  implement single steps and clocked multi-step runs of any fixed generic-RAM program over sparse
  memory and arbitrary `NativePrimitives`, preserving all successor states, halts and faults
  (`denote_step`, `denote_run`, `executes_iff_exists_run`), bounding sparse-memory growth by at most
  one stored address per step (`length_entries_run_le`), retaining parameterized primitive and
  sparse-memory time/space bounds along the run (`le_runTime_of_run_eq_inl`,
  `le_runSpace_of_run_eq_inl`), and transporting halting `Executes` certificates to native
  multitape Turing machines with both explicit `ComputableTidilyInO` bounds and automatic
  `ComputableTidilyInPolyTime` corollaries, including `WordRAM` specializations (#298, #292).
  Uniform arbitrary-program dispatch, general width-selection/input-fit theorems, and simulating
  individual operations by programs over smaller bases remain open (#293).
  Generalizing the structured program calculus and time-class APIs to arbitrary domains,
  weighted/bit costs, and simulations between these instances also remain open. No
  real-RAM/Turing-machine equivalence is claimed. The redesigned typed core is proposed in
  [CSLib #1158](https://github.com/leanprover/cslib/pull/1158); its scope and remaining compatibility
  bridges are recorded in [UPSTREAM.md](UPSTREAM.md#coordination-before-submission);
* Sparse RAM memory: [association-list semantics](Complexity/Computability/GenericRAM/SparseMemory/Basic.lean)
  and [native multitape TM certificates](Complexity/Computability/GenericRAM/SparseMemory/Turing.lean)
  implement default-valued reads and insert/replace writes using Mathlib's `AList` and the existing
  encoded equality/search/filter calculus. Parameterized time/space bounds depend on stored-cell
  count and encoded address/value lengths; cubic-time and linear-space corollaries use full binary
  input length. Overwrites preserve cardinality, and writes retain distinct addresses. The read
  default is supplied as input to one uniform machine. Combined with the certified single-step and
  clocked whole-run simulators above (#298, #292), this supports transporting fixed-program RAM
  executions to native multitape Turing machines; uniform arbitrary-program dispatch and general
  width-selection/input-fit reductions remain open (#293). No bridge
  for arbitrary exact real arithmetic is claimed;
* RAM models: the [bounded-word RAM](Complexity/Computability/WordRAM/Defs.lean), adapted from the
  Lean formalization accompanying the tromino undecidability paper, is parameterized by a
  [basis of word operations](Complexity/Computability/WordRAM/Basis.lean) built on circuit
  signatures, with the standard, arithmetic (the source's operations on unsigned words) and
  additive bases; programs and decision procedures
  [transfer along meaning-preserving maps of bases](Complexity/Computability/WordRAM/MapOp.lean)
  with identical runs, and `Program .additive r` compiles directly to `Cslib.RAM` via
  `ToRAM.compileAdditive` and `Basis.additiveHomStandard` (#315). Simulating an operation by a
  program over a smaller basis with an instruction budget (the analogue of circuit
  `SimulatesWithCost`) and an AC⁰ basis remain open. The machine has [linear and polynomial
  instruction bounds](Complexity/Computability/WordRAM/Time.lean) with width-dependent time and
  encodings, arbitrary predicates on input/width pairs, and width-indexed code of uniformly bounded
  length. Explicit `Uniform` variants retain one fixed program, which may read the word size;
  `LogWord` wrappers express the transdichotomous lower-bound assumption. Alongside these,
  asymptotic time with constants shared across widths and Mathlib width-schedule bridges are
  available. The machine also has
  [structured programs](Complexity/Computability/WordRAM/Structured.lean) compiling with exact
  instruction counts, [allocation and arrays](Complexity/Computability/WordRAM/Allocation.lean) and
  a [linear-time element-distinctness client](Complexity/Algorithms/WordRAM/ElementDistinctness.lean)
  over `.additive` whose promised inputs provably fit at that threshold. The generic classes alone do not supply
  this input-fit guarantee. The [additive-memory compiler](Complexity/Computability/WordRAM/RAM.lean)
  now forward-simulates successful fitting runs in the existing
  [`Cslib.RAM`](Complexity/Computability/RAM/Defs.lean) with logarithmic cost
  `8 * (bitLength (r + 5) + 1) * (t + 1) * (w + 1)`, including its two register initializers
  and final output copy/jump, from an explicitly supplied padded input. A separate
  [input preparer](Complexity/Computability/RAM/Input.lean) now charges the backward relocation and
  prefix clearing from five zero scratch cells followed by a length header and the input words.
  It reaches the exact padded register state before arbitrary appended code in logarithmic cost
  `(24 + R) * (bitLength (R + 5) + 2) * (input.length + 1) * b` for `R ≥ 5`, given bit-length
  bound `b` on the header and words; external input installation remains uncharged. The
  [composed bridge](Complexity/Computability/WordRAM/RAMInput.lean) now includes that preparation
  in `C_r * (t + input.length + 1) * (w + 1)`, for an explicit constant depending only on the
  source register count. The same fixed compiler gives a
  [bounded-universe element-distinctness decider](Complexity/Algorithms/WordRAM/ElementDistinctnessRAM.lean)
  of logarithmic RAM cost `2735 * (n + 1) * (Nat.log 2 (n + 1) + 1)`, including preparation;
  the separately supplied padded-input bound is `2448 * (n + 1) * (Nat.log 2 (n + 1) + 1)`.
  These statements retain the explicit preloaded length-bearing convention and entry promise.
  Wider-fragment and Turing-machine simulations remain open. The unrestricted converse
  from prescribed-width to uniform decision is false: width can supply instance-dependent advice.
  A useful conversion must specify an input-fit guarantee, a size-based width-selection procedure
  with computability and resource bounds, encoding conventions, and simulation overhead. Transfer
  of cell-probe lower bounds and the source's Horn-SAT, 2SAT, matching and domino-tiling clients
  also remain open;
* Single-tape, Post–Turing (`TM0`/`TM1`), and `Partrec` integration (#318): [tape equivalences](Complexity/Foundations/Data/BiTape.lean) (`StackTape.equivListBlank`, `BiTape.equivTape`), [translations](Complexity/Computability/Machines/Turing/SingleTape/PostTuringMachine.lean) between `SingleTapeTM` and Mathlib's `Turing.TM0` and `Turing.TM1` (step-for-step for `toTM1` and up to one final halting step for `ofTM0`; `toTM0` and `ofTM1` preserve evaluation only), [1-work-tape multi-tape simulation](Complexity/Computability/Machines/Turing/MultiTape/SingleTape.lean) (`MultiTapeTM.ofSingleTapeTM` in time `3 * |x| + 2 * t + 6` and space `3 * |x| + 2 * t + 7`, lifting `SingleTapeTM.TimeComputable` and `PolyTimeComputable`), [`Primrec`/`Partrec`/`Computable` bridges](Complexity/Computability/Machines/Turing/MultiTape/Halting/Partrec.lean) for [single-tape](Complexity/Computability/Machines/Turing/SingleTape/Partrec.lean) and multi-tape machines (`IsComputable.computable`, `IsDecidable.computablePred`, `MappingReducible.manyOneReducible`), and [machine-backed Kolmogorov complexity](Complexity/Computability/Kolmogorov/SingleTape.lean) (`ofSingleTapeTM`, `ofTM0`, `ofTM1`, [multi-tape `IsPartrec` optimality](Complexity/Computability/Kolmogorov/MultiTape.lean)) are proved; reverse multi-tape-to-single-tape simulation and machine-backed Nisan–Wigderson decoding results remain open;
* concrete list-decodable codes for Nisan–Wigderson and order-invariant descriptive-complexity
  queries.

Check upstream work before starting these developments. The existing combinatorial or
machine-relative cores do not by themselves establish the missing uniform resource guarantees.

## Candidate proof improvements

These are experiments to validate, not claimed savings:

* Factor indicator-expectation identities from PCP's second-moment calculation and recurring
  cardinality/logarithm conversions only when a second client benefits.

Judge changes on client readability, total proof burden and elaboration cost. Count proof fields
and helper APIs, and distinguish source-line counts from runtime or proof-term size.
[scripts/proof_lengths.py](scripts/proof_lengths.py) supports comparison against a Git revision.

Past measurements, reviews and proposals remain in the
[historical roadmap](https://github.com/cslib-community/complexitylib/blob/c88395234575284c2fe1e9e3619ead1c2f6fd7f3/ROADMAP.md).
