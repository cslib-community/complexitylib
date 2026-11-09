# Security games and primitive families

## Generic games and adversary quantifiers

[Game](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L67) is a `PMF Bool`. Success is its true probability; advantage is the nonnegative distance between two success probabilities. [Indistinguishable](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L154) says that every admissible complete adversary has negligible advantage as the parameter grows. `Indistinguishable.of_reduction` transfers security through a reduction with a polynomially bounded loss and negligible additive error, while `indistinguishable_pure_false_iff`, `Indistinguishable.of_succProbability_le`, and `Indistinguishable.of_succProbability_reduction` specialize one-sided search and forgery games compared against `PMF.pure false`. This layer is mathematical probability; admissibility determines the computational interpretation [cslib-frontier][complexitylib].

For finite-source statistical bounds, import [Game/CloseTo/Statistical.lean](../../CslibFrontier/Crypto/Game/CloseTo/Statistical.lean). `Cslib.Interactive.closeTo_of_dist_le` turns a bound on the finite-PMF metric (half the L1 distance) into the existing all-event `CloseTo` relation with the same error. Its `CloseTo.bind_left` law then handles arbitrary randomized continuations, including infinite output types. This shared import exposes the existing bridge without importing lattice protocols or their native sampler certificates; the former `Lyubashevsky.Efficient` import still reexports it.

For adaptive stateful replacement, import [Security/Oracle.lean](../../CslibFrontier/Computability/Interactive/Security/Oracle.lean). `OracleComp.IsCostBounded.closeTo_runWith` turns a program's existing cost bound `K` and per-call `CloseTo` bounds `cost q * ε` into a bound `K * ε` on the joint result and final state. The premise compares both handlers at every identical query and starting state, including unreachable states; no coupling or finite state space is assumed. Calls of cost zero can still update a shared cache, but their joint reply/state laws must agree statistically at error zero. Charging only signing calls therefore avoids paying for unchanged hash calls or private sampling. The checked adaptive client in [OracleStatistical.lean](../../CslibFrontierTests/OracleStatistical.lean) uses two repeated signing requests, answer-dependent repeated cache reads, and a concrete nonzero error bound while preserving the cache and signing log. This shared lemma does not itself complete the native Schnorr signing-game or key-generation transport in #2568.

For two continuations that agree outside a bad input event, import [Game/CloseTo/UntilBad.lean](../../CslibFrontier/Crypto/Game/CloseTo/UntilBad.lean). `CloseTo.bind_of_eq_on μ f g bad` bounds the mixtures by the actual probability `μ.toOuterMeasure bad`; agreement is required only on supported inputs outside `bad`, and neither type must be finite. This lets a cache-programming step charge only the probability that the sampled point was already cached. The [checked clients](../../CslibFrontierTests/CloseToUntilBad.lean) retain the actual Fiat–Shamir reply and final cache, show a sharp one-half error on an infinite output type, and allow arbitrary disagreement on impossible inputs at zero cost. This law does not identify different hidden cache states or justify removing aborted queries.

[ComputationallyIndistinguishable](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Basic.lean#L94) specializes admissibility to a uniform native strict-PPT test on `(1^n, sample)`. Its ensembles are arbitrary PMFs on bit strings: sampleability and polynomial output length are not bundled. `IsPPTTest` admits semantic tests whose laws have a native program witness. Efficient postprocessing and hybrid results use those certificates, not the mere presence of a Lean function.

Pinned cslib also has the finite [Generator](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Primitives/PRG/Defs.lean#L38) interface, whose `Secure` accepts any chosen predicate on randomized tests, while expansion is a separate cardinality property. cslib-frontier adds circuit-bounded tests and uniform machine tests on top. These are intentionally different quantifiers; the circuit version can select a new bounded circuit at each input length [cslib][cslib].

## Hardness and pseudorandomness

| Schema | Principal source | Formal parameters and main use |
|---|---|---|
| One-way functions | [CslibFrontier/Crypto/Computational/OneWay.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay.lean) | Deterministic native polynomial evaluation; uniform seed-length sampling; strict-PPT inverter gets unary length and image; any preimage may win |
| Pseudorandom generator | [CslibFrontier/Crypto/Computational/PseudorandomGenerator.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomGenerator.lean) | Length schedule, expansion, native deterministic evaluation and indistinguishability |
| Adaptive pseudorandom function | [CslibFrontier/Crypto/Computational/PseudorandomFunction.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomFunction.lean) | Oracle-PPT access, consistent ideal random function, explicit input/output widths and malformed-query convention |
| Collision resistance | [CslibFrontier/Crypto/Computational/CollisionResistant.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CollisionResistant.lean) | Public setup distribution/encoding and input-validity predicate; keyed word specialization; setup need not be efficiently sampleable in the general interface; [DiscreteLog/GroupHash.lean](../../CslibFrontier/Crypto/Computational/DiscreteLog/GroupHash.lean) instantiates it with the Katz–Lindell discrete-logarithm hash (`DiscreteLog.collisionResistantForOn_groupHash`, exact zero-loss reduction for the encoded outputs; fixed digest width, compression and efficient setup are not established) |
| Target collision resistance | [CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean](../../CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean), [CslibFrontier/Crypto/Computational/NaorYung.lean](../../CslibFrontier/Crypto/Computational/NaorYung.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Two-stage pre-key target choice and post-key second-preimage search; polynomial key/block schedules, fixed-depth `2^n`-capacity tree extension, Naor–Yung UOWHFs from `OneWayPermutation`, and Rompel–HHRVW UOWHFs from `OneWay` |
| Inaccessible entropy and shrinking collision grids | [CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Fixed-width native polynomial evaluation, accessible preimage subsets with eventual `1 / denom n` entropy gap, polynomial-size grids of `1`-bit shrinking candidates with an existential random-collision-resistant sequence (`exists_good_candidate`), and uniform `gridCount n`-way cascade concatenation |
| Discrete logarithm and DDH | [CslibFrontier/Crypto/Computational/DiscreteLog.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiscreteLog.lean), [CslibFrontier/Crypto/Computational/DiffieHellman.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiffieHellman.lean) | Encoded prime-order group families, exact ideal group laws; public operations and samplers require separate certificates |
| Decisional composite residuosity and Paillier encryption | [CslibFrontier/Crypto/Computational/CompositeResiduosity.lean](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean), [CslibFrontier/Crypto/Computational/Paillier.lean](../../CslibFrontier/Crypto/Computational/Paillier.lean), [CslibFrontier/Crypto/Computational/Paillier/Security.lean](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean) | Factor pairs `(p, q)` of balanced moduli with validity in the type; arbitrary setup law; Paillier encryption with perfect correctness and plaintext-addition preservation under decryption over an abstract strict-PPT modulus generator, which is not constructed; IND-CPA security under DCR with an explicit prime-growth hypothesis |
| Quadratic residuosity, Goldwasser–Micali, RSA, and Rabin factoring | [CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [CslibFrontier/Crypto/Computational/GoldwasserMicali.lean](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean), [CslibFrontier/Crypto/Computational/RSATrapdoor.lean](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), [CslibFrontier/Crypto/Computational/RabinFactoring.lean](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) | Composite Jacobi symbol `jacobiSymbol`, `QR_N` / `QNR_N^{+1}` split and `QuadraticResiduosityHard`; Goldwasser–Micali bit and bounded-word public-key encryption (`KeyDesc`, `encrypt`, `decrypt`, `mulCiphertexts`, ideal distributional XOR homomorphism, `INDCPA` / `INDCPAOn` under `QuadraticResiduosityHard` and explicit prime growth, and Jacobi `-1` attack); all-residue and unit-group RSA trapdoor bijection (`rsaEval`, `rsaInvert`, `RSAOneWay`); Blum-integer square roots (`blumSqrt`, `crtSqrt`), `FactoringHard`, `RabinOneWay`, and explicit PPT equivalence `rabinOneWay_iff_factoringHard` |
| LWE, SIS, and module lattices | [CslibFrontier/Crypto/Computational/LWE/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/LWE/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/SIS/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Module.lean](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), [CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean) | Explicit dimensions, modulus and noise/norm parameters (`2^w` binary matrix words in `Basic.lean`, arbitrary `[NeZero (q security)]` moduli, Ajtai collision extraction, negacyclic `R_q = ℤ_q[X]/(X^n+1)` block-anticirculant expansion `expandModuleMatrix`, `ModuleSIS`, `RingSIS`, and `DecisionModuleLWE` in `SIS/Module.lean`, and dual-Regev `ModuleLWE` public-key encryption in `SIS/ModuleEncryption.lean`); classical uniform-PPT hardness hypotheses |

For a one-bit expanding PRG, [Stretch/Prefix.lean](../../CslibFrontier/Crypto/Computational/Stretch/Prefix.lean)
proves that `(forwardIterate g ℓ seed).take ℓ` has length `ℓ` and agrees with the first `ℓ`
emitted bits of every longer run. The premise is global: `length (g seed) = length seed + 1`
for every seed, including the empty word. The complete `forwardIterate` output also retains a
reversed final seed and is not prefix-consistent. Native computation charges both the seed and
unary `ℓ`; for each uniform native length schedule `L n`, the emitted `L n`-bit prefix from a
uniform `n`-bit seed is computationally indistinguishable from `uniformList (L n)`, by existing
stretch security and reverse/take postprocessing. [PRGStretch clients](../../CslibFrontierTests/PRGStretch.lean)
check zero widths, order-sensitive output, and native XOR encryption/recovery. This is the emitted-pad
prerequisite for the stream-cipher route of Boneh–Shoup §3.2 [bs23][bs23]; adaptive arbitrary-word
one-time encryption and hash-then-MAC/EtM remain open in [#2749](https://github.com/cslib-community/cslib-frontier/issues/2749).

Several independently keyed copies of a pseudorandom function are again pseudorandom: [`PseudorandomFunction.multiKey`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/MultiKey.lean) answers `t` word channels with the `n`-bit blocks of one `t * n`-bit key, against `t` independent random functions, for every fixed `t`. Its hybrid reduction `prfMultiReduction` simulates the already random channels with a lazy list cache and is itself oracle PPT; the concrete bound sums `t` PRF advantages (Boneh–Shoup, Exercise 4.26). The number of keys is a constant, not a function of the security parameter; the exercise also allows a polynomially bounded number of keys, which this theorem does not cover.

Unconditionally, any pseudorandom function on `n`-bit inputs requires at least `2 * n - 2` binary gates over the full binary Boolean basis `B₂` (`fullInterpretation (k := 2)`) on all but a negligible fraction of keys (Fan–Li–Yang §§4.2, 7.1, Theorem 7.5 [fly22][fly22]): [`CircuitLowerBound.lean`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/CircuitLowerBound.lean) proves the bound both for arbitrary `BooleanPRF` ensembles (which impose no efficient sampling or evaluation condition) and for word-valued `PseudorandomFunction` families via deterministic `BitString.lowBits`-encoded restriction queries. The underlying wire out-degree, syntactic dead-gate elimination (`Circuit.NoDeadGates`), critical-path `2 * n - 2 * m` gate bound, and `B₂` intersection bottleneck live in [`CslibFrontier/Computability/Circuit/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/CriticalPath.lean) and [`CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean). Tightness at `2 * n - 2`, distinguisher completeness, refutation of bitwise XOR, unconditional `BooleanPRF` non-vacuity on random functions, and conditional `OneWay` non-vacuity are checked in [`CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean`](../../CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean).

The main uniform construction chain is [OneWay.exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRG.lean#L54), [exists_oneWay_iff_exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PRGToOneWay.lean#L215), polynomial stretch, and [OneWay.exists_pseudorandomFunction](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRF.lean#L46). The formal abstract [hill](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/CslibFrontierAbstracts/CryptographyAbstract.lean#L81) (since retired) stated the one-bit expansion endpoint, and `adaptive_functions` stated the adaptive PRF endpoint, as restatements of `OneWay.exists_pseudorandomGenerator` and `OneWay.exists_pseudorandomFunction`. The forward generator proof follows the Holenstein pseudoentropy route to the Håstad–Impagliazzo–Levin–Luby theorem; the function construction follows Goldreich–Goldwasser–Micali. The cited primary sources establish the classical OWF/PRG and adaptive function-construction results [hill99][hill99] [holenstein06][holenstein06] [ggm86][ggm86]. The uniform Lean endpoint does not assume an extra entropy or nonuniform-advice premise. In parallel, relativizing the Holenstein pseudoentropy, three-source, entropy-grid, XOR-combination and reindexing pipeline to polynomially bounded advice families yields the nonuniform construction chain [`NonuniformOneWay.exists_nonuniformPRG`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L68) (one-bit stretch) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L77) (length-tripling `3 * n + 1` stretch) from any [`NonuniformOneWay`](../../CslibFrontier/Crypto/Computational/Nonuniform/Basic.lean#L304) function.

Target collision resistance (universal one-wayness) separates target selection from key sampling: in [`TargetCollisionResistant.lean`](../../CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean), `TargetCollisionFinder.choose` commits to `(m₀, state)` from `1^n` before a uniform `keyLen n`-bit key is drawn, and `TargetCollisionFinder.find` receives `(1^n, state, k)` to output `m₁` (Boneh–Shoup §8.11.2, Attack Game 8.5 and Definition 8.7 [bs23][bs23]; Naor–Yung §2 [naoryung89][naoryung89]; Goldreich §6.4.3 [goldreich04][goldreich04]). Full collision resistance implies target collision resistance with identical game success probability (`CollisionResistantOn.targetCollisionResistantOn`). Because single-key Merkle–Damgård requires the key to compute intermediate chaining targets, domain extension from `KeyedCompressionFamily` (`2M(n) → M(n)` with `n ≤ M(n)`) to unrestricted `KeyedHashFamily` on `List Bool` instead uses `uowhfTreeHash`, a total fixed-depth adaptation of level-keyed binary-tree hashing (Naor–Yung 1995 revision §2.3 [naoryung89][naoryung89]; Goldreich June 2003 chapter draft §6.4.3.2, Constructions 6.4.24/6.4.26 and Propositions 6.4.25/6.4.27 [goldreich04][goldreich04]; cf. Boneh–Shoup §8.11.3, pp. 339–340 [bs23][bs23], which instead presents a chain that reuses one compression key with `1 + log₂ L` XOR masks, so that its key is logarithmic in the message length, and mentions a tree-based alternative): `uowhfLeaves` encodes one message bit per zero-padded `M(n)`-bit leaf, `uowhfTreeLevels` folds `n` fixed halving levels under independent subkeys, `top.headD []` selects the first resulting block, and an `(n + 1)`-st subkey compresses that block with `BitString.lowBits (M n) msg.length` (`msg.length mod 2^{M(n)}`). At fixed `n`, inputs longer than `2^n` bits leave multiple blocks in `top` and `top.headD []` discards the extra roots (so out-of-capacity messages such as `[false, false, false]` and `[false, false, true]` at `n = 1` collide), whereas `KeyedCompressionFamily.targetCollisionResistant_treeHash` still holds on unrestricted `List Bool` because strict-PPT admissibility polynomially bounds the output lengths of both `choose` and `find`, placing supported `m₀` and `m₁` strictly below `2^n ≤ 2^{M(n)}` for all sufficiently large `n`; [`CslibFrontierTests/Crypto/TargetCollisionResistant.lean`](../../CslibFrontierTests/Crypto/TargetCollisionResistant.lean) gives checked instances, collision extractions and insecurity witnesses. In [`NaorYung.lean`](../../CslibFrontier/Crypto/Computational/NaorYung.lean), any `OneWayPermutation` instantiates that compression interface without trapdoors (adapting Naor–Yung §3 [naoryung89][naoryung89] and Goldreich June 2003 draft §6.4.3.2, Construction 6.4.20 and Proposition 6.4.21 [goldreich04][goldreich04]): `naorYungShrink` quotients `{0, 1}^{n+2}` by `{0, δ}` via pivot-bit canonicalization and deletion rather than an affine/Toeplitz matrix so `naorYungStep` reduces to `inversionGame` at length `n + 2` with exact loss `1` and zero additive error, `naorYungCompression` cascades `n + 1` steps (`2(n + 1) → n + 1`) with loss `dyadicSize (n + 1)`, and `naorYungHash` composes with `KeyedCompressionFamily.treeHash` (`OneWayPermutation.targetCollisionResistant_naorYungHash`, `OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`; client checks and an explicit `1 / 2`-success break of `naorYungStep id` are in [`CslibFrontierTests/Crypto/NaorYung.lean`](../../CslibFrontierTests/Crypto/NaorYung.lean)).

For universal one-way hashing from general one-way functions without permutations, [`OneWay.exists_inaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean) constructs an [`InaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean) with gap denominator `denom n = 64 * (n + 1)` from any uniform `OneWay` function, proving a weaker constant-threshold adaptation of Haitner–Holenstein–Reingold–Vadhan–Wee, Section 4.2, Theorem 4.5 [hhrvw20][hhrvw20] via the `3`-wise independent Boolean affine hash family [`isThreeWiseIndependentHash_affineHash`](../../CslibFrontier/Probability/BitString/AffineHash/ThreeWise.lean) and prefix-collision seed projection `adjustAffineSeed`: whereas the paper uses threshold `2^(n - i) / n^c` to achieve gap `d log n / n` for every constant `d > 0` under Definition 3.9, the Lean construction fixes one adversary-independent accessible-set family against uniform strict-PPT adversaries, encodes the prefix length in a dyadic `(Nat.log 2 n + 1)`-bit saturating field, and uses constant threshold `2^(n - min r n) / 4` to obtain the smaller inverse-linear gap `1 / (64 * (n + 1))`. Parallel repetition with Hoeffding concentration and dyadic planted-coordinate escape reductions ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean), Lemma 5.3) combined with two-universal input/output hashing for `1`-bit shrinkage ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean), Lemmas 5.4 and 5.5) then yield [`InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) and [`OneWay.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (Section 5.1.5, Theorem 5.1, STEPS 1–3), producing a [`ShrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) of uniformly polynomial-time `1`-bit shrinking candidates containing an existential candidate sequence (`exists_good_candidate`) collision-resistant on random inputs (`randomCollisionGame`). Although that existential index `goodIdx n` need not be efficiently computable, [`rompelCompression`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) evaluates all `gridCount n` candidates uniformly across `rompelCascadeSteps G n = (2 * gridCount n - 1) * outLen n` XOR-masked `1`-bit shrinking steps under one shared `rompelCascadeSteps G n * inLen n`-bit step-key sequence and concatenates their outputs (`2 * (gridCount n * outLen n) → gridCount n * outLen n`; adapting [hhrvw20][hhrvw20] Section 5.1.4, Lemmas 5.6–5.7, pp. 29–30, and Section 5.1.5, STEP 4, p. 31, and STEP 5(ii–iii), p. 32, using one fresh `inLen n`-bit subkey per `1`-bit step and sharing that sequence across candidates rather than claiming Lemma 5.7's `O(|y| log t)` compact-key bound or STEP 5(iii)'s per-candidate keys), with single-stage planted-subkey reduction `rompelCompressionInverter` achieving exact key simulation at multiplicative loss `dyadicSize (gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero additive error (`ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`, `OneWay.exists_targetCollisionResistant_keyedCompressionFamily`). Composing with `KeyedCompressionFamily.treeHash` yields `rompelHash` and `OneWay.exists_targetCollisionResistant_keyedHashFamily` ([rompel90][rompel90]; [hhrvw20][hhrvw20] Section 5.1, Theorem 5.1, p. 25), with concrete checks in [`CslibFrontierTests/Crypto/InaccessibleEntropy.lean`](../../CslibFrontierTests/Crypto/InaccessibleEntropy.lean) and [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean).

The polynomial interpretation of the module-lattice coefficient vectors is proved in
[`SIS/Polynomial.lean`](../../CslibFrontier/Crypto/Computational/SIS/Polynomial.lean).
For `n ≠ 0` and a nontrivial commutative ring `R`, `negacyclicEquiv` identifies `Fin n → R`
with Mathlib's `AdjoinRoot (X^n + 1)` as an `R`-module, and `negacyclicEquiv_mul` carries
`negacyclicMul` to quotient multiplication. Use the equivalence's injectivity to reflect
quotient equalities back to coefficient vectors. `negacyclicEquiv_moduleSISMap` transports the
existing Module-SIS map to a quotient-ring matrix product. The checked examples in
[`NegacyclicPolynomial.lean`](../../CslibFrontierTests/Crypto/NegacyclicPolynomial.lean) include
integers, composite modulus `6`, characteristic `2`, dimension `1`, and reflection of the
Module-SIS zero equation. The source function type retains pointwise multiplication; use
`negacyclicMul` for polynomial multiplication. Dimension zero is excluded because its quotient
is `R/(2)`. This algebraic bridge adds no hardness or runtime claim.

The pure coefficient identity `negacyclicMul_eq_coeff_mul` is available separately in
[SIS/Polynomial/Coefficients.lean](../../CslibFrontier/Crypto/Computational/SIS/Polynomial/Coefficients.lean),
so algebra clients need not import native computation certificates. For native multiplication, import
[SIS/Native.lean](../../CslibFrontier/Crypto/Computational/SIS/Native.lean).
`negacyclicMulResidues n q a b` truncates two natural-coefficient lists to `n`, computes the
existing integer `mulZJet (2*n)`, and reduces each lower coefficient minus its wrapped upper
coefficient modulo `q`. Short lists are zero-padded and the output has exactly `n` entries.
The plain certificate charges unary `n`, binary `q`, and both complete framed binary input
lists. It imposes no coefficient-size bound. For `q > 0`, `negacyclicMulResidues_ofFn` identifies
the output with the canonical coefficients of the existing `negacyclicMul`; neither primality
nor positive dimension is needed. At `q = 0`, the total operation instead truncates each
signed result at zero, with no canonical-residue interpretation claimed.
The [checked clients](../../CslibFrontierTests/Crypto/NegacyclicNative.lean) include `X² = -1`
modulo six, modulus one, empty and irregular inputs, a 128-bit modulus, and the actual
rank-one `moduleLWEKeyGen` coefficient computation. Full native encryption, seed codecs and
small-secret security still remain separate obligations. This arithmetic certificate does not
remove the existing restrictions on exact native samplers or imply small-secret security.

These are implications from hardness assumptions. They do not prove that a concrete OWF, DDH group, LWE family or SIS parameter choice is hard. The LWE interface exposes only the serialized public matrix `[B*t+e | B]`, with independent errors and one shared uniform secret; in [`SIS/Module.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), `expandModuleMatrix` and `flattenPolyVec` embed negacyclic `ModuleSIS` and `ModuleLWE` instances over `ℤ_q[X]/(X^n+1)` into unstructured `(d * n) × (k * n)` matrices over `ℤ_q` (checked with concrete evaluations and nonvacuity proofs in [`CslibFrontierTests/Crypto/ModuleSIS.lean`](../../CslibFrontierTests/Crypto/ModuleSIS.lean)), and [`SIS/ModuleEncryption.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean) builds dual-Regev public-key encryption (`moduleLWEKeyGen`, `moduleLWEEncrypt`, `moduleLWEDecrypt`), bounded-noise decryption correctness (`moduleLWEDecrypt_moduleLWEEncrypt_eq`), and two-hop public-key/ciphertext reductions to `ModuleLWE.sampleLaw` (`advantage_realEncryptionView_uniform_le`, `advantage_realEncryptionView_msg_le`, checked in [`CslibFrontierTests/Crypto/ModuleEncryption.lean`](../../CslibFrontierTests/Crypto/ModuleEncryption.lean)); no worst-case lattice reduction is asserted there.

For deterministic native key generation, import
[`ModuleEncryption/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Native.lean).
`exists_computableInPolyTime_moduleLWEKeyGen` supplies one total word function with a plain
polynomial-time certificate and exact agreement with `ModuleLWE.encodeSample (moduleLWEKeyGen …)`.
Both rank and polynomial degree are unary inputs; the positive modulus and signed secret/error
coefficients are binary. The public matrix input uses `ModuleSIS.encodeMatrix`: its structured
`(k*n)`-square rotation-block expansion is already present. Runtime charges that complete matrix
word, both complete framed signed lists and the dimensions; it does not assume a seed codec.
The implementation reuses total framing/number decoders and the upstream padded list dot product,
then reduces each integer coordinate modulo `q`. Short rows/vectors pad with zero and excess
entries are ignored, but still contribute to input length. Canonical equality requires `q > 0`;
there is no assertion that malformed words are rejected. [Checked clients](../../CslibFrontierTests/Crypto/ModuleKeyGenNative.lean)
use the same certified function for rank two, degree two, composite modulus six, signed wraps,
modulus one, zero dimensions and a 129-bit modulus. The structured matrix sampler below supplies
its public matrix input, and the joint sampler below composes the actual secret/error samplers.
Full native encryption, seed compression and security remain separate obligations.

For deterministic native decryption, `exists_computableInPolyTime_moduleLWEDecrypt` in
[`ModuleEncryption/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Native.lean)
supplies one total word function with a plain polynomial-time certificate and exact agreement with
`List.ofFn (moduleLWEDecrypt …)`. Unary rank `k`, unary degree `n`, and binary modulus `q` are
runtime inputs; secret coordinates use `ModuleSIS.encodeVec` over signed integers, and the ciphertext
uses `GeneralSIS.encodeMatrix (extendCiphertext ct)`. Decryption evaluates each secret polynomial's
canonical residues modulo `q`, performs negacyclic multiplication against each ciphertext polynomial
using the certified integer negacyclic engine, sums polynomial columns, and applies centered threshold
decoding `decodePolyMsg` on canonical natural coefficients. The private implementation pads missing
coefficients and rows with zero, ignores excess entries while charging their input length, and at
modulus zero or on incomplete framing remains total without asserting quotient-ring semantics.
In-source checks and [checked clients](../../CslibFrontierTests/Crypto/ModuleEncryptionNative.lean) verify
honest Ring-LWE and Module-LWE encryption/decryption, rank zero, degree zero, modulus zero, modulus
one, incomplete framing, and threshold edge cases where residue differences of `q / 4` and `q / 4 + 1`
decode to `false` and `true`. Full native encryption, seed codecs, and security reductions under native
sampling remain separate obligations.

The structured matrix input itself now has a native constructor and exact sampler in
[`SIS/Module/MatrixSampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module/MatrixSampling.lean).
`exists_computableInPolyTime_encodeModuleMatrix` supplies one total implementation of the existing
`ModuleSIS.encodeMatrix`, from rectangular nested coefficient lists, unary row/rank/degree and a
binary modulus. Its canonical identity assumes `q > 0`; zero dimensions and modulus one are
included. The private implementation pads missing coefficients with zero, ignores excess entries
while charging their input length, and uses the actual negative wrap of `rotMatrix`. At modulus
zero it remains total, without a canonical residue interpretation.
`exists_isPPTOn_sampleEncodedModuleMatrix` samples independent polynomial coefficients using
`sampleBinaryNat w`, then performs that certified expansion. Its exact law is uniform on the
original polynomial matrix over `ZMod (2 ^ w)` followed by `ModuleSIS.encodeMatrix`, for unary
dimensions and bit width, including width zero. The expanded scalar entries are correlated. [Tests](../../CslibFrontierTests/Crypto/ModuleMatrixSampling.lean)
check a rectangular modulus-six expansion, empty shapes, a 129-bit modulus, and a nonrotation
matrix with zero structured-sampler mass but positive independent-scalar-uniform mass. They also
compose the same obtained sampler with the native key generator: the composition is strict PPT
for runtime dimensions/width and complete supplied signed secret/error words, and its concrete
conditional law agrees with the existing key generator. The joint sampler below supplies the
random secret and error, and deterministic native decryption is certified above by
`exists_computableInPolyTime_moduleLWEDecrypt`; native encryption, seed codecs and security
remain separate tasks.

For arbitrary positive binary moduli, including primes, import
[`Module/ApproximateSampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module/ApproximateSampling.lean).
`exists_isPPTOn_approximateEncodedModuleMatrix` gives one strict-PPT program using the existing
`sampleModNat width q` independently on each polynomial coefficient, then the same native
rotation-block expansion. Its exact law is the nested product of those actual residue laws
followed by `ModuleSIS.encodeMatrix`. Its all-event `CloseTo` error against the ideal structured
uniform law is at most `d*k*n*q/2^width`. The count is the number of independent polynomial
coefficients; expanded scalar entries remain correlated. The modulus is binary, dimensions and
width unary, and the program is total even at modulus zero, outside the positive-modulus law.
`exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision` computes width `q.size + precision`
natively and gives error at most `d*k*n/2^precision`, with unary precision and binary modulus.
Neither theorem asserts exact uniform sampling for arbitrary moduli.

[Checked clients](../../CslibFrontierTests/Crypto/ModuleMatrixApproximation.lean) show that four fair
bits reduced modulo three give the encoded zero two-coefficient block mass `9/64`, whereas the
ideal structured law gives `1/9`. The bound is `3/8`. The same obtained sampler and native keygen
function compose uniformly on runtime dimensions, binary modulus and complete supplied secret
and error words; deterministic keygen postprocessing preserves that error against the existing
ideal conditional key law. Other clients cover width zero, modulus one, empty dimensions and a
129-bit modulus. The joint sampler below completes secret/error composition; native encryption
and security remain open.
The scalar all-event bridge `Probability.closeTo_uniform_sampleModNat` in
[`Game/CloseTo/UniformNat.lean`](../../CslibFrontier/Crypto/Game/CloseTo/UniformNat.lean) bounds the
sampled residue law against uniform `ZMod q` within `q / 2^width`.

For full randomized key generation, import
[`ModuleEncryption/Sampling/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling/Native.lean).
`exists_isPPTOn_moduleLWEKeyGenJoint` supplies one native program before choosing rank `k`, degree
`n`, secret/error CBD widths, precision and modulus. It returns an ordinary pair of the existing
`ModuleSIS.encodeVec` signed-secret word and `ModuleLWE.encodeSample` public-key word. The secret
is the actual integer CBD draw; reducing its decoded coefficients modulo `q` gives exactly the
secret used to generate that public key, including when residues wrap. No no-wrap assumption or
additional secret codec is introduced. Dimensions, CBD widths and precision are unary runtime
inputs; the modulus is binary. The certificate charges all generated signed words, the full
expanded structured matrix, public output and framing.

The exact implemented joint law uses the existing CBD programs and bounded modular coefficient
sampler. Its all-event error from the ideal joint experiment is at most `k*k*n/2^precision`:
retain the same signed secret, then use `moduleLWEPublicKeyLaw` conditional on its residue and
with actual independent CBD polynomial errors. The theorem also bounds the public projection
against the existing generalized public-key law. Exact secret/error sampling adds no error to
the matrix bound. The program is total, with semantic claims requiring only `q > 0`.
[Checked clients](../../CslibFrontierTests/Crypto/ModuleKeyGenJoint.lean) use the same obtained witness
for a prime-three event with secret `-1`, matrix coefficient `1` and public coefficient `0`,
forcing nonzero error `1`. Its actual mass is `5/256` versus ideal `1/48`, a gap of `1/768`.
The same witness covers zero widths, modulus one, both empty shapes and a rank-two/degree-two
129-bit-modulus instance. These are key-sampling and execution statements (deterministic native
decryption is certified by `exists_computableInPolyTime_moduleLWEDecrypt`); native encryption, seed
codecs and small-secret security remain separate obligations.

The Module-LWE sampling APIs now accept explicit distributions: `moduleLWEPublicKeyLaw` has an
optional `secretLaw`, `encryptionViewOfKeyLaw` an optional `ephemeralLaw`, and `realEncryptionView`
accepts both. Their defaults remain uniform, and the existing security reductions concern those
uniform defaults. [`ModuleEncryption/Sampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling.lean)
proves that conditioning public-key generation on the actual sampled secret preserves the public
view, including when the same run retains `(secret, view)`. Sampling a fresh secret independently
of a public key would not preserve that correlation.
The concrete small-secret instance reuses the existing centered-binomial fair-bit program and
modular `GSW.noiseLaw`. Under `2*η < 2^w`, every sampled integer is its residue's centered lift,
so the resulting module secret satisfies the coefficient bound `η`. Nested list sampling has a
uniform strict-PPT certificate for unary row count, degree and binomial width, with binary signed
integer output. The subsequent modular-cast identity is semantic; this is not a native certificate
for the whole encryption scheme. [Tests](../../CslibFrontierTests/Crypto/ModuleEncryptionSampling.lean)
include nonzero supported secrets, zero dimensions/width, and a variable-row native client.
They also show that uniform rank-one, degree-one secrets and ephemeral values modulo sixteen,
with all errors one, decrypt a true message correctly with probability only `7/16`.
The existing deterministic correctness theorem requires bounded secrets as well as bounded noise;
this example does not contradict it. Small-secret security requires its own assumption and reduction;
the randomized correctness result below uses explicit support and noise-tail hypotheses.

For numerical modulus conversion, import
[`SIS/ModulusSwitch.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch.lean).
`moduleLWEModulusSwitch p ct` converts the existing ciphertext components with the reusable
[`ZMod.modulusSwitch`](../../CslibFrontier/Foundations/Data/ZMod/ModulusSwitch.lean): take
`valMinAbs`, multiply by the rational ratio `p / q`, round to the nearest integer with half
ties toward positive infinity, and reduce modulo `p`. It is not a ring homomorphism.
For `q,p > 0`, `exists_moduleLWEModulusSwitch_phase` supplies an integer representative of
the target phase whose distance from the scaled canonical source phase is at most
`(1 + ∑ j, ∑ l, |s j l|) / 2`. The secret at both moduli is the cast of the same integer
vector. The representative supplied at the target need not be its centered lift.
`exists_moduleLWEModulusSwitch_phase_of_lifts` exposes arbitrary integer lifts and their
carry equation; the canonical theorem constructs these carries automatically.
The [checked examples](../../CslibFrontierTests/Crypto/ModulusSwitch.lean) cover negative half
ties, composite moduli, modulus one, nonadditivity, and a ciphertext with nonzero carry.
This nearest-integer phase bound is original supporting algebra; it does not assert Boolean
plaintext preservation, parity-preserving switching, a security reduction, or a runtime bound.

For its native implementation, import
[`SIS/ModulusSwitch/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Native.lean).
`ZMod.modulusSwitchResidue q p x` computes the rounded integer by signed Euclidean division
`(2*p*x + q) / (2*q)`, then reduces it to a natural residue modulo `p`.
`modulusSwitchResidue_eq_val` identifies that result with the existing coefficient switch for
positive moduli, including negative half ties. The plain `intBin_roundScale` and
`ComputableInPolyTime.modulusSwitchResidue` certificates use binary `encNat` moduli and signed
binary `encIntBin` representatives; they reuse the existing signed division and remainder
certificates. `computableInPolyTime_modulusSwitchRows` lifts the implementation to arbitrary
runtime nested rows in `encList (encList encNat)`. Dimensions vary through the actual list
structure, and the polynomial bound counts the complete encoded input. The
`modulusSwitchRows_encodeMatrix_extendCiphertext` theorem identifies the output with
`GeneralSIS.encodeMatrix (extendCiphertext (moduleLWEModulusSwitch p ct))`, so there is no
separate ciphertext format. The [native tests](../../CslibFrontierTests/Crypto/ModulusSwitchNative.lean)
exercise a 128-bit modulus, negative representatives, modulus one, ragged/empty rows, the
existing ciphertext encoding, and composition of two certified conversions. This runtime
certificate adds no decoding or security guarantee.

For sufficient plaintext-preserving margins, import
[`SIS/ModulusSwitch/Correctness.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Correctness.lean).
Suppose the actual source phase is `encodePolyMsg q m + err`, with integer error bounded by
`Bq`, and use the same integer secret at both moduli. Write `S` for its coefficient absolute-value
sum and `Δ = |(p/q) * floor(q/2) - floor(p/2)|`. If
`(p/q) * Bq + (1+S)/2 + Δ ≤ Bp` and `4*Bp+2 < p`, then
`moduleLWEDecrypt_modulusSwitch_eq` proves that the switched ciphertext decrypts to `m`.
The source modulus need only be positive for that conclusion. The separate
`moduleLWEDecrypt_modulusSwitch_eq_source` adds `4*Bq+2 < q` to derive equality of the actual
source and target decryptions. These sufficient margins are not claimed optimal.
The error theorem constructs its target representative from the phase bound, including source
carries, rather than assuming a decoding conclusion. `moduleLWEDecrypt_modulusSwitch_encrypt_eq`
applies it to honest encryption using the existing integer error polynomial and centered secret.
The exact scale mismatch is zero for two even moduli, `1/2` for even source and odd target,
`p/(2*q)` for odd source and even target, and `|1-p/q|/2` for two odd moduli.
[Checked examples](../../CslibFrontierTests/Crypto/ModulusSwitchCorrectness.lean) apply the honest
encryption theorem in all four cases with nonzero noise, and exercise negative half ties and a
nonzero carry. They also show plaintext loss at target moduli one and two and failure at the
strict decoder threshold. This is deterministic correctness, with no additional security claim.

For randomized correctness, import
[`SIS/ModulusSwitch/Failure.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Failure.lean).
`toOuterMeasure_moduleLWEModulusSwitch_failure_le` uses the existing encryption view while
retaining the actual secret that generated the public key. Suppose the secret and ephemeral laws
are supported in centered coefficient bounds `Bs,Br`, and write `ν` for the polynomial-noise law.
Set `Q = k*n*Be*Br + k*n*Be*Bs + Be`. For positive source modulus `q`, target margin `4*Bp+2 < p`,
and `(p/q)*Q + (1+k*n*Bs)/2 + Δ ≤ Bp`, switched decryption fails with probability at most
`(2*k+1) * ν{e | e exceeds centered coefficient bound Be}`. The count is `k` key-error
polynomials, `k` encryption-error polynomials and one final polynomial, each sampled independently
as in the existing view. The proof reuses the deterministic theorem and the product-event union
bound; it assumes neither a decryption conclusion nor a source decoding margin.
[Checked clients](../../CslibFrontierTests/Crypto/ModulusSwitchFailure.lean) use the native
centered-binomial small-secret law for rank and degree one, switching from 32 to 16. Width-one
errors give zero failure. Width-two errors exceed good radius one with exact probability `1/8`,
giving an upper bound `3/8`; a supported error triple produces target phase 12 and proves positive
actual failure. These are original sufficient correctness bounds for the supplied laws. They add
no small-secret security reduction, Gaussian sampler or native certificate for the entire scheme.

For a concrete growing family, [ModulusSwitch/CenteredBinomial.lean](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/CenteredBinomial.lean)
sets `t = l+1`, rank and degree `t`, CBD1 secret/ephemeral coefficients, and CBD(8t) error
coefficients with good radius `4t`. Put `Q = 8t³+4t`, `Bp = floor((Q+t²+2)/2)`,
`w = Nat.size(4Bp+2)`, target `p = 2^w` and source `q = 2^(w+1)`.
The proved bounds are `p ≤ 68t³`, `q ≤ 136t³`, strict no-wrap `16t < q`, and target
margin `4Bp+2 < p`. Half scaling and even moduli make the message-scale mismatch zero.
The actual retained-secret experiment fails with probability at most `4(2t+1)t exp(-t)`,
which is negligible for every message family. The extra factor `t` counts coefficients inside
each noise polynomial; the shared coefficient bound lives in
[Sampling/Concentration.lean](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling/Concentration.lean).
The [checked clients](../../CslibFrontierTests/Crypto/ModulusSwitchCenteredBinomial.lean)
certify growing native CBD rows and power-of-two uniform matrix-entry samples, with unary
parameters and binary outputs, and check their semantic modular laws. They also prove positive
actual failure at `t=1`: `q=64`, `p=32`, errors all eight and supported secrets produce phase 29
and decode a true message incorrectly. The displayed bound is below one at `t=10`.
This is correctness for explicit laws, not a small-secret security reduction. Deterministic
unswitched native key generation and decryption (`exists_computableInPolyTime_moduleLWEKeyGen`,
`exists_computableInPolyTime_moduleLWEDecrypt`), randomized CBD key generation
(`exists_isPPTOn_moduleLWEKeyGenJoint`), and coefficient conversion in
[`ModulusSwitch/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Native.lean)
are certified above; native encryption, switched-decryption assembly and seed codecs remain
separate.

Discrete-logarithm and factoring cryptanalysis lives in two algebra-level modules. Import
[`DiscreteLog/PohligHellman.lean`](../../CslibFrontier/Crypto/Computational/DiscreteLog/PohligHellman.lean)
for the Pohlig–Hellman subgroup reduction and CRT uniqueness (`pohligHellman_subgroup_modEq`,
`pohligHellman_crt_modEq`), the prime-power digit step (`pohligHellman_step`), the smooth/rough
trial-division split (`smoothDivisorSeq`, `coprime_smoothDivisorSeq_div`) and composite-order CRT
extraction from two Schnorr transcripts (`extractModRough`, `crtCombine`,
`crtCombine_extractModRough_eq`). These are correctness identities under explicit positivity,
divisor, inverse and range hypotheses; there is no executable Pohlig–Hellman solver, subgroup
discrete-log solver or running-time bound. Import
[`Factoring/PollardRho.lean`](../../CslibFrontier/Crypto/Computational/Factoring/PollardRho.lean) for
`rhoFactorLoop N F B x y`, a `B`-step Floyd loop over a caller-supplied walk on `(ZMod N)ˣ`. Every
`some d` output is a nontrivial factor (`isNontrivialFactor_of_rhoFactorLoop_eq_some`), `none` is
characterized exactly (`rhoFactorLoop_start_eq_none_iff`), and `floyd_cycle_modEq` turns a
modulo-`p` collision into a tortoise-and-hare meeting modulo `p`. That meeting need not give a
distinct pair modulo `N`; the heuristic success probability and `O(N^{1/4})` running time are not
formalised, and the bounded loop has no native cost certificate. The
[checked examples](../../CslibFrontierTests/Crypto/GroupCryptanalysis.lean) run Katz–Lindell's
Example 10.5 in `(ZMod 31)ˣ`, CRT recombination for `12 = 4 * 3`, and
`rhoFactorLoop 15 walk15 4 1 1 = some 3`.

For composite-modulus number-theoretic hardness assumptions, import [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), and [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], §§9.2.3–9.2.4, §15.1.1, §§15.4.1–15.4.3, and §§15.5.1–15.5.2; checked examples and reduction clients are in [`CslibFrontierTests/Crypto/QuadraticResiduosity.lean`](../../CslibFrontierTests/Crypto/QuadraticResiduosity.lean), [`CslibFrontierTests/Crypto/RSATrapdoor.lean`](../../CslibFrontierTests/Crypto/RSATrapdoor.lean), and [`CslibFrontierTests/Crypto/RabinFactoring.lean`](../../CslibFrontierTests/Crypto/RabinFactoring.lean)). In [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean) ([katzlindell20][katzlindell20], Proposition 15.23 and Definition 15.27), quadratic residues reuse Mathlib's `IsSquare` and `Subgroup.square` (`Subgroup.mem_square`, `mem_quadResidueSet_iff`), `jacobiSymbol p q` multiplies the Legendre symbols on `(ZMod (p * q))ˣ`, `jacobiPosSet_eq_disjoint_union` and `card_quadResidueSet_eq_card_positiveNonresidues` partition `J_N^{+1}` into equal-sized `quadResidueSet` (`QR_N`) and `positiveNonresidues` (`QNR_N^{+1}`) for distinct odd primes `p ≠ q`, `blumSqrt p q` inverts squaring on `QR_N` for Blum moduli `IsBlumModulus p q` (`blumSqrt_sq`, `sq_bijOn_quadResidueSet`, `neg_one_mem_positiveNonresidues`), and `QuadraticResiduosityHard` compares `qrRealGame` against `qrIdealGame`. In [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean) ([katzlindell20][katzlindell20], Definitions 9.46 and 15.1), `rsaEval N e x = x ^ e % N` and `rsaInvert N d y = y ^ d % N` are certified in polynomial time (`computableInPolyTime_rsaEval`, `computableInPolyTime_rsaInvert`) and proved mutually inverse across all residues `x < N` (`rsaInvert_rsaEval`, `rsaEval_rsaInvert`), inducing bijections both on `Fin N` (`rsaEval_bijective_fin`, including nonunits dividing `p` or `q`) and on `(ZMod N)ˣ` (`rsaEval_bijective_units`), with `rsaInversionGame` sampling `x` uniformly from `Fin desc.modulus` (`RSAOneWay`, whereas Definition 9.46 samples uniformly from `(ZMod N)ˣ`). In [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], Definition 9.45, Lemma 15.35, Theorem 15.36, Proposition 15.37, and Theorem 15.38), `rabinOneWay_iff_factoringHard` establishes `RabinOneWay gen ↔ FactoringHard gen` for Blum moduli via explicit certified PPT reductions `factorToRabin` (computing `crtSqrt y a b` from a nontrivial factorization `a * b = N`, with exact loss `1` in `succProbability_factoringGame_le`) and `rabinToFactor` (`rabinOneWay_of_factoringHard`, `factoringHard_of_rabinOneWay`). Across all three modules, generator families (`setup : ℕ → PMF ModulusDesc`, `RSAGen := ℕ → PMF RSADesc`, `BlumGen := ℕ → PMF BlumDesc`) are arbitrary `PMF` families over valid parameter tuples without bundled prime-generation algorithms or bit-length bounds in `n`, and adversaries/reductions use uniform native strict-PPT (`IsPPTOn`) on `(1^n, ...)` with binary `encNat` encodings (charging the full encoded input and sampled/callback output uniformly before `n`). Rather than assuming an exact uniform sampler on `(ZMod N)ˣ`, `rabinInversionGame` and `rabinToFactor` use an original dyadic all-residue sampling variant that draws a uniform `2 * N.bits.length`-bit list `r` (`x = ofBits r < 2^(2 * bits(N))` with `N^2 ≤ 2^(2 * bits(N))`) and squares `x` modulo `N`: `rabinToFactor` checks `1 < gcd(x, N) < N` first and otherwise queries the inverter on `x^2 % N` to return `rabinFactorPair (x + x') N`, yielding the concrete factor-`3` reduction bound `succProbability_rabinInversionGame_le` without modular rejection-sampling error.

For composite residuosity and Paillier encryption, import
[`CompositeResiduosity.lean`](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean) and
[`Paillier.lean`](../../CslibFrontier/Crypto/Computational/Paillier.lean), and for IND-CPA security
[`Paillier/Security.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean)
([katzlindell20][katzlindell20], Chapter 15, Proposition 15.6, Claims 15.7–15.9, Definition 15.10,
Construction 15.11, Example 15.12, Theorem 15.13, and Definition 15.14; checked instances are in
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean)).
A balanced modulus is a product `N = p * q` of distinct odd primes of the same bit length
(`BalancedModulus.Valid (p, q)`). The Decisional Composite Residuosity assumption
`DCR setup` ([katzlindell20][katzlindell20], Definition 15.10) compares `dcrRealGame` (drawing an
`N`-th residue `r ^ N mod N ^ 2` for a uniform unit `r`) against `dcrIdealGame` (drawing a uniform
unit modulo `N ^ 2`) under `Game.Indistinguishable` against uniform strict-PPT distinguishers
`IsPPTOn (encPair encUnary (encPair encNat encNat)) encBool`. The parameter `setup : ℕ → PMF Desc`
is arbitrary: prime factor generation is not constructed, and equal factor bit lengths are not
tied to the security parameter `n`.

Paillier public-key encryption operates over binary words with natural-number encodings `encNat`
and `encPair encNat encNat (N, φ(N))`:
- `keyGen gen n` draws a valid description `(p, q) ← gen n` and emits `pk = encNat N` and
  `sk = encPair encNat encNat (N, φ(N))`. Given `IsPPTOn encUnary encDesc gen`, `isPPTOn_keyGen`
  proves that key generation is uniform strict PPT.
- `encrypt n pk m` draws a candidate residue using `ProbComp.sampleModNat (n + |N|) N` and maps
  nonunits to `1` via `unitOrOne N r = if gcd(r, N) = 1 then r else 1`, computing the ciphertext as
  `c = (1 + N) ^ m * r ^ N mod N ^ 2`. `isPPTOn_encrypt` proves encryption is uniform strict PPT.
- `decrypt sk ct` computes `((c ^ φ(N) mod N ^ 2) - 1) / N * φ(N)⁻¹ mod N` using square-and-multiply
  exponentiation and Euler's totient inversion `φ(N) ^ (φ(N) - 1) mod N` (`gcd(N, φ(N)) = 1` by
  `BalancedModulus.Desc.coprime_totient`, Katz–Lindell Claim 15.7), certified polynomial-time by
  `computableInPolyTime_decrypt`.
- `decrypt_encrypt` establishes perfect correctness: for any key pair in the support of `keyGen gen n`
  and message `m < ofBits pk = N`, decrypting any supported ciphertext recovers `encNat m`.
- `addCiphertexts pk ct₁ ct₂` multiplies ciphertexts modulo `N ^ 2`. `decrypt_addCiphertexts`
  proves preservation of plaintext addition under decryption: combining supported encryptions of `m₁`
  and `m₂` yields a ciphertext that decrypts to `(m₁ + m₂) mod N`.

Only this decryption-side addition identity is established; the second condition of Katz–Lindell
Definition 15.14—distributional equality between combined ciphertexts and fresh encryptions of the
sum—does not hold for the dyadic sampler with `unitOrOne` (e.g. at `N = 143`, `n = 0`, and
`m₁ = m₂ = 0`, fresh `encNat 1` has mass `44 / 256`, whereas multiplying two independent encryptions
yields mass `2316 / 65536 = 579 / 16384`), and full Definition 15.14 remains a separate objective.

IND-CPA security (Katz–Lindell Theorem 15.13) is in
[`Paillier/Security.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean).
Challenge pairs are admissible when both messages are below the modulus (`validMessages n pk m₀ m₁`,
i.e. `m₀, m₁ < ofBits pk`). `DCR.indcpaOn_paillier` proves
`Encryption.INDCPAOn validMessages encNat (keyGen gen) encrypt` from `DCR (fun n => eval (gen n))`
and the extra hypothesis `hsize`: every description in the support of `gen n` has primes of at least
`n` bits. The reduction `dcrDistinguisher A b` answers the challenge with `(1 + N) ^ m_b * y mod N ^ 2`
and is uniform strict PPT (`isPPTOn_dcrDistinguisher`). The book samples the encryption randomness
uniformly from the units modulo `N`; here `encrypt` uses the dyadic sampler with `unitOrOne`, which is
within `N / 2 ^ (n + |N|) + (N - φ(N)) / N` of uniform on the units. Under `hsize` this costs at most
`5 / 2 ^ n` per real hop (`Game.advantage_sampleModNat_units_le` in
[`UnitSampling.lean`](../../CslibFrontier/Crypto/Computational/UnitSampling.lean), also used for
Goldwasser–Micali below), so the IND-CPA advantage is at most `10 / 2 ^ n` plus the two DCR
advantages; without a growth condition on the primes the non-unit loss need not be negligible. The
distributional-homomorphism gap above is unaffected.
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean) checks the
concrete parameters of Example 15.12 (`N = 187`, `m = 175`, `r = 83`, `c = 23911`), homomorphic
decryption to `12` and `7` modulo `143`, validity of `(11, 13)`, uniform strict PPT for a constant
generator `constGen`, and end-to-end correctness and homomorphic addition on its supported key pair;
for IND-CPA it evaluates `validMessages` on admissible and inadmissible pairs and applies
`isPPTOn_dcrDistinguisher` and `DCR.indcpaOn_paillier` to a concrete strict-PPT adversary.

For Goldwasser–Micali public-key encryption under `QuadraticResiduosityHard`, import
[`GoldwasserMicali.lean`](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean)
([katzlindell20][katzlindell20], §15.4.4, Definition 15.14, Construction 15.28, Theorem 15.29, and
Exercises 15.11–15.12; checked instances are in
[`CslibFrontierTests/Crypto/GoldwasserMicali.lean`](../../CslibFrontierTests/Crypto/GoldwasserMicali.lean)).
`KeyDesc` bundles distinct odd primes `(p, q)` (`2 < p, q`) with a residue `z < p * q`
representing an element of `positiveNonresidues p q` (`KeyDesc.ofBlum` specializes to Blum primes `p % 4 = 3`, `q % 4 = 3` with `z = N - 1`, Exercise
15.12), and `keyGen gen` wraps an abstract generator `gen : ℕ → ProbComp KeyDesc` (prime and
nonresidue sampling are not constructed) emitting `pk = encPair encNat encNat (N, z)` and
`sk = encPair encNat encNat (p, q)` (`isPPTOn_keyGen`). `encrypt` draws randomness via
`ProbComp.sampleModNat (n + |N|) N` with `unitOrOne N` to output `encNat ((z^m * r^2) mod N)`
(`isPPTOn_encrypt`), `decrypt` tests quadratic residuosity modulo `p` and `q` via Euler's criterion
`powMod p c ((p - 1) / 2)` (`computableInPolyTime_decrypt`, `decrypt_encrypt`), and
`mulCiphertexts` multiplies ciphertexts modulo `N` (`computableInPolyTime_mulCiphertexts`,
`decrypt_mulCiphertexts`). As with Paillier, distributional XOR homomorphism and re-randomization
(Definition 15.14, Exercise 15.11) hold on the ideal unit-sampling law `idealEncrypt`
(`idealEncrypt_mulCiphertexts_eq`, `rerandomize_idealEncrypt_eq`), whereas the dyadic `sampleModNat`
with `unitOrOne` approximates uniform `(ZMod N)ˣ` within `5 / 2 ^ n` under `hsize : n ≤ d.p.size ∧
n ≤ d.q.size` (`advantage_encrypt_idealEncrypt_le`). Under `QuadraticResiduosityHard setup`,
`hsize`, and public-key indistinguishability from `publicKeyLaw setup`, `indcpa_goldwasserMicali`
proves single-bit `Encryption.INDCPA` (`advantage_publicKeyGame_le_qr`, factor-`2` QR loss plus
`10 / 2 ^ n` via `qrDistinguisher`) and `indcpaOn_goldwasserMicali_bits` proves bounded-word
`Encryption.INDCPAOn (validBoundedWords maxLen) encBits` for `encryptWord` under any unary
polynomial-time `maxLen` (`advantage_publicKeyWordGame_le_qr`, factor-`2` QR loss independent of
`maxLen n` plus `(10 * maxLen n) / 2 ^ n` via lossy quadratic-residue public keys and
`qrWordDistinguisher`). Conversely, `jacobiAttackAdversary` (`jacobiAttackAdversary_isPPT`) achieves
exact chosen-message advantage `1` whenever `z ∈ jacobiNegSet p q`
(`advantage_jacobiAttackAdversary_eq_one`), witnessing the necessity of `J_N(z) = +1`.

## Encryption and chosen-message attacks

[AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/Basic.lean#L73) has a first stage choosing two messages and a saved word from the public key, and a second stage guessing from that saved state and the challenge ciphertext. Each stage has a native certificate. `INDCPAOn` explicitly constrains admissible message pairs. `WordINDCPA` requires equal lengths; the general `INDCPAOf` with all pairs is stronger for variable-length word messages. Invalid challenges are made independent of the hidden experiment bit. `Encryption.advantage (gameOn valid keyGen encrypt adversary) n` names the advantage between the two sides of the experiment at parameter `n`, and `INDCPAOn` asks that it be negligible for every admissible adversary; bounds on other two-sided encryption experiments, such as the DEM and CCA games, are stated with the same name.

[CCA2AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/CCA.lean#L266) exposes adaptive decryption before and after the challenge; the second handler rejects the exact challenge ciphertext. The multi-challenge interface in [`CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA.lean) (`MultiCCA2AdversaryOf`, `INDCCA2MultiOn`) is a two-phase **batch** model, whereas [`CCA/Interleaved.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean) (`InterleavedCCA2AdversaryOf`, `interleavedCcaOracle`, `INDCCA2InterleavedOn`) formalizes Boneh–Shoup Attack Game 12.1 and Definition 12.1 ([bs23][bs23], §12.1, pp. 467–468) with a single stateful combined encryption-and-decryption oracle that tracks the list `S` of challenge ciphertexts generated so far, allowing arbitrary adaptive interleaving of `.challenge m₀ m₁` and `.decrypt c` queries (including decryption of a ciphertext `c` before a later challenge happens to produce `c`) and proving equivalence with both 1CCA and phased batch multi-challenge CCA (`indcca2InterleavedOn_iff_indcca2On`, `indcca2InterleavedOn_iff_indcca2MultiOn`, and `advantage_interleavedCca2GameOn`, with concrete checks in [`CslibFrontierTests/Crypto/CCAInterleaved.lean`](../../CslibFrontierTests/Crypto/CCAInterleaved.lean)). Encodings are part of the security boundary: the inspected Cramer–Shoup parser [decodeCramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup/Scheme.lean#L876) requires canonical framing, so a different raw serialization of the challenge does not silently bypass the equality check.

The endpoint [DDH.indcca2On_cramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup.lean#L1688) (together with its batch multi-challenge lift `DDH.indcca2MultiOn_cramerShoup` and fully adaptive interleaved multi-challenge lift [`DDH.indcca2InterleavedOn_cramerShoup`](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean)) combines DDH, collision resistance, negligible inverse group order, and explicit efficient public operations. Approximate modular sampling and its statistical error are accounted for. Other clients include ElGamal, hybrid encryption, authenticated encryption and encrypt-then-MAC; they instantiate the same staged/oracle security schemas. Homomorphic schemes add circuit functionality and are treated [separately](homomorphic-encryption.md).

The canonical [`KEMINDCPA keyLen keyGen encaps`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid.lean) compares the real encapsulated key with an independent uniform `keyLen n`-bit word. Use `fun n => n` for normalized keys, or another schedule such as `fun n => 2 * n`. The composition methods `KEMINDCPA.hybrid_indcpa` and `KEMINDCPA.hybrid_indcpaOn` consume `DEMOneTimeKeyINDCPAOf` and `DEMOneTimeKeyINDCPAOn` at the same schedule; the latter requires a polynomial-time admissibility predicate independent of the public key. The exact bound is twice the hidden-bit KEM distinguisher's advantage plus the DEM adversary's advantage (Boneh–Shoup v0.6, Exercise 11.9(b), pp. 460–461 [bs23][bs23]). The native ideal-game certificate `isPPTOn_kemIdealGame` additionally takes `ComputableInPolyTime keyLen encUnary encUnary`. The reductions do not sample ideal keys, so the security implication itself does not need that certificate.

Starting with the imports and local context in [`CslibFrontierTests/Crypto/HybridEncryption.lean`](../../CslibFrontierTests/Crypto/HybridEncryption.lean), `indcpaOf_hybridEncrypt_doubleKey_otp` shows the doubled-key composition; adjacent examples check native sampling, supported key lengths, correct decryption and the zero-width boundary. The unconditional security fixture discards its key and is explicitly not decryptable; decryption correctness is checked separately on a leaking KEM. Security does not bundle correctness, and the zero-width pad recovers only the empty message. For an actual cryptographic client, [`DDH.wordINDCPA_hybrid_hashedElGamal`](../../CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean) now accepts a `SecureKDF` and a standalone DEM at arbitrary `keyLen`; [`CslibFrontierTests/Crypto/DiffieHellman.lean`](../../CslibFrontierTests/Crypto/DiffieHellman.lean) instantiates the bridge with doubled key length. The security parameter controlling its modular-sampling error remains `n`, independently of the key length.

[`encryptKeyEncaps keyLen encrypt`](../../CslibFrontier/Crypto/Computational/Encryption/KEMFromPKE.lean) constructs a KEM from word public-key encryption by sampling a key and encrypting it (Boneh–Shoup v0.6, Exercise 11.9(e), p. 461 [bs23][bs23]). Apply `WordINDCPA.kemINDCPA_encryptKeyEncaps` with a native unary polynomial-time certificate for `keyLen`; the reduction chooses two equal-length keys, saves the public key and the first key, and preserves advantage exactly. The separate `isPPTOn_encryptKeyEncaps` certificate also needs native encryption, while `decrypt_encryptKeyEncaps` reuses the original total decryptor and its supported-ciphertext correctness. [`CslibFrontierTests/Crypto/KEMFromPKE.lean`](../../CslibFrontierTests/Crypto/KEMFromPKE.lean) provides complete checked clients, including composition of this constructor with the existing doubled-width one-time pad DEM, exact zero-width sampling, and a correctly decryptable but insecure key-revealing encryptor. No new failure/rejection behavior is added.

For adaptive decapsulation security, import [`KEMFromPKE/CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean) and apply `WordINDCCA2.indistinguishable_encryptKeyEncaps` (Boneh–Shoup v0.6, Exercise 12.5(f), p. 514 [bs23][bs23]). The result uses `Game.Indistinguishable` over `kemCCARealGame` and `kemCCAIdealGame`, with the existing `IsOraclePPT` adversaries. Both games share the CPA sampling continuations and use `cca2Phase2Oracle` to reject the exact challenge word. The reduction preserves advantage exactly, samples two equal-length keys, and forwards postchallenge queries unchanged. It requires a unary polynomial-time `keyLen`; honest algorithm certificates and supported-output correctness are separate. Here the original option-valued decryptor is retained, so `some []` denotes successful empty-key decapsulation and `none` denotes rejection.

The [checked CCA KEM clients](../../CslibFrontierTests/Crypto/KEMFromPKECCA.lean) instantiate doubled key length, an unconditional correct zero-width KEM, and a reply-dependent tag-flipping attack with advantage `1 - 2^(-keyLen n)`. The attack fixture is correctly decryptable but insecure; it makes no CPA-security claim. Its native oracle certificate bounds reply reading, and the honest-game certificate charges decryption. This KEM endpoint covers one encapsulation followed by adaptive queries. The composition below uses this schedule; prechallenge KEM queries and multiple encapsulation challenges remain separate objectives.

The canonical `hybridDecrypt` now takes Option-valued decapsulation and symmetric decryption,
rejects noncanonical ciphertext-pair encodings, and propagates component failures. Its supported
correctness theorem concludes `some msg`, preserving accepted empty keys and messages. The
native certificate charges the framing test and both callbacks. This repairs the representation
boundary needed by CCA composition, without changing `hybridEncrypt` or its CPA security
theorems.

[`Hybrid/DEMCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean)
proves the exact DEM leg of Boneh–Shoup Exercise 12.5(a), p. 513 [bs23][bs23]. Its middle game
retains the original KEM key/encapsulation correlation and independently samples the actual
symmetric key distribution. The selected KEM component uses that key before and after the
challenge. A native reduction to the existing `SymmetricCipher.OneTimeINDCCA` game preserves
each experiment's output law, hence its advantage with factor one. Both challenge messages must
have length `n`, matching this symmetric-cipher model; invalid pairs return false in both worlds.
Canonical framing makes component-level challenge rejection agree with exact word rejection.

The [checked clients](../../CslibFrontierTests/Crypto/HybridDEMCCA.lean) include the existing PRF
Encrypt-then-MAC construction, a full-advantage echo-cipher counterexample, and a zero-width
adaptive trace distinguishing `none` from `some []`.

[`Hybrid/CompositionCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
completes both KEM hops and Exercise 12.5(a)'s concrete bound for this `n`-bit-message model:
`exists_hybridCCA_reductions` supplies native adversaries with hybrid advantage at most twice
the KEM advantage plus the actual symmetric CCA advantage. The hidden-bit reduction's signed
probability identities precede the absolute-value bound. `hybrid_indcca2On` gives the asymptotic
endpoint using existing `INDCCA2On`, and `isPPTOn_hybridCCAGame` certifies the honest experiment.
No new encryption scheme or security predicate is introduced.

The postprocessor `F` must take uniform `keyLen n`-bit seeds to exactly the distribution of
`E.keyGen n`, with one native algorithm for all parameters. The
[checked clients](../../CslibFrontierTests/Crypto/HybridCompositionCCA.lean) instantiate an actual
CCA-secure PKE's encrypted-key KEM with the PRF Encrypt-then-MAC cipher. Its `3*n` random bits
produce framed keys of encoded length `4*n+1`, not uniform encoded words. A general total
saved-coins client uses the existing evaluator theorem and returns supported keys on every seed.
Supported KEM correctness justifies the real-hop sampling commutation; perfect hybrid correctness
additionally checks support of the postprocessed real key. Tests expose the failure without that
KEM premise, and show that a perfect zero-width KEM with the insecure echo DEM remains insecure.
Arbitrary message-space extension and stronger KEM query schedules remain separate.

For explicit-coin public-key encryption and modular Fujisaki–Okamoto KEM transforms ([hhk17][hhk17],
ePrint 2017/604 full version dated 2 November 2021), import
[`FujisakiOkamoto.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto.lean).
Unlike the word-level encryption interface used by `encryptKeyEncaps`, `ExplicitCoinPKE` (§2.1)
exposes a fixed coin type `R`, an arbitrary coin sampler `sampleCoins : ProbComp R` (where the
paper uses uniform draws and permits key-dependent `R`), and deterministic encryption
`encDet : PK → M → R → CT` alongside `keyGen` and `dec`, together with expected
worst-case-message `δ`-correctness `ExplicitCoinPKE.DeltaCorrect` (defined via `ProbComp.expect`
and `PMF.toOuterMeasure`, with `deltaCorrect_zero_of_perfect` and `DeltaCorrect.mono`),
`γ`-spreadness `ExplicitCoinPKE.GammaSpread`, and the single-stage fixed-message distinguishing
experiment `ExplicitCoinPKE.indCpaGame` (`ExplicitCoinPKE.indCpaAdvantage`, which takes
caller-supplied messages `(m₀, m₁)` and probability-difference `Game.advantage` rather than
§2.1 Def. 2.2 / Fig. 4's two-stage key-dependent-message guessing experiment and `|Pr[b' = b] - 1/2|`
normalization). On top of `ExplicitCoinPKE`, `FujisakiOkamoto.encT` and `FujisakiOkamoto.decT`
define the derandomization transform `T[PKE, G]` (§3.1, Fig. 5) with mandatory re-encryption check
`encT P G pk m' = c` (`decT_encT_eq_some`, `encT_of_decT_eq_some`, `dec_of_decT_eq_some`,
`decT_eq_none_of_reencrypt_ne`), while `FujisakiOkamoto.Scheme` (with arbitrary samplers
`sampleMsg` and `sampleKey`) packages both explicit-rejection `FO^⊥` (§3.2.1, Fig. 9;
`Scheme.encapsBot`, `Scheme.decapsBot`, `decapsBot_encT_eq_some`,
`decapsBot_eq_none_of_reencrypt_ne`) and a deliberate domain-separated variant of
implicit-rejection `FO-notbot` (§3.2.2, Fig. 12; `ImplicitSK`, `Scheme.keyGenNotBot`,
`Scheme.encapsNotBot`, `Scheme.decapsNotBot`, `decapsNotBot_encT_eq`,
`decapsNotBot_of_reencrypt_ne`) that tags `H : Bool × M × CT → K` with `false` for valid key
derivations and `true` for fallback rejection keys `H(true, dk.fallback, c)` in place of HHK17's
untagged `H(s, c)`. Only the transform definitions, correctness/spreadness predicates, and
deterministic recovery and re-encryption rigidity lemmas are established in this module;
random-oracle IND-CCA games and security reductions remain separate objectives. Checked clients in
[`CslibFrontierTests/Crypto/FujisakiOkamoto.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamoto.lean)
exercise honest `T`/`FO^⊥`/`FO-notbot` recovery and non-canonical-coin rejection on
`maskedShiftPKE`, zero-error and non-zero tight/non-tight `DeltaCorrect` witnesses (`noisyCoinPKE`
with failure probability `1 / 2`), and positive and negative `GammaSpread` and `indCpaAdvantage`
witnesses on `identityPKE`.

For multi-block symmetric modes of operation over `BitString n`, import
[`BlockCipher/Modes.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/Modes.lean)
(Katz–Lindell 3rd ed., §3.6.2–§3.6.4 and Exercises 3.21, 3.24, 3.25, 3.29, 3.30, 3.32, 3.33).
It defines CBC (`cbcEncryptBlocks`, `cbcDecryptBlocks`), OFB (`ofbChain`, `ofbEncryptBlocks`,
`ofbDecryptBlocks`), counter mode (`ctrMaskBlocks`, `ctrEncryptBlocks`, `ctrDecryptBlocks`), and
self-synchronizing CFB (`cfbEncryptBlocks`, `cfbDecryptBlocks`, included alongside KL's modes) with
round-trip inversion theorems and the identity `ofbChain_eq_cbcEncryptBlocks_replicate_zero`
equating the OFB keystream chain with CBC encryption of all-zero plaintext blocks. The generic
sampling facts live in
[`Probability/BitString/Collision.lean`](../../CslibFrontier/Probability/BitString/Collision.lean):
under an ideal random function `PMF.uniformOfFintype (BitString n → BitString n)`,
`BitString.map_evalPoints_uniformOfFintype` and `BitString.map_xorEvalPoints_uniformOfFintype` give
keystream and ciphertext uniformity on fixed (non-adaptive) injective point schedules (such as CTR
counters), and `BitString.toOuterMeasure_addRight_mem_finset_eq` and
`BitString.toOuterMeasure_addRight_mem_list_le` give the shifted-block collision probabilities
`S.card / 2^n` and at most `ks.length / 2^n`. The modes module builds on them with
`advantage_xorEvalPoints_eq_zero` and the chain collision bound `toOuterMeasure_badChain_le`
(`bs.length * (ks.length + bs.length) / 2^n`, over `uniformBlocks`, the `PMF.iid` uniform blocks read
as a list) used when analyzing random-IV chaining. The indexed OFB and CTR masks decrypt the
list-mode ciphertexts (`maskBlockDecrypt_ofbBlockMask_ofbEncryptBlocks`,
`maskBlockDecrypt_ctrBlockMask_ctrEncryptBlocks`); indexed block `j ≥ 1` of `ctrBlockMask` uses
counter value `j - 1`, matching list block `j - 1` of `ctrMaskBlocks`. The module
also proves mode separations and counterexamples for same-IV reuse (`advantage_streamIVReuseGame_eq`,
`cfbSameIVRecover_cfbEncryptBlocks`), overlapping counter/stream nonces
(`ctrEncryptBlocks_overlapping_nonce`, `advantage_overlappingStreamGame_eq`), predictable-IV CBC
chosen-plaintext attacks (`advantage_cbcPredictableIVGame_eq_one`), linear XOR and modular/group
additive-IV modes (`xorFunctionCipherRecover_correct`, `additiveModeDistinguisher_spec`), and
single-bit/dropped-block error-propagation laws (`maskBlockDecrypt_flipBit`,
`cbcBlockDecrypt_flipBit`, `cfbBlockDecrypt_flipBit`, `cbcBlockDecrypt_dropBlock`,
`cfbBlockDecrypt_dropBlock`, `maskBlockDecrypt_dropBlock`). Concrete `BitString 4` and
`ZMod (2 ^ 4)` checks, including indexed CTR decryption of list CTR ciphertexts under a
nonconstant counter schedule, are in
[`CslibFrontierTests/Crypto/BlockCipherModes.lean`](../../CslibFrontierTests/Crypto/BlockCipherModes.lean),
and direct checks of the sampling lemmas are in
[`CslibFrontierTests/BitStringCollision.lean`](../../CslibFrontierTests/BitStringCollision.lean).

## Authentication, signatures, and state

[SignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Signature.lean#L87) bundles efficient key generation, signing, verification and correctness. The base message space is exactly `n` bits. Its oracle forger chooses signing requests adaptively; ordinary EUF-CMA rejects any message previously signed. [exists_oneWay_iff_exists_oneTimeSignature](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToSignature.lean#L882) is the OWF/one-time-signature equivalence via Lamport's construction. Stateless many-time `EUFCMA` `SignatureScheme`s on `n`-bit messages are constructed from any `OneWayPermutation` in [`TCRSignature.lean`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) (`OneWayPermutation.exists_eufCMA`) and from any general `OneWay` function in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) (`OneWay.exists_eufCMA`, `exists_oneWay_iff_exists_signature`, `exists_oneTimeSignature_iff_exists_signature` [rompel90][rompel90]). For unrestricted bit-string messages (`msg : List Bool`), [`WordSignatureScheme`](../../CslibFrontier/Crypto/Computational/WordSignature.lean) removes the `n`-bit message-length filter from signing, verification and `eufCmaGame` (`WordSignatureScheme.EUFCMA`, strictly stronger than `toSignatureScheme.EUFCMA`), [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) lifts any `SignatureScheme.EUFCMA` scheme via per-signature fresh-key target collision-resistant hash-and-sign (`SignatureScheme.EUFCMA.eufCMA_wordScheme`, `OneWayPermutation.exists_wordEUFCMA`; Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23]), and [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) closes the unrestricted-message equivalence from any uniform `OneWay` function (`OneWay.exists_wordEUFCMA`, `exists_oneWay_iff_exists_wordSignature`, `exists_oneTimeSignature_iff_exists_wordSignature` [rompel90][rompel90]).

[MACScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/MAC.lean#L176) reuses `SignatureScheme.signingOracleOf` and `oneTimeSigningOracleOf` for fresh-message EUF-CMA while distinguishing it from fresh-pair SUF-CMA (`signingPairOracle`, `oneTimeSigningPairOracle`). A randomized signer can return more than one valid tag for a message, so the distinction is observable. `PseudorandomFunction.sufCma_prfMAC` proves a native PRF-based construction with forging probability bounded by reduction advantage plus `2^-n`. `NonceMACScheme` adds a nonce-respecting query condition.

For concrete multi-block CBC-MAC bounds and domain-separation counterexamples over `BitString n`,
import [`BlockCipher/CBCMAC.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/CBCMAC.lean)
(Katz–Lindell 3rd ed., §4.4, Construction 4.9, Theorem 4.12, Claim 4.13, and Exercises 4.13–4.16).
`cbcMacBlocks` folds `state ↦ g (state + block)` with composition law `cbcMacBlocks_append` and
last-ciphertext-block identity `getLast_cbcEncryptBlocks_eq_cbcMacBlocks`. On bounded nonempty
inputs `CBCInput n ℓ`, `cbcSmooth_of_prefixFree` proves `(q, ℓ, q^2 * ℓ^2 / 2^n)`-smoothness for
any `q` distinct prefix-free queries (`CBCPrefixFree`, `CBCSmooth`), and
`abs_cbcRealSuccess_sub_cbcIdealSuccess_le` lifts this to an adaptive PRF bound for distinguishers
written as ordinary oracle programs `OracleComp (CBCOracleSpec n ℓ) Bool`, run with the query log of
`OracleComp.interpret` (`cbcQueryRun`) and restricted on every fixed-oracle execution to a
prefix-free budget of `q` queries (`CBCAdmissible`, `cbcRealSuccess`, `cbcIdealSuccess`). The bound
is information-theoretic: no computational PRF reduction or machine-realizability is claimed. The
module also proves
probability-`1` forgery attacks for each of the six relaxations in Exercises 4.13–4.16:
variable-length extensions without prefix-freeness (`cbcTwoToFourAttack_valid`,
`cbcToThreeAttack_valid`), leaked intermediate
chaining blocks (`cbcLeakedTagsAttack_valid`), random IVs (`cbcRandomIVAttack_valid`), appended
rather than prepended message lengths (`cbcLengthSuffixAttack_valid`), and ambiguous zero padding
(`zeroPadAttack_valid`, using `List.rightpad` and the floor-count block splitter
[`BitString.padBlocks`](../../CslibFrontier/Foundations/Data/BitString/PadBlocks.lean)), with concrete
four-bit witnesses in
[`CslibFrontierTests/Crypto/CBCMAC.lean`](../../CslibFrontierTests/Crypto/CBCMAC.lean).

[IndexedSignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/IndexedSignature.lean#L89) signs index/message pairs with polynomially bounded capacity; the oracle refuses repeated or out-of-range signing indices. The syntax is stateless but the game enforces single use. Counter wrappers and Merkle signature clients turn that contract into stateful signing, whereas [TreeSignature.scheme](../../CslibFrontier/Crypto/Computational/TreeSignature.lean#L550) and [TreeSignature/Security.lean](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4763) upgrade any indexed EUF-CMA scheme of capacity at least `2` plus a pseudorandom function (or one-way function) to a stateless `SignatureScheme` (`eufCMA_scheme`, `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`, `exists_eufCMA_of_oneWay`) by sampling a uniform leaf and deriving internal node keys and signing coins from the PRF [bs23][bs23]; `TreeSignature.sign` returns `[]` outside the `n`-bit message domain. Composing Lamport, depth-`1` Merkle trees, PRFs from one-way functions, and stateless tree signatures gives [OneWay.exists_eufCMA_of_hashFamily](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4821) from a one-way function and a collision-resistant hash family. Without full collision resistance, [`TCRSignature.scheme`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) adapts Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23] to a capacity-`1` `IndexedSignatureScheme` over a one-time signature scheme `S` and an unrestricted target collision-resistant `KeyedHashFamily` `H` without storing a hash key in `pk` (`SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`; concrete checks and an explicit `1`-probability break against a constant hash family are in [`CslibFrontierTests/Crypto/TCRSignature.lean`](../../CslibFrontierTests/Crypto/TCRSignature.lean)), and [`IndexedSignatureScheme.double`](../../CslibFrontier/Crypto/Computational/IndexedSignature/Double.lean) doubles any indexed scheme of capacity at least `1` to constant capacity `2` with plug-and-pray loss `2` (Boneh–Shoup §14.6.1, construction `(14.4)` on p. 597, and Exercise 13.2 [bs23][bs23]; `IndexedSignatureScheme.IndexedEUFCMA.double`). Composing Lamport one-time signatures, `TCRSignature.scheme`, `IndexedSignatureScheme.double`, and `TreeSignature` yields `OneWay.exists_eufCMA_of_targetCollisionResistant`: instantiating `H` with `naorYungHash` proves `OneWayPermutation.exists_eufCMA` (Naor–Yung §4 / Theorem 2 [naoryung89][naoryung89]), while instantiating `H` with `rompelHash` in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) removes the permutation hypothesis to yield `OneWay.exists_indexedEUFCMA_two` and `OneWay.exists_counterEUFCMA_two` on arbitrary-length `List Bool` messages, `OneWay.exists_eufCMA` and `exists_oneWay_iff_exists_signature` on `SignatureScheme`'s `n`-bit message domain, and—after applying [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) (`SignatureScheme.EUFCMA.eufCMA_wordScheme`)—`OneWay.exists_wordEUFCMA` and `exists_oneWay_iff_exists_wordSignature` on unrestricted `List Bool` messages ([rompel90][rompel90]; client checks and message-space separation witnesses in [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean)). Keep the indexed game's no-repeat invariant distinct from durable storage in a deployed stateful implementation: no filesystem or crash-recovery model is asserted here.

Collision-resistant hashing alone gives these stateless signatures.
[`HashFamily.oneWay_keyDigest`](../../CslibFrontier/Crypto/Computational/CollisionResistantToOneWay.lean)
proves that `keyDigest H`, which reads its input as a key `k` (the first third) and a message `x`
and outputs `k ++ H k x`, is one-way for every collision-resistant hash family `H` (Katz–Lindell,
Exercise 8.4). An inverter either finds a collision under the uniform key or returns `x` itself;
since it sees the `(2 n + r)`-bit message only through its `n`-bit digest, the latter happens with
probability at most `(1 / 2) ^ n`. Composed with `OneWay.exists_eufCMA` and
`OneWay.exists_wordEUFCMA`, this gives `HashFamily.exists_eufCMA` and `HashFamily.exists_wordEUFCMA`
(Katz–Lindell, Theorem 14.16), so the one-way function assumed by
`OneWay.exists_eufCMA_of_hashFamily` follows from its hash family. Through Merkle–Damgård,
`CompressionFamily.exists_oneWay` and `CompressionFamily.exists_wordEUFCMA` give the same
conclusions for `2 n → n` compression families. No converse is claimed.

## Commitments and ideal distributions

[CommitmentScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Commitment/Basic.lean#L83) is intentionally distributional. It gives a faithful public-key encoding, valid messages, an exact PMF of commitment/opening pairs, verification and correctness. Efficient realization is separate. Chosen-message hiding reuses the saved-state encryption adversary; binding asks for two distinct messages opening one commitment. Pedersen's ideal exact uniform exponent law is compatible with this model even when a strict finite fair-coin implementation must approximate it. `Commitment/PublicOperations` and `PedersenCommitment/ProbComp` supply the separate public-operation and sampling bridges.

## Garbling schemes

[Garbling/Scheme.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Scheme.lean) is the abstract garbling-scheme syntax of Bellare, Hoang and Rogaway, Sections 3 and 4 [bhr12][bhr12]: `Scheme Fn` is `(Gb, En, De, Ev, ev)` over an abstract type of function descriptions with length readers, and `Scheme.Garbled` is the output triple `(F, e, d)`. `Gb` carries its coins explicitly (`coinLen` and a deterministic `gb`), and `Scheme.garble` samples them via `BitString.sampleList`, so non-degeneracy can quantify over the coins (`Scheme.eval_garble`, `Scheme.mem_support_eval_garble_iff`). `Scheme.IsValid` bundles `Scheme.LengthCondition`, `Scheme.NonDegenerate` and `Scheme.Correct`; `Scheme.WellTyped` fixes the output length of `ev` and of every successful decoding of an arbitrary string. A `SideInfo Fn Λ` is a side-information function `Φ` with length readers (`SideInfo.circ` is the identity side information `Φ_circ`), and `SideInfo.Compatible`, `SideInfo.IsEvInverter` and `SideInfo.IsInverter` are the compatibility condition of Section 3.3 and the inversion hypotheses of Section 4.1 (`SideInfo.Compatible.inLen_eq`, `SideInfo.circ_compatible`, `SideInfo.circ_isInverter`). For a concrete point-and-permute circuit garbling construction over `Cslib.Circuits.Circuit`, see [Protocols and privacy](protocols-and-privacy.md#garbled-circuits).

[Garbling/Games.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Games.lean) states the single-query games `prvIndExp`, `prvSimExp`, `obvIndExp`, `obvSimExp` and `autGame` (Sections 3.4–3.6) as `ProbComp` experiments whose advantages (`prvIndAdvantage`, `prvSimAdvantage`, `obvIndAdvantage`, `obvSimAdvantage`, `autAdvantage`) are `ℝ≥0` through `Game.advantage` and `Game.succProbability`. An invalid query (`prvIndValid`, `obvIndValid`) is answered by `⊥`, `prvIndAdvantage_eq_zero_of_invalid` records that an always-invalid adversary has advantage `0`, and `prvIndAdvantage_eq_two_mul_guessingAdvantage` identifies the `prv.ind` advantage with twice the bias of the hidden-bit game `prvIndBitGame` via `Game.succProbability_uniform_bool_beq`. [Garbling/Foundations.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Foundations.lean) proves Propositions 2 and 3 (Section 4) as exact per-adversary identities: `prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim` for every simulator (`prvIndToSim`, state `IndToSimState`) and `prvSimAdvantage_prvSimFromInverter_eq` against the inverter simulator `prvSimFromInverter` (`prvSimToInd`, `eval_prvSimExp_prvSimFromInverter`) under an `ev`-inverter, together with the obliviousness analogues (`obvIndToSim`, `obvSimFromInverter`, `obvSimToInd`, `obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_eq`, `eval_obvSimExp_obvSimFromInverter`) under an inverter and `≤` corollaries (`prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim`, `prvSimAdvantage_prvSimFromInverter_le`, `obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_le`). No polynomial-time or negligible-advantage statement is made, and projective schemes (`Π` of Section 3.2), conventional-circuit topology/size inverters (`Φ_topo`, `Φ_size` of Proposition 1), and the authenticity relations of Section 4 are not part of these modules. [Garbling-scheme clients](../../CslibFrontierTests/Crypto/GarblingScheme.lean) check a valid and well-typed scheme (`identityScheme`, `identityScheme_isValid`, `identityScheme_wellTyped`), verify zero advantage for an invalid-query adversary, separate shape-only side information from `SideInfo.circ` on a valid `prv.ind` query over a one-bit gate scheme, and instantiate all four privacy and obliviousness reductions.

## Known Limitations

The finite query-only PRG/cipher results, semantic commitment interfaces and uniform native primitive structures do not share one implicit efficiency premise. The table records the differences. The long internal HILL and GGM proofs, all serialization helpers, and every named reduction were not independently re-proved or built in this pass. Existing nonvacuity tests are useful checks of interfaces, not evidence that cryptographic hardness assumptions hold.

[bhr12]: ../sources.md#bhr12
[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[fly22]: ../sources.md#fly22
[ggm86]: ../sources.md#ggm86
[goldreich04]: ../sources.md#goldreich04
[hhk17]: ../sources.md#hhk17
[hhrvw20]: ../sources.md#hhrvw20
[hill99]: ../sources.md#hill99
[holenstein06]: ../sources.md#holenstein06
[katzlindell20]: ../sources.md#katzlindell20
[naoryung89]: ../sources.md#naoryung89
[rompel90]: ../sources.md#rompel90
