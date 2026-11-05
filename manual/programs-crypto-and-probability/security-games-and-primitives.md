# Security games and primitive families

## Generic games and adversary quantifiers

[Game](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L67) is a `PMF Bool`. Success is its true probability; advantage is the nonnegative distance between two success probabilities. [Indistinguishable](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L154) says that every admissible complete adversary has negligible advantage as the parameter grows. `Indistinguishable.of_reduction` transfers security through a reduction with a polynomially bounded loss and negligible additive error, while `indistinguishable_pure_false_iff`, `Indistinguishable.of_succProbability_le`, and `Indistinguishable.of_succProbability_reduction` specialize one-sided search and forgery games compared against `PMF.pure false`. This layer is mathematical probability; admissibility determines the computational interpretation [complexitylib][complexitylib].

For finite-source statistical bounds, import [Game/CloseTo/Statistical.lean](../../Complexity/Crypto/Game/CloseTo/Statistical.lean). `Cslib.Interactive.closeTo_of_dist_le` turns a bound on the finite-PMF metric (half the L1 distance) into the existing all-event `CloseTo` relation with the same error. Its `CloseTo.bind_left` law then handles arbitrary randomized continuations, including infinite output types. This shared import exposes the existing bridge without importing lattice protocols or their native sampler certificates; the former `Lyubashevsky.Efficient` import still reexports it.

For adaptive stateful replacement, import [Security/Oracle.lean](../../Complexity/Computability/Interactive/Security/Oracle.lean). `OracleComp.IsCostBounded.closeTo_runWith` turns a program's existing cost bound `K` and per-call `CloseTo` bounds `cost q * ε` into a bound `K * ε` on the joint result and final state. The premise compares both handlers at every identical query and starting state, including unreachable states; no coupling or finite state space is assumed. Calls of cost zero can still update a shared cache, but their joint reply/state laws must agree statistically at error zero. Charging only signing calls therefore avoids paying for unchanged hash calls or private sampling. The checked adaptive client in [OracleStatistical.lean](../../ComplexityTests/OracleStatistical.lean) uses two repeated signing requests, answer-dependent repeated cache reads, and a concrete nonzero error bound while preserving the cache and signing log. This shared lemma does not itself complete the native Schnorr signing-game or key-generation transport in #2568.

For two continuations that agree outside a bad input event, import [Game/CloseTo/UntilBad.lean](../../Complexity/Crypto/Game/CloseTo/UntilBad.lean). `CloseTo.bind_of_eq_on μ f g bad` bounds the mixtures by the actual probability `μ.toOuterMeasure bad`; agreement is required only on supported inputs outside `bad`, and neither type must be finite. This lets a cache-programming step charge only the probability that the sampled point was already cached. The [checked clients](../../ComplexityTests/CloseToUntilBad.lean) retain the actual Fiat–Shamir reply and final cache, show a sharp one-half error on an infinite output type, and allow arbitrary disagreement on impossible inputs at zero cost. This law does not identify different hidden cache states or justify removing aborted queries.

[ComputationallyIndistinguishable](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Basic.lean#L94) specializes admissibility to a uniform native strict-PPT test on `(1^n, sample)`. Its ensembles are arbitrary PMFs on bit strings: sampleability and polynomial output length are not bundled. `IsPPTTest` admits semantic tests whose laws have a native program witness. Efficient postprocessing and hybrid results use those certificates, not the mere presence of a Lean function.

Pinned cslib also has the finite [Generator](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Primitives/PRG/Defs.lean#L38) interface, whose `Secure` accepts any chosen predicate on randomized tests, while expansion is a separate cardinality property. Complexitylib adds circuit-bounded tests and uniform machine tests on top. These are intentionally different quantifiers; the circuit version can select a new bounded circuit at each input length [cslib][cslib].

## Hardness and pseudorandomness

| Schema | Principal source | Formal parameters and main use |
|---|---|---|
| One-way functions | [Complexity/Crypto/Computational/OneWay.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay.lean) | Deterministic native polynomial evaluation; uniform seed-length sampling; strict-PPT inverter gets unary length and image; any preimage may win |
| Pseudorandom generator | [Complexity/Crypto/Computational/PseudorandomGenerator.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomGenerator.lean) | Length schedule, expansion, native deterministic evaluation and indistinguishability |
| Adaptive pseudorandom function | [Complexity/Crypto/Computational/PseudorandomFunction.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomFunction.lean) | Oracle-PPT access, consistent ideal random function, explicit input/output widths and malformed-query convention |
| Collision resistance | [Complexity/Crypto/Computational/CollisionResistant.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CollisionResistant.lean) | Public setup distribution/encoding and input-validity predicate; keyed word specialization; setup need not be efficiently sampleable in the general interface |
| Target collision resistance | [Complexity/Crypto/Computational/TargetCollisionResistant.lean](../../Complexity/Crypto/Computational/TargetCollisionResistant.lean), [Complexity/Crypto/Computational/NaorYung.lean](../../Complexity/Crypto/Computational/NaorYung.lean), [Complexity/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../Complexity/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Two-stage pre-key target choice and post-key second-preimage search; polynomial key/block schedules, fixed-depth `2^n`-capacity tree extension, Naor–Yung UOWHFs from `OneWayPermutation`, and Rompel–HHRVW UOWHFs from `OneWay` |
| Inaccessible entropy and shrinking collision grids | [Complexity/Crypto/Computational/InaccessibleEntropy/Basic.lean](../../Complexity/Crypto/Computational/InaccessibleEntropy/Basic.lean), [Complexity/Crypto/Computational/InaccessibleEntropy/Amplify.lean](../../Complexity/Crypto/Computational/InaccessibleEntropy/Amplify.lean), [Complexity/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../Complexity/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Fixed-width native polynomial evaluation, accessible preimage subsets with eventual `1 / denom n` entropy gap, polynomial-size grids of `1`-bit shrinking candidates with an existential random-collision-resistant sequence (`exists_good_candidate`), and uniform `gridCount n`-way cascade concatenation |
| Discrete logarithm and DDH | [Complexity/Crypto/Computational/DiscreteLog.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiscreteLog.lean), [Complexity/Crypto/Computational/DiffieHellman.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiffieHellman.lean) | Encoded prime-order group families, exact ideal group laws; public operations and samplers require separate certificates |
| LWE, SIS, and module lattices | [Complexity/Crypto/Computational/LWE/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/LWE/Basic.lean), [Complexity/Crypto/Computational/SIS/Basic.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/SIS/Basic.lean), [Complexity/Crypto/Computational/SIS/Module.lean](../../Complexity/Crypto/Computational/SIS/Module.lean), [Complexity/Crypto/Computational/SIS/ModuleEncryption.lean](../../Complexity/Crypto/Computational/SIS/ModuleEncryption.lean) | Explicit dimensions, modulus and noise/norm parameters (`2^w` binary matrix words in `Basic.lean`, arbitrary `[NeZero (q security)]` moduli, Ajtai collision extraction, negacyclic `R_q = ℤ_q[X]/(X^n+1)` block-anticirculant expansion `expandModuleMatrix`, `ModuleSIS`, `RingSIS`, and `DecisionModuleLWE` in `SIS/Module.lean`, and dual-Regev `ModuleLWE` public-key encryption in `SIS/ModuleEncryption.lean`); classical uniform-PPT hardness hypotheses |

For a one-bit expanding PRG, [Stretch/Prefix.lean](../../Complexity/Crypto/Computational/Stretch/Prefix.lean)
proves that `(forwardIterate g ℓ seed).take ℓ` has length `ℓ` and agrees with the first `ℓ`
emitted bits of every longer run. The premise is global: `length (g seed) = length seed + 1`
for every seed, including the empty word. The complete `forwardIterate` output also retains a
reversed final seed and is not prefix-consistent. Native computation charges both the seed and
unary `ℓ`; for each uniform native length schedule `L n`, the emitted `L n`-bit prefix from a
uniform `n`-bit seed is computationally indistinguishable from `uniformList (L n)`, by existing
stretch security and reverse/take postprocessing. [PRGStretch clients](../../ComplexityTests/PRGStretch.lean)
check zero widths, order-sensitive output, and native XOR encryption/recovery. This is the emitted-pad
prerequisite for the stream-cipher route of Boneh–Shoup §3.2 [bs23][bs23]; adaptive arbitrary-word
one-time encryption and hash-then-MAC/EtM remain open in [#2749](https://github.com/cslib-community/complexitylib/issues/2749).

Several independently keyed copies of a pseudorandom function are again pseudorandom: [`PseudorandomFunction.multiKey`](../../Complexity/Crypto/Computational/PseudorandomFunction/MultiKey.lean) answers `t` word channels with the `n`-bit blocks of one `t * n`-bit key, against `t` independent random functions, for every fixed `t`. Its hybrid reduction `prfMultiReduction` simulates the already random channels with a lazy list cache and is itself oracle PPT; the concrete bound sums `t` PRF advantages (Boneh–Shoup, Exercise 4.26). The number of keys is a constant, not a function of the security parameter; the exercise also allows a polynomially bounded number of keys, which this theorem does not cover.

Unconditionally, any pseudorandom function on `n`-bit inputs requires at least `2 * n - 2` binary gates over the full binary Boolean basis `B₂` (`fullInterpretation (k := 2)`) on all but a negligible fraction of keys (Fan–Li–Yang §§4.2, 7.1, Theorem 7.5 [fly22][fly22]): [`CircuitLowerBound.lean`](../../Complexity/Crypto/Computational/PseudorandomFunction/CircuitLowerBound.lean) proves the bound both for arbitrary `BooleanPRF` ensembles (which impose no efficient sampling or evaluation condition) and for word-valued `PseudorandomFunction` families via deterministic `BitString.lowBits`-encoded restriction queries. The underlying wire out-degree, syntactic dead-gate elimination (`Circuit.NoDeadGates`), critical-path `2 * n - 2 * m` gate bound, and `B₂` intersection bottleneck live in [`Complexity/Computability/Circuit/CriticalPath.lean`](../../Complexity/Computability/Circuit/CriticalPath.lean) and [`Complexity/Computability/Circuit/Boolean/CriticalPath.lean`](../../Complexity/Computability/Circuit/Boolean/CriticalPath.lean). Tightness at `2 * n - 2`, distinguisher completeness, refutation of bitwise XOR, unconditional `BooleanPRF` non-vacuity on random functions, and conditional `OneWay` non-vacuity are checked in [`ComplexityTests/Crypto/PRFCircuitLowerBound.lean`](../../ComplexityTests/Crypto/PRFCircuitLowerBound.lean).

The main uniform construction chain is [OneWay.exists_pseudorandomGenerator](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRG.lean#L54), [exists_oneWay_iff_exists_pseudorandomGenerator](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PRGToOneWay.lean#L215), polynomial stretch, and [OneWay.exists_pseudorandomFunction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRF.lean#L46). The formal abstract [hill](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CryptographyAbstract.lean#L81) states the one-bit expansion endpoint, and `adaptive_functions` states the adaptive PRF endpoint. The forward generator proof follows the Holenstein pseudoentropy route to the Håstad–Impagliazzo–Levin–Luby theorem; the function construction follows Goldreich–Goldwasser–Micali. The cited primary sources establish the classical OWF/PRG and adaptive function-construction results [hill99][hill99] [holenstein06][holenstein06] [ggm86][ggm86]. The uniform Lean endpoint does not assume an extra entropy or nonuniform-advice premise. In parallel, relativizing the Holenstein pseudoentropy, three-source, entropy-grid, XOR-combination and reindexing pipeline to polynomially bounded advice families yields the nonuniform construction chain [`NonuniformOneWay.exists_nonuniformPRG`](../../Complexity/Crypto/Computational/OneWayToPRG.lean#L68) (one-bit stretch) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../Complexity/Crypto/Computational/OneWayToPRG.lean#L77) (length-tripling `3 * n + 1` stretch) from any [`NonuniformOneWay`](../../Complexity/Crypto/Computational/Nonuniform/Basic.lean#L304) function.

Target collision resistance (universal one-wayness) separates target selection from key sampling: in [`TargetCollisionResistant.lean`](../../Complexity/Crypto/Computational/TargetCollisionResistant.lean), `TargetCollisionFinder.choose` commits to `(m₀, state)` from `1^n` before a uniform `keyLen n`-bit key is drawn, and `TargetCollisionFinder.find` receives `(1^n, state, k)` to output `m₁` (Boneh–Shoup §8.11.2, Attack Game 8.5 and Definition 8.7 [bs23][bs23]; Naor–Yung §2 [naoryung89][naoryung89]; Goldreich §6.4.3 [goldreich04][goldreich04]). Full collision resistance implies target collision resistance with identical game success probability (`CollisionResistantOn.targetCollisionResistantOn`). Because single-key Merkle–Damgård requires the key to compute intermediate chaining targets, domain extension from `KeyedCompressionFamily` (`2M(n) → M(n)` with `n ≤ M(n)`) to unrestricted `KeyedHashFamily` on `List Bool` instead uses `uowhfTreeHash`, a total fixed-depth adaptation of level-keyed binary-tree hashing (Naor–Yung 1995 revision §2.3 [naoryung89][naoryung89]; Goldreich June 2003 chapter draft §6.4.3.2, Constructions 6.4.24/6.4.26 and Propositions 6.4.25/6.4.27 [goldreich04][goldreich04]; cf. Boneh–Shoup §8.11.3, pp. 339–340 [bs23][bs23], which instead presents a per-step-key chain and notes tree hashing): `uowhfLeaves` encodes one message bit per zero-padded `M(n)`-bit leaf, `uowhfTreeLevels` folds `n` fixed halving levels under independent subkeys, `top.headD []` selects the first resulting block, and an `(n + 1)`-st subkey compresses that block with `BitString.lowBits (M n) msg.length` (`msg.length mod 2^{M(n)}`). At fixed `n`, inputs longer than `2^n` bits leave multiple blocks in `top` and `top.headD []` discards the extra roots (so out-of-capacity messages such as `[false, false, false]` and `[false, false, true]` at `n = 1` collide), whereas `KeyedCompressionFamily.targetCollisionResistant_treeHash` still holds on unrestricted `List Bool` because strict-PPT admissibility polynomially bounds the output lengths of both `choose` and `find`, placing supported `m₀` and `m₁` strictly below `2^n ≤ 2^{M(n)}` for all sufficiently large `n`; [`ComplexityTests/Crypto/TargetCollisionResistant.lean`](../../ComplexityTests/Crypto/TargetCollisionResistant.lean) gives checked instances, collision extractions and insecurity witnesses. In [`NaorYung.lean`](../../Complexity/Crypto/Computational/NaorYung.lean), any `OneWayPermutation` instantiates that compression interface without trapdoors (adapting Naor–Yung §3 [naoryung89][naoryung89] and Goldreich June 2003 draft §6.4.3.2, Construction 6.4.20 and Proposition 6.4.21 [goldreich04][goldreich04]): `naorYungShrink` quotients `{0, 1}^{n+2}` by `{0, δ}` via pivot-bit canonicalization and deletion rather than an affine/Toeplitz matrix so `naorYungStep` reduces to `inversionGame` at length `n + 2` with exact loss `1` and zero additive error, `naorYungCompression` cascades `n + 1` steps (`2(n + 1) → n + 1`) with loss `dyadicSize (n + 1)`, and `naorYungHash` composes with `KeyedCompressionFamily.treeHash` (`OneWayPermutation.targetCollisionResistant_naorYungHash`, `OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`; client checks and an explicit `1 / 2`-success break of `naorYungStep id` are in [`ComplexityTests/Crypto/NaorYung.lean`](../../ComplexityTests/Crypto/NaorYung.lean)).

For universal one-way hashing from general one-way functions without permutations, [`OneWay.exists_inaccessibleEntropyFamily`](../../Complexity/Crypto/Computational/InaccessibleEntropy/OneWay.lean) constructs an [`InaccessibleEntropyFamily`](../../Complexity/Crypto/Computational/InaccessibleEntropy/Basic.lean) with gap denominator `denom n = 64 * (n + 1)` from any uniform `OneWay` function, proving a weaker constant-threshold adaptation of Haitner–Holenstein–Reingold–Vadhan–Wee, Section 4.2, Theorem 4.5 [hhrvw20][hhrvw20] via the `3`-wise independent Boolean affine hash family [`isThreeWiseIndependentHash_affineHash`](../../Complexity/Probability/BitString/AffineHash/ThreeWise.lean) and prefix-collision seed projection `adjustAffineSeed`: whereas the paper uses threshold `2^(n - i) / n^c` to achieve gap `d log n / n` for every constant `d > 0` under Definition 3.9, the Lean construction fixes one adversary-independent accessible-set family against uniform strict-PPT adversaries, encodes the prefix length in a dyadic `(Nat.log 2 n + 1)`-bit saturating field, and uses constant threshold `2^(n - min r n) / 4` to obtain the smaller inverse-linear gap `1 / (64 * (n + 1))`. Parallel repetition with Hoeffding concentration and dyadic planted-coordinate escape reductions ([`Complexity/Crypto/Computational/InaccessibleEntropy/Repetition.lean`](../../Complexity/Crypto/Computational/InaccessibleEntropy/Repetition.lean), Lemma 5.3) combined with two-universal input/output hashing for `1`-bit shrinkage ([`Complexity/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean`](../../Complexity/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean), Lemmas 5.4 and 5.5) then yield [`InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../Complexity/Crypto/Computational/InaccessibleEntropy/Amplify.lean) and [`OneWay.exists_shrinkingCollisionGrid`](../../Complexity/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (Section 5.1.5, Theorem 5.1, STEPS 1–3), producing a [`ShrinkingCollisionGrid`](../../Complexity/Crypto/Computational/InaccessibleEntropy/Amplify.lean) of uniformly polynomial-time `1`-bit shrinking candidates containing an existential candidate sequence (`exists_good_candidate`) collision-resistant on random inputs (`randomCollisionGame`). Although that existential index `goodIdx n` need not be efficiently computable, [`rompelCompression`](../../Complexity/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) evaluates all `gridCount n` candidates uniformly across `rompelCascadeSteps G n = (2 * gridCount n - 1) * outLen n` XOR-masked `1`-bit shrinking steps under one shared `rompelCascadeSteps G n * inLen n`-bit step-key sequence and concatenates their outputs (`2 * (gridCount n * outLen n) → gridCount n * outLen n`; adapting [hhrvw20][hhrvw20] Section 5.1.4, Lemmas 5.6–5.7, pp. 29–30, and Section 5.1.5, STEP 4, p. 31, and STEP 5(ii–iii), p. 32, using one fresh `inLen n`-bit subkey per `1`-bit step and sharing that sequence across candidates rather than claiming Lemma 5.7's `O(|y| log t)` compact-key bound or STEP 5(iii)'s per-candidate keys), with single-stage planted-subkey reduction `rompelCompressionInverter` achieving exact key simulation at multiplicative loss `dyadicSize (gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero additive error (`ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`, `OneWay.exists_targetCollisionResistant_keyedCompressionFamily`). Composing with `KeyedCompressionFamily.treeHash` yields `rompelHash` and `OneWay.exists_targetCollisionResistant_keyedHashFamily` ([rompel90][rompel90]; [hhrvw20][hhrvw20] Section 5.1, Theorem 5.1, p. 25), with concrete checks in [`ComplexityTests/Crypto/InaccessibleEntropy.lean`](../../ComplexityTests/Crypto/InaccessibleEntropy.lean) and [`ComplexityTests/Crypto/Rompel.lean`](../../ComplexityTests/Crypto/Rompel.lean).

The polynomial interpretation of the module-lattice coefficient vectors is proved in
[`SIS/Polynomial.lean`](../../Complexity/Crypto/Computational/SIS/Polynomial.lean).
For `n ≠ 0` and a nontrivial commutative ring `R`, `negacyclicEquiv` identifies `Fin n → R`
with Mathlib's `AdjoinRoot (X^n + 1)` as an `R`-module, and `negacyclicEquiv_mul` carries
`negacyclicMul` to quotient multiplication. Use the equivalence's injectivity to reflect
quotient equalities back to coefficient vectors. `negacyclicEquiv_moduleSISMap` transports the
existing Module-SIS map to a quotient-ring matrix product. The checked examples in
[`NegacyclicPolynomial.lean`](../../ComplexityTests/Crypto/NegacyclicPolynomial.lean) include
integers, composite modulus `6`, characteristic `2`, dimension `1`, and reflection of the
Module-SIS zero equation. The source function type retains pointwise multiplication; use
`negacyclicMul` for polynomial multiplication. Dimension zero is excluded because its quotient
is `R/(2)`. This algebraic bridge adds no hardness or runtime claim.

The pure coefficient identity `negacyclicMul_eq_coeff_mul` is available separately in
[SIS/Polynomial/Coefficients.lean](../../Complexity/Crypto/Computational/SIS/Polynomial/Coefficients.lean),
so algebra clients need not import native computation certificates. For native multiplication, import
[SIS/Native.lean](../../Complexity/Crypto/Computational/SIS/Native.lean).
`negacyclicMulResidues n q a b` truncates two natural-coefficient lists to `n`, computes the
existing integer `mulZJet (2*n)`, and reduces each lower coefficient minus its wrapped upper
coefficient modulo `q`. Short lists are zero-padded and the output has exactly `n` entries.
The plain certificate charges unary `n`, binary `q`, and both complete framed binary input
lists. It imposes no coefficient-size bound. For `q > 0`, `negacyclicMulResidues_ofFn` identifies
the output with the canonical coefficients of the existing `negacyclicMul`; neither primality
nor positive dimension is needed. At `q = 0`, the total operation instead truncates each
signed result at zero, with no canonical-residue interpretation claimed.
The [checked clients](../../ComplexityTests/Crypto/NegacyclicNative.lean) include `X² = -1`
modulo six, modulus one, empty and irregular inputs, a 128-bit modulus, and the actual
rank-one `moduleLWEKeyGen` coefficient computation. Full key generation, encryption and
decryption still need variable-rank traversal and canonical key/ciphertext packing and parsing.
This arithmetic certificate does not remove the existing restrictions on exact native samplers
or imply small-secret security.

These are implications from hardness assumptions. They do not prove that a concrete OWF, DDH group, LWE family or SIS parameter choice is hard. The LWE interface exposes only the serialized public matrix `[B*t+e | B]`, with independent errors and one shared uniform secret; in [`SIS/Module.lean`](../../Complexity/Crypto/Computational/SIS/Module.lean), `expandModuleMatrix` and `flattenPolyVec` embed negacyclic `ModuleSIS` and `ModuleLWE` instances over `ℤ_q[X]/(X^n+1)` into unstructured `(d * n) × (k * n)` matrices over `ℤ_q` (checked with concrete evaluations and nonvacuity proofs in [`ComplexityTests/Crypto/ModuleSIS.lean`](../../ComplexityTests/Crypto/ModuleSIS.lean)), and [`SIS/ModuleEncryption.lean`](../../Complexity/Crypto/Computational/SIS/ModuleEncryption.lean) builds dual-Regev public-key encryption (`moduleLWEKeyGen`, `moduleLWEEncrypt`, `moduleLWEDecrypt`), bounded-noise decryption correctness (`moduleLWEDecrypt_moduleLWEEncrypt_eq`), and two-hop public-key/ciphertext reductions to `ModuleLWE.sampleLaw` (`advantage_realEncryptionView_uniform_le`, `advantage_realEncryptionView_msg_le`, checked in [`ComplexityTests/Crypto/ModuleEncryption.lean`](../../ComplexityTests/Crypto/ModuleEncryption.lean)); no worst-case lattice reduction is asserted there.

For deterministic native key generation, import
[`ModuleEncryption/Native.lean`](../../Complexity/Crypto/Computational/SIS/ModuleEncryption/Native.lean).
`exists_computableInPolyTime_moduleLWEKeyGen` supplies one total word function with a plain
polynomial-time certificate and exact agreement with `ModuleLWE.encodeSample (moduleLWEKeyGen …)`.
Both rank and polynomial degree are unary inputs; the positive modulus and signed secret/error
coefficients are binary. The public matrix input uses `ModuleSIS.encodeMatrix`: its structured
`(k*n)`-square rotation-block expansion is already present. Runtime charges that complete matrix
word, both complete framed signed lists and the dimensions; it does not assume a seed codec.
The implementation reuses total framing/number decoders and the upstream padded list dot product,
then reduces each integer coordinate modulo `q`. Short rows/vectors pad with zero and excess
entries are ignored, but still contribute to input length. Canonical equality requires `q > 0`;
there is no assertion that malformed words are rejected. [Checked clients](../../ComplexityTests/Crypto/ModuleKeyGenNative.lean)
use the same certified function for rank two, degree two, composite modulus six, signed wraps,
modulus one, zero dimensions and a 129-bit modulus. The structured matrix sampler below supplies
its public matrix input; full randomized key generation must still compose the actual secret and
error samplers. Full native encryption/decryption, seed compression and security remain separate
obligations.

The structured matrix input itself now has a native constructor and exact sampler in
[`SIS/Module/MatrixSampling.lean`](../../Complexity/Crypto/Computational/SIS/Module/MatrixSampling.lean).
`exists_computableInPolyTime_encodeModuleMatrix` supplies one total implementation of the existing
`ModuleSIS.encodeMatrix`, from rectangular nested coefficient lists, unary row/rank/degree and a
binary modulus. Its canonical identity assumes `q > 0`; zero dimensions and modulus one are
included. The private implementation pads missing coefficients with zero, ignores excess entries
while charging their input length, and uses the actual negative wrap of `rotMatrix`. At modulus
zero it remains total, without a canonical residue interpretation.
`exists_isPPTOn_sampleEncodedModuleMatrix` samples independent polynomial coefficients using
`sampleBinaryNat w`, then performs that certified expansion. Its exact law is uniform on the
original polynomial matrix followed by `ModuleSIS.encodeMatrix`, for unary dimensions and bit
width, including width zero. The expanded scalar entries are correlated. [Tests](../../ComplexityTests/Crypto/ModuleMatrixSampling.lean)
check a rectangular modulus-six expansion, empty shapes, a 129-bit modulus, and a nonrotation
matrix with zero structured-sampler mass but positive independent-scalar-uniform mass. They also
compose the same obtained sampler with the native key generator: the composition is strict PPT
for runtime dimensions/width and complete supplied signed secret/error words, and its concrete
conditional law agrees with the existing key generator. Full CBD randomized key generation,
native encryption/decryption and security remain separate tasks.

For arbitrary positive binary moduli, including primes, import
[`Module/ApproximateSampling.lean`](../../Complexity/Crypto/Computational/SIS/Module/ApproximateSampling.lean).
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

[Checked clients](../../ComplexityTests/Crypto/ModuleMatrixApproximation.lean) show that four fair
bits reduced modulo three give the encoded zero two-coefficient block mass `9/64`, whereas the
ideal structured law gives `1/9`. The bound is `3/8`. The same obtained sampler and native keygen
function compose uniformly on runtime dimensions, binary modulus and complete supplied secret
and error words; deterministic keygen postprocessing preserves that error against the existing
ideal conditional key law. Other clients cover width zero, modulus one, empty dimensions and a
129-bit modulus. Full random secret/error composition, encryption and security remain open.
The scalar all-event bridge `Probability.closeTo_uniform_sampleModNat` now lives in
[`Game/CloseTo/UniformNat.lean`](../../Complexity/Crypto/Game/CloseTo/UniformNat.lean), publicly
reexported by its original Lyubashevsky consumer, so this construction does not import a
signature protocol to obtain a generic sampler bound.

The Module-LWE sampling APIs now accept explicit distributions: `moduleLWEPublicKeyLaw` has an
optional `secretLaw`, `encryptionViewOfKeyLaw` an optional `ephemeralLaw`, and `realEncryptionView`
accepts both. Their defaults remain uniform, and the existing security reductions concern those
uniform defaults. [`ModuleEncryption/Sampling.lean`](../../Complexity/Crypto/Computational/SIS/ModuleEncryption/Sampling.lean)
proves that conditioning public-key generation on the actual sampled secret preserves the public
view, including when the same run retains `(secret, view)`. Sampling a fresh secret independently
of a public key would not preserve that correlation.
The concrete small-secret instance reuses the existing centered-binomial fair-bit program and
modular `GSW.noiseLaw`. Under `2*η < 2^w`, every sampled integer is its residue's centered lift,
so the resulting module secret satisfies the coefficient bound `η`. Nested list sampling has a
uniform strict-PPT certificate for unary row count, degree and binomial width, with binary signed
integer output. The subsequent modular-cast identity is semantic; this is not a native certificate
for the whole encryption scheme. [Tests](../../ComplexityTests/Crypto/ModuleEncryptionSampling.lean)
include nonzero supported secrets, zero dimensions/width, and a variable-row native client.
They also show that uniform rank-one, degree-one secrets and ephemeral values modulo sixteen,
with all errors one, decrypt a true message correctly with probability only `7/16`.
The existing deterministic correctness theorem requires bounded secrets as well as bounded noise;
this example does not contradict it. Small-secret security requires its own assumption and reduction;
the randomized correctness result below uses explicit support and noise-tail hypotheses.

For numerical modulus conversion, import
[`SIS/ModulusSwitch.lean`](../../Complexity/Crypto/Computational/SIS/ModulusSwitch.lean).
`moduleLWEModulusSwitch p ct` converts the existing ciphertext components with the reusable
[`ZMod.modulusSwitch`](../../Complexity/Foundations/Data/ZMod/ModulusSwitch.lean): take
`valMinAbs`, multiply by the rational ratio `p / q`, round to the nearest integer with half
ties toward positive infinity, and reduce modulo `p`. It is not a ring homomorphism.
For `q,p > 0`, `exists_moduleLWEModulusSwitch_phase` supplies an integer representative of
the target phase whose distance from the scaled canonical source phase is at most
`(1 + ∑ j, ∑ l, |s j l|) / 2`. The secret at both moduli is the cast of the same integer
vector. The representative supplied at the target need not be its centered lift.
`exists_moduleLWEModulusSwitch_phase_of_lifts` exposes arbitrary integer lifts and their
carry equation; the canonical theorem constructs these carries automatically.
The [checked examples](../../ComplexityTests/Crypto/ModulusSwitch.lean) cover negative half
ties, composite moduli, modulus one, nonadditivity, and a ciphertext with nonzero carry.
This nearest-integer phase bound is original supporting algebra; it does not assert Boolean
plaintext preservation, parity-preserving switching, a security reduction, or a runtime bound.

For its native implementation, import
[`SIS/ModulusSwitch/Native.lean`](../../Complexity/Crypto/Computational/SIS/ModulusSwitch/Native.lean).
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
separate ciphertext format. The [native tests](../../ComplexityTests/Crypto/ModulusSwitchNative.lean)
exercise a 128-bit modulus, negative representatives, modulus one, ragged/empty rows, the
existing ciphertext encoding, and composition of two certified conversions. This runtime
certificate adds no decoding or security guarantee.

For sufficient plaintext-preserving margins, import
[`SIS/ModulusSwitch/Correctness.lean`](../../Complexity/Crypto/Computational/SIS/ModulusSwitch/Correctness.lean).
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
[Checked examples](../../ComplexityTests/Crypto/ModulusSwitchCorrectness.lean) apply the honest
encryption theorem in all four cases with nonzero noise, and exercise negative half ties and a
nonzero carry. They also show plaintext loss at target moduli one and two and failure at the
strict decoder threshold. This is deterministic correctness, with no additional security claim.

For randomized correctness, import
[`SIS/ModulusSwitch/Failure.lean`](../../Complexity/Crypto/Computational/SIS/ModulusSwitch/Failure.lean).
`toOuterMeasure_moduleLWEModulusSwitch_failure_le` uses the existing encryption view while
retaining the actual secret that generated the public key. Suppose the secret and ephemeral laws
are supported in centered coefficient bounds `Bs,Br`, and write `ν` for the polynomial-noise law.
Set `Q = k*n*Be*Br + k*n*Be*Bs + Be`. For positive source modulus `q`, target margin `4*Bp+2 < p`,
and `(p/q)*Q + (1+k*n*Bs)/2 + Δ ≤ Bp`, switched decryption fails with probability at most
`(2*k+1) * ν{e | e exceeds centered coefficient bound Be}`. The count is `k` key-error
polynomials, `k` encryption-error polynomials and one final polynomial, each sampled independently
as in the existing view. The proof reuses the deterministic theorem and the product-event union
bound; it assumes neither a decryption conclusion nor a source decoding margin.
[Checked clients](../../ComplexityTests/Crypto/ModulusSwitchFailure.lean) use the native
centered-binomial small-secret law for rank and degree one, switching from 32 to 16. Width-one
errors give zero failure. Width-two errors exceed good radius one with exact probability `1/8`,
giving an upper bound `3/8`; a supported error triple produces target phase 12 and proves positive
actual failure. These are original sufficient correctness bounds for the supplied laws. They add
no small-secret security reduction, Gaussian sampler or native certificate for the entire scheme.

For a concrete growing family, [ModulusSwitch/CenteredBinomial.lean](../../Complexity/Crypto/Computational/SIS/ModulusSwitch/CenteredBinomial.lean)
sets `t = l+1`, rank and degree `t`, CBD1 secret/ephemeral coefficients, and CBD(8t) error
coefficients with good radius `4t`. Put `Q = 8t³+4t`, `Bp = floor((Q+t²+2)/2)`,
`w = Nat.size(4Bp+2)`, target `p = 2^w` and source `q = 2^(w+1)`.
The proved bounds are `p ≤ 68t³`, `q ≤ 136t³`, strict no-wrap `16t < q`, and target
margin `4Bp+2 < p`. Half scaling and even moduli make the message-scale mismatch zero.
The actual retained-secret experiment fails with probability at most `4(2t+1)t exp(-t)`,
which is negligible for every message family. The extra factor `t` counts coefficients inside
each noise polynomial; the shared coefficient bound lives in
[Sampling/Concentration.lean](../../Complexity/Crypto/Computational/SIS/ModuleEncryption/Sampling/Concentration.lean).
The [checked clients](../../ComplexityTests/Crypto/ModulusSwitchCenteredBinomial.lean)
certify growing native CBD rows and power-of-two uniform matrix-entry samples, with unary
parameters and binary outputs, and check their semantic modular laws. They also prove positive
actual failure at `t=1`: `q=64`, `p=32`, errors all eight and supported secrets produce phase 29
and decode a true message incorrectly. The displayed bound is below one at `t=10`.
This is correctness for explicit laws, not a small-secret security reduction. Complete native
key generation, encryption and decryption certificates remain separate.

## Encryption and chosen-message attacks

[AdversaryOf](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/Basic.lean#L73) has a first stage choosing two messages and a saved word from the public key, and a second stage guessing from that saved state and the challenge ciphertext. Each stage has a native certificate. `INDCPAOn` explicitly constrains admissible message pairs. `WordINDCPA` requires equal lengths; the general `INDCPAOf` with all pairs is stronger for variable-length word messages. Invalid challenges are made independent of the hidden experiment bit.

[CCA2AdversaryOf](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/CCA.lean#L266) exposes adaptive decryption before and after the challenge; the second handler rejects the exact challenge ciphertext. The multi-challenge interface in [`CCA.lean`](../../Complexity/Crypto/Computational/Encryption/CCA.lean) (`MultiCCA2AdversaryOf`, `INDCCA2MultiOn`) is a two-phase **batch** model, whereas [`CCA/Interleaved.lean`](../../Complexity/Crypto/Computational/Encryption/CCA/Interleaved.lean) (`InterleavedCCA2AdversaryOf`, `interleavedCcaOracle`, `INDCCA2InterleavedOn`) formalizes Boneh–Shoup Attack Game 12.1 and Definition 12.1 ([bs23][bs23], §12.1, pp. 467–468) with a single stateful combined encryption-and-decryption oracle that tracks the list `S` of challenge ciphertexts generated so far, allowing arbitrary adaptive interleaving of `.challenge m₀ m₁` and `.decrypt c` queries (including decryption of a ciphertext `c` before a later challenge happens to produce `c`) and proving equivalence with both 1CCA and phased batch multi-challenge CCA (`indcca2InterleavedOn_iff_indcca2On`, `indcca2InterleavedOn_iff_indcca2MultiOn`, and `advantage_interleavedCca2GameOn`, with concrete checks in [`ComplexityTests/Crypto/CCAInterleaved.lean`](../../ComplexityTests/Crypto/CCAInterleaved.lean)). Encodings are part of the security boundary: the inspected Cramer–Shoup parser [decodeCramerShoup](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup/Scheme.lean#L876) requires canonical framing, so a different raw serialization of the challenge does not silently bypass the equality check.

The endpoint [DDH.indcca2On_cramerShoup](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup.lean#L1688) (together with its batch multi-challenge lift `DDH.indcca2MultiOn_cramerShoup` and fully adaptive interleaved multi-challenge lift [`DDH.indcca2InterleavedOn_cramerShoup`](../../Complexity/Crypto/Computational/Encryption/CCA/Interleaved.lean)) combines DDH, collision resistance, negligible inverse group order, and explicit efficient public operations. Approximate modular sampling and its statistical error are accounted for. Other clients include ElGamal, hybrid encryption, authenticated encryption and encrypt-then-MAC; they instantiate the same staged/oracle security schemas. Homomorphic schemes add circuit functionality and are treated [separately](homomorphic-encryption.md).

The canonical [`KEMINDCPA keyLen keyGen encaps`](../../Complexity/Crypto/Computational/Encryption/Hybrid.lean) compares the real encapsulated key with an independent uniform `keyLen n`-bit word. Use `fun n => n` for normalized keys, or another schedule such as `fun n => 2 * n`. The composition methods `KEMINDCPA.hybrid_indcpa` and `KEMINDCPA.hybrid_indcpaOn` consume `DEMOneTimeKeyINDCPAOf` and `DEMOneTimeKeyINDCPAOn` at the same schedule; the latter requires a polynomial-time admissibility predicate independent of the public key. The exact bound is twice the hidden-bit KEM distinguisher's advantage plus the DEM adversary's advantage (Boneh–Shoup v0.6, Exercise 11.9(b), pp. 460–461 [bs23][bs23]). The native ideal-game certificate `isPPTOn_kemIdealGame` additionally takes `ComputableInPolyTime keyLen encUnary encUnary`. The reductions do not sample ideal keys, so the security implication itself does not need that certificate.

Starting with the imports and local context in [`ComplexityTests/Crypto/HybridEncryption.lean`](../../ComplexityTests/Crypto/HybridEncryption.lean), `indcpaOf_hybridEncrypt_doubleKey_otp` shows the doubled-key composition; adjacent examples check native sampling, supported key lengths, correct decryption and the zero-width boundary. The unconditional security fixture discards its key and is explicitly not decryptable; decryption correctness is checked separately on a leaking KEM. Security does not bundle correctness, and the zero-width pad recovers only the empty message. For an actual cryptographic client, [`DDH.wordINDCPA_hybrid_hashedElGamal`](../../Complexity/Crypto/Computational/ElGamal/ProbComp.lean) now accepts a `SecureKDF` and a standalone DEM at arbitrary `keyLen`; [`ComplexityTests/Crypto/DiffieHellman.lean`](../../ComplexityTests/Crypto/DiffieHellman.lean) instantiates the bridge with doubled key length. The security parameter controlling its modular-sampling error remains `n`, independently of the key length.

[`encryptKeyEncaps keyLen encrypt`](../../Complexity/Crypto/Computational/Encryption/KEMFromPKE.lean) constructs a KEM from word public-key encryption by sampling a key and encrypting it (Boneh–Shoup v0.6, Exercise 11.9(e), p. 461 [bs23][bs23]). Apply `WordINDCPA.kemINDCPA_encryptKeyEncaps` with a native unary polynomial-time certificate for `keyLen`; the reduction chooses two equal-length keys, saves the public key and the first key, and preserves advantage exactly. The separate `isPPTOn_encryptKeyEncaps` certificate also needs native encryption, while `decrypt_encryptKeyEncaps` reuses the original total decryptor and its supported-ciphertext correctness. [`ComplexityTests/Crypto/KEMFromPKE.lean`](../../ComplexityTests/Crypto/KEMFromPKE.lean) provides complete checked clients, including composition of this constructor with the existing doubled-width one-time pad DEM, exact zero-width sampling, and a correctly decryptable but insecure key-revealing encryptor. No new failure/rejection behavior is added.

For adaptive decapsulation security, import [`KEMFromPKE/CCA.lean`](../../Complexity/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean) and apply `WordINDCCA2.indistinguishable_encryptKeyEncaps` (Boneh–Shoup v0.6, Exercise 12.5(f), p. 514 [bs23][bs23]). The result uses `Game.Indistinguishable` over `kemCCARealGame` and `kemCCAIdealGame`, with the existing `IsOraclePPT` adversaries. Both games share the CPA sampling continuations and use `cca2Phase2Oracle` to reject the exact challenge word. The reduction preserves advantage exactly, samples two equal-length keys, and forwards postchallenge queries unchanged. It requires a unary polynomial-time `keyLen`; honest algorithm certificates and supported-output correctness are separate. Here the original option-valued decryptor is retained, so `some []` denotes successful empty-key decapsulation and `none` denotes rejection.

The [checked CCA KEM clients](../../ComplexityTests/Crypto/KEMFromPKECCA.lean) instantiate doubled key length, an unconditional correct zero-width KEM, and a reply-dependent tag-flipping attack with advantage `1 - 2^(-keyLen n)`. The attack fixture is correctly decryptable but insecure; it makes no CPA-security claim. Its native oracle certificate bounds reply reading, and the honest-game certificate charges decryption. This KEM endpoint covers one encapsulation followed by adaptive queries. The composition below uses this schedule; prechallenge KEM queries and multiple encapsulation challenges remain separate objectives.

The canonical `hybridDecrypt` now takes Option-valued decapsulation and symmetric decryption,
rejects noncanonical ciphertext-pair encodings, and propagates component failures. Its supported
correctness theorem concludes `some msg`, preserving accepted empty keys and messages. The
native certificate charges the framing test and both callbacks. This repairs the representation
boundary needed by CCA composition, without changing `hybridEncrypt` or its CPA security
theorems.

[`Hybrid/DEMCCA.lean`](../../Complexity/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean)
proves the exact DEM leg of Boneh–Shoup Exercise 12.5(a), p. 513 [bs23][bs23]. Its middle game
retains the original KEM key/encapsulation correlation and independently samples the actual
symmetric key distribution. The selected KEM component uses that key before and after the
challenge. A native reduction to the existing `SymmetricCipher.OneTimeINDCCA` game preserves
each experiment's output law, hence its advantage with factor one. Both challenge messages must
have length `n`, matching this symmetric-cipher model; invalid pairs return false in both worlds.
Canonical framing makes component-level challenge rejection agree with exact word rejection.

The [checked clients](../../ComplexityTests/Crypto/HybridDEMCCA.lean) include the existing PRF
Encrypt-then-MAC construction, a full-advantage echo-cipher counterexample, and a zero-width
adaptive trace distinguishing `none` from `some []`.

[`Hybrid/CompositionCCA.lean`](../../Complexity/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
completes both KEM hops and Exercise 12.5(a)'s concrete bound for this `n`-bit-message model:
`exists_hybridCCA_reductions` supplies native adversaries with hybrid advantage at most twice
the KEM advantage plus the actual symmetric CCA advantage. The hidden-bit reduction's signed
probability identities precede the absolute-value bound. `hybrid_indcca2On` gives the asymptotic
endpoint using existing `INDCCA2On`, and `isPPTOn_hybridCCAGame` certifies the honest experiment.
No new encryption scheme or security predicate is introduced.

The postprocessor `F` must take uniform `keyLen n`-bit seeds to exactly the distribution of
`E.keyGen n`, with one native algorithm for all parameters. The
[checked clients](../../ComplexityTests/Crypto/HybridCompositionCCA.lean) instantiate an actual
CCA-secure PKE's encrypted-key KEM with the PRF Encrypt-then-MAC cipher. Its `3*n` random bits
produce framed keys of encoded length `4*n+1`, not uniform encoded words. A general total
saved-coins client uses the existing evaluator theorem and returns supported keys on every seed.
Supported KEM correctness justifies the real-hop sampling commutation; perfect hybrid correctness
additionally checks support of the postprocessed real key. Tests expose the failure without that
KEM premise, and show that a perfect zero-width KEM with the insecure echo DEM remains insecure.
Arbitrary message-space extension and stronger KEM query schedules remain separate.

## Authentication, signatures, and state

[SignatureScheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Signature.lean#L87) bundles efficient key generation, signing, verification and correctness. The base message space is exactly `n` bits. Its oracle forger chooses signing requests adaptively; ordinary EUF-CMA rejects any message previously signed. [exists_oneWay_iff_exists_oneTimeSignature](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToSignature.lean#L882) is the OWF/one-time-signature equivalence via Lamport's construction. Stateless many-time `EUFCMA` `SignatureScheme`s on `n`-bit messages are constructed from any `OneWayPermutation` in [`TCRSignature.lean`](../../Complexity/Crypto/Computational/TCRSignature.lean) (`OneWayPermutation.exists_eufCMA`) and from any general `OneWay` function in [`Rompel.lean`](../../Complexity/Crypto/Computational/Rompel.lean) (`OneWay.exists_eufCMA`, `exists_oneWay_iff_exists_signature`, `exists_oneTimeSignature_iff_exists_signature` [rompel90][rompel90]). For unrestricted bit-string messages (`msg : List Bool`), [`WordSignatureScheme`](../../Complexity/Crypto/Computational/WordSignature.lean) removes the `n`-bit message-length filter from signing, verification and `eufCmaGame` (`WordSignatureScheme.EUFCMA`, strictly stronger than `toSignatureScheme.EUFCMA`), [`TCRSignature.wordScheme`](../../Complexity/Crypto/Computational/TCRSignature/ManyTime.lean) lifts any `SignatureScheme.EUFCMA` scheme via per-signature fresh-key target collision-resistant hash-and-sign (`SignatureScheme.EUFCMA.eufCMA_wordScheme`, `OneWayPermutation.exists_wordEUFCMA`; Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23]), and [`Rompel.lean`](../../Complexity/Crypto/Computational/Rompel.lean) closes the unrestricted-message equivalence from any uniform `OneWay` function (`OneWay.exists_wordEUFCMA`, `exists_oneWay_iff_exists_wordSignature`, `exists_oneTimeSignature_iff_exists_wordSignature` [rompel90][rompel90]).

[MACScheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/MAC.lean#L176) reuses `SignatureScheme.signingOracleOf` and `oneTimeSigningOracleOf` for fresh-message EUF-CMA while distinguishing it from fresh-pair SUF-CMA (`signingPairOracle`, `oneTimeSigningPairOracle`). A randomized signer can return more than one valid tag for a message, so the distinction is observable. `PseudorandomFunction.sufCma_prfMAC` proves a native PRF-based construction with forging probability bounded by reduction advantage plus `2^-n`. `NonceMACScheme` adds a nonce-respecting query condition.

[IndexedSignatureScheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/IndexedSignature.lean#L89) signs index/message pairs with polynomially bounded capacity; the oracle refuses repeated or out-of-range signing indices. The syntax is stateless but the game enforces single use. Counter wrappers and Merkle signature clients turn that contract into stateful signing, whereas [TreeSignature.scheme](../../Complexity/Crypto/Computational/TreeSignature.lean#L550) and [TreeSignature/Security.lean](../../Complexity/Crypto/Computational/TreeSignature/Security.lean#L4779) upgrade any indexed EUF-CMA scheme of capacity at least `2` plus a pseudorandom function (or one-way function) to a stateless `SignatureScheme` (`eufCMA_scheme`, `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`, `exists_eufCMA_of_oneWay`) by sampling a uniform leaf and deriving internal node keys and signing coins from the PRF [bs23][bs23]; `TreeSignature.sign` returns `[]` outside the `n`-bit message domain. Composing Lamport, depth-`1` Merkle trees, PRFs from one-way functions, and stateless tree signatures gives [OneWay.exists_eufCMA_of_hashFamily](../../Complexity/Crypto/Computational/TreeSignature/Security.lean#L4837) from a one-way function and a collision-resistant hash family. Without full collision resistance, [`TCRSignature.scheme`](../../Complexity/Crypto/Computational/TCRSignature.lean) adapts Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23] to a capacity-`1` `IndexedSignatureScheme` over a one-time signature scheme `S` and an unrestricted target collision-resistant `KeyedHashFamily` `H` without storing a hash key in `pk` (`SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`; concrete checks and an explicit `1`-probability break against a constant hash family are in [`ComplexityTests/Crypto/TCRSignature.lean`](../../ComplexityTests/Crypto/TCRSignature.lean)), and [`IndexedSignatureScheme.double`](../../Complexity/Crypto/Computational/IndexedSignature/Double.lean) doubles any indexed scheme of capacity at least `1` to constant capacity `2` with plug-and-pray loss `2` (Boneh–Shoup §14.6.1, construction `(14.4)` on p. 597, and Exercise 13.2 [bs23][bs23]; `IndexedSignatureScheme.IndexedEUFCMA.double`). Composing Lamport one-time signatures, `TCRSignature.scheme`, `IndexedSignatureScheme.double`, and `TreeSignature` yields `OneWay.exists_eufCMA_of_targetCollisionResistant`: instantiating `H` with `naorYungHash` proves `OneWayPermutation.exists_eufCMA` (Naor–Yung §4 / Theorem 2 [naoryung89][naoryung89]), while instantiating `H` with `rompelHash` in [`Rompel.lean`](../../Complexity/Crypto/Computational/Rompel.lean) removes the permutation hypothesis to yield `OneWay.exists_indexedEUFCMA_two` and `OneWay.exists_counterEUFCMA_two` on arbitrary-length `List Bool` messages, `OneWay.exists_eufCMA` and `exists_oneWay_iff_exists_signature` on `SignatureScheme`'s `n`-bit message domain, and—after applying [`TCRSignature.wordScheme`](../../Complexity/Crypto/Computational/TCRSignature/ManyTime.lean) (`SignatureScheme.EUFCMA.eufCMA_wordScheme`)—`OneWay.exists_wordEUFCMA` and `exists_oneWay_iff_exists_wordSignature` on unrestricted `List Bool` messages ([rompel90][rompel90]; client checks and message-space separation witnesses in [`ComplexityTests/Crypto/Rompel.lean`](../../ComplexityTests/Crypto/Rompel.lean)). Keep the indexed game's no-repeat invariant distinct from durable storage in a deployed stateful implementation: no filesystem or crash-recovery model is asserted here.

## Commitments and ideal distributions

[CommitmentScheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Commitment/Basic.lean#L83) is intentionally distributional. It gives a faithful public-key encoding, valid messages, an exact PMF of commitment/opening pairs, verification and correctness. Efficient realization is separate. Chosen-message hiding reuses the saved-state encryption adversary; binding asks for two distinct messages opening one commitment. Pedersen's ideal exact uniform exponent law is compatible with this model even when a strict finite fair-coin implementation must approximate it. `Commitment/PublicOperations` and `PedersenCommitment/ProbComp` supply the separate public-operation and sampling bridges.

## Known Limitations

The finite query-only PRG/cipher results, semantic commitment interfaces and uniform native primitive structures do not share one implicit efficiency premise. The table records the differences. The long internal HILL and GGM proofs, all serialization helpers, and every named reduction were not independently re-proved or built in this pass. Existing nonvacuity tests are useful checks of interfaces, not evidence that cryptographic hardness assumptions hold.

[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[fly22]: ../sources.md#fly22
[ggm86]: ../sources.md#ggm86
[goldreich04]: ../sources.md#goldreich04
[hhrvw20]: ../sources.md#hhrvw20
[hill99]: ../sources.md#hill99
[holenstein06]: ../sources.md#holenstein06
[naoryung89]: ../sources.md#naoryung89
[rompel90]: ../sources.md#rompel90
