# Security games and primitive families

## Generic games and adversary quantifiers

[Game](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L67) is a `PMF Bool`. Success is its true probability; advantage is the nonnegative distance between two success probabilities. [Indistinguishable](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L154) says that every admissible complete adversary has negligible advantage as the parameter grows. `Indistinguishable.of_reduction` transfers security through a reduction with a polynomially bounded loss and negligible additive error, while `indistinguishable_pure_false_iff`, `Indistinguishable.of_succProbability_le`, and `Indistinguishable.of_succProbability_reduction` specialize one-sided search and forgery games compared against `PMF.pure false`. This layer is mathematical probability; admissibility determines the computational interpretation [cslib-frontier][complexitylib]. A `PMF` game body can bind the adversary's programs directly with `←` by importing [Lift.lean](../../CslibFrontier/Languages/Probabilistic/Lift.lean) ([Bind a program inside a distribution](../workflows/probabilistic-workflows.md#bind-a-program-inside-a-distribution)).

To write an experiment as the challenger's program, import [Game/Experiment.lean](../../CslibFrontier/Crypto/Game/Experiment.lean). `Experiment` is `ProbComp Bool`, the program whose output distribution is a `Game`. Scheme algorithms, adversaries and experiments are programs, and `ProbComp.eval` appears only in `Experiment.succProbability` and `Experiment.advantage`; as real numbers these are `Pr[e]` and `|Pr[e₀] - Pr[e₁]|` (`Experiment.coe_succProbability`, `Experiment.coe_advantage`). A `…Experiment` is one fixed instance, and a `…Game` is a family: `Game.withSetup setup exp` draws public parameters from a setup law, which need not be efficiently sampleable, and runs the fixed experiment. `Game.advantage_withSetup_le` and `Game.succProbability_withSetup_le` lift a bound that holds at every supported parameter; when the setup is a program such as key generation, `Experiment.advantage_bind_le_of_support` and `Experiment.succProbability_bind_le_of_support` do the same for `setup >>= exp`. `distAdvantage real sim D` is the advantage of a distinguisher between two view distributions, and a perfect simulation gives zero (`distAdvantage_eq_zero_of_eval_eq`). For the bit-guessing form of a pair of experiments, import [Game/HiddenBit.lean](../../CslibFrontier/Crypto/Game/HiddenBit.lean): `Experiment.guessBit e` draws a uniform hidden bit `b`, runs `e b` and wins when the output is `b`; `Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit` says the advantage between `e false` and `e true` is twice its bias, and `Game.uniform_bool_bind_map_beq_const` says a guess drawn independently of the bit is right with probability exactly one half. For adversaries that choose a challenge and then answer, import [Computational/TwoStage.lean](../../CslibFrontier/Crypto/Computational/TwoStage.lean). `TwoStage I₁ O₁ I₂ O σ` keeps a saved state of any type `σ` between its `choose` and `guess` stages. `TwoStage.IsPPT` asks a family indexed by the security parameter for one machine per stage, which reads the unary parameter and the complete encoded stage input, saved state included. The word-level adversaries are the instance `σ := List Bool`. `lrExperiment valid enc A b x` is the challenge phase of single-challenge IND-CPA (Boneh–Shoup Attack Game 11.1) on a drawn public input `x`, with message pairs `MessagePair` encoded by `encMessagePair`; each scheme's experiment draws `x` and calls it, and the simp lemma `eval_lrExperiment` gives its output distribution. The [checked clients](../../CslibFrontierTests/Crypto/Experiment.lean) cover an adversary whose left-or-right advantage is exactly one, a setup bound that depends only on supported parameters, and the derivation of `TwoStage.IsPPT` from a word-level `Encryption.AdversaryOf.IsPPT`. Statements keep named advantages in `ℝ≥0` and write every other probability as `Pr[e]`, with uniform samples as `$ᵗ α` ([State a probability and sample uniformly](../workflows/probabilistic-workflows.md#state-a-probability-and-sample-uniformly)).

For concrete `(t, q, ε)` security bounds, resource-mapping reductions, and bridges to asymptotic security, import [Game/Concrete.lean](../../CslibFrontier/Crypto/Game/Concrete.lean). `Game.IndistinguishableWithin game1 game2 Within ε` bounds `Game.advantage (game1 adversary n) (game2 adversary n) ≤ ε n r` across all adversaries satisfying `Within n r adversary`, and `Game.SuccWithin` (`indistinguishableWithin_pure_false_iff`) is its one-sided success-probability counterpart. `IndistinguishableWithin` supports equivalence/hopping laws (`.refl`, `.symm`, `.trans`, `.mono`, `.of_within`), multi-hop hybrid sums (`.hybrid`, `.hybrid_const`), and concrete reductions (`IndistinguishableWithin.of_reduction`, `SuccWithin.of_reduction`) mapping target resource budgets `r` to source budgets `mapRes n r` with error `loss n r * ε n (mapRes n r) + err n r`. Standard resource predicates `WithinQueries`, `WithinTime`, `WithinTimeUpTo`, `WithinOracleTime`, and `WithinTimeAndQueries` instantiate `Within` over `IsQueryBounded` and the plain halting predicates of [Time.lean](../../CslibFrontier/Computability/Probabilistic/Time.lean) and [Oracle/Time.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/Time.lean); because halting monotonicity needs no computability hypothesis on padded schedules, `indistinguishableWithin_withinTime_iff` and `indistinguishableWithin_withinTimeAndQueries_iff` equate scalar per-parameter bounds with global schedule bounds. To pass from concrete bounds to asymptotic `Game.Indistinguishable`, use `IndistinguishableWithin.indistinguishable` in general, `Game.Indistinguishable.of_queryBounded` / `of_queryBounded_real` / `of_birthday_queryBounded_real` / `of_succProbability_queryBounded` / `of_costBounded` (as in [PseudorandomPermutation.lean](../../CslibFrontier/Crypto/Computational/PseudorandomPermutation.lean) and [LubyRackoff.lean](../../CslibFrontier/Crypto/Computational/LubyRackoff.lean)) for `Q`-query information-theoretic hops, `Game.Indistinguishable.of_queryBounded_reduction` (built on `IsOraclePPT.exists_computable_queryBound`, as in [GGM/Security.lean](../../CslibFrontier/Crypto/Computational/GGM/Security.lean)) when a reduction takes a unary polynomial-time computable query bound `Q`, and `Game.Indistinguishable.of_timeBounded` / `of_timeAndQueryBounded` for computational `(t, ε)` and `(t, q, ε)` bounds. [Checked clients](../../CslibFrontierTests/Crypto/ConcreteSecurity.lean) verify a sharp `q / 2 ^ n` concrete bound with a `1`-query distinguisher achieving exact advantage `2 ^ (-n)`, compose a machine-certified `(t, q) ↦ (2 * t + c + 4, q)` reduction via `IndistinguishableWithin.of_reduction`, and derive asymptotic `IsOraclePPT` security via `of_timeAndQueryBounded`. To write a concrete hop sequence the way the textbooks do, as a `calc` chain of steps `Pr[G₁] ≈[ε] Pr[G₂]`, see [Step game hops](../design-and-assurance/automation.md#step-game-hops-and-align-shared-random-draws).

For native uniform quantum oracle-circuit families, [Game/Quantum.lean](../../CslibFrontier/Crypto/Game/Quantum.lean) specializes the same concrete-to-asymptotic API. `WithinOracleCircuits L n budget family` bounds qubits, elementary gates and coherent queries separately for every classical input length at most `L n`. `Indistinguishable.of_uniformOracleCircuits` derives asymptotic security from a concrete game bound and negligibility along every componentwise polynomial resource schedule; `of_succ_uniformOracleCircuits` handles one-sided success. Native generation supplies the schedules, provided `L` is polynomially bounded. The [checked resource client](../../CslibFrontierTests/QuantumOracleGames.lean) demonstrates independent budgets and a conditional transfer with error `(queries² + gates * qubits) / 2ⁿ`. A protocol must still prove the concrete premise and that its game uses only the declared input lengths. These bridges add no quantum-advice quantifier or random-oracle distribution and assert no scheme security theorem.

To quantify native quantum tests directly over word ensembles, import [Computational/Quantum.lean](../../CslibFrontier/Crypto/Computational/Quantum.lean). `NativeQuantum.test family n x` supplies `(1ⁿ, x)` as the classical input, starts every quantum-input qubit at zero, runs against the all-zero XOR oracle, and uses the first terminally measured output bit as the decision; an empty output rejects. `NativeQuantum.distinguishingGame X family n` first draws `x ← X n`, and `NativeQuantum.ComputationallyIndistinguishable X Y` requires negligible advantage for every native `UniformOracleCircuitFamily`. `SupportsLength` and `IndistinguishableWithin` expose the common challenge-length and separate qubit, gate and query bounds needed by `ComputationallyIndistinguishable.of_within`. The [checked ensemble client](../../CslibFrontierTests/Crypto/NativeQuantumIndistinguishability.lean) builds one growing family that reads the first challenge bit, proves an exact advantage of one on two point ensembles, and exercises the concrete bridge. This is a zero-advice, no-useful-oracle submodel: it does not supply QROM sampling, quantum advice, gate approximation or an equivalence with every QPPT convention.

For finite-source statistical bounds, import [StatisticalDistance/TotalVariation.lean](../../CslibFrontier/Probability/StatisticalDistance/TotalVariation.lean). `Cslib.Probability.closeTo_of_dist_le` turns a bound on the finite-PMF metric (half the L1 distance) into the existing all-event `CloseTo` relation with the same error. The bound is exact on finite types: `closeTo_coe_iff_dist_le` states `CloseTo μ ν ε ↔ dist μ ν ≤ ε` for an error `ε : ℝ≥0`, and `closeTo_iff_ofReal_dist_le` states `CloseTo μ ν ε ↔ ENNReal.ofReal (dist μ ν) ≤ ε` for `ε : ℝ≥0∞`; and `closeTo_iff_etvDist_le` relates `CloseTo` to Mathlib's total variation of `μ.toMeasure` and `ν.toMeasure` on any type with measurable singletons. Its `CloseTo.bind_left` law then handles arbitrary randomized continuations, including infinite output types. The import is pure probability and brings in no games, lattice protocols or native sampler certificates.

For adaptive stateful replacement, import [Security/Oracle.lean](../../CslibFrontier/Computability/Interactive/Security/Oracle.lean). `OracleComp.IsCostBounded.closeTo_runWith` turns a program's existing cost bound `K` and per-call `CloseTo` bounds `cost q * ε` into a bound `K * ε` on the joint result and final state. The premise compares both handlers at every identical query and starting state, including unreachable states; no coupling or finite state space is assumed. Calls of cost zero can still update a shared cache, but their joint reply/state laws must agree statistically at error zero. Charging only signing calls therefore avoids paying for unchanged hash calls or private sampling. The checked adaptive client in [OracleStatistical.lean](../../CslibFrontierTests/OracleStatistical.lean) uses two repeated signing requests, answer-dependent repeated cache reads, and a concrete nonzero error bound while preserving the cache and signing log. This shared lemma does not itself complete the native Schnorr signing-game or key-generation transport in #581. When the two handlers keep different states, related by a probabilistic map (for example a cache and its completed table), use `OracleComp.closeTo_run_interpret_simulation` in [Simulation/CloseTo.lean](../../CslibFrontier/Languages/Probabilistic/Simulation/CloseTo.lean), of which `closeTo_runWith` is the identity case.

For two continuations that agree outside a bad input event, import [Game/CloseTo/UntilBad.lean](../../CslibFrontier/Crypto/Game/CloseTo/UntilBad.lean). `CloseTo.bind_of_eq_on μ f g bad` bounds the mixtures by the actual probability `μ.toOuterMeasure bad`; agreement is required only on supported inputs outside `bad`, and neither type must be finite. This lets a cache-programming step charge only the probability that the sampled point was already cached. The [checked clients](../../CslibFrontierTests/CloseToUntilBad.lean) retain the actual Fiat–Shamir reply and final cache, show a sharp one-half error on an infinite output type, and allow arbitrary disagreement on impossible inputs at zero cost. This law does not identify different hidden cache states or justify removing aborted queries.

For a simulator that retries until an independent coin succeeds, import [Game/Retry.lean](../../CslibFrontier/Crypto/Game/Retry.lean). An attempt returning `Option β` satisfies `ProbComp.eval attempt = μ.bind (tagWith ch)` when its output follows `μ` and its success is an independent coin `ch`; `Game.advantage_bind_firstSuccess_replicate_le` then bounds the advantage of every continuation of `firstSuccess d <$> OracleComp.replicate k attempt` against `μ` by `(ch false) ^ k`. The GMW zero-knowledge simulators use it with `guessCoin`, a uniform 3-bit challenge guess, so `ch false = 7 / 8`. This is a bound on the selected output's law, not a lazy retry loop; for that, use `OracleComp.retry`.

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
| Decisional composite residuosity and Paillier encryption | [CslibFrontier/Crypto/Computational/CompositeResiduosity.lean](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean), [CslibFrontier/Crypto/Computational/Paillier.lean](../../CslibFrontier/Crypto/Computational/Paillier.lean), [CslibFrontier/Crypto/Computational/Paillier/Security.lean](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean), [CslibFrontier/Crypto/Computational/Paillier/Finite.lean](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean) | Factor pairs `(p, q)` of balanced moduli with validity in the type; arbitrary setup law; Paillier encryption with perfect correctness and plaintext-addition preservation under decryption over an abstract strict-PPT modulus generator, which is not constructed; IND-CPA security under DCR with an explicit prime-growth hypothesis; at a fixed modulus, typed Paillier with exactly uniform randomness, full Definition 15.14 and an exact CPA-to-DCR bound |
| Quadratic residuosity, Goldwasser–Micali, RSA, and Rabin factoring | [CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [CslibFrontier/Crypto/Computational/GoldwasserMicali.lean](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean), [CslibFrontier/Crypto/Computational/RSATrapdoor.lean](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), [CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean](../../CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean), [CslibFrontier/Crypto/Computational/RSAAttacks.lean](../../CslibFrontier/Crypto/Computational/RSAAttacks.lean), [CslibFrontier/Crypto/Computational/RabinFactoring.lean](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) | Composite Jacobi symbol `jacobiSymbol`, `QR_N` / `QNR_N^{+1}` split and `QuadraticResiduosityHard`; Goldwasser–Micali bit and bounded-word public-key encryption (`KeyDesc`, `encrypt`, `decrypt`, `mulCiphertexts`, ideal distributional XOR homomorphism, `INDCPA` / `INDCPAOn` under `QuadraticResiduosityHard` and explicit prime growth, and Jacobi `-1` attack); all-residue and unit-group RSA trapdoor bijection (`rsaEval`, `rsaInvert`, `RSAOneWay`); Blum-integer square roots (`blumSqrt`, `crtSqrt`), `FactoringHard`, `RabinOneWay`, and explicit PPT equivalence `rabinOneWay_iff_factoringHard` |
| LWE, SIS, and module lattices | [CslibFrontier/Crypto/Computational/LWE/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/LWE/Basic.lean), [CslibFrontier/Crypto/Computational/LWE/Decoding.lean](../../CslibFrontier/Crypto/Computational/LWE/Decoding.lean), [CslibFrontier/Crypto/Computational/LWE/KeyGen.lean](../../CslibFrontier/Crypto/Computational/LWE/KeyGen.lean), [CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean), [CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/SIS/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Ajtai.lean](../../CslibFrontier/Crypto/Computational/SIS/Ajtai.lean), [CslibFrontier/Crypto/Computational/SIS/Module.lean](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), [CslibFrontier/Crypto/Computational/LWE/Module.lean](../../CslibFrontier/Crypto/Computational/LWE/Module.lean), [CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean), [CslibFrontier/Crypto/Computational/LWE/Regev.lean](../../CslibFrontier/Crypto/Computational/LWE/Regev.lean), [CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean](../../CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean), [CslibFrontier/Crypto/Computational/LWE/DualRegev.lean](../../CslibFrontier/Crypto/Computational/LWE/DualRegev.lean), [CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean](../../CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean) | Explicit dimensions, modulus and noise/norm parameters (typed decision-LWE experiments over a finite commutative ring and `2^w` binary matrix words in `LWE/Basic.lean`, shared LWE decoding/key-generation helpers in `LWE/Decoding.lean` and `LWE/KeyGen.lean`, Micciancio–Peikert power-of-two gadget matrices, short kernel matrices (kernel membership, `det S_w = 2^w`, and column norm bounds, without the lattice-basis generation proof), tagged `GenTrap` trapdoors, and deterministic trapdoor LWE inversion in `LWE/Trapdoor/*`, the typed fixed-instance experiment `sisExperiment` over arbitrary nonzero moduli and the family hypothesis `SIS` in `SIS/Basic.lean`, the Ajtai collision-to-SIS bound `ajtaiAdvantage_le_sisAdvantage` in `SIS/Ajtai.lean`, negacyclic `R_q = ℤ_q[X]/(X^n+1)` block-anticirculant expansion `expandModuleMatrix`, `moduleSISExperiment`, `ModuleSIS` and `RingSIS` in `SIS/Module.lean`, typed decision Module-LWE games for any secret and error laws and `DecisionModuleLWE` in `LWE/Module.lean`, Module-LWE public-key encryption in `SIS/ModuleEncryption.lean`, and plain-LWE Regev and GPV dual-Regev bit encryption and IND-CPA security at modulus `2^w` in `LWE/Regev*` and `LWE/DualRegev*`); classical uniform-PPT hardness hypotheses |

The pseudoentropy gap of
[`Pseudoentropy/Basic.lean`](../../CslibFrontier/Crypto/Computational/Pseudoentropy/Basic.lean)
is `predictionExperiment` on a pair's latent draw `(x, b)`. A typed `SamplablePair.Predictor`
reads `x : pair.Observation n`, and `Predictor.IsPPT` fixes its machine input `(1ⁿ, encode n x)`
with `enc_structure`; open `Cslib.Crypto.Pseudoentropy` and
`Cslib.Crypto.Pseudoentropy.SamplablePair` for the generated rules.
`SamplablePair.hasGapWithAdvice_iff_word` restates the advised gap for word predictors on
`encAdvisedInput` in the word game `Pseudoentropy.predictionGame`, and the word-level extraction
pipeline applies it once, in `HasGapWithAdvice.eventually_indexed_error_ge`.

For the hashed-parity construction, import
[`Pseudoentropy/HashPair.lean`](../../CslibFrontier/Crypto/Computational/Pseudoentropy/HashPair.lean).
`HashPair.Observation` names the public `image`, `index`, `matrix`, `digest` and `query`.
The digest has width `index.val + 1`, while the matrix retains all sampled rows. Its
`encObservation` encoding writes those five fields in that order, with a unary index and every
field except the final query self-delimited. Open `Cslib.Crypto.Pseudoentropy.HashPair` for the
generated field-access certificates; the dependent digest is read as `List.ofFn observation.digest`.
The [checked client](../../CslibFrontierTests/Crypto/HashPair.lean) verifies the exact word layout,
uses the generated certificates to read the image and digest, and exercises zero-width inputs.
`encodeObservation` also accepts a possibly noninjective image map for the sampler's semantic
agreement theorem; the efficient pair uses `encObservation` with an injective image encoding.

For Diffie–Hellman games, import
[`DiffieHellman.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman.lean) and open
`Cslib.Crypto.PrimeOrderGroupFamily`. Fixing `F : PrimeOrderGroupFamily` fixes the family,
its element encodings and its algorithms. A value `d : F.Desc` supplies public group
parameters selecting `F.Carrier d`, `F.order d` and `F.generator d`; `F.encDesc` encodes
those parameters for algorithms. The established names `Desc` and `encDesc` refer to this
parameter type and encoding. For
[`schnorrGroups`](../../CslibFrontier/Crypto/Computational/DiscreteLog/SchnorrGroup.lean),
a parameter bundle contains `(p, q, g)` and proofs of primality and generator validity.
The concrete `d23` in the [DH client](../../CslibFrontierTests/Crypto/DiffieHellman.lean)
uses `(23, 11, 2)`: the subgroup of order `11` modulo `23` generated by `2`.

Each Diffie–Hellman game runs a fixed-group experiment from
[`DiffieHellman/Finite.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean)
in an additive group `G` that is a `ZMod q`-module, with public element `g`; prime order and
generation enter only as hypotheses of particular bounds. The table sets each step of Boneh–Shoup's
Attack Games 10.5 (CDH) and 10.6 (DDH) [bs23][bs23] beside the corresponding Lean program; `a • g`
is additive notation for the textbook `g^a`.

| Step | Textbook (Boneh–Shoup) | Lean experiment |
|---|---|---|
| CDH challenge | `α, β ←R Z_q`; send `u := g^α`, `v := g^β` | `cdhExperiment q g A`: `a ← uniform (ZMod q)`, `b ← uniform (ZMod q)`, `z ← A (a • g) (b • g)` |
| CDH outcome | adversary outputs `ŵ`; it wins if `ŵ = g^{αβ}` | `return z = (a * b) • g`; `cdhAdvantage` is the success probability |
| DDH Experiment 0 | `α, β, γ ←R Z_q`; send `(g^α, g^β, g^{αβ})` | `ddhRealExperiment q g D`: `D (a • g) (b • g) ((a * b) • g)` |
| DDH Experiment 1 | `α, β, γ ←R Z_q`; send `(g^α, g^β, g^γ)` | `ddhRandomExperiment q g D`: `D (a • g) (b • g) (c • g)` with an independent `c` |
| DDH outcome | adversary outputs a bit; advantage `\|Pr[W₀] − Pr[W₁]\|` | `ddhAdvantage q g D := Game.advantage` of the two evaluated experiments |

The book's Experiment 0 challenger also draws an unused `γ`; omitting it does not change the
distribution. The experiments draw exact uniform exponents from `ZMod q` and carry no efficiency
certificate.

The family games in `DiffieHellman.lean` draw public group parameters `d` from
`setup n : PMF F.Desc` and run these experiments in `F.Carrier d` with `q = F.order d` and
`g = F.generator d`:

- `F.cdhGame setup adversary n` runs `cdhExperiment` on `adversary n d`, where
  `adversary : F.CDHAdversary` maps the security parameter, `d` and two elements of `F.Carrier d`
  to a `ProbComp (F.Carrier d)`. `F.CDH setup` says that every adversary with
  `adversary.IsPPT` wins with negligible probability.
- `F.ddhRealGame setup distinguisher n` and `F.ddhRandomGame setup distinguisher n` run
  `ddhRealExperiment` and `ddhRandomExperiment` on `distinguisher n d`, where
  `distinguisher : F.DDHDistinguisher` maps the security parameter, `d` and three elements of
  `F.Carrier d` to a `ProbComp Bool`. `F.DDH setup` says that every distinguisher with
  `distinguisher.IsPPT` has negligible advantage between the two games.

Adversaries receive and return group elements, so a CDH adversary must output a valid element of
`F.Carrier d`. `F.CDH setup`, and with it the conclusion of `DDH.cdh`, is therefore the textbook
CDH assumption, weaker than the word-level assumption against adversaries that may output any word;
[#4783](https://github.com/cslib-community/cslib-frontier/issues/4783) tracks restoring the
word-level form for families with decodable encodings. A DDH distinguisher outputs only a bit, so
`F.DDH setup` is equivalent to the word-level assumption over distinguishers reading the encoded
tuple (`ddh_iff_encoded`), and likewise for `SecureKDF` (`secureKDF_iff_encoded`). To prove such
an equivalence for a new typed adversary, obtain the word adversary with
`IsPPTOn.exists_bool_factor` (or `IsPPTOn.exists_factor`, given an output decoder), passing the
generated layout lemma such as `encDDHInput_apply`. The typed adversary *equals* the word adversary
run on its input's words, so substitute it and apply the word-level assumption, with no
congruence argument for the game. Efficiency is
stated on encodings: `CDHAdversary.IsPPT` and `DDHDistinguisher.IsPPT` ask for one uniform strict
PPT machine that reads `F.encCDHInput` or `F.encDDHInput` and writes the encoded output element or
the output bit. The inputs are the structures `F.CDHInput` (fields `secParam`, `groupParameters`,
`leftPublic`, `rightPublic`) and `F.DDHInput` (adding `candidateShared`); `encCDHInput_apply` and
`encDDHInput_apply` give their layouts: the unary security parameter, the group parameters and the
encoded elements, each framed except the last. Setup remains an arbitrary PMF and acquires no PPT
certificate. Reductions that need exponents use `F.sampleExp n d`, with its `1 / 2 ^ n` statistical
error and separate PPT theorem `isPPTOn_sampleExp`.

`dlToCDHAdversary` and `cdhToDDHDistinguisher` are the elementary reductions behind
`CDH.discreteLog` and `DDH.cdh`. Random self-reducibility ([bs23][bs23], Exercises 10.8–10.10)
works on the same types: `ddhRerandomize` maps a triple `(u, v, w)` to a uniform real triple when
`w` is the Diffie–Hellman element and to a uniform triple otherwise (`ddhRerandomizeLaw_real`,
`ddhRerandomizeLaw_random`); `ddhSelfReduceDistinguisher` is its efficient form, so
`ddh_of_worstCase` derives `F.DDH setup` from worst-case indistinguishability of fixed triple
families with loss `6 / 2 ^ n`; and `ddhAmplifiedDecider` turns a distinguisher with
inverse-polynomial fixed-group advantage into one that decides every triple except with
negligible error (`negligible_ddhAmplifiedDecider_error`). The
[DH client](../../CslibFrontierTests/Crypto/DiffieHellman.lean) checks the DDH input layout,
runs the CDH-to-DDH reduction and the rerandomization on concrete `d23` elements, and
instantiates the amplified decider. The
[nonvacuity client](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) evaluates the real
and random games with fixed group parameters to probabilities `1 / q` and `1 / q²` for the same
efficient identity test, so a constant group fails the hardness assumptions. From the
repository root, check both clients with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.DiffieHellman CslibFrontierTests.Crypto.AssumptionNonvacuity
```

Inversion and prediction are each stated once, for a fixed function and input distribution, in
[`Crypto/Game/Inversion.lean`](../../CslibFrontier/Crypto/Game/Inversion.lean):
`inversionExperiment sample f A` draws `x`, gives `A` the image `f x` and accepts any preimage,
and `predictionExperiment sample f h P` asks `P` for the bit `h x` given `f x`. The word games
`inversionGame` (one-wayness) and `predictionGame` (hard-core predicates) run them on uniform
`n`-bit inputs, and the finite Goldreich–Levin reduction uses the same inversion experiment on
`PMF.uniformOfFintype (BitString n)`; `ProbComp.eval_inversionExperiment` moves a program
experiment to its distribution. Instantiate these experiments for a new inversion-style notion
instead of writing another sampling block. The inner product of bit lists is
[`BitString.listDot`](../../CslibFrontier/Foundations/Data/BitString/List/Dot.lean), which is
Mathlib's `dotProduct` on `List.ofFn` inputs (`listDot_ofFn`); use it, and its polynomial-time rule
`ComputableInPolyTime.bitsListDot`, instead of spelling out the zip-and-fold parity.

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

The Ideal Cipher Model models a block cipher as a key-indexed family of independent random permutation oracles supporting forward and inverse queries. [`IdealCipher.lean`](../../CslibFrontier/Languages/Probabilistic/IdealCipher.lean) formalizes lazy exact and forgetful ideal-cipher caches, proves partial bijection preservation (`uniform_interpret_eq_lazy`), and bounds the distinguishing advantage between a uniform ideal cipher and the forgetful sampler by `(Q.choose 2) * |Block|⁻¹` (`abs_sub_uniformPerm_forgetful_le`). Built upon this, [`Compression.lean`](../../CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean) models collision resistance (`collisionGame`), records the probability-`1` inverse-query attack on `cipherOutput` (`cipherOutputAdversary_wins`, [katzlindell20][katzlindell20] Exercise 7.23(a)), and proves the Davies–Meyer Ideal-Cipher collision-resistance upper bound of `2 * ((Q + 2).choose 2) * |Block|⁻¹ = ((Q + 2) * (Q + 1)) * |Block|⁻¹` for every `Q`-query adaptive adversary (`daviesMeyer_collisionGame_le`, `daviesMeyer_collisionGame_mul_le`; [katzlindell20][katzlindell20] Theorem 7.5), checked nonvacuously in [`CslibFrontierTests/Crypto/IdealCipherCompression.lean`](../../CslibFrontierTests/Crypto/IdealCipherCompression.lean).

For a fixed keyed function or block cipher over finite types, import [`Primitives/PRF/Finite.lean`](../../CslibFrontier/Crypto/Primitives/PRF/Finite.lean) and [`Primitives/PRP/Finite.lean`](../../CslibFrontier/Crypto/Primitives/PRP/Finite.lean) (Boneh–Shoup §4.1–§4.4 [bs23][bs23]). A `PRF.Adversary D R` is an adaptive oracle program with private coins. `PRF.realExperiment F A` and `PRF.idealExperiment A` are `ProbComp Bool` programs answering its queries with `F key` for a uniform key or with a uniform function `D → R`, and `PRF.advantage` is the distance between their laws. For a block cipher `E : Key → Equiv.Perm D`, `PRP.realExperiment E` is the PRF experiment of `E` and `PRP.idealExperiment` samples a uniform permutation. The switching lemma `PRP.advantage_idealExperiment_prfIdealExperiment_le` bounds the distance between the two ideal experiments by `Q.choose 2 / |D|` for a `Q`-query adversary (Theorem 4.4), and `PRP.prfAdvantage_le_advantage_add` is Corollary 4.5. `PRP.strongRealExperiment` and `PRP.strongIdealExperiment` also answer inverse queries through `RandomPermutation.PermOracleSpec D`; `PRP.StrongAdversary.ofForward` runs a forward adversary there with the same advantage (`PRP.strongAdvantage_ofForward`). These statements are single-instance and track no running time. The word-level `BlockCipher.PRP` switching lemma `advantage_prpIdealGame_randomFunctionIdealGame_le` is derived from the finite one. Checked examples are in [`CslibFrontierTests/Crypto/PseudorandomPermutation.lean`](../../CslibFrontierTests/Crypto/PseudorandomPermutation.lean).

Several independently keyed copies of a pseudorandom function are again pseudorandom: [`PseudorandomFunction.multiKey`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/MultiKey.lean) answers `t` word channels with the `n`-bit blocks of one `t * n`-bit key, against `t` independent random functions, for every fixed `t`. Its hybrid reduction `prfMultiReduction` simulates the already random channels with a lazy list cache and is itself oracle PPT; the concrete bound sums `t` PRF advantages (Boneh–Shoup, Exercise 4.26). The number of keys is a constant, not a function of the security parameter; the exercise also allows a polynomially bounded number of keys, which this theorem does not cover.

Unconditionally, any pseudorandom function on `n`-bit inputs requires at least `2 * n - 2` binary gates over the full binary Boolean basis `B₂` (`fullInterpretation (k := 2)`) on all but a negligible fraction of keys (Fan–Li–Yang §§4.2, 7.1, Theorem 7.5 [fly22][fly22]): [`CircuitLowerBound.lean`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/CircuitLowerBound.lean) proves the bound both for arbitrary `BooleanPRF` ensembles (which impose no efficient sampling or evaluation condition) and for word-valued `PseudorandomFunction` families via deterministic `BitString.lowBits`-encoded restriction queries. The underlying wire out-degree, syntactic dead-gate elimination (`Circuit.NoDeadGates`), critical-path `2 * n - 2 * m` gate bound, and `B₂` intersection bottleneck live in [`CslibFrontier/Computability/Circuit/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/CriticalPath.lean) and [`CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean). Tightness at `2 * n - 2`, distinguisher completeness, refutation of bitwise XOR, unconditional `BooleanPRF` non-vacuity on random functions, and conditional `OneWay` non-vacuity are checked in [`CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean`](../../CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean).

The main uniform construction chain is [OneWay.exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRG.lean#L54), [exists_oneWay_iff_exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PRGToOneWay.lean#L215), polynomial stretch, and [OneWay.exists_pseudorandomFunction](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRF.lean#L46). The formal abstract [hill](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CryptographyAbstract.lean#L81) (since retired) stated the one-bit expansion endpoint, and `adaptive_functions` stated the adaptive PRF endpoint, as restatements of `OneWay.exists_pseudorandomGenerator` and `OneWay.exists_pseudorandomFunction`. The forward generator proof follows the Holenstein pseudoentropy route to the Håstad–Impagliazzo–Levin–Luby theorem; the function construction follows Goldreich–Goldwasser–Micali. The cited primary sources establish the classical OWF/PRG and adaptive function-construction results [hill99][hill99] [holenstein06][holenstein06] [ggm86][ggm86]. The uniform Lean endpoint does not assume an extra entropy or nonuniform-advice premise. In parallel, relativizing the Holenstein pseudoentropy, three-source, entropy-grid, XOR-combination and reindexing pipeline to polynomially bounded advice families yields the nonuniform construction chain [`NonuniformOneWay.exists_nonuniformPRG`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L68) (one-bit stretch) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L77) (length-tripling `3 * n + 1` stretch) from any [`NonuniformOneWay`](../../CslibFrontier/Crypto/Computational/Nonuniform/Basic.lean#L286) function.

Target collision resistance (universal one-wayness) separates target selection from key sampling: in [`TargetCollisionResistant.lean`](../../CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean), `TargetCollisionFinder.choose` commits to `(m₀, state)` from `1^n` before a uniform `keyLen n`-bit key is drawn, and `TargetCollisionFinder.find` receives `(1^n, state, k)` to output `m₁` (Boneh–Shoup §8.11.2, Attack Game 8.5 and Definition 8.7 [bs23][bs23]; Naor–Yung §2 [naoryung89][naoryung89]; Goldreich §6.4.3 [goldreich04][goldreich04]). Full collision resistance implies target collision resistance with identical game success probability (`CollisionResistantOn.targetCollisionResistantOn`). Because single-key Merkle–Damgård requires the key to compute intermediate chaining targets, domain extension from `KeyedCompressionFamily` (`2M(n) → M(n)` with `n ≤ M(n)`) to unrestricted `KeyedHashFamily` on `List Bool` instead uses `uowhfTreeHash`, a total fixed-depth adaptation of level-keyed binary-tree hashing (Naor–Yung 1995 revision §2.3 [naoryung89][naoryung89]; Goldreich June 2003 chapter draft §6.4.3.2, Constructions 6.4.24/6.4.26 and Propositions 6.4.25/6.4.27 [goldreich04][goldreich04]; cf. Boneh–Shoup §8.11.3, pp. 339–340 [bs23][bs23], which instead presents a chain that reuses one compression key with `1 + log₂ L` XOR masks, so that its key is logarithmic in the message length, and mentions a tree-based alternative): `uowhfLeaves` encodes one message bit per zero-padded `M(n)`-bit leaf, `uowhfTreeLevels` folds `n` fixed halving levels under independent subkeys, `top.headD []` selects the first resulting block, and an `(n + 1)`-st subkey compresses that block with `BitString.lowBits (M n) msg.length` (`msg.length mod 2^{M(n)}`). At fixed `n`, inputs longer than `2^n` bits leave multiple blocks in `top` and `top.headD []` discards the extra roots (so out-of-capacity messages such as `[false, false, false]` and `[false, false, true]` at `n = 1` collide), whereas `KeyedCompressionFamily.targetCollisionResistant_treeHash` still holds on unrestricted `List Bool` because strict-PPT admissibility polynomially bounds the output lengths of both `choose` and `find`, placing supported `m₀` and `m₁` strictly below `2^n ≤ 2^{M(n)}` for all sufficiently large `n`; [`CslibFrontierTests/Crypto/TargetCollisionResistant.lean`](../../CslibFrontierTests/Crypto/TargetCollisionResistant.lean) gives checked instances, collision extractions and insecurity witnesses. In [`NaorYung.lean`](../../CslibFrontier/Crypto/Computational/NaorYung.lean), any `OneWayPermutation` instantiates that compression interface without trapdoors (adapting Naor–Yung §3 [naoryung89][naoryung89] and Goldreich June 2003 draft §6.4.3.2, Construction 6.4.20 and Proposition 6.4.21 [goldreich04][goldreich04]): `naorYungShrink` quotients `{0, 1}^{n+2}` by `{0, δ}` via pivot-bit canonicalization and deletion rather than an affine/Toeplitz matrix so `naorYungStep` reduces to `inversionGame` at length `n + 2` with exact loss `1` and zero additive error, `naorYungCompression` cascades `n + 1` steps (`2(n + 1) → n + 1`) with loss `dyadicSize (n + 1)`, and `naorYungHash` composes with `KeyedCompressionFamily.treeHash` (`OneWayPermutation.targetCollisionResistant_naorYungHash`, `OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`; client checks and an explicit `1 / 2`-success break of `naorYungStep id` are in [`CslibFrontierTests/Crypto/NaorYung.lean`](../../CslibFrontierTests/Crypto/NaorYung.lean)).

For universal one-way hashing from general one-way functions without permutations, [`OneWay.rompelBase_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean), [`OneWay.exists_rompelBase_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean), and [`OneWay.exists_inaccessibleEntropyFamily_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean) prove Haitner–Holenstein–Reingold–Vadhan–Wee, Section 4.2, Theorem 4.5 [hhrvw20][hhrvw20] from any uniform `OneWay` function via the `3`-wise independent Boolean affine hash family [`isThreeWiseIndependentHash_affineHash`](../../CslibFrontier/Probability/BitString/AffineHash/ThreeWise.lean), prefix-collision seed projection `adjustAffineSeed`, and dyadic `(Nat.log 2 n + 1)`-bit saturating prefix field: one single uniform polynomial-time base family `rompelBaseEvalWord g outLen` achieves an eventual `d * Real.logb 2 n / n` gap between real Shannon conditional entropy and accessible average max-entropy for every constant `d > 0` against uniform strict-PPT adversaries, witnessed at each `d > 0` by the adversary-independent accessible-set family `rompelAccessibleSet c g outLen` with polynomial light-image threshold `4 * (n + 1) ^ c * |g⁻¹(y)| ≤ 2 ^ (n - min r n)` (`rompelLightImages c`) and packaged as an [`InaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean) with integer gap denominator `rompelGapDenom c n = 64 * (n + 1) / (c * Nat.log 2 n + 1) + 1 = Θ(n / log n)` (`OneWay.exists_inaccessibleEntropyFamily` instantiates `d = 1`). [`AdversaryInaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean) states [hhrvw20][hhrvw20] Section 3.2, Definition 3.9 (p. 15) directly with adversary-dependent accessible preimage sets (`∀` uniform strict-PPT `IsWordCollisionFinder`, `∃ accSet` satisfying `IsAccessibleEntropyWitness`); word-level fallback sanitization `sanitizeWordCollisionFinder` lifts Definition 3.9 to arbitrary uniform strict-PPT adversaries (`AdversaryInaccessibleEntropyFamily.exists_accessibleSet`), and `InaccessibleEntropyFamily.toAdversaryInaccessibleEntropyFamily` embeds any fixed-witness family into it. Parallel repetition with Hoeffding concentration and dyadic planted-coordinate escape reductions ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean), Lemma 5.3) combined with two-universal input/output hashing for `1`-bit shrinkage ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean), Lemmas 5.4 and 5.5) then yield [`AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), [`InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), and [`OneWay.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (Section 5.1.5, Theorem 5.1, STEPS 1–3): because neither `shrunkHashEscapeInverter` nor `repEscapeInverter` reads the candidate index, each grid adversary `B` induces one strict-PPT base adversary whose Definition 3.9 accessible-set family selects a collision-resistant candidate sequence `goodIdx` in [`ShrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (`exists_good_candidate`). Although `goodIdx` depends on the adversary and need not be efficiently computable, [`rompelCompression`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) evaluates all `gridCount n` candidates uniformly across `rompelCascadeSteps G n = (2 * gridCount n - 1) * outLen n` XOR-masked `1`-bit shrinking steps under one shared `rompelCascadeSteps G n * inLen n`-bit step-key sequence and concatenates their outputs (`2 * (gridCount n * outLen n) → gridCount n * outLen n`; adapting [hhrvw20][hhrvw20] Section 5.1.4, Lemmas 5.6–5.7, pp. 29–30, and Section 5.1.5, STEP 4, p. 31, and STEP 5(ii–iii), p. 32, using one fresh `inLen n`-bit subkey per `1`-bit step and sharing that sequence across candidates rather than claiming Lemma 5.7's `O(|y| log t)` compact-key bound or STEP 5(iii)'s per-candidate keys; the compact keys remain open in [#4821](https://github.com/cslib-community/cslib-frontier/issues/4821)), with single-stage planted-subkey reduction `rompelCompressionInverter` (which likewise guesses `(qGuess, slot)` without reading `goodIdx`) achieving exact key simulation at multiplicative loss `dyadicSize (gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero additive error (`ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`, `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression`, `OneWay.exists_targetCollisionResistant_keyedCompressionFamily`). Composing with `KeyedCompressionFamily.treeHash` yields `rompelHash`, `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`, and `OneWay.exists_targetCollisionResistant_keyedHashFamily` ([rompel90][rompel90]; [hhrvw20][hhrvw20] Section 5.1, Theorem 5.1, p. 26), with concrete checks in [`CslibFrontierTests/Crypto/InaccessibleEntropy.lean`](../../CslibFrontierTests/Crypto/InaccessibleEntropy.lean) and [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean).

The negacyclic ring `R[X]/(X^n + 1)` on coefficient vectors lives in
[`Foundations/Algebra/Negacyclic.lean`](../../CslibFrontier/Foundations/Algebra/Negacyclic.lean),
independently of any cryptographic definition. It provides the coefficient-vector operations
`rotMatrix`, `negacyclicMul` and `innerPoly` together with their algebra and coefficient
bounds, and the typed ring `Negacyclic R n`: a one-field structure around `coeffs : Fin n → R`
whose `*` is `negacyclicMul`, a commutative ring and `R`-algebra for commutative `R`. It
represents the quotient for `n ≠ 0`; at `n = 0` it is the zero ring, a chosen zero-dimensional
extension, since the quotient there is `R[X]/(2)`.
`Negacyclic` is a structure rather than a synonym for `Fin n → R`, so the pointwise product of
the function type cannot be used by mistake. Move between the two views with `ofCoeffs`,
`coeffs` and `coeffsLinearEquiv`; `coeffs_mul` and `ofCoeffs_innerPoly` translate products and
inner products. The [checked examples](../../CslibFrontierTests/Foundations/Algebra/Negacyclic.lean)
include `X^4 = -1` over `ZMod 7` and dimension zero, where `1 = 0`.

The polynomial interpretation is proved in
[`SIS/Polynomial.lean`](../../CslibFrontier/Crypto/Computational/SIS/Polynomial.lean).
For `n ≠ 0` and a nontrivial commutative ring `R`, `negacyclicEquiv` is an `R`-algebra
equivalence `Negacyclic R n ≃ₐ[R] AdjoinRoot (X^n + 1)`, so `map_mul` carries
negacyclic multiplication to quotient multiplication and injectivity reflects quotient equalities
back to coefficient vectors. In
[`SIS/Module.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module.lean),
`ofCoeffs_comp_moduleSISMap` reads the existing Module-SIS map as a matrix-vector product over
`Negacyclic (ZMod q) n` and `moduleSISMap_eq_zero_iff` restates its zero equation there; neither
needs the quotient. `negacyclicEquiv_mulVec` then carries any such product entrywise to the
quotient ring. The checked examples in
[`NegacyclicPolynomial.lean`](../../CslibFrontierTests/Crypto/NegacyclicPolynomial.lean) include
integers, composite modulus `6`, characteristic `2`, dimension `1`, and reflection of the
Module-SIS zero equation. Dimension zero is excluded because its quotient is `R[X]/(2)`, while
`Negacyclic R 0` is the zero ring. This algebraic bridge adds no hardness or runtime claim.

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

Plain-LWE bit encryption at modulus `2 ^ w` is formalized in [`LWE/Regev.lean`](../../CslibFrontier/Crypto/Computational/LWE/Regev.lean) and [`LWE/Regev/Security.lean`](../../CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean) (checked in [`CslibFrontierTests/Crypto/Regev.lean`](../../CslibFrontierTests/Crypto/Regev.lean)). Primal Regev encryption (`Regev.encryptWithCoins`, `Regev.decrypt`) uses a noisy LWE public key and binary subset-sum encryption coins `xᵀ A + (μ * 2 ^ (w - 1), 0, …, 0)`, giving zero-error worst-case decryption when key-generation errors are bounded entrywise in `Int.natAbs` by `η` with `4 * (m * η) < 2 ^ w` (`Regev.decrypt_encryptWithCoins`, `Regev.keyGen_encrypt_correct`). For the shared serialized LWE key generator `LWE.keyGenSerialized` and `Regev.encryptSerialized`, `Regev.indCPA_of_decisionLWE` proves native single-challenge `Encryption.INDCPA` for polynomial-time schedules `n`, `m`, `w` satisfying eventually `(n + 1) * w + 2 * security ≤ m` under `DecisionLWE` for the centered-binomial law `LWE.noiseLaw (w k) (η k)`, via the concrete bound `Regev.advantage_game_le` (at most `2` times the advantage of the uniform PPT reduction `Regev.lweDistinguisher` plus `Regev.hidingError = √(2 ^ ((n + 1) * w) / 2 ^ m)`). The statistical step is typed: `Regev.challengeGame keys A b` is `Game.withSetup keys` of the shared `lrExperiment` with Regev encryption, played by a `TwoStage` adversary `A` on public matrices and ciphertexts, and `Regev.challengeGame_uniform_advantage_le` bounds it under a uniform matrix; `Regev.publicKeyGame_uniformEnsemble` identifies the word experiment with the one played by `Regev.typedAdversary`, which reads both inputs through their canonical encodings. Typed adaptive `Q`-query left-or-right bounds `Regev.lorGame_uniform_advantage_le` and `Regev.lorGame_advantage_le` hold for unbounded typed `Regev.LoRAdversary` (`Regev.lorDistinguisher` carries no native PPT certificate).

[`LWE/DualRegev.lean`](../../CslibFrontier/Crypto/Computational/LWE/DualRegev.lean) formalizes Gentry–Peikert–Vaikuntanathan's plain-LWE dual scheme at modulus `2 ^ w`: a short integer secret `e`, the noiseless syndrome public key `(A, eᵀ A)`, and LWE-style noisy encryption `(A s + x, ⟨u, s⟩ + x₀ + μ * 2 ^ (w - 1))` (contrasting with primal Regev's noisy public key and binary subset-sum coins, and with `moduleLWEKeyGen` / `moduleLWEEncrypt` in [`SIS/ModuleEncryption.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean), whose public key `(A, A s + e)` is itself a noisy Module-LWE sample over `ℤ_q[X]/(X^n+1)`). With secret entries bounded in `Int.natAbs` by `β` and encryption errors bounded by `η`, `DualRegev.decrypt_encryptWithCoins` proves zero-error decryption when `4 * (m * β * η + η) < 2 ^ w`; for generated binary secrets (`β = 1`), `DualRegev.keyGen_encrypt_correct` requires `4 * (m * η + η) < 2 ^ w`, and for trapdoor-extracted keys under the support-only preimage condition `DualRegev.GPVTrapdoor.SamplesShortPreimages`, `DualRegev.GPVTrapdoor.decrypt_encryptWithCoins_extract` establishes decryption correctness. `DualRegev.dist_keyGen_uniform_le` bounds the statistical distance of the binary-secret public key from uniform; in [`LWE/DualRegev/Security.lean`](../../CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean), `DualRegev.indCPA_of_decisionLWE` establishes native single-challenge `Encryption.INDCPA` for `DualRegev.keyGenSerialized` and `DualRegev.encryptSerialized` under `(m + 1)`-sample `DecisionLWE` for `LWE.noiseLaw` when polynomial-time schedules eventually satisfy `w * n + 2 * security ≤ m` (via `DualRegev.advantage_game_le`, checked in [`CslibFrontierTests/Crypto/Regev.lean`](../../CslibFrontierTests/Crypto/Regev.lean)).

Micciancio–Peikert gadget-based lattice trapdoors over `ZMod (2 ^ w)` (IACR ePrint 2011/501, Sections 4–5) are in [`LWE/Trapdoor/Gadget.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean) and [`LWE/Trapdoor/Basic.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean) (re-exported by [`LWE/Trapdoor.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor.lean) and checked in [`CslibFrontierTests/Crypto/Computational/LWE/Trapdoor.lean`](../../CslibFrontierTests/Crypto/Computational/LWE/Trapdoor.lean)). `Gadget.lean` connects the power-of-two gadget matrix `gadgetMatrix w` (`G = I_ι ⊗ gᵀ`) to `GSW.bitCompose` and `GSW.powersOfTwo` (`gadgetMatrix_mulVec`, `vecMul_gadgetMatrix`), proves that binary decomposition is a right inverse, `G *ᵥ gadgetDecomp w u = u`, so `G` is primitive (`gadgetMatrix_mul_gadgetDecompMatrix`, `gadgetMatrix_surjective`), shows that `scalarBasis w` (`S_w`) has determinant `2 ^ w` (`det_scalarBasis`) and that the columns of `S_w` and of the block matrix `gadgetBasis w` (`S = I_ι ⊗ S_w`) lie in `Λ^⊥(gᵀ)` and `Λ^⊥(G)` respectively with entries at most `2` and squared column length at most `5` (`gadgetVector_vecMul_scalarBasis`, `gadgetMatrix_mul_gadgetBasis`, `sum_sq_scalarBasis_col_le_five`, `sum_sq_gadgetBasis_col_le_five`; Proposition 4.2), and proves that the iterative inversion of Section 4.1 recovers `s` from `sᵀ G + eᵀ` whenever `4 * |e p| < 2 ^ w` (`invertScalar_correct`, `invertGadget_gadgetLWE`). `Basic.lean` defines the tagged matrix `taggedMatrix w Abar R H = [Abar | H * G - Abar * R]` of Algorithm 1, proves the unrestricted tag identity `A * [R; I] = H * G` (`taggedMatrix_mul_trapdoorTransform`), and defines `IsHTagTrapdoor` requiring both `A * [R; I] = H * G` and an invertible tag `IsUnit H` as in Definition 5.2 (`isHTagTrapdoor_taggedMatrix`, `isHTagTrapdoor_untaggedMatrix`, `IsHTagTrapdoor.surjective`). It lifts binary gadget preimages to short preimages under `A` (`taggedMatrix_mulVec_invertSyndrome`) and lifts `S` to the kernel vectors `[R; I] * S` of `A`, the right-hand block of the basis in Lemma 5.3 (`taggedMatrix_mul_extendedGadgetBasis`). For Algorithm 2, it proves recovery of `s` whenever the projected error `e_1ᵀ R + e_2ᵀ` has every coordinate below `2 ^ w / 4` (`invertLWESecret_trapdoorLWE`), exact recovery of `(s, e)` when in addition every original error coordinate satisfies `2 * |e k| < 2 ^ w` (`invertLWE_trapdoorLWE`), and both from the entrywise bound `4 * (1 + |μ| * B_R) * B_e < 2 ^ w` (`invertLWE_trapdoorLWE_of_norm_bound`), the deterministic part of Theorem 5.4 with infinity-norm hypotheses. `genTrap` samples Algorithm 1 with centered-binomial `R` (`mem_support_genTrap`), and in the idealized hybrid `genTrapIdeal`, where `Abar * R` is replaced by a uniform block, the public matrix is exactly uniform for every tag (`eval_genTrapIdeal_eq_uniform`). Not formalized: the step from `genTrap` to `genTrapIdeal` (regularity or decision-LWE), so the near-uniformity of `A` in Theorem 5.1 is not proved; the basis property of `S_w` and the full basis of Lemma 5.3; the Gaussian-error claim of Theorem 5.4; non-power-of-two moduli; and discrete-Gaussian preimage sampling and delegation (Sections 5.4–5.5).

ML-DSA (CRYSTALS-Dilithium) is in [`MLDSA/Decompose.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Decompose.lean),
[`MLDSA/Basic.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Basic.lean) and
[`MLDSA/KeyOnly.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/KeyOnly.lean). `decompose`,
`highBits` and `lowBits` follow the FIPS 204 rounding with its `q - 1` wrap-around rule; the
reusable facts are uniqueness of the decomposition (`decompose_intCast_mul_add`) and stability of
the high bits under `β`-short perturbations (`highBits_add_of_abs_lowBits_lt`). `signAttempt`,
`sign` and `verify` model the uncompressed-public-key scheme with an arbitrary hash-to-ball
function and mask sampler (no Power2Round, hints, byte encodings or seed expansion), and
`verify_sign` proves correctness under `Params.Valid`, which the three standard parameter sets
satisfy. `succProbability_koaGame_le` bounds key-only forgery by the Module-LWE advantage
`ModuleLWE.advantage` of `forgeryDistinguisher` for the short secret and error laws plus the
self-target MSIS success of `selfTargetReduction`;
chosen-message security, which needs signing-oracle simulation in the random-oracle model, is not
formalized. The [checked examples](../../CslibFrontierTests/Crypto/MLDSA.lean) cover the wrap-around
case and a toy instance that signs, verifies, rejects a modified response and yields a self-target
solution.

These are implications from hardness assumptions. They do not prove that a concrete OWF, DDH group, LWE family or SIS parameter choice is hard. `DecisionLWE` runs the fixed-instance experiments `LWE.realExperiment` and `LWE.randomExperiment` over `ZMod (2 ^ w)`: a typed distinguisher receives a uniform matrix `A` and either `A t + e`, with independent errors and one shared uniform secret, or an independent uniform vector. For other secret and error laws over any finite commutative ring, `LWE.advantage` is the distance between `LWE.realGame` and `LWE.randomGame`. The distinguisher's machine reads only the row-major binary word of `[b | A]`, and `decisionLWE_iff_encoded` shows that this is the word-level assumption on the serialized public matrix `[B*t+e | B]` (checked in [`CslibFrontierTests/Crypto/DecisionLWE.lean`](../../CslibFrontierTests/Crypto/DecisionLWE.lean)); in [`SIS/Module.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), `expandModuleMatrix` and `flattenPolyVec` embed negacyclic `ModuleSIS` and `ModuleLWE` instances over `ℤ_q[X]/(X^n+1)` into unstructured `(d * n) × (k * n)` matrices over `ℤ_q` (checked with concrete evaluations and nonvacuity proofs in [`CslibFrontierTests/Crypto/ModuleSIS.lean`](../../CslibFrontierTests/Crypto/ModuleSIS.lean)); [`LWE/Module.lean`](../../CslibFrontier/Crypto/Computational/LWE/Module.lean) states decision Module-LWE as the typed games `ModuleLWE.realGame` and `ModuleLWE.randomGame` for any secret and error laws, whose advantage `ModuleLWE.advantage` is the LWE advantage over the ring `Negacyclic (ZMod q) n` (`ModuleLWE.advantage_eq_lweAdvantage`), and `DecisionModuleLWE` fixes a uniform secret and is the word-level assumption by `decisionModuleLWE_iff_encoded` (checked in [`CslibFrontierTests/Crypto/DecisionModuleLWE.lean`](../../CslibFrontierTests/Crypto/DecisionModuleLWE.lean)); and [`SIS/ModuleEncryption.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean) builds Module-LWE public-key encryption (`moduleLWEKeyGen`, `moduleLWEEncrypt`, `moduleLWEDecrypt`), bounded-noise decryption correctness (`moduleLWEDecrypt_moduleLWEEncrypt_eq`), and two-hop public-key/ciphertext reductions to `ModuleLWE.sampleLaw` (`advantage_realEncryptionView_uniform_le`, `advantage_realEncryptionView_msg_le`, checked in [`CslibFrontierTests/Crypto/ModuleEncryption.lean`](../../CslibFrontierTests/Crypto/ModuleEncryption.lean)); no worst-case lattice reduction is asserted there.

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
uses `SIS.encodeMatrix (extendCiphertext ct)`. Decryption evaluates each secret polynomial's
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
sampled residue law against uniform `ZMod q` within `q / 2^width`. In the same module,
`Game.advantage_bind_sampleModNat_fin_le` and `Game.advantage_bind_sampleModNat_fin_fin_le` bound
the advantage lost when one or two uniform `Fin` draws are replaced by `sampleModNat` draws.

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
modular `LWE.noiseLaw`. Under `2*η < 2^w`, every sampled integer is its residue's centered lift,
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
`SIS.encodeMatrix (extendCiphertext (moduleLWEModulusSwitch p ct))`, so there is no
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

For composite-modulus number-theoretic hardness assumptions, import [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), and [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], §§9.2.3–9.2.4, §15.1.1, §§15.4.1–15.4.3, and §§15.5.1–15.5.2; checked examples and reduction clients are in [`CslibFrontierTests/Crypto/QuadraticResiduosity.lean`](../../CslibFrontierTests/Crypto/QuadraticResiduosity.lean), [`CslibFrontierTests/Crypto/RSATrapdoor.lean`](../../CslibFrontierTests/Crypto/RSATrapdoor.lean), and [`CslibFrontierTests/Crypto/RabinFactoring.lean`](../../CslibFrontierTests/Crypto/RabinFactoring.lean)). In [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean) ([katzlindell20][katzlindell20], Proposition 15.23 and Definition 15.27), quadratic residues reuse Mathlib's `IsSquare` and `Subgroup.square` (`Subgroup.mem_square`, `mem_quadResidueSet_iff`), `jacobiSymbol p q` multiplies the Legendre symbols on `(ZMod (p * q))ˣ`, `jacobiPosSet_eq_disjoint_union` and `card_quadResidueSet_eq_card_positiveNonresidues` partition `J_N^{+1}` into equal-sized `quadResidueSet` (`QR_N`) and `positiveNonresidues` (`QNR_N^{+1}`) for distinct odd primes `p ≠ q`, `blumSqrt p q` inverts squaring on `QR_N` for Blum moduli `IsBlumModulus p q` (`blumSqrt_sq`, `sq_bijOn_quadResidueSet`, `neg_one_mem_positiveNonresidues`), and `QuadraticResiduosityHard` compares `qrRealGame` against `qrIdealGame`. The unit Chinese remainder isomorphism `ZMod.unitsChineseRemainder` and the square facts behind the count (`ZMod.isSquare_iff_unitsChineseRemainder`, `ZMod.two_mul_card_squares_units`) are in [`ZMod/CRTUnits.lean`](../../CslibFrontier/Foundations/Data/ZMod/CRTUnits.lean). In [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean) ([katzlindell20][katzlindell20], Definitions 9.46 and 15.1), `rsaEval N e x = x ^ e % N` and `rsaInvert N d y = y ^ d % N` are certified in polynomial time (`computableInPolyTime_rsaEval`, `computableInPolyTime_rsaInvert`) and proved mutually inverse across all residues `x < N` (`rsaInvert_rsaEval`, `rsaEval_rsaInvert`), inducing bijections both on `Fin N` (`rsaEval_bijective_fin`, including nonunits dividing `p` or `q`) and on `(ZMod N)ˣ` (`rsaEval_bijective_units`), with `rsaInversionGame` running `inversionExperiment` on `x` drawn uniformly from `Fin desc.modulus` (`RSAOneWay`, whereas Definition 9.46 samples uniformly from `(ZMod N)ˣ`). An `RSAInverter` maps the security parameter, a public key `pk : RSAPublicKey` (fields `N`, `e`) and a residue `y : Fin pk.N` to a `ProbComp (Fin pk.N)`; `RSAInverter.IsPPT` asks for one uniform strict PPT machine reading `encRSAInput` (the unary security parameter, the public key `(N, e)` (`N` framed followed by `e`), and `y` in binary, each of the three fields framed except the last) and writing the returned residue in binary. Because RSA evaluation is a bijection on `Fin N`, accepting any preimage is the same as recovering `x` (`rsaInversionGame_eq`), and `rsaOneWay_iff_encoded` shows that `RSAOneWay` is the word-level assumption over inverters that read the same layout on keys with `0 < N` and may output any natural number. In [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], Definition 9.45, Lemma 15.35, Theorem 15.36, Proposition 15.37, and Theorem 15.38), `rabinOneWay_iff_factoringHard` establishes `RabinOneWay gen ↔ FactoringHard gen` for Blum moduli via explicit certified PPT reductions `factorToRabin` (computing `crtSqrt y a b` from a nontrivial factorization `a * b = N`, with exact loss `1` in `succProbability_factoringGame_le`) and `rabinToFactor` (`rabinOneWay_of_factoringHard`, `factoringHard_of_rabinOneWay`). Across all three modules, generator families (`setup : ℕ → PMF ModulusDesc`, `RSAGen := ℕ → PMF RSADesc`, `BlumGen := ℕ → PMF BlumDesc`) are arbitrary `PMF` families over valid parameter tuples without bundled prime-generation algorithms or bit-length bounds in `n`, and adversaries/reductions use uniform native strict-PPT (`IsPPTOn`) on `(1^n, ...)` with binary `encNat` encodings (charging the full encoded input and sampled/callback output uniformly before `n`). Rather than assuming an exact uniform sampler on `(ZMod N)ˣ`, `rabinInversionGame` and `rabinToFactor` use an original dyadic all-residue sampling variant that draws a uniform `2 * N.bits.length`-bit list `r` (`x = ofBits r < 2^(2 * bits(N))` with `N^2 ≤ 2^(2 * bits(N))`) and squares `x` modulo `N`: `rabinToFactor` checks `1 < gcd(x, N) < N` first and otherwise queries the inverter on `x^2 % N` to return `rabinFactorPair (x + x') N`, yielding the concrete factor-`3` reduction bound `succProbability_rabinInversionGame_le` without modular rejection-sampling error.

For the Miller–Rabin test as a probabilistic program and for random prime and modulus
generation, import [`MillerRabin.lean`](../../CslibFrontier/Crypto/Computational/MillerRabin.lean)
and [`ModulusGeneration.lean`](../../CslibFrontier/Crypto/Computational/ModulusGeneration.lean)
([katzlindell20][katzlindell20], §§9.2.1–9.2.3, Theorems 9.32 and 9.33 and Algorithm 9.34; checked instances
are in [`CslibFrontierTests/Crypto/MillerRabin.lean`](../../CslibFrontierTests/Crypto/MillerRabin.lean)).
`millerRabinTest n t` runs `t` independent rounds (`millerRabinRound`), each of which negates the
coRP verifier `Complexity.MillerRabin.verifier` on `2 |n|` fresh coins. A prime always passes
(`eval_millerRabinTest_of_prime`), any other `n` passes with probability at most `2⁻ᵗ`
(`eval_millerRabinTest_le_of_not_prime`, reusing `ZMod.two_mul_card_isStrongLiar_le`), and the test
is uniform strict PPT on `(n, 1^t)` (`isPPTOn_millerRabinTest`). `randomPrime n` makes up to `3 n²`
attempts, each drawing a uniform `n`-bit candidate with leading bit `1` (`primeCandidate`) and
running `n` rounds of the test, and returns `none` when every attempt fails. A returned number is
not prime with probability at most `3 n² · 2⁻ⁿ` (`toOuterMeasure_randomPrime_not_prime_le`), has
exactly `n` bits (`mem_support_randomPrime`), and all `n`-bit primes are returned with the same
probability (`eval_randomPrime_some_eq`); the generator is uniform strict PPT on `1^n`
(`isPPTOn_randomPrime`). `genModulus n` multiplies two independent outputs into `(N, p, q)`
(`isPPTOn_genModulus`). Its outputs are not certified, so it is not a `PMF ModulusDesc` or
`BalancedModulus.Desc` family. The density of the `n`-bit primes ([katzlindell20][katzlindell20],
Theorem 9.32), proved in
[`PrimeDensity.lean`](../../CslibFrontier/Foundations/NumberTheory/PrimeDensity.lean)
(`Nat.two_pow_sub_one_le_three_mul_card_primes`) by Erdős's central binomial argument
(`Nat.centralBinom_le_pow_card_primes_Ico`, in
[`CentralBinomPrimes.lean`](../../CslibFrontier/Foundations/NumberTheory/CentralBinomPrimes.lean),
which `PrimeWindow.lean` shares), makes a
candidate prime with probability at least `1 / (3 n)` for `n > 1`
(`inv_three_mul_le_toOuterMeasure_primeCandidate_prime`). So for `n > 1` the generator returns
`none` with probability at most `2⁻ⁿ` (`eval_randomPrime_none_le_inv_two_pow`), and `genModulus`
returns an invalid output with probability at most `(6 n² + 2) · 2⁻ⁿ`
(`toOuterMeasure_genModulus_invalid_le_inv_two_pow`, from the bound
`toOuterMeasure_genModulus_invalid_le` in terms of the probability that a candidate is not prime).

For composite residuosity and Paillier encryption, import
[`CompositeResiduosity.lean`](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean) and
[`Paillier.lean`](../../CslibFrontier/Crypto/Computational/Paillier.lean), for IND-CPA security
[`Paillier/Security.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean), and for
the scheme at a fixed modulus
[`Paillier/Finite.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean)
([katzlindell20][katzlindell20], Chapter 15, Proposition 15.6, Claims 15.7–15.9, Definition 15.10,
Construction 15.11, Example 15.12, Theorem 15.13, and Definition 15.14; checked instances are in
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean)).
A balanced modulus is a product `N = p * q` of distinct odd primes of the same bit length
(`BalancedModulus.Valid (p, q)`). The Decisional Composite Residuosity assumption
`DCR setup` ([katzlindell20][katzlindell20], Definition 15.10) compares `dcrRealGame` (drawing an
`N`-th residue `r ^ N mod N ^ 2` for a uniform unit `r`) against `dcrRandomGame` (drawing a uniform
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

For the word scheme only this decryption-side addition identity is established; the second condition
of Katz–Lindell Definition 15.14—distributional equality between combined ciphertexts and fresh
encryptions of the sum—does not hold for the dyadic sampler with `unitOrOne` (e.g. at `N = 143`,
`n = 0`, and `m₁ = m₂ = 0`, fresh `encNat 1` has mass `44 / 256`, whereas multiplying two independent
encryptions yields mass `2316 / 65536 = 579 / 16384`).

[`Paillier/Finite.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean) states the
scheme at one modulus `N` with typed values, as the Diffie–Hellman experiments are stated at one
group. `paillierEncrypt N m` draws `r` uniformly from the units `(ZMod N)ˣ` and returns the unit
`oneAddPowHom N (ofAdd m) * powSelfHom N r` of `ZMod (N ^ 2)`; `paillierDecrypt N t c` is
`logOneAdd N (c ^ t) * t⁻¹`, where `Paillier.logOneAdd` is the function `L` of Construction 15.11.
With `t = φ(N)` and `gcd(N, φ(N)) = 1`, decryption is perfectly correct
(`paillierDecrypt_of_mem_support`) and additive on products (`paillierDecrypt_mul`), and the
second condition of Definition 15.14 holds: multiplying any encryption of `m₁` by a fresh
encryption of `m₂` gives exactly a fresh encryption of `m₁ + m₂` (`eval_mul_paillierEncrypt`,
`eval_paillierEncrypt_mul_paillierEncrypt`). The fixed-modulus DCR worlds `dcrRealExperiment N D`
and `dcrRandomExperiment N D` are in
[`CompositeResiduosity/Finite.lean`](../../CslibFrontier/Crypto/Computational/CompositeResiduosity/Finite.lean),
and the asymptotic games `dcrRealGame` and `dcrRandomGame` are `Game.withSetup` over them.
`paillierCPAExperiment N A b` is the left-or-right experiment `lrExperiment` against a two-stage
adversary `A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ` that receives the public
key `N`. `paillierCPAAdvantage_le_dcrAdvantage` bounds its
advantage by `dcrAdvantage N (paillierToDCR N A false) + dcrAdvantage N (paillierToDCR N A true)`,
with no sampling loss. Connecting this bound to `DCR` and to the word scheme is a separate step.

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
[`UnitSampling.lean`](../../CslibFrontier/Crypto/Computational/UnitSampling.lean), which also
defines `unitOrOne`; both are shared with Goldwasser–Micali below), so the IND-CPA advantage is at most `10 / 2 ^ n` plus the two DCR
advantages; without a growth condition on the primes the non-unit loss need not be negligible. The
distributional-homomorphism gap above is unaffected.
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean) checks the
concrete parameters of Example 15.12 (`N = 187`, `m = 175`, `r = 83`, `c = 23911`), homomorphic
decryption to `12` and `7` modulo `143`, validity of `(11, 13)`, uniform strict PPT for a constant
generator `constGen`, and end-to-end correctness and homomorphic addition on its supported key pair;
for IND-CPA it evaluates `validMessages` on admissible and inadmissible pairs and applies
`isPPTOn_dcrDistinguisher` and `DCR.indcpaOn_paillier` to a concrete strict-PPT adversary. At
`N = 143` it applies fixed-modulus correctness, additive decryption, the distributional
homomorphism and `paillierCPAAdvantage_le_dcrAdvantage` to a concrete two-stage adversary.

For Goldwasser–Micali public-key encryption under `QuadraticResiduosityHard`, import
[`GoldwasserMicali.lean`](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean)
([katzlindell20][katzlindell20], §15.4.4, Definition 15.14, Construction 15.28, Theorem 15.29, and
Exercises 15.11–15.12; checked instances are in
[`CslibFrontierTests/Crypto/GoldwasserMicali.lean`](../../CslibFrontierTests/Crypto/GoldwasserMicali.lean)).
`KeyDesc` extends `ModulusDesc` (distinct odd primes `p`, `q`) with a residue `z < p * q`
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

For two-party key exchange secure against passive eavesdroppers ([katzlindell20][katzlindell20], §11.3, Definition 11.1, Construction 11.2, Theorem 11.3, pp. 390–395, and Exercises 11.3–11.4, pp. 399–400), import [`KeyExchange.lean`](../../CslibFrontier/Crypto/Computational/KeyExchange.lean) and [`Encryption/PublicKeyCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyCPA.lean) (checked in [`CslibFrontierTests/Crypto/KeyExchange.lean`](../../CslibFrontierTests/Crypto/KeyExchange.lean)). `KeyExchange T K` models a protocol by its honest-execution law `execute : ℕ → PMF (Outcome T K)`, with keys in a set `K transcript` named by the transcript (`KeyExchange.Correct`; honest-party efficiency is not bundled). An `Eavesdropper T K` is typed: it receives the security parameter and a `View T K` (a transcript and a candidate key), and its efficiency is `Eavesdropper.IsPPT encT encK`, read through the `enc_structure` encoding `encView`. `realGame` and `idealGame` draw the view `realView` (transcript and Alice's key) or `idealView` (transcript and a fresh ideal key) and run the eavesdropper on it (`EavSecure`, `EavSecureBits`); `withSetup_realView_bind` and `withSetup_idealView_bind` split off a setup draw. Over any `PrimeOrderGroupFamily`, the transcript is the record `DHTranscript` and the key a group element (`DHKey`, `encDHKey`). At a fixed group, `dhExecution` is correct (`dhKeyExchange_correct`) and its real and ideal experiments are the DDH experiments of the typed distinguisher `dhEavToDDH` (`withSetup_realView_dhExecution`, `withSetup_idealView_dhExecution`); `dhKeyExchange setup` draws the group first, which gives `realGame_dhKeyExchange`, `idealGame_dhKeyExchange` and `EavSecure` against the uniform group-element ideal key `dhIdealKey` under `DDH` (`DDH.dhKeyExchange_eavSecure`). The test derives the word-level statement for eavesdroppers on the encoded transcript and key. At a fixed group, the active man-in-the-middle execution `dhMitmExecution` shares keys with both parties while each party's view has the law of `realView` of an honest execution (`dhMitmExecution_keys`, `map_aliceView_dhMitmExecution`, `map_bobView_dhMitmExecution`), and the 3-message XOR protocol `xorKeyExchange`, whose transcript is the record `XorTranscript`, is correct yet broken with advantage at least `1 / 2` by `xorEavesdropper` (`isPPT_xorEavesdropper`, `not_eavSecureBits_xorKeyExchange`). In `Encryption/PublicKeyCPA.lean`, `cpaOracleGameOn`, `WordINDCPAOracleOn`, and `WordINDCPAOracle` equip both stages of a `WordCPAAdversary` with an explicit public-key encryption oracle `encryptionOracle`, and `INDCPAOn.wordINDCPAOracleOn` and `WordINDCPA.wordINDCPAOracle` prove that single-challenge eavesdropping security implies oracle-CPA security whenever `encrypt` is uniform strict PPT ([katzlindell20][katzlindell20], §12.2.1, Proposition 12.3, p. 406; the multi-message left-or-right Theorem 12.6 is not formalized).

For the RSA least-significant-bit experiment and algebraic attacks on plain RSA, import [`RSALeastSignificantBit.lean`](../../CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean) and [`RSAAttacks.lean`](../../CslibFrontier/Crypto/Computational/RSAAttacks.lean) ([katzlindell20][katzlindell20], §9.2.5, pp. 334–336, §12.5.1, pp. 436–440, and §12.5.3, pp. 443–445; checked instances are in [`CslibFrontierTests/Crypto/RSALeastSignificantBit.lean`](../../CslibFrontierTests/Crypto/RSALeastSignificantBit.lean) and [`CslibFrontierTests/Crypto/RSAAttacks.lean`](../../CslibFrontierTests/Crypto/RSAAttacks.lean)). `rsaLSBGame` samples `desc ← gen n` and a uniform residue `x ← Fin desc.modulus` (matching `rsaInversionGame` rather than `(ZMod N)ˣ`), and `RSAHardCoreLSB gen` asks every `RSAPredictor` with `RSAPredictor.IsPPT` (reading `encRSAInput` and writing a bit) to have negligible `Game.guessingAdvantage` for `x.testBit 0` given `pk.eval x`; since the output is a bit, this is the word-level assumption on `(1^n, ((N, e), rsaEval N e x))` for keys with `0 < N` (`rsaHardCoreLSB_iff_encoded`). For odd `N`, `two_pow_mul_mod_mod_two` equates the parity of `2 ^ k * x % N` (`k ≠ 0`) with that of `⌊2 ^ k * x / N⌋`, `lsbRecover_lsbQueries` recovers `x` from the parities of the preimages of the `m` doubling queries `2 ^ (k * e) * y % N` once `N ≤ 2 ^ m`, and `lsbInverter` wins `rsaInversionGame` with probability `1` given a predictor that is always correct on the modulus (`eval_lsbInverter`, `succProbability_rsaInversionGame_lsbInverter`; the noisy reconstruction of Theorem 12.31 for predictors with small bias and a PPT certificate for `lsbInverter` are not formalized). `RSAAttacks.lean` proves plain-RSA multiplicative malleability (`rsaEval_mul`, `rsaInvert_rsaEval_mul`), common-modulus recovery of units under coprime exponents via `zmodIntPow` (`commonModulusAttack_rsaEval`), unreduced short-message and pairwise-coprime CRT broadcast `e`-th root recovery (`rsaEval_eq_pow_of_pow_lt`, `eq_of_pow_eq_rsaEval`, `chineseRemainderOfList_rsaEval_eq_pow`, `eq_of_pow_eq_chineseRemainderOfList_rsaEval`), factoring `N` from `(N, φ(N))` (`factorOfTotient_eq`, `RSADesc.factorOfTotient_eq`), and the deterministic steps `RSADesc.pow_mul_sub_one_modEq_one` and `RSADesc.gcd_sub_one_proper` of Corollary 9.51 without claiming the randomized factoring bound.

### Elliptic curves over finite fields and Hasse's bound

Import [`EllipticCurve/Hasse.lean`](../../CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/Hasse.lean)
(`CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Hasse`). This is mathematics with no
machine model, group-law algorithm or running time. A curve is Mathlib's `WeierstrassCurve F`, and
its points are the type `W.toAffine.Point`: the point at infinity together with the nonsingular
affine solutions of the Weierstrass equation. The number of points is
`Nat.card W.toAffine.Point`, which is finite over a finite field. The instance `[W.IsElliptic]`
says that the discriminant `W.Δ` is a unit. For a concrete curve over `ZMod p`, prove `W.Δ ≠ 0`
by `decide` and build the instance as `⟨isUnit_iff_ne_zero.2 h⟩`.

- **Odd characteristic.** For a finite field `F` with `ringChar F ≠ 2` and `q = Fintype.card F`,
  `WeierstrassCurve.natCard_point_eq` gives `#E(F) = q + 1 + S`, where `S` is the character sum
  `WeierstrassCurve.cubicCharSum` of the cubic obtained by completing the square.
  `WeierstrassCurve.hasse_bound` gives `(#E(F) - (q + 1))² ≤ 4 q` in `ℤ`, and
  `WeierstrassCurve.abs_natCard_point_sub_le` gives the real form `|#E(F) - (q + 1)| ≤ 2 √q`. The
  proof adapts Manin's elementary argument [manin56][manin56]; the implementation notes of
  [`ManinHeight.lean`](../../CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/ManinHeight.lean)
  say how the Lean steps correspond to his paper.
- **Prime fields `ZMod p`, including `p = 2`.** Completing the square needs `2 ≠ 0`, so the
  general theorem excludes characteristic two. `WeierstrassCurve.hasse_bound_zmod` states
  `p + 1 - 2 √p ≤ #E ≤ p + 1 + 2 √p` for every prime `p` (Theorem 9.72 of
  [katzlindell20][katzlindell20]); for `p = 2` it uses the direct count
  `WeierstrassCurve.natCard_point_zmod_two` (`1 ≤ #E ≤ 5`). Other fields of characteristic two are
  not covered.

The [checked client](../../CslibFrontierTests/Foundations/AlgebraicGeometry/EllipticCurveHasse.lean)
counts the points of `y² = x³ + 3x + 3` over `ZMod 7` (Example 9.69 of
[katzlindell20][katzlindell20]), of `y² + y = x³` over `ZMod 2`, and of two curves over `ZMod 5`
that attain both ends of the bound, and applies each form of the theorem to them. Build it with
`lake build CslibFrontierTests.Foundations.AlgebraicGeometry.EllipticCurveHasse`.

### HQC fixed-weight support sampling

Import [`HQC/SupportSampling.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportSampling.lean)
for the `SampleSupport2` program from the [HQC v5.1 specification](https://pqc-hqc.org/doc/hqc_specifications_v5.1.pdf),
p. 19. `sampleSupport2 width n count` draws every word from exactly `width` independent fair bits,
forms candidate `i + floor(word * (n-i) / 2^width)`, and then resolves collisions in descending
index order. `scanSupport` retains the ordered output array; `toFinset_scanSupport` proves that
the literal inner scan gives the same support as the membership-based resolver. For `count ≤ n`,
every output has exactly `count` positions in `range n`. `eval_idealSupport` proves exact
uniformity when each shrinking interval is sampled uniformly instead.

[`HQC/SupportDensity.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportDensity.lean) proves
Proposition 6.2.1's two product bounds for the actual multiply-high choices. The remainder
formulas in Equation (16) are identified by `supportLowerDensity_toReal` and
`supportUpperDensity_toReal`. Use `sampleSupport2_event_bounds` for a Boolean event and
`sampleSupport2_payoff_bounds` for a real payoff nonnegative on valid supports. Nonnegativity
is essential: the source's Lemma 6.5 omits it, and a constant payoff of `-1` refutes that wording.
[Checked examples](../../CslibFrontierTests/Crypto/HQCSupportSampling.lean) include zero/full weight,
collision replacement, and `n=5`, `count=2`, `width=3`, where `{2,4}` has actual probability
`1/16` and ideal probability `1/10`. They also distinguish multiply-high from modulo reduction.

Import [`HQC/Syndrome.lean`](../../CslibFrontier/Crypto/Primitives/HQC/Syndrome.lean) for the
finite 2-QCSD-P/2-DQCSD-P and 3-QCSD-PT/3-DQCSD-PT distributions from Definitions 2.3.6–2.3.9,
pp. 12–13. `realSyndromeLaw` draws the public circulant generator uniformly at its prescribed
parity and draws both secret blocks uniformly at fixed weight. Its comparison law keeps both the
public parity and the syndrome parity; a full-cube uniform comparison has a one-bit parity test.
`realTruncatedSyndromeLaw` uses one shared third secret block in both syndromes and retains the
requested prefix of the second. `mem_support_realTruncatedSyndromeLaw_iff` exposes that shared
witness explicitly. The comparison law keeps the first syndrome parity and samples the retained
second component from the full cube, exactly as the source does.

`eval_idealSupport_map_indicatorVector` connects the sampler above to these distributions: the
indicator of an ideal uniform fixed-cardinality support is exactly a uniform fixed-weight bit
string. The [checked syndrome examples](../../CslibFrontierTests/Crypto/HQCSyndrome.lean) cover
zero and full weight, detect a comparison distribution with the wrong parity baseline, and give a
four-bit sample that an incorrect independent redraw of the third secret accepts but the shared
law rejects. These are distribution definitions and exact finite laws, not assumptions that
2-QCSD-P or 3-QCSD-PT are hard.

The word-source model assumes independence and uniformity; it does not establish them for an
XOF. Positions use natural numbers, with checked 16-bit representability conditions for the
published parameter sets; byte serialization, native runtime, decryption-failure bounds and
HQC security remain separate obligations under the [post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

Import [`HQC/PKE.lean`](../../CslibFrontier/Crypto/Primitives/HQC/PKE.lean) for the ideal
post-expansion algebra of HQC-PKE (§3.6, pp. 38–40). `PKEParams` records the ring, message and
retained-codeword lengths, the three fixed weights and the decoder radius. `pkeKeyGen` draws
fixed-weight `y`, then `x`, followed by a uniform public ring word `h`, publishing
`(h, s = x + circulant h *ᵥ y)` while retaining expanded `y`; `pkeSampleCoins` draws `(r₂, e, r₁)` in
the source order. `pkeEncrypt` and `pkeDecrypt` implement the two source algorithms with
`truncate P` retaining exactly the first `n - ℓ` bits, and `toExplicitCoinPKE` supplies the
shared explicit-coin PKE interface used by the Fujisaki–Okamoto transform.

The central checked identity `pkeDecryptInput_encrypt` says that the decoder sees `Encode(m)` plus
the retained prefix of `x * r₂ - r₁ * y + e` (the minus sign is addition over `Bool`). Its proof
uses `circulant_mulVec_comm` and `circulant_mulVec_assoc` to cancel the two public-`h` terms.
`pkeDecrypt_encrypt_eq_of_weight_le` then consumes the plain encoder/decoder contract
`DecoderCorrects` and a retained-error weight bound. The
[checked client](../../CslibFrontierTests/Crypto/HQCPKE.lean) uses positive weights and proper
one-bit truncation, proves a length-three repetition decoder corrects one error, refutes the same
contract for a constant decoder, checks key/coin support and runs the packaged PKE.

This module does not replace the source's seeds and XOF with a proved implementation model, build
the concatenated Reed–Muller/Reed–Solomon codec, establish primitive-prime admissibility or a DFR
bound, or prove IND-CPA, Fujisaki–Okamoto or KEM security. It is therefore a correctness
prerequisite, not an HQC security endpoint.

## Encryption and chosen-message attacks

[AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/Basic.lean#L73) has a first stage choosing two messages and a saved word from the public key, and a second stage guessing from that saved state and the challenge ciphertext. Each stage has a native certificate. `INDCPAOn` explicitly constrains admissible message pairs. `WordINDCPA` requires equal lengths; the general `INDCPAOf` with all pairs is stronger for variable-length word messages. Invalid challenges are made independent of the hidden experiment bit. `Encryption.advantage (gameOn valid keyGen encrypt adversary) n` names the advantage between the two sides of the experiment at parameter `n`, and `INDCPAOn` asks that it be negligible for every admissible adversary; bounds on other two-sided encryption experiments, such as the DEM and CCA games, are stated with the same name.

To state a security reduction for one fixed scheme, without words or a security parameter, import
[`Encryption/Scheme.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Scheme.lean).
`PKE PK SK M C` has typed keys, messages and ciphertexts (`keyGen`, `encrypt`, and `decrypt`
returning `Option M`), `PKE.Correct` is perfect correctness, and
`E.cpaExperiment valid A b : Experiment` draws a key pair and runs the left-or-right experiment
`lrExperiment` of [`TwoStage.lean`](../../CslibFrontier/Crypto/Computational/TwoStage.lean) on the
public key, against a `TwoStage` adversary with any state type. Bound
`Experiment.advantage (E.cpaExperiment valid A false) (E.cpaExperiment valid A true)` by a
reduction's advantage at a fixed instance, then pass to the word level:
`Encryption.gameOn_eq_cpaExperiment` says that `gameOn valid keyGen encrypt adversary bit n` is
the typed experiment of the scheme with key generation `keyGen n` and encryption `encrypt n`,
played by `adversary.toTwoStage n`. Rewrite advantages with
`Encryption.advantage_gameOn_eq_cpaExperiment`: `Encryption.advantage` applies `gameOn`
partially, so `rw` with the experiment equation does not reach it. `AdversaryOf.isPPT_toTwoStage`
turns a word-level PPT certificate into a `TwoStage.IsPPT` family. The
[checked examples](../../CslibFrontierTests/Crypto/PKEScheme.lean) separate the two challenge
bits of a key-leaking scheme and rewrite `gameOn` into the typed experiment; run
`scripts/build.sh CslibFrontierTests.Crypto.PKEScheme`. The PPT transfer is checked in
[`CslibFrontierTests/Crypto/Experiment.lean`](../../CslibFrontierTests/Crypto/Experiment.lean).

To replace the honest public-key distribution by another law, such as lossy or uniform keys, import
[`Encryption/PublicKeyReplacement.lean`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyReplacement.lean).
`publicKeyGameOn valid keys encrypt adversary bit n` is `gameOn valid` with its public key drawn
from `keys` (`eval_gameOn_eq_publicKeyGameOn`). `keyDistinguisherOn valid encrypt adversary` is the
single hidden-bit reduction between two key laws, and `advantage_publicKeyGameOn_le` bounds the
chosen-message advantage under the real law by twice its advantage plus the advantage under the
replacement law. `isPPT_keyDistinguisherOn` certifies it from a polynomial-time `valid`, native
encryption and a PPT adversary. The unrestricted names `publicKeyGame`, `keyDistinguisher`,
`eval_game_eq_publicKeyGame`, `isPPT_keyDistinguisher` and `advantage_publicKeyGame_le` are the
`valid := fun _ _ _ _ => true` case. Goldwasser–Micali uses both forms (single bits and bounded
words); Regev, dual Regev and GSW use the unrestricted one. A proof that unfolds `publicKeyGame` or
`keyDistinguisher` also unfolds `publicKeyGameOn` or `keyDistinguisherOn`, plus `↓reduceIte` under
`simp only`. The orientation, factor-two and inadmissible-pair checks are in
[`CslibFrontierTests/Crypto/GSWSecurity.lean`](../../CslibFrontierTests/Crypto/GSWSecurity.lean).

[CCA2AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/CCA.lean#L266) exposes adaptive decryption before and after the challenge; the second handler rejects the exact challenge ciphertext. The multi-challenge interface in [`CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA.lean) (`MultiCCA2AdversaryOf`, `INDCCA2MultiOn`) is a two-phase **batch** model, whereas [`CCA/Interleaved.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean) (`InterleavedCCA2AdversaryOf`, `interleavedCcaOracle`, `INDCCA2InterleavedOn`) formalizes Boneh–Shoup Attack Game 12.1 and Definition 12.1 ([bs23][bs23], §12.1, pp. 467–468) with a single stateful combined encryption-and-decryption oracle that tracks the list `S` of challenge ciphertexts generated so far, allowing arbitrary adaptive interleaving of `.challenge m₀ m₁` and `.decrypt c` queries (including decryption of a ciphertext `c` before a later challenge happens to produce `c`) and proving equivalence with both 1CCA and phased batch multi-challenge CCA (`indcca2InterleavedOn_iff_indcca2On`, `indcca2InterleavedOn_iff_indcca2MultiOn`, and `advantage_interleavedCca2GameOn`, with concrete checks in [`CslibFrontierTests/Crypto/CCAInterleaved.lean`](../../CslibFrontierTests/Crypto/CCAInterleaved.lean)). Encodings are part of the security boundary: the inspected Cramer–Shoup parser [decodeCramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup/Scheme.lean#L876) requires canonical framing, so a different raw serialization of the challenge does not silently bypass the equality check.

The endpoint [DDH.indcca2On_cramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup.lean#L1688) (together with its batch multi-challenge lift `DDH.indcca2MultiOn_cramerShoup` and fully adaptive interleaved multi-challenge lift [`DDH.indcca2InterleavedOn_cramerShoup`](../../CslibFrontier/Crypto/Computational/CramerShoup/Interleaved.lean)) combines DDH, collision resistance, negligible inverse group order, and explicit efficient public operations. Approximate modular sampling and its statistical error are accounted for. Other clients include ElGamal, hybrid encryption, authenticated encryption and encrypt-then-MAC; they instantiate the same staged/oracle security schemas. Homomorphic schemes add circuit functionality and are treated [separately](homomorphic-encryption.md).

The canonical [`KEMINDCPA keyLen keyGen encaps`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid.lean) compares the real encapsulated key with an independent uniform `keyLen n`-bit word. Use `fun n => n` for normalized keys, or another schedule such as `fun n => 2 * n`. The composition methods `KEMINDCPA.hybrid_indcpa` and `KEMINDCPA.hybrid_indcpaOn` consume `DEMOneTimeKeyINDCPAOf` and `DEMOneTimeKeyINDCPAOn` at the same schedule; the latter requires a polynomial-time admissibility predicate independent of the public key. The exact bound is twice the hidden-bit KEM distinguisher's advantage plus the DEM adversary's advantage (Boneh–Shoup v0.6, Exercise 11.9(b), pp. 460–461 [bs23][bs23]). The native ideal-game certificate `isPPTOn_kemIdealGame` additionally takes `ComputableInPolyTime keyLen encUnary encUnary`. The reductions do not sample ideal keys, so the security implication itself does not need that certificate.

For a fixed KEM and symmetric cipher, without words or a security parameter, import
[`Encryption/KEMDEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEMDEM.lean).
`KEM PK SK CT K` of [`Encryption/KEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEM.lean)
has typed `keyGen`, `encaps` and `decaps` returning `Option K`. `KEM.Correct` is perfect
correctness, and `E.cpaExperiment sampleKey D b` gives the distinguisher a `KEM.Challenge` whose key
is either the encapsulated key (`b = false`) or a fresh key from `sampleKey` (`b = true`).
`Cipher K M C` of [`Encryption/Cipher.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Cipher.lean)
is a symmetric cipher. `D.oneTimeExperiment sampleKey valid A b` is its one-time left-or-right
experiment under a key drawn from `sampleKey`.

The hybrid scheme is `E.hybrid D : PKE PK SK M (CT × C)`, and `KEM.hybrid_correct` derives its
correctness from that of its components. `KEM.advantage_hybrid_le_two_mul` bounds the advantage of
its `cpaExperiment` by twice the KEM advantage of `KEM.hybridHiddenBitDistinguisher D valid A`,
plus the one-time advantage of `KEM.hybridCipherAdversary E A`. `KEM.advantage_hybrid_le` is the
variant with two distinguishers.

The word-level `advantage_hybridGame_le_two_mul` and `advantage_hybridGame_le` are these bounds for
`wordKEM keyGen encaps decaps n`, `wordCipher encryptSym decryptSym n` and
`adversary.toHybridTwoStage n`. They follow through the bridges `eval_game_hybridEncrypt`,
`eval_kemRealGame_eq_cpaExperiment`, `eval_kemIdealGame_eq_cpaExperiment` and
`eval_demKeyGame_eq_oneTimeExperiment`.

The [checked examples](../../CslibFrontierTests/Crypto/KEMDEM.lean) combine a KEM that sends its
key in the clear with the one-bit one-time pad, and show that the pad has one-time advantage zero.
They also rewrite the word-level hybrid game into the typed experiment. Run
`scripts/build.sh CslibFrontierTests.Crypto.KEMDEM`.

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

For the Diffie–Hellman random-oracle KEM of [katzlindell20][katzlindell20] (Construction 12.19,
Theorem 12.22), import
[`DiffieHellman/GapCDH.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/GapCDH.lean).
It states the Gap-CDH game `PrimeOrderGroupFamily.gapCDHGame` (CDH with a
decisional Diffie–Hellman oracle, §12.4.4), the KEM `dhKEMEncaps` / `dhKEMDecaps`
with correctness `dhKEMDecaps_encaps`, and the IND-CCA game `dhKEMCCAGame` with a random-oracle
hash and a decapsulation oracle that refuses the challenge.
`advantage_dhKEMCCAGame_le` bounds the advantage of a deterministic oracle adversary by the
success probability of the explicit reduction `dhKEMToGapCDH`, with no additive term. The bound
is for one fixed group and an arbitrary finite key sampler; the asymptotic polynomial-time
statement is not yet proved. Checked clients are in
[`CslibFrontierTests/Crypto/GapCDH.lean`](../../CslibFrontierTests/Crypto/GapCDH.lean).

For explicit-coin public-key encryption and modular Fujisaki–Okamoto KEM transforms ([hhk17][hhk17],
ePrint 2017/604 full version dated 2 November 2021), import
[`PKE/ExplicitCoin.lean`](../../CslibFrontier/Crypto/Protocols/PKE/ExplicitCoin.lean) for the
generic scheme interface and
[`FujisakiOkamoto.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto.lean) for the
transform.
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
untagged `H(s, c)`. `FujisakiOkamoto.decTM`, `Scheme.decapsBotM` and `Scheme.decapsNotBotM` are
the same algorithms with oracle access to `G` and `H` in any monad. `decT`, `decapsBot` and
`decapsNotBot` are these in `Id` (`decT_eq`, `Scheme.decapsBot_eq` and `Scheme.decapsNotBot_eq`
give their direct forms), and with pure oracles in any lawful monad the oracle-access
decapsulations return them (`Scheme.decapsBotM_pure`, `Scheme.decapsNotBotM_pure`). The
random-oracle game handlers run them against lazy or table
oracles instead of restating the re-encryption check. For Random Oracle Model (ROM) IND-CCA games
and the keyless IND-CPA reduction
on `FO-notbot`, import
[`FujisakiOkamoto/Security.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Security.lean).
It defines the ROM query family `ROQuery M CT` (`G`, `H`, and punctured decapsulation rejecting
`c = cStar` with `none`) and its dispatcher `ROQuery.dispatch`, on which every lazy, eager and
simulated FO handler is built from its own `G`, `H` and decapsulation implementations (build new
hybrid handlers the same way), deterministic oracle adversaries `ROAdversary` on the challenge
record `KEM.Challenge PK CT K` (fields `pk`, `ct`, `key`; defined in
[`Encryption/KEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEM.lean)), pathwise
`(qG, qH)` query budgets `ROQueryBounds` via `OracleComp.IsCostBounded`, and the lazy-cached executable game `Scheme.roIndCcaGame`
(`Scheme.indCcaRomAdvantage`) and eager random-oracle game `Scheme.eagerIndCcaGame` with exact
eager/lazy equivalence (`Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`,
`Scheme.indCcaRomAdvantage_eq_eager`). Both games are instances of one ROM IND-CCA experiment
`Scheme.romIndCcaExperiment`, which takes the key generator and the decapsulation oracle as a
program `romProgram` against the random oracles `ROSpec`; its eager form is
`Scheme.eagerRomIndCcaExperiment`, and `Scheme.eval_romIndCcaExperiment_eq_eager` proves their
equivalence once for every decapsulation program. The `@[simp]` bridges
`Scheme.romIndCcaExperiment_notBot` and `Scheme.eagerRomIndCcaExperiment_notBot` (and
`Scheme.romIndCcaExperiment_bot`, `Scheme.eagerRomIndCcaExperiment_bot` for `FO^⊥` in `Bot.lean`)
identify the instances with the named games. For another FO variant, instantiate the experiment
with its decapsulation program and prove such bridges rather than writing new handlers and a new
eager/lazy proof. Eager games draw their random oracles from the named tables `Scheme.coinTable`
(for `G`) and `Scheme.keyTable X` (a key-valued table on `X`, such as `H` on `Bool × M × CT` or a
ciphertext table on `CT`); new eager hybrids should use them rather than spelling out `PMF.pi`.
The module also supplies the keyless simulator `Scheme.simHandler` and IND-CPA
reduction `Scheme.romCpaReduction` (`Scheme.simHitProb`, `Scheme.indCpaAdvantage_romCpaReduction`,
the query-count row bound `Scheme.sum_simHitProb_le`, and the OW-to-CPA averaging bound
`Scheme.avg_simHitProb_le_indCpaAdvantage_romCpaReduction`). The IND-CCA theorem itself is
[`FujisakiOkamoto/NotBot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NotBot.lean):
`Scheme.indCcaRomAdvantage_le` bounds `indCcaRomAdvantage A` for uniform messages, a `δ`-correct
and `γ`-spread PKE and `(qG, qH)` random-oracle queries (decapsulation queries unbounded) by
`2 · indCpaAdvantage m₀ m₁ (romCpaReduction A m₀ m₁) + (2 qH + 2 (qG + qH)) / |M| +
2 (qG + qH + 1) δ + 2 (qG + qH) 2^{-γ}` for some `m₀ ≠ m₁` (where `roIndCcaGame` draws both real `H` values and the independent ideal challenge key from the arbitrary sampler `S.sampleKey`, recovering the uniform-key experiment of HHK17 §2.2 Def. 2.4 / Fig. 4 when `S.sampleKey` is uniform). Its hybrids are fixed in
`NotBot/Hybrids.lean` (`Scheme.eagerFbGame`, `Scheme.eagerCoupledGame`, `Scheme.coupledGame`,
`Scheme.simGame`), one file per hop: fallback-seed decoupling (`NotBot/Fallback.lean`), re-indexing
the oracles so that decapsulation reads a ciphertext table (`NotBot/Pushforward.lean`) and its lazy
realization (`NotBot/Lazy.lean`), the `δ`-correctness bad event (`NotBot/Correctness.lean`), and the
challenge hop with the `γ` collision term (`NotBot/Challenge.lean`). To see why the re-encryption check of `T` cannot be omitted in `FO-notbot`, import [`FujisakiOkamoto/NoCheck.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NoCheck.lean): for any explicit-coin PKE `P` over `Fin n → Bool`, `leakyPKE P` appends an `Option (Fin n)` tag to ciphertexts while preserving `indCpaAdvantage` (`leakyPKE_indCpaAdvantage`), `DeltaCorrect` (`leakyPKE_deltaCorrect`), and `GammaSpread` (`leakyPKE_gammaSpread`) and making `Scheme.decapsNotBot` reject tagged ciphertexts `(c, some i)` via the re-encryption check (`decapsNotBot_leakyPKE_some`), whereas dropping the re-encryption check (`Scheme.decapsNoCheck`, `Scheme.eagerNoCheckGame`) lets the bit-recovery adversary `leakAdv` (`roQueryBounds_leakAdv`, `0` `G`-queries and `n + 1` `H`-queries) achieve advantage at least `1 - (n + 1) / |K|` for a perfectly correct `P` and uniform keys (`advantage_eagerNoCheckGame_leakAdv`; checked client in [`CslibFrontierTests/Crypto/FujisakiOkamotoNoCheck.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoNoCheck.lean)). For explicit-rejection `FO^⊥ = U^⊥ ∘ T` (§3.2.1, Fig. 9), import [`FujisakiOkamoto/Bot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Bot.lean) (`ROFullQueryBounds`, `Scheme.roIndCcaBotGame`, `Scheme.eagerIndCcaBotGame`, `Scheme.eval_roIndCcaBotGame_eq_eagerIndCcaBotGame`, `Scheme.simBotGame`, `Scheme.romBotCpaReduction`, `Scheme.indCcaBotAdvantage_le`, which removes the `2 qH / |M|` fallback seed-guessing term and adds the `2 qD 2^{-γ}` ciphertext-validity spreadness term over `qD` decapsulation queries, with `roIndCcaBotGame` and `eagerIndCcaBotGame` likewise drawing both real `H` replies and the independent ideal challenge key from `S.sampleKey` so uniform `S.sampleKey` recovers the standard uniform-ideal-key experiment) and [`FujisakiOkamoto/SpreadNecessity.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/SpreadNecessity.lean) (`unspreadPointPKE`, `unspreadScheme`, `probeDecapsAdv`, `advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv`, showing that a single decapsulation query `qD = 1` with `qG = qH = 0` achieves distinguishing advantage `1 - 1 / |M|` against `simBotGame` when `γ`-spreadness fails at one message); standalone OW-PCA / OW-PCVA security definitions for `T` are not formalized separately. Checked clients in
[`CslibFrontierTests/Crypto/FujisakiOkamoto.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamoto.lean)
exercise honest `T`/`FO^⊥`/`FO-notbot` recovery and non-canonical-coin rejection on
`maskedShiftPKE`, zero-error and non-zero tight/non-tight `DeltaCorrect` witnesses (`noisyCoinPKE`
with failure probability `1 / 2`), positive and negative `GammaSpread` and `indCpaAdvantage`
witnesses on `identityPKE`, and `ROQueryBounds`, `simHitProb`, `romCpaReduction`, positive
`indCcaRomAdvantage`, and eager/lazy/averaging witnesses on `identityScheme`,
`identityUnifKeyScheme`, and `maskedShiftScheme`;
[`CslibFrontierTests/Crypto/FujisakiOkamotoNotBot.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoNotBot.lean)
and [`CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean)
instantiate `Scheme.indCcaRomAdvantage_le` (`≤ 3 / 8`) and `Scheme.indCcaBotAdvantage_le` (`≤ 1 / 4`, plus the `15 / 16` `probeDecapsAdv` separation on `unspreadPointPKE pairCoinPKE 0`) on `pairCoinScheme`.

ML-KEM ([fips203][fips203]) lives in
[`MLKEM/KPKE.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/KPKE.lean),
[`MLKEM/Security.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Security.lean) and
[`KEM/MLKEM.lean`](../../CslibFrontier/Crypto/Protocols/KEM/MLKEM.lean). K-PKE reuses
`ModuleLWEPublicKey`, `moduleSISMap` and `innerPoly`: its uncompressed ciphertext is
`moduleLWEEncrypt` of the zero message shifted by `messagePoly`, since FIPS 203 encodes the bit `1`
as `⌈q / 2⌋` rather than `encodePolyMsg`'s `⌊q / 2⌋`. The FIPS 203 rounding maps `compress` and
`decompress` come with `compress_decompress`, the rounding-error bound
`natAbs_valMinAbs_decompress_compress_sub_le` and one-bit decoding
`compress_one_decompress_one_add`, which together give the deterministic bounded-noise correctness
`decrypt_encrypt_eq_of_noise_le`. Key generation and coins are `ProbComp` programs over
`sampleCenteredBinomial` with a uniform matrix in place of `SampleNTT`, and `toExplicitCoinPKE`
feeds the scheme to the FO layer. `indCpaAdvantage_le` bounds its fixed-message IND-CPA advantage by
four `ModuleLWE.advantage` terms of the explicit reductions `mlweKeyReduction` and
`mlweReduction`, with centered-binomial secret and error laws; `DecisionModuleLWE` fixes a uniform
secret, so it does not bound these terms. `MLKEMTransform.decapsWith` is the FIPS 203 implicit-rejection wrapper over any
`ExplicitCoinPKE`, defined through `FujisakiOkamoto.decT` and proved equal to the standard's
decapsulation algorithm (`decapsWith_eq`). [`CslibFrontierTests/Crypto/MLKEM.lean`](../../CslibFrontierTests/Crypto/MLKEM.lean)
checks the three parameter sets, sharpness of the compression and decoding bounds at `q = 3329`,
and a toy instance (`n = 2`, `q = 17`) on which the noise hypotheses hold, decryption and
decapsulation succeed, and a tampered ciphertext is implicitly rejected.

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
`advantage_xorEvalPoints_eq_zero`, the uniform-block XOR and support-length helpers
(`uniformBlocks_eq`, `length_snd_of_mem_support_uniformDraws`, `map_zipWith_uniformBlocks`,
`map_iv_uniformBlocks_zipWith`), and the chain collision bound `toOuterMeasure_badChain_le`
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

For the shared lazy-versus-fresh random-function hybrid and left-or-right block-mode CPA scaffolding
used by both CTR and OFB mode, import
[`Encryption/RandomFunctionHybrid.lean`](../../CslibFrontier/Crypto/Computational/Encryption/RandomFunctionHybrid.lean):
it packages `FlagState`, the caching/fresh step handlers `lazyStep` and `freshStep`, the game
equivalence `idealExperiment_eq_runWith_lazyStep`, the bad-flag reduction bounds
`advantage_lazy_fresh_le` and `advantage_idealExperiment_freshStep_le` (whose lifted-coin support
facts `PMF.snd_eq_of_mem_support_lift` and `PMF.toOuterMeasure_lift_eq_zero` live in
[`Probability/PMF/Support.lean`](../../CslibFrontier/Probability/PMF/Support.lean)), the two- and
four-hop advantage triangle helpers `advantage_le_two` and `advantage_le_four`, and the shared
block-mode query, cost, oracle, reduction, and ideal-experiment interface (`BlockModeQuery`,
`BlockModeSpec`, `BlockModeAdversary`, `blockModeSelect`, `blockModeBlocks`, `blockModeCost`,
`blockModeOracle`, `blockModeIdealOracle`, `blockModeCpaExperiment`, `blockModeIdealExperiment`,
`blockModeQueryProgram`, `blockModeReduction`, `blockModeCpaExperiment_eq_realExperiment`,
`isQueryBounded_blockModeReduction`, and `freshGame_eq_blockModeIdealExperiment`). The two
experiments are `ProbComp Bool` runs of the adversary (`adversary.run`), and the reduction is
`ProbOracleComp.simulate (blockModeQueryProgram keystream ℓ b) adversary`, so its query bound is
`isCostBounded_simulate` and the CPA experiment equals `PRF.realExperiment` before evaluation.

For the chosen-plaintext security of random-IV counter (CTR) mode, import
[`Encryption/CTRMode.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CTRMode.lean)
(Katz–Lindell 3rd ed., §3.6.3, Figure 3.9, Definition 3.22, Theorem 3.33 [katzlindell20][katzlindell20];
Boneh–Shoup Chapter 4 [bs23][bs23]). Using the shared `BlockModeAdversary` / `blockModeCost` /
`blockModeIdealExperiment` interface, it formalizes the adaptive left-or-right multiple-encryption
experiment (`ctrCpaGame`) for any counter schedule `counter : BitString n → ℕ → BitString n`
satisfying within-query offset distinctness and per-offset IV injectivity, proves exact real-PRF
correspondence for `ctrReduction` (`ctrCpaGame_eq_realExperiment`, `isQueryBounded_ctrReduction`), bounds
the idealization collision error relative to `blockModeIdealExperiment` by `K ^ 2 / 2 ^ n` for `K` total
queried blocks (`advantage_idealExperiment_ctrReduction_le`), and specializes to the modular-addition
counter `ctrModCounter` whenever per-query length `ℓ ≤ 2 ^ n` (`ctrModCounter_injOn`,
`ctrModCounter_injective_left`, `advantage_ctrCpaGame_ctrModCounter_randomFunction_le`,
`advantage_ctrCpaGame_ctrModCounter_le`). The reduction is concrete (`ProbOracleComp`); no native
multitape PPT statement is made. Concrete `BitString 8` evaluations and non-vacuous bounds are in
[`CslibFrontierTests/Crypto/CTRMode.lean`](../../CslibFrontierTests/Crypto/CTRMode.lean).

For the chosen-plaintext security of random-IV OFB mode, import
[`Encryption/OFBMode.lean`](../../CslibFrontier/Crypto/Computational/Encryption/OFBMode.lean)
(Katz–Lindell 3rd ed., §3.6.3, Figure 3.8, Definition 3.22, following the proof of Theorem 3.33
[katzlindell20][katzlindell20]). `ofbCpaGame` is the left-or-right multiple-encryption experiment
for a keyed block function using `BlockModeAdversary`, `blockModeSelect`, and `blockModeBlocks`,
where a pair whose lengths differ or exceed `ℓ` blocks encrypts the empty message. `ofbReduction`
turns an adversary into a PRF distinguisher that computes the keystream with its oracle
(`ofbCpaGame_eq_realExperiment`, `isQueryBounded_ofbReduction`). If the queries ask at most `K` blocks in
total (`OracleComp.IsCostBounded (blockModeCost ℓ) adversary K`), `advantage_idealExperiment_ofbReduction_le`
bounds the distance from `blockModeIdealExperiment` by `K * (K + ℓ) / 2^n` using
`toOuterMeasure_badChain_le`. `advantage_ofbCpaGame_le` then bounds the left-or-right advantage by
the two PRF advantages plus `2 * K * (K + ℓ) / 2^n`, and
`advantage_ofbCpaGame_randomFunction_le` gives `2 * K * (K + ℓ) / 2^n` for a uniform random
function. The reduction is concrete (`ProbOracleComp`); no native multitape PPT statement is made.
Concrete checks are in
[`CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean`](../../CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean).

For hash functions built from a fixed permutation or block cipher, import
[`Hash/Sponge.lean`](../../CslibFrontier/Crypto/Primitives/Hash/Sponge.lean) and
[`Hash/BlockCipherCompression.lean`](../../CslibFrontier/Crypto/Primitives/Hash/BlockCipherCompression.lean)
(Katz–Lindell 3rd ed., §7.3.1 and §7.3.3). The sponge module writes the state as a pair
`(rate, capacity)` with an arbitrary output map and defines `absorb`, `squeeze`, `pad`, `toBlocks`
and `hash` (Construction 7.6). `badEvent_of_hash_eq` is the deterministic core of Claim 7.8 for
forward permutation queries: a collision between distinct messages triggers `ImageCollision` for
the output map (E1), `ZeroCapacity` (E2) or `ImageCollision` for `Prod.snd` (E3) among the
evaluated inputs. `hash_eq_of_capacity_eq` extends any capacity collision to a hash collision, and
`hash_prodCongr_collision` answers Exercise 7.26. Inverse queries, Claim 7.9 and the bound of
Theorem 7.7 are not formalized. The block-cipher module defines Davies–Meyer (`daviesMeyer`) and
the compression functions of Exercise 7.23(a) and (c) (`cipherOutput`, `keyMasked`), with
inverse-query collisions (`cipherOutput_collision`, `keyMasked_collision`) and the fixed-point
collision of Exercise 7.24 (`daviesMeyer_collision_of_fixedPoints`); the Ideal-Cipher bound of
Theorem 7.5 is proved in `daviesMeyer_collisionGame_le` and `daviesMeyer_collisionGame_mul_le`
(combining `daviesMeyer_collision_difference_bound` with the forgetful collision bound) in
[`CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean`](../../CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean). Concrete checks are in
[`CslibFrontierTests/Crypto/Sponge.lean`](../../CslibFrontierTests/Crypto/Sponge.lean) and
[`CslibFrontierTests/Crypto/IdealCipherCompression.lean`](../../CslibFrontierTests/Crypto/IdealCipherCompression.lean).

For the single-oracle real-versus-ideal formulation of authenticated encryption ([katzlindell20][katzlindell20], §5.2, Definition 5.4 and Theorem 5.5, pp. 152–153), import [`Encryption/RealIdealAE.lean`](../../CslibFrontier/Crypto/Computational/Encryption/RealIdealAE.lean). `SymmetricCipher.aeRealGame` answers `n`-bit encryption queries honestly (recording returned ciphertexts and answering decryption queries on them with `[]`) and decrypts fresh ciphertexts via `encOption encBits (E.decrypt n k ct)`, whereas `aeIdealGame` encrypts `List.replicate n false` and answers every decryption query with `[]`; `RealIdealAE` asks every `IsOraclePPT encBool` adversary to have negligible advantage, and `realIdealAE_iff_indcca_and_ciphertextIntegrity` and `realIdealAE_iff_authenticatedEncryption` prove equivalence with `INDCCA ∧ CiphertextIntegrity` and `AuthenticatedEncryption` via `cpaToAEAdversary`, `ciToAEAdversary`, and `aeToCCAAdversary`. [`Encryption/HalfBlockPRP.lean`](../../CslibFrontier/Crypto/Computational/Encryption/HalfBlockPRP.lean) formalizes the half-block construction `BlockCipher.halfBlockCipher` (`F_k(r ‖ m)` on `2 n`-bit blocks, Exercises 5.8 and 5.9, p. 165) and shows via the zero-query `allOnesForger` that it fails `CiphertextIntegrity`, `AuthenticatedEncryption`, and `RealIdealAE` for every block cipher (its CCA security under a strong PRP is not formalized); checked instances over an identity cipher are in [`CslibFrontierTests/Crypto/RealIdealAEAndHalfBlock.lean`](../../CslibFrontierTests/Crypto/RealIdealAEAndHalfBlock.lean).

For fresh-message encryption unforgeability ([katzlindell20][katzlindell20], §5.2, Definition 5.2,
p. 151, and Exercise 5.5, p. 165), import
[`Encryption/EncForge.lean`](../../CslibFrontier/Crypto/Computational/Encryption/EncForge.lean).
`SymmetricCipher.encForgeGame` and `SymmetricCipher.EncForge` test whether a uniform strict
`IsOraclePPT encBits` adversary can produce a ciphertext decrypting to `some m` for a plaintext `m`
not queried to `encForgeOracle`. Ciphertext integrity implies `EncForge`
(`SymmetricCipher.succProbability_encForgeGame_le_ciGame`, `CiphertextIntegrity.encForge`), and
ordinary fresh-message MAC security (`MACScheme.EUFCMA`, without `SUFCMA` or `E.INDCPA`) already
suffices for `(encryptThenMAC E M hctLen).EncForge` (`succProbability_encForgeGame_encryptThenMAC_le`,
`encForge_encryptThenMAC`, Exercise 5.5). The generic authenticated-encryption composition
separations (Exercises 5.4 and 5.10, pp. 164–165) are in
[`Encryption/CompositionCounterexamples.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CompositionCounterexamples.lean).
`SymmetricCipher.tailFallback` (falling back to `E.decrypt n k ct.tail` when direct decryption
returns `none` and `ct` is non-empty) preserves `INDCPA` and `EncForge` while breaking
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`
(`SymmetricCipher.tailFallback_counterexample`,
`PseudorandomFunction.tailFallback_prfEncryptThenMAC_counterexample`, Exercise 5.10); and
`MACScheme.redundantTag` (accepting `tag` or `tag.tail`) preserves `EUFCMA` while breaking `SUFCMA`,
so `encryptThenMAC E M.redundantTag hctLen` satisfies `INDCPA` and `EncForge` yet fails
`CiphertextIntegrity` and `INDCCA` with advantage `1` for every `n ≥ 1`
(`encryptThenMAC_redundantTag_counterexample`,
`PseudorandomFunction.prfEncryptThenMACRedundantTag_counterexample`, Exercise 5.4). Concrete
evaluations and composed `IsPPT` / `IsOraclePPT` checks on `echoFamily` are in
[`CslibFrontierTests/Crypto/CompositionCounterexamples.lean`](../../CslibFrontierTests/Crypto/CompositionCounterexamples.lean).

For generic MAC-then-Encrypt composition, its `INDCPA` preservation, and its chosen-ciphertext
counterexample over `SymmetricCipher` and `MACScheme`, import
[`Encryption/MACThenEncrypt.lean`](../../CslibFrontier/Crypto/Computational/Encryption/MACThenEncrypt.lean)
(Katz–Lindell 3rd ed., §5.2 [katzlindell20][katzlindell20]; Boneh–Shoup §9.4.1 [bs23][bs23]).
Given a polynomial-time plaintext-tag length schedule `ptLen : ℕ → ℕ`
(`hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary`), `M.msgLen n = n`, and
`(encPair encBits encBits (msg, tag)).length = ptLen n` on valid `M` messages and tags,
`macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen` signs `msg` and runs `E` at security
parameter `ptLen n` on `encPair encBits encBits (msg, tag)` (requiring no extra decryption
hypothesis beyond `E.decrypt_encrypt`), verifying length, framing round-trip, and `M.verify` on
decryption. When `StrictMono ptLen`, `indcpa_macThenEncrypt` reduces `INDCPA` of `macThenEncrypt`
to `E.INDCPA` via `mteToCPAAdversary` (reindexing `ptLen` with `GeneratorReindex`). The malleable
wrapper `SymmetricCipher.extendCipher` appends `false` to every ciphertext and ignores the last bit
in decryption, preserving `INDCPA` (`SymmetricCipher.INDCPA.extendCipher`) and `OneTimeINDCPA`
(`SymmetricCipher.OneTimeINDCPA.extendCipher`) via `extendCPAAdversary` and
`extendOneTimeCPAAdversary`. Meanwhile, flipping that trailing bit (`macThenEncryptExtendCIAdversary`,
`macThenEncryptExtendCCAAdversary`) achieves advantage `1` for every `n ≥ 1` against
`macThenEncrypt E.extendCipher M ptLen ...`, refuting `OneTimeCiphertextIntegrity`,
`CiphertextIntegrity`, `OneTimeINDCCA` (`not_oneTimeINDCCA_macThenEncrypt_extendCipher`), and
`INDCCA` (`not_indcca_macThenEncrypt_extendCipher`), combined in
`macThenEncrypt_extendCipher_counterexample` and instantiated unconditionally from any
`PseudorandomFunction` via `prfMacThenEncryptExtend` (`ptLen n = 3 * n + 1`) and
`PseudorandomFunction.prfMacThenEncryptExtend_counterexample`. Concrete checks on `echoCipher` and
`echoMAC` as well as the PRF instantiation are in
[`CslibFrontierTests/Crypto/MACThenEncrypt.lean`](../../CslibFrontierTests/Crypto/MACThenEncrypt.lean).

## Authentication, signatures, and state

To state a forgery experiment, import [Game/Forgery.lean](../../CslibFrontier/Crypto/Game/Forgery.lean). `forgeExperiment keyGen signer verify fresh A` draws a key pair, runs the forger `A` on the public key against a signing oracle, and accepts a candidate `(m, σ)` that verifies and is fresh. The oracle is a policy `Signer SK M Sig` that reads the log of answered queries. `Signer.ofSign` signs every query and `.oneTime` signs only the first; `Signer.indexed` and `Signer.counter` give the indexed and counter oracles. A refused query is answered with `default` and is not logged. `freshMessage` gives existential unforgeability and `freshPair` strong unforgeability; `succProbability_forgeExperiment_freshMessage_le` shows that strong implies existential. Verification also receives the secret key, so a MAC is the case `PK = Unit`. [Signature/Scheme.lean](../../CslibFrontier/Crypto/Computational/Signature/Scheme.lean) defines a typed `Signature.Scheme PK SK M Sig` with `eufCmaExperiment` (Boneh–Shoup Attack Game 13.1), `sufCmaExperiment` and `oneTimeEufCmaExperiment`; `restrict adm` makes verification accept only admissible messages. At each parameter `n`, the word games `SignatureScheme.eufCmaGame` and `eufOneTimeGame` equal these experiments for `S.toScheme n` and `adversary.toTyped n` ([Signature/Bridge.lean](../../CslibFrontier/Crypto/Computational/Signature/Bridge.lean), `eufCmaGame_eq_eufCmaExperiment`). `Signature.IndexedScheme` adds a capacity and passes an index to signing and verification. Its `eufCmaExperiment` uses `Signer.indexed` (Boneh–Shoup Definition 14.6) and `counterEufCmaExperiment` uses `Signer.counter` (Section 14.6.4). The word games `indexedEufCmaGame` and `counterEufCmaGame` equal them at each `n` (`indexedEufCmaGame_eq_eufCmaExperiment`, `counterEufCmaGame_eq_counterEufCmaExperiment`). For any typed scheme on words, `Forger.eval_eufCmaExperiment_toTyped` and its `restrict` form unfold the experiment played by a word forger into the word-level game; the tree signature games `TreeSignature.treeGame` and `treeGameWith` are experiments of the certificate-free `treeScheme` and use this form in the coin hybrid. The [checked clients](../../CslibFrontierTests/Crypto/Forgery.lean) cover the signing policies, a winning forger, a replay that loses, and the unique-signature equality.

[SignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Signature.lean#L87) bundles efficient key generation, signing, verification and correctness. The base message space is exactly `n` bits. Its oracle forger chooses signing requests adaptively; ordinary EUF-CMA rejects any message previously signed. [exists_oneWay_iff_exists_oneTimeSignature](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToSignature.lean#L882) is the OWF/one-time-signature equivalence via Lamport's construction. Stateless many-time `EUFCMA` `SignatureScheme`s on `n`-bit messages are constructed from any `OneWayPermutation` in [`TCRSignature.lean`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) (`OneWayPermutation.exists_eufCMA`) and from any general `OneWay` function in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) (`OneWay.exists_eufCMA`, `exists_oneWay_iff_exists_signature`, `exists_oneTimeSignature_iff_exists_signature` [rompel90][rompel90]). For unrestricted bit-string messages (`msg : List Bool`), [`WordSignatureScheme`](../../CslibFrontier/Crypto/Computational/WordSignature.lean) removes the `n`-bit message-length filter from signing, verification and `eufCmaGame` (`WordSignatureScheme.EUFCMA`, strictly stronger than `toSignatureScheme.EUFCMA`). When full collision resistance is available, [`HashAndSign.scheme`](../../CslibFrontier/Crypto/Computational/HashAndSign.lean) (Katz–Lindell 3rd ed., §13.3, Construction 13.3 and Theorem 13.4, pp. 467–468 [katzlindell20][katzlindell20]) fixes a single hash key `s` once in the public and secret keys (`⟨pk₀, s⟩`, `⟨sk₀, s⟩`) so that signatures carry no per-signature hash-key overhead (`HashAndSign.succProbability_eufCmaGame_le`, `SignatureScheme.EUFCMA.wordEUFCMA_hashAndSign`, `SignatureScheme.EUFCMA.wordEUFCMA_of_hashFamily`, `SignatureScheme.EUFCMA.wordEUFCMA_merkleDamgard`, and key-independent collision attack `HashAndSign.not_eufCMA_scheme_of_collision`; concrete checks in [`CslibFrontierTests/Crypto/HashAndSign.lean`](../../CslibFrontierTests/Crypto/HashAndSign.lean)). Under only target collision resistance (UOWHFs), [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) lifts any `SignatureScheme.EUFCMA` scheme by sampling a fresh hash key per signature (`SignatureScheme.EUFCMA.eufCMA_wordScheme`, `OneWayPermutation.exists_wordEUFCMA`; Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23]), and [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) closes the unrestricted-message equivalence from any uniform `OneWay` function (`OneWay.exists_wordEUFCMA`, `exists_oneWay_iff_exists_wordSignature`, `exists_oneTimeSignature_iff_exists_wordSignature` [rompel90][rompel90]).

Reductions that truncate signing-oracle replies need a polynomial bound on signature length. Take it
from `SignatureScheme.exists_sign_length_bound` (in the parameter and the message length),
`SignatureScheme.exists_sign_length_bound_of_length_eq` (on `n`-bit messages) or
`IndexedSignatureScheme.exists_sign_length_bound` (at indices below the capacity) instead of
re-deriving it from `keyGen_ppt.length_le` and `sign_ppt.length_le`.

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
[`CslibFrontierTests/Crypto/CBCMAC.lean`](../../CslibFrontierTests/Crypto/CBCMAC.lean). The
query-based attacks return a `ForgeryTrace` with its `queries`, forged `message` and claimed `tag`;
`trace.Valid mac` says that the message was never queried and that `mac` gives it the claimed tag.
The random-IV attack instead transforms one observed `(iv, tag)` pair.

For variable-length messages under CBC-MAC, import
[`BlockCipher/LengthPrependedCBCMAC.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/LengthPrependedCBCMAC.lean)
(Katz–Lindell 3rd ed., §4.4.1, Figure 4.2, and Exercise 4.18 [katzlindell20][katzlindell20]).
`lengthPrependedCbcMac` runs basic CBC-MAC on a block-aligned message of at most `L` blocks with
its encoded block count in front (`prependLength`, `blockCountBlock`). For an injective length
encoding, no prepended input is a prefix of another (`not_isPrefix_prependLength`), so
`prependLengthQueries` turns an adaptive distinguisher into a prefix-free CBC-MAC distinguisher.
`abs_lengthPrependedRealSuccess_sub_lengthPrependedIdealSuccess_le` then bounds its advantage
against a uniform random function by `q^2 * (L + 1)^2 / 2^n` for `q` queries. Like the prefix-free
bound, this statement is information-theoretic. Concrete checks are in
[`CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean`](../../CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean).

For messages of varying length built from a fixed-length `MACScheme`, import
[`Protocols/MAC/VariableLength.lean`](../../CslibFrontier/Crypto/Protocols/MAC/VariableLength.lean)
(Katz–Lindell 3rd ed., §4.3.2, Construction 4.7 and Theorem 4.8). `MACScheme.blockwiseSign` tags
every block together with a fresh uniform identifier, the message length and the block index.
`MACScheme.blockwiseGame_le` bounds the fresh-message EUF-CMA success probability by the advantage
of `blockwiseReduction` against the fixed-length scheme plus `(∑ i ∈ range Q, i) / 2 ^ w` for an
adversary with at most `Q` signing queries, where `w` is a quarter of the fixed input length.
`blockwiseGame_noIndex`, `blockwiseGame_noLength` and `blockwiseGame_noIdentifier` show that
omitting any one of the three fields gives an adversary that wins with probability `1` once
`w ≥ 3`, that is, once the fixed input length is at least `12`. No uniform PPT corollary is stated.
Concrete checks are in
[`CslibFrontierTests/Crypto/VariableLengthMAC.lean`](../../CslibFrontierTests/Crypto/VariableLengthMAC.lean).

A weak pseudorandom function only has to look random on uniformly random inputs. In
[`Computational/WeakPRF.lean`](../../CslibFrontier/Crypto/Computational/WeakPRF.lean)
(Katz–Lindell 3rd ed., Exercises 3.28 and 4.9 [katzlindell20][katzlindell20]),
`WeakPseudorandomFunction` gives the distinguisher an oracle that returns a fresh uniform input
together with its value under the keyed function or under a random function, and
`PseudorandomFunction.weakPseudorandomFunction` proves that every pseudorandom function is weak.
The converse fails: `zeroPatch` maps the all-zero input to itself and leaves every other value
unchanged. `advantage_weakPrfRealGame_zeroPatch_le` shows that the patch moves the weak real game
by at most `Q / 2 ^ n` against an adversary making at most `Q` calls, so
`WeakPseudorandomFunction.zeroPatch` keeps weak security, while
`not_pseudorandomFunction_zeroPatch` and `not_eufCma_prfMAC_zeroPatch` show that the patched
family is not pseudorandom and that its direct MAC is forgeable with probability `1`. From any pseudorandom function this
gives `PseudorandomFunction.exists_weak_not_pseudorandom` and
`PseudorandomFunction.exists_weak_not_eufCma_prfMAC`. Another answer to Exercise 3.28(b)
evaluates the function after rounding odd inputs to even ones; the zero patch is simpler and
separates the same notions. Encryption from a weak pseudorandom function (Exercise 3.28(d)) is not formalized.

For polynomial-evaluation hashing of messages shorter than `ℓ` over a finite field, import
[`Protocols/MAC/PolynomialEvaluation.lean`](../../CslibFrontier/Crypto/Protocols/MAC/PolynomialEvaluation.lean)
(Katz–Lindell 3rd ed., §4.5.2, Theorem 4.17 and Exercise 4.22). A message with its length code
appended is evaluated at the key in one of four coefficient layouts.
`PolynomialEvaluation.isDeltaUniversalHash_hash` proves the textbook layout `ℓ / |F|`-difference
universal for any injective length code. For the layouts of Exercise 4.22(a) and (c),
`isDeltaUniversalHash_fixedTopHash` and `isDeltaUniversalHash_ascendingHash` prove the same bound
when, in addition, no positive length is coded as zero, and `not_isDeltaUniversalHash_fixedTopHash`
and `not_isDeltaUniversalHash_ascendingHash` give a key-independent collision when the length `1`
is coded as zero. For `1 < ℓ` and `ε < 1`, the constant-term layout of Exercise 4.22(b) is never
`ε`-difference universal (`not_isDeltaUniversalHash_constantTermHash`). Concrete checks over
`ZMod 5` and for the zero patch are in
[`CslibFrontierTests/Crypto/WeakPRFAndPolyMAC.lean`](../../CslibFrontierTests/Crypto/WeakPRFAndPolyMAC.lean).

[IndexedSignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/IndexedSignature.lean#L89) signs index/message pairs with polynomially bounded capacity; the oracle refuses repeated or out-of-range signing indices. The syntax is stateless but the game enforces single use. Counter wrappers and Merkle signature clients turn that contract into stateful signing, whereas [TreeSignature.scheme](../../CslibFrontier/Crypto/Computational/TreeSignature.lean#L576) and [TreeSignature/Security.lean](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4295) upgrade any indexed EUF-CMA scheme of capacity at least `2` plus a pseudorandom function (or one-way function) to a stateless `SignatureScheme` (`eufCMA_scheme`, `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`, `exists_eufCMA_of_oneWay`) by sampling a uniform leaf and deriving internal node keys and signing coins from the PRF [bs23][bs23]; `TreeSignature.sign` returns `[]` outside the `n`-bit message domain. Composing Lamport, depth-`1` Merkle trees, PRFs from one-way functions, and stateless tree signatures gives [OneWay.exists_eufCMA_of_hashFamily](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4353) from a one-way function and a collision-resistant hash family. Without full collision resistance, [`TCRSignature.scheme`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) adapts Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23] to a capacity-`1` `IndexedSignatureScheme` over a one-time signature scheme `S` and an unrestricted target collision-resistant `KeyedHashFamily` `H` without storing a hash key in `pk` (`SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`; concrete checks and an explicit `1`-probability break against a constant hash family are in [`CslibFrontierTests/Crypto/TCRSignature.lean`](../../CslibFrontierTests/Crypto/TCRSignature.lean)), and [`IndexedSignatureScheme.double`](../../CslibFrontier/Crypto/Computational/IndexedSignature/Double.lean) doubles any indexed scheme of capacity at least `1` to constant capacity `2` with plug-and-pray loss `2` (Boneh–Shoup §14.6.1, construction `(14.4)` on p. 597, and Exercise 13.2 [bs23][bs23]; `IndexedSignatureScheme.IndexedEUFCMA.double`). Composing Lamport one-time signatures, `TCRSignature.scheme`, `IndexedSignatureScheme.double`, and `TreeSignature` yields `OneWay.exists_eufCMA_of_targetCollisionResistant`: instantiating `H` with `naorYungHash` proves `OneWayPermutation.exists_eufCMA` (Naor–Yung §4 / Theorem 2 [naoryung89][naoryung89]), while instantiating `H` with `rompelHash` in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) removes the permutation hypothesis to yield `OneWay.exists_indexedEUFCMA_two` and `OneWay.exists_counterEUFCMA_two` on arbitrary-length `List Bool` messages, `OneWay.exists_eufCMA` and `exists_oneWay_iff_exists_signature` on `SignatureScheme`'s `n`-bit message domain, and—after applying [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) (`SignatureScheme.EUFCMA.eufCMA_wordScheme`)—`OneWay.exists_wordEUFCMA` and `exists_oneWay_iff_exists_wordSignature` on unrestricted `List Bool` messages ([rompel90][rompel90]; client checks and message-space separation witnesses in [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean)). Keep the indexed game's no-repeat invariant distinct from durable storage in a deployed stateful implementation: no filesystem or crash-recovery model is asserted here.

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

To state a commitment scheme and its games as programs, import [Commitment/Scheme.lean](../../CslibFrontier/Crypto/Computational/Commitment/Scheme.lean). `Commitment.Scheme K M C O` has typed key, message, commitment and opening spaces, with key generation and commitment as `ProbComp` programs and a Boolean `verify`. `hidingExperiment` draws a key and runs `lrExperiment` on the commitment component. `bindingExperiment` asks for a `BindingCollision`, two distinct messages opened against one commitment. `PerfectlyHidingAt S k` makes every message's commitment law equal at key `k`. At such a key, the left-or-right advantage is zero (`Scheme.advantage_lrExperiment_eq_zero`). `Scheme.advantage_hidingExperiment_le` bounds the hiding advantage by the probability that key generation lands outside a perfectly hiding set. The Pedersen instance `pedersen d` at a fixed group description is correct (`pedersen_correct`) and perfectly hiding at every key `h ≠ 0` (`pedersen_perfectlyHidingAt`). The zero key, drawn with probability `1 / q`, is the only loss, so `advantage_pedersen_hidingExperiment_le` gives at most `1 / q`. `succProbability_pedersen_bindingExperiment_le` bounds binding by the discrete-logarithm advantage of the explicit reduction `pedersenToDL`, which reads off `α = (r₁ - r₀)⁻¹ * (m₀ - m₁)` from two openings. These are fixed-parameter statements and make no efficiency claim. The [checked clients](../../CslibFrontierTests/Crypto/CommitmentScheme.lean) cover a perfectly hiding scheme whose binding success is one; the [Pedersen clients](../../CslibFrontierTests/Crypto/PedersenCommitment.lean) instantiate both bounds on a group of order `11`.

[CommitmentScheme](../../CslibFrontier/Crypto/Computational/Commitment/Basic.lean) is the older word-level interface and is intentionally distributional. It gives a faithful public-key encoding, valid messages, an exact PMF of commitment/opening pairs, verification and correctness. Efficient realization is separate. Chosen-message hiding reuses the saved-state encryption adversary; binding asks for two distinct messages opening one commitment. Pedersen's ideal exact uniform exponent law is compatible with this model even when a strict finite fair-coin implementation must approximate it. `Commitment/PublicOperations` and `PedersenCommitment/ProbComp` supply the separate public-operation and sampling bridges. The word-level commitment law is a `PMF` and its keys come from an external setup law, so it has no generic translation to `Commitment.Scheme`. For Pedersen, `pedersenHidingGame_eq` and `pedersenBindingGame_eq` state that the word-level games equal the typed experiments under the setup law.

## Garbling schemes

[Garbling/Scheme.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Scheme.lean) is the abstract garbling-scheme syntax of Bellare, Hoang and Rogaway, Sections 3 and 4 [bhr12][bhr12]: `Scheme Fn` is `(Gb, En, De, Ev, ev)` over an abstract type of function descriptions with length readers, `Scheme.Garbled` is the output triple `(F, e, d)`, and `Query Fn` is a query `(f, x)`. `Gb` carries its coins explicitly (`coinLen` and a deterministic `gb`), and `Scheme.garble` samples them via `BitString.sampleList`, so non-degeneracy can quantify over the coins (`Scheme.eval_garble`, `Scheme.mem_support_eval_garble_iff`). `Scheme.IsValid` bundles `Scheme.LengthCondition`, `Scheme.NonDegenerate` and `Scheme.Correct`; `Scheme.WellTyped` fixes the output length of `ev` and of every successful decoding of an arbitrary string. A `SideInfo Fn Λ` is a side-information function `Φ` with length readers (`SideInfo.circ` is the identity side information `Φ_circ`), and `SideInfo.Compatible`, `SideInfo.IsEvInverter` and `SideInfo.IsInverter` are the compatibility condition of Section 3.3 and the inversion hypotheses of Section 4.1 (`SideInfo.Compatible.inLen_eq`, `SideInfo.circ_compatible`, `SideInfo.circ_isInverter`). For a concrete point-and-permute circuit garbling construction over `Cslib.Circuits.Circuit`, see [Protocols and privacy](protocols-and-privacy.md#garbled-circuits).

[Garbling/Games.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Games.lean) states the single-query games of Sections 3.4–3.6 as experiments at a fixed security parameter `k`: `prvIndExperiment`, `prvSimExperiment`, `obvIndExperiment`, `obvSimExperiment` and `autExperiment`. Their adversaries are `TwoStage` adversaries (`PrvIndAdversary`, `PrvSimAdversary`, `ObvIndAdversary`, `ObvSimAdversary`, `AutAdversary`) that choose a `Query` or a `MessagePair` of queries and keep a state; the views are the records `PrvView` `(F, X, d)` and `ObvView` `(F, X)`, the real views are `Scheme.prvView` and `Scheme.obvView`, and the simulators `PrvSimulator` and `ObvSimulator` work at the fixed parameter. The advantages (`prvIndAdvantage`, `prvSimAdvantage`, `obvIndAdvantage`, `obvSimAdvantage`, `autAdvantage`) are `Experiment.advantage` and `Experiment.succProbability`. An invalid pair (`prvIndValid`, `obvIndValid`) or query is answered by `⊥`, so these are not `lrExperiment` instances; `prvIndAdvantage_eq_zero_of_invalid` records that an always-invalid adversary has advantage `0`, and `prvIndAdvantage_eq_two_mul_guessingAdvantage` identifies the `prv.ind` advantage with twice the bias of `Experiment.guessBit (prvIndExperiment G Φ k A)`. [Garbling/Foundations.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Foundations.lean) proves Propositions 2 and 3 (Section 4) as exact per-adversary identities: `prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim` for every simulator (`prvIndToSim`, state `IndToSimState`) and `prvSimAdvantage_prvSimFromInverter_eq` against the inverter simulator `prvSimFromInverter` (`prvSimToInd`, `eval_prvSimExperiment_prvSimFromInverter`) under an `ev`-inverter, together with the obliviousness analogues (`obvIndToSim`, `obvSimFromInverter`, `obvInverterQuery`, `obvSimToInd`, `obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_eq`, `eval_obvSimExperiment_obvSimFromInverter`) under an inverter and `≤` corollaries (`prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim`, `prvSimAdvantage_prvSimFromInverter_le`, `obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_le`). [Garbling/CircuitInverters.lean](../../CslibFrontier/Crypto/Primitives/Garbling/CircuitInverters.lean) specialises this framework to conventional Boolean circuits (`ConventionalCircuit`, `ValidCircuit`, `Topo`, the well-formedness structure `Topo.IsValid`, `ValidTopo` and the shape record `ValidShape` of Section 2.3; `Scheme.IsCircuitScheme`) and the three standard side-information functions `phiTopo`, `phiSize` and `phiCirc` (`phiTopo_compatible`, `phiSize_compatible`, `phiCirc_compatible`). It constructs the explicit deterministic `(Φ, ev)`-inverters `mTopo` and `mSize` (`mTopoGates`, `sizeTopo`) and `Φ`-inverters `mTopoInv` and `mSizeInv` of Section 4.1, Proposition 1 (`phiTopo_isEvInverter`, `phiSize_isEvInverter`, `phiTopo_isInverter`, `phiSize_isInverter`, `phiCirc_isInverter`), and derives Corollaries 1 and 2 of Sections 4.2–4.3 (`prvIndAdvantage_phiTopo_eq_two_mul_prvSimAdvantage`, `prvSimAdvantage_phiTopo_mTopo_eq`, `prvIndAdvantage_phiSize_eq_two_mul_prvSimAdvantage`, `prvSimAdvantage_phiSize_mSize_eq`, and the obliviousness analogues for `phiTopo`, `phiSize` and `phiCirc`). [Garbling/Adaptive.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Adaptive.lean) adds the coarse-grained adaptive privacy game `Prv1` of Bellare, Hoang and Rogaway, Section 3.1, Figure 2 [bhr12b][bhr12b] (`GarbledFn`, `Prv1Adversary`, `Prv1Simulator`, `prv1Experiment`, `prv1Advantage`, `prv1Advantage_eq_two_mul_guessingAdvantage`); its adversary has three stages, so it is not a `TwoStage` adversary. The embedding `prvSimToPrv1` and induced simulator `prv1SimulatorToPrv` (`PrvSimToPrv1State`) show that adaptive `prv1` simulation security implies selective `prv.sim` security with exact advantage equality (`eval_prv1Experiment_prvSimToPrv1`, `prvSimAdvantage_prv1SimulatorToPrv_eq`) and selective `prv.ind` security with a factor of two (`prvIndAdvantage_eq_two_mul_prv1Advantage`). No polynomial-time or negligible-advantage statement is made, and projective schemes (`Π` of Section 3.2) and the authenticity relations of Section 4 are not part of these modules. [Garbling-scheme clients](../../CslibFrontierTests/Crypto/GarblingScheme.lean) and [inverter/adaptive clients](../../CslibFrontierTests/Crypto/GarblingInverters.lean) check valid schemes (`identityScheme`, `plainCircuitScheme`), verify zero advantage for an invalid-query adversary, separate `phiSize`, `phiTopo` and `phiCirc` on concrete valid circuits, execute `mTopo` and `mSize` by `decide`, and instantiate the `prv.sim`, `obv.sim` and `prv1` reductions.

## Known Limitations

The finite query-only PRG/cipher results, semantic commitment interfaces and uniform native primitive structures do not share one implicit efficiency premise. The table records the differences. The long internal HILL and GGM proofs, all serialization helpers, and every named reduction were not independently re-proved or built in this pass. Existing nonvacuity tests are useful checks of interfaces, not evidence that cryptographic hardness assumptions hold.

[bhr12]: ../sources.md#bhr12
[bhr12b]: ../sources.md#bhr12b
[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[fips203]: ../sources.md#fips203
[fly22]: ../sources.md#fly22
[ggm86]: ../sources.md#ggm86
[goldreich04]: ../sources.md#goldreich04
[hhk17]: ../sources.md#hhk17
[hhrvw20]: ../sources.md#hhrvw20
[hill99]: ../sources.md#hill99
[holenstein06]: ../sources.md#holenstein06
[katzlindell20]: ../sources.md#katzlindell20
[manin56]: ../sources.md#manin56
[naoryung89]: ../sources.md#naoryung89
[rompel90]: ../sources.md#rompel90
