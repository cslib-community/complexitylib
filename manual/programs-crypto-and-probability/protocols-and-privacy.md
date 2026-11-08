# Protocol models, ideal oracles, and privacy

The general [public-coin interactive-reduction model](interactive-reductions.md), including sumcheck/GKR and efficient straight-line extraction/honest-verifier simulation, has a separate account.

## Sigma protocols and explicit extraction

[SigmaProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Basic.lean#L78) specifies an honest commitment PMF with private state, a deterministic response to a challenge, and Boolean verification. `Complete`, `SpecialSoundness` and `SpecialHVZK` express correctness, extraction from two accepting same-commitment/distinct-challenge transcripts, and exact simulation at each fixed challenge. The extractor may target a different relation, accommodating relaxed lattice witnesses. The generic interface has no native efficiency built in [complexitylib][complexitylib].

[SigmaProtocol/Efficient.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Efficient.lean) adds encodings and machine-backed extraction/simulation predicates (`EfficientSpecialSoundness`, `EfficientSpecialHVZK`). A simulator certificate compares a strict-PPT realization with an exact `SpecialHVZK` law using an explicit statistical error `δ : I → ℝ≥0∞`; `δ` is not constrained inside `EfficientSpecialHVZK` (`δ i ≥ 1` makes `SimulatorRealizedBy` vacuous), so security claims must state their concrete or `Negligible` bound on `δ` explicitly. These additions do not retroactively make every semantic Sigma instance efficient. Schnorr and Lyubashevsky clients exercise the interfaces; [SigmaProtocol/Lyubashevsky/NativeExtract.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/NativeExtract.lean) and [SigmaProtocol/Lyubashevsky/Efficient.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Efficient.lean) provide the serialized extractor, verifier (`EfficientVerifier`), strict-PPT integer-box samplers (`sampleIntBox`, `sampleIntBoxVec`, `sampleDyadicIntBox`), and non-abort simulator certificate (`EfficientNonAbortSpecialHVZK`).

[SigmaProtocol/Interactive.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean) embeds any `SigmaProtocol X Y T C Z` with `[Fintype C] [Nonempty C]` into the three-message public-coin specification `P.interactiveSpec` (`[.prover T (OracleInterface.full T), .verifier C, .prover Z (OracleInterface.full Z)]`) in [Computability/Interactive](interactive-reductions.md):

- **Protocol embedding ([toInteractiveVerifier](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L213), [toInteractiveProver](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L197), [toInteractiveReduction](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L226)):** `toInteractiveVerifier` samples a uniform challenge `c ∈ C` and accepts when `P.verify y t c z = true`. Given a `ProbComp` commitment realization `sampleCommit : X → Y → ProbComp (T × P.State)` satisfying `P.CommitRealizedBy sampleCommit`, `toInteractiveProver` and `toInteractiveReduction` realize the honest prover in `World.plain`, swapping `SigmaProtocol`'s witness-first relation `R : X → Y → Prop` to `Interactive`'s statement-first convention `Function.swap R : Y → X → Prop` with target relation `Interactive.Accept`.
- **Security and efficiency transfers ([Complete.toInteractiveReduction](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L285), [SpecialSoundness.rbrSound](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L342), [SpecialSoundness.sound](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L352), [SpecialSoundness.knowledgeSound](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L395), [SpecialHVZK.hvzk_zero](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L444), [EfficientSpecialHVZK.efficientHVZK](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean#L601)):** completeness transfers with error `0`; `SpecialSoundness` implies round-by-round soundness (`rbrState` holds at round 0 iff at least two challenges admit valid responses for `t`, at round 1 iff the chosen `c` admits a valid response, and at round 2 iff `P.verify y t c z = true`) and plain-model soundness with error `1 / (Fintype.card C : ℝ≥0∞)`, as well as straight-line `KnowledgeSound` via `P.witnessChooser R` (reflecting that one-shot straight-line extraction without rewinding cannot run a 2-transcript extractor); `SpecialHVZK` transfers to zero-error `Interactive.Reduction.HVZK`; and `EfficientSpecialHVZK` combined with a strict-PPT challenge sampler within `δC i` of uniform on `C i` yields `Interactive.Reduction.EfficientHVZK` with simulation error `0` and realization error `δC i + δ i`. Concrete commitment/simulator realizations and checked instances for `schnorr`, `PrimeOrderGroupFamily.schnorrFamily`, `andProof`, and `orProof` are in [SigmaProtocol/Interactive.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Interactive.lean) and [ComplexityTests/SigmaInteractiveBridge.lean](../../ComplexityTests/SigmaInteractiveBridge.lean).

When statistical simulation is too strong or callers interact through game indistinguishability, import `Complexity.Crypto.Protocols.SigmaProtocol.Computational` ([SigmaProtocol/Computational.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean)), which formalizes Boneh and Shoup's Attack Game 20.4 and Definition 20.6 ([bs23][bs23], Section 20.4.2, p. 840):

- **Two-stage distinguishing game ([CHVZKAdversary](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L107), [chvzkRealGame](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L217), [chvzkSimGame](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L228)):** at security parameter `n`, `i ← setup n` is passed to `adversary.choose n i`, which outputs an encoded witness-statement candidate `(xw, yw)` and saved `state` word (`CHVZKAdversary.IsPPT` clocks `choose` on `(1^n, i)` and `guess` on `(1^n, state, conv)`). When `(xw, yw)` decodes via `encW i` and `enc.statement i` to a valid `(x, y)` in `R i`, `chvzkRealGame` runs `adversary.guess` on an honest encoded conversation while `chvzkSimGame` samples `c ← PMF.uniformOfFintype (C i)` and runs the simulator `sim (i, enc.statement i y, enc.challenge i c)` without `x`; invalid choices output `false` in both experiments so `R i` need not be efficiently decidable by the challenger.
- **Predicate and acceptance parameter ([ComputationalSpecialHVZK](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L243)):** bundles uniform strict PPT admissibility of `sim`, acceptance probability at least `1 - δ i` on every `(i, y, c)` (`δ = fun _ => 0` gives exact Definition 20.6 acceptance; non-zero `δ` accommodates strict fair-coin approximations of non-dyadic distributions), and `Game.Indistinguishable` against all strict-PPT `CHVZKAdversary` distinguishers.
- **Statistical-to-computational bridge and Schnorr instance:** [SimulatorRealizedBy.advantage_chvzkGame_le](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L326) bounds Attack Game 20.4 advantage against *arbitrary* (even unbounded) adversaries via `Game.advantage_bind_le_of_closeTo` ([Game/CloseTo.lean](../../Complexity/Crypto/Game/CloseTo.lean#L130)), yielding [EfficientSpecialHVZK.exists_computationalSpecialHVZK](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L375) whenever `δ` is bounded along `setup` by a `Negligible` function and [SimulatorRealizedBy.computationalSpecialHVZK_of_accepts](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L347) when exact acceptance holds separately. In [SchnorrProtocol.lean](../../Complexity/Crypto/Computational/SchnorrProtocol.lean#L300), `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr` establishes `ComputationalSpecialHVZK` with exact zero acceptance error (`δ = fun _ => 0`) for any `setup : ℕ → PMF F.Desc`.
- **Two-sided separations ([ComplexityTests/ComputationalSpecialHVZK.lean](../../ComplexityTests/ComputationalSpecialHVZK.lean)):** `not_computationalSpecialHVZK_sendWitness` proves that the perfectly `SpecialHVZK` protocol `sendWitnessFamily F` fails `ComputationalSpecialHVZK` under `F.DiscreteLog setup` for *every* `sim` and *every* `δ` (without invoking `accepts`), while `computationalSpecialHVZK_prgWitnessSigma` and `exists_computationalSpecialHVZK_and_not_specialHVZK` construct from any stretching `PseudorandomGenerator` (or uniform `OneWay` function) a complete Sigma protocol family satisfying `ComputationalSpecialHVZK` with `δ = fun _ => 0` that fails `SpecialHVZK`, `EfficientSpecialHVZK` for every `δ`, and even unbounded statistical HVZK below error `1 / 4`.

Abort is observable in [Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean): accepted transcripts and conversations return `Option`, with `none` representing abort. `NonAbortSpecialHVZK` matches the accepted-transcript law including abort mass. Its `none` erases the commitment, so this does not simulate the full view of aborted signing queries. Nonabort completeness alone does not give a lower bound on success, an expected retry cost, or a strict-PPT rejection-sampling implementation; [SigmaProtocol/Lyubashevsky/Efficient.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Efficient.lean) supplies strict-PPT integer-box sampling (`sampleIntBox`, `sampleIntBoxVec`, `sampleIntBoxList`) with statistical distance at most `m * ((2 * B + 1) / 2 ^ width)` from `intBox (Fin m) B`, realizing `lyubashevskySimulate` under `EfficientNonAbortSpecialHVZK`. [SigmaProtocol/Lyubashevsky/Signature.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature.lean) adds the Fiat–Shamir-with-aborts signing and verification layer (`FiatShamirWithAborts`, `fsAbortSignAttempt`, `fsAbortSignBounded`, `fsAbortVerify`, and their Lyubashevsky specializations), proving completeness of non-aborting single and bounded `K`-attempt runs (`fsAbortVerify_of_fsAbortSignAttempt_eq_some`, `fsAbortVerify_of_fsAbortSignBounded_eq_some`), the exact `K`-retry abort law `(p_abort) ^ K` (`fsAbortSignBounded_apply_none`), direct-attack identification security for `lyubashevsky` against the relaxed `[A | T]` SIS relation (`lyubashevsky_succProbability_directAttack_le`), and the witness-invariance collision reduction (`isSISSolution_sub_smul_secret`, `extractSISFromRelaxedWitness`, `extractSISFromTwoTranscripts`, `lyubashevskyForkToSIS`, `lyubashevskySignatureForkToSIS`) that folds an extracted `[A | T]` kernel vector into a homogeneous `SIS.IsSolution` for `A` whenever the extracted response difference differs from the honest secret key's shift (exercised in [ComplexityTests/Crypto/LyubashevskySignature.lean](../../ComplexityTests/Crypto/LyubashevskySignature.lean)). Full random-oracle EUF-CMA game-hop bounds for aborting signers and strict-PPT computational reductions to `SIS` remain separate open obligations.

For the generic fixed-hash abort-signing API, import [SigmaProtocol/Abort/FiatShamir.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Abort/FiatShamir.lean). It provides `fsAbortSignStep`, `fsAbortSignAttempt`, `fsAbortSignBounded`, verification and their generic laws without importing the lattice application. The existing `Lyubashevsky.Signature` import publicly reexports these declarations with unchanged names.

For an executable bounded signer, import [Lyubashevsky/Signature/Efficient.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Efficient.lean). `lyubashevskySignBoundedNative` takes native integer matrix rows, message bits, the existing `LyubashevskyParams`, and a unary attempt budget. For a polynomial-time deterministic hash on encoded message/commitment pairs, `isPPTOn_lyubashevskySignBoundedNative` certifies uniform strict-PPT execution. Matrix entries, the modulus and radii use binary encodings; dimensions, sampling width and the attempt budget are unary. Short rows and challenge words have zero defaults. The program samples all attempts and returns the first success, charging storage for the entire list.

`closeTo_lyubashevskySignBoundedNative` compares the resulting law, including `none`, with the exact bounded signer at distance at most `K * m * (2γ + 1) / 2^width`. `lyubashevskySignBoundedNative_none_le` bounds failure by the exact single-attempt abort probability raised to `K`, plus this sampling error. Keep that exact probability when the hash depends on the commitment: the interactive fixed-challenge abort formula cannot simply be substituted. [The checked one-dimensional example](../../ComplexityTests/Crypto/LyubashevskySigning.lean) covers success, rejection, missing rows, challenge truncation, zero attempts and a two-attempt distance bound `10/64`. These are implementation and distribution guarantees for a deterministic hash; the full random-oracle security obligations remain open.


For an explicit schedule with negligible signing failure, import [Lyubashevsky/Signature/Parameters.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Parameters.lean). `lyubashevskySigningParams λ` uses `t = λ + 1`, dimensions `n = m = k = t`, secret-entry bound one, margin `β = t`, radius `γ = 4t²`, sampling width `λ`, modulus `2^t` and `t` attempts. The exponential modulus is encoded in binary. `isPPTOn_lyubashevskySigningParams` certifies the actual signer jointly in unary `λ` and the complete raw matrix/message input sizes, for a polynomial-time deterministic word hash.

The new [hash-uniform abort bound](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Failure.lean), `lyubashevskySignAttempt_none_le`, holds for every deterministic hash, including one that chooses its challenge from the commitment: if `2β ≤ γ`, `kη ≤ β` and the secret entries are bounded by `η`, exact single-attempt failure is at most `4mβ/(2γ+1)`. Under the schedule above this is at most one half. `lyubashevskySigningParams_failure_le` bounds actual native failure by `2^−(λ+1) + (λ+1)^2 * (8(λ+1)^2+1) / 2^λ`; `negligible_lyubashevskySigningParams_failure` proves it negligible for arbitrary bounded-secret, public-matrix and message sequences. The probability guarantee does not require short messages; the runtime theorem charges their actual lengths. [Checked examples](../../ComplexityTests/Crypto/LyubashevskySigningParameters.lean) include a commitment-dependent hash, nonzero bounded secrets, certainty of native failure at `λ=0`, and an upper bound below one percent at `λ=32`. This schedule demonstrates efficient availability, not SIS hardness or EUF-CMA security.

To discharge the nonzero-vector condition for a public-key-only fork, import [Lyubashevsky/Signature/Extraction.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Extraction.lean). Fix any `A` over `ZMod q` with `q ≠ 0`, draw the `k` secret columns independently and uniformly from `[-η,η]^m`, and let an arbitrary randomized kernel receive only `T = A*S` (with `A` fixed). `lyubashevsky_predict_difference_le` bounds the probability of distinct binary challenges satisfying `z-z' = S*(ĉ-ĉ')` by `k*q^n/(2η+1)^m`. The proof counts secret columns after their public images are revealed; it assumes neither entropy nor a simulator conclusion. The shared finite-leakage lemmas live in [Probability/Guessing/Leakage.lean](../../Complexity/Probability/Guessing/Leakage.lean).

`lyubashevsky_fork_success_le_sis_add` then bounds the probability of two accepting responses at the same commitment and distinct challenges by the probability that the actual integer vector `z-z'-S*(ĉ-ĉ')` solves homogeneous SIS for `A`, with norm bound `2*(γ-β)+k*η`, plus this loss. Both probabilities use the same sampled-secret experiment. Its extraction uses `S`; the theorem alone is not an `A`-only native SIS reduction. [Checked clients](../../ComplexityTests/Crypto/LyubashevskyExtraction.lean) include a nonzero `1×8` matrix modulo 17 and a kernel that accepts with probability one and yields positive SIS success, empty challenges, and zero-radius secrets whose response differences can be predicted with certainty. Applying this bound to a real signature fork still requires proving the public-key-only distribution property while accounting for all aborted hash queries, and then providing efficient replay. Full random-oracle EUF-CMA remains open.

To compare two bounded secrets for the same public key, import [Lyubashevsky/Signature/View.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/View.lean). Under `k*η ≤ β ≤ γ` and `lyubashevskyRelation η` for both secrets, `lyubashevsky_transcript_eq` proves equality of the actual `(commitment, optional response)` law, including each aborted commitment. The proof combines the existing accepted-transcript equality with the actual secret-independent commitment marginal; [PMF/Option.lean](../../Complexity/Probability/PMF/Option.lean) supplies the finite-mass cancellation. `lyubashevsky_attempt_view_eq` extends this to any common deterministic challenge function `c(w)` of the commitment. It does not allow that function to inspect the secret.

`lyubashevsky_sign_attempts_view_eq` compares histories of `K` independent exact attempts, retaining every hash input, challenge and optional response. These histories evaluate all `K` attempts. `lyubashevskySignBounded_eq_attempts_view` projects their first success to the existing bounded signer, and `lyubashevskySignBounded_witness_eq` proves equality of its output laws. [Checked examples](../../ComplexityTests/Crypto/LyubashevskyView.lean) use distinct bounded secrets for one nonzero public matrix, a commitment-dependent challenge, a nonzero aborted commitment with positive probability, and a successful response with positive probability. These independent-history laws alone do not describe an adaptive cache. The next result proves witness invariance for that shared-cache execution; efficient secret-free simulation and equality of paired forks using the same private coins remain open.

For signing through the shared memoizing random oracle, import [Lyubashevsky/Signature/RandomOracle.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/RandomOracle.lean). `lyubashevskyROMSignature` instantiates the existing `ROMSignature.Scheme` with the original key generator, exact independent masks and optional signatures. The wrapper uses the identity hash-point embedding: each oracle query is the typed pair `(message, commitment)`. All `K` attempts run, including after the first success; aborted hash inputs remain cached and repeated inputs reuse their digest. The result is the first successful signature, or `none`, which verification rejects. The canonical handler logs every signing request, including aborts, so final-message freshness counts those requested messages. The shared `fiatShamirAbort_sign_fixedHash` theorem recovers the existing bounded signer's output law for a fixed hash; `fiatShamirAbortSign_queryBound` counts at most `K` hash calls, without a runtime claim.

Under the same bounded-witness hypotheses, `lyubashevskyROMSignature_sign_run_eq` compares the actual joint signature/final-cache law from every common initial cache. A common public randomized challenge/state kernel preserves the full transcript law, and induction threads each updated cache through the next attempt. `lyubashevskyROMSignature_forger_run_eq` retains an adaptive forger's output, cache and queried-message log; `lyubashevskyROMSignature_worldRealize_eq` also covers a probabilistic forger and final verification in the canonical world with the same public key. [Checked cache examples](../../ComplexityTests/Crypto/LyubashevskyRandomOracle.lean) show positive probability of an aborted new query being retained, a later query reading that stored digest, and a success followed by another attempted hash input. These single-run equalities do not supply an efficient secret-free simulator, paired same-coins fork equality, a native shared-oracle runtime certificate, or full EUF-CMA security.

For average-key cache-hit bounds, import [Lyubashevsky/Commitment.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Commitment.lean). With prime modulus `q`, draw a uniform `n×m` matrix `A`, then an arbitrary randomized history `H(A)`, and only then a fresh uniform mask in `[-r,r]^m`. If `2r < q`, [HashFamily/IntegerBox.lean](../../Complexity/Probability/HashFamily/IntegerBox.lean) bounds the joint law `(A,Ay)` against `(A,U)` by `εr = sqrt(q^n/(2r+1)^m)/2` in half-L1 distance. A history-selected cache of length at most `Q`, message and shift therefore give lookup probability at most `Q/q^n + εr`. The shift may depend on `A` and the history, but not on the fresh mask. This averages over the entire experiment, rather than conditioning on an arbitrary realized matrix or history.

`lyubashevsky_commit_lookup_le` applies this bound to the actual honest commitment with `r=γ`, including attempts whose responses later abort. `lyubashevskySimulate_lookup_le` bounds the existing simulator's published `Some` commitment with `r=γ−β`, assuming `β≤γ` and `2(γ−β)<q`; its bound is multiplied by the exact acceptance mass `((2(γ−β)+1)/(2γ+1))^m`. Its `None` erases the commitment, so this theorem does not justify removing aborted hash queries. [Checked clients](../../ComplexityTests/Crypto/LyubashevskyCommitment.lean) include a positive cache-hit probability below `0.06` at `q=17,n=1,m=8,γ=3,Q=1`, a supported zero matrix with conditional hit probability one, a nonzero matrix with positive hit probability, randomized matrix-dependent histories and shifts, empty caches, zero inner radius and zero output dimension. These original bounds use ideal uniform sampling for a supplied prime modulus; native sampling approximation and corrected full-view CMA simulation remain separate obligations. The earlier power-of-two availability schedule does not meet the prime-modulus hypothesis for positive security parameters and is not a security instantiation.

For one signing call's read-to-program hop, import [Lyubashevsky/Signature/Programming.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Programming.lean). `closeTo_lyubashevskySign_program` compares the actual all-`K` signer under memoized challenge reads with the same signer sampling a fresh uniform challenge and prepending its entry on every attempt. Both laws retain aborted entries and later cache effects after the first success. Their joint matrix, history, optional signature and complete final-cache laws are `CloseTo` with additive error `∑ j<K ((Q+j)/q^n + εγ)`, where `εγ = sqrt(q^n/(2γ+1)^m)/2`. The matrix is ideal uniform over a prime modulus, `2γ<q`, and the initial history is an arbitrary kernel of that matrix with cache length at most `Q`. The induction extends this history before each fresh mask, without conditioning the matrix on avoiding earlier collisions. Secret validity and response acceptance are not premises of this hop.

[Checked clients](../../ComplexityTests/Crypto/LyubashevskyProgramming.lean) cover zero attempts, exact one-attempt equality from an empty cache, a retained aborted commitment, and a supported repeated point whose second programmed digest can differ after the first successful response. The canonical scheme's two-attempt full laws satisfy a bound of `1/10` at `q=17,n=1,m=8,γ=3` from an empty cache. `CloseTo.bind_left` transports the result through any common continuation, and `CloseTo.symm` reverses it. This original finite-attempt bound may exceed one for other parameters. It is a one-call replacement, not a multiple-call adaptive reduction, an efficient secret-free simulator or a full signature-security theorem. Replacing programmed attempts by the erased-abort simulator remains a separate visible-law obligation: deleting aborted entries changes the complete cache law and must account for later oracle, verification and signing reads, together with the required abort-branch independence.

For visible signing simulation, import [Lyubashevsky/Signature/Simulation.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Simulation.lean). The single-attempt programmed signing hybrid `lyubashevskySignVisibleProg` programs the random oracle cache by drawing a fresh challenge and prepending `(message, commitment) ↦ challenge` even on an abort and even if that key was already present, while the simulated process `lyubashevskySignVisibleSim` (`lyubashevskySimulate`) adds hash cache entries only for accepted transcripts using `lyubashevskySimCache`. The actual memoizing transport from honest signing (`Sign → Prog`) that reuses cached challenges remains a separate obligation. Under prime modulus `q`, `2γ < q`, and valid secret witness `k*η ≤ β ≤ γ`, `closeTo_lyubashevskySign_simulate` bounds their statistical distance under any visible continuation `cont(A, h, sig)` making at most `R` later oracle reads: the distance on `(A, h, continuation output)` is at most `R / q^n + sqrt(q^n / (2γ + 1)^m) / 2`. The visible experiments factor through the full executions (`lyubashevskySignFullProg`, `lyubashevskySignFullSim`) via `lyubashevskySignVisibleProg_eq_bind_full` and `lyubashevskySignVisibleSim_eq_bind_full`, project their non-cache outputs for pure identity continuations (`lyubashevskySignVisibleProg_eq_map_full`, `lyubashevskySignVisibleSim_eq_map_full`), and agree identically whenever the continuation makes zero oracle queries (`lyubashevskySignVisibleProg_eq_sim_of_pure`). The simulation proof combines input-dependent continuation bounds (`CloseTo.bind_right_tsum`), the matrix leftover-hash commitment hit bound for the counterfactual abort continuation (`counterfactual_hit_le`), and exact equality of the accepted-transcript hybrid with `lyubashevskySimulate` via `lyubashevsky_nonAbortSpecialHVZK`. For `K`-attempt signing, `lyubashevskySimAttempts`, `lyubashevskySignAttemptsVisibleProg`, and `lyubashevskySignAttemptsVisibleSim` define the secret-free stopping simulator and the visible programmed and simulated experiments (imposing query bounds on the theorems rather than the definitions). Only the `K ≤ 1` reductions to the single-attempt bridge are proved so far: `lyubashevskySignAttemptsVisibleProg_zero_eq_sim` gives exact equality for `K = 0`, while `closeTo_lyubashevskySignAttempts_simulate_one`, `closeTo_lyubashevskySignAttempts_simulate_le_one`, `lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_one`, and `lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_le_one` case-split `K ≤ 1` back to the `K = 0` identity and the single-attempt theorems (for `K = 1` the `Finset.range K` sum reduces to `R / q^n + sqrt(q^n / (2γ + 1)^m) / 2`); the `K ≥ 2` visible simulation induction ([#2798](https://github.com/cslib-community/complexitylib/issues/2798)) remains open. [Checked clients](../../ComplexityTests/Crypto/LyubashevskySimulation.lean) cover zero-reads continuations, provably disjoint queries (`(true, 0) ≠ (false, coin.1)`, with both `avoid_closeTo` and exact `avoid_visible_eq` via `avoid_key_disjoint` and `avoid_miss_cache`), accepted-commitment queries (`hit_closeTo` and exact `hit_visible_eq` via `hit_returns_c`), an actual final-verifier client checking signature validity (`R = 1`), the `q=17, n=1, m=2, γ=3, β=1, S=0` counterexample (`progExp_cache_length_eq_one`, `simCache_length_zero_on_abort`, and empty-cache probabilities `0` for `progExp` versus `1 - (5/7)^2 = 24/49` for `simExp` despite equal visible marginals), and the `K = 0`, `K = 1`, and `K ≤ 1` reduction checks.

Identification and Fiat–Shamir add adversarial interaction to this same transcript model. Their security is not merely the existence of a mathematical witness extractor: the computational instances require an encoded efficient extractor, and finite quantitative transformations explicitly track replay and calls. For Schnorr identification over a `PrimeOrderGroupFamily`, [`SchnorrIdentification.lean`](../../Complexity/Crypto/Computational/SchnorrIdentification.lean) formalizes the direct impersonation game (`schnorrDirectGame`) and the rewinding discrete-logarithm extractor (`SchnorrImpersonator.rewind`, `succProbability_schnorrDirectGame_le`, `negligible_schnorrDirectGame`), while [`SchnorrEavesdrop.lean`](../../Complexity/Crypto/Computational/SchnorrEavesdrop.lean) adds eavesdropping security (`SchnorrEavesdropAdversary`, `schnorrEavesdropGame`, `schnorrIdealEavesdropGame`, `IsEavesdropSecure`, `IsIdealEavesdropSecure`; [bs23][bs23], Attack Game 18.2 and Theorems 19.3 and 19.5): because strict-PPT exponent sampling `sampleExp n d` (`ProbComp.sampleModNat`) has statistical distance at most `1 / 2 ^ n` from uniform on `ZMod q`, `Q n` simulated conversations (`schnorrSimulatedTranscript`) are within statistical distance `Q n / 2 ^ n` of ideal honest conversations (`schnorrHonestTranscript`) and within `2 * Q n / 2 ^ n` of strict-PPT honest conversations (`schnorrRealTranscript`), reducing any uniform strict-PPT eavesdropper via `SchnorrEavesdropAdversary.toDirect` to `schnorrDirectGame` and hence to `DiscreteLog` (`succProbability_schnorrEavesdropGame_le`, `negligible_schnorrEavesdropGame`, `schnorr_isEavesdropSecure_of_discreteLogHard`; checked on the order-`11` Schnorr group in `(ZMod 23)ˣ` in [`ComplexityTests/Crypto/SchnorrDiscreteLog.lean`](../../ComplexityTests/Crypto/SchnorrDiscreteLog.lean)).

## VOLE ideal functionality, IT-MACs, and VOLE-in-the-head

Import `Complexity.Crypto.Protocols.VOLE.Basic` ([VOLE/Basic.lean](../../Complexity/Crypto/Protocols/VOLE/Basic.lean)) for Vector Oblivious Linear Evaluation (VOLE) correlations, information-theoretic MACs (IT-MACs), and the linear VOLE-in-the-head Sigma protocol ([BoyleCGIKS2019]; [BaumBMRS2023]):

- **Ideal VOLE correlation ([VOLECorrelation](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L110), [voleSample](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L147), [voleIdealDist](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L175)):** over a commutative ring `R` and vector length `n`, the sender holds `(u, v) : (Fin n → R) × (Fin n → R)` and the receiver holds a global scalar key `delta : R` and tag vector `w : Fin n → R` satisfying `VOLECorrelation.Valid : ∀ i, w i = u i * delta + v i`. `voleIdealDist R n` samples `u, v` and `delta` uniformly and independently, with support characterized by `mem_support_voleIdealDist_iff` (`valid_of_mem_support_voleIdealDist`).
- **Linear homomorphism and witness commitment ([VOLECorrelation.Valid.add](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L241), [VOLECorrelation.Valid.linearComb](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L263), [voleCommitWitness](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L279), [voleAdjustReceiver](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L284)):** IT-MACs are closed under componentwise addition (`add`), public scalar multiplication (`smul`), public constant shifts (`addConst`), and public linear combinations (`Valid.linearComb`). Committing to a witness `x : Fin n → R` via the correction message `voleCommitWitness x u = x - u` and receiver tag update `voleAdjustReceiver w d delta` yields valid tags for `x` (`voleAdjustReceiver_voleCommitWitness`) while `voleCommitWitness_uniform` and `voleCommitWitness_indep` establish uniformity and witness-independence of the correction-message marginal under a uniform VOLE mask `u`.
- **IT-MAC unforgeability and degree-2 multiplication check ([voleOpen_unique_delta_of_ne](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L361), [toOuterMeasure_voleVerifyOpening_le](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L406), [voleMulCheck](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L457)):** over a field `F`, any forged opening `x' ≠ x` satisfies `voleVerifyOpening` for at most one global key `delta = (v' i - v i) / (x i - x' i)` (`card_filter_voleVerifyOpening_le_one`), bounding the cheating acceptance probability under uniform `delta` by `(Fintype.card F)⁻¹`. For authenticated wires `w_x, w_y, w_z`, `voleMulCheck_sub_eq` decomposes `w_x * w_y - w_z * delta` into `(x * y - z) * delta ^ 2` plus the affine-linear check `voleMulCrossTerm x v_x y v_y v_z * delta + voleMulConstTerm v_x v_y`, which holds iff `x * y = z` at any `delta ≠ 0` (`voleMulCheck_iff_of_ne_zero`).
- **Dishonest multiplication claims:** import `Complexity.Crypto.Protocols.VOLE.MulCheck` ([MulCheck.lean](../../Complexity/Crypto/Protocols/VOLE/MulCheck.lean)) when the sender may claim arbitrary affine coefficients `a`, `b`. Apply `toOuterMeasure_voleMulCheck_le` to a false gate `x * y ≠ z`: the check `(x * delta + v_x) * (y * delta + v_y) - (z * delta + v_z) * delta = a * delta + b` holds with probability at most `2 / |F|` under a uniform secret key. For a randomized sender, use `toOuterMeasure_voleMulCheck_bind_le` with its `PMF S` state distribution and eight functions supplying values, masks, and coefficients. The experiment samples the state before an independent key; it does not allow the claim to depend on the receiver's key or tags. The bad event includes the false gate, so the sender distribution needs no support hypothesis. This is a single-constraint information-theoretic bound, not full VOLE-based ZK or VOLE-in-the-head security, and gives no runtime certificate. The bound is sharp over `ZMod 5`; over `ZMod 2` a false claim can pass for every key. See the complete honest, sharp, randomized-sender, and key-dependence examples in [VOLEMulCheck.lean](../../ComplexityTests/Crypto/VOLEMulCheck.lean). From the repository root, check them with `scripts/build.sh ComplexityTests.Crypto.VOLEMulCheck`; successful completion confirms the examples elaborate.
- **Batched multiplication claims:** import `Complexity.Crypto.Protocols.VOLE.BatchMulCheck` ([BatchMulCheck.lean](../../Complexity/Crypto/Protocols/VOLE/BatchMulCheck.lean)). `voleMulCheck_sum` gives honest completeness for every weight vector and key. For a fixed false batch, `toOuterMeasure_voleMulCheck_batch_le` allows the sender's randomized affine reply to depend on a public uniformly sampled vector of weights. The key remains independent and hidden. The bound is `1 / |F| + (1 - 1 / |F|) * (2 / |F|)`: the first term is cancellation of the nonzero residual vector; otherwise at most two keys accept. `toOuterMeasure_voleMulCheck_batch_bind_le` also samples arbitrary sender state before the weights, with a false constraint included in the bad event. Its `..._three_div` corollary gives `3 / |F|`. The challenge contains one independent field element per constraint and the reply two; these statements are ideal algebraic bounds, not the scalar-challenge QuickSilver protocol, ZK, VOLE-in-the-head security or runtime certificates. An empty batch has no false-constraint event, while over `ZMod 2` the sharp bound is one. The [checked examples](../../ComplexityTests/Crypto/VOLEBatchMulCheck.lean) include deterministic cancellation, exact `13 / 25` acceptance for an adaptive two-gate claim over `ZMod 5`, and randomized state and replies. From the repository root, run `scripts/build.sh ComplexityTests.Crypto.VOLEBatchMulCheck`; a successful build checks those examples. The earlier key-dependent counterexample in [VOLEMulCheck.lean](../../ComplexityTests/Crypto/VOLEMulCheck.lean) still explains why revealing the receiver key before the reply is outside the model.
- **Full honest receiver-view simulation:** import `Complexity.Crypto.Protocols.VOLE.MaskedMulCheck` ([MaskedMulCheck.lean](../../Complexity/Crypto/Protocols/VOLE/MaskedMulCheck.lean)). `maskedMulCheck left right output` is an actual three-round `Reduction` for public gate-index maps into a witness vector. The [cached `voleWorld`](../../Complexity/Crypto/Protocols/VOLE/World.lean) samples one ideal correlation of length `n + 1`; separate oracle interfaces give the sender only its two vectors and the receiver only its key and tags. The final coordinate is a fresh affine mask. The prover sends all `n` corrections, receives one independent public weight per gate, then sends the two blinded coefficients. `maskedMulCheck_complete` proves completeness in this world. For every satisfying wire assignment, `maskedMulCheckView_eq_simulate` equates the complete receiver view—private key and raw tags, corrections, weights and reply—with the witness-free `maskedMulCheckSimulate`. The simulator samples a uniform key, tags, corrections, weights and slope, then solves the verification equation for the constant coefficient. `maskedMulCheckView_closeTo_simulate` gives zero-error closeness. The honest-view law works over finite commutative rings, including zero keys; it does not strengthen the preceding field-dependent soundness bounds. This adapts the fresh-mask step of [FAEST v1.0, §2.3.2, pp.12–13](https://faest.info/faest-spec-v1.0.pdf) to full-field wires and vector weights. It covers one honest execution with a fresh mask, not mask reuse, malicious-verifier ZK, scalar-challenge QuickSilver, VOLE-in-the-head security or certified efficiency. Run `scripts/build.sh ComplexityTests.Crypto.VOLEMaskedMulCheck` to check [clients](../../ComplexityTests/Crypto/VOLEMaskedMulCheck.lean) covering shared wires, distinct true witnesses, false-witness failure, an unblinded distinguisher, cache stability, zero keys, F2 and empty batches.
- **Adaptive receiver views in the ideal world:** import `Complexity.Crypto.Protocols.VOLE.AdaptiveMulCheck` ([source](../../Complexity/Crypto/Protocols/VOLE/AdaptiveMulCheck.lean)). `maskedMulCheckReceiverView_eq_simulate` permits any role-local `ProbOracleComp` program returning a `VerifierStrategy`, with arbitrary auxiliary input fixed before fresh setup. The receiver may read its private key/tags, sample coins, choose vector weights from those values and the corrections, and retain a continuation that processes the reply and queries the same cache again. The actual `World`/`runAgainst` view includes the receiver share, full transcript and arbitrary returned view. `maskedMulCheckReceiverSimulate` runs the same initialization and captured continuations; it samples uniform corrections before the receiver chooses weights, then a uniform slope and the corresponding constant coefficient. The proof first reparametrizes setup before the adaptive challenge, leaving the fresh mask independent of the visible prefix. `voleWorld_cached_run` preserves the full cache and client outputs through arbitrary randomized queries. The law holds for satisfying witnesses over finite commutative rings. It covers one fixed correction/challenge/reply schedule with trusted uniform setup and a fresh mask; it does not certify runtime, adversarial setup, resets, concurrent sessions, early-abort schedules, mask reuse or full VOLE-in-the-head security. The [checked clients](../../ComplexityTests/Crypto/VOLEAdaptiveMulCheck.lean) exercise private-key/tag/correction-dependent weights, a retained private coin with zero/adaptive branches and post-reply queries, F2, zero-divisor rings, empty gates, and an actual false-witness distribution inequality. From the repository root, run `scripts/build.sh ComplexityTests.Crypto.VOLEAdaptiveMulCheck`; success checks these clients and the earlier unmasked negative example. This is an original semantic extension of the preceding FAEST masking adaptation, with no new ZK predicate.
- **Native simulator with certified runtime:** import `Complexity.Crypto.Protocols.VOLE.NativePPT` ([source](../../Complexity/Crypto/Protocols/VOLE/NativePPT.lean)). `Native.simulate` is an actual witness-free `ProbComp` program on a supplied encoded public-input carrier. A layout map extracts the unary wire count and binary-index gate triples. `Native.Receiver` is parameterized by that input and its first-message carrier, with four explicit-state callbacks: initialization, adaptive weight selection, reply processing and termination. `Receiver.strategy` adapts them to the existing role-local strategy and reads the same cached receiver share in every phase. `Receiver.mapFirst` preprocesses only the challenge callback using the full input, receiver share and raw corrections. `receiverView_eq_eval_simulate` ties the actual layout to the finite wire maps and proves equality with the raw correction-based ideal-world view for satisfying witnesses. An arbitrary share-dependent first-message map does not assert that a sender can transmit that message; a downstream protocol must prove its own reconstruction law. `isPPTOn_simulate` charges the full input in all four callbacks, layout extraction, first-message conversion, sampler, scalar operations, retained state and full output. Fixing a different receiver closure for every circuit would not establish uniform runtime in the circuit. The ring and scalar encoding are fixed; an actual exact-uniform scalar sampler and strict-PPT certificate are required separately. Arbitrary finite uniform sampling does not follow from finiteness in the strict fair-coin model. The program pads missing weights with zero and discards excess weights; its runtime certificate also covers malformed gate indices through bounded list lookup. The [F2 clients](../../ComplexityTests/Crypto/VOLENative.lean) instantiate every runtime premise, retain a private coin and cached share, vary batch size, and test empty batches, huge binary indices and false-witness failure. The extended input client retains an arbitrary extra word, changes its chosen weight when that word changes, and preserves the converted first message through cached-share reads. From the repository root, run `scripts/build.sh ComplexityTests.Crypto.VOLENative`. This certifies the supplied encoded-state callbacks, not all higher-order strategies. Growing extension fields, full native circuit prover/verifier execution, raw-bit adversarial transport (#2744), adversarial setup, resets, mask reuse and full VOLE-in-the-head security remain separate.
- **Public circuit statements in the ideal VOLE world:** import `Complexity.Crypto.Protocols.VOLE.CircuitSound` ([soundness](../../Complexity/Crypto/Protocols/VOLE/CircuitSound.lean)) and `Complexity.Crypto.Protocols.VOLE.CircuitPrivacy` ([privacy](../../Complexity/Crypto/Protocols/VOLE/CircuitPrivacy.lean)). For the existing `Circuit (arithSignature F)` model, `circuitCheck` authenticates public inputs, addition/constant gates and designated outputs alongside the multiplication batch. Corrections and linear openings are sent together before the weights. `circuitCheck_sound` proves the existing `Verifier.Sound` predicate for the public language `∃ w, C.eval (x ++ w) = y`, against every sender-local strategy with arbitrary initialization, private coins and repeated setup reads. `circuitCheck_eval_execute` justifies delaying the independent hidden key until after the adaptive reply. A failed linear row has error at most `1 / |F|`; otherwise a false public statement forces a failed multiplication gate. This case split retains the batch mixture bound, giving `5/8` over the fixed four-element field. Completeness and `circuitReceiverView_eq_simulate` hold over finite commutative rings: for a satisfying trace, the receiver reconstructs linear openings from its own share, corrections and public targets, then reuses the existing adaptive simulator while retaining its entire transcript and terminal state. The actual sender uses only its two vectors. This is an original circuit-binding construction in the trusted fresh ideal world, with no new circuit or ZK predicate. Run `scripts/build.sh ComplexityTests.Crypto.VOLECircuit` to check [clients](../../ComplexityTests/Crypto/VOLECircuit.lean) covering false public output despite correct internal multiplication, addition-only failure, constants, repeated wires and outputs, private-coin strategies, zero-divisor privacy, empty circuits and a false-statement distribution inequality. Fresh-session amplification, a complete native circuit prover/verifier certificate, adversarial setup, resets, concurrency and full VOLE-in-the-head security remain open under #643.
- **Linear VOLE-in-the-head (`SigmaProtocol`):** [voleInTheHeadSigma](../../Complexity/Crypto/Protocols/VOLE/Basic.lean#L499) packages the three-move protocol in which the prover commits to the aggregate MAC mask `t = ψ y v`, receives the verifier challenge `c` (determining `Δ = ι c`), and responds with the in-the-head VOLE receiver tags `(voleSample x v (ι c)).w`, with `voleInTheHeadSigma_complete`, `voleInTheHeadSigma_specialSoundness` (for prime `q`), and `voleInTheHeadSigma_specialHVZK`. Active two-party VOLE generation and multi-gate circuit compilation remain outside this module; checked finite-field examples are in [ComplexityTests/Crypto/VOLE.lean](../../ComplexityTests/Crypto/VOLE.lean).

## Kilian: honest payload and verifier input accounting

Import `Complexity.Crypto.Computational.Kilian.Succinct` to bound an honest
transcript for a PCP verifier `V`. The
[accounting API](../../Complexity/Crypto/Computational/Kilian/Succinct.lean)
uses `r = V.coins x` random bits and a bound `q` on the number of queries
for every random string of length `r`.

Use `kilianCommunication_honest_le` when those PCP parameters remain explicit.
Its premises require `hlen : ∀ k y, (H k y).length = k.length`, a key of length
`n`, exactly `n` challenge strings, each of length `r`, and the query bound.
It counts the key, commitment root, challenges and honest response payload.
It excludes the statement and the `encPair`/`encList` message framing.
For logarithmic randomness and constant `q`, use
`kilianCommunication_honest_le_log`: the bound is a constant times
`(n + 1)^2 * (Nat.log 2 (enc x).length + 1)`. Thus it is polynomial in the
security parameter and polylogarithmic in the encoded statement length.

For machine time, use the separate
[`computableInPolyTime_kilianVerify`](../../Complexity/Crypto/Computational/Kilian.lean)
certificate. It requires a polynomial-time hash, the digest-length premise
`hlen`, `V.PolyTime enc`, and `hcoins` bounding `V.coins x` logarithmically in
`(enc x).length`. Its clock is polynomial in the **received encoded verifier
input**. `length_kilianVerifierInput_honest_le` bounds that input's framed
encoding, including the statement; it is not itself a runtime certificate.
Combining the two bounds gives polynomial time in `n + (enc x).length` on
honest transcripts when the query bound is polynomial too, as it is for the
PCP-theorem verifier's constant query bound. The verifier does not truncate
malicious oversized messages, so this does not give a clock solely in
`n + (enc x).length` against arbitrary cheating provers.

For the NP endpoint, import `Complexity.Crypto.Computational.Kilian.NP` and use
[`exists_kilianSound_of_mem_NP`](../../Complexity/Crypto/Computational/Kilian/NP.lean).
It combines the collision-resistant `HashFamily` assumption with a PCP-theorem
verifier and a uniform honest-payload bound. Its honest witnesses are accepted
compact PCP tables. It does not supply an efficient conversion from witnesses
of an arbitrary given NP relation to those tables; that remaining part of the
broader argument-system objective is explicit in the source.

The complete checked client
[`ComplexityTests/Crypto/KilianSuccinct.lean`](../../ComplexityTests/Crypto/KilianSuccinct.lean)
includes the import, one-bit/one-query verifier, digest-length proof and bound
application. At `n = 2` its honest transcript has exactly **12 payload bits**,
attaining the generic bound. Its constant hash exercises accounting only;
it is not a collision-resistance example.

For Micali's non-interactive random-oracle compilation of Kilian's protocol,
import `Complexity.Crypto.Computational.Kilian.Micali`
([`Kilian/Micali.lean`](../../Complexity/Crypto/Computational/Kilian/Micali.lean)).
It lifts Merkle tree commitment, opening and verification to `OracleComp`
programs (`merkleRootProg`, `merklePathProg`, `merkleVerifyProg`) over
`MerkleHashSpec`, proves their pure-oracle simulation lemmas under
`OracleComp.evalPure` and lazy random-oracle opening completeness
(`merkleVerifyProg_merklePathProg`), and defines the two-channel Micali prover
and verifier (`micaliProve`, `micaliVerify` over `MicaliSpec α`) where the
Fiat–Shamir query `Sum.inr (x, root)` includes both the statement `x` and the
Merkle root. `micaliVerify_micaliProve_eq_true` and
`micaliHonestGame_eq_pure_true` prove perfect completeness under deterministic
oracles and in the lazy random-oracle experiment `micaliHonestGame` (checked
in [`ComplexityTests/Crypto/Micali.lean`](../../ComplexityTests/Crypto/Micali.lean)).

In the random-oracle model, [`Complexity/Crypto/Computational/MerkleTree/ROMExtract.lean`](../../Complexity/Crypto/Computational/MerkleTree/ROMExtract.lean) replaces two-transcript rewinding with straight-line extraction from a recorded hash query-answer trace `tr : List (List Bool × List Bool)` ([bcs16][bcs16]; Chiesa–Yogev Construction 18.5.3 and Lemma 18.5.7): `findPreimageInTrace` inverts `encPair encBits encBits` via `(unframe, dropFrame)`, `extractNodeFromTrace` and `extractLeafFromTrace` walk `d` levels down from the Merkle root `rt` along the bits of position `i`, and `extractTableFromTrace` reconstructs all `2 ^ d` leaves. When `tr` is collision-free (`TraceCollisionFree tr`) and records every hash step along a valid opening (`PathQueriedInTrace H k tr i leaf path` and `merkleVerify H k d rt i leaf path = true`), `extractLeafFromTrace_eq_some_of_merkleVerify` and `getD_extractTableFromTrace_eq_of_merkleVerify` prove that the extracted leaf and table entry equal `leaf`; conversely, when `tr` is consistent with `H k` (`TraceConsistentWith (H k) tr`) and an accepted queried opening disagrees with `extractLeafFromTrace`, `extractTraceCollision` deterministically extracts a hash collision in `tr` (`extractTraceCollision_spec`, `isCollision_extractTraceCollision`). For a lazy uniform `m`-bit random oracle `memoize (fun _ => BitString.uniformList m)`, `toOuterMeasure_uniformList_mem_list_le`, `toOuterMeasure_memoize_not_traceCollisionFree_step` and `toOuterMeasure_run_memoize_not_traceCollisionFree_le` bound the preimage-hitting probability and the `Q * (Q * (1 / 2 ^ m))` collision probability of any `IsQueryBounded program Q` computation; executable checks are in [`ComplexityTests/Crypto/ROMMerkleExtract.lean`](../../ComplexityTests/Crypto/ROMMerkleExtract.lean).

[`Complexity/Crypto/Computational/Kilian/MicaliSoundness.lean`](../../Complexity/Crypto/Computational/Kilian/MicaliSoundness.lean) combines straight-line Merkle extraction with Fiat–Shamir challenge analysis to prove soundness for an unsalted, two-channel Micali variant in the random-oracle model (Micali 2000; compare Chiesa–Yogev Construction 21.1.1 and Theorem 21.2.1, March 25, 2026 version, pp. 239–242):

- **Fixed-trace soundness and dual collision extraction:** `micaliExtractCompactTable` and `micaliExtractProof` reconstruct the candidate PCP proof from `extractTableFromTrace tr (kilianDepth V x) rt []`. Under `AllOpeningsQueriedInTrace`, `kilianVerify_sound_of_traceCollisionFree` and `micaliVerifyPure_sound_of_traceCollisionFree` show that a collision-free trace forces `V.accepts x (micaliExtractProof V tr x proof.root) ρ = true` on every `V.coins x`-bit challenge in `hFS (x, proof.root)` (`not_traceCollisionFree_or_accepts_of_micaliVerifyPure`), while `exists_collision_of_micaliVerifyPure_of_rejects` deterministically extracts a hash collision in `tr` whenever `V` rejects the extracted proof.
- **Fiat–Shamir challenge union bound and adaptive two-channel ROM soundness:** for a PCP verifier with per-repetition soundness error `≤ 1 / 2` (`2 * acceptCount ... ≤ 2 ^ V.coins x` for `x ∉ L`), `toOuterMeasure_kilianChallenges_accepts_le`, `toOuterMeasure_run_memoize_not_fsTraceSound_le` and `toOuterMeasure_twoStageMicali_le` establish the `(t_FS + 1) * (1 / 2) ^ m` Fiat–Shamir union bound and the two-stage ROM bound. For fully adaptive cheating provers `P : OracleComp (MicaliSpec α) (α × MicaliProof)` that interleave Merkle (`Sum.inl`) and Fiat–Shamir (`Sum.inr`) queries, `micaliExtractProof_cons_of_ne` proves that a fresh Merkle query avoiding root/child digests of `tr_FS` and `tr_MT` leaves `micaliExtractProof` invariant, [`OracleComp.toOuterMeasure_bad_le_two`](../../Complexity/Languages/Probabilistic/UntilBad/TwoCost.lean) generalizes `OracleComp.toOuterMeasure_bad_le` to two-channel cost budgets (`micaliMTCost`, `micaliFSCost`), and `micaliSoundness_bound` (together with `micaliSoundness_bound_of_prover_verifier`) proves `micaliSoundnessGame V L P σ m true ≤ (t_FS + 1) * (1 / 2) ^ m + Q_MT * ((3 * Q_MT + (t_FS + 1)) * (1 / 2 ^ σ))`.
- **Succinctness and `NP` CS-proof corollary:** `micaliProofBits_micaliProvePure_le` and `micaliProofBits_micaliProvePure_le_log` bound the honest proof bit length `micaliProofBits`, and `exists_micaliCSProof_of_mem_NP` combines the PCP theorem (`NP_subset_PCP_log`) with `micaliHonestGame_eq_pure_true`, `micaliSoundness_bound` and `micaliProofBits_micaliProvePure_le_log` for any `L ∈ NP enc` (with `V.tableVerifier` as the honest PCP table relation). Checked examples are in [`ComplexityTests/Crypto/MicaliSoundness.lean`](../../ComplexityTests/Crypto/MicaliSoundness.lean).

To apply the separate-budget corollary, bound verifier Merkle queries only for
`(x, proof) ∈ P.support`; `IsCostBounded.bind_on_support` then adds that bound to the prover's.
A uniform verifier bound over arbitrary proofs is generally unavailable: verification hashes an
authentication path before checking its length. The concrete adaptive client in the
[Micali soundness tests](../../ComplexityTests/Crypto/MicaliSoundness.lean) proves its total bound
of four Merkle calls (two prover calls and at most two verifier calls), so both soundness clients
have a discharged budget rather than a budget assumption. The main total-execution-budget
statement is unchanged.

The cited textbook construction includes privacy parameters and a Fiat–Shamir salt. This variant
uses `(x, root)` queries and a different explicit extraction-error expression. Its compact PCP
table witnesses and payload-size guarantee do not supply arbitrary NP-witness conversion or
native verifier runtime/truncation certificates.

## The BCS transform: public-coin IOPs to non-interactive arguments

Import `Complexity.Crypto.Protocols.BCS.Basic`
([`BCS/Basic.lean`](../../Complexity/Crypto/Protocols/BCS/Basic.lean)) for the
core Ben-Sasson–Chiesa–Spooner compilation [bcs16][bcs16] of an `r`-round,
depth-`d` public-coin Interactive Oracle Proof (`PublicCoinIOP r d Stmt Wit Sym Chal`)
into a non-interactive proof (`BCSProof r Sym`, `bcsProve`, `bcsVerify`):

- **Execution and Fiat–Shamir challenges:** in round `j : Fin r`, the honest
  prover computes the table `bcsHonestTables ... j : Fin (2 ^ d) → Sym` from the
  prior Fiat–Shamir challenges `c_i = bcsChallenge hFS x roots i = hFS x (rootPrefix roots i)`
  (`i < j`) and commits to its encoded leaf list `oracleLeaves encSym d π_j`
  via `merkleRoot H k`. Causal consistency (`bcsHonestTables_eq_iopProverOracles`)
  identifies the sequentially computed tables with `iopProverOracles` evaluated
  on the full challenge vector `bcsHonestChallenges`, yielding perfect
  completeness (`bcsVerify_bcsProve_eq_true`) for every hash `H k` and every
  Fiat–Shamir function `hFS`.
- **Binding and knowledge-extraction reductions:** against committed round
  tables `oracles : Fin r → OracleTable d Sym` with injective symbol encoding
  `encSym`, `bcs_sound_or_merkleCollision` proves that any accepted `BCSProof`
  either makes `iopVerify` accept `oracles` at `bcsChallenge hFS x prf.roots` or
  causes `bcsExtractTableCollision` to output an explicit hash collision for
  `H k` (`isCollision_of_bcsVerify_conflict` covers two proofs with conflicting
  openings against a shared round root). Given a straight-line IOP extractor
  `iopExtract`, `bcs_knowledge_or_soundness_violation_or_collision` and
  `bcs_knowledge_or_merkleCollision` reduce an accepting BCS proof to a valid
  extracted witness `rel x (iopExtract x oracles)`, an IOP knowledge-soundness
  violation at the Fiat–Shamir challenge, or an explicit `H k` collision. Checked
  examples for these deterministic algebraic reductions are in
  [`ComplexityTests/Crypto/BCSTransform.lean`](../../ComplexityTests/Crypto/BCSTransform.lean).

For unconditional random-oracle soundness and straight-line knowledge extraction, import
`Complexity.Crypto.Protocols.BCS.ROM` ([`BCS/ROM.lean`](../../Complexity/Crypto/Protocols/BCS/ROM.lean)),
which lifts the multi-round BCS transform to an explicit two-channel random-oracle model
([bcs16][bcs16]; compare Chiesa–Yogev Construction 25.1.1, Remark 25.1.3, and Theorem 25.2.1,
March 25, 2026 version, pp. 274–278, Theorem 26.1.1 and Construction 26.1.3, pp. 288–289, Chapter
31 Definitions 31.1.1–31.1.2, Definition 31.1.6, Theorem 31.2.1, and Theorem 31.3.1, and Merkle
trace extraction from Construction 18.5.3 and Lemma 18.5.7, pp. 199 and 207):

- **Two-channel BCS random-oracle execution and completeness:** over
  `BCSROMSpec Stmt Chal := MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal` (reusing `MerkleHashSpec`,
  `merkleRootProg`, `merklePathProg`, and `merkleVerifyProg` from
  [`Kilian/Micali.lean`](../../Complexity/Crypto/Computational/Kilian/Micali.lean)), the left
  channel (`Sum.inl`) answers Merkle queries lazily with `BitString.uniformList σ` and the right
  channel (`Sum.inr`) answers transcript-chained Fiat–Shamir queries
  `BCSFSQuery Stmt Chal := Stmt × List (List Bool) × List Chal` lazily with
  `PMF.uniformOfFintype Chal`, querying `(x, rootPrefix roots j, [c_0, ..., c_{j-1}]) ↦ c_j` in
  round `j`. Under any deterministic pair `(hTree, f)`, `evalPure_bcsProveROM` and
  `evalPure_bcsVerifyROM` identify `bcsProveROM` and `bcsVerifyROM` with `bcsProve` and `bcsVerify`
  instantiated with `chainedFS f`, giving perfect completeness in the lazy two-channel ROM
  (`bcsHonestROMGame_eq_pure_true`).
- **Straight-line multi-round oracle reconstruction:** given `Function.LeftInverse decSym encSym`
  and `defaultSym : Sym`, `bcsExtractTable`, `bcsExtractOracles`, and `bcsExtractWitness`
  reconstruct all `r` committed round tables and a candidate witness directly from a Merkle trace
  `tr_MT` via `extractLeafFromTrace` without rewinding. Under `TraceCollisionFree tr_MT` and
  `BCSOpeningsQueriedInTrace`, `iopVerify_bcsExtractOracles_of_bcsVerify` proves that `iopVerify`
  accepts `bcsExtractOracles`, `exists_collision_of_bcsVerify_of_iopVerify_eq_false` extracts a
  trace collision whenever `iopVerify` rejects, and `bcsExtractTable_cons_of_ne` /
  `bcsExtractOracles_cons_of_ne` prove invariance under fresh Merkle answers that avoid target roots
  and child digests.
- **Adaptive two-channel ROM soundness:** under `IOPRoundByRoundSoundness iop lang doomed goodStep`
  with per-round challenge escape probability `≤ ε_rbr`, `BCSGoodState` combines
  `TraceCollisionFree tr_MT` with `BCSChainDoomed` across recorded Fiat–Shamir chains of length
  `≤ r`. Truncating each Fiat–Shamir entry via `List.take r` in `bcsForbiddenDigests` bounds the
  forbidden Merkle digest list by `3 * |tr_MT| + r * |tr_FS|` regardless of adversarial Fiat–Shamir
  root-list sizes, while `fsOutOfOrderTargets` bounds out-of-order Fiat–Shamir chain guessing by
  `|tr_FS| * (1 / Fintype.card Chal)` per query. Generalizing two-channel until-bad accumulation to
  growing budgets on both channels via
  [`OracleComp.toOuterMeasure_bad_le_two_budgets`](../../Complexity/Languages/Probabilistic/UntilBad/TwoCost.lean),
  `bcsROMSoundness_bound` and `bcsROMSoundness_bound_of_prover_verifier` bound `bcsSoundnessGame` by
  `(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) + Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`.
- **Adaptive straight-line ROM knowledge soundness:** `IOPRoundByRoundKnowledgeSoundness` captures
  round-by-round straight-line IOP extraction (and implies `IOPRoundByRoundSoundness` for
  `{x | ∃ w, rel x w}` via `IOPRoundByRoundKnowledgeSoundness.toRoundByRoundSoundness`). In
  `bcsKnowledgeSoundnessGame`, the extractor reconstructs `bcsExtractWitness` from the prover's own
  Merkle trace `tr_P` *before* running `bcsVerifyROM`, with zero rewinding; `bcsROMKnowledgeSoundness_bound`
  and `bcsROMKnowledgeSoundness_bound_of_prover_verifier` (together with the combined-trace variant
  `bcsROMKnowledgeSoundness_trace_bound`) establish the same explicit two-channel error bound. As in
  `MicaliSoundness.lean`, the separate-budget corollaries require verifier Merkle bounds only for
  `(x, prf) ∈ P.support` (discharged via `isCostBounded_bcsMTCost_bcsVerifyROM_of_queries_le`).
  Concrete two-round examples, including an adaptive prover with out-of-order and oversized
  Fiat–Shamir queries, are in [`ComplexityTests/Crypto/BCSROM.lean`](../../ComplexityTests/Crypto/BCSROM.lean).

In Chiesa–Yogev Construction 25.1.1 (pp. 274–275; see also Remark 25.1.3 on root-prefix vs.
hash-chain Fiat–Shamir queries), the BCS protocol already uses `2 * r` separate domain-separated
per-round Merkle and Fiat–Shamir random oracles (with zero-knowledge salt parameters `s_MT`,
`s_FS`), while [bcs16][bcs16] and Chiesa–Yogev Theorems 25.2.1 and 26.1.1 formulate ROM soundness
and straight-line knowledge soundness via IOP state-restoration hypotheses (reduced to
round-by-round soundness and knowledge soundness in Chapter 31, Definitions 31.1.1–31.1.2,
Definition 31.1.6, and Theorems 31.2.1 and 31.3.1) with a state-restoration plus multi-extractor
error expression. Here (`s_MT = s_FS = 0`), `BCSROMSpec` models oracle separation via two unindexed
typed channels (one shared Merkle hash channel with `encPair` node framing, and one
transcript-chained Fiat–Shamir channel) and derives the explicit additive loss above directly from
round-by-round escape hypotheses (`IOPRoundByRoundSoundness`, `IOPRoundByRoundKnowledgeSoundness`,
whose deterministic `extract_of_doomed` on complete `doomed` transcripts is stronger than
Definition 31.1.6's two-phase per-round experiment) and two-channel query budgets (`bcsMTCost`,
`bcsFSCost`), counting all oracle queries including malformed opening paths. Straight-line
extraction (`bcsExtractWitness` on the prover's pre-verifier Merkle trace `tr_P`; compare
Construction 26.1.3) and the soundness games establish exact `OracleComp` probability bounds without
machine-level (`IsPPT` / native Turing-machine) verifier or multi-extractor runtime certificates
(compare Chiesa–Yogev Remark 18.5.8), digest truncation accounting, NP-witness-to-IOP encoding
runtime, or zero-knowledge simulation.

## Shared random oracles and ideal permutations

[Complexity/Crypto/Protocols/Signature/RandomOracle.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Signature/RandomOracle.lean) defines a typed random-oracle signature experiment. Signer, verifier and forger share one lazy hash cache. The forger's coins are drawn explicitly before deterministic oracle interaction, enabling replay. Signing and hash queries have separate bounds. Key generation can be an arbitrary PMF, so this finite experiment is not identical to the native `SignatureScheme` interface.

[Complexity/Crypto/Protocols/SigmaProtocol/FiatShamir.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/FiatShamir.lean) hashes `(message, commitment)` to the challenge and proves correctness and a quantitative EUF-CMA bound using special soundness, special HVZK, commitment unpredictability and the generic forking lemma. The bound includes signing/programming collisions, challenge guessing and the square-root forking term. It is a finite exact-security reduction; an asymptotic machine claim additionally needs the encoded efficiency bridges. The module cites Bellare–Neven and Boneh–Shoup and labels its comparison with their constants [bs23][bs23]. Over a `PrimeOrderGroupFamily`,
[`Complexity/Crypto/Computational/SchnorrSignature.lean`](../../Complexity/Crypto/Computational/SchnorrSignature.lean)
provides bit-encoded key generation, commitment, response, signing from supplied coins and challenge,
verification and commitment recovery, with polynomial-time certificates. The supplied challenge
must come from hashing `(message, commitment)` in the surrounding signature protocol; these
arithmetic operations alone do not enforce random-oracle consistency.

The word verifier compares the supplied commitment with canonical public commitment recovery.
For a canonical public key, acceptance forces the commitment into the encoding range, for arbitrary
response and challenge words; no group-membership decoder is assumed. This rejects aliases such as
`32` in place of residue `9` in the group modulo `23`, which the previous arithmetic comparison
normalized. The encoded verification equation, honest completeness and native runtime certificates
are preserved. Malformed public keys have no encoding-range guarantee. The typed-game transport of
arbitrary hash words and the approximate key-generation law remain part of the full ROM bridge
[#2568](https://github.com/cslib-community/complexitylib/issues/2568).

The existing `fiatShamir` and its finite security theorem accept an injective
`hashPoint : (M × T) ↪ Query`. Signing and final verification query `hashPoint (m, t)`, while
arbitrary other `Query` values remain in the same cache and count toward the hash-query budget.
The original clients use the identity embedding. The proof uses injectivity to recover the same
message and commitment at a successful fork; it requires no image-membership test or decoder.
This representation generalization ([#2684](https://github.com/cslib-community/complexitylib/issues/2684))
preserves the quantitative bound. It does not certify a native implementation of `hashPoint` or
complete the concrete word Schnorr reduction and its key-generation/signing approximation hops.

`FiatShamir.reduction` now takes an explicit `fallback` output for a failed fork. The existing
quantitative theorem holds for every such value, with no requirement that it satisfy the witness
relation. The Schnorr reduction wrappers use zero. This removes the hidden choice of the failure
output ([#2774](https://github.com/cslib-community/complexitylib/issues/2774)); it does not certify
the reduction's native runtime or its ideal scalar sampling. Replacing the transcript and answer
defaults in a native implementation still requires a bounded-execution nonexhaustion proof.

[`SchnorrSignature/WordROM.lean`](../../Complexity/Crypto/Computational/SchnorrSignature/WordROM.lean)
instantiates that theorem with the actual native word verifier. `schnorrWordSigma` keeps statements
as group elements, so the public key is canonical, but permits arbitrary commitment and response
words. Acceptance recovers a canonical commitment in the proof; only response scalars are decoded.
Thus scalar aliases remain valid while commitment aliases are rejected. Its simulator and
extractor reuse the typed Schnorr laws, proving perfect HVZK, special soundness and the
`1 / F.order d` commitment bound.

`schnorrWordROMScheme` hashes `encPair encBits encBits (message, commitment)` into `m`-bit
challenges when `2 ^ m ≤ F.order d`, retaining all other hash words in the same cache. Its finite
bound is `Qs*(Qs+Qro)/F.order d + (Qro+1)/2^m + sqrt((Qro+1)*ε')`, where `ε'` is the displayed
forking reduction's discrete-log success. Key and signing scalars use ideal uniform laws. This
completes the representation milestone [#2696](https://github.com/cslib-community/complexitylib/issues/2696);
native saved-forger composition, adaptive key-generation/signing `CloseTo` game hops and efficient
forking remain open. No guarantee is asserted for malformed public keys, and no group decoder is
assumed. Concrete scalar-alias extraction, rejected commitments, and distinct/repeated junk hash
queries are checked in
[`Crypto/SchnorrWordROM.lean`](../../ComplexityTests/Crypto/SchnorrWordROM.lean).

The same module instantiates `schnorrFamilyROMScheme` with `m`-bit challenges when
`2 ^ m ≤ F.order d`, and `schnorrScalarROMScheme` with full scalar challenges. Their exact typed
EUF-CMA bounds account for both signing queries and random-oracle queries. The asymptotic theorem
`negligible_eufCmaGame_schnorrFamilyROMScheme` assumes negligible success of the specified forking
reduction. Applying the strict-PPT discrete-logarithm assumption still requires an efficient
realization of that reduction, with encoded adaptive signing/hash access and final-message
freshness. The private-coin prerequisite is supplied by `IsOraclePPTOn.exists_savedCoins` in
[`Oracle/Replay.lean`](../../Complexity/Computability/Probabilistic/Oracle/Replay.lean), which charges
full-input replay and retains external state.
[`Signature/WordRandomOracle.lean`](../../Complexity/Crypto/Computational/Signature/WordRandomOracle.lean)
also gives a key-independent saved-coin adapter for actual Boolean-channel word forgers, with
full-input native replay and equality of the existing shared-world and EUF-CMA games. All word
hash payloads stay distinct. Applying that adapter to Schnorr's concrete query encoding, composing
the signer/hash handlers, and certifying the complete forking reduction remain open. See the
checked algorithms and typed-ROM examples in
[`ComplexityTests/Crypto/SchnorrSignature.lean`](../../ComplexityTests/Crypto/SchnorrSignature.lean).

[`SchnorrSignature/NativeROM.lean`](../../Complexity/Crypto/Computational/SchnorrSignature/NativeROM.lean)
provides the actual `schnorrROMSign` and `schnorrROMVerify` oracle programs. The signer samples
`sampleExp n d`, normalizes the nonce modulo the group order, and hashes the same encoded pair.
The verifier uses the existing total outer-signature decoder and canonical commitment verifier.
Both read at most `m` reply bits with `query_take'`; their `IsOraclePPTOn` certificates
(`isOraclePPTOn_schnorrROMSign`, `isOraclePPTOn_schnorrROMVerify`) charge all of their inputs—group
description, unary challenge width `m`, and key, message or signature words, plus unary sampling
accuracy `n` for the signer.
These runtime guarantees apply even to empty or arbitrarily long external replies.

Their joint semantic laws use a stateful handler returning `BitString m`, so every cached answer
has the required width. They preserve the complete signature/cache law; verification is exact,
and actual signing differs from the ideal word-ROM signer by at most `2⁻ⁿ` per call. This error
comes from the proved `sampleExp` law using `n + binaryLength(q)` fair coins, without an assumed
coupling. The separate actual key-generation law `closeTo_schnorrSigKeyGen` also costs at most
`2⁻ⁿ`. The milestone [#2708](https://github.com/cslib-community/complexitylib/issues/2708) does not
compose these errors across adaptive signing requests or certify the full forking reduction.
Checks in [`Crypto/SchnorrNativeROM.lean`](../../ComplexityTests/Crypto/SchnorrNativeROM.lean)
cover bounded reply prefixes, aliases, malformed outer signatures, a cache hit retaining junk
entries, and preservation of external state through private nonce sampling.

[`SchnorrSignature/EncodedROM.lean`](../../Complexity/Crypto/Computational/SchnorrSignature/EncodedROM.lean)
exposes the same arithmetic as `schnorrEncodedROMScheme`, an instance of the existing shared-ROM
scheme with word keys and outer signature words. Its key law and scalar-nonce law are explicit:
the actual sampler choices and the ideal uniform choices are not identified. Canonical-key
per-call laws reuse the native signer/verifier realization, including their complete external
state. No public-key decoder or additional reply-cap premise is introduced.

`schnorrDecodedForger` retains the forger's coins, encodes canonical public-key inputs and signing
replies, and total-decodes its final signature. Every hash word remains distinct. Both signing
and hash budgets are preserved, as are the shared cache and signing-message log. The theorem
`eufCmaGame_schnorrEncodedROMScheme_eq` gives exact equality with the canonical word-pair game
only for the ideal key and nonce laws. Freshness is still final-message nonmembership, so repeated
signing requests are allowed. In particular, malformed outer framing is not automatically
rejected: `[true,true]` decodes to the identity commitment and zero response and is accepted under
the identity public key in the checked order-11 example. The regressions in
[`Crypto/SchnorrEncodedROM.lean`](../../ComplexityTests/Crypto/SchnorrEncodedROM.lean) also retain
distinct junk-cache entries and distinguish fresh from signed final messages. This completes the
representation milestone #2742; adaptive actual-sampling error composition, the key-generation
transport and the native efficient forking reduction remain #2568.

For strict-PPT **identification** under discrete log, use `SchnorrImpersonator`,
`schnorrDirectGame` and `negligible_schnorrDirectGame`; for an adversary given independent honest
conversations, use `SchnorrEavesdropAdversary`, `schnorrEavesdropGame` and
`negligible_schnorrEavesdropGame` from
[`SchnorrEavesdrop.lean`](../../Complexity/Crypto/Computational/SchnorrEavesdrop.lean).
These identification games draw a fresh verifier challenge after the adversary's commitment.
Signature EUF-CMA instead gives adaptive signing and hash access, uses the same memoized hash
answer at verification, and rejects a final message previously signed. Discarding a message field
from an identification adversary does not supply this signature reduction.

[`Complexity/Crypto/Protocols/SigmaProtocol/FiatShamirNIZK.lean`](../../Complexity/Crypto/Protocols/SigmaProtocol/FiatShamirNIZK.lean)
compiles a public-coin `SigmaProtocol X Y T C Z` into a non-interactive proof system
(`fiatShamirNIZKProve`, `fiatShamirNIZKVerify`) over the statement-bound random-oracle specification
`NIZKHashSpec Y T C := fun _ : Y × T => C` ([bs23][bs23], Sections 20.3.3–20.3.5):

- **Completeness and statement binding (`Section 20.3.3`):** `fiatShamirNIZK_complete` proves
  acceptance with probability `1` (`= PMF.pure true`) from any initial lazy random-oracle cache when
  `R x y` holds. Querying `H` on `(y, t)` rather than `t` alone is required when statements can be
  chosen adaptively after querying `H`; a concrete `ZMod 5 × ZMod 5` Schnorr counterexample in
  [`ComplexityTests/Crypto/FiatShamirNIZK.lean`](../../ComplexityTests/Crypto/FiatShamirNIZK.lean)
  forges accepted proofs of false statements with probability `4 / 5` under `H(t)` (`Qro = 1`),
  versus the `2 / 5` cap enforced by `H(y, t)`.
- **Adaptive multi-theorem zero knowledge (`fiatShamirNIZKRealGame`, `fiatShamirNIZKSimGame`; Attack
  Game 20.3 and Theorem 20.3 / Equation (20.9)):** over `NIZKDistinguisherSpec` (`.inl (x, y)` for
  proving, `.inr (y, t)` for hashing) with an explicit checker `valid : X → Y → Bool`, invalid
  queries (`valid x y = false`) return `none` identically without modifying the cache, while valid
  queries are answered in `fiatShamirNIZKSimGame` by the witness-free programmable-ROM simulator
  `nizkSimProve simulate`. Whereas Boneh–Shoup's Figure 20.2 simulator returns `fail` when `(y, t)`
  is already programmed in the oracle table, `nizkSimProve` overwrites `(y, t)` at the head of the
  association-list cache; the `IdenticalUntilBad` collision hop justifies this overwrite simulator,
  yielding `abs_sub_fiatShamirNIZKRealGame_simGame_le` and
  `advantage_fiatShamirNIZKRealGame_simGame_le` (`≤ Qp * (Qp + Qro) * δ`) under `SpecialHVZK` and
  `UnpredictableCommitments R δ`.
- **ROM proof of knowledge (`Section 20.3.4`) and derived simulation-extractability:** via
  `Forking.fork` (Bellare–Neven, Lemma 1), `succProbability_fiatShamirNIZKPokGame_le` bounds an
  explicit-coin `Qro`-hash cheating prover's acceptance probability by
  `(Qro + 1) / |C| + √((Qro + 1) * ε')` for `fiatShamirNIZKExtract` (with `oneWayGame` and
  false-statement soundness corollaries). Combining the Attack Game 20.3 zero-knowledge hop with
  `SimCoinSource` presampling and Bellare–Neven Lemma 1 yields a derived fresh-pair
  simulation-extractability reduction: when the adversary also makes up to `Qp` adaptive prove calls
  and outputs `(y*, (t*, z*))` whose pair `(y*, t*)` was not returned by the prove oracle,
  `fiatShamirNIZKSimExtractWith` (with `fiatShamirNIZKSimExtract` using `PMF.pi` over finite `Y` and
  `linearSimCoinSource` avoiding statement/group finiteness on `SigmaProtocol.linear` and
  `SigmaProtocol.schnorr`) achieves `ε ≤ Qp * (Qp + Qro) * δ + (Qro + 1) / |C| + √((Qro + 1) * ε')`
  (`succProbability_fiatShamirNIZKRealExtGameOn_le`, `succProbability_fiatShamirNIZKRealExtGame_le`).
  All bounds are exact finite probability laws in `OracleComp`; machine-level `IsPPT` efficiency
  bridges for rewinding extractors are separate.

The ideal-permutation model gives an adversary both forward and inverse access to one consistent random permutation. Separate cipher/primitive channels support [Complexity/Crypto/Protocols/Cipher/EvenMansour.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/EvenMansour.lean); the two-key and single-key advantages are bounded by `2*Q_cipher*Q_primitive/|G|`. [Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean) proves three-round forward and four-round strong/bidirectional Feistel results and an explicit three-round chosen-ciphertext attack, while [Complexity/Crypto/Protocols/Cipher/FeistelNetworks.lean](../../Complexity/Crypto/Protocols/Cipher/FeistelNetworks.lean) (tested in [ComplexityTests/Crypto/FeistelNetworks.lean](../../ComplexityTests/Crypto/FeistelNetworks.lean)) adds substitution–permutation networks (`spnNetworkEquiv`, `bijective_spnNetworkEquiv`), original alternating unbalanced Feistel networks on odd/even block lengths (`unbalancedFeistel4`, `unbalancedFeistel4BitString`, built on the bit-string split `BitString.halfSplitEquiv` in [HalfSplit.lean](../../Complexity/Foundations/Data/BitString/HalfSplit.lean)), degenerate round-function periodicity (`feistelNetwork_replicate_zero`, `feistelNetwork_replicate_id`), and explicit 1-round CPA (`feistel1CPAAttack`), 2-round CPA (`feistel2CPAAttack`), 3-round repeated-key CPA (`feistel3RepeatedKeyCPAAttack`), and sharper `(|G| - 1)⁻¹` 3-round CCA (`idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one`) permutation-fiber distinguisher bounds (fiber counts from [RandomPermutation/ExtPermsCard.lean](../../Complexity/Languages/Probabilistic/RandomPermutation/ExtPermsCard.lean)) (with original concrete probability bounds). These are bounded-query theorems over finite groups with exact ideal functions/permutations. Native local computation is not charged merely by `IsQueryBounded`. The uniform computational counterparts live in [Complexity/Crypto/Computational/PseudorandomPermutation.lean](../../Complexity/Crypto/Computational/PseudorandomPermutation.lean) (`BlockCipher`, `BlockCipher.PRP`, `BlockCipher.StrongPRP` against oracle-PPT word distinguishers, with explicit security parameter and the `[]` convention for malformed blocks), [Complexity/Crypto/Computational/EvenMansour.lean](../../Complexity/Crypto/Computational/EvenMansour.lean) (`evenMansourCipher` and `singleKeyEvenMansourCipher`, randomized `ProbOracleComp` and `WordOracleComp (Bool × Bool)` ideal-permutation security bounds `2 * Q_e * Q_π / 2 ^ n`, polynomial-query `Negligible` advantage, and `Game.Indistinguishable` against `IsOraclePPT encBool` distinguishers), and [Complexity/Crypto/Computational/LubyRackoff.lean](../../Complexity/Crypto/Computational/LubyRackoff.lean): `PseudorandomFunction.prp_lubyRackoffCipher` proves that the three-round cipher `lubyRackoffCipher` built from a `PseudorandomFunction` is a PRP. Its proof reduces to `PseudorandomFunction.multiKey` with an oracle-PPT adapter, and both modules transfer their finite-group bounds to randomized adversaries by fixing their private coins (`ProbOracleComp.coinLaw`, [CoinFixing.lean](../../Complexity/Languages/Probabilistic/Oracle/CoinFixing.lean)). `PseudorandomFunction.strongPRP_lubyRackoff4Cipher` proves that the four-round cipher `lubyRackoff4Cipher` is a strong PRP, in the same way, through a bidirectional adapter.

## General zero knowledge: quantifier orders, primary-input clocks, and instance indexing

[GenerableZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L144) chooses one simulator for each uniform strict oracle-PPT verifier before all efficiently generable instance, witness and auxiliary-input families. Those families are deterministic polynomial-time functions of unary `n`. The stronger [AuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L174) permits arbitrary polynomially bounded instance, witness, verifier auxiliary-input (`z`) and distinguisher auxiliary-input (`z'`) families, and therefore potentially nonuniform advice; its simulator is chosen once per `Vstar` before the families and distinguisher and is certified on `(1^n, (a, z))`.

To work with arbitrary, **unbounded** auxiliary inputs `z : List Bool` whose length is not bounded by the security parameter, import `Complexity.Crypto.Computational.ZeroKnowledge.AuxClock` ([ZeroKnowledge/AuxClock.lean](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean)), which builds on [IsPPTWithAux](../../Complexity/Computability/Probabilistic/PPT/AuxClock.lean#L149) and [IsOraclePPTWithAux](../../Complexity/Computability/Probabilistic/PPT/AuxClock.lean#L160) and machine-level input-tape prefix locality ([MultiTapeMachine.runFrom_eq_of_prefix_agree](../../Complexity/Computability/Machines/Turing/MultiTape/Probabilistic/PrefixLocality.lean#L60)):

- **Family-indexed unbounded auxiliary input ([UnboundedAuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L167)):** the malicious verifier `Vstar` is clocked in the primary input `(1^n, a)` via `IsOraclePPTWithAux (encPair encUnary enc) encBits`. One witness-free simulator `S` is chosen per `Vstar` before the families and distinguisher, certified by `IsPPTWithAux (encPair encUnary enc) encBits`, and depends only on a polynomial prefix of `z`. Every distinguisher `adversary` clocked in `((1^n, a), view)` via `IsPPTWithAux` receives the **full untruncated** `z n` and has negligible advantage across all polynomially bounded valid `(a, w)` families and arbitrary, unbounded `z : ℕ → List Bool`.
- **Instance-indexed (`x`-indexed) unbounded auxiliary input ([InstanceAuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L379)):** `Vstar` is clocked in the primary instance `x` via `IsOraclePPTWithAux enc encBits`, and one simulator `S` certified by `IsPPTWithAux enc encBits S` is chosen per `Vstar` before the distinguisher, polynomial bounds, instance `x`, witness `w` and auxiliary input `z`. For every distinguisher `adversary` clocked in `(x, view)` via `IsPPTWithAux (encPair enc encBits) encBool` (receiving the full untruncated `z`), every witness-length bound `w.length ≤ c_w * (n + 1) ^ d_w` at `n = (enc x).length`, and every inverse-polynomial degree `k`, all sufficiently large valid instances `(x, w)` and all arbitrary `z : List Bool` have distinguishing advantage at most `1 / ((n : ℝ) + 1) ^ k`.
- **Clock and indexing bridges:** `AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge` (with its `ZeroKnowledgeProof` and `ZKProof` projections) lifts `AuxiliaryInputZeroKnowledge` to `UnboundedAuxiliaryInputZeroKnowledge` by defining `S n a z := S₀ n a (z.take (T_V n a))` and instantiating `z` with the verifier-sized prefix and `z'` with the distinguisher-sized prefix, and `UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge` (hence `AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`) bridges to `InstanceAuxiliaryInputZeroKnowledge`.

`ZeroKnowledgeProof` bundles native honest interaction and verification, perfect completeness, soundness at most `1/3` against arbitrary provers, and the generable ZK predicate. `ZeroKnowledgeProof.mem_IP` is an explicit bridge into the interactive-proof class. [ZKProof](../../Complexity/Crypto/Computational/ZeroKnowledge/Soundness.lean#L71) generalizes the soundness bound to a security-parameter function `soundness : ℕ → ENNReal` (with `ZeroKnowledgeProof.toZKProof` embedding constant `1/3` soundness), and [ZKProof.NegligibleSoundness](../../Complexity/Crypto/Computational/ZeroKnowledge/Soundness.lean#L206) pairs finiteness `∀ n, soundness n ≠ ⊤` with `Negligible (fun n => (soundness n).toNNReal)` (`negligibleSoundness_one_third_pow` discharges `(1/3) ^ (k n)` for `n ≤ k n`, and [IsOraclePPTOn.sequentialRepeat_count](../../Complexity/Computability/Complexity/Classes/IP/Repetition.lean#L135) certifies polynomial-count sequential verifier repetition). [OneWay.exists_zeroKnowledgeProof_of_mem_NP](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L575) establishes the single-round `1/3`-soundness `ZeroKnowledgeProof` notion for NP from a uniform OWF with 3SAT assignments of the Karp-reduced formula as witnesses, while [OneWay.exists_zeroKnowledgeProof_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Levin.lean#L187) and [PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Levin.lean#L172) compose a Levin reduction ([CookLevin.ThreeSAT_levinHard](../../Complexity/Computability/Complexity/CookLevin/Levin.lean#L234)) so that `zk.isWitness a w = true ↔ R.IsWitness a w` holds for the NP relation's own witnesses. Sequential repetition across `k(n) = n + 1` independent masked rounds in [GMW/Sequential.lean](../../Complexity/Crypto/Computational/GMW/Sequential.lean), its multi-round rewinding simulator in [GMW/Sequential/Simulator.lean](../../Complexity/Crypto/Computational/GMW/Sequential/Simulator.lean), and the Karp/Levin composition in [ZeroKnowledge/Amplification.lean](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean) amplify soundness to `(1/3) ^ (n + 1)` against arbitrary stateful provers, giving [OneWay.exists_zkProof_of_mem_NP](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean#L336) and [OneWay.exists_zkProof_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean#L348) from a uniform OWF.

The unrestricted auxiliary-input theorems (`AuxiliaryInputZeroKnowledge`, `UnboundedAuxiliaryInputZeroKnowledge`, and `InstanceAuxiliaryInputZeroKnowledge` for both the single-round and sequentially amplified GMW proof systems) require the advice-supplied generator premise `GMW.AdvicePRG` rather than uniform OWF security; [`NonuniformPRG.advicePRG`](../../Complexity/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L76) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../Complexity/Crypto/Computational/OneWayToPRG.lean#L77) discharge this premise from any [`NonuniformOneWay`](../../Complexity/Crypto/Computational/Nonuniform/Basic.lean#L304) function. This yields the single-round `1/3`-soundness theorems [`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_mem_NP`](../../Complexity/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L134) and [`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_npRelation`](../../Complexity/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L145) together with the full soundness-amplified GMW landmark theorems [`NonuniformOneWay.exists_zkProof_of_mem_NP`](../../Complexity/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L190) and [`NonuniformOneWay.exists_zkProof_of_npRelation`](../../Complexity/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L205) with soundness `(1/3) ^ (n + 1)`, `ZKProof.NegligibleSoundness`, and `ZKProof.AuxiliaryInputZeroKnowledge` (lifting via `AuxClock` to `ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and `ZKProof.InstanceAuxiliaryInputZeroKnowledge`). The protocol is an adapted masked-3SAT truth-table commitment construction, rather than a literal encoding of the original GMW three-color protocol. Complete checked examples for all three auxiliary-input interfaces, their clock/indexing bridges, sequential soundness amplification, and the nonuniform-OWF derivations are in [ComplexityTests/Crypto/ZeroKnowledge.lean](../../ComplexityTests/Crypto/ZeroKnowledge.lean) and [ComplexityTests/Crypto/Nonuniform.lean](../../ComplexityTests/Crypto/Nonuniform.lean).

## Synchronous multiparty computation

[MultiOracleSpec](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/Basic.lean#L95) gives typed k-ary ideal calls. A `Round` is a private authenticated message or an ideal call with an injective assignment of participants to slots. A `Schedule` is a fixed list of rounds. Each party's view includes only its input, private coins and delivered messages/answers; its output depends on that view. Channels are synchronous and the schedule is fixed, not selected by an asynchronous network adversary.

`PerfectSemiHonestPrivate` requires equality of the joint coalition-view and complete-output law with an explicit ideal simulator for every static coalition. `PerfectSemiHonestPrivateProper` restricts the coalition to a proper subset. These are perfect distributional notions, not computational indistinguishability. Malicious behavior, adaptive corruption, concurrent composition and universal composability are not present in this interface.

The construction chain is explicit:

1. [perfectSemiHonestPrivate_twoPartyMul](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/SharedMul.lean#L290) realizes two-party shared multiplication in an ideal 1-out-of-4 OT world.
2. `perfectSemiHonestPrivate_multiPartyMul` composes pairwise multiplication for m parties.
3. [perfectSemiHonestPrivate_gmwCircuit](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/CircuitEval.lean#L1206) evaluates Boolean circuits over additive shares. It refreshes output shares to support arbitrary output-wire aliases.
4. [PerfectSemiHonestPrivate.compose](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/Composition.lean#L734) proves typed k-ary subprotocol substitution. Deterministic GMW-OT has full-coalition privacy; the randomized wrapper uses proper coalitions.
5. [exists_perfectSemiHonestPrivate_ot14_of_polyTime](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/PolyTime.lean#L5989) compiles a uniform word-level polynomial-time functionality to circuits and supplies native certificates for the centralized joint word-oracle runner and each proper-coalition simulator.

The final theorem fixes the number of parties and has explicit polynomial-time unary schedules for per-party input/output and random-tape widths. Its efficiency assertion concerns the **centralized joint runner**, not separately certified local native machines for every party. Its randomized privacy assertion excludes the full coalition. The source explicitly compares this variant with Goldreich's Chapter 7 and contains a full-coalition counterexample to its independent-coin-share simulator in [ComplexityTests/Crypto/MPC.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/MPC.lean). The primary book page confirms Chapter 7's relevant semi-honest, composition and OT-completeness development; the delicate full-coalition comparison is retained as the formalization's documented statement boundary, not independently adjudicated here [goldreich04][goldreich04].

For arithmetic share multiplication in an ideal Beaver-triple preprocessing hybrid model over `ZMod p`, import [`Complexity.Crypto.Protocols.MPC.Beaver`](../../Complexity/Crypto/Protocols/MPC/Beaver.lean) (and [`Complexity.Crypto.Protocols.MPC.Broadcast`](../../Complexity/Crypto/Protocols/MPC/Broadcast.lean) for the reusable sender-indexed synchronous broadcast combinator `broadcastSteps`, `evalWith_broadcastSteps`, and `outputAt_broadcastSteps`). `beaverMulProtocol p m` queries `beaverTripleSpec p m` once, broadcasts the masked openings `(x_i - a_i, y_i - b_i)`, and outputs additive shares summing to `(∑_i x_i) * (∑_i y_i)` (`sum_output_beaverMulProtocol`), generalizing the 2.5-party dealer protocol of [bs23][bs23] (Section 23.2.2) to `m` parties. `perfectSemiHonestPrivateProper_beaverMul` proves `PerfectSemiHonestPrivateProper` in `beaverTripleWorld p m` for the ring-polymorphic `sharedMulFunctionality m` against every proper static coalition `I ≠ Finset.univ` via `beaverMulSim`; this is an exact distributional equality in the ideal triple-preprocessing hybrid model, with no polynomial-time simulator certificate or preprocessing realization. The same module includes `tamperedOpeningExtract_eq`, `eval_tamperedOpeningReal`, and `le_advantage_tamperedOpeningBitGame`: an original standalone `ProbComp (ZMod p)` / `Game` illustration (motivated by [bs23][bs23], Section 23.2.4) showing that if 2-party unauthenticated Beaver multiplication of `[x] * [0]` is followed by revealing the honest party's output share after an additive-error tampered opening, the tampered transcript determines `x` and distinguishes `x ∈ {0, 1}` with advantage at least `1/2` against any input-independent `blindGuess : ProbComp (ZMod p)`. This illustration is not an execution of `beaverMulProtocol` (which does not broadcast output shares) and is not a general malicious-security definition. Checked examples are in [ComplexityTests/Crypto/Broadcast.lean](../../ComplexityTests/Crypto/Broadcast.lean) and [ComplexityTests/Crypto/Beaver.lean](../../ComplexityTests/Crypto/Beaver.lean).

For SPDZ authenticated secret sharing, online Beaver multiplication (Damgård–Pastro–Smart–Zakarias, CRYPTO 2012; ePrint 2011/535, §2 and Fig. 1), and batch `MACCheck` (Damgård–Keller–Larraia–Pastro–Scholl–Smart, ESORICS 2013; ePrint 2012/642, App. D.1, Fig. 10 and §5.1, Lemma 1) over `ZMod p` (the 2012 paper works over `F_{p^k}`), import [`Complexity.Crypto.Protocols.MPC.SPDZ`](../../Complexity/Crypto/Protocols/MPC/SPDZ.lean). `AuthShare p n` represents `(delta, valShares, macShares)` with `AuthShare.Valid alpha` asserting `∑_i (macShares i) = alpha * ((∑_i (valShares i)) + delta)`. Linear operations (`AuthShare.add`, `AuthShare.neg`, `AuthShare.sub`, `AuthShare.smul`, `AuthShare.addConst`) and online Beaver multiplication (`AuthShare.mulOnline`) preserve `Valid alpha`, agree coordinatewise with `beaverMulShare` on value shares (`AuthShare.valShares_mulOnline_eq_beaverMulShare`), and reconstruct `(∑_i x_i) * (∑_i y_i)` when `d = x - a`, `e = y - b`, and `c = a * b` (`AuthShare.secret_mulOnline_eq_mul`). For a batch of `T` opened values, `macCheckProtocol p n T sampleCoins commit` models steps 5–9 of the 2013 `MACCheck` (Fig. 10: commitment and opening of the residual shares, with the residual adapted to the 2012 `delta`-representation; steps 1–4, which derive the weights from a coin-flipped seed, are replaced by input weights) as a two-round broadcast protocol over `Complexity.Crypto.Protocols.MPC.Basic` and `Complexity.Crypto.Protocols.MPC.Broadcast`; honest batches satisfy `sum_checkResidual_eq_zero` and accept with probability `1` (`eval_snd_macCheckProtocol_eq_pure_true`), while forged openings satisfy `sum_checkResidual_eq_neg_mul` (`∑_i checkResidual (inp i) = -alpha * linearCombAddHom err e`) and the cheating equivalence `sum_checkResidual_add_eq_zero_iff`. Over prime fields (`[Fact (Nat.Prime p)]`), `eval_linearCombZeroGame_eq` proves Stage-1 weight cancellation occurs with exact probability `1 / p` for `err ≠ 0` (via `toOuterMeasure_uniform_linearComb_eq_zero`), `eval_macKey_guess_le` bounds Stage-2 key guessing when the combined error is nonzero (via `toOuterMeasure_uniform_linearComb_eq` on `Unit`), and `eval_macCheckSoundnessGame_le`, `succProbability_macCheckSoundnessGame_le`, and `eval_macCheckSoundnessAdvGame_le` prove that the `MACCheck` cheating equation `alpha * linearCombAddHom err e = deltaShift e` in the standalone games `macCheckSoundnessGame` and `macCheckSoundnessAdvGame` holds with probability at most `2 / p` (the game from the proof of Lemma 1, App. D.3; the game's `alpha` plays the role of an honest party's key share, with corrupt-party contributions and MAC-share tampering absorbed into the shift) against any `e`-adaptive residual shift `deltaShift` and any prior randomized adversary `adv : ProbComp S` independent of `alpha`. In `macCheckProtocol`, weights are supplied as inputs (`PartyCheckInput.weights`) whose joint generation after the openings is not modeled, `alpha` is not sampled by the protocol, `commit : ZMod p → Coins → Comm` is an abstract deterministic commitment map (with `AddCommMonoid` instances on `Coins`, `Comm`, and `ResidualOpening` used only by `broadcastSteps`), and the games analyze the standalone algebraic cheating equation rather than an execution of `macCheckProtocol`, a computational commitment binding reduction, or a UC emulation proof. Checked examples are in [ComplexityTests/Crypto/SPDZ.lean](../../ComplexityTests/Crypto/SPDZ.lean).

For the commitment ingredient toward malicious security, import
[`Complexity.Crypto.Protocols.MPC.OTCommitment`](../../Complexity/Crypto/Protocols/MPC/OTCommitment.lean).
`OTCommitment.Sender` selects arbitrary randomized OT tables from private state and receives
only the ideal sender's `Unit` answer. Apply `binding` to an initial state distribution and a
function producing two candidate openings from the final sender state: it bounds their joint
acceptance probability by `2⁻ᵏ`, without assuming the submitted tables encode a consistent bit.
Keep receiver choices and selected values private; giving either to the sender changes the game.
`perfectHiding` equates full query/answer transcript and final-state laws for arbitrary adaptive
`Receiver` strategies, including all four OT indices. The checked
[OT commitment tests](../../ComplexityTests/Crypto/OTCommitment.lean) demonstrate rejection of an
inconsistent opening, a tight one-call attack with success `1/2`, and the zero-call bound `1`.

For an explicit list opening, import
[`OTCommitment.Opening.PolyTime`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/Opening/PolyTime.lean).
`openPairs choices received submission` returns the accepted bit or `none` for abort or rejection.
It checks that all three lists have the same length before testing every pair's parity and selected
value. `openPairs_ofFn` identifies this total checker with `openResult` on finite-vector encodings;
`openPairs_polyTime` charges the complete choice and answer bit strings and the framed opening
pair list, without a well-formedness hypothesis. The [checked list clients](../../ComplexityTests/Crypto/OTCommitmentOpening.lean)
include short and long inputs in each position. An empty opening accepts either bit when both
receiver lists are empty; this preserves the zero-call boundary and asserts no binding security.

To extract a bit before opening, import
[`OTCommitment.Extraction`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/Extraction.lean).
`extract` takes the strict majority of the actual OT input pair parities, choosing false on a tie.
Only the simulator receives these corrupted sender inputs; this is not extraction from a public
commitment string. `simulatedOpening_coupled` couples `realOpening` with `simulatedOpening` within
`2⁻⌈k/2⌉`, jointly preserving the sender's state at the commit boundary and any auxiliary output
from its opening continuation. The simulator fixes the bit before that continuation runs and
releases only the stored bit or abort. Apply the coupling's `toOuterMeasure_le` for any event of
this joint output. With two mixed-parity rows, extraction error can be `1/2` even though the
double-opening bound is `1/4`; the
[checked examples](../../ComplexityTests/Crypto/OTCommitmentExtraction.lean) attain both bounds.

For native computation, import
[`OTCommitment.PolyTime`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/PolyTime.lean).
`extractPairs_polyTime` certifies the deterministic extractor with input encoding
`encList (encPair encBool encBool)` and output `encBool`. `extractPairs_ofFn` connects the explicit
list algorithm to the OT table extractor. This certificate applies only to the extractor.

For a corrupted receiver, import
[`OTCommitment.Equivocation`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/Equivocation.lean).
`equivocation` proves the exact joint law of the transcript, receiver state and revealed opening.
The simulator runs `receiverRun A false` without the committed bit, then uses `equivocate b` only
when that bit is released at opening. For each recorded index and answer, it keeps the selected
component equal to the answer and reconstructs the other component using the supplied parity.
`equivocation_bind` permits any randomized post-opening continuation on that entire view.
The common `receiverCommit` runner retains the honest sender's actual masks for the proof;
`receiverRun` projects them away and the receiver strategy never sees them. The simulator does
see the corrupted receiver's indices, which are unavailable to a malicious sender in the binding
game. The [checked examples](../../ComplexityTests/Crypto/OTCommitmentEquivocation.lean) cover
slots 2 and 3, adaptive private state and the failure of reusing parity-zero pairs to open to one.

`equivocatePairs_polyTime` in the same `OTCommitment.PolyTime` import certifies the deterministic
map from a revealed bit and an explicit receipt list to opening pairs. Its input encoding is
`encPair encBool (encList (encPair (encFinEnum (Fin 4)) encBool))`; the full four-valued indices
are retained. `equivocatePairs_ofFn` connects this list operation to the transcript reconstruction.

These semantic corruption-specific laws alone do not provide full ideal commitment scheduling,
mid-commit abort, composition, or polynomial-time simulators. The malicious MPC compiler and its
real/ideal simulation remain open in
[#1212](https://github.com/cslib-community/complexitylib/issues/1212).

For a stateful functionality with separate commit and open phases, import
[`Complexity.Crypto.Protocols.Commitment.World`](../../Complexity/Crypto/Protocols/Commitment/World.lean)
and open `Cslib.Crypto.Protocols.Commitment.Phased`. `world` implements the existing
`Interactive.World`: sender queries are `Sum.inl (Command.commit b)`, `Sum.inl Command.open`,
and `Sum.inl Command.abort`; the receiver can only query `Sum.inr ()` to poll. Use
`ProbOracleComp.query (spec := senderSpec ⊕ₒ receiverSpec)` to make these calls and
`world.eval` to observe a program's result. The private `Store` is available for proofs, but is
excluded from that observation. Polling returns `Observation.receipt` while a bit is committed,
then `Observation.opened b` after opening.

This original single-session abort variant ignores early opening and repeated commitments.
Abort before opening is terminal; abort after opening cannot retract the released bit.
`polling_secrecy` handles arbitrary receiver-only programs with private sampling before opening;
it does not assert secrecy when sender commands interleave and open the commitment.
`committed_invariant` preserves the committed bit or abort under arbitrary supported joint
executions. The [checked world clients](../../ComplexityTests/Crypto/CommitmentWorld.lean)
show honest opening, early opening followed by commitment, attempted overwrite, both abort
orders, and adaptive private polling. These are functionality laws, not an OT realization,
UC security, or a simulator runtime certificate.

To connect the OT simulations to these commands, import
[`OTCommitment.World`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/World.lean).
`senderIdeal` samples the actual sender tables and commits `extract ts` before invoking the
sender's opening continuation. It then opens that stored bit or aborts and polls the world.
`senderIdeal_run` identifies its public law with `simulatedOpening`, now including the receipt
and terminal observation; `senderIdeal_coupled` retains the sender state and auxiliary output
with error at most `2⁻⌈k/2⌉`. Start the driver at `.idle` and map `Prod.fst` over its result to hide
the final functionality store.

For a corrupted receiver, `receiverPrefix` has no bit input and `receiverPrefix_committed` proves
its observation is bit-independent in every committed state. `receiverIdeal` runs this prefix,
then a randomized `plan` receiving only the transcript and receiver state. The plan selects
release or abort and returns a retained later private state. Only after the actual open/abort
command and poll does `finish` receive the terminal observation and optional reconstructed
opening. `receiverIdeal_eq_real` equates this complete joint law with the actual honest OT
execution, including both observations, both private states, and any randomized continuation
output. See the [checked simulation clients](../../ComplexityTests/Crypto/OTCommitmentWorld.lean)
for all four OT slots, the mixed-parity attack, withholding and zero calls.

These are semantic `StateT Store PMF` drivers for arbitrary PMF strategies, not realized
`ProbOracleComp` programs or efficient simulators. They cover a fixed-length single session
with one later release decision; arbitrary scheduling, mid-commit abort, malformed bytes,
composition and full malicious MPC remain open.

For a realized receiver simulator, import
`Complexity.Crypto.Protocols.MPC.OTCommitment.Program.PolyTime`.
Supply closed `ProbComp` callbacks `choose`, `receive`, `plan` and `finish`;
`receiverOfPrograms` interprets them in the existing `Receiver` interface.
`receiverPrefixProgram` takes no committed bit. `receiverIdealProgram` alone owns the
commitment-world interface and makes exactly four public calls: commit, receipt poll,
open-or-abort, and terminal poll. `receiverClosedProgram` runs the actual finite handler
from idle, retaining both observations and all receiver data while hiding the final store.
`eval_receiverClosedProgram_eq_real` equates its list-output law with honest OT using the
masks actually sampled during commitment. Abort supplies no reconstructed opening; even
zero rounds pass the terminal observation separately to `finish`.

Apply `receiverClosedProgram_isPPT` with uniform `IsPPTOn` certificates for the four
callbacks on their complete joint inputs. In addition, bound encoded-state growth by a
fixed additive constant for every supported `choose` result and every supported `receive`
result. These are separate obligations: an intermediate state can grow even when a later
callback shrinks it. The input encoding charges the bit, unary round count and initial
state; receipt and opening lists retain all four OT indices and all pair bits. The
[checked program clients](../../ComplexityTests/Crypto/OTCommitmentProgram.lean) provide an
adaptive private-coin receiver with growing answer history, randomized withholding and a
randomized final continuation. They also show why a separately efficient state-doubling
callback fails the additive-growth contract. This certificate covers the fixed receiver
schedule under those hypotheses; arbitrary scheduling, composition and full malicious MPC remain open.

For the corrupted sender, import
[`OTCommitment.SenderProgram.PolyTime`](../../Complexity/Crypto/Protocols/MPC/OTCommitment/SenderProgram/PolyTime.lean).
Supply closed `ProbComp` table-selection and finish callbacks and the deterministic `Sender.receive`
update. `senderOfPrograms` keeps the existing semantic interface; `senderTablesWith` shares its
recursion with the native table-list program. `senderIdealProgram` commits the extracted bit before
sampling finish, privately samples the honest choices, and makes the same four phased-world calls.
Finish receives only the round count and commit-final sender state. It can retain an updated state
or other private information in its auxiliary output. `decodeOpening` maps incorrect list lengths
to rejection; no malformed list is silently truncated into a valid finite opening.

`eval_senderClosedProgram` identifies the actual handler's closed execution with `senderIdeal`.
`senderClosedProgram_coupled` retains both public observations, commit-final sender state and
arbitrary finish output with majority-extraction error `2⁻⌈k/2⌉`.
`senderClosedProgram_coupled_two_mul` gives error `2⁻ⁿ` for `k = 2n`, and
`senderClosedProgram_negligible_error` proves that schedule's error negligible. This is the
extraction error, not the smaller double-opening bound.

Apply `senderClosedProgram_isPPT` with uniform callback certificates on full joint inputs and an
additive encoded-size bound on the **combined round's final state**, for every supported choose
result. The intermediate state may grow polynomially and then shrink in the update; callback
composition charges that work. Every table uses the fixed sixteen-element `Fin 4 → Bool` encoding,
and the growing table list, unary round count, initial state and complete output are all charged.
The [checked sender programs](../../ComplexityTests/Crypto/OTCommitmentSenderProgram.lean) include
private-coin masks with retained history, randomized opening or abort and auxiliary output, the
actual two-round attack with real success `1/2` versus ideal abort, and a separately efficient
doubling update excluded by the growth premise. They instantiate one uniform machine at `k = 2n`
with empty initial history; an arbitrary initial distribution needs its own efficient sampler.

For a complete corrupted sender without callback growth assumptions, import
`OTCommitment.CompleteSender.PolyTime`. Supply one
`program : (ℕ × Input) → WordOracleComp SenderOperation Output` and its global
`IsOraclePPTOn (encPair encUnary input) output program` certificate. The actual input charges the
round count. `SenderOperation` provides fixed four-bit tables, seal, open-bit and abort; the opening
word contains all first pair components followed by all second components and must have length
`2 * k`. Sender replies are always empty. This is a typed command interface, not a general
network-message parser.

`completeSenderReal` executes every accepted row through the existing ideal OT world.
`completeSenderIdeal` commits the extracted bit through the phased handler at seal, before the
complete adversary continues. Sealing requires exactly `k` tables; premature sealing or an excess
pre-seal table aborts. Early opening is ignored, as are tables and repeated seals after sealing.
The first post-seal opening attempt is terminal even when malformed or rejected, so there is no
verification retry. Explicit abort is terminal. Never-sealed execution retains the distinction
between idle and abort. Both laws return the shared phase-history receipt `s.receipt` (rather than
a separate ideal functionality poll), the final receiver observation (`s.observation …` vs.
`Phased.observe store`), and the complete adversary output; the receiver's choices (simulated
internally as simulator coins in `completeSenderIdeal`) and functionality storage remain private.

`completeSender_coupled` bounds disagreement of those actual joint laws by `2^-ceil(k/2)`;
`completeSender_coupled_two_mul` gives `2^-n` at `k = 2n`, to which geometric negligibility applies.
`completeSender_isPPT` certifies both closed executions from the single global adversary
certificate. Only handler storage needs a local growth proof. Existing
`IsOraclePPTOn.query_bounds` supplies query-count and payload-length budgets. The
[complete-program clients](../../ComplexityTests/Crypto/OTCommitmentCompleteSender.lean) include a
sender growing its private buffer by `k` bits in each of `k` rounds: it is globally polynomial
and executes correctly, although no fixed additive per-round state bound holds. They also check
phase and retry rejection, zero rounds, retained private randomness, and the sharp two-round
real acceptance probability `1/2` versus ideal abort.

For a common role-local execution, import `OTCommitment.Serial.CompleteSender` and
`OTCommitment.Serial.Receiver`. `Serial.world k` has separate sender commands and receiver
`select`, `poll` and `readOpening` operations. It executes the existing OT world when the receiver
consumes the one pending row. A second pending table or a seal with an unanswered row aborts;
a row cannot be overwritten or selected twice. Selection requires the pre-seal phase. The first
post-seal opening attempt is terminal even if malformed or rejected; its raw payload stays readable,
while explicit abort exposes none. Private tables, selections and retained answers are storage,
not sender replies. `senderOnly_output` proves that sender-only programs receive constant replies.

`Serial.eval_senderAdapter` routes a complete command program through this world, with an honest
receiver consuming each table before the sender resumes, and recovers `completeSenderReal` exactly.
`Serial.eval_receiverAdapter` uses the existing closed receiver callbacks: each choice is followed
by a fresh mask, the honest table submission and the actual selection. Its release plan sees only
the receiver's transcript and state. The equality to `receiverReal` retains the actual raw opening,
both receipt and terminal observations, private state, randomized release data and continuation
output. Internal masks used to produce the honest opening are absent from that receiver view.
The [serial execution clients](../../ComplexityTests/Crypto/OTCommitmentSerial.lean) exercise
adaptive duplicate slots, opening/answer correlation, zero rows, unanswered rows, rejected retries
and why an opening must not permit a later selection.

These are equalities for two explicit honest-party schedules in an original single-session serial
world. They do not equate arbitrary interleavings or prove a new security notion. A global
receiver-program adapter, uniform native execution contracts for this common world, two-sided
realization, composition/UC and full malicious MPC remain separate obligations.

## Upstream perfect secrecy and sharing

Pinned cslib supplies [PerfectlySecret](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean#L76): observing any positive-probability ciphertext leaves every message prior unchanged. Its equivalent ciphertext-distribution formulation and one-time-pad instance are finite semantic security, with no PPT restriction. The upstream commitment interface separately defines perfect/statistical hiding and perfect binding [cslib][cslib].

[Scheme](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean#L52) bundles deterministic reconstruction for authorized coalitions, a randomness PMF, monotone authorization and equal unauthorized-coalition view laws across all secrets. Shamir's `schemeWith` permits a tail sampler with the translation symmetry needed for privacy; `uniformTailSampler` gives the usual finite-field instance. These are reusable information-theoretic interfaces; the survey does not infer a polynomial-time protocol or a secret-sharing-to-native-MPC compiler from them.

Perfect secrecy, zero knowledge and semi-honest MPC privacy do not substitute for differential privacy's adjacent-dataset comparison, which the next section formalizes.

## Differential privacy

[DifferentialPrivacy/Basic.lean](../../Complexity/Privacy/DifferentialPrivacy/Basic.lean) defines `DifferentiallyPrivate Adj M ε δ` for a mechanism `M : D → PMF R`: for all `Adj`-adjacent datasets `x`, `y` and every set `S` of outputs, `Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ`, with `ε : ℝ`, `δ : ℝ≥0∞` and events measured by `PMF.toOuterMeasure` [DworkRoth2014, Definition 2.4][dworkroth14]. The adjacency relation is an explicit parameter; [DifferentialPrivacy/Hamming.lean](../../Complexity/Privacy/DifferentialPrivacy/Hamming.lean) supplies `HammingAdjacent` (datasets `ι → X` differing in at most one row), the neighbor relation of Ghosh–Roughgarden–Sundararajan [grs12][grs12]. Dwork–Roth's own adjacency is `ℓ₁` distance one between histograms, which is another instance of the parameter, not something these files define. The definition quantifies over ordered pairs, so a symmetric guarantee needs a symmetric relation.

- **Characterizations and post-processing:** `DifferentiallyPrivate.iff_tsum_tsub_le` characterizes the optimal `δ` as the hockey-stick excess `∑ r, (M x r - exp ε · M y r)`, and `iff_apply_le` makes pure privacy a pointwise likelihood-ratio bound. `bind` and `map` give post-processing by an arbitrary randomized or deterministic map (Dwork–Roth Proposition 2.1).
- **Composition:** [DifferentialPrivacy/Composition.lean](../../Complexity/Privacy/DifferentialPrivacy/Composition.lean) proves `DifferentiallyPrivate.bind_pair`, which releases a first output and a second output from a mechanism chosen from the first, at `(ε₁ + ε₂, δ₁ + δ₂)` (Dwork–Roth Theorem B.1, which states equal parameters), and its non-adaptive case `prod` (Theorem 3.16). `adaptiveComposition M k` runs `k` rounds, each choosing its mechanism from the previous outputs. `DifferentiallyPrivate.adaptiveComposition` sums per-round parameters that may depend on the round (Corollary B.2 fixes them).
- **Group privacy:** `DifferentiallyPrivate.hammingDist_le` gives `(k ε, ∑ i < k, exp (i ε) · δ)` at Hamming distance `k`. `hammingDist_le_of_pure` is the `(k ε, 0)` case, the Hamming form of Dwork–Roth Theorem 2.2, and `hammingDist_le'` is the footnote's `k exp ((k - 1) ε) δ` bound, for `0 ≤ ε`.
- **Randomized response:** [DifferentialPrivacy/RandomizedResponse.lean](../../Complexity/Privacy/DifferentialPrivacy/RandomizedResponse.lean) writes the two-coin protocol as a `ProbComp Bool` program. `differentiallyPrivate_randomizedResponse_iff` proves it `(ε, 0)`-private exactly when `ln 3 ≤ ε` (Claim 3.5; tightness is proved here). `differentiallyPrivate_randomizedResponseSurvey` shows the `n`-respondent survey (`OracleComp.pi`) is `(ln 3, 0)`-private for Hamming adjacency, via the product of local randomizers `DifferentiallyPrivate.pi`. `sum_eval_randomizedResponseSurvey_mul_estimator` proves that `2 · (fraction of Yes) − 1/2` is unbiased (§2.3).
- **Geometric and discrete Laplace noise:** [DifferentialPrivacy/DiscreteLaplace.lean](../../Complexity/Privacy/DifferentialPrivacy/DiscreteLaplace.lean) defines `twoSidedGeometric α` with masses `(1 - α) / (1 + α) · α ^ |z|` [grs12][grs12] and `discreteLaplace t` with ratio `exp (-1 / t)` [CanonneKamathSteinke2020, Definition 28][cks20]. `addNoise q noise` releases an integer query plus noise. For a query of real sensitivity `Δ`, `differentiallyPrivate_addNoise_twoSidedGeometric` gives `(Δ · ln α⁻¹, 0)` and `differentiallyPrivate_addNoise_discreteLaplace` gives `(ε, 0)` at scale `Δ / ε` (CKS Lemma 29). `discreteLaplace_toOuterMeasure_Ici` and `discreteLaplace_toOuterMeasure_Iic` give CKS Lemma 30's exact tails `exp (-ε (m - 1)) / (exp ε + 1)`. `twoSidedGeometric_toOuterMeasure_le_natAbs` gives the two-sided accuracy `2 α ^ m / (1 + α)`.

Model boundaries: mechanisms are compared through their exact output laws. Randomized response is a finite `ProbComp` program, but the geometric and discrete Laplace distributions have infinite support, so they are ideal `PMF ℤ` laws, not finite fair-coin programs. Sampling cost, finite-precision error and computational (PPT) differential privacy are not modelled. Advanced composition, the exponential mechanism, continuous Laplace/Gaussian mechanisms and private learning remain open under the *Differential privacy and adaptive data analysis* direction of [ROADMAP.md](../../ROADMAP.md). Run `scripts/build.sh ComplexityTests.Privacy.DifferentialPrivacy --wfail --iofail` to check the [clients](../../ComplexityTests/Privacy/DifferentialPrivacy.lean). They cover a constant mechanism that is `(0, 0)`-private, the identity on bits, which is private for no `ε` when `δ < 1`, randomized response's failure at `ε = 1`, survey group privacy and `k`-fold composition, concrete Hamming adjacency in both directions, the count query's sensitivity under both noise mechanisms, and the masses and tails of the ratio-`1/2` geometric distribution.

## Universal composability with static corruptions

[Protocols/UC/Machine.lean](../../Complexity/Crypto/Protocols/UC/Machine.lean) defines interactive machines (`Machine I E`): a `ProbComp` initial-state sampler and, for each query of the exported interface `E`, an activation in `StateT State (ProbOracleComp I)`. `Machine.comp` composes machines, `Machine.link` runs a program against a machine (removing the exported interface), and `Machine.IsBounded t` bounds the calls of the sampler and of every activation by `t`, counting private samples and imported calls alike. [Protocols/UC/Execution.lean](../../Complexity/Crypto/Protocols/UC/Execution.lean) builds the UC execution of [Canetti](../sources.md#canetti20) on these machines: an `n`-party `Protocol` is a closed machine per security parameter `κ` and corruption set `C` with a party port and a network port, `IdealFunctionality.toProtocol` turns a functionality into a protocol whose network port is its backdoor, `corruptRouter C` lets the environment reach only honest parties on the party port and routes corrupted parties' party-port calls to the adversary, and `exec π A C Z κ z` is the environment's output bit as a `ProbComp Bool` program. [Protocols/UC/Emulation.lean](../../Complexity/Crypto/Protocols/UC/Emulation.lean) defines concrete emulation `EmulatesWithin π φ g ε` (every adversary with per-activation budget `pA` has a simulator with budget at most `g` at `κ + pA κ` and advantage at most `ε pA pZ κ` against every environment with total budget `pZ κ`), the asymptotic `Emulates π φ` (one negligible bound per environment budget), both reflexive and transitive, and their ideal-functionality specializations `RealizesWithin` and `Realizes`.

[Protocols/UC/Linking.lean](../../Complexity/Crypto/Protocols/UC/Linking.lean) proves the package-algebra laws: linking is associative as an equation of programs (`Machine.link_comp`), the forwarding machine is a unit (`Machine.link_id`), and call budgets of compositions and links compose (`Machine.IsBounded.comp`, `Machine.isQueryBounded_link`). [Protocols/UC/DummyAdversary.lean](../../Complexity/Crypto/Protocols/UC/DummyAdversary.lean) uses them for completeness of the dummy adversary: running an adversary `A` is running `dummyAdversary` with `A` absorbed into the environment (`exec_eq_exec_dummy`), so a simulator for the dummy adversary yields the black-box simulator `compSim S_D A` for every `A` (`EmulatesDummyWithin.emulatesWithin`, with the error evaluated at the absorbed environment budget `absorbPoly pZ pA`), and the same module gives the negligible-error equivalence `emulates_iff_emulatesDummy`. Examples are in [ComplexityTests/Crypto/UCDummyAdversary.lean](../../ComplexityTests/Crypto/UCDummyAdversary.lean).

When using these definitions, keep the model boundaries in view. Corruption is static and fixed per session, a session is one closed machine, and messages are pulled by the receiving machine rather than scheduled by the adversary. Moreover, `corruptRouter C` itself only redirects party-port inputs and outputs for `i ∈ C` from the environment to the adversary; stronger corruption power (such as Byzantine state exposure or arbitrary message injection, as in Canetti) exists only insofar as `π κ C` implements it by inspecting `C`, so a protocol independent of `C` is tested only against party-port input/output substitution. Budgets count oracle calls, not running time, so `EmulatesWithin`, `Emulates`, `RealizesWithin` and `Realizes` are statistical/ideal-model notions against interaction-bounded but computationally unbounded adversaries, simulators and environments: protocols whose security rests on computational assumptions generally cannot satisfy `Realizes`, and UC security against polynomial-time machines needs an additional machine-realizability restriction. The environment's budget is a polynomial in `κ` alone and does not grow with its auxiliary input. Concrete transitivity requires the second error to be monotone in the adversary's budget. Checked examples, including an environment that separates two ideal functionalities against every simulator and a check of static-corruption routing, are in [ComplexityTests/Crypto/UC.lean](../../ComplexityTests/Crypto/UC.lean).

## Known Limitations

Only selected protocol endpoints and key definitions were traced. The source files themselves give detailed source mappings; this pass did not independently reconcile every textbook constant, lattice-abort construction or signature reduction. Existing regression tests are not newly executed evidence. The precise coalition and advice restrictions above should be retained even when summarizing the results compactly.

[bcs16]: ../sources.md#bcs16
[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cks20]: ../sources.md#cks20
[cslib]: ../sources.md#cslib
[dworkroth14]: ../sources.md#dworkroth14
[goldreich04]: ../sources.md#goldreich04
[grs12]: ../sources.md#grs12
