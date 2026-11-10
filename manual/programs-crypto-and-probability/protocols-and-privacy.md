# Protocol models, ideal oracles, and privacy

The general [public-coin interactive-reduction model](interactive-reductions.md), including sumcheck/GKR and efficient straight-line extraction/honest-verifier simulation, has a separate account.

## Sigma protocols and explicit extraction

[SigmaProtocol](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Basic.lean#L78) specifies an honest commitment PMF with private state, a deterministic response to a challenge, and Boolean verification. `Complete`, `SpecialSoundness` and `SpecialHVZK` express correctness, extraction from two accepting same-commitment/distinct-challenge transcripts, and exact simulation at each fixed challenge. The extractor may target a different relation, accommodating relaxed lattice witnesses. The generic interface has no native efficiency built in [cslib-frontier][complexitylib].

[SigmaProtocol/Efficient.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Efficient.lean) adds encodings and machine-backed extraction/simulation predicates (`EfficientSpecialSoundness`, `EfficientSpecialHVZK`). A simulator certificate compares a strict-PPT realization with an exact `SpecialHVZK` law using an explicit statistical error `δ : I → ℝ≥0∞`; `δ` is not constrained inside `EfficientSpecialHVZK` (`δ i ≥ 1` makes `SimulatorRealizedBy` vacuous), so security claims must state their concrete or `Negligible` bound on `δ` explicitly. These additions do not retroactively make every semantic Sigma instance efficient. Schnorr and Lyubashevsky clients exercise the interfaces; [SigmaProtocol/Lyubashevsky/NativeExtract.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/NativeExtract.lean) and [SigmaProtocol/Lyubashevsky/Efficient.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Efficient.lean) provide the serialized extractor, verifier (`EfficientVerifier`), strict-PPT integer-box samplers (`sampleIntBox`, `sampleIntBoxVec`, `sampleDyadicIntBox`), and non-abort simulator certificate (`EfficientNonAbortSpecialHVZK`).

[SigmaProtocol/Interactive.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean) embeds any `SigmaProtocol X Y T C Z` with `[Fintype C] [Nonempty C]` into the three-message public-coin specification `P.interactiveSpec` (`[.prover T (OracleInterface.full T), .verifier C, .prover Z (OracleInterface.full Z)]`) in [Computability/Interactive](interactive-reductions.md):

- **Protocol embedding ([toInteractiveVerifier](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L213), [toInteractiveProver](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L197), [toInteractiveReduction](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L226)):** `toInteractiveVerifier` samples a uniform challenge `c ∈ C` and accepts when `P.verify y t c z = true`. Given a `ProbComp` commitment realization `sampleCommit : X → Y → ProbComp (T × P.State)` satisfying `P.CommitRealizedBy sampleCommit`, `toInteractiveProver` and `toInteractiveReduction` realize the honest prover in `World.plain`, swapping `SigmaProtocol`'s witness-first relation `R : X → Y → Prop` to `Interactive`'s statement-first convention `Function.swap R : Y → X → Prop` with target relation `Interactive.Accept`.
- **Security and efficiency transfers ([Complete.toInteractiveReduction](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L285), [SpecialSoundness.rbrSound](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L342), [SpecialSoundness.sound](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L352), [SpecialSoundness.knowledgeSound](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L395), [SpecialHVZK.hvzk_zero](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L444), [EfficientSpecialHVZK.efficientHVZK](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean#L600)):** completeness transfers with error `0`; `SpecialSoundness` implies round-by-round soundness (`rbrState` holds at round 0 iff at least two challenges admit valid responses for `t`, at round 1 iff the chosen `c` admits a valid response, and at round 2 iff `P.verify y t c z = true`) and plain-model soundness with error `1 / (Fintype.card C : ℝ≥0∞)`, as well as straight-line `KnowledgeSound` via `P.witnessChooser R` (reflecting that one-shot straight-line extraction without rewinding cannot run a 2-transcript extractor); `SpecialHVZK` transfers to zero-error `Interactive.Reduction.HVZK`; and `EfficientSpecialHVZK` combined with a strict-PPT challenge sampler within `δC i` of uniform on `C i` yields `Interactive.Reduction.EfficientHVZK` with simulation error `0` and realization error `δC i + δ i`. Concrete commitment/simulator realizations and checked instances for `schnorr`, `PrimeOrderGroupFamily.schnorrFamily`, `andProof`, and `orProof` are in [SigmaProtocol/Interactive.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Interactive.lean) and [CslibFrontierTests/SigmaInteractiveBridge.lean](../../CslibFrontierTests/SigmaInteractiveBridge.lean).

When statistical simulation is too strong or callers interact through game indistinguishability, import `CslibFrontier.Crypto.Protocols.SigmaProtocol.Computational` ([SigmaProtocol/Computational.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean)), which formalizes Boneh and Shoup's Attack Game 20.4 and Definition 20.6 ([bs23][bs23], Section 20.4.2, p. 840):

- **Two-stage distinguishing game ([CHVZKAdversary](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L107), [chvzkRealGame](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L217), [chvzkSimGame](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L228)):** at security parameter `n`, `i ← setup n` is passed to `adversary.choose n i`, which outputs an encoded witness-statement candidate `(xw, yw)` and saved `state` word (`CHVZKAdversary.IsPPT` clocks `choose` on `(1^n, i)` and `guess` on `(1^n, state, conv)`). When `(xw, yw)` decodes via `encW i` and `enc.statement i` to a valid `(x, y)` in `R i`, `chvzkRealGame` runs `adversary.guess` on an honest encoded conversation while `chvzkSimGame` samples `c ← PMF.uniformOfFintype (C i)` and runs the simulator `sim (i, enc.statement i y, enc.challenge i c)` without `x`; invalid choices output `false` in both experiments so `R i` need not be efficiently decidable by the challenger.
- **Predicate and acceptance parameter ([ComputationalSpecialHVZK](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L243)):** bundles uniform strict PPT admissibility of `sim`, acceptance probability at least `1 - δ i` on every `(i, y, c)` (`δ = fun _ => 0` gives exact Definition 20.6 acceptance; non-zero `δ` accommodates strict fair-coin approximations of non-dyadic distributions), and `Game.Indistinguishable` against all strict-PPT `CHVZKAdversary` distinguishers.
- **Statistical-to-computational bridge and Schnorr instance:** [SimulatorRealizedBy.advantage_chvzkGame_le](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L326) bounds Attack Game 20.4 advantage against *arbitrary* (even unbounded) adversaries via `Game.advantage_bind_le_of_closeTo` ([Game/CloseTo.lean](../../CslibFrontier/Crypto/Game/CloseTo.lean#L134)), yielding [EfficientSpecialHVZK.exists_computationalSpecialHVZK](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L375) whenever `δ` is bounded along `setup` by a `Negligible` function and [SimulatorRealizedBy.computationalSpecialHVZK_of_accepts](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Computational.lean#L347) when exact acceptance holds separately. In [SchnorrProtocol.lean](../../CslibFrontier/Crypto/Computational/SchnorrProtocol.lean#L300), `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr` establishes `ComputationalSpecialHVZK` with exact zero acceptance error (`δ = fun _ => 0`) for any `setup : ℕ → PMF F.Desc`.
- **Two-sided separations ([CslibFrontierTests/ComputationalSpecialHVZK.lean](../../CslibFrontierTests/ComputationalSpecialHVZK.lean)):** `not_computationalSpecialHVZK_sendWitness` proves that the perfectly `SpecialHVZK` protocol `sendWitnessFamily F` fails `ComputationalSpecialHVZK` under `F.DiscreteLog setup` for *every* `sim` and *every* `δ` (without invoking `accepts`), while `computationalSpecialHVZK_prgWitnessSigma` and `exists_computationalSpecialHVZK_and_not_specialHVZK` construct from any stretching `PseudorandomGenerator` (or uniform `OneWay` function) a complete Sigma protocol family satisfying `ComputationalSpecialHVZK` with `δ = fun _ => 0` that fails `SpecialHVZK`, `EfficientSpecialHVZK` for every `δ`, and even unbounded statistical HVZK below error `1 / 4`.

Abort is observable in [CslibFrontier/Crypto/Protocols/SigmaProtocol/Abort.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean): accepted transcripts and conversations return `Option`, with `none` representing abort. `NonAbortSpecialHVZK` matches the accepted-transcript law including abort mass. Its `none` erases the commitment, so this does not simulate the full view of aborted signing queries. Nonabort completeness alone does not give a lower bound on success, an expected retry cost, or a strict-PPT rejection-sampling implementation; [SigmaProtocol/Lyubashevsky/Efficient.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Efficient.lean) supplies strict-PPT integer-box sampling (`sampleIntBox`, `sampleIntBoxVec`, `sampleIntBoxList`) with statistical distance at most `m * ((2 * B + 1) / 2 ^ width)` from `intBox (Fin m) B`, realizing `lyubashevskySimulate` under `EfficientNonAbortSpecialHVZK`. [SigmaProtocol/Lyubashevsky/Signature.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature.lean) adds the Fiat–Shamir-with-aborts signing and verification layer (`FiatShamirWithAborts`, `fsAbortSignAttempt`, `fsAbortSignBounded`, `fsAbortVerify`, and their Lyubashevsky specializations), proving completeness of non-aborting single and bounded `K`-attempt runs (`fsAbortVerify_of_fsAbortSignAttempt_eq_some`, `fsAbortVerify_of_fsAbortSignBounded_eq_some`), the exact `K`-retry abort law `(p_abort) ^ K` (`fsAbortSignBounded_apply_none`), direct-attack identification security for `lyubashevsky` against the relaxed `[A | T]` SIS relation (`lyubashevsky_succProbability_directAttack_le`), and the witness-invariance collision reduction (`isSISSolution_sub_smul_secret`, `extractSISFromRelaxedWitness`, `extractSISFromTwoTranscripts`, `lyubashevskyForkToSIS`, `lyubashevskySignatureForkToSIS`) that folds an extracted `[A | T]` kernel vector into a homogeneous `SIS.IsSolution` for `A` whenever the extracted response difference differs from the honest secret key's shift (exercised in [CslibFrontierTests/Crypto/LyubashevskySignature.lean](../../CslibFrontierTests/Crypto/LyubashevskySignature.lean)). Full random-oracle EUF-CMA game-hop bounds for aborting signers and strict-PPT computational reductions to `SIS` remain separate open obligations.

For the generic fixed-hash abort-signing API, import [SigmaProtocol/Abort/FiatShamir.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Abort/FiatShamir.lean). It provides `fsAbortSignStep`, `fsAbortSignAttempt`, `fsAbortSignBounded`, verification and their generic laws without importing the lattice application. The existing `Lyubashevsky.Signature` import publicly reexports these declarations with unchanged names.

For an executable bounded signer, import [Lyubashevsky/Signature/Efficient.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Efficient.lean). `lyubashevskySignBoundedNative` takes native integer matrix rows, message bits, the existing `LyubashevskyParams`, and a unary attempt budget. For a polynomial-time deterministic hash on encoded message/commitment pairs, `isPPTOn_lyubashevskySignBoundedNative` certifies uniform strict-PPT execution. Matrix entries, the modulus and radii use binary encodings; dimensions, sampling width and the attempt budget are unary. Short rows and challenge words have zero defaults. The program samples all attempts and returns the first success, charging storage for the entire list.

`closeTo_lyubashevskySignBoundedNative` compares the resulting law, including `none`, with the exact bounded signer at distance at most `K * m * (2γ + 1) / 2^width`. `lyubashevskySignBoundedNative_none_le` bounds failure by the exact single-attempt abort probability raised to `K`, plus this sampling error. Keep that exact probability when the hash depends on the commitment: the interactive fixed-challenge abort formula cannot simply be substituted. [The checked one-dimensional example](../../CslibFrontierTests/Crypto/LyubashevskySigning.lean) covers success, rejection, missing rows, challenge truncation, zero attempts and a two-attempt distance bound `10/64`. These are implementation and distribution guarantees for a deterministic hash; the full random-oracle security obligations remain open.


For an explicit schedule with negligible signing failure, import [Lyubashevsky/Signature/Parameters.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Parameters.lean). `lyubashevskySigningParams λ` uses `t = λ + 1`, dimensions `n = m = k = t`, secret-entry bound one, margin `β = t`, radius `γ = 4t²`, sampling width `λ`, modulus `2^t` and `t` attempts. The exponential modulus is encoded in binary. `isPPTOn_lyubashevskySigningParams` certifies the actual signer jointly in unary `λ` and the complete raw matrix/message input sizes, for a polynomial-time deterministic word hash.

The new [hash-uniform abort bound](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Failure.lean), `lyubashevskySignAttempt_none_le`, holds for every deterministic hash, including one that chooses its challenge from the commitment: if `2β ≤ γ`, `kη ≤ β` and the secret entries are bounded by `η`, exact single-attempt failure is at most `4mβ/(2γ+1)`. Under the schedule above this is at most one half. `lyubashevskySigningParams_failure_le` bounds actual native failure by `2^−(λ+1) + (λ+1)^2 * (8(λ+1)^2+1) / 2^λ`; `negligible_lyubashevskySigningParams_failure` proves it negligible for arbitrary bounded-secret, public-matrix and message sequences. The probability guarantee does not require short messages; the runtime theorem charges their actual lengths. [Checked examples](../../CslibFrontierTests/Crypto/LyubashevskySigningParameters.lean) include a commitment-dependent hash, nonzero bounded secrets, certainty of native failure at `λ=0`, and an upper bound below one percent at `λ=32`. This schedule demonstrates efficient availability, not SIS hardness or EUF-CMA security.

To discharge the nonzero-vector condition for a public-key-only fork, import [Lyubashevsky/Signature/Extraction.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Extraction.lean). Fix any `A` over `ZMod q` with `q ≠ 0`, draw the `k` secret columns independently and uniformly from `[-η,η]^m`, and let an arbitrary randomized kernel receive only `T = A*S` (with `A` fixed). `lyubashevsky_predict_difference_le` bounds the probability of distinct binary challenges satisfying `z-z' = S*(ĉ-ĉ')` by `k*q^n/(2η+1)^m`. The proof counts secret columns after their public images are revealed; it assumes neither entropy nor a simulator conclusion. The shared finite-leakage lemmas live in [Probability/Guessing/Leakage.lean](../../CslibFrontier/Probability/Guessing/Leakage.lean).

`lyubashevsky_fork_success_le_sis_add` then bounds the probability of two accepting responses at the same commitment and distinct challenges by the probability that the actual integer vector `z-z'-S*(ĉ-ĉ')` solves homogeneous SIS for `A`, with norm bound `2*(γ-β)+k*η`, plus this loss. Both probabilities use the same sampled-secret experiment. Its extraction uses `S`; the theorem alone is not an `A`-only native SIS reduction. [Checked clients](../../CslibFrontierTests/Crypto/LyubashevskyExtraction.lean) include a nonzero `1×8` matrix modulo 17 and a kernel that accepts with probability one and yields positive SIS success, empty challenges, and zero-radius secrets whose response differences can be predicted with certainty. Applying this bound to a real signature fork still requires proving the public-key-only distribution property while accounting for all aborted hash queries, and then providing efficient replay. Full random-oracle EUF-CMA remains open.

To compare two bounded secrets for the same public key, import [Lyubashevsky/Signature/View.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/View.lean). Under `k*η ≤ β ≤ γ` and `lyubashevskyRelation η` for both secrets, `lyubashevsky_transcript_eq` proves equality of the actual `(commitment, optional response)` law, including each aborted commitment. The proof combines the existing accepted-transcript equality with the actual secret-independent commitment marginal; [PMF/Option.lean](../../CslibFrontier/Probability/PMF/Option.lean) supplies the finite-mass cancellation. `lyubashevsky_attempt_view_eq` extends this to any common deterministic challenge function `c(w)` of the commitment. It does not allow that function to inspect the secret.

`lyubashevsky_sign_attempts_view_eq` compares histories of `K` independent exact attempts, retaining every hash input, challenge and optional response. These histories evaluate all `K` attempts. `lyubashevskySignBounded_eq_attempts_view` projects their first success to the existing bounded signer, and `lyubashevskySignBounded_witness_eq` proves equality of its output laws. [Checked examples](../../CslibFrontierTests/Crypto/LyubashevskyView.lean) use distinct bounded secrets for one nonzero public matrix, a commitment-dependent challenge, a nonzero aborted commitment with positive probability, and a successful response with positive probability. These independent-history laws alone do not describe an adaptive cache. The next result proves witness invariance for that shared-cache execution; efficient secret-free simulation and equality of paired forks using the same private coins remain open.

For signing through the shared memoizing random oracle, import [Lyubashevsky/Signature/RandomOracle.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/RandomOracle.lean). `lyubashevskyROMSignature` instantiates the existing `ROMSignature.Scheme` with the original key generator, exact independent masks and optional signatures. The wrapper uses the identity hash-point embedding: each oracle query is the typed pair `(message, commitment)`. All `K` attempts run, including after the first success; aborted hash inputs remain cached and repeated inputs reuse their digest. The result is the first successful signature, or `none`, which verification rejects. The canonical handler logs every signing request, including aborts, so final-message freshness counts those requested messages. The shared `fiatShamirAbort_sign_fixedHash` theorem recovers the existing bounded signer's output law for a fixed hash; `fiatShamirAbortSign_queryBound` counts at most `K` hash calls, without a runtime claim.

Under the same bounded-witness hypotheses, `lyubashevskyROMSignature_sign_run_eq` compares the actual joint signature/final-cache law from every common initial cache. A common public randomized challenge/state kernel preserves the full transcript law, and induction threads each updated cache through the next attempt. `lyubashevskyROMSignature_forger_run_eq` retains an adaptive forger's output, cache and queried-message log; `lyubashevskyROMSignature_worldRealize_eq` also covers a probabilistic forger and final verification in the canonical world with the same public key. [Checked cache examples](../../CslibFrontierTests/Crypto/LyubashevskyRandomOracle.lean) show positive probability of an aborted new query being retained, a later query reading that stored digest, and a success followed by another attempted hash input. These single-run equalities do not supply an efficient secret-free simulator, paired same-coins fork equality, a native shared-oracle runtime certificate, or full EUF-CMA security.

For average-key cache-hit bounds, import [Lyubashevsky/Commitment.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Commitment.lean). With prime modulus `q`, draw a uniform `n×m` matrix `A`, then an arbitrary randomized history `H(A)`, and only then a fresh uniform mask in `[-r,r]^m`. If `2r < q`, [HashFamily/IntegerBox.lean](../../CslibFrontier/Probability/HashFamily/IntegerBox.lean) bounds the joint law `(A,Ay)` against `(A,U)` by `εr = sqrt(q^n/(2r+1)^m)/2` in half-L1 distance. A history-selected cache of length at most `Q`, message and shift therefore give lookup probability at most `Q/q^n + εr`. The shift may depend on `A` and the history, but not on the fresh mask. This averages over the entire experiment, rather than conditioning on an arbitrary realized matrix or history.

`lyubashevsky_commit_lookup_le` applies this bound to the actual honest commitment with `r=γ`, including attempts whose responses later abort. `lyubashevskySimulate_lookup_le` bounds the existing simulator's published `Some` commitment with `r=γ−β`, assuming `β≤γ` and `2(γ−β)<q`; its bound is multiplied by the exact acceptance mass `((2(γ−β)+1)/(2γ+1))^m`. Its `None` erases the commitment, so this theorem does not justify removing aborted hash queries. [Checked clients](../../CslibFrontierTests/Crypto/LyubashevskyCommitment.lean) include a positive cache-hit probability below `0.06` at `q=17,n=1,m=8,γ=3,Q=1`, a supported zero matrix with conditional hit probability one, a nonzero matrix with positive hit probability, randomized matrix-dependent histories and shifts, empty caches, zero inner radius and zero output dimension. These original bounds use ideal uniform sampling for a supplied prime modulus; native sampling approximation and corrected full-view CMA simulation remain separate obligations. The earlier power-of-two availability schedule does not meet the prime-modulus hypothesis for positive security parameters and is not a security instantiation.

For one signing call's read-to-program hop, import [Lyubashevsky/Signature/Programming.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Programming.lean). `closeTo_lyubashevskySign_program` compares the actual all-`K` signer under memoized challenge reads with the same signer sampling a fresh uniform challenge and prepending its entry on every attempt. Both laws retain aborted entries and later cache effects after the first success. Their joint matrix, history, optional signature and complete final-cache laws are `CloseTo` with additive error `∑ j<K ((Q+j)/q^n + εγ)`, where `εγ = sqrt(q^n/(2γ+1)^m)/2`. The matrix is ideal uniform over a prime modulus, `2γ<q`, and the initial history is an arbitrary kernel of that matrix with cache length at most `Q`. The induction extends this history before each fresh mask, without conditioning the matrix on avoiding earlier collisions. Secret validity and response acceptance are not premises of this hop.

[Checked clients](../../CslibFrontierTests/Crypto/LyubashevskyProgramming.lean) cover zero attempts, exact one-attempt equality from an empty cache, a retained aborted commitment, and a supported repeated point whose second programmed digest can differ after the first successful response. The canonical scheme's two-attempt full laws satisfy a bound of `1/10` at `q=17,n=1,m=8,γ=3` from an empty cache. `CloseTo.bind_left` transports the result through any common continuation, and `CloseTo.symm` reverses it. This original finite-attempt bound may exceed one for other parameters. It is a one-call replacement, not a multiple-call adaptive reduction, an efficient secret-free simulator or a full signature-security theorem. Replacing programmed attempts by the erased-abort simulator remains a separate visible-law obligation: deleting aborted entries changes the complete cache law and must account for later oracle, verification and signing reads, together with the required abort-branch independence.

For visible signing simulation, import [Lyubashevsky/Signature/Simulation.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Signature/Simulation.lean). The single-attempt programmed signing hybrid `lyubashevskySignVisibleProg` programs the random oracle cache by drawing a fresh challenge and prepending `(message, commitment) ↦ challenge` even on an abort and even if that key was already present, while the simulated process `lyubashevskySignVisibleSim` (`lyubashevskySimulate`) adds hash cache entries only for accepted transcripts using `lyubashevskySimCache`. The actual memoizing transport from honest signing (`Sign → Prog`) that reuses cached challenges remains a separate obligation. Under prime modulus `q`, `2γ < q`, and valid secret witness `k*η ≤ β ≤ γ`, `closeTo_lyubashevskySign_simulate` bounds their statistical distance under any visible continuation `cont(A, h, sig)` making at most `R` later oracle reads: the distance on `(A, h, continuation output)` is at most `R / q^n + sqrt(q^n / (2γ + 1)^m) / 2`. The visible experiments factor through the full executions (`lyubashevskySignFullProg`, `lyubashevskySignFullSim`) via `lyubashevskySignVisibleProg_eq_bind_full` and `lyubashevskySignVisibleSim_eq_bind_full`, project their non-cache outputs for pure identity continuations (`lyubashevskySignVisibleProg_eq_map_full`, `lyubashevskySignVisibleSim_eq_map_full`), and agree identically whenever the continuation makes zero oracle queries (`lyubashevskySignVisibleProg_eq_sim_of_pure`). The simulation proof combines input-dependent continuation bounds (`CloseTo.bind_right_tsum`), the matrix leftover-hash commitment hit bound for the counterfactual abort continuation (`counterfactual_hit_le`), and exact equality of the accepted-transcript hybrid with `lyubashevskySimulate` via `lyubashevsky_nonAbortSpecialHVZK`. For `K`-attempt signing, `lyubashevskySimAttempts`, `lyubashevskySignAttemptsVisibleProg`, and `lyubashevskySignAttemptsVisibleSim` define the secret-free stopping simulator and the visible programmed and simulated experiments (imposing query bounds on the theorems rather than the definitions). Only the `K ≤ 1` reductions to the single-attempt bridge are proved so far: `lyubashevskySignAttemptsVisibleProg_zero_eq_sim` gives exact equality for `K = 0`, while `closeTo_lyubashevskySignAttempts_simulate_one`, `closeTo_lyubashevskySignAttempts_simulate_le_one`, `lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_one`, and `lyubashevskySignAttemptsVisibleProg_eq_sim_of_pure_le_one` case-split `K ≤ 1` back to the `K = 0` identity and the single-attempt theorems (for `K = 1` the `Finset.range K` sum reduces to `R / q^n + sqrt(q^n / (2γ + 1)^m) / 2`); the `K ≥ 2` visible simulation induction ([#2798](https://github.com/cslib-community/cslib-frontier/issues/2798)) remains open. [Checked clients](../../CslibFrontierTests/Crypto/LyubashevskySimulation.lean) cover zero-reads continuations, provably disjoint queries (`(true, 0) ≠ (false, coin.1)`, with both `avoid_closeTo` and exact `avoid_visible_eq` via `avoid_key_disjoint` and `avoid_miss_cache`), accepted-commitment queries (`hit_closeTo` and exact `hit_visible_eq` via `hit_returns_c`), an actual final-verifier client checking signature validity (`R = 1`), the `q=17, n=1, m=2, γ=3, β=1, S=0` counterexample (`progExp_cache_length_eq_one`, `simCache_length_zero_on_abort`, and empty-cache probabilities `0` for `progExp` versus `1 - (5/7)^2 = 24/49` for `simExp` despite equal visible marginals), and the `K = 0`, `K = 1`, and `K ≤ 1` reduction checks.

Identification and Fiat–Shamir add adversarial interaction to this same transcript model. Their security is not merely the existence of a mathematical witness extractor: the computational instances require an encoded efficient extractor, and finite quantitative transformations explicitly track replay and calls. For Schnorr identification over a `PrimeOrderGroupFamily`, [`SchnorrIdentification.lean`](../../CslibFrontier/Crypto/Computational/SchnorrIdentification.lean) formalizes the direct impersonation game (`schnorrDirectGame`) and the rewinding discrete-logarithm extractor (`SchnorrImpersonator.rewind`, `succProbability_schnorrDirectGame_le`, `negligible_schnorrDirectGame`), while [`SchnorrEavesdrop.lean`](../../CslibFrontier/Crypto/Computational/SchnorrEavesdrop.lean) adds eavesdropping security (`SchnorrEavesdropAdversary`, `schnorrEavesdropGame`, `schnorrIdealEavesdropGame`, `IsEavesdropSecure`, `IsIdealEavesdropSecure`; [bs23][bs23], Attack Game 18.2 and Theorems 19.3 and 19.5): because strict-PPT exponent sampling `sampleExp n d` (`ProbComp.sampleModNat`) has statistical distance at most `1 / 2 ^ n` from uniform on `ZMod q`, `Q n` simulated conversations (`schnorrSimulatedTranscript`) are within statistical distance `Q n / 2 ^ n` of ideal honest conversations (`schnorrHonestTranscript`) and within `2 * Q n / 2 ^ n` of strict-PPT honest conversations (`schnorrRealTranscript`), reducing any uniform strict-PPT eavesdropper via `SchnorrEavesdropAdversary.toDirect` to `schnorrDirectGame` and hence to `DiscreteLog` (`succProbability_schnorrEavesdropGame_le`, `negligible_schnorrEavesdropGame`, `schnorr_isEavesdropSecure_of_discreteLogHard`; checked on the order-`11` Schnorr group in `(ZMod 23)ˣ` in [`CslibFrontierTests/Crypto/SchnorrDiscreteLog.lean`](../../CslibFrontierTests/Crypto/SchnorrDiscreteLog.lean)).

## VOLE ideal functionality, IT-MACs, and VOLE-in-the-head

Import `CslibFrontier.Crypto.Protocols.VOLE.Basic` ([VOLE/Basic.lean](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean)) for Vector Oblivious Linear Evaluation (VOLE) correlations, information-theoretic MACs (IT-MACs), and the linear VOLE-in-the-head Sigma protocol ([BoyleCGIKS2019]; [BaumBMRS2023]):

- **Ideal VOLE correlation ([VOLECorrelation](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L110), [voleSample](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L147), [voleIdealDist](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L175)):** over a commutative ring `R` and vector length `n`, the sender holds `(u, v) : (Fin n → R) × (Fin n → R)` and the receiver holds a global scalar key `delta : R` and tag vector `w : Fin n → R` satisfying `VOLECorrelation.Valid : ∀ i, w i = u i * delta + v i`. `voleIdealDist R n` samples `u, v` and `delta` uniformly and independently, with support characterized by `mem_support_voleIdealDist_iff` (`valid_of_mem_support_voleIdealDist`).
- **Linear homomorphism and witness commitment ([VOLECorrelation.Valid.add](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L241), [VOLECorrelation.Valid.linearComb](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L263), [voleCommitWitness](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L279), [voleAdjustReceiver](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L284)):** IT-MACs are closed under componentwise addition (`add`), public scalar multiplication (`smul`), public constant shifts (`addConst`), and public linear combinations (`Valid.linearComb`). Committing to a witness `x : Fin n → R` via the correction message `voleCommitWitness x u = x - u` and receiver tag update `voleAdjustReceiver w d delta` yields valid tags for `x` (`voleAdjustReceiver_voleCommitWitness`) while `voleCommitWitness_uniform` and `voleCommitWitness_indep` establish uniformity and witness-independence of the correction-message marginal under a uniform VOLE mask `u`.
- **IT-MAC unforgeability and degree-2 multiplication check ([voleOpen_unique_delta_of_ne](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L361), [toOuterMeasure_voleVerifyOpening_le](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L406), [voleMulCheck](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L457)):** over a field `F`, any forged opening `x' ≠ x` satisfies `voleVerifyOpening` for at most one global key `delta = (v' i - v i) / (x i - x' i)` (`card_filter_voleVerifyOpening_le_one`), bounding the cheating acceptance probability under uniform `delta` by `(Fintype.card F)⁻¹`. For authenticated wires `w_x, w_y, w_z`, `voleMulCheck_sub_eq` decomposes `w_x * w_y - w_z * delta` into `(x * y - z) * delta ^ 2` plus the affine-linear check `voleMulCrossTerm x v_x y v_y v_z * delta + voleMulConstTerm v_x v_y`, which holds iff `x * y = z` at any `delta ≠ 0` (`voleMulCheck_iff_of_ne_zero`).
- **Dishonest multiplication claims:** import `CslibFrontier.Crypto.Protocols.VOLE.MulCheck` ([MulCheck.lean](../../CslibFrontier/Crypto/Protocols/VOLE/MulCheck.lean)) when the sender may claim arbitrary affine coefficients `a`, `b`. Apply `toOuterMeasure_voleMulCheck_le` to a false gate `x * y ≠ z`: the check `(x * delta + v_x) * (y * delta + v_y) - (z * delta + v_z) * delta = a * delta + b` holds with probability at most `2 / |F|` under a uniform secret key. For a randomized sender, use `toOuterMeasure_voleMulCheck_bind_le` with its `PMF S` state distribution and eight functions supplying values, masks, and coefficients. The experiment samples the state before an independent key; it does not allow the claim to depend on the receiver's key or tags. The bad event includes the false gate, so the sender distribution needs no support hypothesis. This is a single-constraint information-theoretic bound, not full VOLE-based ZK or VOLE-in-the-head security, and gives no runtime certificate. The bound is sharp over `ZMod 5`; over `ZMod 2` a false claim can pass for every key. See the complete honest, sharp, randomized-sender, and key-dependence examples in [VOLEMulCheck.lean](../../CslibFrontierTests/Crypto/VOLEMulCheck.lean). From the repository root, check them with `scripts/build.sh CslibFrontierTests.Crypto.VOLEMulCheck`; successful completion confirms the examples elaborate.
- **IT-MACs and multiplication checks over `ZMod n`:** import `CslibFrontier.Crypto.Protocols.VOLE.RingMAC` ([RingMAC.lean](../../CslibFrontier/Crypto/Protocols/VOLE/RingMAC.lean)) and `CslibFrontier.Crypto.Protocols.VOLE.RingMulCheck` ([RingMulCheck.lean](../../CslibFrontier/Crypto/Protocols/VOLE/RingMulCheck.lean)) when the IT-MAC ring is `ZMod n` rather than a field, as for the Damgård–Jurik plaintext ring `ZMod (N ^ ζ)` of [HazayYang2024]. `ZMod.card_filter_eval_eq_zero_le` ([PolynomialRoots.lean](../../CslibFrontier/Foundations/Data/ZMod/PolynomialRoots.lean)) bounds the roots of a nonzero `f : (ZMod n)[X]` by `f.natDegree * (n / n.minFac)`. Its degree-one and degree-two cases give `toOuterMeasure_voleVerifyOpening_le_minFac` (a forged opening `x' ≠ x` passes a uniform key with probability at most `1 / n.minFac`) and `card_filter_quadratic_eq_zero_le`; `card_filter_mac_ringMacGap` and `card_filter_quadratic_ringMacGap` show both bounds are attained for every `n > 1`, and `Nat.minFac_mul_pow` evaluates `n.minFac` to `p` for `n = (p * q) ^ ζ` with primes `p < q`; `toOuterMeasure_voleVerifyOpening_le_inv_prime` and `card_filter_quadratic_eq_zero_le_mul_pow` state the paper's forms `1 / p` and `2 * p ^ (ζ - 1) * q ^ ζ`. The masked check `RingMulCheckAccepts` uses one extra authenticated random value: `ringMulCheck_complete` holds over every commutative ring, `ringMulCheckView_eq_simulate` shows the verifier's view `(k_r, c₁, c₀)` under a uniform mask is simulated from the keys alone for every key, and `toOuterMeasure_ringMulCheck_le` and `toOuterMeasure_ringMulCheck_bind_le` bound a false product by `2 / n.minFac` against a fixed or randomized prover that never sees the key. These are single-check information-theoretic statements; they are not security of the protocols of [HazayYang2024]. Run `scripts/build.sh CslibFrontierTests.Crypto.VOLERing` to check the [examples](../../CslibFrontierTests/Crypto/VOLERing.lean) at `n = 225`, where both bounds are attained.
- **Batched multiplication claims:** import `CslibFrontier.Crypto.Protocols.VOLE.BatchMulCheck` ([BatchMulCheck.lean](../../CslibFrontier/Crypto/Protocols/VOLE/BatchMulCheck.lean)). `voleMulCheck_sum` gives honest completeness for every weight vector and key. For a fixed false batch, `toOuterMeasure_voleMulCheck_batch_le` allows the sender's randomized affine reply to depend on a public uniformly sampled vector of weights. The key remains independent and hidden. The bound is `1 / |F| + (1 - 1 / |F|) * (2 / |F|)`: the first term is cancellation of the nonzero residual vector; otherwise at most two keys accept. `toOuterMeasure_voleMulCheck_batch_bind_le` also samples arbitrary sender state before the weights, with a false constraint included in the bad event. Its `..._three_div` corollary gives `3 / |F|`. The challenge contains one independent field element per constraint and the reply two; these statements are ideal algebraic bounds, not the scalar-challenge QuickSilver protocol, ZK, VOLE-in-the-head security or runtime certificates. An empty batch has no false-constraint event, while over `ZMod 2` the sharp bound is one. The [checked examples](../../CslibFrontierTests/Crypto/VOLEBatchMulCheck.lean) include deterministic cancellation, exact `13 / 25` acceptance for an adaptive two-gate claim over `ZMod 5`, and randomized state and replies. From the repository root, run `scripts/build.sh CslibFrontierTests.Crypto.VOLEBatchMulCheck`; a successful build checks those examples. The earlier key-dependent counterexample in [VOLEMulCheck.lean](../../CslibFrontierTests/Crypto/VOLEMulCheck.lean) still explains why revealing the receiver key before the reply is outside the model.
- **Full honest receiver-view simulation:** import `CslibFrontier.Crypto.Protocols.VOLE.MaskedMulCheck` ([MaskedMulCheck.lean](../../CslibFrontier/Crypto/Protocols/VOLE/MaskedMulCheck.lean)). `maskedMulCheck left right output` is an actual three-round `Reduction` for public gate-index maps into a witness vector. The [cached `voleWorld`](../../CslibFrontier/Crypto/Protocols/VOLE/World.lean) samples one ideal correlation of length `n + 1`; separate oracle interfaces give the sender only its two vectors and the receiver only its key and tags. The final coordinate is a fresh affine mask. The prover sends all `n` corrections, receives one independent public weight per gate, then sends the two blinded coefficients. `maskedMulCheck_complete` proves completeness in this world. For every satisfying wire assignment, `maskedMulCheckView_eq_simulate` equates the complete receiver view—private key and raw tags, corrections, weights and reply—with the witness-free `maskedMulCheckSimulate`. The simulator samples a uniform key, tags, corrections, weights and slope, then solves the verification equation for the constant coefficient. `maskedMulCheckView_closeTo_simulate` gives zero-error closeness. The honest-view law works over finite commutative rings, including zero keys; it does not strengthen the preceding field-dependent soundness bounds. This adapts the fresh-mask step of [FAEST v1.0, §2.3.2, pp.12–13](https://faest.info/faest-spec-v1.0.pdf) to full-field wires and vector weights. It covers one honest execution with a fresh mask, not mask reuse, malicious-verifier ZK, scalar-challenge QuickSilver, VOLE-in-the-head security or certified efficiency. Run `scripts/build.sh CslibFrontierTests.Crypto.VOLEMaskedMulCheck` to check [clients](../../CslibFrontierTests/Crypto/VOLEMaskedMulCheck.lean) covering shared wires, distinct true witnesses, false-witness failure, an unblinded distinguisher, cache stability, zero keys, F2 and empty batches.
- **Adaptive receiver views in the ideal world:** import `CslibFrontier.Crypto.Protocols.VOLE.AdaptiveMulCheck` ([source](../../CslibFrontier/Crypto/Protocols/VOLE/AdaptiveMulCheck.lean)). `maskedMulCheckReceiverView_eq_simulate` permits any role-local `ProbOracleComp` program returning a `VerifierStrategy`, with arbitrary auxiliary input fixed before fresh setup. The receiver may read its private key/tags, sample coins, choose vector weights from those values and the corrections, and retain a continuation that processes the reply and queries the same cache again. The actual `World`/`runAgainst` view includes the receiver share, full transcript and arbitrary returned view. `maskedMulCheckReceiverSimulate` runs the same initialization and captured continuations; it samples uniform corrections before the receiver chooses weights, then a uniform slope and the corresponding constant coefficient. The proof first reparametrizes setup before the adaptive challenge, leaving the fresh mask independent of the visible prefix. `voleWorld_cached_run` preserves the full cache and client outputs through arbitrary randomized queries. The law holds for satisfying witnesses over finite commutative rings. It covers one fixed correction/challenge/reply schedule with trusted uniform setup and a fresh mask; it does not certify runtime, adversarial setup, resets, concurrent sessions, early-abort schedules, mask reuse or full VOLE-in-the-head security. The [checked clients](../../CslibFrontierTests/Crypto/VOLEAdaptiveMulCheck.lean) exercise private-key/tag/correction-dependent weights, a retained private coin with zero/adaptive branches and post-reply queries, F2, zero-divisor rings, empty gates, and an actual false-witness distribution inequality. From the repository root, run `scripts/build.sh CslibFrontierTests.Crypto.VOLEAdaptiveMulCheck`; success checks these clients and the earlier unmasked negative example. This is an original semantic extension of the preceding FAEST masking adaptation, with no new ZK predicate.
- **Native simulator with certified runtime:** import `CslibFrontier.Crypto.Protocols.VOLE.NativePPT` ([source](../../CslibFrontier/Crypto/Protocols/VOLE/NativePPT.lean)). `Native.simulate` is an actual witness-free `ProbComp` program on a supplied encoded public-input carrier. A layout map extracts the unary wire count and binary-index gate triples. `Native.Receiver` is parameterized by that input and its first-message carrier, with four explicit-state callbacks: initialization, adaptive weight selection, reply processing and termination. `Receiver.strategy` adapts them to the existing role-local strategy and reads the same cached receiver share in every phase. `Receiver.mapFirst` preprocesses only the challenge callback using the full input, receiver share and raw corrections. `receiverView_eq_eval_simulate` ties the actual layout to the finite wire maps and proves equality with the raw correction-based ideal-world view for satisfying witnesses. An arbitrary share-dependent first-message map does not assert that a sender can transmit that message; a downstream protocol must prove its own reconstruction law. `isPPTOn_simulate` charges the full input in all four callbacks, layout extraction, first-message conversion, sampler, scalar operations, retained state and full output. Fixing a different receiver closure for every circuit would not establish uniform runtime in the circuit. The ring and scalar encoding are fixed; an actual exact-uniform scalar sampler and strict-PPT certificate are required separately. Arbitrary finite uniform sampling does not follow from finiteness in the strict fair-coin model. The program pads missing weights with zero and discards excess weights; its runtime certificate also covers malformed gate indices through bounded list lookup. The [F2 clients](../../CslibFrontierTests/Crypto/VOLENative.lean) instantiate every runtime premise, retain a private coin and cached share, vary batch size, and test empty batches, huge binary indices and false-witness failure. The extended input client retains an arbitrary extra word, changes its chosen weight when that word changes, and preserves the converted first message through cached-share reads. From the repository root, run `scripts/build.sh CslibFrontierTests.Crypto.VOLENative`. This certifies the supplied encoded-state callbacks, not all higher-order strategies. Growing extension fields, full native circuit prover/verifier execution, raw-bit adversarial transport (#2744), adversarial setup, resets, mask reuse and full VOLE-in-the-head security remain separate.
- **Public circuit statements in the ideal VOLE world:** import `CslibFrontier.Crypto.Protocols.VOLE.CircuitSound` ([soundness](../../CslibFrontier/Crypto/Protocols/VOLE/CircuitSound.lean)) and `CslibFrontier.Crypto.Protocols.VOLE.CircuitPrivacy` ([privacy](../../CslibFrontier/Crypto/Protocols/VOLE/CircuitPrivacy.lean)). For the existing `Circuit (arithSignature F)` model, `circuitCheck` authenticates public inputs, addition/constant gates and designated outputs alongside the multiplication batch. Corrections and linear openings are sent together before the weights. `circuitCheck_sound` proves the existing `Verifier.Sound` predicate for the public language `∃ w, C.eval (x ++ w) = y`, against every sender-local strategy with arbitrary initialization, private coins and repeated setup reads. `circuitCheck_eval_execute` justifies delaying the independent hidden key until after the adaptive reply. A failed linear row has error at most `1 / |F|`; otherwise a false public statement forces a failed multiplication gate. This case split retains the batch mixture bound, giving `5/8` over the fixed four-element field. Completeness and `circuitReceiverView_eq_simulate` hold over finite commutative rings: for a satisfying trace, the receiver reconstructs linear openings from its own share, corrections and public targets, then reuses the existing adaptive simulator while retaining its entire transcript and terminal state. The actual sender uses only its two vectors. This is an original circuit-binding construction in the trusted fresh ideal world, with no new circuit or ZK predicate. Run `scripts/build.sh CslibFrontierTests.Crypto.VOLECircuit` to check [clients](../../CslibFrontierTests/Crypto/VOLECircuit.lean) covering false public output despite correct internal multiplication, addition-only failure, constants, repeated wires and outputs, private-coin strategies, zero-divisor privacy, empty circuits and a false-statement distribution inequality. Fresh-session amplification, a complete native circuit prover/verifier certificate, adversarial setup, resets, concurrency and full VOLE-in-the-head security remain open under #643.
- **Linear VOLE-in-the-head (`SigmaProtocol`):** [voleInTheHeadSigma](../../CslibFrontier/Crypto/Protocols/VOLE/Basic.lean#L499) packages the three-move protocol in which the prover commits to the aggregate MAC mask `t = ψ y v`, receives the verifier challenge `c` (determining `Δ = ι c`), and responds with the in-the-head VOLE receiver tags `(voleSample x v (ι c)).w`, with `voleInTheHeadSigma_complete`, `voleInTheHeadSigma_specialSoundness` (for prime `q`), and `voleInTheHeadSigma_specialHVZK`. Active two-party VOLE generation and multi-gate circuit compilation remain outside this module; checked finite-field examples are in [CslibFrontierTests/Crypto/VOLE.lean](../../CslibFrontierTests/Crypto/VOLE.lean).

## Kilian: honest payload and verifier input accounting

Import `CslibFrontier.Crypto.Computational.Kilian.Succinct` to bound an honest
transcript for a PCP verifier `V`. The
[accounting API](../../CslibFrontier/Crypto/Computational/Kilian/Succinct.lean)
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
[`computableInPolyTime_kilianVerify`](../../CslibFrontier/Crypto/Computational/Kilian.lean)
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

For the NP endpoint, import `CslibFrontier.Crypto.Computational.Kilian.NP` and use
[`exists_kilianSound_of_mem_NP`](../../CslibFrontier/Crypto/Computational/Kilian/NP.lean).
It combines the collision-resistant `HashFamily` assumption with a PCP-theorem
verifier and a uniform honest-payload bound. Its honest witnesses are accepted
compact PCP tables. It does not supply an efficient conversion from witnesses
of an arbitrary given NP relation to those tables; that remaining part of the
broader argument-system objective is explicit in the source.

The complete checked client
[`CslibFrontierTests/Crypto/KilianSuccinct.lean`](../../CslibFrontierTests/Crypto/KilianSuccinct.lean)
includes the import, one-bit/one-query verifier, digest-length proof and bound
application. At `n = 2` its honest transcript has exactly **12 payload bits**,
attaining the generic bound. Its constant hash exercises accounting only;
it is not a collision-resistance example.

For Micali's non-interactive random-oracle compilation of Kilian's protocol,
import `CslibFrontier.Crypto.Computational.Kilian.Micali`
([`Kilian/Micali.lean`](../../CslibFrontier/Crypto/Computational/Kilian/Micali.lean)).
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
in [`CslibFrontierTests/Crypto/Micali.lean`](../../CslibFrontierTests/Crypto/Micali.lean)).

In the random-oracle model, [`CslibFrontier/Crypto/Computational/MerkleTree/ROMExtract.lean`](../../CslibFrontier/Crypto/Computational/MerkleTree/ROMExtract.lean) replaces two-transcript rewinding with straight-line extraction from a recorded hash query-answer trace `tr : List (List Bool × List Bool)` ([bcs16][bcs16]; Chiesa–Yogev Construction 18.5.3 and Lemma 18.5.7): `findPreimageInTrace` inverts `encPair encBits encBits` via `(unframe, dropFrame)`, `extractNodeFromTrace` and `extractLeafFromTrace` walk `d` levels down from the Merkle root `rt` along the bits of position `i`, and `extractTableFromTrace` reconstructs all `2 ^ d` leaves. When `tr` is collision-free (`TraceCollisionFree tr`) and records every hash step along a valid opening (`PathQueriedInTrace H k tr i leaf path` and `merkleVerify H k d rt i leaf path = true`), `extractLeafFromTrace_eq_some_of_merkleVerify` and `getD_extractTableFromTrace_eq_of_merkleVerify` prove that the extracted leaf and table entry equal `leaf`; conversely, when `tr` is consistent with `H k` (`TraceConsistentWith (H k) tr`) and an accepted queried opening disagrees with `extractLeafFromTrace`, `extractTraceCollision` deterministically extracts a hash collision in `tr` (`extractTraceCollision_spec`, `isCollision_extractTraceCollision`). For a lazy uniform `m`-bit random oracle `memoize (fun _ => BitString.uniformList m)`, `toOuterMeasure_uniformList_mem_list_le`, `toOuterMeasure_memoize_not_traceCollisionFree_step` and `toOuterMeasure_run_memoize_not_traceCollisionFree_le` bound the preimage-hitting probability and the `Q * (Q * (1 / 2 ^ m))` collision probability of any `IsQueryBounded program Q` computation; executable checks are in [`CslibFrontierTests/Crypto/ROMMerkleExtract.lean`](../../CslibFrontierTests/Crypto/ROMMerkleExtract.lean).

[`CslibFrontier/Crypto/Computational/Kilian/MicaliSoundness.lean`](../../CslibFrontier/Crypto/Computational/Kilian/MicaliSoundness.lean) combines straight-line Merkle extraction with Fiat–Shamir challenge analysis to prove soundness for an unsalted, two-channel Micali variant in the random-oracle model (Micali 2000; compare Chiesa–Yogev Construction 21.1.1 and Theorem 21.2.1, March 25, 2026 version, pp. 239–242):

- **Fixed-trace soundness and dual collision extraction:** `micaliExtractCompactTable` and `micaliExtractProof` reconstruct the candidate PCP proof from `extractTableFromTrace tr (kilianDepth V x) rt []`. Under `AllOpeningsQueriedInTrace`, `kilianVerify_sound_of_traceCollisionFree` and `micaliVerifyPure_sound_of_traceCollisionFree` show that a collision-free trace forces `V.accepts x (micaliExtractProof V tr x proof.root) ρ = true` on every `V.coins x`-bit challenge in `hFS (x, proof.root)` (`not_traceCollisionFree_or_accepts_of_micaliVerifyPure`), while `exists_collision_of_micaliVerifyPure_of_rejects` deterministically extracts a hash collision in `tr` whenever `V` rejects the extracted proof.
- **Fiat–Shamir challenge union bound and adaptive two-channel ROM soundness:** for a PCP verifier with per-repetition soundness error `≤ 1 / 2` (`2 * acceptCount ... ≤ 2 ^ V.coins x` for `x ∉ L`), `toOuterMeasure_kilianChallenges_accepts_le`, `toOuterMeasure_run_memoize_not_fsTraceSound_le` and `toOuterMeasure_twoStageMicali_le` establish the `(t_FS + 1) * (1 / 2) ^ m` Fiat–Shamir union bound and the two-stage ROM bound. For fully adaptive cheating provers `P : OracleComp (MicaliSpec α) (α × MicaliProof)` that interleave Merkle (`Sum.inl`) and Fiat–Shamir (`Sum.inr`) queries, `micaliExtractProof_cons_of_ne` proves that a fresh Merkle query avoiding root/child digests of `tr_FS` and `tr_MT` leaves `micaliExtractProof` invariant, [`OracleComp.toOuterMeasure_bad_le_two`](../../CslibFrontier/Languages/Probabilistic/UntilBad/TwoCost.lean) generalizes `OracleComp.toOuterMeasure_bad_le` to two-channel cost budgets (`micaliMTCost`, `micaliFSCost`), and `micaliSoundness_bound` (together with `micaliSoundness_bound_of_prover_verifier`) proves `micaliSoundnessGame V L P σ m true ≤ (t_FS + 1) * (1 / 2) ^ m + Q_MT * ((3 * Q_MT + (t_FS + 1)) * (1 / 2 ^ σ))`.
- **Succinctness and `NP` CS-proof corollary:** `micaliProofBits_micaliProvePure_le` and `micaliProofBits_micaliProvePure_le_log` bound the honest proof bit length `micaliProofBits`, and `exists_micaliCSProof_of_mem_NP` combines the PCP theorem (`NP_subset_PCP_log`) with `micaliHonestGame_eq_pure_true`, `micaliSoundness_bound` and `micaliProofBits_micaliProvePure_le_log` for any `L ∈ NP enc` (with `V.tableVerifier` as the honest PCP table relation). Checked examples are in [`CslibFrontierTests/Crypto/MicaliSoundness.lean`](../../CslibFrontierTests/Crypto/MicaliSoundness.lean).

To apply the separate-budget corollary, bound verifier Merkle queries only for
`(x, proof) ∈ P.support`; `IsCostBounded.bind_on_support` then adds that bound to the prover's.
A uniform verifier bound over arbitrary proofs is generally unavailable: verification hashes an
authentication path before checking its length. The concrete adaptive client in the
[Micali soundness tests](../../CslibFrontierTests/Crypto/MicaliSoundness.lean) proves its total bound
of four Merkle calls (two prover calls and at most two verifier calls), so both soundness clients
have a discharged budget rather than a budget assumption. The main total-execution-budget
statement is unchanged.

The cited textbook construction includes privacy parameters and a Fiat–Shamir salt. This variant
uses `(x, root)` queries and a different explicit extraction-error expression. Its compact PCP
table witnesses and payload-size guarantee do not supply arbitrary NP-witness conversion or
native verifier runtime/truncation certificates.

## The BCS transform: public-coin IOPs to non-interactive arguments

Import `CslibFrontier.Crypto.Protocols.BCS.Basic`
([`BCS/Basic.lean`](../../CslibFrontier/Crypto/Protocols/BCS/Basic.lean)) for the
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
  [`CslibFrontierTests/Crypto/BCSTransform.lean`](../../CslibFrontierTests/Crypto/BCSTransform.lean).

For unconditional random-oracle soundness and straight-line knowledge extraction, import
`CslibFrontier.Crypto.Protocols.BCS.ROM` ([`BCS/ROM.lean`](../../CslibFrontier/Crypto/Protocols/BCS/ROM.lean)),
which lifts the multi-round BCS transform to an explicit two-channel random-oracle model
([bcs16][bcs16]; compare Chiesa–Yogev Construction 25.1.1, Remark 25.1.3, and Theorem 25.2.1,
March 25, 2026 version, pp. 274–278, Theorem 26.1.1 and Construction 26.1.3, pp. 288–289, Chapter
31 Definitions 31.1.1–31.1.2, Definition 31.1.6, Theorem 31.2.1, and Theorem 31.3.1, and Merkle
trace extraction from Construction 18.5.3 and Lemma 18.5.7, pp. 199 and 207):

- **Two-channel BCS random-oracle execution and completeness:** over
  `BCSROMSpec Stmt Chal := MerkleHashSpec ⊕ₒ BCSFSSpec Stmt Chal` (reusing `MerkleHashSpec`,
  `merkleRootProg`, `merklePathProg`, and `merkleVerifyProg` from
  [`Kilian/Micali.lean`](../../CslibFrontier/Crypto/Computational/Kilian/Micali.lean)), the left
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
  [`OracleComp.toOuterMeasure_bad_le_two_budgets`](../../CslibFrontier/Languages/Probabilistic/UntilBad/TwoCost.lean),
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
  Fiat–Shamir queries, are in [`CslibFrontierTests/Crypto/BCSROM.lean`](../../CslibFrontierTests/Crypto/BCSROM.lean).

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

[CslibFrontier/Crypto/Protocols/Signature/RandomOracle.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Signature/RandomOracle.lean) defines a typed random-oracle signature experiment. Signer, verifier and forger share one lazy hash cache. The forger's coins are drawn explicitly before deterministic oracle interaction, enabling replay. Signing and hash queries have separate bounds. Key generation can be an arbitrary PMF, so this finite experiment is not identical to the native `SignatureScheme` interface.

[CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamir.lean](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamir.lean) hashes `(message, commitment)` to the challenge and proves correctness and a quantitative EUF-CMA bound using special soundness, special HVZK, commitment unpredictability and the generic forking lemma. The bound includes signing/programming collisions, challenge guessing and the square-root forking term. It is a finite exact-security reduction; an asymptotic machine claim additionally needs the encoded efficiency bridges. The module cites Bellare–Neven and Boneh–Shoup and labels its comparison with their constants [bs23][bs23]. Over a `PrimeOrderGroupFamily`,
[`CslibFrontier/Crypto/Computational/SchnorrSignature.lean`](../../CslibFrontier/Crypto/Computational/SchnorrSignature.lean)
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
[#2568](https://github.com/cslib-community/cslib-frontier/issues/2568).

The existing `fiatShamir` and its finite security theorem accept an injective
`hashPoint : (M × T) ↪ Query`. Signing and final verification query `hashPoint (m, t)`, while
arbitrary other `Query` values remain in the same cache and count toward the hash-query budget.
The original clients use the identity embedding. The proof uses injectivity to recover the same
message and commitment at a successful fork; it requires no image-membership test or decoder.
This representation generalization ([#2684](https://github.com/cslib-community/cslib-frontier/issues/2684))
preserves the quantitative bound. It does not certify a native implementation of `hashPoint` or
complete the concrete word Schnorr reduction and its key-generation/signing approximation hops.

`FiatShamir.reduction` now takes an explicit `fallback` output for a failed fork. The existing
quantitative theorem holds for every such value, with no requirement that it satisfy the witness
relation. The Schnorr reduction wrappers use zero. This removes the hidden choice of the failure
output ([#2774](https://github.com/cslib-community/cslib-frontier/issues/2774)); it does not certify
the reduction's native runtime or its ideal scalar sampling. Replacing the transcript and answer
defaults in a native implementation still requires a bounded-execution nonexhaustion proof.

[`SchnorrSignature/WordROM.lean`](../../CslibFrontier/Crypto/Computational/SchnorrSignature/WordROM.lean)
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
completes the representation milestone [#2696](https://github.com/cslib-community/cslib-frontier/issues/2696);
native saved-forger composition, adaptive key-generation/signing `CloseTo` game hops and efficient
forking remain open. No guarantee is asserted for malformed public keys, and no group decoder is
assumed. Concrete scalar-alias extraction, rejected commitments, and distinct/repeated junk hash
queries are checked in
[`Crypto/SchnorrWordROM.lean`](../../CslibFrontierTests/Crypto/SchnorrWordROM.lean).

The same module instantiates `schnorrFamilyROMScheme` with `m`-bit challenges when
`2 ^ m ≤ F.order d`, and `schnorrScalarROMScheme` with full scalar challenges. Their exact typed
EUF-CMA bounds account for both signing queries and random-oracle queries. The asymptotic theorem
`negligible_eufCmaGame_schnorrFamilyROMScheme` assumes negligible success of the specified forking
reduction. Applying the strict-PPT discrete-logarithm assumption still requires an efficient
realization of that reduction, with encoded adaptive signing/hash access and final-message
freshness. The private-coin prerequisite is supplied by `IsOraclePPTOn.exists_savedCoins` in
[`Oracle/Replay.lean`](../../CslibFrontier/Computability/Probabilistic/Oracle/Replay.lean), which charges
full-input replay and retains external state.
[`Signature/WordRandomOracle.lean`](../../CslibFrontier/Crypto/Computational/Signature/WordRandomOracle.lean)
also gives a key-independent saved-coin adapter for actual Boolean-channel word forgers, with
full-input native replay and equality of the existing shared-world and EUF-CMA games. All word
hash payloads stay distinct. Applying that adapter to Schnorr's concrete query encoding, composing
the signer/hash handlers, and certifying the complete forking reduction remain open. See the
checked algorithms and typed-ROM examples in
[`CslibFrontierTests/Crypto/SchnorrSignature.lean`](../../CslibFrontierTests/Crypto/SchnorrSignature.lean).

[`SchnorrSignature/NativeROM.lean`](../../CslibFrontier/Crypto/Computational/SchnorrSignature/NativeROM.lean)
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
`2⁻ⁿ`. The milestone [#2708](https://github.com/cslib-community/cslib-frontier/issues/2708) does not
compose these errors across adaptive signing requests or certify the full forking reduction.
Checks in [`Crypto/SchnorrNativeROM.lean`](../../CslibFrontierTests/Crypto/SchnorrNativeROM.lean)
cover bounded reply prefixes, aliases, malformed outer signatures, a cache hit retaining junk
entries, and preservation of external state through private nonce sampling.

[`SchnorrSignature/EncodedROM.lean`](../../CslibFrontier/Crypto/Computational/SchnorrSignature/EncodedROM.lean)
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
[`Crypto/SchnorrEncodedROM.lean`](../../CslibFrontierTests/Crypto/SchnorrEncodedROM.lean) also retain
distinct junk-cache entries and distinguish fresh from signed final messages. This completes the
representation milestone #2742; adaptive actual-sampling error composition, the key-generation
transport and the native efficient forking reduction remain #2568.

For strict-PPT **identification** under discrete log, use `SchnorrImpersonator`,
`schnorrDirectGame` and `negligible_schnorrDirectGame`; for an adversary given independent honest
conversations, use `SchnorrEavesdropAdversary`, `schnorrEavesdropGame` and
`negligible_schnorrEavesdropGame` from
[`SchnorrEavesdrop.lean`](../../CslibFrontier/Crypto/Computational/SchnorrEavesdrop.lean).
These identification games draw a fresh verifier challenge after the adversary's commitment.
Signature EUF-CMA instead gives adaptive signing and hash access, uses the same memoized hash
answer at verification, and rejects a final message previously signed. Discarding a message field
from an identification adversary does not supply this signature reduction.

[`CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamirNIZK.lean`](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/FiatShamirNIZK.lean)
compiles a public-coin `SigmaProtocol X Y T C Z` into a non-interactive proof system
(`fiatShamirNIZKProve`, `fiatShamirNIZKVerify`) over the statement-bound random-oracle specification
`NIZKHashSpec Y T C := fun _ : Y × T => C` ([bs23][bs23], Sections 20.3.3–20.3.5):

- **Completeness and statement binding (`Section 20.3.3`):** `fiatShamirNIZK_complete` proves
  acceptance with probability `1` (`= PMF.pure true`) from any initial lazy random-oracle cache when
  `R x y` holds. Querying `H` on `(y, t)` rather than `t` alone is required when statements can be
  chosen adaptively after querying `H`; a concrete `ZMod 5 × ZMod 5` Schnorr counterexample in
  [`CslibFrontierTests/Crypto/FiatShamirNIZK.lean`](../../CslibFrontierTests/Crypto/FiatShamirNIZK.lean)
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

The ideal-permutation model gives an adversary both forward and inverse access to one consistent random permutation. Separate cipher/primitive channels support [CslibFrontier/Crypto/Protocols/Cipher/EvenMansour.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/EvenMansour.lean); the two-key and single-key advantages are bounded by `2*Q_cipher*Q_primitive/|G|`. [CslibFrontier/Crypto/Protocols/Cipher/LubyRackoff.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean) proves three-round forward and four-round strong/bidirectional Feistel results and an explicit three-round chosen-ciphertext attack, while [CslibFrontier/Crypto/Protocols/Cipher/FeistelNetworks.lean](../../CslibFrontier/Crypto/Protocols/Cipher/FeistelNetworks.lean) (tested in [CslibFrontierTests/Crypto/FeistelNetworks.lean](../../CslibFrontierTests/Crypto/FeistelNetworks.lean)) adds substitution–permutation networks (`spnNetworkEquiv`, `bijective_spnNetworkEquiv`), original alternating unbalanced Feistel networks on odd/even block lengths (`unbalancedFeistel4`, `unbalancedFeistel4BitString`, built on the bit-string split `BitString.halfSplitEquiv` in [HalfSplit.lean](../../CslibFrontier/Foundations/Data/BitString/HalfSplit.lean)), degenerate round-function periodicity (`feistelNetwork_replicate_zero`, `feistelNetwork_replicate_id`), and explicit 1-round CPA (`feistel1CPAAttack`), 2-round CPA (`feistel2CPAAttack`), 3-round repeated-key CPA (`feistel3RepeatedKeyCPAAttack`), and sharper `(|G| - 1)⁻¹` 3-round CCA (`idealStrongGame_feistel3CCAAttack_true_le_inv_card_sub_one`) permutation-fiber distinguisher bounds (fiber counts from [RandomPermutation/ExtPermsCard.lean](../../CslibFrontier/Languages/Probabilistic/RandomPermutation/ExtPermsCard.lean)) (with original concrete probability bounds). These are bounded-query theorems over finite groups with exact ideal functions/permutations. Native local computation is not charged merely by `IsQueryBounded`. The uniform computational counterparts live in [CslibFrontier/Crypto/Computational/PseudorandomPermutation.lean](../../CslibFrontier/Crypto/Computational/PseudorandomPermutation.lean) (`BlockCipher`, `BlockCipher.PRP`, `BlockCipher.StrongPRP` against oracle-PPT word distinguishers, with explicit security parameter and the `[]` convention for malformed blocks), [CslibFrontier/Crypto/Computational/EvenMansour.lean](../../CslibFrontier/Crypto/Computational/EvenMansour.lean) (`evenMansourCipher` and `singleKeyEvenMansourCipher`, randomized `ProbOracleComp` and `WordOracleComp (Bool × Bool)` ideal-permutation security bounds `2 * Q_e * Q_π / 2 ^ n`, polynomial-query `Negligible` advantage, and `Game.Indistinguishable` against `IsOraclePPT encBool` distinguishers), and [CslibFrontier/Crypto/Computational/LubyRackoff.lean](../../CslibFrontier/Crypto/Computational/LubyRackoff.lean): `PseudorandomFunction.prp_lubyRackoffCipher` proves that the three-round cipher `lubyRackoffCipher` built from a `PseudorandomFunction` is a PRP. Its proof reduces to `PseudorandomFunction.multiKey` with an oracle-PPT adapter, and both modules transfer their finite-group bounds to randomized adversaries by fixing their private coins (`ProbOracleComp.coinLaw`, [CoinFixing.lean](../../CslibFrontier/Languages/Probabilistic/Oracle/CoinFixing.lean)). `PseudorandomFunction.strongPRP_lubyRackoff4Cipher` proves that the four-round cipher `lubyRackoff4Cipher` is a strong PRP, in the same way, through a bidirectional adapter.

## General zero knowledge: quantifier orders, primary-input clocks, and instance indexing

[GenerableZeroKnowledge](../../CslibFrontier/Crypto/Computational/ZeroKnowledge.lean#L144) chooses one simulator for each uniform strict oracle-PPT verifier before all efficiently generable instance, witness and auxiliary-input families. Those families are deterministic polynomial-time functions of unary `n`. The stronger [AuxiliaryInputZeroKnowledge](../../CslibFrontier/Crypto/Computational/ZeroKnowledge.lean#L172) permits arbitrary polynomially bounded instance, witness, verifier auxiliary-input (`z`) and distinguisher auxiliary-input (`z'`) families, and therefore potentially nonuniform advice; its simulator is chosen once per `Vstar` before the families and distinguisher and is certified on `(1^n, (a, z))`.

To work with arbitrary, **unbounded** auxiliary inputs `z : List Bool` whose length is not bounded by the security parameter, import `CslibFrontier.Crypto.Computational.ZeroKnowledge.AuxClock` ([ZeroKnowledge/AuxClock.lean](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/AuxClock.lean)), which builds on [IsPPTWithAux](../../CslibFrontier/Computability/Probabilistic/PPT/AuxClock.lean#L95) and [IsOraclePPTWithAux](../../CslibFrontier/Computability/Probabilistic/PPT/AuxClock.lean#L106) and machine-level input-tape prefix locality ([MultiTapeMachine.runFrom_eq_of_prefix_agree](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/PrefixLocality.lean#L61)):

- **Family-indexed unbounded auxiliary input ([UnboundedAuxiliaryInputZeroKnowledge](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L175)):** the malicious verifier `Vstar` is clocked in the primary input `(1^n, a)` via `IsOraclePPTWithAux (encPair encUnary enc) encBits`. One witness-free simulator `S` is chosen per `Vstar` before the families and distinguisher, certified by `IsPPTWithAux (encPair encUnary enc) encBits`, and depends only on a polynomial prefix of `z`. Every distinguisher `adversary` clocked in `((1^n, a), view)` via `IsPPTWithAux` receives the **full untruncated** `z n` and has negligible advantage across all polynomially bounded valid `(a, w)` families and arbitrary, unbounded `z : ℕ → List Bool`.
- **Instance-indexed (`x`-indexed) unbounded auxiliary input ([InstanceAuxiliaryInputZeroKnowledge](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L374)):** `Vstar` is clocked in the primary instance `x` via `IsOraclePPTWithAux enc encBits`, and one simulator `S` certified by `IsPPTWithAux enc encBits S` is chosen per `Vstar` before the distinguisher, polynomial bounds, instance `x`, witness `w` and auxiliary input `z`. For every distinguisher `adversary` clocked in `(x, view)` via `IsPPTWithAux (encPair enc encBits) encBool` (receiving the full untruncated `z`), every witness-length bound `w.length ≤ c_w * (n + 1) ^ d_w` at `n = (enc x).length`, and every inverse-polynomial degree `k`, all sufficiently large valid instances `(x, w)` and all arbitrary `z : List Bool` have distinguishing advantage at most `1 / ((n : ℝ) + 1) ^ k`.
- **Clock and indexing bridges:** `AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge` (with its `ZeroKnowledgeProof` and `ZKProof` projections) lifts `AuxiliaryInputZeroKnowledge` to `UnboundedAuxiliaryInputZeroKnowledge` by defining `S n a z := S₀ n a (z.take (T_V n a))` and instantiating `z` with the verifier-sized prefix and `z'` with the distinguisher-sized prefix, and `UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge` (hence `AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`) bridges to `InstanceAuxiliaryInputZeroKnowledge`.

`ZeroKnowledgeProof` bundles native honest interaction and verification, perfect completeness, soundness at most `1/3` against arbitrary provers, and the generable ZK predicate. `ZeroKnowledgeProof.mem_IP` is an explicit bridge into the interactive-proof class. [ZKProof](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Soundness.lean#L71) generalizes the soundness bound to a security-parameter function `soundness : ℕ → ENNReal` (with `ZeroKnowledgeProof.toZKProof` embedding constant `1/3` soundness), and [ZKProof.NegligibleSoundness](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Soundness.lean#L205) pairs finiteness `∀ n, soundness n ≠ ⊤` with `Negligible (fun n => (soundness n).toNNReal)` (`negligibleSoundness_one_third_pow` discharges `(1/3) ^ (k n)` for `n ≤ k n`, and [IsOraclePPTOn.sequentialRepeat_count](../../CslibFrontier/Computability/Complexity/Classes/IP/Repetition.lean#L135) certifies polynomial-count sequential verifier repetition). [OneWay.exists_zeroKnowledgeProof_of_mem_NP](../../CslibFrontier/Crypto/Computational/ZeroKnowledge.lean#L563) establishes the single-round `1/3`-soundness `ZeroKnowledgeProof` notion for NP from a uniform OWF with 3SAT assignments of the Karp-reduced formula as witnesses, while [OneWay.exists_zeroKnowledgeProof_of_npRelation](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Levin.lean#L187) and [PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Levin.lean#L172) compose a Levin reduction ([CookLevin.ThreeSAT_levinHard](../../CslibFrontier/Computability/Complexity/CookLevin/Levin.lean#L234)) so that `zk.isWitness a w = true ↔ R.IsWitness a w` holds for the NP relation's own witnesses. Sequential repetition across `k(n) = n + 1` independent masked rounds in [GMW/Sequential.lean](../../CslibFrontier/Crypto/Computational/GMW/Sequential.lean), its multi-round rewinding simulator in [GMW/Sequential/Simulator.lean](../../CslibFrontier/Crypto/Computational/GMW/Sequential/Simulator.lean), and the Karp/Levin composition in [ZeroKnowledge/Amplification.lean](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Amplification.lean) amplify soundness to `(1/3) ^ (n + 1)` against arbitrary stateful provers, giving [OneWay.exists_zkProof_of_mem_NP](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Amplification.lean#L336) and [OneWay.exists_zkProof_of_npRelation](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Amplification.lean#L348) from a uniform OWF.

The unrestricted auxiliary-input theorems (`AuxiliaryInputZeroKnowledge`, `UnboundedAuxiliaryInputZeroKnowledge`, and `InstanceAuxiliaryInputZeroKnowledge` for both the single-round and sequentially amplified GMW proof systems) require the advice-supplied generator premise `GMW.AdvicePRG` rather than uniform OWF security; [`NonuniformPRG.advicePRG`](../../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L76) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L77) discharge this premise from any [`NonuniformOneWay`](../../CslibFrontier/Crypto/Computational/Nonuniform/Basic.lean#L304) function. This yields the single-round `1/3`-soundness theorems [`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_mem_NP`](../../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L143) and [`NonuniformOneWay.exists_auxiliaryInputZeroKnowledge_of_npRelation`](../../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L154) together with the full soundness-amplified GMW landmark theorems [`NonuniformOneWay.exists_zkProof_of_mem_NP`](../../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L198) and [`NonuniformOneWay.exists_zkProof_of_npRelation`](../../CslibFrontier/Crypto/Computational/Nonuniform/ZeroKnowledge.lean#L213) with soundness `(1/3) ^ (n + 1)`, `ZKProof.NegligibleSoundness`, and `ZKProof.AuxiliaryInputZeroKnowledge` (lifting via `AuxClock` to `ZKProof.UnboundedAuxiliaryInputZeroKnowledge` and `ZKProof.InstanceAuxiliaryInputZeroKnowledge`). The protocol is an adapted masked-3SAT truth-table commitment construction, rather than a literal encoding of the original GMW three-color protocol. Complete checked examples for all three auxiliary-input interfaces, their clock/indexing bridges, sequential soundness amplification, and the nonuniform-OWF derivations are in [CslibFrontierTests/Crypto/ZeroKnowledge.lean](../../CslibFrontierTests/Crypto/ZeroKnowledge.lean) and [CslibFrontierTests/Crypto/Nonuniform.lean](../../CslibFrontierTests/Crypto/Nonuniform.lean).

## Synchronous multiparty computation

[MultiOracleSpec](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/Basic.lean#L95) gives typed k-ary ideal calls. A `Round` is a private authenticated message or an ideal call with an injective assignment of participants to slots. A `Schedule` is a fixed list of rounds. Each party's view includes only its input, private coins and delivered messages/answers; its output depends on that view. Channels are synchronous and the schedule is fixed, not selected by an asynchronous network adversary.

`PerfectSemiHonestPrivate` requires equality of the joint coalition-view and complete-output law with an explicit ideal simulator for every static coalition. `PerfectSemiHonestPrivateProper` restricts the coalition to a proper subset, and `PerfectSemiHonestPrivateLe t` restricts to threshold coalitions with `I.card ≤ t` (`PerfectSemiHonestPrivate.le`, `perfectSemiHonestPrivateLe_of_deterministic`, `PerfectSemiHonestPrivateLe.proper_of_succ_eq`). These are perfect distributional notions, not computational indistinguishability. For a concrete distinguishing advantage between the same two joint laws, see `semiHonestAdvantage` under [Yao's two-party protocol](#yaos-two-party-protocol). Malicious behavior, adaptive corruption, concurrent composition and universal composability are not present in this interface.

The construction chain is explicit:

1. [perfectSemiHonestPrivate_twoPartyMul](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/SharedMul.lean#L290) realizes two-party shared multiplication in an ideal 1-out-of-4 OT world.
2. `perfectSemiHonestPrivate_multiPartyMul` composes pairwise multiplication for m parties.
3. [perfectSemiHonestPrivate_gmwCircuit](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/CircuitEval.lean#L1206) evaluates Boolean circuits over additive shares. It refreshes output shares to support arbitrary output-wire aliases.
4. [PerfectSemiHonestPrivate.compose](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/Composition.lean#L734) proves typed k-ary subprotocol substitution. Deterministic GMW-OT has full-coalition privacy; the randomized wrapper uses proper coalitions.
5. [exists_perfectSemiHonestPrivate_ot14_of_polyTime](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/MPC/PolyTime.lean#L5989) compiles a uniform word-level polynomial-time functionality to circuits and supplies native certificates for the centralized joint word-oracle runner and each proper-coalition simulator.

The final theorem fixes the number of parties and has explicit polynomial-time unary schedules for per-party input/output and random-tape widths. Its efficiency assertion concerns the **centralized joint runner**, not separately certified local native machines for every party. Its randomized privacy assertion excludes the full coalition. The source explicitly compares this variant with Goldreich's Chapter 7 and contains a full-coalition counterexample to its independent-coin-share simulator in [CslibFrontierTests/Crypto/MPC.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Crypto/MPC.lean). The primary book page confirms Chapter 7's relevant semi-honest, composition and OT-completeness development; the delicate full-coalition comparison is retained as the formalization's documented statement boundary, not independently adjudicated here [goldreich04][goldreich04].

For arithmetic share multiplication in an ideal Beaver-triple preprocessing hybrid model over `ZMod p`, import [`CslibFrontier.Crypto.Protocols.MPC.Beaver`](../../CslibFrontier/Crypto/Protocols/MPC/Beaver.lean) (and [`CslibFrontier.Crypto.Protocols.MPC.Broadcast`](../../CslibFrontier/Crypto/Protocols/MPC/Broadcast.lean) for the reusable sender-indexed synchronous point-to-point and broadcast combinators `pairwiseSteps`, `broadcastSteps`, `deliverBroadcast`, `evalWith_pairwiseSteps`, `outputAt_pairwiseSteps`, `evalWith_broadcastSteps`, and `outputAt_broadcastSteps`). `beaverMulProtocol p m` queries `beaverTripleSpec p m` once, broadcasts the masked openings `(x_i - a_i, y_i - b_i)`, and outputs additive shares summing to `(∑_i x_i) * (∑_i y_i)` (`sum_output_beaverMulProtocol`), generalizing the 2.5-party dealer protocol of [bs23][bs23] (Section 23.2.2) to `m` parties. `perfectSemiHonestPrivateProper_beaverMul` proves `PerfectSemiHonestPrivateProper` in `beaverTripleWorld p m` for the ring-polymorphic `sharedMulFunctionality m` against every proper static coalition `I ≠ Finset.univ` via `beaverMulSim`; this is an exact distributional equality in the ideal triple-preprocessing hybrid model, with no polynomial-time simulator certificate or preprocessing realization. The same module includes `tamperedOpeningExtract_eq`, `eval_tamperedOpeningReal`, and `le_advantage_tamperedOpeningBitGame`: an original standalone `ProbComp (ZMod p)` / `Game` illustration (motivated by [bs23][bs23], Section 23.2.4) showing that if 2-party unauthenticated Beaver multiplication of `[x] * [0]` is followed by revealing the honest party's output share after an additive-error tampered opening, the tampered transcript determines `x` and distinguishes `x ∈ {0, 1}` with advantage at least `1/2` against any input-independent `blindGuess : ProbComp (ZMod p)`. This illustration is not an execution of `beaverMulProtocol` (which does not broadcast output shares) and is not a general malicious-security definition. Checked examples are in [CslibFrontierTests/Crypto/Broadcast.lean](../../CslibFrontierTests/Crypto/Broadcast.lean) and [CslibFrontierTests/Crypto/Beaver.lean](../../CslibFrontierTests/Crypto/Beaver.lean).

For Shamir secret-sharing homomorphisms and synchronous `m`-party Ben-Or–Goldwasser–Wigderson (BGW) arithmetic gate protocols over finite fields in `noOracleWorld`, import [`CslibFrontier.Crypto.Protocols.SecretSharing.Shamir.Linear`](../../CslibFrontier/Crypto/Protocols/SecretSharing/Shamir/Linear.lean) and [`CslibFrontier.Crypto.Protocols.MPC.BGW`](../../CslibFrontier/Crypto/Protocols/MPC/BGW.lean). `Shamir/Linear.lean` extends upstream `Cslib.Crypto.Protocols.SecretSharing.Shamir` with linear homomorphisms (`share_add`, `share_sum`, `reconstruct_add`, `reconstruct_sum`), explicit Lagrange weights at zero (`Polynomial.lagrangeWeightAtZero`), degree-`2t` product-share reconstruction for `2 * params.threshold < Fintype.card Party` (`reconstruct_mul_share_eq_mul`), and marginal uniformity `PMF.uniformOfFintype (I → F)` for unauthorized coalitions `I.card ≤ params.threshold` (`uniformOfFintype_map_restrict_share`). `MPC/BGW.lean` proves commutativity of Lagrange reconstruction with Shamir sharing (`bgwDegreeReduceShare_share`) and formalizes two synchronous `m`-party gate protocols: the two-round sum protocol `bgwSumProtocol params`, with output correctness (`output_bgwSumProtocol`) and full joint view-and-output `t`-privacy `PerfectSemiHonestPrivateLe params.threshold` (`perfectSemiHonestPrivateLe_bgwSum`); and the one-round Gennaro–Rabin–Rabin degree-reduction multiplication gate `bgwDegreeReductionProtocol params`, which outputs degree-`t` Shamir shares of `a * b` for `2 * params.threshold < m` (`output_bgwDegreeReductionProtocol_eq_share_mul`) and satisfies coalition **view-only** `t`-privacy (`map_restrict_evalWith_bgwDegreeReductionProtocol`; joint view-and-honest-output-share simulation and full circuit composition are not included). Checked examples over `ZMod 5` are in [CslibFrontierTests/Crypto/BGW.lean](../../CslibFrontierTests/Crypto/BGW.lean).

For SPDZ authenticated secret sharing, online Beaver multiplication (Damgård–Pastro–Smart–Zakarias, CRYPTO 2012; ePrint 2011/535, §2 and Fig. 1), and batch `MACCheck` (Damgård–Keller–Larraia–Pastro–Scholl–Smart, ESORICS 2013; ePrint 2012/642, App. D.1, Fig. 10 and §5.1, Lemma 1) over `ZMod p` (the 2012 paper works over `F_{p^k}`), import [`CslibFrontier.Crypto.Protocols.MPC.SPDZ`](../../CslibFrontier/Crypto/Protocols/MPC/SPDZ.lean). `AuthShare p n` represents `(delta, valShares, macShares)` with `AuthShare.Valid alpha` asserting `∑_i (macShares i) = alpha * ((∑_i (valShares i)) + delta)`. Linear operations (`AuthShare.add`, `AuthShare.neg`, `AuthShare.sub`, `AuthShare.smul`, `AuthShare.addConst`) and online Beaver multiplication (`AuthShare.mulOnline`) preserve `Valid alpha`, agree coordinatewise with `beaverMulShare` on value shares (`AuthShare.valShares_mulOnline_eq_beaverMulShare`), and reconstruct `(∑_i x_i) * (∑_i y_i)` when `d = x - a`, `e = y - b`, and `c = a * b` (`AuthShare.secret_mulOnline_eq_mul`). For a batch of `T` opened values, `macCheckProtocol p n T sampleCoins commit` models steps 5–9 of the 2013 `MACCheck` (Fig. 10: commitment and opening of the residual shares, with the residual adapted to the 2012 `delta`-representation; steps 1–4, which derive the weights from a coin-flipped seed, are replaced by input weights) as a two-round broadcast protocol over `CslibFrontier.Crypto.Protocols.MPC.Basic` and `CslibFrontier.Crypto.Protocols.MPC.Broadcast`; honest batches satisfy `sum_checkResidual_eq_zero` and accept with probability `1` (`eval_snd_macCheckProtocol_eq_pure_true`), while forged openings satisfy `sum_checkResidual_eq_neg_mul` (`∑_i checkResidual (inp i) = -alpha * linearCombAddHom err e`) and the cheating equivalence `sum_checkResidual_add_eq_zero_iff`. Over prime fields (`[Fact (Nat.Prime p)]`), `eval_linearCombZeroGame_eq` proves Stage-1 weight cancellation occurs with exact probability `1 / p` for `err ≠ 0` (via `toOuterMeasure_uniform_linearComb_eq_zero`), `eval_macKey_guess_le` bounds Stage-2 key guessing when the combined error is nonzero (via `toOuterMeasure_uniform_linearComb_eq` on `Unit`), and `eval_macCheckSoundnessGame_le`, `succProbability_macCheckSoundnessGame_le`, and `eval_macCheckSoundnessAdvGame_le` prove that the `MACCheck` cheating equation `alpha * linearCombAddHom err e = deltaShift e` in the standalone games `macCheckSoundnessGame` and `macCheckSoundnessAdvGame` holds with probability at most `2 / p` (the game from the proof of Lemma 1, App. D.3; the game's `alpha` plays the role of an honest party's key share, with corrupt-party contributions and MAC-share tampering absorbed into the shift) against any `e`-adaptive residual shift `deltaShift` and any prior randomized adversary `adv : ProbComp S` independent of `alpha`. In `macCheckProtocol`, weights are supplied as inputs (`PartyCheckInput.weights`) whose joint generation after the openings is not modeled, `alpha` is not sampled by the protocol, `commit : ZMod p → Coins → Comm` is an abstract deterministic commitment map (with `AddCommMonoid` instances on `Coins`, `Comm`, and `ResidualOpening` used only by `broadcastSteps`), and the games analyze the standalone algebraic cheating equation rather than an execution of `macCheckProtocol`, a computational commitment binding reduction, or a UC emulation proof. Checked examples are in [CslibFrontierTests/Crypto/SPDZ.lean](../../CslibFrontierTests/Crypto/SPDZ.lean).

For the commitment ingredient toward malicious security, import
[`CslibFrontier.Crypto.Protocols.MPC.OTCommitment`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment.lean).
`OTCommitment.Sender` selects arbitrary randomized OT tables from private state and receives
only the ideal sender's `Unit` answer. Apply `binding` to an initial state distribution and a
function producing two candidate openings from the final sender state: it bounds their joint
acceptance probability by `2⁻ᵏ`, without assuming the submitted tables encode a consistent bit.
Keep receiver choices and selected values private; giving either to the sender changes the game.
`perfectHiding` equates full query/answer transcript and final-state laws for arbitrary adaptive
`Receiver` strategies, including all four OT indices. The checked
[OT commitment tests](../../CslibFrontierTests/Crypto/OTCommitment.lean) demonstrate rejection of an
inconsistent opening, a tight one-call attack with success `1/2`, and the zero-call bound `1`.

For an explicit list opening, import
[`OTCommitment.Opening.PolyTime`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/Opening/PolyTime.lean).
`openPairs choices received submission` returns the accepted bit or `none` for abort or rejection.
It checks that all three lists have the same length before testing every pair's parity and selected
value. `openPairs_ofFn` identifies this total checker with `openResult` on finite-vector encodings;
`openPairs_polyTime` charges the complete choice and answer bit strings and the framed opening
pair list, without a well-formedness hypothesis. The [checked list clients](../../CslibFrontierTests/Crypto/OTCommitmentOpening.lean)
include short and long inputs in each position. An empty opening accepts either bit when both
receiver lists are empty; this preserves the zero-call boundary and asserts no binding security.

To extract a bit before opening, import
[`OTCommitment.Extraction`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/Extraction.lean).
`extract` takes the strict majority of the actual OT input pair parities, choosing false on a tie.
Only the simulator receives these corrupted sender inputs; this is not extraction from a public
commitment string. `simulatedOpening_coupled` couples `realOpening` with `simulatedOpening` within
`2⁻⌈k/2⌉`, jointly preserving the sender's state at the commit boundary and any auxiliary output
from its opening continuation. The simulator fixes the bit before that continuation runs and
releases only the stored bit or abort. Apply the coupling's `toOuterMeasure_le` for any event of
this joint output. With two mixed-parity rows, extraction error can be `1/2` even though the
double-opening bound is `1/4`; the
[checked examples](../../CslibFrontierTests/Crypto/OTCommitmentExtraction.lean) attain both bounds.

For native computation, import
[`OTCommitment.PolyTime`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/PolyTime.lean).
`extractPairs_polyTime` certifies the deterministic extractor with input encoding
`encList (encPair encBool encBool)` and output `encBool`. `extractPairs_ofFn` connects the explicit
list algorithm to the OT table extractor. This certificate applies only to the extractor.

For a corrupted receiver, import
[`OTCommitment.Equivocation`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/Equivocation.lean).
`equivocation` proves the exact joint law of the transcript, receiver state and revealed opening.
The simulator runs `receiverRun A false` without the committed bit, then uses `equivocate b` only
when that bit is released at opening. For each recorded index and answer, it keeps the selected
component equal to the answer and reconstructs the other component using the supplied parity.
`equivocation_bind` permits any randomized post-opening continuation on that entire view.
The common `receiverCommit` runner retains the honest sender's actual masks for the proof;
`receiverRun` projects them away and the receiver strategy never sees them. The simulator does
see the corrupted receiver's indices, which are unavailable to a malicious sender in the binding
game. The [checked examples](../../CslibFrontierTests/Crypto/OTCommitmentEquivocation.lean) cover
slots 2 and 3, adaptive private state and the failure of reusing parity-zero pairs to open to one.

`equivocatePairs_polyTime` in the same `OTCommitment.PolyTime` import certifies the deterministic
map from a revealed bit and an explicit receipt list to opening pairs. Its input encoding is
`encPair encBool (encList (encPair (encFinEnum (Fin 4)) encBool))`; the full four-valued indices
are retained. `equivocatePairs_ofFn` connects this list operation to the transcript reconstruction.

These semantic corruption-specific laws alone do not provide full ideal commitment scheduling,
mid-commit abort, composition, or polynomial-time simulators. The malicious MPC compiler and its
real/ideal simulation remain open in
[#1212](https://github.com/cslib-community/cslib-frontier/issues/1212).

For a stateful functionality with separate commit and open phases, import
[`CslibFrontier.Crypto.Protocols.Commitment.World`](../../CslibFrontier/Crypto/Protocols/Commitment/World.lean)
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
executions. The [checked world clients](../../CslibFrontierTests/Crypto/CommitmentWorld.lean)
show honest opening, early opening followed by commitment, attempted overwrite, both abort
orders, and adaptive private polling. These are functionality laws, not an OT realization,
UC security, or a simulator runtime certificate.

To connect the OT simulations to these commands, import
[`OTCommitment.World`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/World.lean).
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
output. See the [checked simulation clients](../../CslibFrontierTests/Crypto/OTCommitmentWorld.lean)
for all four OT slots, the mixed-parity attack, withholding and zero calls.

These are semantic `StateT Store PMF` drivers for arbitrary PMF strategies, not realized
`ProbOracleComp` programs or efficient simulators. They cover a fixed-length single session
with one later release decision; arbitrary scheduling, mid-commit abort, malformed bytes,
composition and full malicious MPC remain open.

For a realized receiver simulator, import
`CslibFrontier.Crypto.Protocols.MPC.OTCommitment.Program.PolyTime`.
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
[checked program clients](../../CslibFrontierTests/Crypto/OTCommitmentProgram.lean) provide an
adaptive private-coin receiver with growing answer history, randomized withholding and a
randomized final continuation. They also show why a separately efficient state-doubling
callback fails the additive-growth contract. This certificate covers the fixed receiver
schedule under those hypotheses; arbitrary scheduling, composition and full malicious MPC remain open.

For the corrupted sender, import
[`OTCommitment.SenderProgram.PolyTime`](../../CslibFrontier/Crypto/Protocols/MPC/OTCommitment/SenderProgram/PolyTime.lean).
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
The [checked sender programs](../../CslibFrontierTests/Crypto/OTCommitmentSenderProgram.lean) include
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
[complete-program clients](../../CslibFrontierTests/Crypto/OTCommitmentCompleteSender.lean) include a
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
The [serial execution clients](../../CslibFrontierTests/Crypto/OTCommitmentSerial.lean) exercise
adaptive duplicate slots, opening/answer correlation, zero rows, unanswered rows, rejected retries
and why an opening must not permit a later selection.

These are equalities for two explicit honest-party schedules in an original single-session serial
world. They do not equate arbitrary interleavings or prove a new security notion. A global
receiver-program adapter, uniform native execution contracts for this common world, two-sided
realization, composition/UC and full malicious MPC remain separate obligations.

## Garbled circuits

[Primitives/Garbling/Basic.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Basic.lean) garbles a circuit `C : Circuit σ n m` over any signature with a Boolean interpretation. It uses point-and-permute in the style of Yao [yao86][yao86] and Beaver–Micali–Rogaway [bmr90][bmr90]. Each wire carries two labels in `K × Bool` for a finite additive group `K`. The `Bool` component is the colour, which is the wire's value masked by a permutation bit. A gate of arity `a` has `2 ^ a` rows indexed by argument colours. Each row holds the gate's output label for those colours, masked by the sum `Σₖ F (key of argument k) (tw slot)` of a keyed function `F : K → T → K × Bool`, where `tw` assigns a tweak to each (gate, row, argument) slot. `Garbled.run_garbleWith` proves exact correctness for every `F`, every tweak map and every choice of keys and permutation bits; `Garbled.run_of_mem_support` lifts this to every outcome of the randomized `garble`. Evaluation runs `n + C.size` rounds on the public `Circuit.Topology` and needs only `Topology.IsOrdered`, which every circuit's topology satisfies (`Circuit.isOrdered_topology` in [Circuit/Topology.lean](../../CslibFrontier/Computability/Circuit/Topology.lean)).

[Primitives/Garbling/Privacy.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Privacy.lean) proves simulation privacy with topology side information in the sense of Bellare–Hoang–Rogaway [bhr12][bhr12]. The evaluator's `View` is the table, one label per input wire and the decoding bits. `simulate` sees only the topology, `F`, `tw` and the output. It samples uniform wire labels and filler rows, and `View.run_simulateWith` shows that its views decode to the output. `advantage_realGame_simGame_le` bounds the advantage of every distinguisher `D` between `realGame` and `simGame` by `Σ_{j < n + C.size} PRF.advantage F (reduction C I F tw x D j)`, assuming `tw` is injective. The assumption is needed: in a row that reads one wire twice with the same colour, equal tweaks on the two slots would make their mask terms cancel in the colour bit. The identity tweak map on slots satisfies it. The proof is a hybrid over wires in wire-number order. The reduction for wire `j` embeds the PRF key as the inactive key of wire `j`, makes at most one oracle query per argument slot (`isQueryBounded_reduction`), and runs `D` once. `advantage_realGame_simGame_le_mul` gives `(n + C.size) · ε` under a uniform bound `ε`. The PRF game is the finite private-coin oracle game of [Primitives/PRF/Finite.lean](../../CslibFrontier/Crypto/Primitives/PRF/Finite.lean).

The statement is concrete and single-instance: the circuit, input and distinguisher are fixed and the keyed function is arbitrary, so the bound is meaningful only when the reductions' PRF advantages are small. In the `prv.sim` game of [bhr12][bhr12] (formalized together with conventional-circuit topology/size inverters and coarse-grained adaptive privacy `prv1` in the abstract garbling-scheme framework; see [Security games and primitive families](security-games-and-primitives.md#garbling-schemes)) the adversary chooses the circuit and input itself; a bound for that game follows by averaging over its choice, but this transfer is not formalized. Running time is not tracked: there are no cost bounds for garbling, evaluation, the simulator or the reductions. Nothing here is asymptotic or polynomial-time; there is no connection to the word-level `PseudorandomFunction`; and this scheme has no table-size optimizations. Free XOR and half gates are covered in the subsections below, as separate constructions with single-instance simulation privacy under circular correlation robustness. Adversary-chosen circuits and inputs, asymptotic and polynomial-time cost bounds, a formalized query-legality condition for circular correlation robustness, and instantiation in the garbling-scheme interface of [bhr12][bhr12] remain in [#3236](https://github.com/cslib-community/cslib-frontier/issues/3236). Theorem numbers of [bhr12][bhr12] and [lp09][lp09] were not checked, since their full texts were inaccessible in this pass. Checked instances are in [CslibFrontierTests/Crypto/Garbling.lean](../../CslibFrontierTests/Crypto/Garbling.lean).

[Primitives/Garbling/SizeLowerBound.lean](../../CslibFrontier/Crypto/Primitives/Garbling/SizeLowerBound.lean) proves the generic one-world garbled-payload bit-length lower bound `sub_le_bitLength_of_recover`: if a simulated law of `(C, X)` within statistical distance `ε` of the real law of `(C, X)` leaves at least `t` bits of conditional entropy in a hidden value `X : α` given the observation `C`, and in the real view a deterministic decoder recovers `X` from `(C, G)` for an `m`-bit payload `G : BitString m` with error probability `δ` (the probability under the real law that it outputs a value other than `X`), then `t - ε log₂ |α| - condEntropyModulus ε - (h₂(δ) + δ log₂ (|α| - 1)) ≤ m`, where `h₂` is binary entropy in bits and `condEntropyModulus ε = (1 + ε) h₂(ε / (1 + ε))` (attained with zero slack by the one-time pad in [CslibFrontierTests/Crypto/GarblingSizeLowerBound.lean](../../CslibFrontierTests/Crypto/GarblingSizeLowerBound.lean)). This packages the single-world transfer (`sub_le_conditionalEntropy_of_dist_le`), chain-rule and Fano steps; the multi-world gate-specific Shannon-type inequalities for AND and XOR gates and the single-gate random-oracle model of Januzelli, Rosulek and Roy [jrr25][jrr25] are not formalized here.

### Free XOR

[Primitives/Garbling/FreeXOR.lean](../../CslibFrontier/Crypto/Primitives/Garbling/FreeXOR.lean) is the free-XOR technique of Kolesnikov and Schneider [ks08][ks08]. It is a separate construction from the scheme above: it reuses `encode` and `decode` but has its own tables, evaluation and views. A Boolean `free` on the gates marks the XOR gates, and the hypothesis `hfree` says that each marked gate computes the sum in `Bool` of its arguments, for any arity. Labels live in `K × Bool` for an additive group `K` with `k + k = 0` (hypothesis `hK`). One secret offset `δ` links the two labels `W` and `W + (δ, true)` of every wire (`label`). A free gate has no garbled rows (`card_garbledRow`): its zero label is the sum of its arguments' zero labels (`propagate`), so the sum of their active labels is its active label (`label_add_label`, `sum_label`). Every other gate of arity `a` has `2 ^ a` point-and-permute rows masked by `Σₖ H (key of argument k) (tw slot)` for a hash `H : K → T → K × Bool`. `Garbled.run_garbleWith` proves exact correctness for every hash, tweak map, offset and base labelling.

Privacy rests on circular correlation robustness, which Choi, Katz, Kumaresan and Zhou [ckkz12][ckkz12] introduced to prove free XOR secure; [ks08][ks08] relied on a random oracle. [Primitives/Garbling/CorrelationRobust.lean](../../CslibFrontier/Crypto/Primitives/Garbling/CorrelationRobust.lean) follows the tweakable form of Guo, Katz, Wang and Yu [gkwy20][gkwy20]. The oracle `circular H δ` answers `(x, t, b)` with `H (x + δ) t`, plus `(δ, true)` when `b` is set, and `CorrelationRobust.advantage` is the advantage of telling it, under a uniform offset, from a uniform random function in the finite PRF game. `FreeXOR.advantage_realGame_simGame` states that the advantage of every distinguisher `D` between `realGame` and `simGame` equals `CorrelationRobust.advantage H (reduction C I H tw x D)`, assuming `hfree`, `hK` and that `tw` is injective. The simulator `simulate` sees only the topology, `free`, `H`, `tw` and the output, and `View.run_simulateWith` shows that its views decode to the output. The proof is one exact step with no hybrid. Against the circular oracle the reduction builds the real view; against a random function every row other than the one named by the active colours is uniform, which is the simulated view. The reduction asks one query per slot of the garbled table (`isQueryBounded_reduction`), at that slot's tweak (`reductionQuery_tweak`). With injective `tw` it never repeats a tweak, so it never asks both `(x, t, false)` and `(x, t, true)`, as [gkwy20][gkwy20] require of adversaries; `advantage` itself does not impose this restriction, and `circular_sub_circular` shows why it matters. As above, the statement is single-instance and running time is not tracked. Checked instances are in [CslibFrontierTests/Crypto/FreeXOR.lean](../../CslibFrontierTests/Crypto/FreeXOR.lean).

[Primitives/Garbling/MixedModulus.lean](../../CslibFrontier/Crypto/Primitives/Garbling/MixedModulus.lean) and [Primitives/Garbling/BMR16.lean](../../CslibFrontier/Crypto/Primitives/Garbling/BMR16.lean) garble mixed-modulus arithmetic circuits in the style of Ball–Malkin–Rosulek [bmr16][bmr16]. A `MixedModulusCircuit` is a typed straight-line program whose wires carry residues modulo per-sort moduli. Addition and multiplication by a constant are free, and a projection gate `ℤ_m → ℤ_n` sends `m - 1` ciphertexts after row reduction. `Garbled.run_ofKeys` proves correctness for every hash, tweak map, offsets and zero labels. Privacy rests on mixed-modulus circular correlation robustness (`MixedModulusCCR`). `advantage_realGame_simGame` shows that the advantage of any distinguisher between the real view and a view simulated from the circuit's shape and output equals the `ccrAdvantage` of an explicit reduction, which is legal (`reduction_isLegal`), assuming distinct gate tweaks. Legality is relaxed from the paper's Definition 1, which requires distinct tweaks on all queries: the reduction asks `m - 1` queries under one gate tweak, so a legal adversary here must avoid `a = 0` and must not ask two different queries with the same tweak, source sort, label and `a`, along every run. `MixedModulusCCR` is therefore a stronger assumption than Definition 1 as stated. Decoding uses the colours of the output zero labels instead of the paper's hashed decoding table, `Mult_c` is allowed for every constant, and the statement is concrete and single-instance with no cost bounds, as above. Checked instances are in [CslibFrontierTests/Crypto/GarblingBMR16.lean](../../CslibFrontierTests/Crypto/GarblingBMR16.lean).

### Arithmetic garbling of switch systems

[Primitives/Garbling/Switch/Basic.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Switch/Basic.lean), [Switch/Garble.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Switch/Garble.lean) and [Switch/Oblivious.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Switch/Oblivious.lean) formalize a bounded part of Heath's garbled switch systems [heath24][heath24]; `import CslibFrontier.Crypto.Primitives.Garbling.Switch.Oblivious` brings in all three. A `SwitchSystem n m N R` is a list of affine gates, switches and joins over one commutative ring `R` (§3.2, Definition 4). It is a constraint system rather than a straight-line program: `SwitchSystem.Satisfies` describes satisfying assignments, `SwitchSystem.solve` finds wire values by propagation, and `SwitchSystem.solve_sound` shows that every value it finds agrees with every satisfying assignment. Garbling (§3.3, Construction 1 and Figure 2) uses arithmetic free-XOR labels `K w + v • Δ` in an `R`-module `L`, with an offset `Δ` of colour `1` under an additive colour map `col : L →+ ZMod 2`.

Correctness is relative to propagation. `Switch.evaluate_garbleWith` shows that, for a well-formed system and any assignment `σ` satisfying it, the garbled evaluator finds a label on exactly the wires on which `solve` finds a value, and that label encodes the value. `Switch.Garbled.run_garbleWith` decodes only output wires whose value is a bit `0` or `1`. Heath's legality condition (Definition 6, a unique satisfying assignment found by propagation) is replaced by an arbitrary satisfying assignment, gates have a single output, and affine gates propagate forward only.

`Switch.advantage_realGame_simGame` is the fixed-instance obliviousness statement. For a fixed well-formed system, satisfying assignment and distinguisher, the advantage between the evaluator's real view and the view that `Switch.simulate` builds from the control bits `S.controls σ` equals the `CCR.advantage` of an explicit reduction, which never repeats a tweak (`Switch.isTweakUnique_reduction`). The assumption is an arithmetic circular correlation robustness: the keyed oracle answers `(k, t, s)` with `H (k - Δ) t + s • Δ`. Heath's proof (Appendix A, Theorem 4 and the hybrids of Figure 4) assumes the Boolean form of Definition 1, and no implication between the two is formalized. The simulator is given the control bits, so the statement allows the view to leak them. Heath's simulation of the control bits for oblivious randomized switch systems is omitted, as are authenticated output decoding (decoding here is by colour only), adversary-chosen systems and inputs, and running-time bounds.

The checked client [CslibFrontierTests/Crypto/GarblingSwitch.lean](../../CslibFrontierTests/Crypto/GarblingSwitch.lean) builds a five-gate multiplexer over `ZMod 4`. It checks that the system is well formed and satisfiable on both control values, that propagation and garbled decoding give the expected outputs by computation, and that both theorems apply. The obliviousness theorem is applied to a toy hash that is not correlation robust. Build it with `lake build CslibFrontierTests.Crypto.GarblingSwitch`.


### Half gates

[Primitives/Garbling/HalfGates.lean](../../CslibFrontier/Crypto/Primitives/Garbling/HalfGates.lean) is the half-gates scheme of Zahur, Rosulek and Evans [zre15][zre15], for circuits over the XOR–AND basis `HalfGates.signature`. It is a separate construction from the point-and-permute scheme above and does not reuse its tables. Labels live in `K × Bool` for a finite additive group `K` with `k + k = 0`. A global offset `Δ = (R, true)` links the two labels `W w` and `W w + Δ` of every wire. XOR gates are free in the sense of Kolesnikov and Schneider [ks08][ks08]: they need no ciphertext. Each AND gate sends two ciphertexts, the generator half and the evaluator half, so the table is indexed by `Slot C` with two entries per AND gate (`card_slot`). `andEval_active` is the half-gates identity for one gate. `Garbled.run_garbleWith` proves exact correctness for every hash `H : K × Bool → T → K × Bool`, tweak map, offset key and choice of input zero labels, and `Garbled.run_of_mem_support` covers the randomized `garble`. Labels are the unique fixed point of one evaluation round (`IsLocal.iterate_eq_of_isFixed`), reached after `n + C.size` rounds.

[Primitives/Garbling/HalfGates/Privacy.lean](../../CslibFrontier/Crypto/Primitives/Garbling/HalfGates/Privacy.lean) proves simulation privacy. The simulator `simulate` sees the circuit and its output; it samples uniform input labels and a uniform table, and `View.run_simulateWith` shows that its views decode to the output. Security rests on circular correlation robustness, in the whole-label form of [CorrelationRobust.lean](../../CslibFrontier/Crypto/Primitives/Garbling/CorrelationRobust.lean) above, because the half-gates hash reads the colour bit: the oracle `circularLabel H R` answers `(a, t, b)` with `H(a + Δ, t) + bΔ` and must look like a random function, and `advantageLabel` is the advantage of telling it, under a uniform offset key `R`, from a uniform random function in the finite PRF game. A hash that ignores the colour gives back the key-only oracle `circular` of Free XOR (`circularLabel_fst`). `advantage_realGame_simGame` states that the advantage of every distinguisher `D` between `realGame` and `simGame` equals `CorrelationRobust.advantageLabel H (reduction C H tw x D)`, assuming `tw` is injective. The reduction builds the table gate by gate and queries each slot once, at its own tweak. Against the keyed oracle it produces the real table, by the half-gates identity; against a random function its table is uniform (`map_oracleTable`). Circular correlation robustness only constrains adversaries that never query both `(a, t, 0)` and `(a, t, 1)`. The reduction satisfies this, but the condition is not formalized. As above, the statement is single-instance, and running time is not tracked. Checked instances are in [CslibFrontierTests/Crypto/HalfGates.lean](../../CslibFrontierTests/Crypto/HalfGates.lean).

### One-hot garbling for lookup tables

The lookup-table garbling `logrow` of Heath–Kolesnikov–Ng [hkn24][hkn24] builds on the one-hot garbling of Heath–Kolesnikov [hk21][hk21] and works with Free-XOR labels [ks08][ks08] in an additive group `L` of characteristic two (`[Module (ZMod 2) L]`): the label of bit `b` with zero-label `G` is `G + bitOffset Δ b` for a global offset `Δ`. [Primitives/Garbling/OneHot.lean](../../CslibFrontier/Crypto/Primitives/Garbling/OneHot.lean) has the one-hot algebra. `tableMulBits_oneHot` is Lemma 1 of [hkn24][hkn24] (the transposed truth table times the one-hot vector of `x` is row `x`), `tableMul_bitOffset` is Free-XOR linearity of the labelled product, and `tableMul_oneHotLabels` is the labelled form displayed after Lemma 1: labels of a one-hot vector give labels of the selected row.

[Primitives/Garbling/BinaryToOneHot.lean](../../CslibFrontier/Crypto/Primitives/Garbling/BinaryToOneHot.lean) is the binary-to-one-hot conversion `bin-to-hot` of Heath [heath24][heath24] (§4.1, p. 14), which provides the one-hot interface of Figure 1 of [hkn24][hkn24]. It turns one label on each of `n + 1` input wires and `n` ciphertexts into labels of the one-hot vector of the input. Each doubling step hashes the current zero-labels `G j` to `y j`, keeps `G j + y j` and `y j` as the two halves `h′ + h` and `h′` of Heath's step, and sends one ciphertext `b + ∑ j, y j` for the join with the new bit. This is a factor of two smaller than the GGM-tree conversion of [hk21][hk21] (§4.1, p. 10), which sends two encrypted values per level and a final correction. The `n` ciphertexts are the `(n − 1)κ` term of Theorem 1 of [hkn24][hkn24], whose `n` is `n + 1` here; Figure 1 of [hkn24][hkn24] states the `(2n − 1)κ` of [hk21][hk21] instead. The positions are bit vectors and each doubling step extends them with `Fin.snoc`. `evaluate_garble` proves correctness for every tweakable hash `H`, tweak map `tw`, offset and zero-labels, and `tableMul_evaluate_garble` composes it with the table product. The evaluator's index is taken as given; in `logrow` it is the input masked by permutation bits.

[Primitives/Garbling/BinaryToOneHotObliviousness.lean](../../CslibFrontier/Crypto/Primitives/Garbling/BinaryToOneHotObliviousness.lean) proves obliviousness of the gadget in the sense of [bhr12][bhr12]: the simulator sees only `n`. This is the gadget's part of the proof of Theorem 3 of [hkn24][hkn24]. The reduction is original to the library: it is an exact finite reduction for Heath's single-ciphertext step, not the proof of [hk21][hk21], which treats the GGM-tree construction. The assumption is circular correlation robustness in the form of Definition 1 of [hkn24][hkn24], stated as the finite PRF game for `ccrOracle H δ`, which answers `(X, τ, b)` with `H (X + Δ) τ + bitOffset Δ b`. `advantage_realGame_simGame_eq` shows that the advantage between the real view (input labels and ciphertexts) and uniform labels and ciphertexts *equals* the advantage of `reduction H tw n x D`, provided different doubling steps use different tweaks. The reduction makes one query per step (`isQueryBounded_reduction`), at a fresh tweak each time, so it never asks the same `(X, τ)` with both bits. The bound is meaningful only for such legal adversaries; legality is documented, not formalized. The random-function side uses `uniformOfFintype_bind_bind_adaptiveUpdate` from [Probability/PMF/Uniform.lean](../../CslibFrontier/Probability/PMF/Uniform.lean): the value at a query point chosen from the function itself can be resampled because resampling it does not move the point. The random-function garbling of `logrow`, the complete gate with its material count `2ⁿm + (n − 1)κ + nmκ`, and its obliviousness, privacy and authenticity remain open. Checked instances are in [CslibFrontierTests/Crypto/GarblingOneHot.lean](../../CslibFrontierTests/Crypto/GarblingOneHot.lean).

### Yao's two-party protocol

[Protocols/MPC/Yao.lean](../../CslibFrontier/Crypto/Protocols/MPC/Yao.lean) runs Yao's protocol [yao86][yao86] in the form analysed by Lindell–Pinkas [lp09][lp09], inside the synchronous MPC framework. The circuit is `C : Circuit σ (n₀ + n₁) m`. Party `0`, the garbler, holds `x₀ : Fin n₀ → Bool`, and party `1`, the evaluator, holds `x₁ : Fin n₁ → Bool`. The garbler samples uniform keys and permutation bits (`sampleGarblerCoins`), garbles `C`, and sends a `YaoMessage`: the table, the labels of its own input bits and the decoding bits. One call to the ideal batched oblivious transfer `batchOTSpec n₁ (K × Bool)` of [Protocols/MPC/BatchOT.lean](../../CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean) then gives the evaluator the labels of its own bits. This oracle is `n₁` parallel 1-out-of-2 transfers of values in an arbitrary type, the `k = 2` case of Goldreich's 1-out-of-`k` OT (Section 7.3.2, Eq. 7.20) [goldreich04][goldreich04]. The evaluator evaluates and decodes. `yaoFunctionality C I` gives the evaluator `C.eval I (Fin.append x₀ x₁)` and the garbler nothing.

- `yao_output_of_mem_support`: exact correctness in every run, for every `F` and `tw`.
- `idealJoint_yao_garbler`: perfect privacy against the garbler, whose OT answer is `()`. The simulator `yaoGarblerSim` samples fresh coins, and `semiHonestAdvantage_yao_garbler` restates this as zero advantage.
- `semiHonestAdvantage_yao_evaluator_le`: privacy against the evaluator. The simulator `yaoEvaluatorSim` places the garbling simulator's view, computed from the topology and the evaluator's output, into the evaluator's `PartyView`. The advantage of every distinguisher `D` is at most `Σ_{j < n₀ + n₁ + C.size} PRF.advantage F (reduction C I F tw (yaoInput x) D' j)`, where `D' = yaoEvaluatorDistinguisher …` is the induced distinguisher on garbled views. The bound requires injective `tw`. `semiHonestAdvantage_yao_evaluator_le_mul` gives `(n₀ + n₁ + C.size) · ε`.

The advantage notion is `semiHonestAdvantage proto W f I S x D` in [Protocols/MPC/Advantage.lean](../../CslibFrontier/Crypto/Protocols/MPC/Advantage.lean). It is the `Game.advantage` of a randomized test `D` on the coalition's views and all outputs, between `idealJoint` and `Protocol.realJoint`. This replaces the computational indistinguishability of Goldreich's Definitions 7.2.1 and 7.5.1 by a concrete, per-instance quantity. `semiHonestAdvantage_eq_zero_iff` shows that it vanishes for every `D` exactly when the two joint laws are equal, and `PerfectSemiHonestPrivate.semiHonestAdvantage_eq_zero` specializes this to perfect privacy. `singletonView` and `restrict_singleton` handle the singleton coalitions of the two-party case.

Scope limits:

- The oblivious transfer is the ideal oracle, and no composition theorem replaces it with an OT protocol.
- The bounds are single-instance, with no security parameter.
- Running time is not tracked, and neither the simulators nor the reductions are certified efficient.
- Only the evaluator gets an output.

Checked instances are in [CslibFrontierTests/Crypto/Yao.lean](../../CslibFrontierTests/Crypto/Yao.lean): a one-gate AND circuit decoded by computation, with correctness, garbler privacy and the evaluator bound with `tw = id`. That file also checks the advantage on the perfectly private XOR protocol, and shows that every simulator for a leaky protocol has a coalition, input and distinguisher with positive advantage.

### IKNP oblivious-transfer extension

[Protocols/MPC/IKNP.lean](../../CslibFrontier/Crypto/Protocols/MPC/IKNP.lean) runs the oblivious-transfer extension of Ishai, Kilian, Nissim and Petrank [iknp03][iknp03]: `m` transfers of values in a finite additive group `L` from one call to `batchOTSpec κ (BitString m)`, with the roles reversed (`iknpRoleReversal` sends slot `0`, the base sender, to party `1`, the extension's receiver). Party `0`, the sender, holds pairs `X : Fin m → Bool → L`; party `1`, the receiver, holds choice bits `r : Fin m → Bool`. The receiver offers the columns `(tⁱ, tⁱ + r)` of a uniform matrix `T` (`iknpColumns`), the sender chooses with a uniform `s` and sends `X j b + H j (qⱼ + b s)` (`iknpMasked`), and the receiver subtracts `H j tⱼ`. The functionality is `batchOTFunctionality m L` from [Protocols/MPC/BatchOT.lean](../../CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean), so the protocol realizes the same batched transfer it consumes, for `m` values instead of `κ`. The hash family `H : Fin m → BitString κ → L` is assumed correlation robust in the sense of [Primitives/CorrelationRobust.lean](../../CslibFrontier/Crypto/Primitives/CorrelationRobust.lean): `CorrelationRobust.advantage H A` compares `(t, fun j => H j (t j + s))` with `(t, u)` for uniform `s`, `t` and `u`.

- `iknp_output_of_mem_support`: exact correctness in every run, for every `H`; the key identity is `iknp_mask_input`.
- `idealJoint_iknp_sender`: perfect privacy against the sender, whose columns `tⁱ + sᵢ r` are uniform for every `s` and `r`; `semiHonestAdvantage_iknp_sender` restates it as zero advantage.
- `semiHonestAdvantage_iknp_receiver`: the advantage of every distinguisher `D` against `iknpReceiverSim` *equals* `CorrelationRobust.advantage H (iknpReduction H x D)`, since the unchosen entries are masked by `H j (tⱼ + s)` with `s` hidden.

The scope limits of Yao's protocol apply: the base transfers are the ideal oracle, the statements are single-instance, efficiency is not tracked, and only semi-honest corruption is covered. Checked instances are in [CslibFrontierTests/Crypto/IKNP.lean](../../CslibFrontierTests/Crypto/IKNP.lean), including a constant hash family with positive correlation-robustness advantage.

### Three-message DDH oblivious transfer

[Protocols/MPC/DDHOT.lean](../../CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean) formalizes a variant of the three-message 1-out-of-2 oblivious transfer protocol over a finite additive group `G` of exponent dividing `q` generated by `g` ([bs23][bs23], Section 23.5.7, Figure 23.17, Theorem 23.7, and Remark 23.6; DDH-based OT of this kind goes back to [np01][np01]) as a plain-world (`noOracleWorld`) two-party protocol `ddhOTProtocol g q` computing `otFunctionality G` (compatible with `batchOTSpec 1 G` in [Protocols/MPC/BatchOT.lean](../../CslibFrontier/Crypto/Protocols/MPC/BatchOT.lean)). Unlike Figure 23.17—where the sender samples `d ← G` without its discrete logarithm, encrypts both branches under one shared exponent, and performs no check—here in round 1 the sender (`0`) samples `a : ZMod q` and sends `u = a.val • g` (retaining `a`); in round 2 the receiver (`1`) samples `b : ZMod q`, sets `v = b.val • g`, and sends `ddhOTReceiverMsg g σ b u` (`(u - v, v)` if `σ` else `(v, u - v)`, satisfying `w₀ + w₁ = u`); in round 3 the sender checks `w₀ + w₁ = u` (Remark 23.6) and encrypts each branch `i ∈ {0, 1}` with its own fresh randomization coins `(rᵢ, sᵢ) : ZMod q × ZMod q` via `ddhOTEncryptBranch g u wᵢ mᵢ rᵢ sᵢ a` (which collapses to ElGamal encryption under `wᵢ` with exponent `rᵢ + a * sᵢ`, sending zeros if the check fails), and the receiver decrypts the chosen branch as `c_σ - b.val • e_σ` (`ddhOTReceiverOutput`).

- `ddhOT_output_of_mem_support`: exact correctness (`r.2 = otOutputs x`) in every supported execution of `ddhOTProtocol g q`.
- `idealJoint_ddhOT_sender` and `semiHonestAdvantage_ddhOT_sender`: under `∀ y : G, q • y = 0`, the simulator `ddhOTSenderSim g q` matches the corrupted sender's real joint distribution identically, giving `semiHonestAdvantage = 0` against every distinguisher `D`.
- `semiHonestAdvantage_ddhOT_receiver_eq`: under `Fintype.card G = q` and generator surjectivity `∀ y : G, ∃ k : ZMod q, k.val • g = y`, the corrupted receiver's distinguishing advantage against `ddhOTReceiverSim g q` equals `Cslib.Crypto.DDH.advantage g q (ddhOTReduction g q x D)` (defined in [DiffieHellman/Finite.lean](../../CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean)) via the one-instance reduction `ddhOTReduction`.
- `ddhOTSenderReply_eq_unchecked_of_add`, `ddhOTSenderReply_eq_zero_of_add_ne`, `ddhOTAttackBothMessages_eq`, `succProbability_ddhOTUncheckedIdealGame_le`, and `ddhOTUnchecked_malicious_receiver_advantage`: `ddhOTUncheckedProtocol` omits the `w₀ + w₁ = u` check ([bs23][bs23], Section 23.5.7.3, Remark 23.6), and in `ddhOTUncheckedRealGame` a deviating receiver sending `ddhOTAttackMsg g b₀ b₁ = (b₀.val • g, b₁.val • g)` against `ddhOTSenderReplyOf (ddhOTUncheckedProtocol g q)` recovers both `(m₀, m₁)` with probability `1`, whereas in `ddhOTUncheckedIdealGame S` any simulator `S` that freely chooses one query bit `τ` and receives only `m_τ` outputs `(m₀, m₁)` on uniform `(m₀, m₁) ← G × G` with probability at most `(Fintype.card G : ℝ)⁻¹`, giving distinguishing advantage at least `1 - (Fintype.card G : ℝ)⁻¹`.

Scope limits: the DDH game (`Cslib.Crypto.DDH.realGame`, `Cslib.Crypto.DDH.randomGame`, `Cslib.Crypto.DDH.advantage` in [DiffieHellman/Finite.lean](../../CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean)) is single-instance over a fixed finite group `(G, g, q)` rather than a security-parameter family (`PrimeOrderGroupFamily.DDH` in [DiffieHellman.lean](../../CslibFrontier/Crypto/Computational/DiffieHellman.lean)); simulators and reductions carry no `IsPPT` / `ComputableInPolyTime` certificates; and the unchecked-protocol separation is a standalone simultaneous-recovery game rather than a general malicious-security or UC realization. Checked `ZMod 5` instances are in [CslibFrontierTests/Crypto/DDHOT.lean](../../CslibFrontierTests/Crypto/DDHOT.lean).

### Arithmetic garbling foundations

The modules under [Primitives/Garbling/Arithmetic](../../CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/AffineLabel.lean) formalize the information-theoretic layer of arithmetic and mixed garbling following Applebaum–Ishai–Kushilevitz [aik11][aik11] and Li–Liu [ll24][ll24]. An arithmetic wire carrying `x : R` has the affine label `affineLabel k s x = k + x • s`; in [ll24][ll24] the slope is a global offset. With a shared slope, sums and public linear combinations of labels are labels (`affineLabel_add_affineLabel`, `sum_smul_affineLabel`), and a slope with a unit coordinate makes the label determine `x` (`affineLabel_injective`). The multiplication gadget `mulEncodeWith` is an explicit instance of the degree-two affinization notion of [aik11][aik11] (Definitions 4.2 and 4.5, Fact 5.1), simulated from the output label as in [ll24][ll24] Section 3.1; it splits the label of `x * y` into two values affine in `x` and two affine in `y`; `decode_mulEncodeWith` is its correctness and `eval_mulEncode` its perfect privacy against the simulator `mulSimulate`, which sees only the output label. [BitComposition.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/BitComposition.lean) defines bit decomposition and composition over `ℤ/p^k` (`bitComp_bitDecomp`) and the linear bit-composition gadget of [ll24][ll24] Section 4.1 (Figure 5, Lemma 4), with additive pads over the ring in place of XOR pads: `linCompEval_linCompTable` is its correctness for arbitrary pads, and `eval_activeShares` shows that the unpadded active rows are a uniform additive sharing of the output label, reusing `ProbComp.sampleAdditiveShares`. Digits are the existing `Cslib.Radix.digit`; the lemmas added for it are in [Foundations/Data/Nat/Radix/Digit.lean](../../CslibFrontier/Foundations/Data/Nat/Radix/Digit.lean). [Foundations/Data/Nat/ConstantDivision.lean](../../CslibFrontier/Foundations/Data/Nat/ConstantDivision.lean) proves the multiply-and-shift identity `Nat.mul_div_pow_eq_div`, a radix-`p` variant of Granlund–Montgomery [gm94][gm94] Theorem 4.2 in the form of [ll24][ll24] Lemma 5, and [ConstantDivision.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/ConstantDivision.lean) uses it for the exactness of division and remainder by a constant `N` in `ℤ/p^(2k+1)` on inputs below `p ^ k` (`constDiv_eq_div`, `constMod_eq_mod`), as in [ll24][ll24] Section 4.2. [CRT.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Arithmetic/CRT.lean) shows that the CRT combination of the residues of `x` modulo pairwise coprime `m i` is `x` modulo `∏ i, m i` (`crtSum_modEq`), never exceeds `(∏ i, m i - 1) ^ 2` (`crtSum_le_sq`), and is reduced to `x mod ∏ i, m i` by `constMod` when `(∏ i, m i) ^ 2 ≤ p ^ k` (`constMod_crtSum`), following [ll24][ll24] Section 5 for arbitrary pairwise coprime moduli. The bound uses `Nat.sum_sub_one_le_prod_sub_one` from [Foundations/Data/Nat/BigOperators.lean](../../CslibFrontier/Foundations/Data/Nat/BigOperators.lean).

These are building blocks, not a garbling scheme: the random-oracle pads that hide inactive rows, key extension, the Boolean–arithmetic conversion gadgets as garbled tables, and an end-to-end privacy theorem for mixed circuits are not formalized. Checked instances are in [CslibFrontierTests/Crypto/GarblingArithmetic.lean](../../CslibFrontierTests/Crypto/GarblingArithmetic.lean).

## Upstream perfect secrecy and sharing

Pinned cslib supplies [PerfectlySecret](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean#L76): observing any positive-probability ciphertext leaves every message prior unchanged. Its equivalent ciphertext-distribution formulation and one-time-pad instance are finite semantic security, with no PPT restriction. The upstream commitment interface separately defines perfect/statistical hiding and perfect binding [cslib][cslib].

[Scheme](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean#L52) bundles deterministic reconstruction for authorized coalitions, a randomness PMF, monotone authorization and equal unauthorized-coalition view laws across all secrets. Shamir's `schemeWith` permits a tail sampler with the translation symmetry needed for privacy; `uniformTailSampler` gives the usual finite-field instance. These are reusable information-theoretic interfaces; the survey does not infer a polynomial-time protocol or a secret-sharing-to-native-MPC compiler from them.

The quantum one-time pad ([OneTimePad.lean](../../CslibFrontier/Crypto/Protocols/Quantum/OneTimePad.lean)) is the quantum counterpart: the key-averaged ciphertext state is the same for every plaintext state, even given an entangled reference system. It is stated with density matrices rather than through `PerfectlySecret`; see [Density matrices, no-signalling and the quantum one-time pad](../circuits-logic-and-other-models/algebraic-and-quantum.md#density-matrices-no-signalling-and-the-quantum-one-time-pad).

Perfect secrecy, zero knowledge and semi-honest MPC privacy do not substitute for differential privacy's adjacent-dataset comparison, which the next section formalizes.

## Differential privacy

[DifferentialPrivacy/Basic.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/Basic.lean) defines `DifferentiallyPrivate Adj M ε δ` for a mechanism `M : D → PMF R`: for all `Adj`-adjacent datasets `x`, `y` and every set `S` of outputs, `Pr[M x ∈ S] ≤ exp ε · Pr[M y ∈ S] + δ`, with `ε : ℝ`, `δ : ℝ≥0∞` and events measured by `PMF.toOuterMeasure` [DworkRoth2014, Definition 2.4][dworkroth14]. The adjacency relation is an explicit parameter; [DifferentialPrivacy/Hamming.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/Hamming.lean) supplies `HammingAdjacent` (datasets `ι → X` differing in at most one row), the neighbor relation of Ghosh–Roughgarden–Sundararajan [grs12][grs12]. Dwork–Roth's own adjacency is `ℓ₁` distance one between histograms, which is another instance of the parameter, not something these files define. The definition quantifies over ordered pairs, so a symmetric guarantee needs a symmetric relation.

- **Characterizations and post-processing:** `DifferentiallyPrivate.iff_tsum_tsub_le` characterizes the optimal `δ` as the hockey-stick excess `∑ r, (M x r - exp ε · M y r)`, and `iff_apply_le` makes pure privacy a pointwise likelihood-ratio bound. `bind` and `map` give post-processing by an arbitrary randomized or deterministic map (Dwork–Roth Proposition 2.1).
- **Composition:** [DifferentialPrivacy/Composition.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/Composition.lean) proves `DifferentiallyPrivate.bind_pair`, which releases a first output and a second output from a mechanism chosen from the first, at `(ε₁ + ε₂, δ₁ + δ₂)` (Dwork–Roth Theorem B.1, which states equal parameters), and its non-adaptive case `prod` (Theorem 3.16). `adaptiveComposition M k` runs `k` rounds, each choosing its mechanism from the previous outputs. `DifferentiallyPrivate.adaptiveComposition` sums per-round parameters that may depend on the round (Corollary B.2 fixes them).
- **Advanced composition:** [DifferentialPrivacy/AdvancedComposition.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/AdvancedComposition.lean) proves `DifferentiallyPrivate.advancedComposition`, Dwork–Roth Theorem 3.20: if every round of `adaptiveComposition M k` is `(ε, δ)`-private for a symmetric adjacency relation, the transcript is `(√(2k ln (1/δ')) ε + k ε (e^ε - 1), k δ + δ')`-private for every `δ' > 0`. Lean's `Real.log (1 / 0) = 0`, so `δ' = 0` (where the source reads `ln (1/0) = ∞`) is excluded. The proof replaces the source's KL-divergence and Azuma argument with a moment bound. [DifferentialPrivacy/PrivacyLoss.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/PrivacyLoss.lean) defines `lossMoment t p q = ∑ a, p a · (p a / q a) ^ t` and proves Markov's inequality (`tsum_indicator_le_lossMoment`). It bounds the moment of an `ε`-close pair by a convexity (chord) argument (`lossMoment_le_of_le_mul`, `lossMoment_le_exp`), and `exists_le_of_tsum_tsub_le` splits an `(ε, δ)`-close pair into `ε`-close sub-probability parts that keep all but `δ` of the mass. The moments multiply along the transcript (`lossMoment_transcriptWeight_le`), and `k` rounds lose at most `k δ` of the mass (`one_le_tsum_transcriptWeight_add`). This yields the sharper linear term `k ε tanh (ε / 2) = k ε (e^ε - 1) / (e^ε + 1)` of Kairouz–Oh–Viswanath Theorem 3.4 [kov17][kov17] (`advancedComposition_sqrt`, with failure probability `k δ + δ'`; `tanh (ε / 2) ≤ e^ε - 1` recovers Theorem 3.20), and `advancedComposition_tanh` keeps a free slack parameter. `advancedComposition_experiment` is the composition experiment of Definition 3.7: a randomized adversary chooses, from its coins and the previous outputs, two adjacent inputs and an `(ε, δ)`-private mechanism in every round, and its view (coins and all outputs) is private in the challenge bit. `advancedComposition_of_target` is Corollary 3.21 under the explicit hypothesis `ε₀ ≤ 8 ln (1/δ')`. The source assumes only `0 < ε₀ < 1`; its proof also needs `ε₀ ≤ 4 ln (1/δ')`, and without such a condition the corollary fails (for example `k = 1`, `ε₀ = 0.9`, `δ' = 0.999`, with randomized response reporting the true bit with probability `e^ε / (1 + e^ε)` at the prescribed per-round `ε ≈ 10.06`).
- **Group privacy:** `DifferentiallyPrivate.hammingDist_le` gives `(k ε, ∑ i < k, exp (i ε) · δ)` at Hamming distance `k`. `hammingDist_le_of_pure` is the `(k ε, 0)` case, the Hamming form of Dwork–Roth Theorem 2.2, and `hammingDist_le'` is the footnote's `k exp ((k - 1) ε) δ` bound, for `0 ≤ ε`.
- **Randomized response:** [DifferentialPrivacy/RandomizedResponse.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/RandomizedResponse.lean) writes the two-coin protocol as a `ProbComp Bool` program. `differentiallyPrivate_randomizedResponse_iff` proves it `(ε, 0)`-private exactly when `ln 3 ≤ ε` (Claim 3.5; tightness is proved here). `differentiallyPrivate_randomizedResponseSurvey` shows the `n`-respondent survey (`OracleComp.pi`) is `(ln 3, 0)`-private for Hamming adjacency, via the product of local randomizers `DifferentiallyPrivate.pi`. `sum_eval_randomizedResponseSurvey_mul_estimator` proves that `2 · (fraction of Yes) − 1/2` is unbiased (§2.3).
- **Geometric and discrete Laplace noise:** [DifferentialPrivacy/DiscreteLaplace.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/DiscreteLaplace.lean) defines `twoSidedGeometric α` with masses `(1 - α) / (1 + α) · α ^ |z|` [grs12][grs12] and `discreteLaplace t` with ratio `exp (-1 / t)` [CanonneKamathSteinke2020, Definition 28][cks20]. `addNoise q noise` releases an integer query plus noise. For a query of real sensitivity `Δ`, `differentiallyPrivate_addNoise_twoSidedGeometric` gives `(Δ · ln α⁻¹, 0)` and `differentiallyPrivate_addNoise_discreteLaplace` gives `(ε, 0)` at scale `Δ / ε` (CKS Lemma 29). `discreteLaplace_toOuterMeasure_Ici` and `discreteLaplace_toOuterMeasure_Iic` give CKS Lemma 30's exact tails `exp (-ε (m - 1)) / (exp ε + 1)`. `twoSidedGeometric_toOuterMeasure_le_natAbs` gives the two-sided accuracy `2 α ^ m / (1 + α)`.
- **Exponential mechanism:** [DifferentialPrivacy/ExponentialMechanism.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/ExponentialMechanism.lean) defines `exponentialMechanism u Δ ε` on a finite nonempty range, with masses proportional to `exp (ε u(x, r) / (2 Δ))` (Dwork–Roth Definition 3.4). `differentiallyPrivate_exponentialMechanism` proves `(ε, 0)`-privacy when `u` has sensitivity at most `Δ > 0` in the dataset (Theorem 3.10). With `optUtility` and `optSet` for the optimum and its maximizers, `exponentialMechanism_toOuterMeasure_utility_le_opt_sub` is Theorem 3.11 and `exponentialMechanism_toOuterMeasure_utility_le_opt_sub_log_card` is Corollary 3.12.
- **AboveThreshold and Sparse:** [DifferentialPrivacy/AboveThreshold.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/AboveThreshold.lean) defines `aboveThreshold ρ ν T as` (Algorithm 1), which returns the index of the first answer reported above threshold, and `aboveThresholdMechanism` on datasets. The noise is integer-valued, so the results are discrete-noise analogues of Dwork–Roth's continuous-Laplace theorems; queries and threshold stay real. `DifferentiallyPrivate.aboveThresholdMechanism` gives `(ε₁ + ε₂, 0)` for any threshold and query noise whose masses change by at most `exp ε₁` and `exp ε₂` under integer shifts by `s` and `2 s`, generalizing Theorem 3.23. `differentiallyPrivate_aboveThreshold_discreteLaplace` instantiates discrete Laplace scales `2 Δ / ε` and `4 Δ / ε` for queries of integer sensitivity `Δ : ℕ`, `Δ ≥ 1`. For sensitivity-`1` queries and scales `2 / ε`, `4 / ε`, `aboveThreshold_discreteLaplace_toOuterMeasure_not_thresholdAccurate_le` bounds by `β` the probability that the output violates `ThresholdAccurate` (Definition 3.9) for `α = 8 (ln (k + 1) + ln (2 / β)) / ε` on `k` answers, and `aboveThreshold_discreteLaplace_toOuterMeasure_not_accurate_le` adds that an accurate run does not halt early (Theorem 3.24, with `k + 1` for `k`). `sparse ρ ν T qs c` is Algorithm 2 on an adaptively chosen stream: `c`-fold `adaptiveComposition` of AboveThreshold, where the round after history `h` runs on the queries `qs h`; within a round the analyst sees only `⊥`s, so this covers deterministic adaptive analysts. `differentiallyPrivate_sparse_discreteLaplace` is the `δ = 0` case of Theorem 3.25, and `sparseStream fs` is the fixed-stream instance. Randomized analysts (mixtures over the analyst's coins) and infinite streams (finite prefixes) are reduced in prose only.
- **Lower bounds:** [DifferentialPrivacy/Packing.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/Packing.lean) proves the packing bound `DifferentiallyPrivate.card_mul_le`: if `M` is `(ε, δ)`-private for an adjacency relating a centre `x₀` to datasets `x j` (`j ∈ J`) with pairwise disjoint events `B j` and `Pr[M (x j) ∈ B j] ≥ p`, then `|J| · p ≤ exp ε + |J| · δ`. Group privacy turns this into `card_mul_le_of_hammingDist_le` for datasets within Hamming distance `m` of `x₀`, with `|J| · p ≤ exp (m ε)` for pure privacy (`card_mul_le_of_hammingDist_le_of_pure`). `log_two_mul_le_of_hammingDist_le` is the Hamming form of Dwork–Roth Lemma 8.4, which they credit to Hardt and Talwar and state for histograms at `ℓ₁` distance: `ln 2 · (s - 1) ≤ Δ ε`. `two_pow_mul_le_of_oneWayMarginals` and `log_two_mul_le_of_oneWayMarginals` are Theorem 8.7. An `(ε, 0)`-private mechanism that answers all `k` one-way marginals (`oneWayMarginals`) of every dataset of `n` rows with error below `n / 2` (`accurateMarginals`) with probability `p` satisfies `2 ^ k · p ≤ exp (n ε)`, so `(k - 1) ln 2 ≤ n ε` at `p = 1 / 2`. [DifferentialPrivacy/Reconstruction.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/Reconstruction.lean) proves Theorem 8.1 (Dinur–Nissim, as credited by Dwork–Roth). Answers to all subset-count queries (`subsetCount`) with distortion at most `E` (`SubsetCountsWithin`) let the adversary `reconstruct` recover the database in all but `4 E` rows (`hammingDist_reconstruct_le`). The privacy consequence is a standard derivation, not a numbered source theorem. `mul_sum_sum_toOuterMeasure_le` pairs databases differing in one bit to show that an `(ε, δ)`-private guesser recovers on average at most `n (exp ε + δ) / (1 + exp ε)` bits. `mul_card_sub_mul_le` turns this into `(1 + exp ε) (n - t) q ≤ n (exp ε + δ)` for a guesser that lands within distance `t` with probability at least `q` on every database. `card_mul_one_sub_le_of_subsetCountsWithin` gives `n (1 - δ) ≤ 4 E (1 + exp ε)` when the answers have distortion at most `E` with probability one on every database. So the distortion a private mechanism can guarantee uniformly over all databases is linear in `n`. This is not a bound on a single database: a constant mechanism is `(0, 0)`-private and answers exactly on the database it was built from.
- **Lower bound over a small universe:** [DifferentialPrivacy/SmallUniverse.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/SmallUniverse.lean) proves a row-replacement form of Dwork–Roth Theorem 8.8, which they credit to De. `exists_symmetric_query_forall_exists_half_lt` takes a universe `X` of `d ≥ 33` items, `k ≥ 2`, `ε ∈ (0, 1 / 18]` and `n ≥ min (k, d) / ε` rows. It provides a query `F : (ι → X) → (Fin k → ℝ)` that is invariant under reordering the rows (so it is a query of the histogram) and changes by at most `1` per coordinate between Hamming-adjacent datasets. Every `(ε, 0)`-private mechanism then has `ℓ∞` noise at least `min (k, d) / (1024 ε)` with probability more than `1 / 2` on some dataset. The packing form `exists_symmetric_query_two_pow_mul_le` gives `2 ^ L · p ≤ exp (t L ε)` whenever `L ≤ k`, `16 L < d` and `t L ≤ n`. The proof encodes a Gilbert–Varshamov code over `16` letters (`Cslib.Code.exists_two_pow_le_card_and_le_two_mul_hammingDist`) as datasets with `t` rows per coordinate. It separates them with McShane extensions (`exists_symmetric_lipschitz_extension`) of the histogram excess `countExcess`, the number of rows of one dataset with no match in another, and applies `card_mul_le_of_hammingDist_le_of_pure`. Dwork and Roth's proof uses `k` random `± 1` combinations of bump functions and a Chernoff bound. Labelling the codewords by `L ≤ k` bits makes the query deterministic, since `ℓ∞` separation needs only one coordinate per pair. This simplifies the proof and does not change the theorem. Scope: adjacency replaces one of exactly `n` rows, while Dwork and Roth add or remove a row of a histogram of weight at most `n`. An `(ε, 0)`-private mechanism for their adjacency is `(2 ε, 0)`-private for this one; since `2 ε ≤ 1 / 18` whenever `ε ≤ 1 / 40`, this would cover their full range with noise `min (k, d) / (2048 ε)`. The transfer also needs the query extended from weight-`n` histograms to all of `ℕ ^ d`, where McShane's extension in `ℓ₁` with constant `1 / 2` works; it is not formalized. Their proof implicitly needs `min (k, d) ≥ 400`. The query is not a counting query: Dwork and Roth use the theorem to separate counting queries from arbitrary sensitivity-`1` queries.
- **Reconstruction from random `±1` queries:** [DifferentialPrivacy/RandomReconstruction.lean](../../CslibFrontier/Privacy/DifferentialPrivacy/RandomReconstruction.lean) proves Dwork–Roth Theorem 8.2, which they credit to Dwork, McSherry and Talwar, with the constant `((⌊α⌋₊ + 1) / η) ^ 2` in place of their `(2 α / η) ^ 2`. Databases and queries are sign vectors `ι → Bool` read through `signVal`, and `signDot v d` is the answer to the query `v`. `AnswersWithin A y d α η` says that the answers `y` to the queries `A : κ → ι → Bool` are within `α` on at least a `1 / 2 + η` fraction; the other answers are arbitrary. For `m ≥ b n` uniformly random queries on `n` rows, `toOuterMeasure_exists_le_hammingDist_reconstructSigned_le` bounds by `exp (-n (η b / 4 - ln 3))` the probability that, for some database `d` and some answers within `α` on a `1 / 2 + η` fraction, the adversary `reconstructSigned` misses `d` in `((⌊α⌋₊ + 1) / η) ^ 2` or more positions. The bad event depends only on the queries (`ReconstructionFails`, of probability at most `3 ^ n exp (-η m / 3)` by `toOuterMeasure_reconstructionFails_le`), so the guarantee holds against every curator. The proof combines the Erdős–Littlewood–Offord bound, the library's Chernoff bound for product distributions and a union bound over the `3 ^ n` disagreement patterns. For `α ≥ 1 / 2` we have `⌊α⌋₊ + 1 ≤ 2 α`, so this implies Dwork and Roth's form (`toOuterMeasure_exists_lt_hammingDist_reconstructSigned_le_of_half_le`). For small `α` their constant is false: `exists_answersWithin_answersWithin_hammingDist_eq_two` shows that for any `m ≥ 10` queries on at least two rows, two databases at Hamming distance `2` both fit some answers exactly on a `7 / 10` fraction, so whenever `2 α < η ≤ 1 / 5` every attack errs in at least one position on some database with fitting answers (`exists_answersWithin_lt_hammingDist`). The source's application of its Lemma 8.3 drops the lemma's `+ 1`, which the parity of `∑ i, v_i z_i` compensates exactly when `α ≥ 1 / 2`. Whether the source's constant holds for `η / 2 ≤ α < 1 / 2` is not settled. The floor constant corrects the source and is not claimed as a new result. The privacy consequence is a standard derivation through `mul_card_sub_mul_le`, following the source's remark that if differential privacy is meaningful, lower bounds for preventing blatant non-privacy also apply to private mechanisms. Good queries exist once `3 ln 3 · n < η m` (`exists_not_reconstructionFails`). For them, an `(ε, δ)`-private mechanism whose answers are within `α` on a `1 / 2 + η` fraction with probability at least `q` on every database satisfies `(1 + exp ε) (n - ((⌊α⌋₊ + 1) / η) ^ 2) q ≤ n (exp ε + δ)` (`mul_card_sub_mul_le_of_answersWithin`). With probability one this gives `n (1 - δ) ≤ ((⌊α⌋₊ + 1) / η) ^ 2 (1 + exp ε)` (`exists_forall_card_mul_one_sub_le_of_answersWithin`), so error `o(√n)` is impossible. The adversary is not efficient: it searches all `2 ^ n` databases.

Model boundaries: mechanisms are compared through their exact output laws. Randomized response is a finite `ProbComp` program, but the geometric and discrete Laplace distributions have infinite support, so they are ideal `PMF ℤ` laws, not finite fair-coin programs. Sampling cost, finite-precision error and computational (PPT) differential privacy are not modelled. The cost of sampling the exponential mechanism is not modelled either. Sparse for `δ > 0` (which needs advanced composition combined with AboveThreshold), continuous Laplace/Gaussian mechanisms, Rényi or concentrated privacy accounting and private learning remain open under the *Differential privacy and adaptive data analysis* direction of [ROADMAP.md](../../ROADMAP.md). Run `scripts/build.sh CslibFrontierTests.Privacy.DifferentialPrivacy CslibFrontierTests.Privacy.SparseVector CslibFrontierTests.Privacy.AdvancedComposition --wfail --iofail` to check the clients. The [foundations clients](../../CslibFrontierTests/Privacy/DifferentialPrivacy.lean) cover a constant mechanism that is `(0, 0)`-private, the identity on bits, which is private for no `ε` when `δ < 1`, randomized response's failure at `ε = 1`, survey group privacy and `k`-fold composition, concrete Hamming adjacency in both directions, the count query's sensitivity under both noise mechanisms, and the masses and tails of the ratio-`1/2` geometric distribution. The [selection and sparse-vector clients](../../CslibFrontierTests/Privacy/SparseVector.lean) cover the exponential mechanism on a count utility, Dwork–Roth's best-of-two bound `2 exp (-c ε / 2)` (Example 3.6), AboveThreshold on count queries (two copies of a query cost no more than one), Sparse with cutoff `2` on a fixed stream and with cutoff `3` on a history-dependent stream, AboveThreshold on no queries, the accuracy condition holding and failing on concrete answers, and Theorem 3.24's combined accuracy and no-early-halting statement on a concrete pair of answers. The [advanced-composition clients](../../CslibFrontierTests/Privacy/AdvancedComposition.lean) cover `k` rounds of randomized response in the Theorem 3.20 and `tanh` forms (`tanh (ln 3 / 2) = 1 / 2`), a genuinely approximate round (randomized response plus a leak releasing a `true` input with probability `δ`, which is `(ln 3, δ)`-private but `(ε, 0)`-private for no `ε`), Corollary 3.21 at `k = 10000`, `δ' = e^{-32}`, where per-round privacy `1 / 1600` gives total `ε = 1` but basic composition gives only `25 / 4`, and a randomized adaptive adversary in the composition experiment. Run `scripts/build.sh CslibFrontierTests.Privacy.LowerBounds --wfail --iofail` to check the [lower-bound clients](../../CslibFrontierTests/Privacy/LowerBounds.lean). They cover the packing bound for one-respondent randomized response, accuracy of exact marginals and the empty-dataset edge case, a constant mechanism that the marginals bound shows inaccurate, exact reconstruction from exact answers, the failure of exact subset counts to be `(ε, δ)`-private for `δ < 1`, and randomized response attaining the bit-guessing bound `3 / 4`. Run `scripts/build.sh CslibFrontierTests.Privacy.SmallUniverse --wfail --iofail` to check the [small-universe clients](../../CslibFrontierTests/Privacy/SmallUniverse.lean). They cover the histogram excess ignoring row order (excess `0` at Hamming distance `2`) and detecting different histograms, satisfiable hypotheses for Theorem 8.8 (`80` rows, `33` items, `k = 2`, `ε = 1 / 40`), and the theorem applied to a constant mechanism. Run `scripts/build.sh CslibFrontierTests.Privacy.RandomReconstruction --wfail --iofail` to check the [random-query reconstruction clients](../../CslibFrontierTests/Privacy/RandomReconstruction.lean). They cover `signDot` on concrete sign vectors, exact answers fitting and an answer off by one not fitting, a failure probability below `1` for `20` queries per row at `η = 1 / 2`, both with the floor constant and in Dwork and Roth's form at `α = 1 / 2`, the failure of the source's constant at `α = 0` and at `α = 1 / 20`, `η = 1 / 5` for every choice of `10` queries on `2` rows, and `1500` queries on `60` rows that no `(1, 0)`-private mechanism answers exactly on `3 / 4` of them with probability one.

## Universal composability with static corruptions

[Protocols/UC/Machine.lean](../../CslibFrontier/Crypto/Protocols/UC/Machine.lean) defines interactive machines (`Machine I E`): a `ProbComp` initial-state sampler and, for each query of the exported interface `E`, an activation in `StateT State (ProbOracleComp I)`. `Machine.comp` composes machines, `Machine.link` runs a program against a machine (removing the exported interface), and `Machine.IsBounded t` bounds the calls of the sampler and of every activation by `t`, counting private samples and imported calls alike. [Protocols/UC/Execution.lean](../../CslibFrontier/Crypto/Protocols/UC/Execution.lean) builds the UC execution of [Canetti](../sources.md#canetti20) on these machines: an `n`-party `Protocol` is a closed machine per security parameter `κ` and corruption set `C` with a party port and a network port, `IdealFunctionality.toProtocol` turns a functionality into a protocol whose network port is its backdoor, `corruptRouter C` lets the environment reach only honest parties on the party port and routes corrupted parties' party-port calls to the adversary, and `exec π A C Z κ z` is the environment's output bit as a `ProbComp Bool` program. [Protocols/UC/Emulation.lean](../../CslibFrontier/Crypto/Protocols/UC/Emulation.lean) defines concrete emulation `EmulatesWithin π φ g ε` (every adversary with per-activation budget `pA` has a simulator with budget at most `g` at `κ + pA κ` and advantage at most `ε pA pZ κ` against every environment with total budget `pZ κ`), the asymptotic `Emulates π φ` (one negligible bound per environment budget), both reflexive and transitive, and their ideal-functionality specializations `RealizesWithin` and `Realizes`.

[Protocols/UC/Linking.lean](../../CslibFrontier/Crypto/Protocols/UC/Linking.lean) proves the package-algebra laws: linking is associative as an equation of programs (`Machine.link_comp`), the forwarding machine is a unit (`Machine.link_id`), and call budgets of compositions and links compose (`Machine.IsBounded.comp`, `Machine.isQueryBounded_link`). [Protocols/UC/DummyAdversary.lean](../../CslibFrontier/Crypto/Protocols/UC/DummyAdversary.lean) uses them for completeness of the dummy adversary: running an adversary `A` is running `dummyAdversary` with `A` absorbed into the environment (`exec_eq_exec_dummy`), so a simulator for the dummy adversary yields the black-box simulator `compSim S_D A` for every `A` (`EmulatesDummyWithin.emulatesWithin`, with the error evaluated at the absorbed environment budget `absorbPoly pZ pA`), and the same module gives the negligible-error equivalence `emulates_iff_emulatesDummy`. Examples are in [CslibFrontierTests/Crypto/UCDummyAdversary.lean](../../CslibFrontierTests/Crypto/UCDummyAdversary.lean).

[Protocols/UC/Composition.lean](../../CslibFrontier/Crypto/Protocols/UC/Composition.lean) proves the universal composition theorem for one subroutine instance. A `HybridProtocol` is a protocol whose machines also call the party port of a subroutine; `compose ρ σ` answers those calls with the protocol `σ` behind `corruptRouter C`, for the same parties and corruptions, and exposes `σ`'s routed network port beside `ρ`'s own, so `compose ρ F.toProtocol` is the `F`-hybrid protocol. `Emulates.compose` shows that if `π` UC-emulates `φ` then `compose ρ π` UC-emulates `compose ρ φ` for every hybrid protocol `ρ` with a polynomial budget (`HybridProtocol.PolyBounded`), and `Realizes.compose` and `Realizes.compose_trans` specialize it to replacing an ideal functionality by a protocol that realizes it. The proof absorbs `ρ` into the environment (`absorbHybrid`, with budget `absorbPoly pZ pρ`): the real side is an equation of programs (`exec_compose_dummy`), and the ideal side, with the composed simulator `hybridSim S`, has the same output distribution (`eval_exec_compose_hybridSim`); the concrete forms `EmulatesDummyWithin.compose` and `EmulatesWithin.compose` record the simulator budgets and the error evaluated at the absorbed environment budget. Several subroutine sessions, dynamically created sessions and the hybrid argument over sessions are not covered. Examples are in [CslibFrontierTests/Crypto/UCComposition.lean](../../CslibFrontierTests/Crypto/UCComposition.lean).

When using these definitions, keep the model boundaries in view. Corruption is static and fixed per session, a session is one closed machine, and messages are pulled by the receiving machine rather than scheduled by the adversary. Moreover, `corruptRouter C` itself only redirects party-port inputs and outputs for `i ∈ C` from the environment to the adversary; stronger corruption power (such as Byzantine state exposure or arbitrary message injection, as in Canetti) exists only insofar as `π κ C` implements it by inspecting `C`, so a protocol independent of `C` is tested only against party-port input/output substitution. Budgets count oracle calls, not running time, so `EmulatesWithin`, `Emulates`, `RealizesWithin` and `Realizes` are statistical/ideal-model notions against interaction-bounded but computationally unbounded adversaries, simulators and environments: protocols whose security rests on computational assumptions generally cannot satisfy `Realizes`, and UC security against polynomial-time machines needs an additional machine-realizability restriction. The environment's budget is a polynomial in `κ` alone and does not grow with its auxiliary input. Concrete transitivity requires the second error to be monotone in the adversary's budget. Checked examples, including an environment that separates two ideal functionalities against every simulator and a check of static-corruption routing, are in [CslibFrontierTests/Crypto/UC.lean](../../CslibFrontierTests/Crypto/UC.lean).

## State-separating proofs

[Protocols/SSP/Basic.lean](../../CslibFrontier/Crypto/Protocols/SSP/Basic.lean) reads the machines of the previous section as the packages of state-separating proofs ([Brzuska, Delignat-Lavaud, Fournet, Kohbrok and Kohlweiss](../sources.md#bdfkk18)): `Machine.comp` is sequential composition and `Machine.link_comp` is its associativity. `parFin M` runs the packages `M j : Machine I E` side by side as `m` independent sessions, each on its own state, behind the tagged interface `sessionSpec m E`, and `par M₁ M₂` runs two packages side by side behind `E₁ ⊕ₒ E₂`. `advantage A M₀ M₁` is the advantage of an adversary `A : ProbOracleComp E Bool` in distinguishing two closed packages. `advantage_comp` moves a reduction package into the adversary, `advantage_le_sum_range` is the hybrid bound along a sequence of closed packages, and `eval_run_eq_of_represent` equates the output distributions of two closed packages when every state of the first is represented by a state of the second, compatibly with initialization and with every activation.

[Protocols/SSP/Hybrid.lean](../../CslibFrontier/Crypto/Protocols/SSP/Hybrid.lean) proves the multi-session hybrid bound `advantage_parFin_le_sum`: the advantage between `parFin real` and `parFin ideal` is at most the sum over the sessions `j` of the advantage of `hybridDistinguisher real ideal A j` between `real j` and `ideal j`, and `advantage_parFin_le_mul` turns a uniform single-session bound `ε` into `m * ε`. Each hop is an equality (`advantage_hybridFamily_succ`): the reduction `hybridReduction j₀` runs every session other than `j₀` itself, each on its own persistent state, and forwards the session `j₀` to the package under attack. When the sessions import a global package `G` that the environment also queries directly, as in universal composability with global setup ([Canetti, Dodis, Pass and Walfish](../sources.md#cdpw07)), `globalWorld P G` is the world of the sessions and `eucWorld Q G` is the world of one session. `advantage_globalWorld_le_sum` bounds the advantage between `globalWorld real G` and `globalWorld ideal G` by the sum of the single-session advantages between `eucWorld (real j) G` and `eucWorld (ideal j) G`; the reduction `globalReduction j₀` routes the calls of the sessions it runs itself to `G` through its own import.

These are exact statements about advantages: running time and call budgets are not tracked, so the efficiency of the single-session distinguishers (each is the original adversary linked with a reduction package) has to be argued separately. Checked examples, including adversaries that separate the real and the ideal sessions with advantage `1` and instances of both hybrid bounds, are in [CslibFrontierTests/Crypto/SSP.lean](../../CslibFrontierTests/Crypto/SSP.lean).

## Private information retrieval

[PIR/Basic.lean](../../CslibFrontier/Crypto/Protocols/PIR/Basic.lean) formalizes one-round information-theoretic private information retrieval [cgks98][cgks98] (Definition 1). A database is `x : ι → Bool`, replicated on the servers `S`. A `Scheme ι S R Q A` has a query generator `query i : ProbComp (R × (S → Q))` that returns a retained user state and one query per server, deterministic answers `answer s x : Q → A`, and a reconstruction `reconstruct i r : (S → A) → Bool`. `IsCorrect` asks the user's output law `ProbComp.eval (P.run x i)` to be `PMF.pure (x i)` for every database and index; `isCorrect_iff` restates this on the support of the queries. `IsPrivate` asks the law of each server's query (`serverQuery s i`) to be the same for all indices. Both are exact equalities of laws. The coins are a `ProbComp` program, so they are uniform choices from finite ranges, which include the source's uniform bit strings. `communication S Q A = |S| (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉)` counts a fixed-length binary encoding of each query and answer, and `HasScheme ι k c` asserts a correct, private `k`-server scheme with at most `c` bits. `Scheme.rows` is the generic transformation of §3.4 (restated as Proposition 4 in §4.1): the user queries the column and each server answers once per row; its communication (`communication_rows`) is computed only for one-bit answers. `Scheme.comap` restricts a scheme along an embedding of indices, padding the database with `false`.

- **Single server** ([PIR/SingleServer.lean](../../CslibFrontier/Crypto/Protocols/PIR/SingleServer.lean), §5.1): `Scheme.exists_injective_answer` finds a query on which the answer map `x ↦ answer x q` is injective, so `two_pow_card_le_card_answer` gives `2 ^ n ≤ |A|` and `card_le_communication` gives `n ≤ communication`. Sending the whole database (`download`) matches it, and `hasScheme_one_iff` says a one-server scheme with `c` bits exists exactly when `n ≤ c`.
- **Interactive single server** ([PIR/Interactive.lean](../../CslibFrontier/Crypto/Protocols/PIR/Interactive.lean), §5.1): an `InteractiveScheme ι C D` is a deterministic two-party protocol tree (`Communication.Protocol`) between the server (Alice), holding the database and coins `d : D`, and the user (Bob), holding the index and coins `c : C`. Both sets of coins are `ProbComp` programs, and the user's coins may depend on the index. The transcript is the leaf reached. `IsPrivate` asks the law of the transcript to be the same for all indices, on every database. This is weaker than privacy of the server's whole view, and the proofs use it only through supports. Leaves are labelled by functions of the user's view `(i, c)`, because an output that depended on the transcript alone would, by privacy, have the same law for all indices. The source's step that the user's output is determined by the communication is therefore replaced by the rectangle property (`Protocol.leaf_eq_iff`). `injective_leaf` shows that, for fixed coins, the transcript determines the database. So `two_pow_card_le_ncard_transcripts` gives at least `2 ^ n` possible transcripts for each index, `two_pow_card_le_leafCount` at least `2 ^ n` leaves, and `card_le_depth` protocol depth at least `n` (the worst-case number of bits over all branches of the protocol tree, reachable or not). The server sending its database (`InteractiveScheme.download`) has depth `n`, and `InteractiveScheme.exists_iff` says a scheme of protocol depth at most `c` exists exactly when `n ≤ c`.
- **Two-server linear summation** ([PIR/LinearSummation.lean](../../CslibFrontier/Crypto/Protocols/PIR/LinearSummation.lean), §5.2): `Scheme.IsLinearSummation` covers two-server schemes whose queries are sets, whose answers are parities `x ⬝ᵥ q`, and whose output is the sum of the two answers. `twoServer` is one (`isLinearSummation_twoServer`). With correctness, the two queries add up to `eᵢ` (`IsLinearSummation.query_add_query`). With privacy, `IsLinearSummation.mem_support_add` (the Claim) shows that every set at even (resp. odd) Hamming distance from a set possible for a server is possible for that server (resp. the other one). So `two_pow_le_ncard_support` gives each server at least `2 ^ (n - 1)` sets, and `card_sub_one_le` gives `n - 1 ≤ ℓ` for any encoding by `ℓ`-bit strings that is injective on them. The even-set scheme `evenTwoServer h₀` draws a uniform set of even size. It is correct and private, and it attains the bound: `ncard_support_evenTwoServer` gives exactly `2 ^ (n - 1)` sets, and `exists_injOn_evenTwoServer` encodes them in `n - 1` bits, with one encoding for every index, as the note closing §5.2 says. Only linear-summation schemes are covered.
- **Subcube schemes** ([PIR/Cube.lean](../../CslibFrontier/Crypto/Protocols/PIR/Cube.lean), §§3.1, 3.2, 3.4): `twoServer` sends a uniform set `t` and `t + eᵢ` and adds the two parities (`BitString.hadamardCode`). `isPrivate_twoServer` and `isCorrect_twoServer` prove it private and correct, `communication_twoServer` gives `2 (n + 1)` bits, and `query_add_query_twoServer` shows that the two servers together learn `i`. `cube D ι` is the `2 ^ d`-server scheme for the cube `D → ι`, with `communication_cube` giving `2 ^ d (d ℓ + 1)` bits. `hasScheme_two_of_le_mul_self` gives two servers with `4 m` bits for `n ≤ m²` (Corollary 3 with `m = ⌈√n⌉`), and `hasScheme_two_pow_of_le_pow` gives `2 ^ d` servers with `2 ^ d (d ℓ + 1)` bits for `n ≤ ℓ ^ d`.
- **Covering codes** ([PIR/CoveringCode.lean](../../CslibFrontier/Crypto/Protocols/PIR/CoveringCode.lean), §3.3): a `RadiusOneCover S D M` gives each server `s` a codeword `code s : D → Bool` and directions `dir s r` for `r : M`. Its `cover` map assigns each word of `D → Bool` the server, and possibly the direction, that produce it, as in the footnote's exact cover of the cube by subsets of radius-`1` balls. The server `s` receives the query of `cube` for `code s`. It answers that query and, for each of its directions, all `ℓ` answers of the neighbour flipped there, since that neighbour's query differs only in one position of one set (`query_update_cube`). `isPrivate_scheme` inherits privacy from `cube`, and `isCorrect_scheme` recovers all `2 ^ d` answers of `cube`. With fixed-length answers, `communication_scheme` gives `k ((d + m) ℓ + 1)` bits for `k` servers and `m` directions. `communication_scheme_of_balanced` shows that this equals Theorem 1's `k + (2 ^ d + (d - 1) k) ℓ` when `k (m + 1) = 2 ^ d`, and `two_pow_card_le` is the volume bound `2 ^ d ≤ k (m + 1)`. `ofHammingDist` turns any radius-`1` covering code into a cover in which each server emulates all its neighbours, and `hasScheme_of_hammingDist` gives `k (2 d ℓ + 1)` bits. Corollary 2 uses the balanced covers `cubeThree` (`{000, 111}`) and `cubeFour` (`{0000, 1111, 1000, 0111}`): `hasScheme_two_of_le_pow_three` gives two servers with `12 ℓ + 2` bits for `n ≤ ℓ ^ 3`, and `hasScheme_four_of_le_pow_four` gives four servers with `28 ℓ + 4` bits for `n ≤ ℓ ^ 4`. Because answers have fixed length, Theorem 1 is covered for balanced covers only. (*Balanced* means `k (m + 1) = 2 ^ d`, so that `cover` is a bijection; this is a different notion from the source's balancing of user and server communication.) To use another code, build a `RadiusOneCover` on a concrete `Fin d → Bool` and discharge `coveredWord_cover` by `decide` (`coveredWord` is exposed for this), as `cubeThree` and `cubeFour` do, or apply `ofHammingDist` to a proof that the code has covering radius `1`.
- **From perfectly smooth codes** ([PIR/SmoothCode.lean](../../CslibFrontier/Crypto/Protocols/PIR/SmoothCode.lean), [yekhanin12][yekhanin12] Lemma 6.2): `ofDecoder` gives each read of a non-adaptive decoder (`Code.nonadaptive`, see the locally decodable codes section of the query and communication chapter) its own server. `isCorrect_ofDecoder_iff` and `isPrivate_ofDecoder_iff` reduce correctness to exact decoding of codewords and privacy to index-independent reads. `hasScheme_ofDecoder` gives `q` servers with `q (⌈log₂ N⌉ + ⌈log₂ |Γ|⌉)` bits when every read is uniform. The same uniformity makes the decoder smooth (`Code.isSmoothDecoder_nonadaptive_of_uniform`).

Model boundaries: privacy is against each single server, not coalitions (`t`-privacy). Multi-server schemes have one round; only the single-server lower bound covers interaction. Communication is fixed-length (or protocol depth), so it is a worst case over all executions. Block retrieval (§4), the converse from schemes to smooth codes and lower bounds for general (not linear-summation) two-server schemes are open under [ROADMAP.md](../../ROADMAP.md). The [checked examples](../../CslibFrontierTests/Crypto/PIR.lean) verify the reconstruction identity of the two-server scheme on three bits by `decide`. They also check the schemes on nine, ten and eight bits, the tight single-server bound on three bits, and a correct scheme that sends the index. That scheme communicates `3` bits for four bits and is therefore not private. They add a private scheme that is not correct, and the two-server scheme recovered from the Hadamard decoder. The [lower-bound examples](../../CslibFrontierTests/Crypto/PIRLowerBounds.lean) check:
  - the interactive download on three bits, and that no scheme on three bits sends only two;
  - a correct protocol in which the user sends its index (checked by `decide`), which uses three bits for four and is therefore not private;
  - the supports of `8` and exactly `4` sets for the basic and even-set schemes on three bits;
  - a correct linear-summation scheme that sends `∅` and `{i}`, which is therefore not private.

The [covering-code examples](../../CslibFrontierTests/Crypto/PIRCoveringCode.lean) check Corollary 2 on `27` and `81` bits. For `n = 2 ^ 30` they compare the `12 290` bits of the two-server covering-code scheme with the `131 076` bits of the `√n` scheme. They also check that both covers meet Theorem 1's count exactly, that `{0000, 1111}` is not a radius-`1` covering code, and that the volume bound rules out a one-server cover of the three-bit cube.

## Known Limitations

Only selected protocol endpoints and key definitions were traced. The source files themselves give detailed source mappings; this pass did not independently reconcile every textbook constant, lattice-abort construction or signature reduction. Existing regression tests are not newly executed evidence. The precise coalition and advice restrictions above should be retained even when summarizing the results compactly.

[aik11]: ../sources.md#aik11
[bcs16]: ../sources.md#bcs16
[bhr12]: ../sources.md#bhr12
[bmr16]: ../sources.md#bmr16
[bmr90]: ../sources.md#bmr90
[bs23]: ../sources.md#bs23
[cgks98]: ../sources.md#cgks98
[ckkz12]: ../sources.md#ckkz12
[cks20]: ../sources.md#cks20
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[dworkroth14]: ../sources.md#dworkroth14
[gkwy20]: ../sources.md#gkwy20
[gm94]: ../sources.md#gm94
[goldreich04]: ../sources.md#goldreich04

## One-shot tetrahedral random oblivious transfer

Import [Tetrahedral.lean](../../CslibFrontier/Crypto/Multiparty/Tetrahedral.lean) for
Beaver's STOC submission 1234, Theorem 4.1 (PDF p. 3). `shuffle` enumerates
all 24 permutations exactly once; `aliceTable` and `bobTable` are Figures 2–3.
Alice's ordered two-card hand and Bob's third card come from one uniform shuffle.
`correctness` proves that the selected bit is received, and `uniform_output`
gives each sender-bits/selection triple exactly three preimages, hence probability
$1/8$. `alice_privacy` and `bob_privacy` condition on complete views, including the
local hand, public announcement and outputs. Their count identities make the
selection or unselected bit exactly fair within every view fiber; zero-probability
views have zero counts on both sides.

The [checked client](../../CslibFrontierTests/PaperEndpointsBatchB.lean) reproduces
Figure 4 and a pair of Bob-indistinguishable shuffles with opposite hidden bits.
It also checks an obstruction to Section 5's reverse privacy assertion: given
Bob's card 0, the event that Alice has ordered hand (1,3) has probability $1/6$;
message X has probability $1/3$; their joint probability is $1/6$, not $1/18$.
Thus the reverse public announcement leaks hand information beyond the dealt
card. `reverse_message_leakage` in
[TetrahedralYield.lean](../../CslibFrontier/Crypto/Multiparty/TetrahedralYield.lean)
exports that obstruction as a named theorem.

For chosen-input OT, import
[TetrahedralChosen.lean](../../CslibFrontier/Crypto/Multiparty/TetrahedralChosen.lean).
Bob sends `choiceOffset`, the XOR of his random and desired selections. Alice
sends `chosenMasks`, two bits masking her chosen input pair with the appropriately
permuted random pair. `chosen_correctness` proves that Bob recovers his selected
input bit for every shuffle. `chosen_alice_privacy` equates full-view counts for
either receiver choice; `chosen_bob_privacy` equates them for any two input pairs
agreeing at the selected position. Views retain the original local hand, trit,
outputs and all conversion messages. The exact resource count is one shuffle,
one trit and three additional public bits. This is standalone passive privacy;
typed protocol substitution and the advertised circuit/MPC consequence remain
unproved for this implementation.

For larger decks, `rankHand`, `goodRanks`, `yield` and `expectedYield` in
`TetrahedralYield.lean` implement Section 10's successful-rank count for actual
permutations of $4m$ distinct cards and arbitrary hand-position sets.
`yield_le` and `expectedYield_le` prove $g\le m$ pointwise and in expectation.
`advertised_rates_exceed_bound` proves that both advertised constants,
$(9/32)n$ and $(81/256)n$ for $n=4m$, exceed this bound for every positive $m$.
Thus those quantitative claims in Theorems 10.1–10.2 (PDF p. 13) cannot describe
the protocol in Figure 31. This does not refute the weaker $\Theta(n)$ yield
claim. Its lower bound, parallel privacy, optimality and MPC consequences remain
unproved; the forward single-shuffle result is preserved.

## Exact signed correlation of Add/XNOR chains

Import [AddXNOR.lean](../../CslibFrontier/Cryptanalysis/AddXNOR.lean) for Wang,
Lv, Shen and Zhang's STOC submission 733, Theorem 4 (PDF p. 16).
`step` uses Lean's actual full-width `BitVec` modular addition or bitwise XNOR.
The sampler `word` is bijective from a high-part index and a two-bit index to
all words of width $h+2$ (`word_bijective`); uniform independent indices therefore
give a uniform word. `averageFrom` samples a fresh operand and fair operator at
each step and tracks the affine bit-1 approximation in parallel. It averages
$+1$ for agreement and $-1$ for disagreement, without taking absolute values.
`word_low` and `step_low` connect full-width sampling and operations to their
low two bits before the proof derives the recurrence.

`averageCorrelation_eq h k` gives $(k+2)/2^{k+1}$ for $k$ operators and $k+1$
operands. `averageCorrelation_source N m` uses the paper's $N,m\ge2$ parameters,
with $k=N-1$ and $h=m-2$ (word width $m-2+2=m$), yielding $(N+1)/2^N$.
The [client](../../CslibFrontierTests/PaperEndpointsBatchB.lean) checks full-width
operations and two-operand and longer-chain theorem applications.
These are uniform-ensemble signed expectations; they do not establish an absolute
correlation bound, a planted-instance statistic, NP-hardness or a search bound.

Import [AddXNORRuns.lean](../../CslibFrontier/Cryptanalysis/AddXNORRuns.lean) for
Theorem 3 (PDF pp. 15–16). `fixedCorrelation h bs` holds every operator fixed
while averaging independent uniform full-width operands. `runs zs` encodes
addition runs separated by XNORs, allowing zero runs and a final XNOR.
`exists_runs` represents every operator string this way after one extra XNOR;
`fixedCorrelation_append_xnor` proves that this extra step preserves correlation.
`fixedCorrelation_runs_cos` proves the exact product of
$(1/\sqrt2)^z\cos(z\pi/4)$ over the runs. `abs_runFactor_le` gives the per-run
decay bound and `runFactor_eq_zero_iff` characterizes zero factors by
$z\equiv2\pmod4$. The checked client includes a vanishing run and a negative
signed correlation. These results cover arbitrary strings and run lengths;
the general-bit extension is described below. They do not prove NP-completeness.

Import [AddXNORChain.lean](../../CslibFrontier/Cryptanalysis/AddXNORChain.lean) for
arbitrary-width forward and backward evaluation. `eval` consumes a list of
operator/operand pairs from an initial word; `backward` recovers the initial
word from a target. `eval_append_eq_iff` is the exact meeting criterion at any
cut. `eval_project` and `backward_project` commute with reduction to any lower
width, including width zero. `eval_eq_xor_parity_carries` expresses the output
as the XOR of all operands, the all-ones word for odd XNOR parity, and the
accumulated carries. `carryWord_bit` identifies each carry bit with Lean's
ripple-carry recurrence. For positive width, `solution_parity` forces the XNOR
parity of every zero solution. `unique_cut` proves uniqueness of the positional
prefix/suffix split; this is a property of this formulation, not an impossibility
result for other representations.

Import [AddXNORStripping.lean](../../CslibFrontier/Cryptanalysis/AddXNORStripping.lean)
for the common-power-of-two reduction (Lemma 4, PDF p. 7). `scaled s xs`
appends $s$ zero bits to each noninitial operand. `eval_scaled` factors the full
state into the stripped high chain and the initial low field, complemented
exactly at odd XNOR parity. `solvable_scaled_iff` quantifies over every free
operator string: zero is reachable precisely when the initial low field is zero
and the stripped instance has an even-parity zero solution, or the field is all
ones and the stripped instance has an odd-parity zero solution.
`eval_strip_eq_zero_iff` works directly from arbitrary words satisfying actual
divisibility by $2^s$, using extracted high and low fields. No carry or parity
invariant is assumed as a premise.

Import [AddXNORSwap.lean](../../CslibFrontier/Cryptanalysis/AddXNORSwap.lean) for
Theorem 6 (PDF pp. 19–20). `swap_collision n` proves that the equality
$(T+A)\mathbin{\mathrm{XNOR}}B=(T\mathbin{\mathrm{XNOR}}A)+B$, evaluated
on actual words of width $n+1$, has probability
$2(5/8)^n-(1/2)^n$ for independent uniform $T,A,B$.
`swap_collision_context` allows any common prefix and suffix. Operands outside
the window are fixed arbitrarily; bijectivity makes the statement true
conditionally on each such choice, and hence also under independent uniform
sampling of those operands. The proof derives the carry transition weights from
the three independent low bits and then solves the recurrence. Width one has
probability one; width two has 48 colliding triples out of 64.
The complete [client](../../CslibFrontierTests/AddXNOR.lean) checks these counts,
a noncollision, arbitrary context, backward projection, actual carries, both
stripping parity branches and an impossible low field.

Import [AddXNORDecay.lean](../../CslibFrontier/Cryptanalysis/AddXNORDecay.lean)
for all four parts of Theorem 5 (PDF pp. 17–18). `bitCorrelation m j bs`
fixes the operator list and averages independent uniform full-width operands,
comparing output bit $j$ with the same bit of the full affine model.
`bitCorrelation_runs` factors this signed correlation into `bitRunFactor m j z`
for every addition run. A fresh XNOR operand resets the state by an actual
permutation; run independence is derived rather than assumed. The bit-one API
agrees with the earlier experiment (`bitCorrelation_bit_one`).

For $m=(h+1)+j$, `bitRunFactor_spectrum h j z` gives
$2^{-j(z+2)}\sum_k |\lambda_k|^2\lambda_k^z$ for arbitrary run length $z$.
The sum is complex, with its imaginary part necessarily zero because the left
side is rational. The $2^j$ eigenvalues are `carryEigenvalue`; `carryEigenvalue_cot`
identifies them with $1-i\cot((2k+1)\pi/2^{j+1})$.
[AddXNORTransfer.lean](../../CslibFrontier/Cryptanalysis/AddXNORTransfer.lean)
derives the signed matrix entry $(-1)^{[s'<s]}$ from actual addition and proves
its full-word distribution bridge. [AddXNORSpectrum.lean](../../CslibFrontier/Cryptanalysis/AddXNORSpectrum.lean)
constructs the invertible geometric eigenvector matrix and its Fourier inverse;
`carry_diagonalization` and `signedMatrix_pow` are explicit matrix identities.
No spectral formula is an input hypothesis.

`abs_bitRunFactor_le` bounds each run by `bitDecay j` raised to its length,
where $\rho_j=1/(2^j\sin(\pi/2^{j+1}))$. `bitDecay_strictAnti`,
`bitDecay_one` and `tendsto_bitDecay` give strict decrease, $\rho_1=1/\sqrt2$
and limit $2/\pi$. For $j\ge1$, `abs_bitCorrelation_le_bit_one` bounds any
operator string by $(1/\sqrt2)^a$, where $a$ counts its additions.
`abs_bitRunFactor_bit_one_four` gives equality at every bit-one run length
$4t$. Extremality concerns the decay envelope, not pointwise comparison:
at length two bit one has correlation zero, while bit two has correlation
$-1/4$. The complete [spectrum client](../../CslibFrontierTests/AddXNORSpectrum.lean)
checks that distinction on actual words, high-bit independence, separated
higher-bit runs, matrix orientation, zero runs, zero width and quantified bounds.
The full-word spectrum requires $j<m$; its decay inequality includes $j=0$,
where $\rho_0=1$, while the uniform half-bit bound requires $j\ge1$.

## Add/XNOR hardness with an explicit encoding

Import [AddXNORNPComplete.lean](../../CslibFrontier/Cryptanalysis/AddXNORNPComplete.lean)
for Theorem 1 (PDF pp. 9–11), and
[AddXNORWidth.lean](../../CslibFrontier/Cryptanalysis/AddXNORWidth.lean) for
Corollary 2 (p. 12). `encInstance` encodes a unary width followed by framed
binary operands; leading zeros are implicit. `Decision` requires at least two
operands, with operand count equal to word width, and all operands fitting that
width. Its semantic predicate is `Solvable` on actual `BitVec` words, with every
operator free. The framed encoding and the source's fixed-width representation
have polynomially related lengths on these valid inputs.

`toAddXNOR` is a total map from binary Subset-Sum. It discards zero source
numbers, retains indexed repeated entries, rejects targets above the total,
and otherwise constructs the paper's $U_i=3\cdot2^{4i+2}$ and
$V_i=s_i2^K-U_i$, with $K=4r+2$. `guard_forces_pattern` and
`recover_guarded_chain` derive the forced gadget patterns from unrestricted
actual evaluation. `final_control` rules out a final XNOR and odd padding parity;
`subset_reduction_iff` then excludes modular aliasing and recovers a source
sublist. The desired map, hardness or a resource certificate is never a premise.
`toAddXNOR_mem_iff`, `toAddXNOR_polyTime` and `Decision_npComplete` connect
that construction to the library's existing Subset-Sum and NP APIs.

The width satisfies $n\le5L+3$ for source encoding length $L$;
`toAddXNOR_encoding_length_le` bounds encoded output length by
$2(5L+3)^2+3(5L+3)+1$. The reduction and verifier have actual native
`ComputableInPolyTime` certificates. `natEval_polyTime` certifies a fold with
at most $m$ binary bits of state after every step, and `natEval_toNat` connects
it to actual word evaluation. These certificates assert polynomial time and
space, without asserting the paper's sharper $O(n^2)$ verifier running time.

For two independent parameters, `WordDecision` permits $N\ge2$ and $m\ge1$.
`powerShape` checks $(m-1)^b<N^a\le m^b$ with integer arithmetic;
`powerShape_iff` proves its ceiling interpretation. `toPowerAddXNOR` pads the
same actual guard construction to $N=t^b$ and $m=t^a$. Its polynomial-time
certificate treats $a,b$ as fixed positive integers. `rational_width_npComplete`
quantifies over every rational $\delta>0$ and states NP-completeness with the
literal restriction $m=\lceil N^\delta\rceil$.

`threeSATToAddXNOR` composes the existing checked 3-SAT digit construction
with this map. It uses base eight with two unit slack numbers and target three,
rather than the manuscript's base ten, slack one/two and target four. Both
constructions are carry-free; the reused library proof handles repeated literals
and tautological clauses. `threeSATToAddXNOR_mem_iff` and
`threeSATToAddXNOR_polyTime` prove actual correctness and polynomial time;
`threeSATToAddXNOR_width_le` gives $n\le13(v+c)+3$, counting variables by
distinct occurrence, independently of their binary labels. This proves the first
conclusion of Theorem 2. Its sparsification/disjunction resource refinement is
still unproved for this map.

The complete [hardness client](../../CslibFrontierTests/AddXNORHardness.lean)
checks actual operands and both gadget choices, mixed-pattern rejection,
zero/repeated entries, empty input, out-of-range rejection, width one,
a non-dense 3-SAT variable label and rational-width padding. Start with the two
imports above; use the semantic equivalence to inspect a constructed instance,
and the separate polynomial-time theorem for a complexity-class reduction.

Import [AddXNORSearch.lean](../../CslibFrontier/Cryptanalysis/AddXNORSearch.lean)
for executable exact witness search at any cut. `meetSearch left right s t`
builds actual forward records and inverse suffix records, indexes the forward
states by all their bits in a binary trie, and scans suffix records for a match.
`meetSearch_sound` checks both witness lengths and actual evaluation;
`meetSearch_ne_none_iff` proves completeness. Duplicates retain one witness.
`meetSearch_operation_bounds` bounds full-word step calls, insertion-node
inspections and lookup-node inspections separately by a polynomial times
$2^h$ when both cut lengths are at most $h$; `half_cut_lengths` supplies the
ceiling-half cut. `meetSearch_trie_resources` bounds retained trie nodes too.
These are concrete operation/data-size bounds, **not** multitape bit-runtime
or peak working-space certificates: `BitVec` arithmetic, list administration,
key generation and witness storage still require that bridge. No desired runtime
is assigned as an annotation. The complete [search client](../../CslibFrontierTests/AddXNORSearch.lean)
checks successful and unsuccessful inputs, empty cuts, width zero and duplicate states.

Import [AddXNORReachability.lean](../../CslibFrontier/Cryptanalysis/AddXNORReachability.lean)
for the actual reachable-state decision program. Supply width-$m$ words as lists
of $m$ bits, low bit first, to `WordTable.decide`. `decide_correct` identifies
its answer with unrestricted `Solvable`; the complete
[resource client](../../CslibFrontierTests/AddXNORResources.lean) shows the imports,
bit order, successful and unsuccessful inputs, modular wrap and zero width.
The implementation pulls a binary truth table back through addition using a
ripple carry and through XOR by branch exchanges, then unions the two images.
It avoids full-word arithmetic primitives and exponential witness enumeration.

`decide_time_le` is derived from the actual recursive calls: for $q$ operands its
bound is $(m+1)(m+4)+q(29\cdot2^m+3m+3)+3m+2$. The `TimeM` annotations count
Boolean operation groups, list/table inspections and constructors in an immutable
pointer model. Constant-time allocation and projections, pointer sharing and
uncharged garbage collection are part of that model; the instrumentation counter
is uncharged. The annotations have not been compiled to native machine steps.
Pointers are not single bits. This is therefore an executable source-level cost
bound, not Observation 1's multitape bit-runtime or a peak-space certificate.
`decide_linear_table_work` derives the simpler $40(q+1)(m+1)2^m$ bound
in the same source model.
Do not use it as the missing native exact-algorithm endpoint.

For a native implementation, import
[AddXNORNativeResources.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeResources.lean)
and use `Native.encoded_answers` or `Native.encoded_time_space` in the
`Cslib.Cryptanalysis.AddXNOR` namespace. The complete
[native client](../../CslibFrontierTests/AddXNORNative.lean) starts from ordinary
`Data.init` input and proves actual flat-program halting, unrestricted
solvability and a bound on the full memory-access transcript. From the repository
root with the pinned Lean toolchain installed, first build its dependencies, then
check the client:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeResources
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNative.lean
```

The kernel evaluations should accept wraparound and XNOR cases, reject an
unreachable target, and handle three buffer exchanges, empty chains and width
zero. The generic examples cover arbitrary widths and operand lists.

`Native.encodeInput as s t` consists of width, initial word, target, operand
count and the actual operands. The standard input convention supplies the length
in cell 0; the program reads the four header words in cells 1--4 and the operands
starting at cell 5. Its 56 fixed instructions include the final halt. All header
reads, modulus construction, zero filling, table updates, buffer exchanges and
target lookup are charged. It retains two reusable Boolean arrays after the
input, with 18 registers and physical word width
$W=\lfloor\log_2(3\cdot2^m+2q+12)\rfloor+1$. The input-fit theorem is
unconditional on typed instances; no initial table, desired answer or runtime
bound is a premise. `encoded_time_space` derives at most $45(q+1)2^m$ native
instructions and at most $(6\cdot2^m+4q+42)W$ bits for accessed cells plus
registers. The storage proof bounds every cell ever accessed, including temporary
writes, rather than just the final changed cells.

These are standard-basis WordRAM instruction and word-storage bounds. A flag
occupies one $W$-bit word; it is not packed into one bit. No multitape bit-time
simulation, sorted-list output-sensitive bound, small-operand algorithm,
meet-in-the-middle native certificate or streaming dissection follows from this
array program. If using another input representation, provide the conversion
and charge it separately; the complete client uses the checked representation
above. The earlier pointer-table and class-counter interfaces retain their
stated source-level resource contracts.

Import [AddXNORClasses.lean](../../CslibFrontier/Cryptanalysis/AddXNORClasses.lean)
for forward/backward low-bit class counts and the exact `classBalance` maximum.
`WordTable.classCounters` and `WordTable.backwardCounters` compute all counts
by dynamic programming on the projected instance, preserving every indexed
operator string even when states coincide. `projected_classCounters` and
`projected_backwardCounters` connect those executable tables to the literal
classes; `computed_balance` verifies the max/min traversal that computes the
balance before full-width class lists are generated. The complete resource client
checks both projections, counter multiplicity and a concentrated balance example.
The recursive work bounds count natural additions/comparisons as arithmetic
operations; `classCounters_size_le` and `backwardCounters_size_le` prove that
the counters need at most $q+1$ bits. These facts do not supply a native bit-cost
or native streaming dissection resource certificate.

`mean_forwardClassCount` and `mean_backwardClassCount` give exactly $2^q/2^p$
for each fixed low-bit class at projection width $p\le m$. The former averages
the initial word, conditional on every operand; the latter averages the first
operand of a **nonempty** suffix, conditional on the remaining operands and
fixed target. Their uniform counterparts sample all those operands independently.
An empty suffix has no random operand and is excluded from the backward mean.
No independence between class sizes or bound on expected maximum balance follows.

Import [AddXNORNativeCounters.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeCounters.lean)
for native **forward** counter preprocessing. In namespace
`Cslib.Cryptanalysis.AddXNOR.Native.Counters`, `encoded_resources as s t`
starts with `Native.encodeInput (List.ofFn as) s t`, executes initialization and
every counting layer, and halts with the final array pointer in `Native.source`.
For every state $g$, the certified final memory cell contains `solutionCount as s g`.
Coincident predecessors are added twice. The target header word is read but does
not affect this all-states preprocessing. From the repository root after setup:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeCounters
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNativeCounters.lean
```

The complete [counter client](../../CslibFrontierTests/AddXNORNativeCounters.lean)
checks the generic certificate and actual kernel executions with repeated states,
wraparound, empty chains and width zero. Width zero with three operands returns
eight, illustrating why a Boolean reachable-state table is insufficient here.
The native instruction bound, including halt, is $43(q+1)2^m$.
The physical word width is
$W=\lfloor\log_2(3\cdot2^m+2q+2\cdot2^q+12)\rfloor+1$;
the counter value $2^q$ must fit even when $m=0$.
The complete accessed footprint plus registers is bounded by
$(43(q+1)2^m+18)W$ bits, using at most one accessed cell per charged
instruction. This is conservative but bounds every execution prefix without
allocating all $2^W$ possible addresses. Input memory is supplied under the
existing `Data.init` convention; all program reads and initialization stores are
charged. For a projected instance, this certificate begins with the already
projected input. For original-input projection and backward preprocessing, use
the following interface. The later `Driver.dissection_exec` endpoint composes
original-array counters with native selected-class search; its simultaneous
compiled-space resource theorem remains open.

Import [AddXNORNativeProjection.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeProjection.lean)
for native projection and both counter directions from the original-width input.
In namespace `Cslib.Cryptanalysis.AddXNOR.Native.Counters`, call
`encoded_projected_resources back hp as s t`, where `hp : p ≤ m`.
`encodeProjected p (List.ofFn as) s t` appends the projection width to the
standard full-width encoding. The native program copies low bits into a separate
operand interval. For `back = true`, it reverses the operands during that copy,
seeds the unchanged forward kernel at the complemented projected target, and
returns a table read at complemented addresses. For `back = false`, read the
returned table at ordinary low-bit addresses. The theorem identifies these cells
with `backwardClassCount` and `forwardClassCount`, respectively, including all
indexed collisions. The original input words and appended width survive.

From the repository root after the normal setup:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeProjection
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNativeProjection.lean
```

The complete [projection client](../../CslibFrontierTests/AddXNORNativeProjection.lean)
checks nonuniform forward/backward arrays from five-bit input projected to two
bits, reversal and wraparound, repeated states, the empty chain, the original
header/operand preservation, and width-zero multiplicity eight. No projected
array is installed by the host. `encodeProjected_fits` verifies every original
input word and the projection width against
$W=\lfloor\log_2(3\cdot2^p+2\cdot2^q+4q+2^m+30)\rfloor+1$.
`encoded_projected_resources` proves at most $77(q+1)2^p$ instructions,
including halt, and at most $(77(q+1)2^p+18)W$ bits of accessed cells plus
registers. Every execution prefix has bounded words and memory support covered
by at most $(77(q+1)2^p+q+24)W$ bits including registers and the entire initial
input, even cells never read. This support bound uses actual stores and initial
support, not the largest representable address; the accessed-cell bound also
charges zero-filled cells. Both bounds are deliberately conservative.

These statements concern typed word input under `Data.init`: input installation,
binary decoding and malformed-input checking are outside the program's cost.
Native reads, projection, reversal, zero-fill initialization, counter additions,
buffer exchanges and halt are charged. This is the counter preprocessing part
of Lemma 8. It does not certify native quarter enumeration, dictionary lifetimes,
computed-balance traversal or the integrated Theorem 7 peak-space bound.

The native quarter components are in
[AddXNORNativeBuckets.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeBuckets.lean),
[AddXNORNativeQuery.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeQuery.lean) and
[AddXNORNativeEmit.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeEmit.lean).
Import the last module to use all three in namespace
`Cslib.Cryptanalysis.AddXNOR.Native.Quarter`. From the repository root after
[normal setup](../workflows/getting-started.md), check the complete
[native quarter client](../../CslibFrontierTests/AddXNORNativeEnumeration.lean):

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeEmit
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNativeEnumeration.lean
```

`prepare_exec` takes original full-width quarter operands in memory and explicit
layout registers. The operand interval must avoid the head and record regions.
`prepare` clears $2^p$ head cells by native stores, computes the numeric iteration
bound by a shift, and visits all $2^a$ packed operator indices. The least
significant bit acts first; zero selects addition and one selects XNOR.
Every record occupies three words: next bucket pointer, full state and original
operator index. A positive record base and disjoint head/record regions give
`preparedMemory_linked`, which derives the null-terminated bucket lists from
those actual stores. Equal states retain distinct indexed witnesses. Dirty head
and record memory is allowed. The complete preparation instruction bound is
$4\cdot2^p+2^a(11a+22)+10$, with one further instruction for halt.

`prepare_resources` chooses `preparationWidth`, fits addresses and packed indices,
and certifies bounded words and exact nonzero support at every continuing prefix
through halt. For an initial support cover $S$ and preparation bound $T$, its
conservative stored-bit bound is $(|S|+T+32)W$. This is already
$O^*(2^a+2^p)$ for quarter preparation, including dirty unread input and 32
registers. It uses actual stores, rather than the address capacity as occupancy.
A failed fit usually means the physical width fits states but not $2^a$, a
pointer or an intermediate sum. Supply a sufficient width or use the proved
`preparationWidth_fits`; verify `x.Bounded W` separately for all initial data.

`queryBucket_exec` consumes the reversed projected second-quarter operands in a
read-only interval. It charges native operator-bit reversal, inverse evaluation
by complement conjugacy and one head-array load, within $18b+23$ instructions.
Construction of that reversed projected array belongs to the native projection
API above and is an explicit prerequisite here. `emitLoop_exec` follows only
the returned linked records and evaluates the full second quarter for each hit.
It writes the full resulting state and both packed quarter indices, advances an
actual output pointer by three and terminates at zero, within
$H(11b+20)+2$ instructions for $H$ hits. The bucket and full second-quarter
operands must lie below a read-only boundary, and output must start above it;
this prevents output from corrupting later pointer or operand reads.
`emittedMemory_read` specifies all three physical output cells. The client
executes preparation, an inverse query and hit recovery consecutively, checks
collisions, empty quarters, width zero, leading zero operator bits, overflow
rejection and an unread sentinel, and instantiates the generic resource and
emission contracts.

Direct dictionary retention and release are in
[AddXNORNativeDictionary.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeDictionary.lean)
and [AddXNORNativeRetain.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeRetain.lean).
From the repository root after normal setup, run:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeRetain
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNativeDictionary.lean
```

The [complete dictionary client](../../CslibFrontierTests/AddXNORNativeDictionary.lean)
executes original-quarter preparation, inverse bucket query, direct full-state
retention, lookup and release consecutively. It also supplies every hypothesis
of the native array-fill and direct-retention lifetime resource contracts.
Repeated full states replace a witness without adding a second release link;
zero states and zero packed witnesses remain present records. Absent full states
with the same low bits remain absent. Two successive lifetimes reuse the same
slots and restore the original memory, including an unread dirty sentinel.

In namespace `Cslib.Cryptanalysis.AddXNOR.Native.Dictionary`, `put_exec` and
`get_exec` certify actual native insertion and lookup. A state $s$ addresses
three cells at $D+3s$: first packed witness plus one (the presence tag), second
packed witness, and next distinct state plus one (the release link). A zero link
ends the stack. `Valid.put` derives the stack and its distinctness from insertion;
`release_exec` loads each successor before clearing all three words, in at most
$12K+5$ instructions for $K$ distinct states. `filledMemory_read` specifies exact
last-writer replacement. `fill_exec` reads a real three-word record array below
$D$; it is available for materialized clients but direct retention does not use it.

In namespace `Native.Quarter`, `retainLoop_exec` follows only the actual bucket
pointers, evaluates the full second quarter and calls the native dictionary
insertion immediately. It takes at most $H(11b+30)+2$ instructions for $H$ hits
and $b$ second-quarter operands. There is no intermediate output-record array.
`retainLifetime_exec` includes release, within $T=H(11b+42)+7$ instructions.
Its through-halt resource theorem adds one halt instruction; every continuing
prefix has bounded words and exact nonzero support within $(|S|+T+32)W$ bits,
including the initial support cover $S$ and all 32 registers. The final memory
is exactly the initial memory. Release follows the constructed stack, never a
caller-provided list of addresses or an assumed resource conclusion.

This implementation uses **sparse WordRAM memory**, rather than the source's
sorted lists or a compact arena. Its address span is $3\cdot2^m$, while occupied
words depend on the current hit count. The dictionary region must initially be
zero; original input support must lie below $D$. This follows for a suitably
placed region above an installed finite input, but arbitrary dirty dictionary
cells are not allowed. No exponential table initialization is performed or
claimed. The word-fit hypotheses must cover these sparse addresses, state and
witness arithmetic, original input values and all registers. A physical width
that fits only the state is insufficient. These are instruction and occupied-bit
bounds for this RAM model, not a multitape bit-time simulation.

The native full-class iterator and original-input decision/witness run for one
selected class are proved by `AddXNORNativeClassSearch`, described below.
Counter-selected orientation and a fixed-size native all-class loop are now
composed by `Driver.dissection_exec`, described below. In particular,
the fixed-size all-class loop below releases each class, but no theorem yet
derives the global peak bound from the computed $\mu_p$. The native components do not
complete Lemma 8 or Theorem 7. A compact sorted-list/arena realization or a
justified sparse-memory simulation is still needed for the source bit model.

Import [AddXNORNativeBalance.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeBalance.lean)
for the native balance traversal. In namespace
`Cslib.Cryptanalysis.AddXNOR.Native.Balance`, `scan_classes_exec` consumes two
already constructed arrays in one memory: `Native.source` points to the forward
array, `Native.destination` to the complement-indexed backward array, and
`Native.modulus` holds $2^p$. Its hypotheses identify every cell with the actual
indexed class count. It returns the exact `classBalance` in `Native.answer`;
no balance hypothesis or host maximum is supplied. It uses the backward array
directly, without constructing an array of reversed counters or branch choices.

From the repository root after setup:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeBalance
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORNativeBalance.lean
```

The complete [balance client](../../CslibFrontierTests/AddXNORNativeBalance.lean)
supplies all hypotheses on actual nonuniform counts from a five-bit chain. Its
kernel runs also distinguish complemented addressing from ordinary addressing,
check ties with multiplicity eight, preserve dirty outside memory and handle an
empty generic interval. `scan_classes_resources` charges at most
$14\cdot2^p+7$ native instructions including halt. The physical word width is
the caller's `W`; the address sum must fit, and bounded initial data ensure all
intermediate words fit. For an initial finite support cover `S`, every continuing
prefix has exact nonzero support `live` with stored-bit bound
$(|\mathrm{live}|+18)W\le(|S|+18)W$. The scan contains no stores, so this
includes unread input and adds no occupied memory cells. The reusable
`Runs.mem_eq_of_no_store` lemma in
[ReadOnly.lean](../../CslibFrontier/Computability/WordRAM/ReadOnly.lean) proves
memory preservation for every flat-program prefix.

If applying the certificate fails, check the complemented backward addresses,
the two buffer pointers, $2^p$ in the modulus register and the word-fit premise.
This interface starts after counter construction. A single original-input
execution joining both counters, native quarter streaming, dictionary allocation,
lookup, reuse/freeing and witness output remains required for Theorem 7.

Import [AddXNORDissection.lean](../../CslibFrontier/Cryptanalysis/AddXNORDissection.lean)
for the actual quarter-indexed streaming class search of Lemma 8 and Theorem 7.
In `Cslib.Cryptanalysis.AddXNOR.Dissection`, call `solve p as s t` on the
noninitial operands, initial word and target. It uses three consecutive quarters
of length $k=\lfloor q/4\rfloor$ and a final quarter containing the remainder.
It caps the projection width at $m$. `solve_correct` proves unrestricted decision
correctness; `solve_sound` proves that a returned operator list has length $q$
and evaluates to the target. From the repository root after the normal setup:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORDissection
lake env lean -DwarningAsError=true CslibFrontierTests/AddXNORDissection.lean
```

The complete [streaming client](../../CslibFrontierTests/AddXNORDissection.lean)
checks exact emission order in both directions, wraparound, misses, colliding
witnesses, both dictionary orientations, every quarter-length remainder, empty
and zero-width instances, and all one-bit four-operand inputs and endpoints.
A failed concrete equality usually indicates reversed inverse-quarter order or
a lost collision witness; compare `classRecords` and `backClassRecords` before
changing the full-state join.

[ClassEnumeration](../../CslibFrontier/Cryptanalysis/AddXNORClassEnumeration.lean)
indexes the first quarter's full states by low-bit keys. Each second-quarter
word computes its projected inverse from the requested class, visits one bucket
and recovers a full output state only on hits. The backward version indexes the
last quarter and exchanges forward/inverse directions. The reusable
[collision buckets](../../CslibFrontier/DataStructure/BinaryTrie/Buckets.lean)
retain all indexed witnesses. `foldClass` and `foldBackClass` pass records directly
to a consumer; the collecting observers specify their order and multiplicity.
The two observer lengths agree exactly with the existing counter DP.

The dissection computes both counter tables once, then compares their entries
to choose the stored side. `storedClass_length` proves that this is the actual
smaller class; `storedClass_nodes_le_balance` bounds its full-state dictionary
by $(m+1)\mu_p$ nodes. `all_chainStepCalls` proves an unconditional exact
chain-call budget for visiting every class, including repeated quarter setup;
the search may stop at an earlier successful class.
For four quarters of length $k$ this sum is
$4k2^{p+k}+2k2^{2k}$. Each quarter index has at most $(p+1)2^k$ trie nodes.
These statements separate counted chain calls, inspected dictionary nodes and
retained dictionary size. The dictionary is now bound before its consumer fold.
The native endpoint below now composes projection, both counter directions and
balance with selected-class construction and fixed-size native all-class search, under
explicit address-fit hypotheses; `Driver.original_resources` also derives a
compact layout and simultaneous prefix-space bound. This is separate from the
functional trie implementation here, which has no native word-bit simulation
or global allocation certificate. The source bit-model endpoint remains open. The existing
per-class means still give no bound on expected maximum balance.

Import [AddXNORCounting.lean](../../CslibFrontier/Cryptanalysis/AddXNORCounting.lean)
for Propositions 1–2. `steps` uses all `Fin q → Bool` operator strings on the
actual operands. `uniform_mean_solutionCount` gives $2^q/2^m$ under independent
uniform full-width inputs, and `uniform_solution_probability_le` bounds the
probability of any solution by that mean. The balanced mean is exactly $1/2$.
`plantedLastMass_size_bias` derives the manuscript's exact size-bias identity
from its actual final-operand planting: sample the operator string and every
preceding operand independently, then use `plantedLast` to complete the target.
A second identity covers initial-word planting by inverse evaluation. Neither
identity asserts independent solution events or a Poisson law.

Import [AddXNORParity.lean](../../CslibFrontier/Cryptanalysis/AddXNORParity.lean)
for the exact $2^{q-1}$ size of the required parity class and the even Hamming
distance of every solution pair. Positive width is required; the count bound
also requires $q>0$. These theorems reuse the existing Boolean parity and
Hamming-weight APIs. Import [AddXNORDifference.lean](../../CslibFrontier/Cryptanalysis/AddXNORDifference.lean)
for all three parts of Lemma 7 and the actual complemented-carry formula for
an operator flip. `addition_difference_probability` uses two independent
uniform words and a fixed difference; its exponent counts precisely the active
bits below the MSB. `msb_addition_difference` holds deterministically.
The complete [counting/difference client](../../CslibFrontierTests/AddXNORCounting.lean)
checks mean/planting contracts, degenerate-width exclusions, parity bounds and
mixed low/MSB differences. It also shows why Proposition 3's parenthetical
$2^{-w}$ must count non-MSB activity: an MSB-only difference has weight one
but preservation probability one. Import [AddXNORFlipWeight.lean](../../CslibFrontier/Cryptanalysis/AddXNORFlipWeight.lean)
for `expected_operator_flip_weight`, which proves the proposition's exact
$(m+2)/2-2^{-m}$ mean by deriving the two carry-in recurrences from actual
addition. The independent uniform words are the running state and current
operand. The result is the weight immediately after the flip; a common suffix
preserves nonvanishing but need not preserve weight. Width zero is included.
This proof does not use the erroneous total-weight parenthetical.

The [search client](../../CslibFrontierTests/AddXNORSearch.lean) also gives a checked
obstruction to the literal `Real` simulator in Lemma 10 (PDF pp. 25–26).
Conditional on $q=3$, $m=5$, $s_0=t=0$ and planted word $000$, the fresh-answer
rules permit $\pi_{2,0}(0)=0$, $\pi_{1,0}(0)=1$, and $\pi_{3,0}^{-1}(0)=0$.
These draws use separate initially empty tables and have conditional mass
$32^{-3}$. The fourth query $\pi_{2,0}(1)$ closes the chain and is forced to
return zero, violating that table's injectivity. `planted_trace_impossible`
proves that the same three answers are impossible in the true planted experiment.
The parameters satisfy Theorem 8's range. This trace already has a collision
(`BAD`), so it does not challenge the collision-free coupling. It refutes exact
simulation as written, **not** Theorem 8's inequality; repairing the simulator
and proving the adversary-quantified lower bound remain open.

The full-paper objective remains open. Remaining endpoints are the sparsification
resource refinement, exact reduction multiplicity, reachable-state/small-operand
and meet-in-the-middle native bit-runtime/space certificates, streaming class
enumeration and full dissection time/space certificates, and repaired ideal-model
search/decision lower bounds. The positional-cut result is not a universal
algorithmic barrier, and experimental CDCL exponents remain finite observations.


The single-hit opposite-side component is
[AddXNORNativeProbe.lean](../../CslibFrontier/Cryptanalysis/AddXNORNativeProbe.lean).
From the repository root after normal setup, check it and its complete client:

```bash
scripts/build.sh --wfail --iofail CslibFrontier.Cryptanalysis.AddXNORNativeProbe
lake env lean CslibFrontierTests/AddXNORNativeProbe.lean
```

`Quarter.probeBody_exec` loads one actual node, evaluates a full backward quarter
using physically reversed operands, and probes the retained full-state slot. For
$b$ operands it takes at most $18b+33$ standard WordRAM instructions, preserves
all memory, and returns both the nonzero presence tag and second retained witness.
The first retained witness is the tag minus one. Zero witnesses remain present;
a zero tag denotes absence. The node's witness and original backward-quarter
index remain in `firstOperators` and `operators`. The
[complete client](../../CslibFrontierTests/AddXNORNativeProbe.lean) supplies every
premise and tests present zero payloads, absent full keys and an unread sentinel.

Supply the reversed full-width operand cells, dictionary base and initial one
register explicitly. The theorem checks the word/address capacity with `Fits`;
an undersized word cannot satisfy that premise. The dictionary contents are
returned exactly, rather than assumed to encode a valid solution. This theorem
does not yet iterate the opposite class, exit with a complete chain witness,
select orientation from counters or join original-input preprocessing. It proves
no global peak-space or source multitape bit-time bound.


`Quarter.probeScan_exec` extends this operation to a complete linked bucket.
Initialize `operand` and `zero` to zero and supply the actual `Linked` chain,
bounded full states, reversed operands and word-fit premise. The returned tag
is nonzero exactly when some node's computed full backward state has a nonzero
dictionary tag. For $H$ nodes and $b$ operands, execution costs at most
$H(18b+39)+2$ instructions. Every memory cell is preserved. The scan stops at
the first present key; its witness registers are those of that probe. This
physical membership contract still requires dictionary validity and original-chain
composition before its tag can be interpreted as an Add/XNOR solution.
The same complete client checks a miss followed by a zero-witness hit, all
misses, an empty bucket, and early exit before an invalid successor. This scan
is not the second-quarter/class iterator or a global computed-balance bound.


`Quarter.probeScan_witness_exec` additionally identifies a node in the actual
linked bucket when the tag is nonzero. Its first packed index, preserved second
index, recovered full state and both dictionary cells agree with the returned
registers. The complete client above instantiates this stronger contract on a
miss followed by a hit with zero retained witnesses. This is physical witness
provenance, not original-chain correctness: the latter still requires semantic
validity of the bucket construction and retained dictionary, plus the general
class iterator theorem. Empty buckets return tag zero; no witness is asserted
on exhaustion. Instruction bounds and prerequisites are unchanged.

`Quarter.probeScan_original_exec` supplies a bounded original-chain reconstruction
contract. Supply full original quarters, their initial and target states, a linked
bucket whose records are the computed backward fourth-quarter states, and memory
equal to the actual `retainedEntries`/`filledMemory` construction from forward
first-quarter states. Initial dictionary tags must be empty. On a hit, decoding
`operand - 1`, `bits`, `operators` and `firstOperators` in quarter order gives
operations whose full original-chain evaluation equals the target. The subtraction
removes the presence encoding; packed index zero remains valid.
`Dictionary.filledMemory_provenance` derives both payload words from one inserted
record even after replacement, and `Quarter.retained_provenance` identifies its
originating retained bucket record. No assumed decoded-witness correctness is
needed. The complete client above supplies all premises for four original
operands and zero packed witnesses, and checks last-writer replacement.
This theorem still requires constructed memory and semantic bucket records:
the raw-input `searchClass_exec` endpoint below now derives those premises and
executes complete retention and opposite-side probing with general termination.
The original-input global endpoint remains open. This component does not change the
instruction model or establish the source's sorted-list bit-runtime theorem.

The same checked client now includes `constructedPipeline`: starting with only
four original operand cells and an unread sentinel, it executes low-bit projection
by loads/remainders/stores, first-quarter preparation, projected inverse filtering,
direct dictionary retention, fourth-quarter preparation and the streaming opposite
class. It checks the decoded original-chain evaluation on the actual returned
registers. Runs cover full width two with projection width one, projection-width-zero
bucket collisions, and full width zero with dictionary replacement. These are
restricted executable examples: quarters have length one, the fourth-quarter
operations are self-inverse for these operands, and only retained second-quarter
index zero is visited. They do not supply a general inverse construction or prove
the outstanding universal construction-to-witness endpoint.

For general fourth-quarter preparation, import
`CslibFrontier.Cryptanalysis.AddXNORNativeBackward` and use
`Quarter.Backward.prepare_linked_exec`. Supply the target in `initial`, the
full-width modulus in `modulus`, and the reversed fourth-quarter operand array
at `base`, with `count` equal to its length. `heads` addresses $2^p$ writable
head cells; `frontier` starts a positive, disjoint three-cell-per-index record
region. Operands must avoid both writable regions. The theorem derives the
linked records of actual inverse states, preserving original packed indices
and outside memory, after native zero-fill and enumeration. It includes physical
address/index fit premises. The complete
[backward preparation client](../../CslibFrontierTests/AddXNORNativeBackward.lean)
checks non-self-inverse addition, collisions, dirty memory, and an empty
zero-width quarter. From the repository root, check it with
`lake env lean CslibFrontierTests/AddXNORNativeBackward.lean` after building its
import. This API supplies backward bucket semantics. The `searchClass_exec` endpoint
below connects both prepared sides through actual forward dictionary retention
and a complete native projected-query stream, deriving original-chain soundness.

For the retained **forward** side, import
`CslibFrontier.Cryptanalysis.AddXNORNativeForwardRetain` and apply
`Quarter.Forward.prepareRetain_exec`. Starting at the repository root with warm
build outputs, build that module and run
`lake env lean CslibFrontierTests/AddXNORNativeForwardRetain.lean`.
The [complete client](../../CslibFrontierTests/AddXNORNativeForwardRetain.lean)
supplies forward-order first-quarter operands, a separate forward second-quarter
array, disjoint head/record regions below an initially zero dictionary, and the
physical word-fit bound. The program derives the exact forward dictionary
insertion stream, top pointer and payload provenance; no computed dictionary is
an input. `Forward.retainedMemory_linked` preserves every first-quarter bucket.
The bound covers preparation plus one bucket and one second-quarter word.
The client distinguishes forward states from inverse states and checks zero-width
collisions. A failed fit or separation premise requires a larger word/layout;
it cannot be discharged by treating the dictionary as a host oracle.
For consecutive separate inverse preparation, import
`CslibFrontier.Cryptanalysis.AddXNORNativeDualPreparation` and apply
`Quarter.dualPrepare_exec`. Put the inverse heads and records after the forward
records and below the dictionary. Supply reversed fourth-quarter operands outside
both arenas and below the dictionary, plus the combined physical fit bound.
Seven native instructions transfer the inverse-stage registers. The theorem derives
both linked bucket families, the exact retained forward dictionary equation, zero
base tags, outside-memory preservation and a register frame. `dictionaryBase` is
proof bookkeeping for the memory below the table after construction; it is not a
RAM operation or a supplied dictionary. The
[complete preparation client](../../CslibFrontierTests/AddXNORNativeDualPreparation.lean)
checks forward and inverse construction, retained witness tags and a dirty sentinel.

For an actual original-chain witness scan, import
`CslibFrontier.Cryptanalysis.AddXNORNativeDualProbe` and use `Quarter.dualProbe_exec`.
Supply reversed full-width third-quarter operands below the dictionary and outside
both arenas. Ten more native instructions transfer registers and load the selected
inverse bucket head; the scan then inverts the third quarter and probes the full
retained states. Any reported witness is proved to solve the original chain.
The [complete probe client](../../CslibFrontierTests/AddXNORNativeDualProbe.lean)
supplies all raw premises, and kernel runs check a hit with zero packed witnesses
and a miss. From the repository root, build the two modules, then run
`lake env lean CslibFrontierTests/AddXNORNativeDualPreparation.lean` and
`lake env lean CslibFrontierTests/AddXNORNativeDualProbe.lean`.
Increase word width or separate the arenas/arrays when fit or separation fails;
initial dictionary cells must really be zero. Bounds count every construction,
transfer, load and scan instruction in this sparse WordRAM model.

To derive those bucket choices from original operands, import
`CslibFrontier.Cryptanalysis.AddXNORNativeProjectedProbe` and use
`Quarter.projectedProbe_exec`. Supply the original first/second-quarter arrays
in forward order and third/fourth-quarter arrays in reverse order. All original
arrays must end before the first scratch array. Place the two nonoverlapping
projection arrays before the forward heads, followed by the forward records,
inverse heads/records, and initially zero dictionary region. The two explicit
word-fit bounds cover query setup and construction/scanning respectively.
The class value and two middle-quarter packed words are ordinary parameters;
there is no projected-array, selected-key, dictionary or witness premise.

`selectQueries_exec` constructs the reversed projected second-quarter array and
forward projected third-quarter array, computes the inverse and forward queries,
and saves their actual physical bucket addresses. It also computes the forward
class index and complemented backward index used by the existing counter API.
This computes indices, not counter contents or an orientation decision.
`selectedProbe` reads the saved addresses; register-parameter substitution reuses
the earlier execution proof with identical final data and instruction count.
`projectedProbe_exec` includes every projection, query, transfer, preparation,
retention and probe instruction, and proves any reported witness solves the
original chain. For the source's low-bit class interpretation use $p\le m$;
the hit-soundness contract itself permits other admitted widths.

From the repository root run
`lake build CslibFrontier.Cryptanalysis.AddXNORNativeProjectedProbe`, then
`lake env lean CslibFrontierTests/AddXNORNativeProjectedProbe.lean`.
The [complete client](../../CslibFrontierTests/AddXNORNativeProjectedProbe.lean)
supplies all raw premises with non-self-inverse addition and colliding low keys,
checks native multiword projection/query order and counter indices, and executes
whole-program zero-width-hit and empty-class-miss cases. Dirty scratch cells are
allowed and overwritten; unread input is framed. If layout/fit fails, separate the
arrays/arenas or increase word width rather than installing query results as an
oracle. `RegisterParameter` in `CslibFrontier.Computability.WordRAM.RegisterParameters`
is also available for clients replacing selected immediate writes by copies of
an already computed, preserved register.

Those bounded APIs fix one word per middle quarter. For a complete selected-class
search, import `CslibFrontier.Cryptanalysis.AddXNORNativeClassSearch` and use
`Quarter.searchClass_exec`. Its raw input order and layout are the same: original
first/second-quarter arrays in forward order, third/fourth arrays in reverse order,
then scratch projections, heads and record arenas, and an initially zero dictionary.
Supply $p\le m$, separation and the combined physical word-fit bound. Initial
registers need no semantic setup. The program computes both middle-word bounds
with shifts and visits every admissible packed index, rather than accepting words
or correct bucket keys from the caller.

The program projects both middle quarters and prepares both quarter bucket families
before retaining the complete forward class. The native opposite-class iterator
then streams every third-quarter word and its computed inverse bucket. A hit sets
`stop` to the current word to exit without destroying the witnesses; exhaustion
leaves a zero tag and `operators = stop = 2^{cs.length}`. The theorem proves a
nonzero tag exactly when an original solution occurs in the selected class, and
a zero tag exactly when that class has no solution. `PackedClassSolution` states
all four admissible packed-index bounds explicitly; `packedClassSolution_iff_meets`
identifies it with the existing `Dissection.Meets` predicate. Reported registers
solve the original four-quarter chain. A valid dictionary release chain and a
bound on its distinct states are derived from construction, not assumed.

`classRetainTime_eq` and `classProbeTime_eq` expose the loop budgets. If $b,c$ are
the second/third quarter lengths, $H_F$ is the number of emitted retained entries,
and $H_B$ is the number of records in the full opposite stream, the loop budgets are
$H_F(11b+30)+2^b(18b+35)+2$ and
$H_B(18c+39)+2^c(11c+22)+2$. Early exit uses at most the full-stream budget.
The endpoint also charges projection, both preparations, register transfers,
initialization and bound computation. These are standard WordRAM instructions,
not bit operations or a derived global word-width theorem.

For counter-selected search across all classes, import
`CslibFrontier.Cryptanalysis.AddXNORNativeDissection` and use `Driver.dissection_exec`.
The `SearchLayout` record admits either orientation and states only raw address
separation and physical word capacity. `CounterLayout` places two projection
buffers and two reusable counter-buffer pairs before the class workspaces. Supply
the four original quarter arrays, an original contiguous forward-half array and a
reversed original suffix array; these may alias the quarter arrays when arranged
contiguously. Original input ends before counter scratch; class scratch follows
both counter-buffer pairs. Dictionary cells at and above `D` are initially zero.
No counter values, balance, orientation, projected query, dictionary, traversal,
termination or witness correctness is a premise.

`Driver.prepare_exec` projects the raw halves and executes both native counter
kernels. It saves their actual result pointers in a separate high register bank,
then scans the actual arrays before any full class is stored. The backward array
uses complemented low-bit indices. The returned balance equals `computedBalance`;
`computedBalance_eq_classBalance` identifies it with the existing manuscript
`classBalance`. At each key, `selectedClass` loads both actual counter cells and
retains the smaller side, choosing forward on ties. Inverse retention runs the
proved class kernel on reversed quarters with complemented start, target and
class. Reversing the decoded operator words reconstructs the original witness;
`packedClassSolution_reverse_iff` proves that both orientations decide the same
original class. This avoids interpreting inverse continuation records as an
original forward dictionary.

Every `orientedCycle` releases the physical dictionary even on a successful hit.
It saves and restores the witness register used by release. Its proof derives the
release chain and key bounds from construction, frames original arrays and leaves
all dictionary cells zero for the next class. The actual `searchLoop` controller
computes $2^p$ with a native shift, initializes the class index and miss tag, then
executes one fixed while loop. The current key and its complement live in preserved
registers; `registerSelected` supplies them to the proved class subroutines. The
actual counter tables still select orientation. A miss advances exactly one class;
a hit copies the bound into the index without changing the witness. Induction on
the finite remaining counter proves exhaustive misses and sound early exit.
`searchLoop_exec` also exports the final index and bound, both $2^p$, and frames
original memory, counter tables and balance.

`dissection_exec` now uses this loop. It proves a nonzero tag exactly when some
original class has a solution, a zero tag exactly when none does, original-chain
witness soundness, the actual computed balance and reusable empty dictionary
memory. Use `Driver.witness` to decode the returned words according to the
preserved orientation bit. `searchLoop_size` proves 812 instructions for the
outer search block, and `dissection_size` proves 960 for preprocessing plus search;
`dissection_program_length` gives 961 after appending halt. These instruction
counts are independent of class count, quarter lengths and scalar values.
Layout, widths and seeds are still explicit scalar parameters; these results do
not provide a new fully encoded input-header decoder or bound immediate bit sizes.

`prepareTime + (5 + loopTime)` charges counter projections/constructions, balance,
all quarter setup, release, loads/comparisons, complemented-key computation,
initialization, the shift, increment and loop/early-exit control. The bound in
`dissection_exec` is for the structured block; compiling with `Code.program` adds
one charged final halt through `Exec.executes`. `loopTime_eq_allTime` reuses the
earlier full-interval cost observer: the new complete search adds
$7\cdot2^p+6$ to that reference bound. `allTime_eq_sum` expresses its class-cost
sum; the earlier unrolled code is a reference certificate, not the executed
program. No traversal, termination or runtime conclusion is assumed by the
raw-input endpoint. If an outer state must survive a class call, keep it in the
reserved high registers; `Code.RegisterParameter` now supports both branches,
with `preserves_iff` and `size_eq` for frames and compiled size.

For the global native resource endpoint, import
`CslibFrontier.Cryptanalysis.AddXNORNativeGlobalResources` and apply
`Driver.original_resources hp as bs cs ds s t`, where `hp : p ≤ m`.
The theorem supplies the initialized original input, compact array layout and
physical word width; no counter, orientation, query, traversal, dictionary,
completion or desired resource invariant is a premise. Its tag decides the
ordinary `Solvable ((as ++ bs) ++ (cs ++ ds)) s t` predicate, a miss proves absence,
and a hit returns an original-chain witness through `Driver.witness`. The actual
balance register equals `computedBalance`, the maximum of the constructed
forward/backward count minima.

Write $a,b,c,d$ for the quarter lengths, $q=a+b+c+d$, $N=2^p$,
$C=100(q+1)$ and $Q=N+2^a+2^b+2^c+2^d$. Put
$\mu=\max_g\min(F_g,B_g)$ for the actual multiplicity counters and let
$P=\texttt{prepareTime}\ p\ (a+b)\ (c+d)$. The complete compiled program,
including halt, takes at most
$$P+N(CQ+18)+C(2^{a+b}+2^{c+d})+8$$
native instructions. `insertionCount_eq_forwardCount` and
`classProbeHits_eq_backwardCount` identify actual indexed records with computed
counts; conjugacy exchanges these counts in the inverse orientation.
`sum_forwardCount` and `sum_backwardCount` sum them to the two half-word
populations, including duplicates. `dissectionTime_le` composes preprocessing,
construction, both directions, release and all outer loop control.

The compact layout places the dictionary at
$$D=1+2q+2(b+c)+6N+6(2^a+2^d).$$
Every continuing prefix of the actual compiled run, including its final state
before halt, has nonzero memory support at most
$$D+P+C(Q+\mu).$$
The theorem includes unread input cells and all surviving counter/projection/quarter
scratch cells. Add forty words for registers. `Exec.All.prefix` carries the
structured execution's annotation through native jumps and tests. The probe
phase is proved write-free; one lifetime's actual stores depend on its retained
count, which the native comparison bounds by $\mu$. Dictionary release resets
the zero tail before the next lifetime. The proof reuses this allowance across
classes; it does not sum historical allocations or replace a maximum by a mean.
Collisions can shorten the physical dictionary chain without discarding their
indexed counter multiplicity.

`compactSearchLayout` and `compactCounterLayout` arrange the original arrays
contiguously, reuse the reversed suffix and place all counter buffers before the
class workspaces. `quarterInput_raw` establishes every construction premise from
`Data.init (quarterInput as bs cs ds)`. `globalWidth` is one plus the base-two
logarithm of `layoutLimit`, which bounds layout addresses, full-state dictionary
slots, quarter indices and half-word counters. `quarterInput_fits` includes the
input length header. Every actual read/write address and value fits that width;
every prefix's cells and registers remain word-bounded. Multiplying the occupied
cell allowance plus forty by `globalWidth` bounds stored word contents. It is not
a bit-time simulation or a sparse-memory serialization theorem.

For source quarter lengths $k,k,k,k+r$ and $p≤k$, `globalTime_quarters` bounds the
block by $1000(4k+r+1)2^{2k+r}$ instructions, with one more for halt.
`peakCells_quarters` bounds occupied memory by
$1000(4k+r+1)(2^{k+r}+\mu)$ words. The source split has $r=q-4k$ between zero and
three; the Lean bounds also admit larger remainders. These are resource components
of [WangLvShenZhang2027], Lemma 8/Theorem 7, PDF pp. 21–22, for the actual fixed
native program. Input placement is the RAM convention, and scalar lengths, seeds
and layout/width values remain program parameters. A header decoder, encoded
program/immediate-bit accounting are not supplied by this native endpoint.
The uniform preparation endpoint below supplies those stages; a uniform runtime
program interpreter and the sharp source multitape bounds remain open. Native variable-length output and a concrete bit-output codec are now
supplied by the following endpoint. Four packed witness words also remain in
the charged register bank. This does not complete Lemma 8/Theorem 7
or 733 ALL-main.

From the repository root build
`lake build CslibFrontier.Cryptanalysis.AddXNORNativeGlobalResources`, then run
`lake env lean CslibFrontierTests/AddXNORNativeGlobalResources.lean`.
The complete clients include unequal quarters with strict inverse selection and
non-self-inverse addition, colliding low keys, exhaustive empty-quarter misses,
zero-width multiplicity collisions, and a concrete bit-capacity bound including
all forty registers at every prefix.
The complete client instantiates all raw premises with unequal quarters,
non-self-inverse addition, dirty scratch and low-key collisions. It checks native
strict inverse and forward selection, tie/forward zero-width collisions, exhausted
empty-quarter misses, actual balance, dictionary release and final native class
index/bound. The generic size client checks the fixed instruction count. If physical premises
fail, move counter buffers before class scratch or increase word capacity; do not
supply desired counter values or an orientation flag as an oracle.


For a materialized output array, import
`CslibFrontier.Cryptanalysis.AddXNORNativeOutputResources` and apply
`Driver.original_output_resources hp as bs cs ds s t`. The actual program is
`dissectionOutput`: the proved core followed by `Output.program`. It returns an
address of a length-prefixed array using the standard `ExecutesList` convention.
The payload is `[0]` for a miss and `1 :: ops.map Bool.toNat` for a hit. A successful
empty witness is `[1]`, so it remains distinguishable from a miss. The theorem
derives absence or a list of exactly $q=a+b+c+d$ original operators solving the
original input; no output correctness conclusion is a premise.

`OutputBits.program` emits one word per packed bit, including leading zero
operators, in $7n+5$ native instructions. Its inverse-order version moves the
actual destination cursor backwards; it does not reverse a host output list.
`Output.program` loads the actual orientation flag, copies all four packed words,
subtracts the presence tag, writes the status/length and runs four fixed loops.
It preserves the packed source registers, computed balance and memory below the
output region. The complete serializer costs at most $7q+53$ instructions and
has exactly 148 instructions in its graph, independent of quarter lengths. The
composed block has 1,108 instructions, or 1,109 with halt. Its global time allowance
is the prior `globalTime` plus $7q+53$, then one final halt. At every compiled
prefix, occupied memory is bounded by the prior `peakCells` plus $7q+53$ cells;
the same forty registers and derived `globalWidth` suffice. The added linear
allowance conservatively charges all serializer stores, not an assumed output
footprint. `compact_output_fits` proves the complete output interval fits the
original physical width. The computed balance is unchanged.

`OutputCodec.decoder` is an actual six-state multitape transducer with zero work
tapes. Its input is `encList encNat` of the represented word array; each zero word
has the one-symbol frame `[false]` and each one word has the three-symbol frame
`[true,true,false]`. The machine emits `encOption encBits`: the empty word for a
miss or `true :: ops` for a hit. `decoder_run` proves this exact format connection,
including zeros and empty witnesses; `wire_injective` distinguishes the outcomes.
`decoder_computes_linear` charges at most $6q+9$ Turing steps for an output of at
most $q$ operators, including status and halt, with zero work-tape space. The final
native resource theorem includes this machine certificate for the encoding of
its own actual returned array. Input/output tapes are not counted as work tapes.

This standalone bit stage starts from the already encoded output array. Reading RAM memory
into that machine input is not charged by the codec theorem. Original input still
uses the reversed-suffix RAM calling convention; this standalone codec does not
decode scalar headers or construct encoded programs. The later uniform preparation
endpoint supplies those stages. The core uses sparse full-state
addresses and unit-cost word operations, whereas the source conventions (PDF p. 6)
count deterministic multitape bit operations. The existing association-list
simulator scans stored bindings and retains bindings written to zero; its generic
bounds depend on historical storage and may add factors exponential in $q$.
Neither it nor the output codec supplies the source sorted-list membership and
memory-reuse algorithm. No source global bit-time or peak-space asymptotic is
claimed from this output milestone. The following fixed-parameter execution bridge
charges input conversion and memory extraction without supplying the missing sharp bound.

From the repository root build
`lake build CslibFrontier.Cryptanalysis.AddXNORNativeOutputResources`, then run
`lake env lean CslibFrontierTests/AddXNORNativeOutput.lean`. The complete original-input
client includes unequal quarters, non-self-inverse addition, colliding low keys,
computed balance, actual output validity and all-prefix space. Consecutive native
executions check both bit orders, leading zeros and dirty outside memory. Empty
original-input hits and exhaustive misses check both status formats; the same
client checks the concrete bit decoder and fixed graph size.

For an actual bit-machine input and execution connection, import
`CslibFrontier.Cryptanalysis.AddXNORBitExecution`. `BitInput.encoding` represents four
quarter lists of binary natural words in original chain order, with explicit
framed quarter boundaries. `BitInput.prepareCertificate` implements concatenation
and suffix reversal on a multitape machine; `initialCertificate` also constructs
the finite sparse memory, including the length header, zero-valued input cells
and their addresses. These are charged polynomial bit computations. For $q$
original $m$-bit operands the encoded input has at most $4q(2m+1)+4$ bits.

`BitExecution.solveBitsCertificate p a b c d s t` composes that preparation with
the concrete finite-state simulation of the 1,109-instruction native program,
then reads the length-prefixed output from simulated memory and runs the actual
output decoder. `original_bits_correct hp as bs cs ds s t` proves exhaustive
absence or a correctly sized original-chain witness from those original operands.
No simulation, dictionary, query, completion or witness correctness conclusion is
an input premise. The input words are not presumed already reversed or already
materialized in RAM. The generic reusable implementation is
`Program.clockedListCertificate` in
`CslibFrontier.Computability.WordRAM.Turing.ClockedListOutput`.

The certificate's `time` and `space` have explicit composition equations
`executionCertificate_time` and `executionCertificate_space`: input preparation,
initialization and runtime width/clock setup, `FiniteState.runTime`/`runSpace`,
then the standalone parked-output reader. That reader operates on the produced
state, so it does not rerun the dissection. Simulator profiles charge control
dispatch, checked arithmetic, address encodings and sparse-memory scans; workspace
bounds are simultaneous bounds on the implementing machine, including encoded
intermediates and output charges, up to constants. The final linear bit decoder
is absorbed using the producer's proved output-length charge.

This is a **fixed-parameter machine family**. Widths, quarter lengths and endpoints
are fixed in the program and in the finite machine; implementation constants can
depend on them. This simulator family accepts no encoded program at runtime.
The uniform preparation endpoint below computes headers, code and immediates;
runtime dispatch and malformed-input validation are separate obligations.
For the actual prepared operands, `original_encoding_bound` bounds every simulated
outcome by `stateBound 40 (labelBound P.parkHalts.toGeneric) W (q+1+j)` after $j$
steps, with the proved physical width $W=globalWidth$ and clock
`globalTime + outputTime + 1`. The simulator retains zero bindings, so its stored
state can depend on $j$ rather than native computed-balance live support. The
native bounds remain intact, but these bit profiles do not establish the source
sorted-list time or peak-space asymptotics. A generic simulator certificate is
not a sharp bit-model theorem, and this family is not a uniform ALL-main endpoint.

From the repository root build
`lake build CslibFrontier.Cryptanalysis.AddXNORBitExecution`, then run
`lake env lean CslibFrontierTests/AddXNORBitExecution.lean`. The
[complete client](../../CslibFrontierTests/AddXNORBitExecution.lean) checks original-order
suffix reversal, materialized zero cells, concrete small-program simulation and
readback, an actual overflow fault, unequal-quarter strict inverse/collision and
nonempty forward clients, and empty hit/miss bit encodings. For a failed physical
fit, use the derived `globalWidth` and valid full-width operands; do not replace
it with the operand width $m$. For a variable input header or a source asymptotic,
the fixed-parameter theorem is insufficient: use the uniform preparer below,
then prove runtime-program dispatch and the stronger source simulation.

For **uniform encoded program generation and complete simulation-input preparation**,
import `CslibFrontier.Cryptanalysis.AddXNORGeneratedRunInput`. Construct a
`ProgramGeneration.Source`: unary width/class parameters $(m,p)$, binary endpoints
$(s,t)$, and four original-order operand lists. `sourceEncoding` frames the two
parameter pairs and quarter lists explicitly. Lengths are computed from the actual
lists, including zero operands and repeated values; no quarter-length advice or
executable is supplied. `originalSource p as bs cs ds s t` constructs this input
from full-width operands. To match the paper's source convention, take its first
operand as $s$ and target zero as $t$; the API also admits arbitrary endpoints.

`ProgramTemplate.literalTemplate` has 303 expressions. Unary size expressions
supply powers-of-two exponents; endpoint words and generated values stay binary.
The actual multitape arithmetic implementations compute the literals in polynomial
metadata bit time and workspace, without exponentially long unary intermediates.
`literals_exact` checks every value against the native definitions for all metadata,
and `graph_exact` checks that erasure gives one fixed graph. `generate` fills this
graph; `generate_exact` proves equality to the actual reviewed executable, not just
equality of program sizes. The original 1,109-instruction graph is reused directly
rather than copied or expanded by the runtime class range.

`ProgramLiterals.record` encodes opcodes, operations, register indices, control
labels and literals as rows of at most five natural fields. The whole program wire
is `encList (encList encNat)` of its 1,109 rows. For example, the row
`[2,7,0,1,2]` is XOR into register zero from registers one and two; `[0,1,0]` writes
literal zero. `deserialize` is a concrete **row-level** parser with proved program
roundtrip and invalid-tag/register rejection. The wire encoding is injective.
The separate uniform execution stage below supplies the runtime bit-program interpreter.
`generationCertificate` and `rawGenerationCertificate` are actual uniform code-emitting machines;
`sourceGenerationCertificate` additionally computes lengths from the original input.
The external metadata ABI has six unary sizes `[m,p,a,b,c,d]` and two binary
endpoints `[s,t]`. The total `readMetadata` conversion defaults missing entries to
zero and ignores excess entries; it is not a malformed-input recognizer.

`GeneratedRunInput.configurationCertificate` computes the physical width
`globalWidth` in unary and `globalTime + outputTime + 1` in binary. Computing this
large binary clock is polynomial preparation work; executing its many steps is a
separate cost. `packetCertificate` materializes the generated program, computed
width/clock and the actual finite initial memory. Initialization includes the
length header, input addresses and zero-valued cells. Source-order suffix reversal
is computed by the existing bit input machine. `packet_resources` proves that one
polynomial in the original encoded input length bounds this machine's time,
simultaneous workspace and entire encoded output packet, with constants independent
of runtime metadata. These are polynomial bounds on an implementing machine, up
to constants, without a claimed explicit degree or exact step count. For an original
input with $q$ operands, `original_input_length` bounds its encoding by
$14m+4p+4q(2m+1)+13$ bits. `original_packet_resources` bounds preparation time,
workspace and emitted packet size by $C(14m+4p+4q(2m+1)+14)^d$, with uniform
constants $C,d$; this does not bound the subsequent search.

`packet_original` identifies every generated packet field with the proved native
execution. `GeneratedRunInput.run` consumes that packet's actual program and state
using the concrete clocked finite RAM evaluator, then reads and decodes its output.
`original_correct` proves an exhaustive miss or a correctly sized original-chain
witness for arbitrary quarter lengths and $p≤m$, without supplied compiler,
execution, query, dictionary or witness conclusions. Runtime width/clock, original
input materialization and executable generation are all derived, not advice.

`UniformExecution.packetExecutionCertificate` now implements `GeneratedRunInput.run`
with **one** multitape machine on runtime packets. The reusable `WordRAM.Interpreter`
reads opcode, register index, literal and jump-label fields on tape. Its finite
opcode dispatcher uses checked standard operations, including overflow-safe shifts,
and capped binary indexing rather than expanding arbitrary labels in unary.
`step_serialize` proves exact native step refinement for every program and finite
state, including faults. The binary-counted loop absorbs faults and returns.
Runtime halt parking is actually generated; the reader uses the supplied program's
length, scans its length-prefixed memory output and runs the existing witness decoder.

`UniformExecution.sourceCertificate` composes this machine with packet preparation.
`original_machine` quantifies its tape count, finite state set and resource constant
**before** all original-input parameters. It returns an exhaustive miss or a sound,
correctly sized original-chain witness, without a supplied simulation contract.
`source_time` and `source_space` charge preparation plus packet execution. For a
runtime clock $T$, encoded input length $I$ and maximum complete loop encoding $M$
over all prefixes, `Interpreter.clocked_resources` bounds the simulator's charged
profiles by
$3I+(T+1)(C(M+1)^d+M+(ℓ(T)+1)^2)$ time and
$3I+C(M+1)^d+M+ℓ(T)$ workspace, where $ℓ(T)=|\mathrm{encNat}(T)|$.
The constant and degree depend on the fixed register count/instruction set, not
runtime program fields. These are bounds up to a uniform machine constant;
parking, packet preparation and the output-reading loop carry their additional
certified profiles. The latter charges every output cell, including unwritten zeros.

The original uniform implementation retains zero bindings, so its full encoding
can grow with elapsed instructions. The separate `CompactExecution` path now
**executes** `SparseMemory.compact` at initialization and after every interpreter
round. `step_compact` and `iterate_compactRound` prove exact normalization of each
native prefix, preserving labels, registers, faults, returns and total memory.
The real filtering machine has cubic scan time and linear workspace in its input
wire; it deletes explicit default bindings, including nonzero defaults.

`CompactExecution.original_compact_encoding` derives a retained-state bound from
computed-balance native support and physical word/address width, for every clock,
including arbitrary parking after early exit. `original_compact_trajectory` bounds
the complete program/width/state maximum used by the actual compacting certificate.
For support allowance $S$, the state wire is bounded by
`stateBound 40 L W S`, where $L$ is the program's label bound and $W$ its derived
physical width. Here $S$ is `peakCells` at actual `computedBalance`, plus native
witness serialization work. It is no longer the number of historical stores.
`compactClocked_time` and `compactClocked_space` retain all interpreter and filter
charges. **This encoding bound is not a sharp bit-machine workspace theorem:**
association-list scans and the interpreter's polynomial workspace overhead persist.
Sorted-list/resource-faithful access, sharp bit time and sharp peak workspace remain
open, alongside the other 733 ALL-main endpoints.

`Source.prepareCertificate` receives unary width/requested depth and one framed
binary operand list (`Source.encoding`). It computes the first operand as seed,
zero target and the consecutive cut $k,k,k,q-3k$, where $q=N-1$ and
$k=⌊q/4⌋$; the fourth quarter retains every remainder. Effective depth is
$\min(p,m,k)$, and `prepare_ofWords_admitted` proves the cap inert when
$p\le m$ and $p\le k$. These are computed fields, not seed/quarter advice.
`Source.original_machine` composes source preparation with compacting execution,
actual memory output and witness decoding; one machine precedes all original input
parameters. `compact_trajectory_bound` connects that actual prepared packet to the
derived prefix encoding bound. Correctness is stated for a nonempty typed word
list; empty/malformed raw input validation is not asserted. This completes the
source operand/seed/target/cut convention bridge, not Theorem 7's sharp resources.

`RadixSort.computable` supplies a separate **uniform deterministic multitape sorter**
for runtime unary key width $w$ and binary key/packed-payload records. One loop
performs stable streaming radix partitions. For encoded input length $I$, record
count $n$ and $B=w+\max_r|\mathrm{enc}(r)|+1$, a fixed monotone polynomial $Q$
bounds time by $O((w+1)(I+(n+1)Q(B)))$ and charged peak space by $O(I+Q(B))$.
The proof derives permutation, low-bit sortedness and the maxima over every loop
prefix. It charges clock conversion, partition buffers, materialized lists and
output; no growing output accumulator is copied on each record. `wire_bounds`
charges payload width separately from key width. Thus sorting a bounded-width
materialized list costs its record count times polynomial width overhead.

`AddXNORSortedRecords.projectedQuarter_correct` connects these sorted keys to every
admissible packed original-quarter index. `retainedClass_correct` connects sorted
full-state records to the actual forward insertion stream and original two-quarter
witnesses. Both preserve collisions and multiplicity; `unpack_payload` recovers
both packed indices, including leading zero operators. `projectedQuarter_wires`
and `retainedClass_wires` derive physical record widths from those constructions.
Their calling boundary is an **already materialized list**. Quarter/class
generation, counting, selected-class access/reuse and the full source execution
are not charged by these sorting theorems. The source convention remains the
computed seed/zero-target/cut described above.

`SparseMemory.compact_streaming` is also an actual alternative filter: time is
$O(I+(n+1)P(B))$ and charged peak space is $O(I+P(B))$, for a fixed polynomial $P$
in default/maximum-binding width. It computes precisely the existing compaction,
including nonzero defaults. It is **not installed in `CompactExecution`**; that
path's cubic filter and general interpreter overhead remain charged. These new
components do not prove the source's global sharp time or peak-space bounds.

`SourceQuarter.run` closes that materialized-list boundary for the **first
projected quarter**. It starts with the original `Source.encoding` input, executes
`Source.prepare` to compute the cut, first-operand seed and capped depth, and
projects the actual seed/operands. `SortedQuarterMachine` generates each packed
index by a runtime loop of streaming doublings, evaluates its original chain with
certified modular addition/XNOR and packed decoding, and invokes the uniform radix
sorter. It uses the tape primitives directly, bypassing sparse RAM interpretation
and its cubic compaction for this route. The generation loop derives the record
count, binary width and wire volume at every prefix; callback and sort certificates
charge all simultaneous input/output and transient buffers.

`SourceQuarter.run_computable` proves time **and charged peak bit space**
$O((2^k+1)Q(I+1))$, for one fixed monotone polynomial $Q$, original input wire
length $I$, $q=N-1$ and computed `k = q / 4`. No executable, generated
list, traversal or desired resource bound is supplied as a premise.
`original_correct` connects every sorted record to its original full-width packed
quarter witness and projected state. For admitted $p≤m$,
`original_input_length` bounds the original wire by
$6m+3+(q+1)(2m+1)$; thus this first-quarter component has the source's
$O^*(2^k)$ time/space with the polynomial bit overhead explicit. Empty/zero-width
quarters and colliding states retain all indices. This is **not a whole-instance
witness or exhaustive-miss algorithm**: inverse-quarter generation, class counts,
matching, smaller-side full-state retention, access/probing and reuse/release still
need the charged sorted-list composition. The existing complete `CompactExecution`
path and all its cubic filter/interpreter costs remain unchanged. Neither global
source resource bound nor 733 ALL-main is concluded here.

`SortedMeet.run` adds a separate **whole-input full-state batch route**. It
uses the same actual index/chain generator for both halves of the computed
consecutive cut. Inverse execution reverses the actual suffix operands and
complements the target/state; decoded suffix operators are restored to original
order. This handles modular addition as an inverse operation, not as a
self-inverse step. `SortedMatch.run` tags the packed witnesses by side, radix
sorts their actual full-state keys and streams adjacent records. Equal keys from
opposite sides have an adjacent boundary even with collisions and duplicates.
The scan keeps one previous record and the first hit, while continuing through
the batch. Its monotone-polynomial time/charged-space bound is
$O(I+(n+1)P(B+1))$, where $I$ is the encoded record list length and $B$ its
maximum record wire length. Tagging, sorting and scanning have separate actual
machine certificates; no semantic dictionary or assumed traversal is supplied.

`SortedMeet.original_machine` composes preparation, both generated arrays,
inverse input/output transforms, matching and original-order witness readback
into one finite deterministic multitape machine before all original widths,
depths and operand lists. It proves exhaustive miss and returned-witness
soundness from the original single-list input, including residual quarters.
`sourceCertificate.time` and `.space` are the composed phase bounds: they charge
all intermediate input/output tapes and callback temporaries, including
simultaneously materialized half lists. These profiles are **not yet reduced to
a global source asymptotic**. This route does not use the projection depth to
select smaller retained classes and does not provide the target
$O^*(2^{q/4}+\mu_p)$ peak space. Actual projected class counts, orientation,
batching and deletion/reuse remain to be integrated. It bypasses the old sparse
interpreter only for this separate route; the old interpreter/compactor costs
remain unchanged. Sharp source time/space and the broader 733 results stay open.

`ClassStreaming.run` provides a separate **class-retaining execution** that avoids
both full half-space arrays. A packed counter evaluates one original forward or
inverse word at a time and tests its low bits. Count-only passes derive occurrence
counts, including equal-state collisions; a count-only outer prepass computes
the maximum of the smaller class sizes before any class is retained. Each class
then computes its retaining orientation, collects only the smaller side, sorts
that class by the existing radix machine, and streams/probes opposite-side words
against it. The original input, class counter and optional hit are the only values
passed between classes. Retained lists do not accumulate across the outer loop.
A hit skips subsequent searches while the fixed binary counter finishes.

`count_eq`, `retained_length` and `balance_eq` derive this behavior from the
executed passes. `global_retained_prefix` bounds every retaining prefix by the
computed maximum. `retaining_prefix_wire` separately derives physical full-state
and packed-witness widths: for half lengths $l,r$, width $m$ and smaller count
$c_g$, the encoded sort input of every retaining prefix is at most
$2m+1+c_g(4m+2(l+r)+3)$ bits. These are **retained-value bounds**, not a substitute
for machine auxiliary-workspace bounds. `original_machine` composes a single
finite multitape machine before all original input parameters, with the actual
balance prepass, counter control, chosen orientation, class sorting, streamed
lookup, release between classes and witness decoding charged in
`sourceCertificate.time/space`. Output is the computed maximum paired with the
optional original-order witness; `.2 = none` proves exhaustive absence.

This route **rescans all half words for each class**, rather than using Lemma 8's
output-sensitive projected-quarter join and dynamic-programming count tables.
Its retained-list lookup is linear, and the certified callbacks currently charge
polynomial time/workspace in the complete retained input. Sorting's simultaneous
input/output buffers and these callback costs remain in the composed profiles.
This earlier route alone does not conclude sharp $O^*(2^{q/2})$ global time or
$O^*(2^{q/4}+\mu_p)$ peak space ($\mu_d=\mu_p$ when $p$ fits). The later
`SourceResources.sourceCertificate_bounds` paragraph gives the whole-run bounds for the assembled projected-quarter route,
which replaces these retained-list callbacks.
The older `SortedMeet` and compacting interpreter implementations are unchanged.

`BatchedAccess.run` refines retained-class access with an actual **bounded
sorted-batch route**. Its capacity is the computed retained occurrence count
$c_g+1$. Accepted opposite records enter a buffer; a full buffer is radix-sorted
and matched against the retained class using `SortedMatch`, then released.
`finish` also tests the final partial batch. The next class starts with a fresh
buffer; a found hit suppresses subsequent batch searches. Every hit retains
original packed witnesses in either orientation, and `original_correct` proves
original-input witness soundness and exhaustive miss. A valid witness can differ
from `ClassStreaming`'s choice because batch order changes which collision is
encountered first.

`source_buffer_bound` derives that every live buffer contains fewer than $c_g+1$
records. `recordWork_bound` and `total_recordWork` bound the cumulative full-batch
and final-batch **record-volume budget** by $4d_g+2(c_g+1)+1$, where $d_g$ is the
number of opposite occurrences fed. This charges retained records again at each
flush; it is not an assumed constant-time dictionary. The implementation uses
structural linear framed insertion for retention and buffers. Only scalar and
single-record inputs enter polynomial callbacks, excluding growing retained or
probe arrays. The composed uniform machine certificates separately include all
sort/scan buffers, intermediate tapes, initialization and readback.

**The volume bound is not a bit-time bound.** In this earlier route, the counter
combinator copies captured retained/buffer state between rounds, and linear insertion
copies the growing buffer. These costs remain in `sourceCertificate.time/space`;
a factor comparable to retained size times streamed words can therefore persist
in bit time even though no per-record dictionary search is executed. The source
class/count generation in this earlier route still repeats half-word scans.
Its volume bounds alone give no sharp global time or peak-space theorem and do
not discharge auxiliary-space obligations. The later assembled route replaces
these costs; see `SourceResources.sourceCertificate_bounds` below for its
whole-run theorem. This is an original batching refinement of the source's
membership stage; the older ClassStreaming/SortedMeet/CompactExecution routes
remain unchanged.

`GroupedQuarter.run` adds a **one-pass equal-key writer** after the actual
original-input quarter generator and radix sorter. It computes Core's
`List.splitBy` consecutive runs, but its realizing bit machine does not build a
growing group in the loop state. It retains only the previous binary key and
writes each record directly into the nested framed output, closing a group when
the key changes and at the end. The exact wire theorem proves those emitted
bytes encode the same grouped records; no grouping decoder is supplied as advice.

For $n$ input records, encoded input length $I$ and maximum record wire $B$,
`KeyGrouping.run_computable` proves time $O(I+(n+1)P(B+1))$ and charged peak space
$O(I+P(B+1))$ for a fixed monotone polynomial $P$. Every logical stream prefix has
a derived previous-key wire bound, and the machine theorem includes the reader,
framing, callback and finalization temporaries. Nested grouped output has exactly
$2I+b$ bits, where $b$ is the number of groups, and is at most $3I$. Input/output quarters are
therefore still charged; this is not a constant-total-space claim. A single
large collision group does not cause quadratic copying of a growing group.

`GroupedQuarter.run_computable` composes original source preparation, packed
index generation, projected evaluation, sorting and grouping into one uniform
bit computation with time and peak space $(2^k+1)Q(I_0+1)$, for fixed monotone
polynomial $Q$, computed $k=(N-1)/4$ and original source wire $I_0$.
The physical key and packed-index widths are derived from the actual prepared
operands. `flatten_run` preserves the exact sorted quarter sequence, while
`original_correct` preserves its original full-width packed-witness semantics
under the admitted depth conditions. Duplicate keys and payload occurrences
are not discarded, including zero-width quarters.

These are **first-quarter buckets**, not the full two-quarter classes $F_g,B_g$,
and they do not compute $\mu_p$.

`ClassJoin` now generates the forward first quarter and genuine inverse
second-quarter queries, tags and sorts their union, and feeds the same one-pass
group writer. `KeyJoin` emits every cross-side occurrence pair in a group;
the installed count machine instead feeds the sorted tagged records directly
to `KeyCount.run`. It keeps the previous key, two run populations and the
accumulated pair count, adding the opposite population on each record. No group
or Cartesian product is built on this count path. `count_streaming` proves exact
agreement with the grouped definition. Collisions and duplicate occurrences
contribute to the count. `original_witnesses` and `mem_fullStates` prove exhaustive
packed-pair semantics and actual original full-width states, with inverse payloads reversed
back to original operator order. Full-state reconstruction uses a real streamed
per-pair callback, charging the original input and one packed pair.

`ClassJoin.table` is a fixed runtime-counter program visiting all $2^p$ computed
forward classes, producing binary counts and releasing each round's quarter/sort
temporaries. `tableCertificate` composes actual preparation, generation, inverse
execution, sorting, direct record counting and loop control. `original_table_zero_iff`
proves an indexed zero is an exhaustive original-input class miss. `table_wire`
bounds the stored table by $2^p(4k+7)$ bits; it does **not** bound the machine's
internal workspace by that table size.

`ClassBalance` now generates both directions. For a backward class it reverses
$Q_4,Q_3$, starts from the complemented target and uses the complemented low-bit
class key; full emitted states are reflected back before matching. Packed
complete-half payloads preserve leading zero operators and the existing reversed
suffix readback convention. `records_nodup` derives unique packed words despite
state collisions. `count_eq_counter` proves exact equality with the original-half
counter counts, and `balance_eq_counter` proves equality of the computed maximum
smaller population. Counts or dictionary correctness are not supplied as advice.

`JoinedDissection.run` receives the original input and computes the balance with
actual counts in both directions. `ClassBalance.balanceCertificate` now streams
class indices and reduces each count minimum into one scalar maximum. It builds
no count table, reverses no table and runs no whole-table minimum/maximum callback.
`balance_eq_prefix` identifies this loop with the existing semantic balance;
`balancePrefix_le` and `balancePrefix_wire` derive its accumulator bound and
half-word-count bit width at every prefix. Count callbacks and index generation
remain charged. The separate table API is preserved, but is not executed by this
solver's balance prepass. The source reachable-state DP's $O^*(2^p)$ count prepass
remains unimplemented.

For each class, actual counts select the smaller retained side. `materialize`
also computes whether the nonempty retained class plus the four quarter
populations can hold the opposite class. If so, `directSearch` generates that
class and invokes the radix matcher once: no dictionary or growing buffer is
passed through a per-pair feed. Otherwise the installed fallback is now `ClassBatches.run`, which regenerates
bounded row-aligned quarter windows and matches each completed batch. Empty retained dictionaries still skip
opposite generation by matcher soundness. Class release, original-order decoding,
`original_correct` witness/miss semantics and `original_balance` are preserved.
Orientation/branch selection use generated counts, not cached-size advice.

`quarterBudget_source` bounds the four-population allowance by $11\cdot2^k$ for
the actual source quarter cut, including all fourth-quarter residue cases.
`direct_prefix_wire` bounds the retained dictionary plus every direct output
prefix by $(2\mu+Q)(4m+2q+3)$ bits, where $Q$ is this computed quarter allowance.
`sum_directRecordWork` bounds all directly matched dictionary/opposite input
record volumes by the two half populations. These logical wire/record-volume
bounds do not bound internal matcher/producer workspace or establish bit time.
The preserved older `JoinedProbe` component retains `simultaneous_wire`; it is
not the installed fallback. The separate table API retains
`source_count_prefix_wire`; its table is not an accumulator of this solver.
Here $\mu$ is the computed maximum, not an expectation.

`allSearch_wire` derives packed output bit width from actual witness provenance.
`preparation_readback_bounds` proves a common monotone polynomial in the physical
original-input wire bounds the sum of time and the sum of every-prefix charged space of actual input
preparation, half-array construction and the installed final decoder, evaluated on the real search result.
No witness-size or decoder-execution conclusion is a premise. This covers these
boundary phases only; it excludes balance/count callbacks and search. The uniform
`sourceCertificate` includes all remaining internal tapes and composed costs.

The actual count consumer has $O(I+(n+1)P(B))$ bit time and
$O(I+P(B))$ charged peak space, where $I$ is the sorted record wire,
$n$ its record count, and $B$ the maximum record width plus the binary length of
$n^2+1$ and one. The latter covers all three counters at every prefix, including
an entirely colliding run. Callback tapes, state/token framing, initialization
and binary output are charged by `KeyCount.run_computable`. This bound replaces
the former whole-group polynomial count callback in the assembled certificates;
it is a count-consumer bound, not a global solver theorem. Quarter generation,
sorting, all-class control and their materialized phase boundaries remain charged.

Retention now also bypasses the generic polynomial grouped join callback.
`KeyJoinStream.join_computable` executes actual side-tag filters, then nested
record streaming. Replaying the right occurrence run for each left record is
charged to the emitted Cartesian pairs. Outer control streams groups without a
growing output accumulator. If $N$ is the number of input quarter records, $M$
the emitted class population, $G$ the group count and $B$ the maximum physical
row width plus one, both time and charged prefix space are
$O((N+M+G+1)P(B))$. This includes filtered runs, decoded current group, callback
tapes, framing/state replay and final materialized class output. Generated groups
are nonempty, so $G\le N$; `groups_volume` derives the quarter input size and
`ClassBalance.retained_join_volume` bounds the selected output factor by the
actual computed balance. Both orientations and full-state reconstruction inherit
the installed machine through `witnessesCertificate`. This remains a join-phase
bound; preparation, quarter generation/sorting and full-state readback have
separate composed profiles.

`sum_pairVisits` bounds the source class pair populations across classes by
at most $2^{|Q_1|+|Q_2|}+2^{|Q_3|+|Q_4|}$. Duplicate full states still correspond
to distinct packed words; both orientations, empty-dictionary skipping and
early-hit parking are included.
This bounds the pair domain, not the restarted machine's bit cost.

The consumer and class loop reuse
[`NativeCertificate.foldlStream`](../../CslibFrontier/Computability/GenericRAM/Native/StreamingFold.lean),
the actual encoded streaming kernel: each list is read once. Time charges input/setup and finalization plus the sum of actual callback
time and current/next state/token framing. Space takes actual callback,
prefix-state and token maxima; the returned state is charged separately, without
adding the entire loop clock to workspace. These prefix measures are derived,
not supplied invariants. Scalar index/full-state callbacks receive isolated
records/original input; side filters use the proved physical-width streaming
filter. `ClassBatches` now replaces that per-pair fallback in the assembled
solver. Its window producer receives only source operands, side, class and binary
rank bounds; it never receives the retained dictionary or a growing batch state.
`KeyJoinBatch.window` selects whole right occurrence rows whose first Cartesian
rank falls in the batch interval. It scans quarter lists and emits only selected
cross products, avoiding per-pair lookup or generation of skipped Cartesian pairs.
A row crossing an interval boundary is emitted in full by its starting window.
`window_cover` and `window_mem_join` prove coverage/provenance, including empty
groups and collisions; `window_length` bounds output by capacity plus quarter input.

Capacity is retained count plus one plus produced quarter volume $N$. Each
restart uses actual generated labels, padded to a power of two and guarded before
batch generation. `batchCount_le_quarter` and `labels_wire` bound this data by
quarter scale with binary framing. The fixed label loop holds only the retained
parameter and optional witness; it releases a batch before the next one. The
parameter is copied per batch rather than per pair. Pair/full-state callbacks
receive isolated records/original input, and count/cut state uses binary scalars.
`NativeCertificate.emitFoldCertificate` reuses the real framed kernel, accumulating
output on the output tape rather than in the evolving callback state. Actual
callback clocks, framing, both filtered runs, selected output, scalar state,
setup/finalization and matcher tapes remain charged.

`restart_prefix_wire` bounds dictionary plus every logical output prefix by
$(2\mu+2Q+1)(4m+2q+3)$ bits, where $Q$ is the four-quarter allowance.
`copyAllowance` charges all generated restart labels by at most $2M+4C$, with
produced population $M$ and computed capacity $C$. Regenerating quarters is paid
because $C\ge N$; retained input is paid because $C$ exceeds retained size.
`sum_restartCopyWork` bounds this allowance over all classes by
$6(2^{|Q_1|+|Q_2|}+2^{|Q_3|+|Q_4|})+4\cdot2^p(Q+1)$.
This is a global repeated-input volume bound, not a proved global bit-time bound.
The actual machine profiles still need composition/normalization in scalar widths.
[`SortedMatchBounds.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Algorithms/SortedMatchBounds.lean)
now bounds the installed tagging/radix-sort/witness-scan certificate by record
volume times one fixed monotone polynomial in physical key/record width.
[`AddXNORMatcherResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORMatcherResources.lean)
includes the two-orientation wrapper's framed argument copies and derives row
width $B=2m+1+q$ from original words and packed indices. Its
`original_restart_bounds` proves actual fallback matching clock sum at most
$4[6(2^{|Q_1|+|Q_2|}+2^{|Q_3|+|Q_4|})+4\cdot2^p(Q+1)]P(B)$ and each
matching machine's all-prefix workspace at most $2(\mu+Q+1)P(B)$.
The polynomial is fixed before all input widths/classes; collisions, empty and
padded batches require no unit-cost-record assumption. These bounds include
matcher auxiliaries but exclude count/division, regenerated-quarter/window/
full-state producers and outer control, so they are not a global solver bound.
The complete restarted client checks a genuine fallback residue, batches crossing
rows, padded labels, non-self-inverse addition, a returned original witness and
an exhaustive miss, rather than only the selected single-match branch.

[`AddXNORProducerResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORProducerResources.lean)
now normalizes the installed count route's actual preparation, forward/inverse
quarter generation, reflection, tagging, sorting and one-pass count allowances.
Its counter polynomial sees binary width derived from quarter populations, not
the numeric population or an assumed class size. With $V=6H+4\cdot2^p(Q+1)$,
`original_count_bounds` charges both orientations over all classes by
$2^p(Q+2)P(B)$, where $B$ is original encoded-input length plus $p+1$.
`original_restarted_count_bounds` charges opposite counting repeated at every
generated restart label by $VP(B)$. This pays real recomputation with capacity,
not just copied input. It is not the source's reachable-state-DP fast prepass.
`original_reconstruction_sum` charges actual window full-state evaluation by
$4VR(B+q)$ and each reconstruction prefix by $2(\mu+Q+1)R(B+q)$, including
pair input, reconstructed output and internal callback tapes. Pair widths are
derived from actual original quarter witnesses, even with collisions.
These phase allowances reuse the approved matcher bound. The window scan/cut/division
phase is now normalized below; retained/group-emission composition, internal
class-search control and simultaneously live ambient frames still require composition.

[`AddXNORWholeRunResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORWholeRunResources.lean)
now connects those outer/boundary costs to the actual installed `sourceCertificate`.
For original physical input length $I$, computed class count $G$, installed balance
allowances $T_b,S_b$, search-time sum $T_c$ and search-workspace maximum $S_c$,
`sourceCertificate_bounds` proves
$$
T_{\mathrm{source}}\le T_b+(T_c+G+1)P(I),\qquad
S_{\mathrm{source}}\le S_b+(S_c+G+1)P(I).
$$
One monotone polynomial is fixed before all inputs. These are real installed
subprogram allowances, with no supplied execution or runtime conclusions.
The unchanged streaming fold's actual callback-time sum and prefix-space maximum
are exposed by
[`StreamingFoldBounds.lean`](../../CslibFrontier/Computability/GenericRAM/Native/StreamingFoldBounds.lean).
Captured parameters, every prefix state, input/output/framing and generated
class-index data are charged. Parked packed-witness widths follow from original
soundness, including empty lists and early hits. The complete client computes
non-unit/empty fold budgets and applies the envelope to the actual arithmetic fallback.
[`AddXNORBalanceResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORBalanceResources.lean)
closes the installed balance prepass, including both regenerated count callbacks,
scalar min/max, every prefix state, label generation and copy/frame workspace.
For actual quarter population $Q$, its `balanceCertificate_bounds` gives
$T_b\le 2^p(Q+2)A(B)$ and $S_b\le(2^p+Q+2)A(B)$ in original quarter-input
width $B$. The actual source cut has $Q\le11\cdot2^{\lfloor q/4\rfloor}$ and capped
$p\le\lfloor q/4\rfloor$. Thus `source_balance_bounds` derives half-exponential time
and quarter-exponential workspace in original physical input bits, without a
supplied resource invariant. `sourceCertificate_search_bounds` composes this into
the unchanged whole run:
$$
T_{\mathrm{source}}\le (T_c+2^{\lfloor q/2\rfloor})P(I),\qquad
S_{\mathrm{source}}\le (S_c+2^{\lfloor q/4\rfloor})P(I).
$$
The client checks the actual arithmetic fallback and zero-width/no-operator input
with an overlarge requested class depth. These are not sharp whole-run bounds:
$T_c,S_c$ still include unnormalized window scan/cut/division, retained/group
emission and internal class-search lifetimes. Regenerated counts fit the
half-exponential total time but do not prove the source's faster quarter-time
reachable-state-DP all-count prepass, which remains open.

[`AddXNORSearchResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORSearchResources.lean)
normalizes the actual class-pair and full-state producers, using the approved
quarter/sort/count and matcher bounds. `classSearch_bounds` closes all selected
direct searches, including actual count-selected orientation/materialization,
both generated classes and matching/input/output/internal tapes. Its time sums
computed class populations; its workspace uses the materialization test to derive
that the opposite class fits the retained class plus $Q$, then bounds the smaller
class by actual computed balance $\mu$. No desired class-memory bound is a premise.
`restartTime` and `restartSpace` are the sum/max of the installed search allowances
on classes selecting restart, conservatively including classes skipped after a hit.
`sourceCertificate_restart_bounds` now gives
$$
T_{\mathrm{source}}\le (R_T+2^{\lfloor q/2\rfloor})P(I),\qquad
S_{\mathrm{source}}\le (R_S+2^{\lfloor q/4\rfloor}+\mu)P(I).
$$
The direct-branch client derives both whole-source bounds on a real original input
with two colliding low-bit classes, and checks a full-state miss with complete
projected collisions. The arithmetic fallback client checks that the residual still
contains its full class-search costs. These residual expressions are actual certificate
costs, not supplied runtime
hypotheses. `SourceResources.source_restart_bounds`, described below, now normalizes
both for the general restarted branch and composes the whole-run bounds.

[`StreamingEmitBounds.lean`](../../CslibFrontier/Computability/GenericRAM/Native/StreamingEmitBounds.lean)
now bounds the unchanged installed emitter by summed actual callback clocks and
summed token wires, with a separate maximum for callback workspace and every
prefix state charged. This matters when tokens are whole groups: multiplying
maximum group wire size by the number of groups introduces an unnecessary
quadratic term. [`KeyJoinBatchBounds.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Algorithms/KeyJoinBatchBounds.lean)
applies this to the actual window certificate. Its binary skip/count state never
exceeds the original scalar widths. At each prefix, emitted population plus
remaining capacity is at most initial capacity plus quarter records scanned;
empty groups, collisions, zero capacity and a cut Cartesian row are included.
The complete batch client applies the certificate to arbitrary runtime source
contexts and checks uneven groups.

[`KeyJoinBatchCallbackBounds.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Algorithms/KeyJoinBatchCallbackBounds.lean)
now normalizes the actual callback profiles: binary length scans, side filters,
population multiplication, ceiling division, cut scans and selected Cartesian
emission. The fixed polynomial sees binary scalar and individual-record wires;
whole-group list length is only a linear factor. Actual callback time is summed;
workspace uses its prefix maximum and charges input/output/internal tapes.
[`AddXNORRestartResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORRestartResources.lean)
derives these scalar widths from original operands and generated labels in both
computed orientations. `original_window_bounds` charges each actual window and
its callbacks by capacity times a fixed polynomial in original widths.
`original_window_sum` amortizes the installed window clocks over every class/label
using computed capacities, and bounds each window's workspace by computed balance
plus quarter volume. `source_window_bounds` specializes the actual source cut to
$2^{\lfloor q/2\rfloor}P(I)$ summed window allowances and
$(2^{\lfloor q/4\rfloor}+\mu_p)P(I)$ simultaneous window workspace.
[`AddXNORBatchResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORBatchResources.lean)
composes these windows with actual recomputed counts/division, quarter generation/sort,
full-state reconstruction, retained-context copies and either computed matcher orientation.
`matchLabelCertificate_bounds` bounds the installed guarded label callback, including its
padding-label miss branch. `source_label_bounds` gives the same half-time and
quarter-plus-balance bounds for the sum of complete callback allowances and each callback's
all-prefix workspace. Scalar factors use original widths; the dictionary contributes linearly
through actual computed capacity, amortized over labels.
These are callback-phase bounds. The enclosing setup/loop and retained/ambient
composition is supplied by the following resource endpoint. Source reachable-state-DP all-count/fast
prepass and the other paper objectives remain open.

The binary layouts in these public APIs use documented reducible names: `encNatPairList`
frames each binary pair (whose second coordinate is unframed), `encNatPairOption` uses
an empty word for `none` and a true bit before a `some` pair, `encFoldStep` frames the
parameter/state pair before the unframed record, and `subsetSumEncoding` frames the
binary number list before its unframed binary target. They preserve the existing
encodings without defaults or typeclass selection.

The all-class search uses the same fixed streaming kernel over an actually
generated class-index list. The approved uniform index generator supplies its
real time/space profile and the derived wire bound $2^p(2p+1)$; the capped source
depth makes this extra data quarter scale. It is data for a fixed machine, not
input-dependent program advice. `allSearch_eq_fold` connects that execution to
the approved fixed class counter. Its clock sums executed class rounds, including
found-hit parking; workspace takes their actual prefix maximum, with each class
released before the next and only a found pair surviving. Index generation,
framing, setup and readback remain charged.

[`AddXNORBatchLoopResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORBatchLoopResources.lean)
now charges the actual generated-label setup, scalar controls, option parking and
retained-context frames around the callbacks. `prefix_wire` derives each parked
witness's physical width from actual full-state matching. `runCertificate_bounds`
uses the installed streaming fold's clock sum and workspace maximum: time is
label count times capacity times an original-width polynomial, while simultaneous
space pays capacity once. Label storage, initial/final framing and empty/padding
branches are included. The setup and round certificates factor the existing bodies;
they preserve the loop's actual time/space profiles.

[`AddXNORSourceResources.lean`](../../CslibFrontier/Cryptanalysis/AddXNORSourceResources.lean)
composes original-input orientation/counts, retained construction, task/context
layout, labels/parking, every producer/matcher callback, class release and ambient
frames. `source_restart_bounds` closes the general restart sum/max. Its
`sourceCertificate_bounds` then composes the approved DIRECT, balance and whole-run
preparation/readback envelopes to prove
$$
T_{\mathrm{source}}\le 2^{\lfloor q/2\rfloor}P(I),\qquad
S_{\mathrm{source}}\le (2^{\lfloor q/4\rfloor}+\mu_d)P(I).
$$
This bounds the existing uniform deterministic multitape certificate, including
encoded input/output and internal tapes at every execution prefix. $I$ is the
physical original input size (unary word width/requested depth and binary original
operand list); $q$ is the number of operators. The first operand is the seed,
the target is zero, the fourth quarter keeps the remainder, and the existing
machine computes $d=\min(p,m,\lfloor q/4\rfloor)$ from the requested depth $p$.
The balance in this bound is $\mu_d$, namely
`ClassBalance.balance (Source.prepare original)`; when the requested depth fits
width and quarter size, $d=p$. It is derived from actual counts, rather than
supplied as a space bound; no direct-only restriction or runtime conclusion is
a premise. `JoinedDissection.original_correct` supplies witness soundness and
exhaustive misses for the same executed function. The complete client couples
this correctness and both resource inequalities for arbitrary typed source inputs,
as well as arithmetic hit/miss, backward retention and empty/zero-width cases.

These are the whole solver's worst-case time/space bounds, not the complete
source Theorem 7: reachable-state-DP all-counts and the faster quarter-time balance
prepass remain unproved. The old association-list/cubic-filter interpreter is
unchanged; the resource theorem uses the assembled sorted-list route. Other
small-operand, multiplicity, sparsification and ideal-model paper objectives also
remain open.

The reachable-state counter DP now has a concrete binary-addition stage in
[`AddXNORCounterSerialization.lean`](../../CslibFrontier/Cryptanalysis/AddXNORCounterSerialization.lean).
`forward_layer_append` and `backward_layer_cons` identify the streamed sums with
the next original-input DP table, including repeated states and zero counters.
`layer_certificate` fixes one multitape machine before all widths and operands.
On the derived interleaved pulled-table input, both its bit time and charged
prefix workspace are at most $O(2^p P(q+1))$ for a fixed monotone polynomial $P$.
The $q+1$ counter-bit budget follows from the original operator count; addition
is executed on binary strings rather than charged as a unit-cost operation.
The input uses framed binary pairs (first coordinate framed, second unframed),
and the output is a framed list of binary counters.

This certificate starts **after** the two pull transformations and interleaving.
It includes the addition pass's input/output and callback temporaries, but does
not charge generation of that input. The state-keyed pull/pair/add route below
addresses those stages; initialization, indexing for reuse, the operand loop and
readback still need composition
to obtain Lemma 8's $O^*(2^p)$ all-count prepass. The installed dissection
certificate and its proved whole-run bound are unchanged. The checked client is
[`AddXNORCounterSerialization.lean`](../../CslibFrontierTests/AddXNORCounterSerialization.lean);
from the repository root run
`lake build CslibFrontierTests.AddXNORCounterSerialization --wfail --iofail`.

[`AddXNORCounterPull.lean`](../../CslibFrontier/Cryptanalysis/AddXNORCounterPull.lean)
now implements those permutations by streaming binary state/counter records
through the original step or its actual inverse, then radix-sorting the keys.
There is no per-state table lookup. `run_table_eq` proves that the output is
exactly the selected native recursive pull in ascending numeric state order,
including all zero counters. `source_certificate` fixes one uniform multitape
machine with time and charged prefix workspace $O(2^p P(p+q+1))$ on the actual
original forward/backward counter tables. The polynomial covers unary width,
binary operands/counters, mapping, sorting, framing and simultaneous buffers;
the counter-bit bound is derived from the original operator count.

The earlier addition examples specify alignment with `List.zip`; the executable
replacement is now in
[`AddXNORCounterPairing.lean`](../../CslibFrontier/Cryptanalysis/AddXNORCounterPairing.lean).
It reads the original keyed counter table once and emits both actual relocations,
using the generated key $2\,\text{state}+\text{side}$. One radix sort makes each
state's two counters consecutive. `AdjacentPairs` retains one payload, emits its
pair with the next payload, then clears its state. `BinaryPairSums` executes the
binary addition. `pairs_table` derives exact alignment; `layer_table` proves the
native `countAdvance` or `countBackAdvance` result for arbitrary tables and both
directions. No caller supplies an alignment, execution or resource conclusion.

`layer_computable` charges the mapper, sort, pairing and adder, with a linear
record-volume factor times a polynomial in header and maximum record width.
`source_certificate` derives time and charged every-prefix workspace
$O(2^p P(p+q+1))$ on the actual original forward/backward counter tables. The
input, doubled tagged records, sort buffers, retained counter, paired output,
binary-arithmetic temporaries and final count list are included. The generic
adjacent writer discards an unmatched final record; the source proof derives an
even stream with exactly two records per state, including zeros and equal counts.

The output is a counter list in numeric state order. Efficiently restoring its
keys for another pass, table initialization, the complete operand loop with
reuse and readback remain necessary for the full DP and Lemma 8's faster prepass.
The older `WordTable.entries` uses recursive low-bit-child order; that order is
kept distinct. The checked clients include actual forward and inverse updates,
zero width, zero counters, collisions and non-self-inverse addition. From the
repository root run
`lake build CslibFrontierTests.AddXNORCounterPairing --wfail --iofail`.

The installed fallback is checked by
[`CslibFrontierTests/AddXNORClassBatches.lean`](../../CslibFrontierTests/AddXNORClassBatches.lean),
including actual hit/miss runs with non-self-inverse addition in the inverse direction.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORSourceResources`, then run
`lake env lean CslibFrontierTests/AddXNORClassBalance.lean` and
`lake env lean CslibFrontierTests/AddXNORJoinedDissection.lean`; also run
`lake env lean CslibFrontierTests/KeyCount.lean` for the direct streamed counter and
`lake env lean CslibFrontierTests/KeyJoinStream.lean` for the retained join and
`lake env lean CslibFrontierTests/AddXNORClassBatches.lean` for the installed restarted fallback;
use `lake env lean CslibFrontierTests/AddXNORJoinedProbe.lean` for the online opposite
consumer. The
[class-balance client](../../CslibFrontierTests/AddXNORClassBalance.lean) checks
unequal computed populations, both orientations, empty backward classes and
fourth-quarter residue, including execution of the actual new count path in
both directions. The [counter client](../../CslibFrontierTests/KeyCount.lean) checks
empty/one-sided runs, repeated occurrences and key changes. The
[join client](../../CslibFrontierTests/KeyJoinStream.lean) checks ordering, duplicates,
empty groups and the uniform input/output-sensitive resource theorem. The
[online consumer client](../../CslibFrontierTests/AddXNORJoinedProbe.lean) exercises
full-batch release/parking, final partial flushes, empty dictionaries/classes,
zero width/quarters and raw zero capacity. The complete
[joined dissection client](../../CslibFrontierTests/AddXNORJoinedDissection.lean)
executes original non-self-inverse additions/collisions through decoded hits and
exhaustive misses, including zero/empty/capped input. It also applies the general
correctness, computed-balance, logical-prefix wire and actual machine certificates.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORClassJoin`, then run
`lake env lean CslibFrontierTests/AddXNORClassJoin.lean`. The
[class-join client](../../CslibFrontierTests/AddXNORClassJoin.lean) executes real
non-self-inverse addition with colliding projected keys, all-class counts,
full-width retained records, exhaustive zero counts, duplicate occurrences and
zero/empty/capped inputs. It also applies the arbitrary-width original-input
semantics and actual source/count/state/table machine certificates.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORGroupedQuarter`, then run
`lake env lean CslibFrontierTests/AddXNORGroupedQuarter.lean`. The
[grouped-quarter client](../../CslibFrontierTests/AddXNORGroupedQuarter.lean) executes
large single groups, duplicate payloads, key changes, original-operand generation,
width/depth capping, zero/empty inputs and exact nested encoding, and instantiates
the arbitrary-input time/space theorems.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORBatchedAccess`, then run
`lake env lean CslibFrontierTests/AddXNORBatchedAccess.lean`. The
[batched access client](../../CslibFrontierTests/AddXNORBatchedAccess.lean) executes
full-batch hits, missed-batch release followed by a partial-batch hit, early-hit
parking, both computed orientations, duplicates, empty/zero-width cases and the
complete original-input uniform machine. It also checks actual capacity validity
and instantiates the separate record-volume theorem.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORClassStreaming`, then run
`lake env lean CslibFrontierTests/AddXNORClassStreaming.lean`. The
[class-streaming client](../../CslibFrontierTests/AddXNORClassStreaming.lean) executes
both count-selected orientations, collisions, class misses, zero width, empty
tails, residual quarter cuts and original-order inverse readback. It instantiates
the general prefix-volume, correctness and uniform-machine certificates.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORSortedMeet`, then run
`lake env lean CslibFrontierTests/AddXNORSortedMeet.lean`. The
[matching client](../../CslibFrontierTests/AddXNORSortedMeet.lean) executes forward
and inverse original-input generation, non-self-inverse addition, full-state
collisions, empty/zero-width inputs and misses, and instantiates the arbitrary
input correctness and actual uniform machine certificates.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORSourceQuarter`, then run
`lake env lean CslibFrontierTests/AddXNORSortedQuarterMachine.lean`. The
[integrated client](../../CslibFrontierTests/AddXNORSortedQuarterMachine.lean) starts
from original operands, checks a real non-self-inverse addition quarter, stable
full-state/projected collisions, computed seed/depth/cut, capped/zero widths and
empty inputs, and instantiates the arbitrary-input machine/resource theorem.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORSortedRecords`, then run
`lake env lean CslibFrontierTests/AddXNORSortedRecords.lean`. The
[sorting client](../../CslibFrontierTests/AddXNORSortedRecords.lean) checks arbitrary-width
machine bounds, stable duplicate payloads, empty/zero-width lists, an excluded
nonfitting key, non-self-inverse addition/XNOR collisions, witness unpacking,
nonzero-default deletion and a residual source quarter cut.

From the repository root, build `lake build CslibFrontier.Cryptanalysis.AddXNORSource`,
then run `lake env lean CslibFrontierTests/AddXNORCompactExecution.lean`. The
[complete compact/source client](../../CslibFrontierTests/AddXNORCompactExecution.lean)
checks that three historical zero stores and the zero input header consume four
bindings in the old interpreter but none in the actual compacting loop. It also
checks nonzero overwrites/defaults, all quarter residues, depth capping, a colliding
source hit with addition/XNOR, an empty-tail miss and a bound for arbitrary parked
prefixes. For sharp-resource work, inspect the internal round/output-reader
workspace profiles as well as the retained-state encoding bound.

From the repository root, build
`lake build CslibFrontier.Cryptanalysis.AddXNORUniformExecution`, then run
`lake env lean CslibFrontierTests/AddXNORUniformExecution.lean`. The
[execution client](../../CslibFrontierTests/AddXNORUniformExecution.lean) uses one
source machine for an unequal-quarter colliding strict-inverse hit and an exhaustive
empty-quarter miss. It also checks addition versus overflow, arbitrary runtime
program fields, empty programs, a huge binary label, parking refinement and the
prefix resource bound. Inspect both the runtime execution certificate and its
full encoded trajectory before transferring a source resource claim.

From the repository root build
`lake build CslibFrontier.Cryptanalysis.AddXNORGeneratedRunInput`, then run
`lake env lean CslibFrontierTests/AddXNORProgramGeneration.lean`. The
[complete client](../../CslibFrontierTests/AddXNORProgramGeneration.lean) checks concrete
metadata/literal values, instruction roundtrip/rejection, general generation
certificates, physical width/clock and stored input cells, strict inverse/collision
and nonempty forward runs, and empty hit/miss outputs. A native-code change that
breaks `literals_exact` or `graph_exact` requires updating and rechecking the literal
template against the actual definitions; do not replace these checks by assumed
code equality. A source resource claim needs the uniform execution profiles and its remaining
sharp-resource proofs rather than an application of `packet_resources`.

From the repository root, run
`lake build CslibFrontier.Cryptanalysis.AddXNORNativeClassSearch` followed by
`lake env lean CslibFrontierTests/AddXNORNativeClassSearch.lean`.
The [complete client](../../CslibFrontierTests/AddXNORNativeClassSearch.lean)
instantiates every raw premise at nontrivial widths for arbitrary targets/classes,
then checks a class hit and an exhausted class for the same original instance,
non-self-inverse additions, replacement collisions, zero-width indexed duplicates,
and whole-program empty-quarter hit/miss runs. Separate arenas or increase width
when fit/separation fails; dictionary cells must actually start at zero. The scan
and retention contracts expose their returned increment register, and the scan also
exposes its restored packed word, so outer loops reuse proved register facts.

This older API searches one class and always retains the forward side. The
`Driver.dissection_exec` endpoint above supplies actual counter-table selection
and native iteration/release across classes. `Driver.original_resources` supplies
the composed native time and simultaneous prefix-space theorem. A local miss from the older API is
not a global no-instance conclusion. The following backward-record consumer
cannot substitute for the forward retained dictionary.

For consecutive backward preparation and native forward retention, import
`CslibFrontier.Cryptanalysis.AddXNORNativeBackwardRetain` and apply
`Quarter.Backward.prepareRetain_exec`. In addition to the preparation layout,
supply a separate forward operand array below the dictionary, disjoint from
heads and records, and zero dictionary memory. The program loads the selected
head and transfers registers itself. Its conclusion derives the exact dictionary
insertion stream and originating-record payloads, including collisions and zero
indices, while framing other memory and preserved registers. The complete
[composition client](../../CslibFrontierTests/AddXNORNativeBackwardRetain.lean)
can be checked with `lake env lean CslibFrontierTests/AddXNORNativeBackwardRetain.lean`
after building its import. This forward consumer of inverse records is a bounded
component; it does not implement the source's full backward-half enumeration or
the projected-query/probe/global pipeline.

The direction-exchanged head lookup is available separately from
`CslibFrontier.Cryptanalysis.AddXNORNativeOppositeQuery` as
`Quarter.Backward.queryBucket_exec`. Starting with forward-order operands at
`base`, the class value in `state`, the projected modulus and the original packed
index, it charges forward evaluation and the two head-address/load instructions.
It preserves all memory and the packed index. `Backward.retainedMemory_linked`
shows that the computed retention memory preserves every prepared inverse bucket,
including buckets other than the consumed one. The complete
[forward-query client](../../CslibFrontierTests/AddXNORNativeOppositeQuery.lean)
checks addition by one (distinguishing forward and inverse lookup) and a
zero-width collision. Build the module, then run
`lake env lean CslibFrontierTests/AddXNORNativeOppositeQuery.lean`.
Use `projectedProbe_exec` above for the bounded raw-input projected-query/scan
connection; these older interfaces alone do not certify a complete class search.

To execute the complete opposite-class consumer, use `Quarter.probeClass`
from the same import and root-context client above. Set `count` to the second
quarter length and `stop` to $2^{\text{count}}$; supply `initial` as the projected
class value, `heads` as the backward first-quarter bucket table, and
`Dictionary.table` as the retained dictionary base. `projectedBase` addresses
forward-order projected operands, while `fullBase` addresses reversed full-width
operands; set `projectedModulus` and `fullModulus` to their respective powers of
two. The code computes the projected forward image of the class value for each
packed index, loads exactly that bucket, and calls the early-exit backward scan.
It resets its own packed index, tag, zero and one registers. A hit sets `stop`
to the current index, preserving `operators`, `firstOperators`, `operand` and
`bits` as the opposite and retained witness words. Decode the retained first
index as `operand - 1` only when its tag is nonzero.

The checked client executes later-index success, full exhaustion, empty buckets,
an empty index range and success before an invalid later bucket. The
`probeClass_prefix_memory` theorem proves memory preservation at every execution
prefix. `probeClass_exec` in `CslibFrontier.Cryptanalysis.AddXNORNativeClassProbe`
now proves general termination, exact complete-stream hit/miss semantics and
payload provenance, with a decreasing finite counter and a charged budget.
`searchClass_exec` above supplies its constructed buckets/dictionary and original
chain interpretation from raw input. That older component alone does not supply
counter-selected orientation or global computed-balance resources;
`Driver.original_resources` above supplies the native composition. The source
sorted-list bit-operation
model remains distinct.
[grs12]: ../sources.md#grs12
[heath24]: ../sources.md#heath24
[hk21]: ../sources.md#hk21
[hkn24]: ../sources.md#hkn24
[iknp03]: ../sources.md#iknp03
[jrr25]: ../sources.md#jrr25
[kov17]: ../sources.md#kov17
[ks08]: ../sources.md#ks08
[ll24]: ../sources.md#ll24
[lp09]: ../sources.md#lp09
[np01]: ../sources.md#np01
[yao86]: ../sources.md#yao86
[yekhanin12]: ../sources.md#yekhanin12
[zre15]: ../sources.md#zre15
