# Protocol models, ideal oracles, and privacy

The general [public-coin interactive-reduction model](interactive-reductions.md), including sumcheck/GKR and efficient straight-line extraction/honest-verifier simulation, has a separate account.

## Sigma protocols and explicit extraction

[SigmaProtocol](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Basic.lean#L78) specifies an honest commitment PMF with private state, a deterministic response to a challenge, and Boolean verification. `Complete`, `SpecialSoundness` and `SpecialHVZK` express correctness, extraction from two accepting same-commitment/distinct-challenge transcripts, and exact simulation at each fixed challenge. The extractor may target a different relation, accommodating relaxed lattice witnesses. The generic interface has no native efficiency built in [complexitylib][complexitylib].

[SigmaProtocol/Efficient.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Efficient.lean) adds encodings and machine-backed extraction/simulation predicates (`EfficientSpecialSoundness`, `EfficientSpecialHVZK`). A simulator certificate compares a strict-PPT realization with an exact `SpecialHVZK` law using an explicit statistical error `δ : I → ℝ≥0∞`; `δ` is not constrained inside `EfficientSpecialHVZK` (`δ i ≥ 1` makes `SimulatorRealizedBy` vacuous), so security claims must state their concrete or `Negligible` bound on `δ` explicitly. These additions do not retroactively make every semantic Sigma instance efficient. Schnorr and Lyubashevsky clients exercise the interfaces; the latter has separate native-extraction modules.

When statistical simulation is too strong or callers interact through game indistinguishability, import `Complexity.Crypto.Protocols.SigmaProtocol.Computational` ([SigmaProtocol/Computational.lean](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean)), which formalizes Boneh and Shoup's Attack Game 20.4 and Definition 20.6 ([bs23][bs23], Section 20.4.2, p. 840):

- **Two-stage distinguishing game ([CHVZKAdversary](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L107), [chvzkRealGame](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L217), [chvzkSimGame](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L228)):** at security parameter `n`, `i ← setup n` is passed to `adversary.choose n i`, which outputs an encoded witness-statement candidate `(xw, yw)` and saved `state` word (`CHVZKAdversary.IsPPT` clocks `choose` on `(1^n, i)` and `guess` on `(1^n, state, conv)`). When `(xw, yw)` decodes via `encW i` and `enc.statement i` to a valid `(x, y)` in `R i`, `chvzkRealGame` runs `adversary.guess` on an honest encoded conversation while `chvzkSimGame` samples `c ← PMF.uniformOfFintype (C i)` and runs the simulator `sim (i, enc.statement i y, enc.challenge i c)` without `x`; invalid choices output `false` in both experiments so `R i` need not be efficiently decidable by the challenger.
- **Predicate and acceptance parameter ([ComputationalSpecialHVZK](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L243)):** bundles uniform strict PPT admissibility of `sim`, acceptance probability at least `1 - δ i` on every `(i, y, c)` (`δ = fun _ => 0` gives exact Definition 20.6 acceptance; non-zero `δ` accommodates strict fair-coin approximations of non-dyadic distributions), and `Game.Indistinguishable` against all strict-PPT `CHVZKAdversary` distinguishers.
- **Statistical-to-computational bridge and Schnorr instance:** [SimulatorRealizedBy.advantage_chvzkGame_le](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L326) bounds Attack Game 20.4 advantage against *arbitrary* (even unbounded) adversaries via `Game.advantage_bind_le_of_closeTo` ([Game/CloseTo.lean](../../Complexity/Crypto/Game/CloseTo.lean#L130)), yielding [EfficientSpecialHVZK.exists_computationalSpecialHVZK](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L375) whenever `δ` is bounded along `setup` by a `Negligible` function and [SimulatorRealizedBy.computationalSpecialHVZK_of_accepts](../../Complexity/Crypto/Protocols/SigmaProtocol/Computational.lean#L347) when exact acceptance holds separately. In [SchnorrProtocol.lean](../../Complexity/Crypto/Computational/SchnorrProtocol.lean#L300), `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr` establishes `ComputationalSpecialHVZK` with exact zero acceptance error (`δ = fun _ => 0`) for any `setup : ℕ → PMF F.Desc`.
- **Two-sided separations ([ComplexityTests/ComputationalSpecialHVZK.lean](../../ComplexityTests/ComputationalSpecialHVZK.lean)):** `not_computationalSpecialHVZK_sendWitness` proves that the perfectly `SpecialHVZK` protocol `sendWitnessFamily F` fails `ComputationalSpecialHVZK` under `F.DiscreteLog setup` for *every* `sim` and *every* `δ` (without invoking `accepts`), while `computationalSpecialHVZK_prgWitnessSigma` and `exists_computationalSpecialHVZK_and_not_specialHVZK` construct from any stretching `PseudorandomGenerator` (or uniform `OneWay` function) a complete Sigma protocol family satisfying `ComputationalSpecialHVZK` with `δ = fun _ => 0` that fails `SpecialHVZK`, `EfficientSpecialHVZK` for every `δ`, and even unbounded statistical HVZK below error `1 / 4`.

Abort is observable in [Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/Abort.lean): accepted transcripts and conversations return `Option`, with `none` representing abort. `NonAbortSpecialHVZK` matches the entire law including abort mass. Nonabort completeness alone does not give a lower bound on success, an expected retry cost, or a strict-PPT rejection-sampling implementation.

Identification and Fiat–Shamir add adversarial interaction to this same transcript model. Their security is not merely the existence of a mathematical witness extractor: the computational instances require an encoded efficient extractor, and finite quantitative transformations explicitly track replay and calls.

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

## Shared random oracles and ideal permutations

[Complexity/Crypto/Protocols/Signature/RandomOracle.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Signature/RandomOracle.lean) defines a typed random-oracle signature experiment. Signer, verifier and forger share one lazy hash cache. The forger's coins are drawn explicitly before deterministic oracle interaction, enabling replay. Signing and hash queries have separate bounds. Key generation can be an arbitrary PMF, so this finite experiment is not identical to the native `SignatureScheme` interface.

[Complexity/Crypto/Protocols/SigmaProtocol/FiatShamir.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/SigmaProtocol/FiatShamir.lean) hashes `(message, commitment)` to the challenge and proves correctness and a quantitative EUF-CMA bound using special soundness, special HVZK, commitment unpredictability and the generic forking lemma. The bound includes signing/programming collisions, challenge guessing and the square-root forking term. It is a finite exact-security reduction; an asymptotic machine claim additionally needs the encoded efficiency bridges. The module cites Bellare–Neven and Boneh–Shoup and labels its comparison with their constants [bs23][bs23].

The ideal-permutation model gives an adversary both forward and inverse access to one consistent random permutation. Separate cipher/primitive channels support [Complexity/Crypto/Protocols/Cipher/EvenMansour.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/EvenMansour.lean); the two-key and single-key advantages are bounded by `2*Q_cipher*Q_primitive/|G|`. [Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Protocols/Cipher/LubyRackoff.lean) proves three-round forward and four-round strong/bidirectional Feistel results and an explicit three-round chosen-ciphertext attack. These are bounded-query theorems over finite groups with exact ideal functions/permutations. Native local computation is not charged merely by `IsQueryBounded`. The uniform computational counterparts live in [Complexity/Crypto/Computational/PseudorandomPermutation.lean](../../Complexity/Crypto/Computational/PseudorandomPermutation.lean) (`BlockCipher`, `BlockCipher.PRP`, `BlockCipher.StrongPRP` against oracle-PPT word distinguishers, with explicit security parameter and the `[]` convention for malformed blocks) and [Complexity/Crypto/Computational/LubyRackoff.lean](../../Complexity/Crypto/Computational/LubyRackoff.lean): `PseudorandomFunction.prp_lubyRackoffCipher` proves that the three-round cipher built from a `PseudorandomFunction` is a PRP. Its proof reduces to `PseudorandomFunction.multiKey` with an oracle-PPT adapter, and transfers the finite-group bound to randomized adversaries by fixing their private coins (`ProbOracleComp.coinLaw`, [CoinFixing.lean](../../Complexity/Languages/Probabilistic/Oracle/CoinFixing.lean)).

## General zero knowledge: quantifier orders, primary-input clocks, and instance indexing

[GenerableZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L144) chooses one simulator for each uniform strict oracle-PPT verifier before all efficiently generable instance, witness and auxiliary-input families. Those families are deterministic polynomial-time functions of unary `n`. The stronger [AuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L174) permits arbitrary polynomially bounded instance, witness, verifier auxiliary-input (`z`) and distinguisher auxiliary-input (`z'`) families, and therefore potentially nonuniform advice; its simulator is chosen once per `Vstar` before the families and distinguisher and is certified on `(1^n, (a, z))`.

To work with arbitrary, **unbounded** auxiliary inputs `z : List Bool` whose length is not bounded by the security parameter, import `Complexity.Crypto.Computational.ZeroKnowledge.AuxClock` ([ZeroKnowledge/AuxClock.lean](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean)), which builds on [IsPPTWithAux](../../Complexity/Computability/Probabilistic/PPT/AuxClock.lean#L149) and [IsOraclePPTWithAux](../../Complexity/Computability/Probabilistic/PPT/AuxClock.lean#L160) and machine-level input-tape prefix locality ([MultiTapeMachine.runFrom_eq_of_prefix_agree](../../Complexity/Computability/Machines/Turing/MultiTape/Probabilistic/PrefixLocality.lean#L60)):

- **Family-indexed unbounded auxiliary input ([UnboundedAuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L167)):** the malicious verifier `Vstar` is clocked in the primary input `(1^n, a)` via `IsOraclePPTWithAux (encPair encUnary enc) encBits`. One witness-free simulator `S` is chosen per `Vstar` before the families and distinguisher, certified by `IsPPTWithAux (encPair encUnary enc) encBits`, and depends only on a polynomial prefix of `z`. Every distinguisher `adversary` clocked in `((1^n, a), view)` via `IsPPTWithAux` receives the **full untruncated** `z n` and has negligible advantage across all polynomially bounded valid `(a, w)` families and arbitrary, unbounded `z : ℕ → List Bool`.
- **Instance-indexed (`x`-indexed) unbounded auxiliary input ([InstanceAuxiliaryInputZeroKnowledge](../../Complexity/Crypto/Computational/ZeroKnowledge/AuxClock.lean#L379)):** `Vstar` is clocked in the primary instance `x` via `IsOraclePPTWithAux enc encBits`, and one simulator `S` certified by `IsPPTWithAux enc encBits S` is chosen per `Vstar` before the distinguisher, polynomial bounds, instance `x`, witness `w` and auxiliary input `z`. For every distinguisher `adversary` clocked in `(x, view)` via `IsPPTWithAux (encPair enc encBits) encBool` (receiving the full untruncated `z`), every witness-length bound `w.length ≤ c_w * (n + 1) ^ d_w` at `n = (enc x).length`, and every inverse-polynomial degree `k`, all sufficiently large valid instances `(x, w)` and all arbitrary `z : List Bool` have distinguishing advantage at most `1 / ((n : ℝ) + 1) ^ k`.
- **Clock and indexing bridges:** `AuxiliaryInputZeroKnowledge.unboundedAuxiliaryInputZeroKnowledge` (with its `ZeroKnowledgeProof` and `ZKProof` projections) lifts `AuxiliaryInputZeroKnowledge` to `UnboundedAuxiliaryInputZeroKnowledge` by defining `S n a z := S₀ n a (z.take (T_V n a))` and instantiating `z` with the verifier-sized prefix and `z'` with the distinguisher-sized prefix, and `UnboundedAuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge` (hence `AuxiliaryInputZeroKnowledge.instanceAuxiliaryInputZeroKnowledge`) bridges to `InstanceAuxiliaryInputZeroKnowledge`.

`ZeroKnowledgeProof` bundles native honest interaction and verification, perfect completeness, soundness at most `1/3` against arbitrary provers, and the generable ZK predicate. `ZeroKnowledgeProof.mem_IP` is an explicit bridge into the interactive-proof class. [ZKProof](../../Complexity/Crypto/Computational/ZeroKnowledge/Soundness.lean#L71) generalizes the soundness bound to a security-parameter function `soundness : ℕ → ENNReal` (with `ZeroKnowledgeProof.toZKProof` embedding constant `1/3` soundness), and [ZKProof.NegligibleSoundness](../../Complexity/Crypto/Computational/ZeroKnowledge/Soundness.lean#L206) pairs finiteness `∀ n, soundness n ≠ ⊤` with `Negligible (fun n => (soundness n).toNNReal)` (`negligibleSoundness_one_third_pow` discharges `(1/3) ^ (k n)` for `n ≤ k n`, and [IsOraclePPTOn.sequentialRepeat_count](../../Complexity/Computability/Complexity/Classes/IP/Repetition.lean#L135) certifies polynomial-count sequential verifier repetition). [OneWay.exists_zeroKnowledgeProof_of_mem_NP](../../Complexity/Crypto/Computational/ZeroKnowledge.lean#L575) establishes the single-round `1/3`-soundness `ZeroKnowledgeProof` notion for NP from a uniform OWF with 3SAT assignments of the Karp-reduced formula as witnesses, while [OneWay.exists_zeroKnowledgeProof_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Levin.lean#L199) and [PseudorandomGenerator.exists_auxiliaryInputZeroKnowledge_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Levin.lean#L184) compose a Levin reduction ([CookLevin.ThreeSAT_levinHard](../../Complexity/Computability/Complexity/CookLevin/Levin.lean#L234)) so that `zk.isWitness a w = true ↔ R.IsWitness a w` holds for the NP relation's own witnesses. Sequential repetition across `k(n) = n + 1` independent masked rounds in [GMW/Sequential.lean](../../Complexity/Crypto/Computational/GMW/Sequential.lean), its multi-round rewinding simulator in [GMW/Sequential/Simulator.lean](../../Complexity/Crypto/Computational/GMW/Sequential/Simulator.lean), and the Karp/Levin composition in [ZeroKnowledge/Amplification.lean](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean) amplify soundness to `(1/3) ^ (n + 1)` against arbitrary stateful provers, giving [OneWay.exists_zkProof_of_mem_NP](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean#L349) and [OneWay.exists_zkProof_of_npRelation](../../Complexity/Crypto/Computational/ZeroKnowledge/Amplification.lean#L361) from a uniform OWF.

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

## Upstream perfect secrecy and sharing

Pinned cslib supplies [PerfectlySecret](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/PerfectSecrecy/Defs.lean#L76): observing any positive-probability ciphertext leaves every message prior unchanged. Its equivalent ciphertext-distribution formulation and one-time-pad instance are finite semantic security, with no PPT restriction. The upstream commitment interface separately defines perfect/statistical hiding and perfect binding [cslib][cslib].

[Scheme](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Protocols/SecretSharing/Scheme.lean#L52) bundles deterministic reconstruction for authorized coalitions, a randomness PMF, monotone authorization and equal unauthorized-coalition view laws across all secrets. Shamir's `schemeWith` permits a tail sampler with the translation symmetry needed for privacy; `uniformTailSampler` gives the usual finite-field instance. These are reusable information-theoretic interfaces; the survey does not infer a polynomial-time protocol or a secret-sharing-to-native-MPC compiler from them.

No differential-privacy model was identified by the recorded local/upstream search. Perfect secrecy, zero knowledge and semi-honest MPC privacy do not substitute for differential privacy's adjacent-dataset comparison.

## Known Limitations

Only selected protocol endpoints and key definitions were traced. The source files themselves give detailed source mappings; this pass did not independently reconcile every textbook constant, lattice-abort construction or signature reduction. Existing regression tests are not newly executed evidence. The precise coalition and advice restrictions above should be retained even when summarizing the results compactly.

[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[goldreich04]: ../sources.md#goldreich04

## One-shot tetrahedral random oblivious transfer

Import [Tetrahedral.lean](../../Complexity/Crypto/Multiparty/Tetrahedral.lean) for
Beaver's STOC submission 1234, Theorem 4.1 (PDF p. 3). `shuffle` enumerates
all 24 permutations exactly once; `aliceTable` and `bobTable` are Figures 2–3.
Alice's ordered two-card hand and Bob's third card come from one uniform shuffle.
`correctness` proves that the selected bit is received, and `uniform_output`
gives each sender-bits/selection triple exactly three preimages, hence probability
$1/8$. `alice_privacy` and `bob_privacy` condition on complete views, including the
local hand, public announcement and outputs. Their count identities make the
selection or unselected bit exactly fair within every view fiber; zero-probability
views have zero counts on both sides.

The [checked client](../../ComplexityTests/PaperEndpointsBatchB.lean) reproduces
Figure 4 and a pair of Bob-indistinguishable shuffles with opposite hidden bits.
It also checks an obstruction to Section 5's reverse privacy assertion: given
Bob's card 0, the event that Alice has ordered hand (1,3) has probability $1/6$;
message X has probability $1/3$; their joint probability is $1/6$, not $1/18$.
Thus the reverse public announcement leaks hand information beyond the dealt
card. `reverse_message_leakage` in
[TetrahedralYield.lean](../../Complexity/Crypto/Multiparty/TetrahedralYield.lean)
exports that obstruction as a named theorem.

For chosen-input OT, import
[TetrahedralChosen.lean](../../Complexity/Crypto/Multiparty/TetrahedralChosen.lean).
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

Import [AddXNOR.lean](../../Complexity/Cryptanalysis/AddXNOR.lean) for Wang,
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
The [client](../../ComplexityTests/PaperEndpointsBatchB.lean) checks full-width
operations and two-operand and longer-chain theorem applications.
These are uniform-ensemble signed expectations; they do not establish an absolute
correlation bound, a planted-instance statistic, NP-hardness or a search bound.

Import [AddXNORRuns.lean](../../Complexity/Cryptanalysis/AddXNORRuns.lean) for
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

Import [AddXNORChain.lean](../../Complexity/Cryptanalysis/AddXNORChain.lean) for
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

Import [AddXNORStripping.lean](../../Complexity/Cryptanalysis/AddXNORStripping.lean)
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

Import [AddXNORSwap.lean](../../Complexity/Cryptanalysis/AddXNORSwap.lean) for
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
The complete [client](../../ComplexityTests/AddXNOR.lean) checks these counts,
a noncollision, arbitrary context, backward projection, actual carries, both
stripping parity branches and an impossible low field.

Import [AddXNORDecay.lean](../../Complexity/Cryptanalysis/AddXNORDecay.lean)
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
[AddXNORTransfer.lean](../../Complexity/Cryptanalysis/AddXNORTransfer.lean)
derives the signed matrix entry $(-1)^{[s'<s]}$ from actual addition and proves
its full-word distribution bridge. [AddXNORSpectrum.lean](../../Complexity/Cryptanalysis/AddXNORSpectrum.lean)
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
$-1/4$. The complete [spectrum client](../../ComplexityTests/AddXNORSpectrum.lean)
checks that distinction on actual words, high-bit independence, separated
higher-bit runs, matrix orientation, zero runs, zero width and quantified bounds.
The full-word spectrum requires $j<m$; its decay inequality includes $j=0$,
where $\rho_0=1$, while the uniform half-bit bound requires $j\ge1$.

## Add/XNOR hardness with an explicit encoding

Import [AddXNORNPComplete.lean](../../Complexity/Cryptanalysis/AddXNORNPComplete.lean)
for Theorem 1 (PDF pp. 9–11), and
[AddXNORWidth.lean](../../Complexity/Cryptanalysis/AddXNORWidth.lean) for
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

The complete [hardness client](../../ComplexityTests/AddXNORHardness.lean)
checks actual operands and both gadget choices, mixed-pattern rejection,
zero/repeated entries, empty input, out-of-range rejection, width one,
a non-dense 3-SAT variable label and rational-width padding. Start with the two
imports above; use the semantic equivalence to inspect a constructed instance,
and the separate polynomial-time theorem for a complexity-class reduction.

Import [AddXNORSearch.lean](../../Complexity/Cryptanalysis/AddXNORSearch.lean)
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
is assigned as an annotation. The complete [search client](../../ComplexityTests/AddXNORSearch.lean)
checks successful and unsuccessful inputs, empty cuts, width zero and duplicate states.

Import [AddXNORReachability.lean](../../Complexity/Cryptanalysis/AddXNORReachability.lean)
for the actual reachable-state decision program. Supply width-$m$ words as lists
of $m$ bits, low bit first, to `WordTable.decide`. `decide_correct` identifies
its answer with unrestricted `Solvable`; the complete
[resource client](../../ComplexityTests/AddXNORResources.lean) shows the imports,
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
[AddXNORNativeResources.lean](../../Complexity/Cryptanalysis/AddXNORNativeResources.lean)
and use `Native.encoded_answers` or `Native.encoded_time_space` in the
`Cslib.Cryptanalysis.AddXNOR` namespace. The complete
[native client](../../ComplexityTests/AddXNORNative.lean) starts from ordinary
`Data.init` input and proves actual flat-program halting, unrestricted
solvability and a bound on the full memory-access transcript. From the repository
root with the pinned Lean toolchain installed, first build its dependencies, then
check the client:

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeResources
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNative.lean
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

Import [AddXNORClasses.lean](../../Complexity/Cryptanalysis/AddXNORClasses.lean)
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

Import [AddXNORNativeCounters.lean](../../Complexity/Cryptanalysis/AddXNORNativeCounters.lean)
for native **forward** counter preprocessing. In namespace
`Cslib.Cryptanalysis.AddXNOR.Native.Counters`, `encoded_resources as s t`
starts with `Native.encodeInput (List.ofFn as) s t`, executes initialization and
every counting layer, and halts with the final array pointer in `Native.source`.
For every state $g$, the certified final memory cell contains `solutionCount as s g`.
Coincident predecessors are added twice. The target header word is read but does
not affect this all-states preprocessing. From the repository root after setup:

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeCounters
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNativeCounters.lean
```

The complete [counter client](../../ComplexityTests/AddXNORNativeCounters.lean)
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

Import [AddXNORNativeProjection.lean](../../Complexity/Cryptanalysis/AddXNORNativeProjection.lean)
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
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeProjection
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNativeProjection.lean
```

The complete [projection client](../../ComplexityTests/AddXNORNativeProjection.lean)
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
[AddXNORNativeBuckets.lean](../../Complexity/Cryptanalysis/AddXNORNativeBuckets.lean),
[AddXNORNativeQuery.lean](../../Complexity/Cryptanalysis/AddXNORNativeQuery.lean) and
[AddXNORNativeEmit.lean](../../Complexity/Cryptanalysis/AddXNORNativeEmit.lean).
Import the last module to use all three in namespace
`Cslib.Cryptanalysis.AddXNOR.Native.Quarter`. From the repository root after
[normal setup](../workflows/getting-started.md), check the complete
[native quarter client](../../ComplexityTests/AddXNORNativeEnumeration.lean):

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeEmit
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNativeEnumeration.lean
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
[AddXNORNativeDictionary.lean](../../Complexity/Cryptanalysis/AddXNORNativeDictionary.lean)
and [AddXNORNativeRetain.lean](../../Complexity/Cryptanalysis/AddXNORNativeRetain.lean).
From the repository root after normal setup, run:

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeRetain
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNativeDictionary.lean
```

The [complete dictionary client](../../ComplexityTests/AddXNORNativeDictionary.lean)
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
Counter-selected orientation and an unrolled all-class decision run are now
composed by `Driver.dissection_exec`, described below. In particular,
the unrolled all-class composition below releases each class, but no theorem yet
derives the global peak bound from the computed $\mu_p$. The native components do not
complete Lemma 8 or Theorem 7. A compact sorted-list/arena realization or a
justified sparse-memory simulation is still needed for the source bit model.

Import [AddXNORNativeBalance.lean](../../Complexity/Cryptanalysis/AddXNORNativeBalance.lean)
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
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeBalance
lake env lean -DwarningAsError=true ComplexityTests/AddXNORNativeBalance.lean
```

The complete [balance client](../../ComplexityTests/AddXNORNativeBalance.lean)
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
[ReadOnly.lean](../../Complexity/Computability/WordRAM/ReadOnly.lean) proves
memory preservation for every flat-program prefix.

If applying the certificate fails, check the complemented backward addresses,
the two buffer pointers, $2^p$ in the modulus register and the word-fit premise.
This interface starts after counter construction. A single original-input
execution joining both counters, native quarter streaming, dictionary allocation,
lookup, reuse/freeing and witness output remains required for Theorem 7.

Import [AddXNORDissection.lean](../../Complexity/Cryptanalysis/AddXNORDissection.lean)
for the actual quarter-indexed streaming class search of Lemma 8 and Theorem 7.
In `Cslib.Cryptanalysis.AddXNOR.Dissection`, call `solve p as s t` on the
noninitial operands, initial word and target. It uses three consecutive quarters
of length $k=\lfloor q/4\rfloor$ and a final quarter containing the remainder.
It caps the projection width at $m$. `solve_correct` proves unrestricted decision
correctness; `solve_sound` proves that a returned operator list has length $q$
and evaluates to the target. From the repository root after the normal setup:

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORDissection
lake env lean -DwarningAsError=true ComplexityTests/AddXNORDissection.lean
```

The complete [streaming client](../../ComplexityTests/AddXNORDissection.lean)
checks exact emission order in both directions, wraparound, misses, colliding
witnesses, both dictionary orientations, every quarter-length remainder, empty
and zero-width instances, and all one-bit four-operand inputs and endpoints.
A failed concrete equality usually indicates reversed inverse-quarter order or
a lost collision witness; compare `classRecords` and `backClassRecords` before
changing the full-state join.

[ClassEnumeration](../../Complexity/Cryptanalysis/AddXNORClassEnumeration.lean)
indexes the first quarter's full states by low-bit keys. Each second-quarter
word computes its projected inverse from the requested class, visits one bucket
and recovers a full output state only on hits. The backward version indexes the
last quarter and exchanges forward/inverse directions. The reusable
[collision buckets](../../Complexity/DataStructure/BinaryTrie/Buckets.lean)
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
balance with selected-class construction and an unrolled all-class search, under
explicit address-fit hypotheses. This is separate from the functional trie
implementation here. Word-bit simulation, global allocation and compiled
peak storage remain unproved. Thus this streaming implementation is functionally certified,
while the paper's full runtime/space endpoint remains open. The existing
per-class means still give no bound on expected maximum balance.

Import [AddXNORCounting.lean](../../Complexity/Cryptanalysis/AddXNORCounting.lean)
for Propositions 1–2. `steps` uses all `Fin q → Bool` operator strings on the
actual operands. `uniform_mean_solutionCount` gives $2^q/2^m$ under independent
uniform full-width inputs, and `uniform_solution_probability_le` bounds the
probability of any solution by that mean. The balanced mean is exactly $1/2$.
`plantedLastMass_size_bias` derives the manuscript's exact size-bias identity
from its actual final-operand planting: sample the operator string and every
preceding operand independently, then use `plantedLast` to complete the target.
A second identity covers initial-word planting by inverse evaluation. Neither
identity asserts independent solution events or a Poisson law.

Import [AddXNORParity.lean](../../Complexity/Cryptanalysis/AddXNORParity.lean)
for the exact $2^{q-1}$ size of the required parity class and the even Hamming
distance of every solution pair. Positive width is required; the count bound
also requires $q>0$. These theorems reuse the existing Boolean parity and
Hamming-weight APIs. Import [AddXNORDifference.lean](../../Complexity/Cryptanalysis/AddXNORDifference.lean)
for all three parts of Lemma 7 and the actual complemented-carry formula for
an operator flip. `addition_difference_probability` uses two independent
uniform words and a fixed difference; its exponent counts precisely the active
bits below the MSB. `msb_addition_difference` holds deterministically.
The complete [counting/difference client](../../ComplexityTests/AddXNORCounting.lean)
checks mean/planting contracts, degenerate-width exclusions, parity bounds and
mixed low/MSB differences. It also shows why Proposition 3's parenthetical
$2^{-w}$ must count non-MSB activity: an MSB-only difference has weight one
but preservation probability one. Import [AddXNORFlipWeight.lean](../../Complexity/Cryptanalysis/AddXNORFlipWeight.lean)
for `expected_operator_flip_weight`, which proves the proposition's exact
$(m+2)/2-2^{-m}$ mean by deriving the two carry-in recurrences from actual
addition. The independent uniform words are the running state and current
operand. The result is the weight immediately after the flip; a common suffix
preserves nonvanishing but need not preserve weight. Width zero is included.
This proof does not use the erroneous total-weight parenthetical.

The [search client](../../ComplexityTests/AddXNORSearch.lean) also gives a checked
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
[AddXNORNativeProbe.lean](../../Complexity/Cryptanalysis/AddXNORNativeProbe.lean).
From the repository root after normal setup, check it and its complete client:

```bash
scripts/build.sh --wfail --iofail Complexity.Cryptanalysis.AddXNORNativeProbe
lake env lean ComplexityTests/AddXNORNativeProbe.lean
```

`Quarter.probeBody_exec` loads one actual node, evaluates a full backward quarter
using physically reversed operands, and probes the retained full-state slot. For
$b$ operands it takes at most $18b+33$ standard WordRAM instructions, preserves
all memory, and returns both the nonzero presence tag and second retained witness.
The first retained witness is the tag minus one. Zero witnesses remain present;
a zero tag denotes absence. The node's witness and original backward-quarter
index remain in `firstOperators` and `operators`. The
[complete client](../../ComplexityTests/AddXNORNativeProbe.lean) supplies every
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
`Complexity.Cryptanalysis.AddXNORNativeBackward` and use
`Quarter.Backward.prepare_linked_exec`. Supply the target in `initial`, the
full-width modulus in `modulus`, and the reversed fourth-quarter operand array
at `base`, with `count` equal to its length. `heads` addresses $2^p$ writable
head cells; `frontier` starts a positive, disjoint three-cell-per-index record
region. Operands must avoid both writable regions. The theorem derives the
linked records of actual inverse states, preserving original packed indices
and outside memory, after native zero-fill and enumeration. It includes physical
address/index fit premises. The complete
[backward preparation client](../../ComplexityTests/AddXNORNativeBackward.lean)
checks non-self-inverse addition, collisions, dirty memory, and an empty
zero-width quarter. From the repository root, check it with
`lake env lean ComplexityTests/AddXNORNativeBackward.lean` after building its
import. This API supplies backward bucket semantics. The `searchClass_exec` endpoint
below connects both prepared sides through actual forward dictionary retention
and a complete native projected-query stream, deriving original-chain soundness.

For the retained **forward** side, import
`Complexity.Cryptanalysis.AddXNORNativeForwardRetain` and apply
`Quarter.Forward.prepareRetain_exec`. Starting at the repository root with warm
build outputs, build that module and run
`lake env lean ComplexityTests/AddXNORNativeForwardRetain.lean`.
The [complete client](../../ComplexityTests/AddXNORNativeForwardRetain.lean)
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
`Complexity.Cryptanalysis.AddXNORNativeDualPreparation` and apply
`Quarter.dualPrepare_exec`. Put the inverse heads and records after the forward
records and below the dictionary. Supply reversed fourth-quarter operands outside
both arenas and below the dictionary, plus the combined physical fit bound.
Seven native instructions transfer the inverse-stage registers. The theorem derives
both linked bucket families, the exact retained forward dictionary equation, zero
base tags, outside-memory preservation and a register frame. `dictionaryBase` is
proof bookkeeping for the memory below the table after construction; it is not a
RAM operation or a supplied dictionary. The
[complete preparation client](../../ComplexityTests/AddXNORNativeDualPreparation.lean)
checks forward and inverse construction, retained witness tags and a dirty sentinel.

For an actual original-chain witness scan, import
`Complexity.Cryptanalysis.AddXNORNativeDualProbe` and use `Quarter.dualProbe_exec`.
Supply reversed full-width third-quarter operands below the dictionary and outside
both arenas. Ten more native instructions transfer registers and load the selected
inverse bucket head; the scan then inverts the third quarter and probes the full
retained states. Any reported witness is proved to solve the original chain.
The [complete probe client](../../ComplexityTests/AddXNORNativeDualProbe.lean)
supplies all raw premises, and kernel runs check a hit with zero packed witnesses
and a miss. From the repository root, build the two modules, then run
`lake env lean ComplexityTests/AddXNORNativeDualPreparation.lean` and
`lake env lean ComplexityTests/AddXNORNativeDualProbe.lean`.
Increase word width or separate the arenas/arrays when fit or separation fails;
initial dictionary cells must really be zero. Bounds count every construction,
transfer, load and scan instruction in this sparse WordRAM model.

To derive those bucket choices from original operands, import
`Complexity.Cryptanalysis.AddXNORNativeProjectedProbe` and use
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
`lake build Complexity.Cryptanalysis.AddXNORNativeProjectedProbe`, then
`lake env lean ComplexityTests/AddXNORNativeProjectedProbe.lean`.
The [complete client](../../ComplexityTests/AddXNORNativeProjectedProbe.lean)
supplies all raw premises with non-self-inverse addition and colliding low keys,
checks native multiword projection/query order and counter indices, and executes
whole-program zero-width-hit and empty-class-miss cases. Dirty scratch cells are
allowed and overwritten; unread input is framed. If layout/fit fails, separate the
arrays/arenas or increase word width rather than installing query results as an
oracle. `RegisterParameter` in `Complexity.Computability.WordRAM.RegisterParameters`
is also available for clients replacing selected immediate writes by copies of
an already computed, preserved register.

Those bounded APIs fix one word per middle quarter. For a complete selected-class
search, import `Complexity.Cryptanalysis.AddXNORNativeClassSearch` and use
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
`Complexity.Cryptanalysis.AddXNORNativeDissection` and use `Driver.dissection_exec`.
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
all dictionary cells zero for the next class. The outer `searchClasses` composition
visits all $2^p$ keys in order unless a valid hit exits early. `dissection_exec`
proves a nonzero tag exactly when some original class has a solution, a zero tag
exactly when none does, original-chain witness soundness, the actual computed
balance and reusable empty dictionary memory. Use `Driver.witness` to decode the
returned words according to the preserved orientation bit.

`prepareTime + allTime` charges both counter projections/constructions, balance,
all quarter setup, dictionary release, loads, comparisons and early-exit control.
`allTime_eq_sum` expresses the conservative full-interval bound as the sum of
`selectedTime` budgets plus two control instructions per class and a final write.
The outer code is currently generated by unrolling the class interval; its code
size is linear in $2^p$. A fixed-size outer while program is still needed for a
uniform-code resource endpoint. `selected_count_le_balance` bounds the multiplicity
selected by the actual comparison, but it is not a simultaneous compiled-prefix
memory bound. Global asymptotic time, peak occupied storage in terms of computed
balance, derived global word/address fit and the source sorted-list multitape bit
model remain open. This does not complete Lemma 8/Theorem 7 or 733 ALL-main.

From the repository root build
`lake build Complexity.Cryptanalysis.AddXNORNativeDissection`, then run
`lake env lean ComplexityTests/AddXNORNativeDissection.lean`.
The complete client instantiates all raw premises with unequal quarters,
non-self-inverse addition, dirty scratch and low-key collisions. It checks native
strict inverse and forward selection, tie/forward zero-width collisions, exhausted
empty-quarter misses, actual balance and dictionary release. If physical premises
fail, move counter buffers before class scratch or increase word capacity; do not
supply desired counter values or an orientation flag as an oracle.


From the repository root, run
`lake build Complexity.Cryptanalysis.AddXNORNativeClassSearch` followed by
`lake env lean ComplexityTests/AddXNORNativeClassSearch.lean`.
The [complete client](../../ComplexityTests/AddXNORNativeClassSearch.lean)
instantiates every raw premise at nontrivial widths for arbitrary targets/classes,
then checks a class hit and an exhausted class for the same original instance,
non-self-inverse additions, replacement collisions, zero-width indexed duplicates,
and whole-program empty-quarter hit/miss runs. Separate arenas or increase width
when fit/separation fails; dictionary cells must actually start at zero. The scan
and retention contracts expose their returned increment register, and the scan also
exposes its restored packed word, so outer loops reuse proved register facts.

This older API searches one class and always retains the forward side. The
`Driver.dissection_exec` endpoint above supplies actual counter-table selection
and unrolled iteration/release across classes; its global asymptotic time and
compiled peak-storage theorem remain open. A local miss from the older API is
not a global no-instance conclusion. The following backward-record consumer
cannot substitute for the forward retained dictionary.

For consecutive backward preparation and native forward retention, import
`Complexity.Cryptanalysis.AddXNORNativeBackwardRetain` and apply
`Quarter.Backward.prepareRetain_exec`. In addition to the preparation layout,
supply a separate forward operand array below the dictionary, disjoint from
heads and records, and zero dictionary memory. The program loads the selected
head and transfers registers itself. Its conclusion derives the exact dictionary
insertion stream and originating-record payloads, including collisions and zero
indices, while framing other memory and preserved registers. The complete
[composition client](../../ComplexityTests/AddXNORNativeBackwardRetain.lean)
can be checked with `lake env lean ComplexityTests/AddXNORNativeBackwardRetain.lean`
after building its import. This forward consumer of inverse records is a bounded
component; it does not implement the source's full backward-half enumeration or
the projected-query/probe/global pipeline.

The direction-exchanged head lookup is available separately from
`Complexity.Cryptanalysis.AddXNORNativeOppositeQuery` as
`Quarter.Backward.queryBucket_exec`. Starting with forward-order operands at
`base`, the class value in `state`, the projected modulus and the original packed
index, it charges forward evaluation and the two head-address/load instructions.
It preserves all memory and the packed index. `Backward.retainedMemory_linked`
shows that the computed retention memory preserves every prepared inverse bucket,
including buckets other than the consumed one. The complete
[forward-query client](../../ComplexityTests/AddXNORNativeOppositeQuery.lean)
checks addition by one (distinguishing forward and inverse lookup) and a
zero-width collision. Build the module, then run
`lake env lean ComplexityTests/AddXNORNativeOppositeQuery.lean`.
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
prefix. `probeClass_exec` in `Complexity.Cryptanalysis.AddXNORNativeClassProbe`
now proves general termination, exact complete-stream hit/miss semantics and
payload provenance, with a decreasing finite counter and a charged budget.
`searchClass_exec` above supplies its constructed buckets/dictionary and original
chain interpretation from raw input. Counter-selected orientation and global
computed-balance resources remain open. The source sorted-list bit-operation
model remains distinct.
