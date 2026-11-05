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
## Sharing with imperfect randomness

Import `Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomnessBinary` and use
`Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.binary_field_separation` for an actual
finite-field family at every message length $b \ge 2$. The source class varies a set of field
indices; each source is uniform on its selected key set. The theorem supplies perfect
reconstruction, equality of each share's marginal law across all messages, source min-entropy
at least $b$, and extraction error at least $1/6$ for every deterministic bit extractor on some
source. The ambient key and share alphabets have cardinalities $2^{b+2}$ and $2^{b+1}$.
Use `binary_string_separation` for the same separation on literal `Fin n → Bool`
alphabets. It supplies one scheme and source family, flat supports of size between
$2^b$ and $2^{b+1}$, and the extraction obstruction for every positive output length.
The checked two-bit client uses the same scheme for correctness, privacy and failure
of arbitrary three-bit extractors. The encoding bijections are chosen noncomputably. The separate `shareWithFieldCost_spec`
and `reconstructWithFieldCost_spec` certify the actual algebraic routines with at most
three field operations for sharing and four for reconstruction. Each field arithmetic
operation costs one; tags, pairing and field-coordinate access are free. These are
field-operation bounds, with no bit-level runtime claim for arithmetic or encoding.
The existing upstream `Scheme`
fixes one generator, whereas this endpoint quantifies over a class of generator laws.

The abstract's supplementary main Theorem 1.2 is covered by the two-out-of-$n$ and
$r$-out-of-$r$ constructions, Theorems 4.1 and 5.1. The next section documents the full
`TwoOutOfN.binary_theorem4_1` bundle. For $r=n+1\ge2$ and $b\ge r$, use
`AllOutOfR.binary_separation`: it constructs coefficients and literal encodings and proves
all-key reconstruction, joint privacy of every proper coalition, exact size/entropy bounds
and sharp extraction. See the
[all-out-of-r instructions](../design-and-assurance/assurance.md#all-out-of-r-sharing-from-odd-sources)
for its model and complete client. Import `Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.ThresholdEntropy`
for `TwoOutOfN.minEntropy_key_relative` and `AllOutOfR.minEntropy_key_relative`,
which give Theorem 1.2's explicit common bound $H_\infty(P)\ge\log_2|K|-\log_2 3$
on the actual unpadded threshold key alphabets. Review and final integration evidence remain in
[issue 2524](https://github.com/cslib-community/complexitylib/issues/2524).

Import `Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoPartyTightness`
and apply `binary_padded_extraction_tight` for the matching $1/6$ upper bound at every
admitted field size. It constructs an index bit whose error is at most $1/6$ on every
original padded source and exactly $1/6$ on some source. The generic
`OddSources.no_string_extractor` proves the lower bound $1/(2|B|)$ for every positive
output length when the branch type is odd. `exists_tight_index_extractor` supplies
an attaining bit extractor for even nonempty index spaces when the branch classes
have consecutive sizes. These are actual source laws and constructed extractors;
correctness and joint privacy of an arbitrary-party scheme are separate obligations.
The [generic and tightness clients](../../ComplexityTests/Crypto/OddSourcesTests.lean)
exercise both class orientations, real branch/source counts and the original two-party
class, including the padded case.

The [checked clients](../../ComplexityTests/Crypto/ImperfectRandomness.lean) instantiate the
four-element field, show both source-size endpoints, check concrete sharing rules, and apply
the extraction obstruction. From the repository root after setup, run
`scripts/build.sh ComplexityTests.Crypto.ImperfectRandomness`; a successful build checks these
examples. The [source](../../Complexity/Crypto/Protocols/SecretSharing/ImperfectRandomness.lean)
maps the construction to Aggarwal's Theorem 1.1 and Section 3.

## Two-out-of-n sharing with the actual source class

Import `Complexity.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN`. In namespace
`Cslib.Crypto.Protocols.SecretSharing.ImperfectRandomness.TwoOutOfN`, use
`binary_theorem4_1 n b hn hb` with $n \ge 2$ and $n < 2^b$. It constructs distinct nonzero
slopes in `GaloisField 2 b`, fixed message/share bijections onto `Fin b → Bool` and
`Fin (b + 1) → Bool`, and the sharing map `bitShare`. These bijections transport actual sharing
functions. They are noncomputable choices,
so no bit-level runtime is claimed. Field operations have the convention of the preceding
section. Theorem 4.1 itself states no additional runtime bound.

Keys are `(Fin (n - 1) ⊕ Fin n) × GaloisField 2 b`: the $n-1$ central branches are distinct keys,
although their outputs agree. At a side key only its owning party receives a tagged index;
every other party gets $\alpha_j i+m$. The shared `OddSources.source (central n)` law takes
all central branches at indices in $T$ and all side branches outside $T$, then samples uniformly
from that entire set, with no additional dealer randomness. Every choice of $T$ is retained.
The key space has $(2n-1)2^b$ elements. The exact support size is $n2^b-|T|$, between
$(n-1)2^b$ and $n2^b$, and min-entropy is at least $b+\log_2(n-1)$.

`authorized_correctness` reconstructs from the complete view of every coalition with at least
two members, on every ambient key. `unauthorized_privacy` equates the joint view laws of every
coalition with fewer than two members, including the empty coalition. The `bit_` versions
preserve these claims for the encoded shares. `share_apply_inl` and `share_apply_inr` expose
Lemma 4.3's exact ordinary and tagged masses, $(n-1)/Z_T$ and $1/Z_T$ outside $T$, respectively.
Subtraction in the general-field reconstruction formulas becomes addition in characteristic two,
matching equations (5)–(6), PDF pp. 8–9 of STOC submission 886.

`extraction_parameters` proves that the actual central/side counts are $n-1$ and $n$, that both
are nonempty, and that the total is odd. `binary_index_parameters` proves even index cardinality
and slope existence at every admissible $n,b$. The constructor's `no_string_extractor`
instantiates `OddSources.no_string_extractor` on exactly these sources, for every positive
output length and every deterministic extractor, with lower bound $1/(4n-2)$.
`exists_tight_index_extractor` instantiates the common balanced-index theorem: it constructs
an actual index function attaining that error on one source and at most that error on every
source. `binary_theorem4_1` bundles these with the same sharing scheme, source family,
correctness, privacy, literal encodings and size/entropy statements, with no unproved linking
premises. `binary_construction` remains the intermediate correctness/privacy/items 1–2 result.

From the repository root after setup, run `scripts/build.sh ComplexityTests.Crypto.TwoOutOfN`.
The [checked client](../../ComplexityTests/Crypto/TwoOutOfN.lean) covers $n=2,3$ at $b=2$, rejects
the inadmissible $b=1$ edge, checks the actual tag ownership and duplicated central keys,
reconstructs an actual pair, proves singleton/empty privacy and failure of authorized privacy,
checks both extremal source supports and masses, and applies the full bundle to arbitrary
three-bit extractors at $n=3$ while obtaining tight index errors $1/10$ and $1/6$ at $n=3,2$.
The [source module](../../Complexity/Crypto/Protocols/SecretSharing/ImperfectRandomness/TwoOutOfN.lean)
gives the precise result-to-declaration mapping.

## Independent thinning of spread sources

Import `Complexity.Probability.Thinning`. In namespace `Cslib.Probability.Thinning`,
`pmf_thinning_le_bernoulli` compares the independent $t$-thinning of any $q$-spread parent PMF
with Bernoulli density $p$ on every increasing event, under
$tq(1-p) \le p(1-t)$, $0 \le t < 1$, $0 < p < 1$ and $0 \le q$.
Parent coordinates may be correlated; the retention mask is independent of the parent.
`IsSpread` bounds the probability of containing each fixed subset.
`thinning_le_bernoulli_explicit_density` gives density $tq/(1-t+tq)$ for $0<t<1$ and $q>0$;
`thinning_le_bernoulli_of_alpha` gives the universal thinning corollary when
$\alpha^2 \le 1-\alpha$.

For the actual containing coupling, apply `exists_thinning_coupling` to the parent PMF and
its spread proof under the same parameter hypotheses. It returns a joint PMF `γ` with
`γ.map Prod.fst = thin μ t ht ht'.le`,
`γ.map Prod.snd = bernoulliSet p hp.le hp'.le`, and
`∀ z ∈ γ.support, z.1 ⊆ z.2`. Thus containment holds almost surely, and both marginals
are actual laws. `thin` draws the parent and a fresh independent retention mask;
`Cslib.BitString.bernoulliPMF` gives the mask its normalized product weights.
The coupled output sets need not be independent. These are semantic probability laws with
no sampler runtime bound.

`exists_thinning_coupling_explicit_density` returns this coupling at $tq/(1-t+tq)$, together
with proofs that the density lies in $[0,1]$. `exists_thinning_coupling_of_alpha` gives the
containing-coupling form of the corollary, including the universal choice $α=1/2$.
These cover STOC submission 1278, Definition 1.1, Theorem 1.2 (including (1.4)) and
Corollary 1.3 on PDF page 2. Every finite ground type is allowed, including the empty type.
The parameter extensions $t=0$ and $q=0$ are also supported by the general endpoint.
The signed kernel used to prove event comparison can have negative entries; it is an
algebraic device rather than a conditional probability.

For other finite ordered state spaces, import `Complexity.Probability.PMF.MonotoneCoupling`
and use `Cslib.Probability.PMF.exists_monotone_coupling`. Supply upper-event comparison for
the two PMFs; the theorem produces an ordered joint law on any finite preorder.
`upperSet_le_of_monotone_coupling` recovers event comparison from a joint law. The proof
uses finite level sets and compact convex separation, so it requires no assumed Strassen
or transport theorem.

The [checked thinning clients](../../ComplexityTests/Thinning.lean) use a correlated, nonempty
singleton parent at the exact boundary $t=q=1/2$, $p=1/3$, recover the same density from the
explicit formula, exclude a noncontained pair from the joint support, and exercise the
corollary and empty ground type. The [generic coupling clients](../../ComplexityTests/ProbabilityMonotoneCoupling.lean)
also rule out reversed deterministic marginals. From the repository root, run
`scripts/build.sh ComplexityTests.Thinning ComplexityTests.ProbabilityMonotoneCoupling` to check them.

[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[goldreich04]: ../sources.md#goldreich04
