# Native machines and resource contracts

[Chapter index](index.md) · [Model map](../model-map.md)

## Configuration and uniformity

The underlying native configuration is cslib's [Turing.Cfg](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean#L97). Its input is a fixed list; the input head lies in `Fin (input.length + 2)`, with one blank boundary position on each side. Movement clamps at the boundaries. Each work tape is a function from integer positions to optional symbols, with an integer head. Output is a list to which a transition can append at most one symbol. Input is read-only and output is not readable. The action simultaneously chooses each work-tape write/move, input movement, optional output, and next optional control state. `none` in the control state denotes halting. [cslib][cslib]

A raw machine can have an arbitrary state or symbol type. Complexity predicates quantify one fixed number of tapes, finite state type, and binary-alphabet machine before quantifying over inputs. Encodings are explicit embeddings `α ↪ List Bool`; they do not by themselves promise a computable decoder or a decidable image. Native correctness therefore applies to all valid encoded values. A theorem over an encoded graph type does not automatically recognize malformed graph strings. [cslib-frontier][complexitylib]

The native execution model keeps data access and resource accounting separate:

```mermaid
flowchart TB
input["Read-only input<br/>bounded head position"]
work["Work tapes<br/>symbols and head positions"]
control["Finite control<br/>one native transition"]
output["Append-only output<br/>not readable"]
time["Time bound<br/>transitions until halt"]
space["Workspace bound<br/>visited work-tape cells"]
input -->|"read input symbol"| control
work -->|"read"| control
control -->|"write and move heads"| work
control -->|"emit at most one symbol"| output
control -->|"count transitions"| time
work -->|"count visited cells"| space
```

The read/write arrows describe a transition; the counting arrows describe its resource contracts. Input and output are excluded from workspace, while emitting output still takes time. The diagram uses the finite-control machine required by [ComputableInTimeAndSpace](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean#L352), with the components of [Cfg](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Configuration.lean#L97). The oracle extension below adds its own query buffers and reply heads.

The common extension [MultiTapeMachine](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Machine.lean#L148) adds a finite family of named oracle channels and a choice functor. A channel has a query buffer, a reply word and a reply-head position. An ordinary action writes at most one query symbol per channel and moves reply heads locally. A query action invokes one channel, clears that query buffer, installs the returned word and resets its reply head. Other channels and ordinary tapes retain their state, apart from the specified control continuation. Payloads are words; channel names identify operations, not payload values.

The specialization to no channels and `Id` is [step-exactly equivalent to the deterministic machine](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Machine/Equivalence.lean#L74); `Set` gives [the nondeterministic machine](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Machine/Equivalence.lean#L79). A clocked run is itself a program, through [runConfigFrom, runFrom and run](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Machine/Program.lean#L59), linking operational semantics to the free-program chapter.

## Search a bounded witness space

Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch` for
`ComputableInO.exists_bits` ([source](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/BoundedSearch.lean)).
Supply a Boolean test on `(context, word)` and independent uniform time and space bounds `T` and
`S` over words of the runtime unary width `n`. The result supplies polynomial bookkeeping `P`:
time is `O((2^n + 1) * (P + T))`, and charged space is `O(P + S)`. No polynomial-time assumption
on the test is needed. The machine streams candidates; the enumeration list appears only in its
specification. The retained context and candidate contribute to the bookkeeping, so this is not
a logarithmic-workspace transducer theorem.

For class membership, `setOf_exists_mem_PSPACE` applies this rule to a PSPACE test.
`bounded_image_mem_PSPACE` in
[Space.Image](../../CslibFrontier/Computability/Complexity/Classes/Space/Image.lean) searches source
words under a unary polynomial-time bound computed from the output. The forward function may
have collisions, and the bound is required only on accepted source words. No efficient inverse
is required. The [checked clients](../../CslibFrontierTests/BoundedSearch.lean) cover width zero,
failed search, and a constant image map whose accepted source words alone satisfy the bound.
Run `scripts/build.sh CslibFrontierTests.BoundedSearch` from a prepared checkout to check them.

## Choice changes semantics

| Native variant | Choice representation | What a branch means | Main uses |
|---|---|---|---|
| Deterministic `MultiTapeTM` | One action | One run, with halting fixed thereafter | P, DTIME, DSPACE, reductions and universal simulation |
| Nondeterministic `MultiTapeNTM` | Set of actions | Existence of an accepting path; repeated equal actions have no multiplicity | NP, NL, NSPACE, NPSPACE |
| `MultiTapePTM` | A Boolean-indexed pair of actions | One fresh fair bit per live instruction; equal successor actions still receive their full probability mass | Strict PPT, BPP/RP, randomized logspace, oracle verifiers |
| `MultiTapeCTM` | List of actions | Occurrences are distinguished by list indices, even when actions coincide | #P, GapP, exact acceptance/rejection counts |
| `MultiTapeATM` | Boolean pair plus state polarity | Existential control chooses one child; universal control requires both | ATIME, ASPACE, AP, APSPACE, AL and polynomial-length alternating games |

The definitions are [PTM](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Probabilistic.lean#L41), [CTM](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Counting.lean#L63), and [ATM](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Alternating.lean#L76). These differences cannot be recovered simply by reusing a set of successors: sets forget multiplicity, and probability and universal branching evaluate the resulting tree differently.

Nondeterministic acceptance is specifically a halted configuration whose output is exactly `[true]`, not a final state label or an output prefix. [DecidesInTime](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Nondeterministic.lean#L192) requires every computation path of at least the specified duration to end halted. A path may instead become stuck earlier; it does not accept. [RecognizesInSpace](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Nondeterministic.lean#L217) bounds every prefix on every path but permits infinite and stuck branches. [DecidesInSpace](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Nondeterministic.lean#L231) additionally supplies a finite common bound on path length for each input. These clauses prevent an accepting short branch from masking unbounded workspace on another branch.

For counting, halting branches are counted at first halt. The CTM labelled transition system does not add artificial choices after halt. `HaltsWithin` and the nonblocking condition rule out the loss of branches at stuck live states where needed for class characterizations. This is distinct from the harmless halted self-loop used to pad nondeterministic reachability paths. [Counting definitions](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Counting.lean#L222)

For alternation, [AcceptsWithin](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/Alternating.lean#L128) is a finite accepting-tree relation. A halted `[true]` configuration accepts; live existential and universal configurations use one or both successors respectively. `Accepts` existentially quantifies a finite depth. Infinite branches therefore do not obtain acceptance from coinductive interpretation. The polynomial-time class also supplies an all-branches time bound. The [parametric classes](../../CslibFrontier/Computability/Complexity/Classes/Alternation.lean) `ATIME enc t` and `ASPACE enc s` take bounds `c₁ * t n + c₂` in the length of the encoded instance, like `NTIME` and `NSPACE`; `mem_AP_iff_exists_mem_ATIME`, `mem_APSPACE_iff_exists_mem_ASPACE` and `AL_eq_ASPACE` identify the named classes with their unions or instances. The input head moves one cell per step, so `ATIME` below linear time is not the alternating logarithmic time of random-access machines. Towards `ATIME t ⊆ DSPACE t` ([#4086](https://github.com/cslib-community/cslib-frontier/issues/4086)), the [single-bit game evaluator](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/InSpace/BitGame.lean) evaluates a game of single-bit moves depth first. It is given by a leaf test, a leaf value and the player to move, each a function of the instance and the moves so far. `bitGame_value` computes the value within space `O(|x| + m + Q)`, where every play ends within `m` moves and the three tests run in space `Q`; `m` needs no certificate. The [BitGame client](../../CslibFrontierTests/BitGame.lean) evaluates a game of `n` moves, which has `2 ^ n` leaves, within space linear in `n`. Applying it to the coin game of an alternating machine is not yet done.

[Space-bounded alternation](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Alternating/Space.lean) follows the nondeterministic pattern. `MultiTapeATM.RecognizesInSpace` bounds every computation path of the table's nondeterministic machine and permits infinite branches. `MultiTapeATM.DecidesInSpace` also bounds path length for each input. The classes `ASPACE`, `APSPACE` and `AL` use this deciding form, following Sipser; Chandra, Kozen and Stockmeyer bound space without asking for halting, which is the recognizing form. The [simulation](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Alternating/Marking.lean) marks the reachable views bottom-up. Because `Accepts` is a least fixed point, `markAccepts_iff` shows that a bounded number of rounds computes it exactly, with no halting assumption. [Class inclusions](../../CslibFrontier/Computability/Complexity/Classes/Alternation/Space.lean) are proved for recognizers: `RecognizesInSpace.mem_P` and `RecognizesInSpace.mem_EXP` give `AL ⊆ P` and `APSPACE ⊆ EXP`. For a parametric bound `s`, [`reachableAccepts`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Alternating/DeterministicTime.lean) finds the views by [breadth-first search until no new view appears](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/LogSpace/ReachableViews.lean), so no bound on the number of views is computed and `s` need not be constructible. [`RecognizesInSpace.mem_DTIME` and `exists_mem_DTIME_of_mem_ASPACE`](../../CslibFrontier/Computability/Complexity/Classes/Alternation/DeterministicTime.lean) give `ASPACE s ⊆ DTIME (2 ^ O(log₂ n + s n))`, and `DTIME (2 ^ O(s n))` when `log₂ n ≤ s n`. The search loop is the plain-machine lemma [`exists_computableInTimeAndSpace_iterateWhile`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/IterateWhile.lean): polynomial-time rounds repeated until an empty value, where neither the number of rounds nor the size bound needs to be computable. Towards the converse, the [word game machine](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Alternating/WordGame.lean) keeps one position on a work tape and recomputes the next one after each move. Its space is that of one round, independent of the number of rounds, and `wordGame_spec` matches its acceptance with the least-fixed-point game semantics `WordGame.Wins`. [`mem_APSPACE_of_wins_polySpace`](../../CslibFrontier/Computability/Complexity/Classes/Alternation/SpaceGame.lean) puts every game with polynomially long positions and finite plays in `APSPACE` when its initial position and update are polynomial-space computable; the update need only be computed on reachable positions, through an encoding of typed positions. `mem_APSPACE_of_wins` is the special case of a polynomial-time update on all words. Its [checked client](../../CslibFrontierTests/AlternatingSpaceGame.lean) solves the `List.tail` game and discharges every hypothesis. The [circuit-value game](../../CslibFrontier/Computability/Circuit/Boolean/Tableau/ValueGame.lean) plays on claims about the wires of the tableau circuit used for the P-completeness of CVP: `wins_position_iff` shows that the existential player wins exactly the true claims, and `step_inSpace` computes the update within linear space in the claim through the space-bounded gate decoder. For a decider within `2 ^ p n` steps the claims have polynomial length, so `EXP_subset_APSPACE` holds, and with `APSPACE_subset_EXP` this gives `APSPACE_eq_EXP`. The converse `P ⊆ AL` is still open: it needs a word game machine whose round reads the input tape and keeps only a logarithmic claim ([#2873](https://github.com/cslib-community/cslib-frontier/issues/2873)). The [checked clients](../../CslibFrontierTests/AlternatingSpace.lean) include a universal machine with an infinite branch. It recognizes `∅` within zero space but decides nothing, and marking its views rejects.

## Independent time, workspace, and encoded output

The base predicate [ComputableInTimeAndSpace](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean#L352) keeps time and workspace independent. Workspace counts cells visited on the work tapes, including transient use; input and append-only output are excluded. The initial heads already occupy work cells. A time upper bound does not replace a separately asserted space bound.

cslib-frontier deliberately has both output-uncharged and output-charged APIs:

| Predicate | Time | Workspace | Extra output charge |
|---|---|---|---|
| `ComputableInTimeAndSpace f … t s` | Exact supplied upper bound | Exact supplied upper bound | None |
| `ComputableInBigO f … T S` | `c (T+1)` | `c (S+1)` | None |
| `ComputableInO f … T S` | `c (T+1)` | `c (S+1)` | Encoded value also at most `c (S+1)` |
| `ComputableInSpace f … S` | Some input-dependent bound | `c (S+1)` | Same output bound |
| `ComputableInPolySpace` | Some input-dependent bound | Polynomial in input length | Polynomial encoded output |
| `ComputableInDegree … d e` | Degree `d` | Degree `d` | Independent output degree `e` |
| `ComputableInLogSpace` | No externally prescribed clock | `O(log n + 1)` | None |

The definitions and the documented reason for the output charge are in [ResourceBounds.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Machines/Turing/MultiTape/ResourceBounds.lean#L88). The charge supports composition when returned values must subsequently occupy work tapes. It matters below linear space: copying an arbitrary input is a logarithmic-workspace transduction but cannot satisfy `ComputableInSpace` with a logarithmic output charge. For decision problems, one output bit makes the distinction asymptotically immaterial. The intended public direction uses plain computability; tidy cleanup and head rewinding remain in machine-level construction proofs and some transitional interfaces at this snapshot.

[Degree.BitString](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/Degree/BitString.lean) certifies linear conversion between raw words (`encBits`) and the existing framed Boolean-list encoding (`encList encBool`). Its [Cut module](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/Degree/BitString/Cut.lean) composes those streaming conversions with the existing unary list cutters. `ComputableInDegree.bitsTake` and `bitsDrop` charge the complete raw word and unary count, including empty words and counts beyond their length. Existing plain polynomial wrappers now reuse these stronger certificates. The [adaptive-game tape client](../../CslibFrontierTests/Crypto/LeveledTapePartition.lean) certifies its actual choose/encrypt/guess partition in time and output-charged workspace `O(tape.length + chooseCoins + encCoins + 1)`; callback execution and the complete reduction clock remain separate obligations.

`FTIME` is the corresponding function-time class with explicit input and output encodings and affine time `c₁ t(n) + c₂`; its workspace has an arbitrary length-dependent bound. It adds no output charge beyond the time required to write the output. [FTIME](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/FunctionTime.lean#L46) `DTIME`, `NTIME`, `BPTIME`, `DSPACE` and `NSPACE` attach affine bounds to the relevant machine predicates; `P`, `NP`, `BPP`, `L`, `NL`, `PSPACE`, `NPSPACE`, `E`, `NE`, `EXP` and `NEXP` derive familiar bound families.

## Fair-coin efficiency

[IsPPTOn](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/PPT.lean#L71) says that one fixed finite PTM, under one polynomial clock, has exactly the encoded output distribution of a program on every input. This is strict bounded time, rather than expected time or a nonuniform machine family. The initial clocked semantics can truncate at its budget, but [exists_halting_machine](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Probabilistic/PPT/Clock.lean#L77) realizes the same semantics by an actually halting machine. Closed interpretation supplies fair Boolean draws; an open PTM's coin operation has no prescribed distribution until interpreted.

Coin-tape theorems compile a strict PPT computation into a deterministic native evaluator of a polynomial-length seed, and conversely realize the usual fixed-seed verifier models. This supports the [PromiseBPP characterization](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/Promise/Probabilistic.lean#L149) and the time-bounded BPP union theorem. It does not make arbitrary Lean PMFs, exact uniform sampling from every finite cardinality, or hidden unbounded preprocessing free.

To go from a verifier class (`NP`, `BPP`, `PP`) to a fair-coin machine, start from [`isPPTOn_sampleVerify`](../../CslibFrontier/Computability/Probabilistic/Sampling/Verifier.lean). It certifies as strict PPT the program that samples a word of length `p.eval (enc a).length` and returns the verdict of a polynomial-time `V`. `IsPPTOn.exists_halting_machine` then gives the halting machine. For the nondeterministic reading, `singleton_true_mem_support_sampleVerify_iff` says the encoded verdict `[true]` is possible exactly when some word of that length is accepted. [Guess and verify](../../CslibFrontier/Computability/Complexity/Classes/NP/GuessVerify.lean) follows this route.

Randomized logarithmic space is defined directly over PTMs. Workspace is bounded on all prefixes of the nondeterministic projection, with a fresh one-way random bit at each live step. `RL` has acceptance at least one half on yes instances and zero on no instances; `BPL` uses two thirds and one third. Their definitions require all branches to terminate but initially do not prescribe a clock. Finite configuration counting derives a polynomial clock, and matrix/counting simulations yield `RL ⊆ P` and `BPL ⊆ P`. This is a particular all-branches-halting model; an expected-time randomized-space model is not silently substituted. [Randomized logspace](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/LogSpace/Randomized.lean#L15) [Polynomial-time containment](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/LogSpace/Randomized/PolyTime.lean#L246)

For paired-port linear-system reductions (Lemma 2.1 of [OpenAI][openai-logspace26]), import [`CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.PairedPorts`](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PairedPorts.lean#L491). Obtain a [`PairedTimeLayerFamily`](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PairedPorts.lean#L491) from class membership via [`exists_pairedTimeLayerFamily_of_mem_RL`](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PairedPorts.lean#L785) or [`exists_pairedTimeLayerFamily_of_mem_BPL`](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PairedPorts.lean#L770), or from one fixed all-branches-space-bounded `MultiTapePTM` at space constant `c` and polynomial clock exponent `d` via [`PairedTimeLayerFamily.ofMachine`](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/Randomized/PairedPorts.lean#L665) (`ofMachine_potential_start` equates `potential a (start a)` to clocked coin acceptance). On each input `a`, `matrix a` is strict upper triangular and substochastic on `Fin (dim a)` with `2` outgoing ports and constant `dIn` incoming ports (`ports a`), while the executable interface works on natural-number IDs (`startNat`, `acceptBool`, `outCount`, `outPortNat`, `inPortNat`) bridged to `Fin` indices by `val_start`, `reward_eq_acceptBool`, `outWeight_eq_outCount`, `outPort_map_val`, `inPort_map_val`, mutual inversion `outPortNat_eq_some_iff`, and strict topological advance `lt_of_outPortNat_eq_some` (`u < v`). Port multiplicities satisfy `outCount a u p ∈ {0, 1, 2}` with weight `(outCount a u p : ℝ) / 2`: distinct fair-coin targets carry multiplicity `1` on each outgoing port, merged coin branches and pre-horizon halted self-loops carry multiplicity `2` on port `0` with port `1` inactive, and `outCount a u p = 0 ↔ outPortNat a u p = none` (`outCount_eq_zero_iff`) covers inactive ports, terminal-clock vertices, and out-of-range vertex or port indices (`acceptBool_eq_false_of_ge`, `outPortNat_eq_none_of_ge_dim`, `outPortNat_eq_none_of_port_ge`, `inPortNat_eq_none_of_ge_dim`, `inPortNat_eq_none_of_port_ge`). Six `ComputableInLogSpace` fields (`computableInLogSpace_dim`, `computableInLogSpace_startNat`, `computableInLogSpace_acceptBool`, `computableInLogSpace_outCount`, `computableInLogSpace_outPortNat`, `computableInLogSpace_inPortNat`) certify deterministic logarithmic-space local evaluation under `enc`, `encPair`, `encOption`, and `encNat`. The complete checked client [`CslibFrontierTests/Computability/Complexity/Classes/LogSpace/PairedPorts.lean`](../../CslibFrontierTests/Computability/Complexity/Classes/LogSpace/PairedPorts.lean#L1) exercises split versus merged coin branches, pre-horizon self-loops, terminal clock exhaustion, out-of-range queries, and non-vacuous `RL`/`BPL` instantiations. Scope remains at the Lemma 2.1 reduction for fixed halting logspace PTMs (`(1 - matrix a)⁻¹ *ᵥ reward a` at `start a`, with gap `1 / 2` vs `0` for `RL` and `2 / 3` vs `1 / 3` for `BPL`); a deterministic logarithmic-space potential estimator closing `RL = L` and `BPL = L` remains separate open work ([#2541](https://github.com/cslib-community/cslib-frontier/issues/2541)).

The preprint's analytic layer lives in `CslibFrontier/Computability/LogSpaceDerandomization/`: the correction-and-copy hierarchy, starting at [`CorrectionHierarchy`](../../CslibFrontier/Computability/LogSpaceDerandomization/CorrectionHierarchy.lean), along with row compression, root metrics, stochastic atoms, estimator schedules and their hash-family channels. These are conditional milestones toward the estimator, not a proof of `BPL ⊆ L` ([#1444](https://github.com/cslib-community/cslib-frontier/issues/1444)). [Compare compressed row outputs](../workflows/finding-results.md#compare-compressed-row-outputs) gives the entry points for its comparison theorems. Self-contained mathematics the development uses, such as strictly upper triangular matrices, time layers, paired ports, root-error inequalities and switch functions, stays under `CslibFrontier/Foundations`.

The Saks–Zhou route to `BPL ⊆ L^{3/2}` ([Saks and Zhou][sakszhou99]) has its matrix iteration formalized as pure mathematics, without a machine model. Definition A.2 and Lemmas A.3–A.4 follow Appendix A.1 of [Chattopadhyay and Liao][chattopadhyayliao20]. [`SaksZhou.Snap`](../../CslibFrontier/Probability/SaksZhou/Snap.lean) defines the random-shift rounding `snap d x y = max (⌊x 2^d - y 2^(-d)⌋ 2^(-d)) 0` for a shift `y : Fin (2 ^ d)`, and its entrywise form `snapMatrix`. Snapping loses at most `2^(1-d)` per entry (`abs_snap_sub_le`) and maps substochastic matrices to `IsDyadicSubstochastic` ones. Lemma A.3 is proved by exact counting with Hermite's identity: two values within `ε` are snapped differently on a shift set of density at most `2^d ε + 2^(-d)` (`dens_snap_ne_le`), and for matrices at most `|ι| |κ|` times that (`dens_snapMatrix_ne_le`). [`SaksZhou`](../../CslibFrontier/Probability/SaksZhou.lean) defines `snapIter d pow M n z`, with `M̂₀ = M` and `M̂ᵢ₊₁ = snapMatrix d (pow M̂ᵢ) zᵢ`. Here `pow A y` is an arbitrary approximation of `A ^ n₁` with seed `y` in a finite type `Ω`, and the hypothesis is that its bad-seed set `entryFarSet ε (pow A) (A ^ n₁)` (`ε`-far in some entry) has density at most `ε`. This is required only for `M` and for dyadic substochastic matrices, as in [Hoza][hoza21]'s `a`-bit setting. Lemma A.4 is then exact: except on a set of density at most `n₂ (ε + w^2 (2^d ε + 2^(-d)))` in `Ω × (Fin n₂ → Fin (2 ^ d))`, every row of `M̂_{n₂} - M ^ (n₁ ^ n₂)` has absolute sum at most `(∑_{k<n₂} n₁^k) w 2^(1-d)` (`dens_snapIter_far_le`, stated as the density of a `rowFarSet`). The bound is at most `n₁^{n₂} w 2^(1-d)` when `n₁ ≥ 2` (`dens_snapIter_far_le_of_two_le`). Only the probability statement of Lemma A.4 is formalized: `pow` is an arbitrary function, so its space clause belongs to the space-bounded realization. The two sets are named so that their decidability instances are fixed once; a set-builder restatement at a concrete `ι = Fin w` elaborates `∃ i` with `Nat.decidableExistsFin` and would match only up to `congr!`. The deterministic step uses the power-perturbation bound `‖aᵐ - bᵐ‖ ≤ m ‖a - b‖` for norms at most one ([`PowSub`](../../CslibFrontier/Foundations/Analysis/Normed/Ring/PowSub.lean)), in row-sum form for matrices ([`PowPerturbation`](../../CslibFrontier/Foundations/LinearAlgebra/Matrix/PowPerturbation.lean)). The [tests](../../CslibFrontierTests/SaksZhou.lean) give concrete snaps, a dyadic matrix and a non-dyadic one, the `pow` hypothesis holding for the exact power and failing for the zero map, a randomized `pow` with a bad seed instantiating Lemma A.4 at failure density below `1/3`, and a `1 × 1` iteration showing that `n₁ ≥ 2` is needed for the `n w 2^(1-d)` form. Still open under [#474](https://github.com/cslib-community/cslib-frontier/issues/474): instantiating `pow` with Nisan's generator, and realizing the iteration in space `O(log^{3/2} n)`.

[Buffered probabilistic composition](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Probabilistic/Composition/Space.lean) also has an explicit all-prefix workspace bound for the existing `second.comp first mark` compiler. If the source uses at most `s₀` cells, every supported completed output has length at most `L`, and the consumer uses at most `s₁` cells on those outputs, the combined machine uses at most `(k₁+k₀+2) * (2 * max (max s₀ s₁) (L+2) + 1)` cells. The source must halt by its supplied clock; the consumer need not halt. Source scratch remains allocated, and two extra work tapes hold the intermediate word and its boundary marker. The proof bounds every head on every path prefix, independently of elapsed time. [Checked clients](../../CslibFrontierTests/ProbabilisticCompositionSpace.lean) compose the actual framed sampler with the native copying machine, rule out a zero-space certificate for the resulting two-tape machine, and also cover an endless zero-workspace consumer. This compiler theorem does not establish the complete FHE game clock or its source-relative runtime comparison ([#2722](https://github.com/cslib-community/cslib-frontier/issues/2722), [#2585](https://github.com/cslib-community/cslib-frontier/issues/2585)).

## Representative semantic tests

The source of [MachinePrograms.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/MachinePrograms.lean#L24) distinguishes two nondeterministic successors, a stuck state, and a halted self-loop; it also checks channel isolation and fair-coin semantics. [CountingMachine.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/CountingMachine.lean#L25) contains repeated equal accepting actions and checks three accepting versus one rejecting branch, first-halt padding stability, and malformed certificates. [Alternation.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/ComplexityTests/Alternation.lean#L1) uses the same two choices with existential and universal polarity and obtains different acceptance outcomes. These are inspected regression witnesses, not test executions performed during the initial source review.

## Composing polynomial resource envelopes

For a polynomial-time map on pairs, import
[`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Families`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Families.lean).
Given `hg : ComputableInPolyTime g (encPair encA encB) encC` and polynomial bounds `ha`, `hb`
on the encoded lengths of two input families, `hg.polynomiallyBounded_length_prod ha hb`
bounds the encoded output family. The families themselves need not be computable. The
[Levin](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Levin.lean) and
[amplification](../../CslibFrontier/Crypto/Computational/ZeroKnowledge/Amplification.lean)
proofs use this rule to transport witness families through the same deterministic reduction.

Import
[`ResourceBounds.Polynomial.Automation`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/ResourceBounds/Polynomial/Automation.lean)
and use `growth_poly` for `Turing.MultiTapeTM.PolyBounded size cost`. Constants, the original
size, sums, products, fixed powers, natural logarithms, square roots, `max`, truncated
subtraction and division compose. The leaves come from the local context: `PolyBounded` facts,
also inside conjunctions and definitions such as a native certificate's `IsPolynomial`;
certificates such as `ComputableInPolyTime f encIn encOut`, through the bound on their encoded
output (with `encUnary` output, on the value itself); and `Cslib.PolynomiallyBounded` functions
applied to a bounded argument. Local `let` values and arithmetic definitions are unfolded, and
`growth_poly [h]` adds a fact that is not in the context. Existing `Cslib.PolynomiallyBounded`
goals use their `fun_prop` rules.

A certificate gives a leaf only when the module proving its bound is imported. `Automation`
imports none of them, so that it stays below the machine layers. For `ComputableInPolyTime`,
import `MultiTape.Internal.PolyTimePrimitives` (also through `Complexity.PolyTime.Basic`) for the
encoded output, and `MultiTape.Internal.PolyTimeLoops` (also through `Complexity.PolyTime.Fold`)
for a unary value. The other certificates need `Complexity.PolySpace.Plain`,
`Complexity.LogSpace`, `ResourceBounds.Degree` or `GenericRAM.Native.Certificate`. When a
certificate in the context gives no leaf because its module is missing, the failure names the
module to import; the [minimal-import examples](../../CslibFrontierTests/PolynomialGrowthImports.lean)
check these messages.

Substitution keeps the intermediate measure explicit. With an outer bound
`hv : PolyBounded size' v` in the context, `growth_poly` bounds `v (g a)` by asking for the inner
size, `PolyBounded size (fun a => size' (g a))`; it never guesses `size'`.

The tactic follows the syntax of the bound without backtracking: it closes a polynomial-growth
goal or fails at once, naming the term it could not bound. Exponentials, variable exponents and
factorials need independent bounds and are rejected by the
[ordinary-import examples](../../CslibFrontierTests/PolynomialGrowth.lean). Exact instruction
allowances, encoded-output bounds and physical word fits remain separate obligations; a coarse
polynomial envelope does not certify a particular word width or a fixed degree.

When a final statement uses one constant as both coefficient and degree, import
[`ResourceBounds.Polynomial.Envelope`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/ResourceBounds/Polynomial/Envelope.lean)
and apply `PolyBounded.exists_le_succ_pow` after composing the polynomial overhead. It supplies
`u a ≤ K' * (size a + 1) ^ K'` at every input for every `K'` above some `K`, so a final constant
such as `K + K₀` can also absorb other parts of the bound; the
[truncated contraction algorithm](../../CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/TruncatedAlgorithm.lean)
widens its exponential factor's constant this way. `PolyBounded.exists_le_self_pow` gives
`u a ≤ K * size a ^ K` instead, at positive sizes only; add a constant to the chosen size when the
contract includes empty inputs. Keep any exponential time factor outside this polynomial envelope.
The [native packet resource proofs](../../CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/PacketTerms.lean)
use `exists_le_self_pow` to combine polynomial preprocessing/postprocessing while retaining their
separate exponential time and polynomial space conclusions.

Pure lookup in `frame u ++ v` uses the small
[`Encodings.Frame.Lookup`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Encodings/Frame/Lookup.lean)
module. `getElem?_frame_append` identifies each marker and data bit;
`getElem?_frame_append_length` identifies the terminator and
`getElem?_frame_append_boundary` the suffix, including out-of-bounds
lookup. Both the unary take/drop and zip-transducer machine proofs use these list laws, so
clients can reuse them without importing either machine implementation.

[chattopadhyayliao20]: ../sources.md#chattopadhyayliao20
[complexitylib]: ../sources.md#complexitylib
[cslib]: ../sources.md#cslib
[hoza21]: ../sources.md#hoza21
[openai-logspace26]: ../sources.md#openai-logspace26
[sakszhou99]: ../sources.md#sakszhou99
