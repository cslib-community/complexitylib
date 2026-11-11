# Prove deterministic resource bounds

Use plain `Turing.MultiTapeTM.ComputableInPolyTime` for public polynomial-time claims. Its definition supplies a finite native machine with independently polynomially bounded time and workspace, measured against encoded input length. Each Lean block is a **contextual excerpt** from the current source, requiring its linked original file; these are not newly compiled standalone examples. The excerpts are by Samuel Schlesinger, under the source repository's Apache 2.0 license. [cslib-frontier][complexitylib]

## Compose a certified function

<!-- worked-example -->

**Worked example: Swap the arguments of a certified routine**

**Goal:** `ComputableInPolyTime f encIn encOut`. Start with `CslibFrontier.Tactic.PolyTime`, the modules supplying your operations, and `open Turing.MultiTapeTM`. [PolyTimePlainDriver](../../CslibFrontierTests/PolyTimePlainDriver.lean) also imports `CslibFrontier.Computability.WordRAM.Native` for its arithmetic examples.

The input obligation in this excerpt is a polynomial-time certificate for `routine` with *binary* pair inputs and binary output:

<!-- excerpt: deterministic-compose -->
```lean
example (routine : ℕ × ℕ → ℕ)
    (hroutine : ComputableInPolyTime routine (encPair encNat encNat) encNat) :
    ComputableInPolyTime (fun p : ℕ × ℕ => routine (p.2, p.1))
      (encPair encNat encNat) encNat := by polytime
```

Prove certificates for opaque subroutines, then let `fun_prop` compose registered rules or use `polytime` for the richer certificate search. For an explicit `ComputableInDegree … 1 1` contract, import `CslibFrontier.Tactic.Degree` and use `degree`; the [degree workflow](../design-and-assurance/automation.md#preserve-explicit-polynomial-degrees) gives the complete checked client and its limits.

**Result:** argument swapping followed by `routine` is polynomial-time computable under the stated binary encodings. This does not establish any additional functional specification of `routine`.

**When it fails:** expose a local definition or supply its named certificate, then inspect the remaining contract. Do not replace the goal with a tidy interface.

<!-- /worked-example -->

The [automation reference](../design-and-assurance/automation.md) explains registration and [troubleshooting](troubleshooting.md) handles failures.

For binary sign-magnitude integers, import
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary`.
The plain `ComputableInPolyTime.intBin_*` rules (sign and magnitude, ring operations,
comparisons, list sums and products, unary powers) compose through `fun_prop`; `intBin_pow'` accepts computed
base and unary exponent certificates. The complete
[IntBinary client](../../CslibFrontierTests/RationalHitting/IntBinary.lean) checks composed ring operations, products, powers,
magnitudes and signs. A binary exponent has a different output-size obligation: do not replace
the unary exponent encoding merely to make a goal match.

For a padded integer dot product, import
[PolyTime/Int/DotProduct.lean](../../CslibFrontier/Computability/PolyTime/Int/DotProduct.lean)
and use `ComputableInPolyTime.listDotProduct`. It certifies the existing pure public
`Mathlib.Tactic.Matrix.ListMatrix.dotProduct`: the cutoff is unary, coefficients are signed
binary, missing entries are zero, and entries beyond the cutoff are ignored. Runtime still
charges both complete framed input lists. The operation lives in a Mathlib tactic-support
file but is ordinary term-level arithmetic, not a meta program.
The pure [list identities](../../CslibFrontier/Foundations/Data/List/DotProduct.lean) and
[residue-matrix bridge](../../CslibFrontier/Foundations/Data/ZMod/DotProduct.lean) require neither
crypto nor native imports. The former local Lyubashevsky `listDot` duplicate has been removed;
its verifier, extractor and signer use the same upstream operation. The
[checked clients](../../CslibFrontierTests/ListDotProduct.lean) cover padding, truncation, signed
large coefficients and unchanged verifier outcomes and commitment bytes. This API
consolidation adds no cryptographic security claim.

Keep a record's encoded tuple layout at its construction boundary. For example,
[`NativePacket.PacketCtx.mk_polyTime`](../../CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/PacketTerms.lean)
composes certificates for named fields while preserving the existing encoded words; its
[packet-construction client](../../CslibFrontier/Computability/Circuit/Frontier/TensorNetwork/NativeChildPolyTime.lean)
does not reconstruct the product tree. The
[`BranchEvalInput` interface](../../CslibFrontier/Computability/PolyTime/BooleanAnalysis/SparsePolyCounter.lean)
similarly supplies named parameter access and certificates with the original unary/binary
choices. Use these boundaries when changing a client, and retain its encoded-length bounds.

For a computed optional value, import
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option`.
The shared `ComputableInPolyTime.optionMapWithInput` rule certifies
`fun x => (value x).map (f x)` from certificates for `value` and the joint callback
`fun p => f p.1 p.2`. The callback is charged against both the original input and
the present value; input and output value encodings may differ.
The [public-import client](../../CslibFrontierTests/Machines/Turing/MultiTape/Internal/PolyTimeOptionPublicImport.lean)
checks a captured parameter and an encoding change.
[Boolean measurement search](../../CslibFrontier/Computability/PolyTime/LinearAlgebra/BooleanMeasurements.lean)
uses this rule for its optional-result codec, and
[hybrid CCA composition](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
uses it to postprocess successful decapsulation while preserving rejection.

## Walk two lists with a collecting fold

Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold`
and open `Turing.MultiTapeTM`. Apply `ComputableInO.zipFold` or
`ComputableInSpace.zipFold` explicitly. The complete [zipFold clients](../../CslibFrontierTests/ZipFold.lean)
show padding, dropping and a time certificate; [subtractSums_inSpace](../../CslibFrontier/Computability/TreeEval/Reader/Cert/Regs.lean)
uses the space-only rule for register subtraction.

`zipFold f p left right` takes one step for every element of `left`, consuming one
position of `right` even when `f` returns `none` and drops that output. After `right`
is exhausted, the callback receives `none`; it chooses whether to pad or drop.
Unused elements of a longer `right` are ignored, and retained outputs keep their order.

Supply one joint certificate for `(p, a, b?) ↦ f p a b?`, with the parameter, left element
and optional right element encoded together. Both cost rules require `Inhabited` for the
right-element and output types. They also require a bound on **every encoded output prefix**:
the result of `zipFold f p (left.take i) right` for every `i`, not only the final list.
Keep the parameter and element encodings explicit when applying the rule.

Let `N` be the length of the joint encoding of `(p, left, right)`. A callback with linear
time and charged space, and prefixes bounded by `k * (N + 1)` for one constant `k`, gives
time `O((left.length + 1) * (N + 1))` and linear charged space. The space-only rule needs
a linear-space callback and a prefix bound `B (p, left, right)`; it gives space
`O(N + B (p, left, right) + 1)` and makes no time claim. Both space bounds include the
encoded output. A callback certificate for each fixed parameter is insufficient: certify
the joint function, and discharge the prefix bound separately.

## Certify a loop and its postcondition

**Goal:** a plain computation certificate together with a final invariant. Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration`. The public import exposes [ComputableInPolyTime.iterate_spec](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Internal/PolyTimeLoops.lean); its current implementation lives in the machine layer.

Supply three computation certificates: the iteration count in unary, the initial state, and the step. Then provide an invariant indexed by original input, iteration number and state. Prove initialization and preservation. Finally, bound the encoded state under that invariant at **every** index up to the count by a `PolyBounded` function of original input length. The mathematical bound itself need not be computable.

The result has two projections: polynomial-time computability of the iterated function, and the invariant at termination. [Ladner’s shrink-loop client](../../CslibFrontier/Computability/Complexity/Classes/Ladner.lean) obtains `hreduce` and `hinv` this way: its invariant preserves satisfiability and bounds the current formula's encoded length. That use is inside the theorem's stated reduction and growth hypotheses, not an unconditional SAT algorithm.

For a step capturing a parameter, use `iterateWith_spec` and certify the joint `(parameter, state)` operation. `iterateWith_of_bounded_growth` handles additive encoded-state growth bounded polynomially in the original input. A separate efficient procedure for each fixed parameter does not provide the required uniform joint certificate. A polynomial number of efficient steps also does not bound a state that doubles each time. The [plain loop regression client](../../CslibFrontierTests/Machines/Turing/MultiTape/Internal/PolyTimeLoops.lean) exercises both positive contracts and a failed constant-state bound. When the size obligation fails, inspect the representation and growth argument before changing tactics.

For a space bound on a loop whose number of rounds is not computable, or would cost too much to compute, import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.IterateUntil` and apply [ComputableInSpace.iterateUntil](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/InSpace/IterateUntil.lean). Supply space certificates for the initial state, the step and a Boolean `done` test, and give the number of rounds `n x` as a function with no certificate. Show that `done` holds after `n x` rounds and fails before. Then bound the space of the step and the test, and the encoded state, at every round up to `n x`. The loop stops when the test first holds, and its space is that of the start, the rounds and the states, with no counter. `ComputableInSpace.iterate` instead charges a binary counter, and it needs a certificate for the count. The [BitGame client](../../CslibFrontierTests/BitGame.lean) counts down from `n` in `n` rounds within `O(|encNat n|)` space.

## Derandomize an averaging argument

**Goal:** turn an averaging proof that some choice of bits is good into a deterministic
algorithm with the same quantitative guarantee, then certify its running time. Import
`CslibFrontier.Foundations.Combinatorics.PessimisticEstimator` and open
`Cslib.PessimisticEstimator`. Describe one round by a branch function
`branch : R → Bool → S → S` and an estimate `Φ : S → M` of the final cost, for `M` such as `ℕ`
or `ℝ`; `greedy branch Φ rounds s` takes, in each round, the branch with the smaller estimate,
with ties going to `true`.

Apply `greedy_spec` with an invariant `Inv : List R → S → Prop` indexed by the rounds still to
come. Prove that it passes along both branches and that, wherever it holds, the smaller branch
estimate is at most the current estimate. For an averaging argument, use
`greedy_spec_of_add_le` and prove instead that the two branch estimates sum to at most twice the
current estimate. The estimate need not be an exact conditional expectation; a pessimistic upper
bound suffices. The conclusion returns the
invariant for the final state together with `Φ final ≤ Φ initial`; use the final invariant to
identify the final estimate with the cost of the constructed object. For exact conditional
expectations of a real function on the cube, `BitString.expect_le_greedy_fixCoord` in
`CslibFrontier.Foundations.BooleanAnalysis.GreedyFixing` already does this.

[Johnson.lean](../../CslibFrontier/Logics/Propositional/CNF/Johnson.lean) is the satisfiability
client. Its state is the partially set formula and the variables set to `true`; its estimate is
the weight `Σ_c 2 ^ (L - |c|)`. It sets a variable with the resolution module's `CNF.restrict`. Its invariant records
that the remaining variables are those still to be set and that the partial formula falsifies
the same number of clauses as the original under any completion. [Johnson/PolyTime.lean](../../CslibFrontier/Logics/Propositional/CNF/Johnson/PolyTime.lean)
certifies the running time. Because `L` is read from the input formula, the rounds form a fold
whose step reads the input, certified by `foldlWithInput_of_bounded_growth`. Its growth premise
uses the fact that setting a variable does not lengthen the encoded formula. The complete
[JohnsonMaxSAT client](../../CslibFrontierTests/JohnsonMaxSAT.lean) checks a tight `7 / 8`
instance and a formula with an empty clause, where the `1 / 2` bound fails without its
hypothesis. Build it with `scripts/build.sh CslibFrontierTests.JohnsonMaxSAT`.

When the averaging argument uses only `k`-wise independence, you can search a small sample
space instead of fixing bits one by one. For satisfiability,
[KWiseIndependent.lean](../../CslibFrontier/Logics/Propositional/CNF/KWiseIndependent.lean) takes a
family `h` with `IsKWiseIndependentHash k h` and a labelling `e` of the variables that is
injective on `φ.vars`. `exists_two_pow_mul_countUnsat_le` then gives a seed `i` with
`2 ^ k * φ.countUnsat (h i ∘ e) ≤ φ.length` whenever every clause has at least `k` distinct
literals. [ParitySearch.lean](../../CslibFrontier/Logics/Propositional/CNF/ParitySearch.lean)
instantiates it for `k ≤ 3` with the three-wise parity hash
`LinearHash.isKWiseIndependentHash_dotProduct_cons_true`, labelling each variable by the binary
digits of its position. `paritySearch` folds `betterCandidate` over
the fewer than `4n` candidate assignments, and
[ParitySearch/PolyTime.lean](../../CslibFrontier/Logics/Propositional/CNF/ParitySearch/PolyTime.lean)
certifies the running time with `foldlWithInput_of_bounded_growth`. Every candidate is a
sublist of the variable list, which bounds the fold's growth. The
[ParitySearchMaxSAT client](../../CslibFrontierTests/ParitySearchMaxSAT.lean) evaluates the
candidate lists. It also shows that the parity space is not four-wise independent and that the
guarantee fails for clauses of four literals. Build it with
`scripts/build.sh CslibFrontierTests.ParitySearchMaxSAT`.

**When it fails:** if the round inequality holds only on reachable states, strengthen the
invariant rather than the estimate. Clauses with complementary literals, for example, make
Johnson's weight strictly pessimistic, but the inequality still holds for every partial
formula without repeated literals. If the fold's growth premise fails, check that the step
does not enlarge the encoded state by more than a polynomial in the input.

## Round, solve exactly and certify a pseudo-polynomial table

**Goal:** an approximation scheme that rounds numbers, solves the rounded instance exactly by
dynamic programming, and runs in polynomial time. Import
`CslibFrontier.Algorithms.Lean.Knapsack.PolyTime` (it re-exports `ProfitDP` and `FPTAS`) and open
`Cslib.Algorithms.Lean.Knapsack Turing.MultiTapeTM ComputableInPolyTime`.

First prove the exact program correct. [Knapsack/ProfitDP.lean](../../CslibFrontier/Algorithms/Lean/Knapsack/ProfitDP.lean)
folds a table indexed by profit over the items. Its invariant `TableSpec` records the table
length (total profit plus one), that each entry is a subsequence of the right profit, and that
each entry weighs at most every subsequence of that profit. Prove the invariant for the initial
table and for one step, then fold it (`TableSpec.foldl`). Then prove the rounding bound against
the exact program on the rounded instance: [Knapsack/FPTAS.lean](../../CslibFrontier/Algorithms/Lean/Knapsack/FPTAS.lean)
rounds the values to at most `n * k`, and `sub_one_mul_value_le_fptas` gives
`(k - 1) * OPT ≤ k * value`.

Then certify the running time, as [Knapsack/PolyTime.lean](../../CslibFrontier/Algorithms/Lean/Knapsack/PolyTime.lean)
does. Certify one step of the table jointly in the table and the item, and pass it to `foldl'`.
Discharge the fold's states bound at every prefix (`l.take i`) from the invariant: the table has
total-profit-plus-one entries, each a subsequence of the items. That bound is polynomial only
when profits are charged in unary, so read them in `encUnary`. The FPTAS computes its rounded
values in unary from `k` in unary, while weights and the capacity stay in binary.
[Knapsack/Unary.lean](../../CslibFrontier/Computability/Complexity/Problems/Knapsack/Unary.lean)
turns the exact program into `Knapsack ∈ P` for the unary-value encoding.

For a hardness-of-approximation statement in this style, state the algorithm as a function with
a plain `ComputableInPolyTime` hypothesis, a validity hypothesis and a ratio hypothesis. Derive
`P = NP` from a known `NPComplete` problem through `NPComplete.P_eq_NP_of_mem_P`, as
[PCP/Approximation/BinPacking.lean](../../CslibFrontier/Computability/PCP/Approximation/BinPacking.lean)
does from `Partition` and
[PCP/Approximation/KCenter.lean](../../CslibFrontier/Computability/PCP/Approximation/KCenter.lean)
does from `DominatingSet`.

Check the clients with
`scripts/build.sh CslibFrontierTests.KnapsackFPTAS CslibFrontierTests.BinPackingApprox`. The
[KnapsackFPTAS client](../../CslibFrontierTests/KnapsackFPTAS.lean) checks an instance where the
scheme is not optimal but meets its bound. The [BinPackingApprox client](../../CslibFrontierTests/BinPackingApprox.lean)
shows that an exact, non-polynomial algorithm satisfies the hardness hypotheses other than
running time, and that First Fit violates the ratio hypothesis.

For a ratio of a greedy packing that pairing cannot give, use a weighting function, as
[BinPacking/FirstFitWeight.lean](../../CslibFrontier/Algorithms/Lean/BinPacking/FirstFitWeight.lean)
does for First Fit's `17/10`. Keep the weights in `ℕ` by scaling them by `10 * C`, so each case
of the piecewise weight closes with `split_ifs <;> omega`. Bound the weight of one bin
(`sum_map_firstFitWeight_le`) and transfer it to a packing with
`IsPacking.sum_map_le_mul_length`. Then lower-bound the algorithm's bins from the invariant of
its rule: for First Fit, every item of a later bin overflows every earlier bin
(`pairwise_forall_lt_sum_add_firstFit`), which is stronger than pairwise overfull bins. The
result `ten_mul_length_firstFit_le` gives `10 * FF ≤ 17 * OPT + 8` against every packing, and
`length_firstFit_le_ceil` gives `FF ≤ ⌈17/10 * OPT⌉`. The absolute bound
`FF ≤ ⌊17/10 * OPT⌋` of [Dósa and Sgall][dosasgall2013] is not formalized. The
[BinPackingFirstFitWeight client](../../CslibFrontierTests/BinPackingFirstFitWeight.lean) checks a bin
attaining the weight bound and an instance with `OPT = 9` where First Fit uses `15` bins; check it
with `scripts/build.sh CslibFrontierTests.BinPackingFirstFitWeight`. If a case of the weight bounds
does not close under `omega`, check the scaling and whether each breakpoint of the weight is open
or closed as in the source; if the lower bound fails, check that it uses the algorithm's rule, not
only pairwise overfull bins.

**When it fails:** if the `foldl'` states-bound premise fails, bound the encoded table through the
invariant (its length and the subsequence property of every entry), not by the number of steps.
Then check that the profits really are read in `encUnary`; with binary profits the table is
exponential in the input and no bound exists. If `fun_prop` times out on `max` or on a map whose
body mixes unary and binary arithmetic, build that certificate by hand. Use `ite` with the plain
`ComputableInPolyTime.binary_le'` for `max`, and `mapWithInput` with
`ComputableInPolyTime.unary_to_binary`, `binary_mul'` and `ComputableInPolyTime.binary_div` for
the rounding map.

## Preserve independent workspace

<!-- worked-example -->

**Worked example: Compose a logspace callback without storing the intermediate word**

**Goal:** `ComputableInLogSpace f encIn encOut`, whose [definition](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/LogSpace.lean) requires halting and workspace at most `c * (Nat.log2 n + 1)`. Input and append-only output are excluded. Use the `LogSpace.Words` and `LogSpace.CounterProgram.Words` modules under `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity`, as imported by [LogSpaceFunProp](../../CslibFrontierTests/LogSpaceFunProp.lean), and open `Turing.MultiTapeTM`.

Start with a logspace certificate for the callback; the client composes it with concatenation and projections:

<!-- excerpt: deterministic-logspace -->
```lean
/-- A supplied logspace certificate composes with the registered rules. -/
example (f : List Bool → Bool) (hf : ComputableInLogSpace f encBits encBool) :
    ComputableInLogSpace (fun p : List Bool × List Bool => [f (p.1 ++ p.2), f p.2])
      (encPair encBits encBits) (encList encBool) := by
  fun_prop
```

**Result:** the two callback results form a list computable in logarithmic workspace under the displayed encodings. `ComputableInLogSpace.comp` uses `ComputableInTimeAndSpace.comp_space`: the second machine's requests for intermediate symbols cause recomputation of the first machine's output. It need not store the complete intermediate word. The implementation also proves that logspace outputs have polynomial length, allowing position counters to fit the space bound.

**When it fails:** a polynomial-time callback hypothesis alone will not discharge a logspace goal. Prove its stronger certificate or change the intended claim explicitly.

<!-- /worked-example -->

This conclusion is different from `ComputableInO`, which additionally charges encoded output against its space bound. A long output is compatible with logarithmic *workspace*. For sharper independent bounds, state `ComputableInTimeAndSpace` or `ComputableInBigO` directly and retain both functions. When only polynomial time is needed downstream, use `ComputableInLogSpace.computableInPolyTime`; the same client demonstrates that transition. See the [resource table](../machines-and-classes/native-and-resources.md).

## Turn computation into P, NP and hardness

<!-- worked-example -->

**Worked example: Supply the fields of a class-membership proof**

**Goals:** `A ∈ P enc` or `A ∈ NP enc`. Open [NPCompleteness](../../CslibFrontierTests/NPCompleteness.lean), which imports `CslibFrontier.Computability.Complexity.Problems.Clique` and `CslibFrontier.Tactic.PolyTime`, and opens `Cslib.Complexity Turing.MultiTapeTM`.

A P proof supplies the Boolean decider, its computation certificate, and its membership equivalence:

<!-- excerpt: deterministic-p -->
```lean
/-- A P proof supplies a Boolean decider, its cost certificate and its membership equivalence. -/
theorem startsTrue_mem_P : {w : List Bool | w.headD false = true} ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- The same ordinary decision problem is in NP by the public class inclusion. -/
example : {w : List Bool | w.headD false = true} ∈ NP encBits :=
  P_subset_NP startsTrue_mem_P
```

For NP, additionally supply a verifier and a polynomial certificate-length condition. In this API `IsVerifier` requires the witness length to **equal** the polynomial evaluated at encoded input length; use [IsVerifier.of_padding](../../CslibFrontier/Computability/Complexity/Classes/NP.lean) when adapting a bounded-witness presentation. The client reuses the library's Clique theorem:

<!-- excerpt: deterministic-np -->
```lean
/-- For NP, the verifier also needs a proved certificate bound: here exactly the encoded
instance length, represented by the polynomial `X`. -/
theorem clique_mem_NP : Clique ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, Clique.verifier, by fun_prop, Clique.isVerifier⟩
```

**Result:** the first example supplies P membership and then NP membership by inclusion; the second supplies Clique's NP membership using the existing verifier and its exact witness-length theorem. These are applications of the library's class interfaces.

**When it fails:** separate a failed computation certificate from a failed membership or witness-length equivalence. Check the verifier's encoding and exact length convention before trying a different tactic.

<!-- /worked-example -->

<!-- worked-example -->

**Worked example: Transfer hardness through graph complementation**

**Goal:** prove `PolyTimeReducible encA encB A B` from a known hard source problem to the target problem, then combine transferred hardness with NP membership.

Continue in [NPCompleteness](../../CslibFrontierTests/NPCompleteness.lean), keeping the imports and open declarations above. Build a map from the known hard problem **to** your problem. Prove its cost separately from correctness. Here `complementInstance`, defined and certified immediately above the excerpt in the source file, complements the declared graph and keeps the requested size:

<!-- excerpt: deterministic-reduction -->
```lean
/-- A reduction has a map, its polynomial-time certificate, and a membership equivalence.
The equivalence must point from the source problem to the image in the target problem. -/
theorem independentSet_to_clique :
    PolyTimeReducible (encPair encGraph encNat) (encPair encGraph encNat) IndependentSet Clique :=
  ⟨complementInstance, by fun_prop,
    fun ⟨G, k⟩ => (Graph.compl_mem_Clique_iff G k).symm⟩

/-- Combine NP membership with hardness transferred from the known hard source problem. -/
theorem clique_npComplete : NPComplete (encPair encGraph encNat) Clique :=
  ⟨clique_mem_NP, IndependentSet_npHard.trans independentSet_to_clique⟩
```

**Result:** `.symm` aligns the correctness lemma with the source-to-target membership equivalence, and `NPHard.trans` transports hardness forward. The final proof combines that hardness with `clique_mem_NP`. This client reuses known results; it is not a new completeness theorem.

**When it fails:** check the reduction's direction and both encodings, then isolate its computation and equivalence obligations. A new problem still needs the verifier, certificate length, reduction cost and equivalence. Check empty instances and boundary targets as the client does.

<!-- /worked-example -->

`PolyTimeReducible.mem_P` instead transports a target's P algorithm backward to the source. Use the [reduction reference](../machines-and-classes/reductions.md) when the desired reduction is stronger than polynomial-time many-one reducibility.

[complexitylib]: ../sources.md#complexitylib
[dosasgall2013]: ../sources.md#dosasgall2013
