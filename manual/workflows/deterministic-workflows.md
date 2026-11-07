# Prove deterministic resource bounds

Use plain `Turing.MultiTapeTM.ComputableInPolyTime` for public polynomial-time claims. Its definition supplies a finite native machine with independently polynomially bounded time and workspace, measured against encoded input length. Each Lean block is a **contextual excerpt** from the current source, requiring its linked original file; these are not newly compiled standalone examples. The excerpts are by Samuel Schlesinger, under the source repository's Apache 2.0 license. [complexitylib][complexitylib]

## Compose a certified function

<!-- worked-example -->

**Worked example: Swap the arguments of a certified routine**

**Goal:** `ComputableInPolyTime f encIn encOut`. Start with `Complexity.Tactic.PolyTime`, the modules supplying your operations, and `open Turing.MultiTapeTM`. [PolyTimePlainDriver](../../ComplexityTests/PolyTimePlainDriver.lean) also imports `Complexity.Computability.WordRAM.Native` for its arithmetic examples.

The input obligation in this excerpt is a polynomial-time certificate for `routine` with *binary* pair inputs and binary output:

<!-- excerpt: deterministic-compose -->
```lean
example (routine : ℕ × ℕ → ℕ)
    (hroutine : ComputableInPolyTime routine (encPair encNat encNat) encNat) :
    ComputableInPolyTime (fun p : ℕ × ℕ => routine (p.2, p.1))
      (encPair encNat encNat) encNat := by polytime
```

Prove certificates for opaque subroutines, then let `fun_prop` compose registered rules or use `polytime` for the richer certificate search.

**Result:** argument swapping followed by `routine` is polynomial-time computable under the stated binary encodings. This does not establish any additional functional specification of `routine`.

**When it fails:** expose a local definition or supply its named certificate, then inspect the remaining contract. Do not replace the goal with a tidy interface.

<!-- /worked-example -->

The [automation reference](../design-and-assurance/automation.md) explains registration and [troubleshooting](troubleshooting.md) handles failures.

For binary sign-magnitude integers, import
`Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary`.
The plain `ComputableInPolyTime.intBin_natAbs`, `intBin_isNeg`, `intBin_signMagnitude`,
`intBin_prod` and `intBin_pow` rules compose through `fun_prop`; `intBin_pow'` accepts computed
base and unary exponent certificates. The complete
[IntBinary client](../../ComplexityTests/RationalHitting/IntBinary.lean) checks composed products, powers,
magnitudes and signs. A binary exponent has a different output-size obligation: do not replace
the unary exponent encoding merely to make a goal match.

For a padded integer dot product, import
[PolyTime/Int/DotProduct.lean](../../Complexity/Computability/PolyTime/Int/DotProduct.lean)
and use `ComputableInPolyTime.listDotProduct`. It certifies the existing pure public
`Mathlib.Tactic.Matrix.ListMatrix.dotProduct`: the cutoff is unary, coefficients are signed
binary, missing entries are zero, and entries beyond the cutoff are ignored. Runtime still
charges both complete framed input lists. The operation lives in a Mathlib tactic-support
file but is ordinary term-level arithmetic, not a meta program.
The pure [list identities](../../Complexity/Foundations/Data/List/DotProduct.lean) and
[residue-matrix bridge](../../Complexity/Foundations/Data/ZMod/DotProduct.lean) require neither
crypto nor native imports. The former local Lyubashevsky `listDot` duplicate has been removed;
its verifier, extractor and signer use the same upstream operation. The
[checked clients](../../ComplexityTests/ListDotProduct.lean) cover padding, truncation, signed
large coefficients and unchanged verifier outcomes and commitment bytes. This API
consolidation adds no cryptographic security claim.

Keep a record's encoded tuple layout at its construction boundary. For example,
[`NativePacket.PacketCtx.mk_polyTime`](../../Complexity/Computability/Circuit/Frontier/TensorNetwork/PacketTerms.lean)
composes certificates for named fields while preserving the existing encoded words; its
[packet-construction client](../../Complexity/Computability/Circuit/Frontier/TensorNetwork/NativeChildPolyTime.lean)
does not reconstruct the product tree. The
[`BranchEvalInput` interface](../../Complexity/Computability/PolyTime/BooleanAnalysis/SparsePolyCounter.lean)
similarly supplies named parameter access and certificates with the original unary/binary
choices. Use these boundaries when changing a client, and retain its encoded-length bounds.

For a computed optional value, import
`Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option`.
The shared `ComputableInPolyTime.optionMapWithInput` rule certifies
`fun x => (value x).map (f x)` from certificates for `value` and the joint callback
`fun p => f p.1 p.2`. The callback is charged against both the original input and
the present value; input and output value encodings may differ.
The [public-import client](../../ComplexityTests/Machines/Turing/MultiTape/Internal/PolyTimeOptionPublicImport.lean)
checks a captured parameter and an encoding change.
[Boolean measurement search](../../Complexity/Computability/PolyTime/LinearAlgebra/BooleanMeasurements.lean)
uses this rule for its optional-result codec, and
[hybrid CCA composition](../../Complexity/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
uses it to postprocess successful decapsulation while preserving rejection.

## Walk two lists with a collecting fold

Import `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold`
and open `Turing.MultiTapeTM`. Apply `ComputableInO.zipFold` or
`ComputableInSpace.zipFold` explicitly. The complete [zipFold clients](../../ComplexityTests/ZipFold.lean)
show padding, dropping and a time certificate; [subtractSums_inSpace](../../Complexity/Computability/TreeEval/Reader/Cert/Regs.lean)
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

**Goal:** a plain computation certificate together with a final invariant. Import `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration`. The public import exposes [ComputableInPolyTime.iterate_spec](../../Complexity/Computability/Machines/Turing/MultiTape/Internal/PolyTimeLoops.lean); its current implementation lives in the machine layer.

Supply three computation certificates: the iteration count in unary, the initial state, and the step. Then provide an invariant indexed by original input, iteration number and state. Prove initialization and preservation. Finally, bound the encoded state under that invariant at **every** index up to the count by a `PolyBounded` function of original input length. The mathematical bound itself need not be computable.

The result has two projections: polynomial-time computability of the iterated function, and the invariant at termination. [Ladner’s shrink-loop client](../../Complexity/Computability/Complexity/Classes/Ladner.lean) obtains `hreduce` and `hinv` this way: its invariant preserves satisfiability and bounds the current formula's encoded length. That use is inside the theorem's stated reduction and growth hypotheses, not an unconditional SAT algorithm.

For a step capturing a parameter, use `iterateWith_spec` and certify the joint `(parameter, state)` operation. `iterateWith_of_bounded_growth` handles additive encoded-state growth bounded polynomially in the original input. A separate efficient procedure for each fixed parameter does not provide the required uniform joint certificate. A polynomial number of efficient steps also does not bound a state that doubles each time. The [plain loop regression client](../../ComplexityTests/Machines/Turing/MultiTape/Internal/PolyTimeLoops.lean) exercises both positive contracts and a failed constant-state bound. When the size obligation fails, inspect the representation and growth argument before changing tactics.

## Preserve independent workspace

<!-- worked-example -->

**Worked example: Compose a logspace callback without storing the intermediate word**

**Goal:** `ComputableInLogSpace f encIn encOut`, whose [definition](../../Complexity/Computability/Machines/Turing/MultiTape/Complexity/LogSpace.lean) requires halting and workspace at most `c * (Nat.log2 n + 1)`. Input and append-only output are excluded. Use the `LogSpace.Words` and `LogSpace.CounterProgram.Words` modules under `Complexity.Computability.Machines.Turing.MultiTape.Complexity`, as imported by [LogSpaceFunProp](../../ComplexityTests/LogSpaceFunProp.lean), and open `Turing.MultiTapeTM`.

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

**Goals:** `A ∈ P enc` or `A ∈ NP enc`. Open [NPCompleteness](../../ComplexityTests/NPCompleteness.lean), which imports `Complexity.Computability.Complexity.Problems.Clique` and `Complexity.Tactic.PolyTime`, and opens `Cslib.Complexity Turing.MultiTapeTM`.

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

For NP, additionally supply a verifier and a polynomial certificate-length condition. In this API `IsVerifier` requires the witness length to **equal** the polynomial evaluated at encoded input length; use [IsVerifier.of_padding](../../Complexity/Computability/Complexity/Classes/NP.lean) when adapting a bounded-witness presentation. The client reuses the library's Clique theorem:

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

Continue in [NPCompleteness](../../ComplexityTests/NPCompleteness.lean), keeping the imports and open declarations above. Build a map from the known hard problem **to** your problem. Prove its cost separately from correctness. Here `complementInstance`, defined and certified immediately above the excerpt in the source file, complements the declared graph and keeps the requested size:

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
