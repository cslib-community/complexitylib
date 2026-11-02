# Work with randomized and oracle programs

Start with three separate questions: what program is being described, what distribution it denotes, and what machine implements it. `ProbComp α` describes finite-uniform sampling with ordinary `do` notation; `ProbComp.eval` interprets that syntax as a `PMF α`. `ProbOracleComp spec α` adds external requests whose reply types are given by `spec`. The underlying `OracleComp` is a free program over a typed request interface. A PMF supplies mathematical probability semantics; merely writing a PMF does not supply a sampler or a runtime certificate. The [programs and realization reference](../programs-crypto-and-probability/programs-and-realization.md) explains these layers and their sources. [complexitylib][complexitylib]

## Certify a closed randomized routine

Use `IsPPTOn input output program` when the required conclusion is a uniform, strict polynomial-time implementation on encoded types. The encodings are embeddings into bit lists. One finite-control fair-coin machine and one polynomial clock must work for every input, with exact equality of encoded output laws. Output writing is charged. This is the contract to request before proving a probabilistic routine efficient.

<!-- worked-example -->

**Worked example: Compose a fair coin with a certified callback**

**Goal:** certify a coin-sampling routine, then a scan whose deterministic callback has a supplied polynomial-time certificate.

Open [ComplexityTests/PPTTactic.lean](../../ComplexityTests/PPTTactic.lean). Its entry import is `Complexity.Tactic.PPT`; the file also imports `Complexity.Crypto.Computational.GGM.Evaluation` for later clients. The following contextual excerpt uses its `open Cslib Cslib.Probability Turing.MultiTapeTM`. It is copied from the checked file, not independently checked as a standalone snippet.

<!-- excerpt: ppt-coin-reverse -->
```lean
example : IsPPTOn encBits encBits (fun word => do
    let bit ← ProbComp.uniform Bool
    pure (if bit then word.reverse else word)) := by
  ppt
```

The working sequence is: choose the input/output encodings, write the program, supply certificates for named callbacks, and invoke `ppt`. It combines probabilistic composition rules with deterministic `polytime` automation. For a callback, the missing obligation is often a deterministic certificate with the exact captured-argument encoding. This second contextual excerpt, from the same client, makes that obligation visible:

<!-- excerpt: ppt-callback-scan -->
```lean
example (test : List Bool × Bool × ℕ → Bool)
    (htest : ComputableInPolyTime test
      (encPair encBits (encPair encBool encUnary)) encBool) :
    IsPPTOn encBits encBool (fun word => do
      let bit ← ProbComp.uniform Bool
      pure ((List.range word.length).any fun i => test (word, bit, i))) := by
  fail_if_success (clear htest; ppt)
  ppt
```

**Result:** native efficiency of the whole sampling-and-scan routine. This does not establish the application-specific meaning of `test`.

**When it fails:** compare tuple association and encodings before unfolding the machine. Here the scan index is unary; a binary certificate is a different contract. For folds, inspect the client's explicit `PolyBounded` growth premise. For a named routine, the same file demonstrates registering its proved theorem with `@[program_certificate]`.

<!-- /worked-example -->

Also check the sampler itself. `ProbComp.uniform (Fin 3)` has exact uniform semantics, but a strictly bounded fair-coin machine cannot give each outcome probability one third. The client deliberately tests that `ppt` does not certify it for free. Use an applicable dyadic sampler or the library's approximate-sampling results, carrying the approximation error into the later probability proof.

## Certify an adaptive oracle client

For native oracle efficiency, start with `WordOracleComp Operation α`: finite operation names and word payloads/replies.

<!-- worked-example -->

**Worked example: Bound the reply prefix of an adaptive oracle call**

**Goal:** certify the oracle client's native runtime while allowing its next query to depend on the previous reply.

Open [ComplexityTests/OracleComposition.lean](../../ComplexityTests/OracleComposition.lean), whose main import is `Complexity.Computability.Probabilistic.Oracle.Composition`. Its query-bound examples additionally import `Complexity.Computability.Probabilistic.QueryBounds`. This contextual excerpt uses the file's `open Cslib Cslib.Probability Turing Turing.MultiTapeTM`:

<!-- excerpt: oracle-adaptive-prefix -->
```lean
private noncomputable def adaptive (word : List Bool) : WordOracleComp Bool (List Bool) := do
  let first ← List.take 1 <$> ProbOracleComp.query (false, word)
  if first = [true] then List.take word.length <$> ProbOracleComp.query (true, first)
  else pure []

-- The certificate is found compositionally from the bounded-prefix query and the conditional.
private theorem adaptive_isOraclePPTOn : IsOraclePPTOn encBits encBits adaptive := by
  unfold adaptive
  fun_prop
```

First specify the operation set and request representation. Then bound the amount of each reply inspected or retained, prove deterministic preprocessing efficient, and compose the query/conditional rules.

**Result:** one machine and clock work for every input, state type, stateful handler and initial state, preserving the joint law of output and final oracle state. The certificate charges request construction and reply access; the external handler's computation remains external.

Next inspect behavior under a concrete handler. The same client defines `counting`, which increments a counter on every call. Its semantic examples establish final count one on the unselected branch and two on the selected branch. This catches interaction differences that equality of output marginals could hide. For the simpler `runWith` interface, open [ComplexityTests/OracleSemantics.lean](../../ComplexityTests/OracleSemantics.lean).

Use `adaptive_isOraclePPTOn.query_bounds` to obtain polynomial bounds on external call count and request length. A separately proved `IsCostBounded` charges chosen requests along every path; `ProbOracleComp.IsQueryBounded` counts external calls rather than private samples. Neither bound by itself pays for arbitrary Lean callbacks.

**When it fails:** if `fun_prop` fails on returning an entire oracle reply, check whether the requested conclusion permits unbounded output. The linked client contains explicit failure examples and the bounded-prefix repair.

<!-- /worked-example -->

When replacing the external handler with an implementation, open [Oracle/Substitution.lean](../../Complexity/Computability/Probabilistic/Oracle/Substitution.lean). The plain-certificate variant `IsOraclePPTOn.run_interpret_preprocess_open'` requires efficient preparation, initialization and handling, plus an invariant and bounds on reply length and added encoded state. Its `hresources` premise also certifies a uniform unary computation of the resource allowance from the original caller and request; an abstract polynomial bound alone does not supply this certificate. Repeated state doubling explains why “each call is polynomial time” is insufficient.

## Carry the certificate into a security proof

Keep efficiency and security as separate goals. In [Crypto/Computational/Basic.lean](../../Complexity/Crypto/Computational/Basic.lean), computational indistinguishability quantifies over certified strict-PPT distinguishers. It does not require the compared PMF ensembles to be efficiently sampleable or polynomially bounded in length. Check those properties separately when the intended construction needs them.

Specify the experiment, admissible adversaries, success event and assumption; prove the reduction's efficiency using the routines above; then prove the probability or advantage inequality. Semantic rewrites and native certificates discharge different obligations. If a proposed reduction only has a query bound, return to the realization step before calling it a computational security reduction. Use the [security-game reference](../programs-crypto-and-probability/security-games-and-primitives.md) to choose the correct primitive and adversary model.

[complexitylib]: ../sources.md#complexitylib
