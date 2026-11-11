# Proof automation and client interfaces

The automation layer searches for proofs of explicit mathematical contracts. It generally reuses named certificates and compositional rules; it is not a compiler that can assign a polynomial bound to an arbitrary Lean program. In particular, a short tactic call hides a checked derivation, but the model, algorithm and invariant still have to be right. [cslib-frontier][complexitylib]

## Find the tactic for a goal

The tables below list the tactics and commands the library provides for general use, by the goal
each proves; helper macros written for the proofs of a single module are left out. The
module column omits the common prefix `CslibFrontier.`; import that module, and for a scoped
tactic also open the namespace named in its row. Each reference is the most complete account of
the tactic, in this chapter or another, or its checked clients when no chapter covers it; the
clients show the imports and local context. Search tactics such as `polytime` and `fits` either
close the goal or fail with a diagnostic; when `degree`, `logspace`, `space`, `fo_qf`,
`fo_iso_closed` or `fo_definable` fails, the error ends with a note saying what to supply, as
described in [Read the remaining goal](../workflows/troubleshooting.md#read-the-remaining-goal).
Execution and reduction tactics such as `wram_exec`, `fo_reduction` and `realize` leave the
obligations they cannot prove as goals; their references say which.

**Resource certificates**

| Tactic | Module | Goal | Reference |
|---|---|---|---|
| `polytime`, `polytime [f, g]` | `Tactic.PolyTime` | `ComputableInPolyTime f encIn encOut`, or its tidy form | [Named certificates](#named-certificates-and-polynomial-time) |
| `ppt`, `ppt [f, g]` | `Tactic.PPT` | `IsPPTOn`, `IsPPT`, `IsOraclePPTOn`, `IsOraclePPT` | [Named certificates](#named-certificates-and-polynomial-time), [other resource predicates](#other-resource-predicates) |
| `@[program_certificate h*]` (attribute) | `Tactic.PolyTime.Init` | registers a certificate for `polytime`, `logspace` and `ppt` | [Named certificates](#named-certificates-and-polynomial-time) |
| `logspace` | `Tactic.LogSpace` | `ComputableInLogSpace f encIn encOut` | [Other resource predicates](#other-resource-predicates), [checked clients](../../CslibFrontierTests/LogSpaceTactic.lean) |
| `space`, `space [f]` | `Tactic.Space` | `ComputableInSpace f encIn encOut S`, with an explicit budget `S`, including finite values, decidable conditions and Boolean connectives | [Choose a model](../workflows/choosing-models.md#write-the-contract-before-the-proof) |
| `degree` | `Tactic.Degree` | `ComputableInDegree f encIn encOut d e` | [Preserve explicit polynomial degrees](#preserve-explicit-polynomial-degrees) |
| `fun_prop` (Mathlib) | `Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists` | `ComputableInO f encIn encOut T S` | [Assemble joint time and space bounds](#assemble-joint-time-and-space-bounds) |
| `option_match_to_elim` | `Tactic.OptionMatch` | any goal with an option match, before resource automation | [Rewrite option matches](#rewrite-option-matches-before-resource-automation) |
| `growth_poly`, `growth_poly [h]` | `Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation` | `PolyBounded size cost`, `Cslib.PolynomiallyBounded p` | [Composing polynomial resource envelopes](../machines-and-classes/native-and-resources.md#composing-polynomial-resource-envelopes) |
| `bigO` (scoped, `Turing.MultiTapeTM`) | `Computability.Machines.Turing.MultiTape.Complexity.BigOLe` | `u ≼ v` (`BigOLe`) | [Source docstring](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/BigOLe.lean#L123) |

**Encodings and arithmetic**

| Tactic | Module | Goal | Reference |
|---|---|---|---|
| `enc_structure eS : S where f₁ : e₁, …` (command) | `Computability.Machines.Turing.MultiTape.Encodings.Structure` | declares the encoding of a structure and its rules | [Choose a model](../workflows/choosing-models.md#write-the-contract-before-the-proof) |
| `enc_inductive eT : T where …` (command) | `Computability.Machines.Turing.MultiTape.Encodings.Inductive` | declares the encoding of an inductive type and its rules | [Choose a model](../workflows/choosing-models.md#write-the-contract-before-the-proof) |
| `enc_len`, `enc_len [l] at h ⊢` | `Tactic.EncLen` | a linear bound on encoded lengths | [Close encoded-length arithmetic](#close-encoded-length-arithmetic) |
| `fits`, `fits [h]` | `Tactic.Fits` | `Fits w v` or `v < 2 ^ w` | [Close word-size bounds](#close-word-size-bounds) |

**Word-RAM and counter programs**

| Tactic | Module | Goal | Reference |
|---|---|---|---|
| `ram_eval`, `ram_eval n [p, h]` (scoped, `Cslib.WordRAM`) | `Computability.WordRAM.Notation` | `ExecWithin w c x y T`, `Exec w c x y T` | [Execute word-RAM code](#execute-word-ram-code) |
| `ram_exact_eval n [p, h]` (scoped, `Cslib.WordRAM`) | `Computability.WordRAM.ExactNotation` | the same, over the exact basis | [Execute word-RAM code](#execute-word-ram-code) |
| `wram_exec`, `wram_exec -split (disch := t) [h]` | `Computability.WordRAM.SymbolicExec` | `WP w c x Q`, `∃ y, ExecWithin w c x y T ∧ P y`, and the `Exec` forms | [Execute word-RAM code](#execute-word-ram-code) |
| `wram_simp [h] at l` | `Computability.WordRAM.SymbolicExec` | reads of registers and memory after `Data.set` and `Data.write` | [Execute word-RAM code](#execute-word-ram-code) |
| `wram_bounded` | `Computability.WordRAM.SymbolicExec` | `y.Bounded w` for data built by writes | [Execute word-RAM code](#execute-word-ram-code) |
| `wram_call h with pats`, `wram_call h renamed hf with pats` | `Computability.WordRAM.SymbolicExec.Call` | a `WP` or `WP.Exact` goal at a call of the routine that `h` specifies | [Routine calls](../algorithms-and-memory/wordram-and-bridges.md#proving-routine-calls-and-memory-frames) |
| `wram_call h canonical hf with pats` | `Computability.WordRAM.SymbolicExec.CanonicalCall` | the same, keeping the caller state as `small.extend bank caller` | [Routine calls](../algorithms-and-memory/wordram-and-bridges.md#proving-routine-calls-and-memory-frames) |
| `ram_keep view`, `ram_keep view using frame` (scoped, `Cslib.WordRAM`) | `Computability.WordRAM.MemoryView` | a block, list or footprint view, kept through stores outside its support | [Routine calls](../algorithms-and-memory/wordram-and-bridges.md#proving-routine-calls-and-memory-frames) |
| `realize` (scoped, `Cslib.WordRAM`) | `Tactic.Realize` | `Realizes B p input output safe work` for a memory client | [Certify and reuse memory methods](#certify-and-reuse-memory-methods) |
| `simp only [client_simps]` (simp set) | `DataStructure.StateTransition`; `Computability.WordRAM.Realization.Basic` for `memoryCost` | splits `clientResult`, `clientState`, `clientHistory`, `totalCost`, `ValidHistory` and `memoryCost` at the binds of a client | [Relational operations and adaptive clients](../algorithms-and-memory/memory-specifications.md#relational-operations-and-adaptive-clients) |
| `cp_step`, `cp_step [h]` | `Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step` | one step of `P.Reaches w Q (l, regs) s'` for a counter program | [Step through counter programs](#step-through-counter-programs) |

**Circuits, logic and probability**

| Tactic | Module | Goal | Reference |
|---|---|---|---|
| `synthesis_available` | `Tactic.Synthesis` | membership of a wire among those already available | [Circuit construction](#circuit-construction), [worked example](../workflows/finding-results.md#build-a-shared-boolean-circuit) |
| `synthesis_union` | `Tactic.Synthesis` | `X ⊆ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ`, syntactically or by a local hypothesis; `f ∈ A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ` by a local hypothesis | [Circuit construction](#circuit-construction) |
| `synthesis_step b using r` | `Tactic.Synthesis` | appends the rule `r` to the builder `b` | [Circuit construction](#circuit-construction) |
| `fo_qf`, `fo_iso_closed` | `Tactic.FirstOrder` | quantifier-freeness; closure of a class under isomorphism (`IsoClosed`) | [Logical descriptions](#logical-descriptions), [checked clients](../../CslibFrontierTests/FirstOrderAutomation.lean) |
| `fo_simp [h] at l` | `Tactic.FirstOrder` | unfolds the realization of formulas and interpreted structures | [Logical descriptions](#logical-descriptions) |
| `fo_reduction I [h]` | `Tactic.FirstOrder` | `FO.QFReduces K K'`, `FO.Reduces K K'` through the interpretation `I` | [Logical descriptions](#logical-descriptions) |
| `fo_definable`, `fo_wf [φ]` | `Tactic.FOOperator` | `Operator.Definable …`; formation conditions of explicit formulas | [Logical descriptions](#logical-descriptions), [checked clients](../../CslibFrontierTests/FOOperators.lean) |
| `simp only [pmf_norm]` (simp set) | `Languages.Probabilistic.Norm` | the law of a probabilistic program, to nested `PMF.bind` | [Normalize the law of a program](../workflows/probabilistic-workflows.md#normalize-the-law-of-a-program) |
| `simp only [runWith_norm, pmf_norm]` (simp set) | `Languages.Probabilistic.Oracle.Norm` | the law of an oracle experiment (`runWith` or stateless `evalWith` of interpreted handlers, including stateful inner reductions via `eval_interpret_eq_evalWith` / `evalWith_run_interpret`), to nested `PMF.bind` | [One semantics with several views](../programs-crypto-and-probability/programs-and-realization.md#one-semantics-with-several-views) |
| `pmf_swap`, `pmf_swap with x y` | `Tactic.PMFSwap` | an equation of distributions that draw the same independent samples in different orders | [Reorder independent samples](#reorder-independent-samples) |
| `pmf_hoist q`, `pmf_hoist q at h` | `Tactic.PMFSwap` | moves the samples of `q` toward the front of their `PMF.bind` chains | [Reorder independent samples](#reorder-independent-samples) |
| `supp_cases h`, `supp_cases h [p] with pat`; `simp only [supp_norm]` (simp set) | `Tactic.SuppCases` | inverts `h : x ∈ m.support` for a `PMF` or `OracleComp` program into the results of its parts | [Invert a support membership](../workflows/probabilistic-workflows.md#invert-a-support-membership) |
| `negligible`, `negligible using hle`, `negligible eventually hle` | `Tactic.Negligible` | `Cslib.Crypto.Negligible f` | [Close negligibility bounds](#close-negligibility-bounds) |
| `game_trans [g₁, …]`, `game_trans [g₁, …] using [h₀, …]` | `Tactic.GameHop` | `Game.advantage`, `Encryption.advantage`, one-sided or difference `Game.succProbability` bounds, and `CloseTo`, split into one subgoal per hop | [Step game hops](#step-game-hops-and-align-shared-random-draws) |
| `peel_binds`, `peel_binds x₁ …` | `Tactic.GameHop` | removes the shared leading draws of the two sides of a `Game.advantage`, `Encryption.advantage`, `CloseTo` or `PMF` equality goal | [Step game hops](#step-game-hops-and-align-shared-random-draws) |

The tactics search simp sets and Aesop rule sets that modules extend by registering lemmas: the
simp sets `wram_simps` (used by `wram_exec` and `wram_simp`), `cp_simps` (used by `cp_step`),
`fo_realize` (used by `fo_simp`), `supp_norm` (used by `supp_cases`) and `runWith_norm` (used with
`pmf_norm` on oracle experiments), and the Aesop rule sets
`PolyTime`, `PPT`, `OraclePPT`, `LogSpace`, `FirstOrder` and `FODefinable`.

## Assemble joint time and space bounds

Import `CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists`
and work in `Turing.MultiTapeTM`. Build one `ComputableInO` certificate for the whole
function with `fun_prop`, then use `ComputableInO.mono` to compare its assembled time and
space bounds with the desired bounds. Keep the input and output encodings explicit. The
complete [FunPropLists clients](../../CslibFrontierTests/Machines/Turing/MultiTape/FunPropLists.lean)
show this pattern for a list operation, finite tests, a binary-number branch and options,
including the separate arithmetic comparisons after automation succeeds.

The encoding determines which rule applies. `take'` and `drop'` require the computed count
to have encoding `encUnary`; binary numbers use `encNat`. Changing between those encodings
needs a certificate, not just a different annotation. The registered binary `natSucc` and
`natPred` rules carry quadratic time and linear charged space in encoded length. The
unary successor/predecessor rules have linear bounds. Space includes encoded output and
intermediate values; it is not an uncharged-output or scratch-only convention.

Tests against a fixed finite value (`decideEq'`) and binary zero (`natIsZero'`) retain the
tested computation's premise bounds. Testing a computed list with `isEmpty'` instead adds
that list's encoded length to both time and space. For equality of two computed values,
enable `ComputableInO.eq'` locally as a `fun_prop` rule when needed. It adds the explicit
time term `(La + 1) * (La + Lb + 1)`, where `La` and `Lb` are their encoded lengths, and
the encoded-pair space charge to the premise bounds. It is deliberately not a global rule,
so cheaper constant-test rules remain available.

If `fun_prop` cannot assemble the certificate, check the import, function's argument type,
encodings and available callback certificates; use the named compositional rule to inspect
the missing premise. If it succeeds but `mono` fails, inspect the intermediate/output
encoding lengths and prove the remaining growth inequalities. The tactic does not infer
those bounds or supply missing callback certificates. The [deterministic workflow](../workflows/deterministic-workflows.md)
explains the joint certificate and charged-space convention in context.

## Preserve explicit polynomial degrees

Import `CslibFrontier.Tactic.Degree` and `open Turing.MultiTapeTM` to use `degree` for
`ComputableInDegree f encIn encOut d e`. Degree `d` bounds both time and workspace;
degree `e` bounds encoded output length. In particular, `1 1` retains linear time,
linear space and linear output growth, rather than merely proving some polynomial bound.
The complete [DegreeTactic client](../../CslibFrontierTests/DegreeTactic.lean) checks option
matches and list-head/default composition with these explicit encodings:

```lean
example : ComputableInDegree (fun l : List ℕ => (l.head?).getD 0)
    (encList encUnary) encUnary 1 1 := by
  degree
```

`degree` rewrites supported option matches to `Option.elim`, then invokes `fun_prop`, using
reflexivity and linear arithmetic for degree side conditions. It does not unfold named
routines: first `unfold` a local wrapper, or provide its registered certificate. The
[Universal step client](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Universal/Complexity.lean)
uses this for tape reads, writes and fixed-direction moves, then composes their certificates.
The named read/move lemmas remain useful to other modules even when their proofs are one line.

This is composition of existing resource rules, not degree inference for arbitrary programs.
The new option-elimination and list-head rules apply at `1 1` and require an inhabited payload;
the tactic may solve other degrees only when the imported rules and arithmetic permit it.
Finite-enumeration matches, dependent matches and missing callback or loop-growth certificates
still need explicit reasoning. Use `polytime` when the contract needs only an unspecified
polynomial; use `fun_prop` with explicit bounds for `ComputableInO`.

## Named certificates and polynomial time

[`program_certificate`](../../CslibFrontier/Tactic/PolyTime/Init.lean) indexes a theorem by its efficiency predicate and the head constant of its program, with an encoding flag. The predicate index keeps the families apart: a logarithmic-space or PPT certificate is never tried on a polynomial-time goal. Looking up a named routine before unfolding its body keeps clients abstract and controls search. The same annotation registers with `fun_prop`, reusing an existing registration when present; parameterized `IsPPT` certificates are normalized to `IsPPTOn` for the shared encoded-input interface.

[`polytime`](../../CslibFrontier/Tactic/PolyTime.lean) combines these certificates with `fun_prop` composition and the Aesop `PolyTime` rules. On efficiency goals, Aesop's normalization pass disables `dsimp`, projection reduction, and `match`/`let` unfolding until named certificates, local calls, `fun_prop`, and composition rules have tried (while side premises normalize as usual, and full `simp_all` on efficiency goals remains available at lower priority); this preserves reducible `abbrev` wrappers and projection heads for certificate argument inference. Loops use Hoare-style iteration theorems plus bounds on state growth and iteration count. A bounded number of calls to individually efficient routines is insufficient if intermediate data grows exponentially; the growth hypotheses are part of the proof obligation. Ordinary search failure can expose a failed compositional attempt as a diagnostic, not as evidence of noncomputability.

Before searching, `polytime` and `ppt` prepare the goal the same way. `polytime [f, g]` (or
`ppt [f, g]`) unfolds the definitions `f` and `g` in the goal and inlines the `let`s this exposes;
use it for a program defined in the same module, instead of a separate `unfold`. Both forms also
replace local encoding `let`s, such as `let EIn := encPair encUnary encBits`, by their values, and
add the certificates stored in fields of local structures as local facts: a scheme `S` contributes
fields such as `S.encrypt_ppt`, an admissibility hypothesis `hA` its stage certificates. A hint
that does not occur in the goal is an error. The checked
[client](../../CslibFrontierTests/OraclePPTTactic.lean) shows each step.

When either tactic fails without a timeout, its error can name one subterm that a compositional
attempt could not certify. Both tactics decide once per file which imported rules plain search
may use, so only the first call in a file pays for that; a heartbeat budget on one call covers it
only if that proof is elaborated first. `[local irreducible]` on an imported definition that is
not `Prop`-valued, such as an encoding, makes each call in its scope decide again: slower, with
the same results. The [checked controls](../../CslibFrontierTests/PolyTimeRuleClassCache.lean)
cover local registrations and both reducibility cases.

Plain and internal tidy predicates have separate search rules at this snapshot. The preferred plain tactic does not change the user's goal to tidy computability or silently restate hypotheses. Machine-level proofs may still use tidy witnesses internally. This is the implemented direction even where older prose or issues describe a stronger prohibition on tidy use inside proofs.

Import [`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Captured.lean) for shared-input plain composition rules (`CslibFrontier.Tactic.PolyTime` does not import it). It registers `fun_prop` rules for `_root_.cond`, `List.take` and `List.drop` (requiring `encUnary` count premises), `List.head?`, `List.headD`, `List.count` (returning its count in `encUnary`), and fixed-list `List.any` (`anyConst`, whose fixed list needs no index encoding). Rules whose result encoding hides an element encoding (`listHead?WithInput`, `listHeadDWithInput`, `countWithInput`) also carry `program_certificate hlist` so `polytime` infers the element encoding from the `encList E` list premise before checking element arguments or outer projections. Binary remainder `ComputableInPolyTime.binary_mod'` on `encNat` stays explicit alongside `binary_div'` so `HMod.hMod` automation on `encUnary` remains unambiguous; see the complete checked client [`PolyTimeCaptured.lean`](../../CslibFrontierTests/PolyTimeCaptured.lean).

## Rewrite option matches before resource automation

Import `CslibFrontier.Tactic.OptionMatch` to use `option_match_to_elim`. For a
`ComputableInO` goal, also import
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option`; that module
registers `ComputableInO.optionElimWithInput` with `fun_prop`. The
[complete checked client](../../CslibFrontierTests/OptionMatch.lean) gives both imports, local
context and an example with explicit time and space bounds.

Unfold a local wrapper to expose its option match, run `option_match_to_elim`, then use
`fun_prop` to assemble the available certificates. The tactic rewrites the goal to
`Option.elim` using a checked equality proof; it does not prove the branch computations
efficient. In the quantitative client, `ComputableInO.mono` leaves separate time and space
comparisons, discharged from the encodings. Supply missing callback certificates and prove
those remaining inequalities. The migrated
[checker proof](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Counting/Checker.lean),
`computableInPolyTime_binaryStep`, demonstrates the same route for a named wrapper.

The rewrite supports non-dependent two-way option matches, including nested occurrences,
occurrences under binders and either alternative order. It rewrites `Option.bind` directly;
unfold `Option.map` or `Option.any` first to expose their matches. An option payload need
not have an inhabitant for the quantitative elimination rule.

Dependent matches, general matches on multiple discriminants and alternatives that destructure
a payload, such as `some (a, b)`, are left unchanged. The diagnostic
`option_match_to_elim: no option match in the goal` means no supported occurrence was
rewritten. Check that the wrapper is unfolded and the pattern is supported. For the remaining
cases, use explicit case analysis or an elimination lemma, then apply the appropriate
certificates and bounds. Rewriting alone does not supply a missing resource certificate.

## Other resource predicates

| Tactic/interface | Input contract and strategy | Boundary |
|---|---|---|
| [`logspace`](../../CslibFrontier/Tactic/LogSpace.lean) | Named certificates, recomputation-based composition, bounded output vectors and loop rules | Arbitrarily long intermediate output cannot simply be retained in logarithmic workspace |
| [`ppt`](../../CslibFrontier/Tactic/PPT.lean) | Closed strict fair-coin (`IsPPTOn`, `IsPPT`) and strict oracle (`IsOraclePPTOn`, `IsOraclePPT`) certificates by Aesop search (`[PPT, PolyTime]` and `[OraclePPT, PPT, PolyTime]` with `simp` disabled on oracle goals), tuple routine-call preparation, plain conditional guards (`cond'`, `ite'`), charged reply prefixes (`query_take'`), sequencing, captured maps, closed sampling and bounded-growth `OracleComp.iterate` loops | Arbitrary ideal PMFs need realization theorems; uncharged raw `ProbOracleComp.query` calls are rejected; handler substitution (`run_interpret_preprocess'`) and general loop invariants (`iterate_spec'`, `iterateWith_spec'`) keep their explicit rules |

This is a family of focused proof tools, not one universal automatic complexity analyzer. Their common interface makes reusable algorithms easier to recognize without conflating the predicates they prove.

## Execute word-RAM code

Two tactics run structured word-RAM programs (`Cslib.WordRAM.Code`) in proofs. `ram_eval`
evaluates a whole run; `wram_exec` steps through the straight-line parts of a correctness proof
and leaves the rest to specifications.

Import `CslibFrontier.Computability.WordRAM.Notation` and `open Cslib.WordRAM` to use `ram_eval`;
like the `ram[ … ]` notation, it is scoped. On a goal `ExecWithin w c x y T` or `Exec w c x y T`
it runs the interpreter `Code.eval` with `simp` and closes the goal when the run reaches `y`
within `T` instructions, or exactly `T` for `Exec`. The data `x` may be arbitrary as long as
`simp` decides every condition the run tests. With `y` a metavariable, as after
`refine ⟨?y, ?run, ?post⟩`, it computes `y`. `ram_eval n` allows each loop `n` iterations, and the
default `0` suits loop-free code. Pass programs given by name and facts about the data as simp
lemmas, as in `ram_eval 3 [count]`. Fitting conditions are decided by `omega` from the `Fits`
hypotheses in context, as described [below](#close-word-size-bounds). `ram_exact_eval`, in
`CslibFrontier.Computability.WordRAM.ExactNotation`, does the same over the exact basis, and
uses its simp lemmas to show that subtractions do not go below zero and that divisors are
nonzero. The [interpreter clients](../../CslibFrontierTests/WordRAM.lean) run straight-line code
on arbitrary data and at a symbolic word size, a counting loop with three iterations, and a
renamed program.

Import `CslibFrontier.Computability.WordRAM.SymbolicExec` to use `wram_exec` when a run reaches
loops, random samples or subprograms that need their own specifications, or branches on facts
`simp` cannot decide. On `WP w c x Q`, `∃ y, ExecWithin w c x y T ∧ P y` or their exact
forms, it executes data instructions and conditionals and leaves the postcondition at the data
reached. It stops at a loop, a random sample or a program given by name and leaves `WP w c' y Q'`:
continue with `refine WP.of_execWithin h ?_` from a specification `h` of `c'` (with
`refine WP.Exact.of_exec h ?_` on an exact goal), or with `wram_call`, then run `wram_exec`
again. A conditional the facts do not decide splits into goals tagged `pos` and `neg`;
`wram_exec -split` stops there instead. `wram_simp` simplifies register
and memory reads in the remaining postcondition, and `wram_bounded` proves `y.Bounded w` for data
built by writes from bounded data, leaving the fitting conditions it cannot prove. The
[symbolic-execution clients](../../CslibFrontierTests/WordRAMSymbolicExec.lean) check each step
and the diagnostics for a goal of the wrong form, a value that cannot be evaluated and a program
with nothing to execute. Calls, register renaming and memory frames are covered in
[routine calls](../algorithms-and-memory/wordram-and-bridges.md#proving-routine-calls-and-memory-frames).

If `ram_eval` does not close its goal, its error names the failing step: a goal of neither form,
a program `simp` cannot evaluate, a run that returns `none`, an undecided condition or an
instruction bound that `omega` cannot prove, showing the last two. Check that every program given
by name is among its simp lemmas, that `n` covers the iterations of every loop, and that the simp
lemmas decide each condition the run tests: pass a hypothesis such as `h : x.regs i < x.regs j`
explicitly, as in `ram_eval [p, h]`, because its `simp` call does not read hypotheses from the
context. Fitting conditions are decided from the `Fits` hypotheses in context. A loop with a
symbolic iteration count needs an invariant, such as `ExecWithin.loop_count` in the
[counting-loop chapter](../algorithms-and-memory/wordram-and-bridges.md#proving-a-constant-cost-counting-loop),
not a larger `n`.

The two tactics' fixed lemmas form the simp sets `ram_eval_simps` and `ram_exact_eval_simps`,
which [`Notation`](../../CslibFrontier/Computability/WordRAM/Notation.lean) and
[`ExactNotation`](../../CslibFrontier/Computability/WordRAM/ExactNotation.lean) fill and index
once with `ram_eval_simp_set_for`, so a call no longer elaborates the list. Do not tag a lemma
with either attribute, because that changes every call; pass it as a simp lemma of the call
instead. To change the shared lemmas, edit the `ram_eval_simp_set_for` macro in `Notation`; to
change a basis's lemmas, edit its `ram_eval_simp_set_for` command. The
[equivalence test](../../CslibFrontierTests/WordRAMEvalSimpSet.lean) then fails until its copy of
the old literal list is updated to match, and the
[pinned budget](../../CslibFrontierTests/AutomationRamEval.lean) catches a return of the per-call
cost.

## Certify and reuse memory methods

Import `CslibFrontier.Tactic.Realize` for a memory-client goal
`Realizes B p input output safe work`. Activate `realize` inside `Cslib.WordRAM`, with
`open Cslib.WordRAM`, or with `open scoped Cslib.WordRAM`. Importing the module alone leaves
the syntax inactive; a command-local open ends with that declaration. Open the complete
[scope clients](../../CslibFrontierTests/WordRAMRealizeScope.lean) for both activation forms and
the check that local opens do not leak into later declarations.

Place a callee's zero-local-work `Realizes` certificate in the local context to reuse an opaque
method before unfolding it. The tactic checks its basis and output encoding and uses existing
`Realizes.reindex` to wire encoded argument coordinates to live words. When some coordinates
need computation, it first certifies a charged `pure` stage for the whole argument using the
callee's input encoding, then wires the call to those new words. This supports custom and
dependent input encodings without a `WordEncoding` instance for the argument type. The
complete [method-call clients](../../CslibFrontierTests/WordRAMRealizationCall.lean) cover
projections, aliased inputs, curried and dependent arguments, and optional-pair replies.
Word-vector type abbreviations in the callee's input and output encodings are accepted without
restating their literal `Fin` widths; the [encoding-alias clients](../../CslibFrontierTests/WordRAMRealizeAliases.lean)
include a nine-word input, six-word result and empty-vector methods.
Certificates are tried in context order; this does not search for a runtime bound.
Zero local work is an absorbed grading: the callee still has its certified native allowance
against memory charge. It does not mean zero machine instructions.

The called method's domain must hold at the memory actually reached by earlier queries.
The call client after a write demonstrates that obligation explicitly. Write computed arguments
directly, such as `method (d + 1)`: `realize` leaves the result's `Fits w (d + 1)` obligation and
the method's domain as goals. Exact subtraction and division retain their definedness conditions.
The same file checks automatic and explicit staging, dependent arguments, standard-basis
truncated subtraction, and rejection when fit or exact-operation evidence is missing.
Automatic staging computes the whole encoded argument when any coordinate needs computation;
an explicit `pure` stage remains useful to share a computed value between several calls.

Ordinary `if` guards accept natural-word `=`, `≠`, `<`, `≤`, `>` and `≥`, and negations of
these comparisons. Write `if a ≤ b then ... else ...` directly: the tactic reverses a strict
test and swaps alternatives, charging the existing branch without computing `b + 1`. An
operand actually written as `b + 1` still needs its usual fit proof. The complete
[guard clients](../../CslibFrontierTests/WordRAMRealizeGuards.lean) check equal and maximal
fitting words, selected-path safety and native execution of the migrated QuotientFilter query
scan step with a maximal cutoff. From the repository root, run:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMRealizeGuards
```

Use nested branches for compound tests. Loop guards keep their existing grammar: `=`, `<`,
`>` and `≠ 0`; this branch support does not extend the loop guard rules.

Returned choices can also stay inside `pure`, including tuple and option components:
`pure (min a b, max a b)` and `pure (decide (a = 0))` need no separate source program with
branches around the returns. `realize` transports checked equalities through the returned
value, then uses the existing native branch rules. Branch instructions are charged, and only
the selected alternative requires its fit and exact-operation definedness proofs. Computing a
comparison operand still requires that operand to fit before the test. Values fixed before
runtime or already supplied by the input encoding retain their existing constant or live-word
rules. Min/max selection uses the input words directly, so the largest fitting word needs no
fitting successor. The complete
[conditional-result clients](../../CslibFrontierTests/WordRAMRealizeValues.lean) check these cases,
inactive exact division/subtraction, rejected missing premises, and frontier-bounded
certificates. Check them from the repository root with
`scripts/build.sh --wfail --iofail CslibFrontierTests.WordRAMRealizeValues`.

If `realize` is unavailable, check scope activation. If a method call is unsupported, check the
certificate's basis, output encoding, zero local work and whether its argument coordinates use
supported word glue, then inspect the domain at the reached memory. Retain the fit and safety
obligations left by the tactic;
unfolding the method or dropping a resource premise does not supply those proofs. The
[realization reference](../algorithms-and-memory/memory-specifications.md) explains the uniform
code and charging contract; the complete clients above supply imports and local context.

## Circuit construction

[`synthesis_step`](../../CslibFrontier/Tactic/Synthesis.lean) applies an explicitly supplied synthesis rule and locates its required wires among available values. `Synthesis.Builder` retains earlier wires and accumulates certified cost. Membership search itself adds no gates. Reusing a computed value preserves sharing; invoking a new construction charges its bound. A final budget check verifies the chosen construction fits the target, but does not search globally for an optimal circuit.

`synthesis_available` is that membership search on its own: it proves that a function is among the available wires, through the unions, ranges and indexed unions a builder's wire set is made of, and fails rather than adding a gate when it is not. The [worked example](../workflows/finding-results.md#build-a-shared-boolean-circuit) uses it for every gate input and for the selected outputs. It first tries `synthesis_union`, which matches the wires against the members of a union `A₀ ∪ T₁ ∪ ⋯ ∪ Tₖ`, the shape a chain of `Synthesis.extend` steps produces, syntactically or through a local hypothesis and without unfolding any definition. Only when that fails does it compare wire functions at default transparency, which can unfold word operations on wire families of equal width. A proof over a long chain can call `synthesis_union` directly, as [Karatsuba](../../CslibFrontier/Computability/Circuit/Boolean/Karatsuba.lean) does.

This contract answers a recurrent concern in the transcript: removing proof bookkeeping must not silently introduce gates. The [circuit case study](../history/case-studies.md) connects that concern to PR #520 and to the subsequent decision not to pursue general budget-guided synthesis in that session. The present tactic source is the authority for its current capabilities.

## Logical descriptions

[`FirstOrder.lean`](../../CslibFrontier/Tactic/FirstOrder.lean) provides `fo_qf`, `fo_iso_closed`, `fo_simp` and `fo_reduction`. They separate syntactic obligations and structural semantic rewrites from the mathematical proof that a reduction expresses the intended property. High-level composition lemmas avoid expanding every pullback into raw syntax.

[`FOOperator.lean`](../../CslibFrontier/Tactic/FOOperator.lean) similarly synthesizes a single uniform formula for a family through `fo_definable`, with `fo_wf` handling supported well-formedness/positivity obligations. This does not mean a different formula may be selected separately for each structure. Fixed-point operators, positivity and interpretation legality remain mathematical constraints. The [logic survey](../circuits-logic-and-other-models/index.md) records the distinction between interpretation, quantifier-free reduction and projection.

## Close encoded-length arithmetic

Import `CslibFrontier.Tactic.EncLen` and use `enc_len` to expand standard encoded lengths
(pairs, frames, unary numbers, raw bit lists, Booleans, options, sums, and `nil`/`cons` of
`encList`) with a fixed `simp only` list, then close the resulting arithmetic with `omega`. The
complete [checked clients](../../CslibFrontierTests/EncLenTactic.lean) cover nested and variable
pairs, leaf encodings, framed list constructors, local encodings, locations, scaling facts and
diagnostics. This proves encoding arithmetic; it does not construct a computation or resource
certificate.

By default only the current goal is expanded. Supply a local encoding lemma explicitly with
`enc_len [eFoo_apply]`. Use `enc_len at h ⊢` to expand one hypothesis and the goal, or `enc_len at *`
when expansion of every hypothesis is useful. Each call handles its original goal: if expansion
closes it, unrelated sibling goals remain for the caller. The checked multi-goal client exercises
that case without bullets or `<;>`.

Variable products remain atoms for `omega`. Supply a scaling fact, such as
`Nat.mul_le_mul_left k h`, before the final call; expanding a product's factors does not prove
its monotonicity. Prefer the selective location form when hypotheses already state bounds in
the encoding's original form.

If nothing expands, the diagnostic recommends plain `omega`. If the expanded goal remains,
inspect its bounds, supply missing arithmetic facts or name a local encoding lemma. An unknown
lemma reports the underlying name-resolution error; check its spelling, namespace and import.
The tactic neither invents a growth bound nor searches for an encoding definition to unfold.

## Close negligibility bounds

Asymptotic security theorems finish by showing that a concrete advantage or failure bound is
`Cslib.Crypto.Negligible`. Import `CslibFrontier.Tactic.Negligible` and close such a goal with
`negligible`, `negligible using hle` or `negligible eventually hle` instead of restating a real
upper bound as an `ℝ≥0` mirror expression and threading `negligible_of_le`, `NNReal.coe_*` and
`Pi.add_apply` by hand. The [checked clients](../../CslibFrontierTests/NegligibleTactic.lean) cover
dyadic reciprocals, polynomial and birthday numerators, parameter shifts and scalings, square roots,
geometric terms, range sums, local `let` definitions, unary `ComputableInPolyTime` certificates,
`ℝ≥0` and `ℝ` upper bounds, and failure diagnostics. To check them, run
`lake build CslibFrontierTests.NegligibleTactic --wfail --iofail` from the repository root after
[setup](../workflows/getting-started.md).

Plain `negligible` normalizes pointwise `Pi` operations, unit fractions `1 / x` and natural-number
casts, derives `PolynomiallyBounded` facts from local `ℕ → ℕ` `let` bindings and unary
`ComputableInPolyTime f encUnary encUnary` hypotheses in context, and runs `fun_prop` with
`norm_num`, `positivity` and `omega` on side conditions. Through the closure rules in
`CslibFrontier.Crypto.Negligible.Dyadic`, it handles `((2 : ℝ≥0) ^ n)⁻¹`, `(1 : ℝ≥0) / 2 ^ n`,
polynomial and birthday ratios such as `(Q n : ℝ≥0) ^ 2 / (2 * 2 ^ n)` and
`((Q n).choose 2 : ℝ≥0) / 2 ^ n`, constant scaling and division, `NNReal.sqrt`, geometric powers
`ratio ^ n` with `ratio < 1`, parameter schedules (`ε (n + c)`, `ε (c + n)`, `ε (c * n)` and
`ε (n / c)` for `0 < c`), and uniform `Finset.range (Q n)` sums.

When the quantitative step gives an inequality rather than a syntactic expression in the goal, pass
it directly with `negligible using hle` for a pointwise bound `∀ n, …` or
`negligible eventually hle` for an asymptotic bound `∀ᶠ n in Filter.atTop, …`. Both forms accept
bounds in `ℝ≥0` (`f n ≤ B n`) and in `ℝ` (`(f n : ℝ) ≤ B n`, including `.toReal` bounds on
`Game.succProbability`). On a real bound, the tactic applies `negligible_of_coe_le` or
`negligible_of_eventually_coe_le` and pushes `Real.toNNReal` structurally across sums, products,
quotients, reciprocals, natural powers, `Real.sqrt`, `Finset.sum` and casts before invoking
`fun_prop`.

If the target is not `Cslib.Crypto.Negligible f`, the diagnostic reports the unexpected goal. If
`using` or `eventually` cannot match `hle` as an `ℝ≥0` or `ℝ` upper bound on `f`, it reports the
expected inequality shape. If `fun_prop` cannot discharge the resulting `ℝ≥0` bound, the diagnostic
displays the normalized residual `Negligible` goal; supply the missing `Negligible` or
`PolynomiallyBounded` fact in context, or bound an indexed sum first with
`Negligible.sum_range_of_le`. The tactic discharges asymptotic decay from a proved quantitative
bound; it does not perform game hops or probability rewrites itself.

## Close word-size bounds

Word-RAM instructions need a fitting condition `Fits w v`, which unfolds to `v < 2 ^ w`, for
each value they write. Import `CslibFrontier.Tactic.Fits` and prove such a condition with `fits`
instead of choosing a larger fact `h` and writing `h.of_le (by omega)`. The tactic unfolds `Fits`
in the goal and in the hypotheses that mention it, adds that each power of two `2 ^ e` among them
is positive, and runs `omega`. It finds the hypotheses by their statements, so it does not depend
on their names, and the goal may also be written `v < 2 ^ w`. The
[checked clients](../../CslibFrontierTests/FitsTactic.lean) cover offsets, constants, masks, shifts,
a wider word, conjunctions and negations of fitting facts, a product bound and both diagnostics.
To check them, run `lake build CslibFrontierTests.FitsTactic --wfail --iofail` from the repository
root after [setup](../workflows/getting-started.md).

`ram_eval` and `ram_exact_eval` decide the fitting conditions of the values they write the same
way, with the simplification procedure `Cslib.WordRAM.reduceFits`. It uses only the hypotheses
that mention `Fits`, and at most 16 of them; past that it only matches a hypothesis of the same
statement. A value that fits by a larger fitting fact in context therefore needs no named
`Fits` statement among their simp lemmas. These tactics' modules import `CslibFrontier.Tactic.Fits`,
so their clients can call `fits` without importing it.

A side condition used once can be proved where it is used, as the argument `(by fits)`. Products
are atoms for `omega`: give a bound on one as a term, as in
`fits [Nat.mul_le_mul_right b hc]`. A hypothesis about a different word width is related to `w`
only when `omega` can see it, as for `w + 1`; otherwise weaken it first with `Fits.mono`.

If the goal is not a word-size bound `Fits w v` or `v < 2 ^ w`, the diagnostic recommends plain
`omega`.
If `omega` fails, the diagnostic shows the unfolded goal with the facts it was given; supply the
missing bound, for instance on a product or on a value read from memory.

## Reorder independent samples

Two experiments that draw the same independent samples in different orders have the same law.
Import `CslibFrontier.Tactic.PMFSwap` and, after `simp only [pmf_norm]`, prove the equation with
`pmf_swap`. It matches the samples of the two sides by their distributions, not their positions,
moves them to the front with `PMF.bind_comm` and strips them. It closes the goal when the remaining
continuations agree up to reducible unfolding, trying the matches of repeated distributions; `simp
[PMF.bind_comm]` instead loops on two samples of one distribution. That search has a budget of 256
steps, renewed after stripping each sample whose distribution occurs once on each side. When it
runs out, `pmf_swap` fails rather than guess an order: many samples of one distribution, such as
six drawn in reverse order, exceed it. Then strip or reorder some samples first. If no order makes
the sides agree, it strips the common samples, first those whose distribution occurs once on each
side, and leaves the equation of the continuations, or closes it when `rfl` proves it.
`pmf_swap with x y` skips the search, strips exactly two samples the same way and names them in
the order they occur in the right side, whichever is stripped first; it leaves the remaining
equation as it is.

Samples may also move past a sampler `F` that takes a continuation, such as
`Game.runStatelessOracle o prog`, when `pmf_swap [h]` is given a commutation lemma
`h : μ.bind (fun b => F (k b)) = F (fun a => μ.bind fun b => k b a)` that holds for every
distribution `μ`, as `Game.bind_runStatelessOracle_comm` does. A lemma of another form is
rejected with the expected form, and two samplers do not move past each other.

When both sides draw the same distributions and differ only in what they return, the goal does
not determine which sample to strip. Choose it with `pmf_hoist q`, which moves the samples of `q`
toward the front of their chains anywhere in the goal, or in a hypothesis with `at h`, then strip
it with `congr 1 with x : 1`. When a chain draws `q` twice, `pmf_hoist (occ := n) q` moves only
its `n`th independent sample, counting along each chain and through the chains in order, the left
side of an equation first. A sample whose distribution mentions an earlier sample never moves past
it; the diagnostic lists the samples of both sides and marks those dependencies. The
[checked clients](../../CslibFrontierTests/PMFSwap.lean) cover each form and diagnostic.

## Step game hops and align shared random draws

Import `CslibFrontier.Tactic.GameHop` to step cryptographic hybrid arguments without repeating
`Game.advantage_triangle`, `Game.advantage_comm`, `NNReal.coe_le_coe`, or nested
`Game.advantage_bind_le_of_support` boilerplate. Both tactics keep intermediate games and variable
couplings explicit in the proof script and perform no backtracking search. The complete
[checked clients](../../CslibFrontierTests/GameHopTactic.lean) exercise every supported goal shape
and pin the user-facing error for each rejected input they cover; run
`lake build CslibFrontierTests.GameHopTactic --wfail --iofail` from the repository root after
[setup](../workflows/getting-started.md). Representative library proofs using them include the
[Cramer–Shoup 1CCA hops](../../CslibFrontier/Crypto/Computational/CramerShoup.lean),
[Cramer–Shoup adaptive rejection](../../CslibFrontier/Crypto/Computational/CramerShoup/Scheme.lean),
and
[Naor–Reingold security](../../CslibFrontier/Crypto/Computational/NaorReingold/Security.lean).

Use `game_trans [g₁, g₂, ...]` (or `game_trans g₁, g₂, ...`) on goals of the form
`Game.advantage G₀ Gₖ ≤ B` (`ℝ≥0`), `(Game.advantage G₀ Gₖ : ℝ) ≤ B` (`ℝ`),
`Encryption.advantage exp n ≤ B`, `Game.succProbability G₀ ≤ Game.succProbability Gₖ + B` (in
`ℝ≥0` or `ℝ`, in either addition order), one-sided `Game.succProbability G₀ ≤ B` (in `ℝ≥0` or
`ℝ`, hopping from `G₀` to `PMF.pure false`), or `CloseTo μ₀ μₖ B` (`ℝ≥0∞`). It creates one hop
subgoal per adjacent pair followed by a trailing bound subgoal `?ε₀ + ... + ?εₘ ≤ B`. Passing
`using [h₀, h₁, ...]` discharges hops directly (use `_` to leave a hop open for tactic proof),
automatically orienting reversed `Game.advantage_comm` and `CloseTo.symm` bounds, accepting
`Game.succProbability x ≤ ε` proofs on `PMF.pure false` endpoints, lifting `ℝ≥0` bounds into `ℝ`,
turning game equalities `A = B` or `B = A` into zero error, and closing a fully instantiated sum
bound when it holds by `rfl`, symmetric `Game.advantage_comm` summand alignment,
associativity/commutativity of `+` (with zeros), or `ring`. With no intermediate list,
`game_trans` unfolds `Encryption.advantage` or reduces a `Game.succProbability` bound to
`Game.advantage`, and `game_trans using [h]` closes a single hop up to symmetry. For finite-support `dist μ ν ≤ ε` bounds with `ε : ℝ`, import
`CslibFrontier.Crypto.Game.CloseTo.Statistical` and apply `Cslib.Interactive.closeTo_of_dist_le_ofReal`
to obtain `CloseTo μ ν (ENNReal.ofReal ε)` directly without a separate nonnegativity proof; see the
[Lyubashevsky commitment binding proof](../../CslibFrontier/Crypto/Protocols/SigmaProtocol/Lyubashevsky/Commitment.lean).

Use `peel_binds` (or `peel_binds x₁ x₂ ...`) on `Game.advantage`, `Encryption.advantage`,
`CloseTo`, or `PMF` equality goals. It first normalizes outer `ProbComp.eval` monadic binds,
`PMF` monad notation, and left-nested `PMF.bind_bind` at the root without unfolding named
experiment definitions, then peels shared leading `PMF.bind` and `Game.runStatelessOracle` stages.
Each peeled stage introduces the draw `xᵢ` and its support witness `xᵢ_mem : xᵢ ∈ μ.support`
(`_` names the draw `x` and leaves the witness inaccessible). When the two leading distributions are not definitionally equal,
`peel_binds` checks whether either side's second stage is independent of its first and matches the
opposite leading stage, applying one `PMF.bind_comm`, `Game.bind_runStatelessOracle_comm`, or
`Game.runStatelessOracle_comm` swap automatically before peeling. Omitting binder names peels all
shared leading stages and retains the existing lambda binder names.

Intermediate hybrid games and multi-step couplings across identical distributions (such as
reordering uniform draws over `ZMod q`) remain explicit choices: `peel_binds` couples identical
leading distributions in place rather than guessing from bound variable names, so unfold named game
wrappers and perform any deeper `PMF.bind_comm` / `Game.advantage_bind_comm` reordering before
peeling. For a `PMF.bind` chain, `pmf_hoist q` from
[Reorder independent samples](#reorder-independent-samples) moves the samples of `q` to the front
first. When a trailing sum bound needs cast rewriting or monotonicity (such as `push_cast; ring`
or `gcongr`), `game_trans` leaves that single ground inequality open.

If `peel_binds` reports that leading stages do not match and cannot be aligned by a single
independent swap, check whether an inner draw mentions the outer binder or lies more than one stage
deep, or apply a distribution-replacement lemma (such as modular-sampling or until-bad bounds)
before peeling the remaining prefix. If `game_trans` reports a `using` count mismatch, check that
`m` intermediate items are paired with `m + 1` hop proofs (using `_` for hops proved
interactively); if it reports that a hop proof's type does not match the expected hop, verify the
intermediate game list order and parameter arguments.

## Step through counter programs

A reachability proof for a counter program (`Turing.CounterProgram.Reaches`) goes through its
instructions one at a time. Import
`CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Step` and
take each step with `cp_step` instead of `refine Reaches.assign h hB ?_` followed by
`simp only [eval_add, eval_reg, …]`. The tactic reads the instruction at the current label from a
hypothesis `P.instr l = i`, or by evaluation when the program is concrete. It applies the rule of
that instruction: assignment, comparison or read, plus the oblivious and shifted rules when
`CounterProgram.AllBranches` or `CounterProgram.Block` is imported. It proves the register bound
from a hypothesis and simplifies the next configuration with the simp set `cp_simps`. Pass the
values of the registers read and the input bit read as simp lemmas, as in `cp_step [h0, hw]`.
The goal closes when the configuration reached is the target or a hypothesis. The
[checked clients](../../CslibFrontierTests/CounterProgramStep.lean) cover running, oblivious and
shifted steps, a concrete program, conditional labels and the diagnostics. The shape check of the
[logspace model checker](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/FirstOrder.lean)
is a library client.

A conditional label `if c then l₁ else l₂` is decided when `c` or its negation is a hypothesis
or, for a comparison of numbers, follows from the hypotheses by `omega`: a hypothesis `hn : 2 ≤ n`
decides `if n < 2 then F else E` without passing `Nat.not_lt.mpr hn`. This applies to the label
before a step, and after a step to the label of either configuration when the other's label is
one of its branches; the decided label stays even when the goal does not then close. A fact
stated about expressions that `cp_simps` would evaluate first, such as
`(const 0).eval regs < e.eval regs ↔ us ≠ zs`, applies only before that simplification: pass it
as `cp_step [↓h]`. A label still undecided, or a `match` on an input bit the lemmas do not give,
stops the tactic with a diagnostic. Split into cases first, as in
`by_cases h : regs.getD 0 0 < 3`, after which `cp_step` decides the label in each case; for the
bit read, pass `w[i]? = some b` as a simp lemma.

A side condition the tactic cannot prove, typically a register bound that is not a hypothesis but
part of an invariant, is named in the error; state it with `have` first, as in
`have hB := hk.2.2`. For a step followed by a reachability fact `hrest`
from a lemma, leave the step as a goal with `refine Reaches.trans ?_ hrest` and close it by
`cp_step`; the oblivious steps of the
[counting loop](../../CslibFrontier/Computability/Complexity/Classes/LogSpace/FirstOrder/TransitiveClosure/Counting.lean)
are written this way.

## Proof style as interface maintenance

The project asks for nonterminal `simp only` where later steps depend on the resulting normal form, forbids global simplification attributes on machine transitions, and requires comments and reviewed allowlisting for unusually large heartbeat bounds. These policies address predictable search explosions and fragile proofs. They complement semantic lemmas and named certificates; they do not prove maintainability by themselves. [Proof hygiene](../../AGENTS.md#proof-hygiene)

Readable `do` notation, named intermediate circuit values and named state fields are recurring client-facing priorities. Inspect representative source clients and before/after PRs to assess these benefits; a raw tactic count does not demonstrate usability. The historical study does not measure an automation success rate: such a rate would need a denominator of attempted goals, failures, manual repairs and timeouts.

[complexitylib]: ../sources.md#complexitylib
