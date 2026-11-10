# Proof automation and client interfaces

The automation layer searches for proofs of explicit mathematical contracts. It generally reuses named certificates and compositional rules; it is not a compiler that can assign a polynomial bound to an arbitrary Lean program. In particular, a short tactic call hides a checked derivation, but the model, algorithm and invariant still have to be right. [cslib-frontier][complexitylib]

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

[`program_certificate`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PolyTime/Init.lean#L17) indexes a theorem by its efficiency predicate and the head constant of its program, with an encoding flag. The predicate index prevents a RAM certificate from accidentally solving a Turing-machine goal. Looking up a named routine before unfolding its body keeps clients abstract and controls search. The same annotation registers with `fun_prop`, reusing an existing registration when present; parameterized `IsPPT` certificates are normalized to `IsPPTOn` for the shared encoded-input interface.

[`polytime`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PolyTime.lean#L25) combines these certificates with `fun_prop` composition and the Aesop `PolyTime` rules. Loops use Hoare-style iteration theorems plus bounds on state growth and iteration count. A bounded number of calls to individually efficient routines is insufficient if intermediate data grows exponentially; the growth hypotheses are part of the proof obligation. Ordinary search failure can expose a failed compositional attempt as a diagnostic, not as evidence of noncomputability.

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
| [`logspace`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/LogSpace.lean#L15) | Named certificates, recomputation-based composition, bounded output vectors and loop rules | Arbitrarily long intermediate output cannot simply be retained in logarithmic workspace |
| [`ppt`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/PPT.lean#L18) | Closed strict fair-coin program certificates, deterministic calls, supported sampling, bounded-growth iteration; strict oracle programs (`IsOraclePPTOn`, `IsOraclePPT`) by plain `fun_prop` composition of charged reply prefixes, sequencing, maps, conditionals and sampling | Arbitrary ideal PMFs need realization theorems; handler substitution and adaptive oracle loops keep their explicit rules, whose invariants and growth bounds are part of the claim |
| [`stateful`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/Stateful.lean#L14) | Local semantic/operation-cost Hoare contracts and Aesop rules | Intermediate assertions and implementations for bind/link are supplied explicitly; total machine time remains separate |
| [`wordram`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/WordRAM.lean#L16) | Registered controller/refinement and polynomial-time certificates | Width, basis and fixed-code realization matter; host-language continuation work is not automatically free |

This is a family of focused proof tools, not one universal automatic complexity analyzer. Their common interface makes reusable algorithms easier to recognize without conflating the predicates they prove.

## Certify and reuse memory methods

Import `CslibFrontier.Tactic.Realize` for a memory-client goal
`Realizes B p input output safe work`. Activate `realize` inside `Cslib.WordRAM`, with
`open Cslib.WordRAM`, or with `open scoped Cslib.WordRAM`. Importing the module alone leaves
the syntax inactive; a command-local open ends with that declaration. Open the complete
[scope clients](../../CslibFrontierTests/WordRAMRealizeScope.lean) for both activation forms and
the check that local opens do not leak into later declarations.

Place a callee's zero-local-work `Realizes` certificate in the local context to reuse an opaque
method before unfolding it. The tactic checks its basis and output encoding and uses existing
`Realizes.reindex` to wire every encoded argument coordinate to an already live word. The
complete [method-call clients](../../CslibFrontierTests/WordRAMRealizationCall.lean) cover
projections, aliased inputs, curried and dependent arguments, and optional-pair replies.
Word-vector type abbreviations in the callee's input and output encodings are accepted without
restating their literal `Fin` widths; the [encoding-alias clients](../../CslibFrontierTests/WordRAMRealizeAliases.lean)
include a nine-word input, six-word result and empty-vector methods.
Certificates are tried in context order; this does not search for a runtime bound.
Zero local work is an absorbed grading: the callee still has its certified native allowance
against memory charge. It does not mean zero machine instructions.

The called method's domain must hold at the memory actually reached by earlier queries.
The call client after a write demonstrates that obligation explicitly. Computed arguments
such as `d+1` need an explicit certified `pure` stage and its fit/domain proof; they cannot be
supplied by static register wiring. The same file contrasts the rejected unstaged call with
its successful staged version and includes dependent pair/scalar staging.

If `realize` is unavailable, check scope activation. If a method call is unsupported, check the
certificate's basis, output encoding, zero local work and live input coordinates, then inspect
the domain at the reached memory. Retain the fit and safety obligations left by the tactic;
unfolding the method or dropping a resource premise does not supply those proofs. The
[realization reference](../algorithms-and-memory/memory-specifications.md) explains the uniform
code and charging contract; the complete clients above supply imports and local context.

## Circuit construction

[`synthesis_step`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/Synthesis.lean#L13) applies an explicitly supplied synthesis rule and locates its required wires among available values. `Synthesis.Builder` retains earlier wires and accumulates certified cost. Membership search itself adds no gates. Reusing a computed value preserves sharing; invoking a new construction charges its bound. A final budget check verifies the chosen construction fits the target, but does not search globally for an optimal circuit.

This contract answers a recurrent concern in the transcript: removing proof bookkeeping must not silently introduce gates. The [circuit case study](../development-history/case-studies.md) connects that concern to PR #520 and to the subsequent decision not to pursue general budget-guided synthesis in that session. The present tactic source is the authority for its current capabilities.

## Logical descriptions

[`FirstOrder.lean`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/FirstOrder.lean) provides `fo_qf`, `fo_iso_closed`, `fo_simp` and `fo_reduction`. They separate syntactic obligations and structural semantic rewrites from the mathematical proof that a reduction expresses the intended property. High-level composition lemmas avoid expanding every pullback into raw syntax.

[`FOOperator.lean`](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Tactic/FOOperator.lean#L14) similarly synthesizes a single uniform formula for a family through `fo_definable`, with `fo_wf` handling supported well-formedness/positivity obligations. This does not mean a different formula may be selected separately for each structure. Fixed-point operators, positivity and interpretation legality remain mathematical constraints. The [logic survey](../circuits-logic-and-other-models/index.md) records the distinction between interpretation, quantifier-free reduction and projection.

## Close encoded-length arithmetic

Import `CslibFrontier.Tactic.EncLen` and use `enc_len` to expand standard encoded lengths with
a fixed `simp only` list, then close the resulting arithmetic with `omega`. The complete
[checked clients](../../CslibFrontierTests/EncLenTactic.lean) cover nested and variable pairs,
leaf encodings, local encodings, locations, scaling facts and diagnostics. This proves encoding
arithmetic; it does not construct a computation or resource certificate.

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

## Proof style as interface maintenance

The project asks for nonterminal `simp only` where later steps depend on the resulting normal form, forbids global simplification attributes on machine transitions, and requires comments and reviewed allowlisting for unusually large heartbeat bounds. These policies address predictable search explosions and fragile proofs. They complement semantic lemmas and named certificates; they do not prove maintainability by themselves. [Proof hygiene](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/AGENTS.md#proof-hygiene)

Readable `do` notation, named intermediate circuit values and named state fields are recurring client-facing priorities. Inspect representative source clients and before/after PRs to assess these benefits; a raw tactic count does not demonstrate usability. The historical study does not measure an automation success rate: such a rate would need a denominator of attempted goals, failures, manual repairs and timeouts.

[complexitylib]: ../sources.md#complexitylib
