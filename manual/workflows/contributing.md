# Contribute and review

A useful contribution gives the next client a clearer theorem, construction or proof interface. Start with the intended mathematical endpoint and a representative use. For a substantial task, agree scope through an existing issue or a new issue after checking for duplicates. `ROADMAP.md` lists directions; it does not assign ownership or guarantee complete prerequisites. The authoritative [contribution process](../../CONTRIBUTING.md) governs the current checkout. [cslib-frontier][complexitylib]

## Design the statement before its proof

Specify the model, encodings, resource convention, uniformity and quantifier order. For a published result, identify the source version and locator and map those choices to the source. For a conditional or restricted milestone, state its restriction and preserve the broader objective. Assuming the difficult endpoint is not constructing it.

Model domain objects, problem instances, certificates, configurations, and multi-field algorithm contexts or states as documented `structure`s rather than tuple `abbrev`s or bare product sets, and declare field-tuple structure encodings with [`enc_structure`](choosing-models.md#write-the-contract-before-the-proof) ([structures for domain objects](../../AGENTS.md#structures-for-domain-objects-and-records)). Where ordinary pairs remain—such as generic combinators or `Instance × List Bool` verifier inputs—bind tuple components by name instead of reaching into nested tuples with chains such as `c.1.2`; CI stops a changed module from adding such chains to its public statements and definition bodies ([named components](../../CONTRIBUTING.md#library-quality-standard)). Write encodings so that readers can see them without parsing the same nested term repeatedly: name a compound encoding that recurs in a module's statements with a documented reducible `abbrev` (not a `local notation`, which CI rejects in changed modules), and keep unary versus binary and representation choices visible in names and docstrings. The [encoding rules](../../AGENTS.md#encodings-in-statements) state when a name is required.

Search CSLib, Mathlib, local modules and the in-flight work recorded in source markers and the [coordination threads](../../CONTRIBUTING.md#upstreaming). Reuse definitions that express the same mathematics. Similar names with different encodings, costs or adversary power prompt a search for a bridge, not an automatic identification of models. The [model-selection chapter](choosing-models.md) gives the questions to settle.

After building, `python3 scripts/parallel_defs.py --theorems --base origin/main` reports possible duplicate statements, including reversed equalities and built-in list lookup by a `Fin` index versus its natural value. It ignores the lookup's bounds proof while retaining the list and index. The report is advisory: a clean report does not replace the search above. Specializations, arbitrary definition unfolding and custom indexing instances are outside its [normalization contract](../../scripts/parallel_defs.py).

## Place the API and preserve its clients

Put general definitions and lemmas in the lowest suitable module imported by their consumers. Prefer a small topic module over a high-fan-out hub when both are mathematically appropriate. Keep specialized constructions with their applications. An exposed definition body is part of its interface: add `@[expose]` only when downstream proofs need it. A section-level `@[expose]` reaches only the section's `def`-kind declarations, and CI rejects a header over a section with nothing to expose. A hidden body that the module itself rewrites with `simp [f]` or `rw [f]` still reaches importers through its equation lemma; see [Public surface under the module system](../../CONTRIBUTING.md#public-surface-under-the-module-system).

Do not copy an argument from one proof into another. Before re-deriving a fact inside a proof, even a short one, search this library, CSLib, Mathlib and core for it: the library's `Nat.mul_add_div_of_lt` in [Div](../../CslibFrontier/Foundations/Data/Nat/Div.lean) and core's `Nat.mul_add_mod_of_lt` already give the quotient and remainder of `k * m + i` by `m` when `i < m`. When a proof you write needs a construction, bound or change of variables that another proof makes and nothing provides it, state it once as a lemma and use it in both, provided the lemma makes both proofs clearer; otherwise leave them. Make the lemma `private` if it is plumbing within one module; place a lemma shared across modules as the previous paragraph describes. Derive a special case, or the same result with another constant, from the general statement instead of copying and editing its proof. A routine side goal of a few lines usually stays inline: extract it only when the lemma states a fact a reader would look up by name, such as a round trip, and replaces a fragile `simpa` or a similar opaque step. A shared lemma pays when each call site can supply its hypotheses directly; one whose hypotheses restate most of what the copied block derives saves nothing. When callers of a routine keep re-deriving the same frame or invariant after each call, state the frame in the routine's specification in a form they can apply, such as a `Finset` of written registers, or prove the invariant's transfer across the call once, as a corollary of that specification. [Reuse routine postconditions and register frames](../algorithms-and-memory/memory-specifications.md#reuse-routine-postconditions-and-register-frames) shows the existing frame rules. [Library quality standard](../../CONTRIBUTING.md#library-quality-standard)

Library paths are intended to migrate from `CslibFrontier.` to `Cslib.` unchanged apart from that prefix. Documented exceptions cover general mathematics destined for Mathlib and project scaffolding. New modules use the Apache header, `module`, upstream marker, API documentation and required public import chain to `CslibFrontier.Init`/`Cslib.Init`. Use `public import` for API dependencies and ordinary `import` for proof-only dependencies. Follow the [exact file template and marker rules](../../AGENTS.md#file-rules).

Public resource statements use plain computability predicates; tidiness remains an internal machine-proof mechanism during migration. Before a supported release, renaming an interface means updating its in-repository clients and removing the superseded API, rather than adding compatibility aliases. Preserve ported files' authors and licenses and cite mathematical sources through the ordered `references.bib` keys. See [upstream coordination and credit](../design-and-assurance/upstream-and-credit.md).

Before handing off an API change, open a representative caller and inspect the work it must do
to use the result. Repeated Boolean-case analysis suggests a matcher characterization; repeated
coordinate arithmetic suggests an embedding range lemma; projection-certificate plumbing suggests
named records and the generated `enc_structure` rules. Use the improved interface in that caller
in the same change. Compare sibling implementations too: a PMF result may specialize a measure
result through an existing conversion theorem, and a game can call the handler its proof already
names. Keep one-proof representation wrappers private while retaining useful mathematical facts.
The [author and reviewer procedure](../../AGENTS.md#check-the-api-through-its-callers) describes
the checks and how to record a concise before/after example without a separate audit report.

## Validate the client, then the change

Begin with diagnostics for the changed file and a representative downstream client. For new bundled hypotheses, provide a satisfying instance; use a negative case when it exposes vacuity or a model boundary. Tests should exercise behavior or the interface rather than restate a theorem by name.

After adding a library file, run `lake exe mk_all` to regenerate the aggregate. New tests belong in `CslibFrontierTests/` and are included by a Lake glob. During development:

```bash
scripts/check.sh --quick
```

Quick mode compares against the merge base with local `origin/main` without fetching by default. It includes committed, staged, unstaged and untracked changes and builds affected modules and importing clients when supported. It runs source hygiene on the changed files and the encoding readability and projection chain ratchets on changed library modules, then the declaration linters on the affected library modules, so an argument that a change leaves unused in a client is reported before CI. A changed ratchet baseline (`scripts/encoding_readability_baseline.json` or `scripts/projection_chains_baseline.json`) runs its ratchet. A library aggregate whose only edit is the import lines `lake exe mk_all` adds for new modules keeps the quick plan, which then builds the aggregate's importing clients. Other non-Lean, unsupported or ambiguous changes, including deletions and renames, fall back to the full check; `scripts/check.sh --quick --no-full-fallback` instead reports the reason and exits with status 3. Quick success is development feedback, not full integration validation.

Quick mode also runs the changed-file lints that read only sources: an `@[expose]` section with nothing to expose, and a new test file that only restates signatures. When building targets directly instead, run them with `python3 scripts/check_changed_files.py --source-only`; CI's changed-file step additionally checks module-doc names against build outputs.

Lean, dependency or build changes need the six Lean gates on the final revision, together with the other required CI checks:

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` restores available caches and runs every required step of CI's `ci-checks` job that can run locally, with CI's commands: these gates, the Python tooling tests, source hygiene, the encoding readability and projection chain ratchets, documentation pins, and the tidy statement ratchet, result registry and changed-file lints that read the build outputs. [`scripts/full_check.py`](../../scripts/full_check.py) lists the steps and why the rest stay CI-only. After the Lean gates, it also re-elaborates built root-package sources whose outputs Lake restored from the shared local artifact cache without their warnings, including unchanged clients ([diagnosis](troubleshooting.md#diagnose-warnings-that-only-ci-reports)). A successful hosted run covering the final revision supplies this evidence without a duplicate local run. Required CI and merge-group checks still apply. Documentation-only changes need consistency, link and introduced Lean-example checks rather than a whole-library rebuild. Validation-tool changes also need direct checks of their changed behavior. [Validation policy](../../AGENTS.md#validation-sequence)

## Update and review both manuals

Before handoff, identify the reader tasks affected in both manuals. Update the relevant
workflows, model descriptions, assumptions, commands and examples in the same PR. If the
manual remains accurate, record a specific reason for it in the PR’s manual-impact assessment.
A proof-only edit preserving statements, imports and automation may need no prose change;
a changed encoding or resource bound normally does. An edit that changes the number of lines
in a file still moves the declarations below it, so repoint any manual links such as
`File.lean#L120` to them (for `[Ns.name](File.lean#Ln)` links,
`python3 scripts/check_operator_manual.py --fix-anchors` repoints unambiguous declaration
headers automatically). The checker below reports a link that no longer starts a
declaration, or whose text names a declaration of the linked file that it does not start.

Run `python3 scripts/check_operator_manual.py` from the repository root, and check changed
complete Lean clients as above. The coordinator must review both assessments and ensure independent review of affected
reader paths against the final revision. Changes to agent roles, direction, permissions or
intervention also require checking the [Agent Operator’s Manual](../AGENT_OPERATORS.md). The [maintenance procedure](../MAINTAINING.md)
sets out the human acceptance test and distinguishes live checks from dated history.

## Check the statement readers will see

Readers see the library statement itself: its module documentation, its declaration in the API documentation and any entry of the [results inventory](../../results/README.md) that lists it. When changing a named theorem's model, encoding, bound or hypotheses, update that documentation and the entry's scope note in [Entries.lean](../../CslibFrontierResults/Entries.lean). Inspect changed rendered pages and declaration links.

The axiom audit checks allowed dependencies of declarations stored in imported CslibFrontier modules. The results registry checks that each listed theorem exists, is public and is a proposition. Neither replaces reading the model and comparing it to the advertised mathematics. See [assurance](../design-and-assurance/assurance.md).

## Make the handoff reviewable

Before approval, inspect the CI **Parallel-definition**, **Duplicate-statement** and **Repeated-proof-block**
notices for the reviewed revision. Follow the source links, compare both declarations or proof
blocks, and record reuse, generalization or the concrete reason to retain both. Link existing
resolutions instead of repeating them. Skipped or incomplete scans need an explicit coverage
assessment and targeted source checks, following [the review cycle](../../AGENTS.md#review-cycle).
For local commands and matching limits, see [the tooling reference](../../CONTRIBUTING.md#ai-assistance-and-review).

Consider alternative statements, representations, invariants and proof strategies when they make
the mathematics more natural to state, prove and apply. Demonstrate the benefit on actual clients,
preserve the mathematical claim and resource bounds, and complete the cleanup affecting the
contribution before approval. Deferral requires the exceptional disposition described in
[Improving library ergonomics](../../AGENTS.md#improving-library-ergonomics).

Explain the problem, resulting behavior, limitations and validation in the PR. Link its task issue and source references, preserve contributor credit, and disclose AI tools and their role under the applicable policy. Obtain independent correctness/API review of the current revision. Reviewers read new and changed proofs against the rest of the file and nearby modules, because a diff does not show the existing proof that a new block repeats; a new copy of an argument the library already makes is a [review finding](../../AGENTS.md#review-cycle) when a shared lemma would pay under the [library quality standard](../../CONTRIBUTING.md#library-quality-standard). A reviewer who helped design or implement the change cannot supply that independence; agent review is not human approval.

After fixes, request review of the affected delta. Changed reasoning, statement semantics and uncertain conflict resolutions require fresh review; a clean rebase may sometimes preserve existing approval. Integration requires maintainer authority as well as validation and review. State what is complete and what remains. When only a milestone is delivered, keep the broader objective visible and open or explicitly disposed of.

Keep a source approval conditional while notices, rendered pages or other source questions still
need review. When releasing that hold, link the earlier proof/API/caller assessment and record
which remaining questions were resolved; reuse unchanged evidence. The queue helper's `--wait`
option queues automatically when CI passes, so finish any review of newly produced material
before starting it. Follow [Approve and queue](../../AGENTS.md#approve-and-queue).

[complexitylib]: ../sources.md#complexitylib
