# Contribute and review

A useful contribution gives the next client a clearer theorem, construction or proof interface. Start with the intended mathematical endpoint and a representative use. For a substantial task, agree scope through an existing issue or a new issue after checking for duplicates. `ROADMAP.md` lists directions; it does not assign ownership or guarantee complete prerequisites. The authoritative [contribution process](../../CONTRIBUTING.md) governs the current checkout. [cslib-frontier][complexitylib]

## Design the statement before its proof

Specify the model, encodings, resource convention, uniformity and quantifier order. For a published result, identify the source version and locator and map those choices to the source. For a conditional or restricted milestone, state its restriction and preserve the broader objective. Assuming the difficult endpoint is not constructing it.

Write encodings so that readers can see them without parsing the same nested term repeatedly: name a compound encoding that recurs in a module's statements with a documented reducible `abbrev`, keep unary versus binary and representation choices visible in names and docstrings, and declare field-tuple structure encodings with [`enc_structure`](choosing-models.md#write-the-contract-before-the-proof). The [encoding rules](../../AGENTS.md#encodings-in-statements) state when a name is required.

Search CSLib, Mathlib, local modules and the in-flight work recorded in source markers and the [coordination threads](../../CONTRIBUTING.md#upstreaming). Reuse definitions that express the same mathematics. Similar names with different encodings, costs or adversary power prompt a search for a bridge, not an automatic identification of models. The [model-selection chapter](choosing-models.md) gives the questions to settle.

## Place the API and preserve its clients

Put general definitions and lemmas in the lowest suitable module imported by their consumers. Prefer a small topic module over a high-fan-out hub when both are mathematically appropriate. Keep specialized constructions with their applications. An exposed definition body is part of its interface: add `@[expose]` only when downstream proofs need it.

Library paths are intended to migrate from `CslibFrontier.` to `Cslib.` unchanged apart from that prefix. Documented exceptions cover general mathematics destined for Mathlib and project scaffolding. New modules use the Apache header, `module`, upstream marker, API documentation and required public import chain to `CslibFrontier.Init`/`Cslib.Init`. Use `public import` for API dependencies and ordinary `import` for proof-only dependencies. Follow the [exact file template and marker rules](../../AGENTS.md#file-rules).

Public resource statements use plain computability predicates; tidiness remains an internal machine-proof mechanism during migration. Before a supported release, renaming an interface means updating its in-repository clients and removing the superseded API, rather than adding compatibility aliases. Preserve ported files' authors and licenses and cite mathematical sources through the ordered `references.bib` keys. See [upstream coordination and credit](../design-and-assurance/upstream-and-credit.md).

## Validate the client, then the change

Begin with diagnostics for the changed file and a representative downstream client. For new bundled hypotheses, provide a satisfying instance; use a negative case when it exposes vacuity or a model boundary. Tests should exercise behavior or the interface rather than restate a theorem by name.

After adding a library file, run `lake exe mk_all` to regenerate the aggregate. New tests belong in `CslibFrontierTests/` and are included by a Lake glob. During development:

```bash
scripts/check.sh --quick
```

Quick mode compares against the merge base with local `origin/main` without fetching by default. It includes committed, staged, unstaged and untracked changes and builds affected modules and importing clients when supported. It then runs the declaration linters on the affected library modules, so an argument that a change leaves unused in a client is reported before CI. Unsupported or ambiguous changes fall back to the full gate. Quick success is development feedback, not full integration validation.

Lean, dependency or build changes need all six gates on the final revision:

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` restores available caches and runs the sequence. A successful hosted run covering the final revision supplies this evidence without a duplicate local run. Required CI and merge-group checks still apply. Documentation-only changes need consistency, link and introduced Lean-example checks rather than a whole-library rebuild. Validation-tool changes also need direct checks of their changed behavior. [Validation policy](../../AGENTS.md#validation-sequence)

## Update and review both manuals

Before handoff, identify the reader tasks affected in both manuals. Update the relevant
workflows, model descriptions, assumptions, commands and examples in the same PR. If the
manual remains accurate, record a specific reason for it in the PR’s manual-impact assessment.
A proof-only edit preserving statements, imports and automation may need no prose change;
a changed encoding or resource bound normally does. An edit that changes the number of lines
in a file still moves the declarations below it, so repoint any manual links such as
`File.lean#L120` to them; the checker below reports a link that no longer starts a declaration.

Run `python3 scripts/check_operator_manual.py` from the repository root, and check changed
complete Lean clients as above. The coordinator must review both assessments and ensure independent review of affected
reader paths against the final revision. Changes to agent roles, direction, permissions or
intervention also require checking the [Agent Operator’s Manual](../AGENT_OPERATORS.md). The [maintenance procedure](../MAINTAINING.md)
sets out the human acceptance test and distinguishes live checks from dated history.

## Check the statement readers will see

Readers see the library statement itself: its module documentation, its declaration in the API documentation and any entry of the [results inventory](../../results/README.md) that lists it. When changing a named theorem's model, encoding, bound or hypotheses, update that documentation and the entry's scope note in [Entries.lean](../../CslibFrontierResults/Entries.lean). Inspect changed rendered pages and declaration links.

The axiom audit checks allowed dependencies of declarations stored in imported CslibFrontier modules. The results registry checks that each listed theorem exists, is public and is a proposition. Neither replaces reading the model and comparing it to the advertised mathematics. See [assurance](../design-and-assurance/assurance.md).

## Make the handoff reviewable

Explain the problem, resulting behavior, limitations and validation in the PR. Link its task issue and source references, preserve contributor credit, and disclose AI tools and their role under the applicable policy. Obtain independent correctness/API review of the current revision. A reviewer who helped design or implement the change cannot supply that independence; agent review is not human approval.

After fixes, request review of the affected delta. Changed reasoning, statement semantics and uncertain conflict resolutions require fresh review; a clean rebase may sometimes preserve existing approval. Integration requires maintainer authority as well as validation and review. State what is complete and what remains. When only a milestone is delivered, keep the broader objective visible and open or explicitly disposed of.

[complexitylib]: ../sources.md#complexitylib
