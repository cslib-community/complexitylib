# Contributing

Follow CSLib's [contribution guidelines](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md)
and [code style](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md).
The pinned copies are in `.lake/packages/cslib/` after fetching dependencies.
[AGENTS.md](AGENTS.md) records the local file, proof, validation, and review requirements.

## Proposing and contributing work

Use this repository's Issues or pull requests to agree on a substantial development
before implementing it.
State the mathematical endpoint, cite its source, identify existing APIs and missing dependencies,
and propose a first independently useful milestone. [ROADMAP.md](ROADMAP.md) lists open directions;
an item there is not an assignment or a claim that its prerequisites are complete.
Small fixes and API improvements can go directly to a pull request.

Keep a pull request small enough to review as one mathematical or engineering change. Include a
checked client for a new API and instances showing that bundled hypotheses can be met. Preserve
the original authors and licenses when porting code; cite mathematical sources in module
docstrings through [references.bib](references.bib), whose entries stay sorted by key.

Develop against representative clients and state the public contract: model or encodings,
mathematical behavior, and resource or security claim. Test automation on ordinary expressions,
alternative encodings, and important failure cases. Distinguish correctness, executability,
certified efficiency, and security in declaration docstrings.

For documentation-only changes, check links, claims against source, and Lean examples with the
imports shown. Record the scope of validation and review accurately.

## Library quality standard

The bar is Mathlib's [style guidelines](https://leanprover-community.github.io/contribute/style.html)
and CSLib's [CODESTYLE](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md), applied
uniformly to every area ([#587](https://github.com/cslib-community/complexitylib/issues/587)).
Mathlib's standard linter set already enforces the mechanical part; reviews enforce the rest:

1. **Reuse.** Use existing abstractions, in CSLib, Mathlib or this library, instead of parallel
   representations; formalize shared concepts once, at the level where they are general.
2. **Surface.** Public declarations are the intended API; helpers are `private`, and `@[expose]`
   marks only definitions whose bodies downstream proofs must unfold.
3. **Statements.** User-facing statements use mathematical notions and plain computability. Proof
   devices such as tidy machines stay inside proofs and the combinator layer that needs them.
   Names follow Mathlib's conventions.
4. **Automation as API.** Curate `simp`, `grind` and `fun_prop` sets so routine facts follow
   without unfolding; a fact that repeatedly needs plumbing signals a missing lemma or interface.
5. **Definitions and proofs.** Definitions are terms where possible. Proofs keep their logical
   progression visible: `simp only` mid-proof, and no large terminal `simpa` hiding the argument.
6. **Placement.** No duplicates; small topic modules; clients import what they use.
7. **Documentation.** Definitions and theorems are documented, citing sources; module docstrings
   list the actual public API; each area has a chapter in the guide.
8. **Tests.** Checked, nonvacuous examples of the area's main API: each exercises a concrete
   instance (a small input, a run, a counterexample). A one-line `example … := someTheorem` that
   only restates a signature is not a test; keep such lines only where they pin a curated abstract.

Improving an interface never weakens the mathematics: keep the models, encodings, independent
resource bounds and nonvacuity of the results it touches.

### Algorithms are programs

Probabilistic algorithms, such as key generation, signing, provers, verifiers, simulators,
extractors, samplers and reductions, are `ProbComp` or `OracleComp` programs. `PMF` is reserved
for their semantics, `OracleComp.evalWith` and its instances such as `ProbComp.eval`, and for
genuinely semantic objects: ideal distributions, the laws of games and the distributions compared
in a statistical argument. A program can be run against different oracles, budgeted, realized by a
machine and substituted into a reduction. A `PMF`-valued algorithm can do none of these, and
needs a separate hypothesis that some program realizes it. Exact theorems stay exact, as
statements about `evalWith`; see `Complexity/Languages/Probabilistic/Semantics.lean`.

### Public surface under the module system

Under an ordinary `import`, importers rebuild only when a module's exported `.olean` changes. That
file holds public statements, exposed bodies, attributes of public declarations, and the axioms
each public declaration depends on. Editing docstrings, private declarations, proofs or
non-exposed bodies leaves it unchanged, unless a proof edit changes that axiom set. `import all`
also loads private information, so such edits do reach its clients.

- **What is a helper.** A helper is proof plumbing: a step meaningful only inside one proof, or a
  fact about a module-local construction, encoding or intermediate quantity. Helpers are `private`
  by default. Keep `@[expose]` for bodies that downstream proofs unfold.
- **What stays public, even if nothing outside the module uses it yet.** Facts stated only in terms
  of public definitions that a user of those definitions would expect: characterizations (`_iff`),
  bounds, monotonicity and closure properties, simp and extensionality equations, invariance
  lemmas, and named results from the literature. Move general mathematics (lists, finsets,
  probability, bit strings) to `Complexity/Foundations` instead of making it private. Reference
  counts are evidence about current use, not the criterion; privatize by intent.
- **Reuse before re-proving.** If a fact you need already exists as a private declaration, make it
  public, moving it to its natural home if needed, instead of proving it again. Reviewers treat a
  re-proof of an existing private fact as a finding.
- A private `@[fun_prop]` theorem still exports its rule, and `fun_prop` then fails in importers.
  Write `attribute [local fun_prop] helper` instead. Private `simp` lemmas, Aesop rules and
  instances stay local.
- Ordinary imports cannot name private declarations. When privatizing, update the tests and
  abstracts that name them in the same PR, or give a companion module `import all`.
- For an audit, `python3 scripts/audit_queries.py references PREFIX` lists where each declaration
  under a source path is referenced, and `duplicates` lists declarations with alpha-equivalent
  statements in different modules. Uses through `rfl`, `decide`, simp sets or instances leave no
  reference, and a declaration nobody references may still be wanted API: privatize by intent
  (#926), not because the helper lists it. It is an on-demand helper, never run in CI.

Tidy computability (`ComputableTidily…`, `ComputesTidily…`, `IsTidy…`) may appear anywhere inside
proofs, through `.tidy`, `.of_tidy`, a proof-local `attribute [local fun_prop] … in` or a tidy
`have`. It never appears in a public statement: a theorem's type, or a definition's type, exposed
body or fields. Only the raw machine constructions in `scripts/tidy_allowlist.txt` are exempt.
CI enforces this with `scripts/check_tidy_surface.py`. The existing tidy statements, which #456 is
restating, are counted per module in `scripts/tidy_surface_baseline.json`, and CI fails when a
module's count differs from its entry. When you remove some, lower the baseline in the same PR
with `python3 scripts/check_tidy_surface.py --update`, so that they cannot come back. Until your
PR lands, any other merge that removes tidy statements makes your baseline stale: rebase and
rerun `--update`.

## AI assistance and review

AI-assisted and human-written contributions follow the same standards. Disclose which AI tools
you used and for what in the PR description. The contributor is responsible for the result and
for resolving review findings; a generated proof or review is not evidence of human approval.
Maintainers decide scope and acceptance, and arrange the independent API and correctness reviews
required by [AGENTS.md](AGENTS.md#review-cycle). Contributors need not install a maintainer's
agent tooling to submit a change.

Run `scripts/build.sh [Lake build arguments]` for a build or `scripts/check.sh` for the six project
checks; both attempt cache restoration first. Before the first MCP elaboration/build in a
checkout, and after changing branches or pins, run `scripts/cache/ensure.sh`. The command is
shared by all agent clients. See the [cache guide](scripts/cache/README.md#automatic-restoration)
for retries and intentional opt-out.

The test suite audits the axiom dependencies of every declaration stored in imported `Complexity`
modules. Named `#print axioms` checks are added only for results meant to depend on fewer axioms
than the standard `propext`, `Classical.choice` and `Quot.sound`, such as choice-free results. The
audit trusts the compiled Lean artifacts and permits `Classical.choice`; it does not certify
efficient computation or agreement with a textbook statement.

For concurrent local validation, choose a thread budget for the shared host, for example
`LEAN_NUM_THREADS=2 scripts/check.sh`. Lean's
[thread-pool setting](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/)
defaults to the number of logical processors and is not a hard process or memory cap; check the
observed concurrency and memory use. Keep mutable build outputs separate between worktrees
(for example with `scripts/worktree.sh create <branch> [dir_name]`, which seeds `.lake/build` from
the root checkout and, when `<branch>` exists only on `origin`, checks it out tracking
`origin/<branch>`). Run `python3 scripts/check_hygiene.py` to audit `-- upstream:` markers,
forbidden proof tokens, `set_option` justifications and the key order of `references.bib`
(pass `--check-simp` to also run the heuristic check for non-terminal bare `simp` calls in
candidate modules). After a build,
`python3 scripts/check_changed_files.py` checks the files your branch adds or changes: each name
listed in a module docstring's "Main …" sections must exist, and a new test file must do more
than restate signatures with `example … := name`. CI runs both. On pull requests CI also runs
`python3 scripts/parallel_defs.py`, an advisory notice (it never fails) that lists new or changed
public definitions sharing a large anonymized subterm with an existing one, or merely renaming one.

The helper hard-links package sources by default, copies root and dependency build caches with
independent files (including symlink targets), isolates dependency `.git` directories and pointer
files, dereferences any package symlink whose target escapes the package directory, and runs
`scripts/cache/ensure.sh` (`scripts/cache/get.sh`) before the first build. It never points a
worktree at the primary checkout and refuses targets or symlinks that do. Do not edit shared
package sources; use `--copy-cslib` or `--copy-packages` when those sources must change. Seeding
preserves existing destination caches and does not repair worktrees created with shared dependency
caches by an older helper; use a fresh worktree for isolated validation.

Coordinate with a run's owner before rescheduling it, preserve completed artifacts, and record
an interrupted run as incomplete. A fresh run must pass all six strict checks on the final revision.

Record validation and review in the PR, or in the commit description for work without a PR:
the tested revision (or base revision and exact diff), commands and outcomes, reviewer/tool and
scope, findings and their resolution, and any remaining limitations. Preserve enough evidence
there for another contributor to assess the change; a path into a local `.lake/` directory is not
a durable review record. Recheck changes made after review and identify the final reviewed revision.
Link the hosted CI run for the final revision rather than asserting which checks passed. Keep review
verdicts short: the revision, the verdict and the findings, linking evidence rather than pasting it.
Before requesting review, run `python3 scripts/check_pr_names.py --pr N` on the PR head: it lists
backticked Lean names in the description that the head does not declare (CI posts the same advisory
notice).

## Documentation

Keep each fact in one maintained location. The README explains the purpose and points to useful
entry points; module docstrings explain the mathematics and API; checked Lean examples show usage.
ROADMAP lists open directions only; status and progress live on issues and PRs, so a PR does not
edit ROADMAP unless it opens or closes a direction. UPSTREAM records coordination and exceptional
integration decisions, while source markers record module status. Batch measurements and
validation/review evidence belong in commit or PR descriptions.
Link to these sources instead of repeating them in new guides. Add a separate document only when
it provides useful explanation that does not already have a suitable home.

The guide (`guide/`) is the narrative path into the library: a chapter per area, written as a
newcomer should meet it, with checked Lean examples whose names link to the API documentation.
When a chapter needs proof plumbing or a missing lemma, improve the library rather than
documenting around it.

The [README](README.md#build-and-use) explains how to generate API documentation using
[doc-gen4](https://github.com/leanprover/doc-gen4) and how to build the guide with
[Verso](https://github.com/leanprover/verso). Their separate `docbuild` and `guide` projects share
the library's toolchain and dependency checkouts, and `docbuild` its bibliography. After changing
library dependencies, run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update complexitylib`
and the same with `-d guide`. When changing Lean, also update the doc-gen4 tag in
`docbuild/lakefile.toml` and the Verso tag in `guide/lakefile.toml`, both named after the Lean
version, and run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update doc-gen4` and
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d guide update verso`. Commit the refreshed lockfiles and
run the documentation checks and builds.

## Maintaining the headline abstracts

The small selection in [abstracts/catalogue.json](abstracts/catalogue.json) is the public headline
catalogue. Every selected result has a checked Lean abstract and bridge, with explicit definitions,
models, encodings, hypotheses, bounds and limitations. The library contains many other results;
selection is an editorial decision, not an automatic consequence of adding a theorem. A headline
must establish a substantial full endpoint with conventional semantics and nonvacuous premises.
Keep incomplete endpoints in `ROADMAP.md` and credit mathematical and formalization sources.

Every AI-authored PR must assess its final Lean changes against the selection. Update affected
abstracts and scope notes, or explain why the catalogue is unaffected. Proof-only changes with
unchanged statements and scope can record that assessment without rewriting the abstract. Follow the
repository's `lean-abstract` skill, import new abstracts in `ComplexityTests/Abstracts/All.lean`,
and run their `#check_abstract` audits. Allow only narrow, explained foundational models; do not
allowlist the result's class definitions or construction to evade a self-contained statement.

Arrange independent API, correctness and abstract reviews against the final source revision.
Reviewers must check quantifiers, semantics, encodings, bounds, nonvacuity and readability. Record
reviewers, exact revisions, findings and resolutions. These checks supplement Lean's proof checking;
they are not a proof that the English interpretation is equivalent or human editorial approval.

Run `python3 -B scripts/build_abstracts.py --check` to check the selection. The **Formal abstract
PDFs** workflow generates individual PDFs and a combined catalogue with source digests, revision
provenance and exact declaration links. Inspect its rendered pages and links before integration,
recording the artifact/run and source revisions. Local generation is supported; see
[the build guide](abstracts/README.md). The documentation site publishes the latest main
build under `https://www.cslib.io/complexitylib/abstracts/`. Generated TeX and PDFs stay untracked; the former paper/TeX index has been retired.

## Upstreaming

```bash
python3 scripts/upstream.py Complexity.Computability.DecisionTree.Basic --cslib ../cslib --dry-run
```

This previews copying a module to its mirrored CSLib path, rewriting imports, and removing the
upstream marker. Omit `--dry-run` to prepare the worktree and regenerate its root imports.
The script writes whole new files and refuses to overwrite an existing destination; integrate
additions to existing files and alternative destinations manually.
Validate there according to CSLib's current instructions before opening a PR. Record its number
and head SHA in the module's `-- upstream:` marker.

Coordinate cross-cutting abstractions with CSLib before proposing them upstream. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for pin updates, synchronization checks,
and removal of superseded local copies.
