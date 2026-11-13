# Contributing

Follow the mathematical, API and style conventions in CSLib's
[contribution guidelines](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md) and
[code style](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md), using the pinned copies
in `.lake/packages/cslib/` after fetching dependencies. [AGENTS.md](AGENTS.md) defines this
repository's workflow, file layout, proof, validation and review requirements. Upstream
submissions follow the target repository's current process.

For setup, start with [Build a checkout](README.md#build-a-checkout). The
[guide](https://www.cslib.io/cslib-frontier/guide/) and
[checked examples](README.md#start-here) introduce the APIs before you change them.

## Proposing and contributing work

Agree on a substantial development before implementing it. An issue in this repository, written
with the [development template](.github/ISSUE_TEMPLATE/development.md), is one good way to
propose a new direction; a pull request can also start the discussion. There is no separate
roadmap repository. State the endpoint, cite its source, identify existing APIs and missing
dependencies, and propose a first independently useful milestone. If you write an issue on
someone else's behalf, for example from their short description, name them in its "Originated
by" field. [ROADMAP.md](ROADMAP.md) lists the accepted directions; an item there is not an
assignment or a claim that its prerequisites are complete.
Small fixes and API improvements can go directly to a pull request. Use the existing issue or
PR to record ownership and handoffs; do not create duplicate task records. Prioritize fixes and
landing open PRs when review or integration is the bottleneck.

A new file's `Copyright` and `Authors:` lines name the originator(s) of the issue or proposal it
implements and the person whose agents did the implementation (the human, not a fleet or bot
account); the [file rules](AGENTS.md#file-rules) give the details. The originator is the person
named in the issue's "Originated by" field when present, and otherwise the issue's author. The
rule applies going forward: existing headers stay unless someone asks for a correction, and ports
keep their original authors.

Keep a pull request small enough to review as one mathematical or engineering change. Batch
related mechanical fixes when they share a contract and validation; split at independently useful
boundaries rather than creating a PR per cleanup. Include a checked client for a new API and
instances showing that bundled hypotheses can be met. Preserve
the original authors and licenses when porting code; cite mathematical sources in module
docstrings through [references.bib](references.bib), whose entries stay sorted by key. Two
branches that add entries between the same neighbours conflict as text;
`scripts/resolve_bib_conflict.py` merges the file entry by entry and refuses when both sides
changed one entry. To have `git merge` use it for `references.bib`, run once per clone:
`git config merge.bibkeys.driver 'python3 scripts/resolve_bib_conflict.py --driver %O %A %B'`.
The `mk_all` import aggregates have a similar opt-in driver, which merges their import lines as
sets and writes them sorted:
`git config merge.leanagg.driver 'python3 scripts/resolve_aggregate_conflict.py %O %A %B'`.
Without it, git merges them as text; regenerate them with `lake exe mk_all` rather than trusting a
hand or `merge=union` merge.

Develop against representative clients and state the public contract: model or encodings,
mathematical behavior, and resource or security claim. Test automation on ordinary expressions,
alternative encodings, and important failure cases. Distinguish correctness, executability,
certified efficiency, and security in declaration docstrings.

For documentation-only changes, check links, claims against source, and Lean examples with the
imports shown. Record the scope of validation and review accurately.

## Library quality standard

The bar is Mathlib's [style guidelines](https://leanprover-community.github.io/contribute/style.html)
and CSLib's [CODESTYLE](https://github.com/leanprover/cslib/blob/main/CODESTYLE.md), applied
uniformly to every area ([#587](https://github.com/cslib-community/cslib-frontier/issues/587)).
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
   Specifications are interfaces too: when callers re-derive the same frame or invariant after
   each call to a routine, state the frame in the routine's specification in a form they can
   apply, such as a `Finset` of written registers, or prove the invariant's transfer across the
   call once, as a corollary of that specification.
5. **Definitions and proofs.** Definitions are terms where possible. Proofs keep their logical
   progression visible: `simp only` mid-proof (a `simp` closed at once by `omega`, `linarith` or
   a similar finishing tactic counts as terminal), and no large terminal `simpa` hiding the
   argument. Do not copy a proof block into another proof. When a proof you add or change needs an
   argument that another proof makes, first look for an existing lemma in this library, CSLib,
   Mathlib or core. If there is none and a lemma would make both proofs clearer, state it once and
   use it in both, `private` if it is plumbing ([Placement and reuse](AGENTS.md#placement-and-reuse)
   covers proofs in different modules); otherwise leave them. Derive variants, such as a special
   case or the same result with another constant, from the general result instead of copying and
   editing its proof. Whether a shared lemma pays is judged on the code: repeated constructions,
   bounds and changes of variables usually do; a routine side goal of a few lines does only when
   the lemma states a fact a reader would look up by name, such as a round trip, and replaces a
   fragile `simpa` or a similar opaque step. A shared lemma pays when each call site can supply
   its hypotheses directly; one whose hypotheses restate most of what the copied block derives
   saves nothing.
6. **Placement.** No duplicates; small topic modules; clients import what they use.
7. **Documentation.** Definitions and theorems are documented, citing sources; module docstrings
   list the actual public API; each area has a chapter in the guide.
8. **Tests.** Checked, nonvacuous examples exercise concrete inputs, runs, counterexamples or
   meaningful client behavior such as inference, imports and automation. Merely restating a
   signature adds no behavioral coverage.
   Preserve existing guarantees when rewriting tests: exact bounds or probabilities must not
   become weaker inequalities, and regression cases must not become tautologies.

For changed APIs and reuse refactors, authors and reviewers
[check the API through its callers](AGENTS.md#check-the-api-through-its-callers): inspect named
access, semantic matcher/range facts, shared operational definitions, representation bridges and
the intended public surface. Identify a representative caller that benefits, with evidence
proportional to the change; a successful build alone does not establish these design properties.

**Structures for domain objects and records**
([#4385](https://github.com/cslib-community/cslib-frontier/issues/4385)). Model domain objects,
problem instances, certificates, configurations, and multi-field algorithm contexts, states or
records as documented `structure`s with named, documented fields, and declare their field-tuple
encodings with `enc_structure` ([AGENTS.md](AGENTS.md#structures-for-domain-objects-and-records)).
A migration keeps the encoded words, with a checked equality; a left-grouped tuple needs nested
sub-records or `encOfEquiv` ([encoding rule 5](AGENTS.md#encodings-in-statements)).
Do not introduce tuple type synonyms such as
`abbrev HittingSetInstance := (List ℕ × List (List ℕ)) × ℕ` or bare-product problem sets such as
`Set (List (ℕ × ℕ) × ℕ × ℕ)` or `Set (Graph × ℕ)`. Named fields document the mathematical
components in `doc-gen4`, enable dot-notation, and eliminate positional projections before they
start, while `enc_structure` supplies the embedding and its `fun_prop` projection and constructor
certificates across degree, `ComputableInO`, `ComputableInSpace` and `ComputableInPolyTime`. Keep
ordinary `Prod` (`×`) for generic binary combinators, Cartesian products and uncurried
multi-argument inputs such as an NP verifier `Instance × List Bool → Bool`.

**Named components instead of positional projections**
([#1764](https://github.com/cslib-community/cslib-frontier/issues/1764)). Public statements and
the bodies of public definitions do not reach into nested tuples with projection chains such as
`c.1.2` or `s.1.1.2`. A reader should not have to reconstruct the tuple layout. In order of
preference:

1. Bind the components by name: `fun ((d, x), c) => step d x c`, not
   `fun c => step c.1.1 c.1.2 c.2`.
2. Use `Function.uncurry`, `Prod.map` or composed projections, as the plain calculus rules
   already do.
3. Turn a recurring tuple context into a small `structure` with named fields.
4. If restructuring is too invasive, add named `abbrev` accessors such as
   `LocalIncidence.route`.

The rewritten form should stay definitionally equal to the old one, so that clients and automation
(`fun_prop`, `@[program_certificate]`) keep working. Single projections (`p.1`) and
destructuring inside proofs (`obtain ⟨⟨d, x⟩, c⟩ := s`) are fine. "Composed projections" means
point-free composition such as `Prod.fst ∘ Prod.snd`; respelling `p.2.1` as `Prod.fst (Prod.snd p)`
or naming a tail with `let rest := p.2` does not name anything.

Two places keep projections, as standing exceptions:

- **Conclusions that automation looks up by head.** Destructuring turns the function into a
  `match` auxiliary, so `@[program_certificate]` and efficiency-key lookups no longer find the
  certificate. Keep the projection form there.
- **Section `variable` hypotheses in `module` files.** On the current toolchain a destructuring
  lambda in a section `variable` of a `public section` elaborates to `sorry`, with only a warning
  ([#1764](https://github.com/cslib-community/cslib-frontier/issues/1764)). Use projections there,
  or bind the hypothesis in the theorem's own signature.

`scripts/check_projection_chains.py` counts the chains of depth 2 or more in each module's public
statements and public definition bodies, leaving out proofs, these two exceptions and named
accessors. CI fails a pull request when a module it changes has more chains than its entry in
`scripts/projection_chains_baseline.json`, or than it had at the merge base unless the pull request
raises the entry; a new module starts at 0. Removing chains needs no baseline edit, which keeps
pull requests from colliding on neighbouring lines of the baseline in the merge queue; a periodic
`--update-baseline --all` prunes stale entries. Edit the baseline only to raise an entry on
purpose, as for a moved module (`--update-baseline --allow-increase`). `--list PREFIX` shows the
remaining chains of an area.

**Readable encodings** ([#1656](https://github.com/cslib-community/cslib-frontier/issues/1656)).
An encoding is part of what a statement claims, so statements show it; they should not make the
reader parse the same nested encoding again and again. Name a compound encoding that recurs in a
module's statements with a documented, reducible `abbrev`, give domain encodings their own names,
declare field-tuple structure encodings with `enc_structure`, and keep unary versus binary,
representations and framing visible in the name or its docstring. For example, the query-machine
certificates take
`ComputableInSpace M.next (encStateRead encS) encS fun p => (encStateRead encS p).length`
rather than restating `encPair encS (encOption encBool)` twice; `encStateRead` is documented as a
state paired with the bit read, with the state framed. Because the name is reducible, the
statement is definitionally unchanged, and `enc_len`, `fun_prop` and the combinators' simp lemmas
see through it; syntactic tools such as `omega` do not. New and changed statements follow the
exact rules in [AGENTS.md](AGENTS.md#encodings-in-statements); the encoding-readability lint
checks the repetition rule and rejects compound-encoding `local notation`s.

To sweep an area, `python3 scripts/check_encoding_readability.py --list CslibFrontier/Logics` lists
its repeated compound encodings with their declarations, ignoring the baseline, and the local
notations that abbreviate a compound encoding. A sweep must leave every statement unchanged:
compare each changed public declaration's type with its type on `main`, either after
`Lean.Meta.deltaExpand` of the new names and of the reducible type synonyms they mention, or with
`isDefEq` at reducible transparency. Expanding only the new names is not enough: a coercion's type
argument can read `CNF V` on one side and `List (List (V × Bool))` on the other.

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
statements about `evalWith`; see `CslibFrontier/Languages/Probabilistic/Semantics.lean`.

### Public surface under the module system

Under an ordinary `import`, importers rebuild only when a module's exported `.olean` changes. That
file holds public statements, exposed bodies, attributes of public declarations, and the axioms
each public declaration depends on. Editing docstrings, private declarations, proofs or
non-exposed bodies leaves it unchanged, with two exceptions: a proof edit that changes that axiom
set, and a body that the module itself rewrites with `simp [f]` or `rw [f]`. That rewrite
generates the equation lemma `f.eq_1`, whose statement is the body, and stores it in the exported
file even when `f` is private (Lean v4.36; `unfold f`, `dsimp only [f]` and `rfl` did not in our
tests, [#4243](https://github.com/cslib-community/cslib-frontier/issues/4243)). `import all` also
loads private information, so such edits do reach its clients.

- **What is a helper.** A helper is proof plumbing: a step meaningful only inside one proof, or a
  fact about a module-local construction, encoding or intermediate quantity. Helpers are `private`
  by default. Keep `@[expose]` for bodies that downstream proofs unfold.
- **What `@[expose]` reaches.** A section-level `@[expose]` affects only the section's `def`-kind
  declarations and derived instances. Theorems, structures and inductives ignore it, and
  abbreviations and non-Prop instances are exposed without it. A header over a section with
  nothing to expose only suggests that bodies are exported; `check_changed_files.py` rejects one in
  a changed file, so write `public section`. When a public proof needs a body that is not exposed,
  Lean may report `Expected a definition with an exposed body`, or only an indirect failure:
  `omega`, `decide` or a projection that cannot see through the definition in a client, or the
  definition's own `@[simps]` lemmas rejected as not `rfl`. Expose that definition, or state the
  lemma the client needs.
- **What stays public, even if nothing outside the module uses it yet.** Facts stated only in terms
  of public definitions that a user of those definitions would expect: characterizations (`_iff`),
  bounds, monotonicity and closure properties, simp and extensionality equations, invariance
  lemmas, and named results from the literature. Move general mathematics (lists, finsets,
  probability, bit strings) to `CslibFrontier/Foundations` instead of making it private. Reference
  counts are evidence about current use, not the criterion; privatize by intent.
- **Reuse before re-proving.** If a fact you need already exists as a private declaration, make it
  public, moving it to its natural home if needed, instead of proving it again. Reviewers treat a
  re-proof of an existing private fact as a finding.
- A private `@[fun_prop]` theorem still exports its rule, and `fun_prop` then fails in importers.
  Write `attribute [local fun_prop] helper` instead. Private `simp` lemmas, Aesop rules and
  instances stay local.
- Ordinary imports cannot name private declarations. When privatizing, update the tests and
  results inventory entries that name them in the same PR, or give a companion module
  `import all`.
- **Before reaching for `import all`.** Prefer a public lemma, such as an equation lemma for an
  unexposed definition, or `@[expose]` on the one definition whose body importers unfold. An
  exposed body is interface, so editing it rebuilds every importer; through `import all`, private
  and body edits rebuild only that client. Each remaining `import all` states its reason in one
  sentence, in the importer's module docstring or a comment beside the import, naming the private
  lemmas or unexposed bodies it reads.
- For an audit, `python3 scripts/audit_queries.py references PREFIX` lists where each declaration
  under a source path is referenced, and `duplicates` lists declarations with alpha-equivalent
  statements in different modules. Uses through `rfl`, `decide`, simp sets or instances leave no
  reference, and a declaration nobody references may still be wanted API: privatize by intent
  (#926), not because the helper lists it. It is an on-demand helper, never run in CI.

Tidy computability (`ComputableTidily…`, `ComputesTidily…`, `IsTidy…`) may appear anywhere inside
proofs, through `.tidy`, `.of_tidy`, a proof-local `attribute [local fun_prop] … in` or a tidy
`have`. It never appears in a public statement: a theorem's type, or a definition's type, exposed
body or fields. Only the raw machine constructions in `scripts/tidy_allowlist.txt` are exempt.
CI enforces this with `scripts/check_tidy_surface.py`. The existing tidy statements, which #862 is
removing, are counted per module in `scripts/tidy_surface_baseline.json`, and CI fails when a
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

Use the [validation sequence](AGENTS.md#validation-sequence) for the project gates and
when focused local checks or hosted CI supply the required evidence. `scripts/build.sh` and
`scripts/check.sh` attempt cache restoration automatically. Bootstrap cold checkouts before MCP
elaboration with `scripts/cache/ensure.sh`; retry for missing outputs or changed dependencies,
not merely a new commit with warm artifacts. See the
[cache guide](scripts/cache/README.md#automatic-restoration) for actual retries and opt-out.

The test suite audits the axiom dependencies of every declaration stored in imported `CslibFrontier`
modules. Named `#print axioms` checks are added only for results meant to depend on fewer axioms
than the standard `propext`, `Classical.choice` and `Quot.sound`, such as choice-free results. The
audit trusts the compiled Lean artifacts and permits `Classical.choice`; it does not certify
efficient computation or agreement with a textbook statement.

For concurrent local validation, choose a thread budget for the shared host, for example
`LEAN_NUM_THREADS=2 scripts/check.sh`. Lean's
[thread-pool setting](https://lean-lang.org/doc/reference/latest/IO/Tasks-and-Threads/)
defaults to the number of logical processors and is not a hard process or memory cap; check the
observed concurrency and memory use. Together, concurrent builds can also exhaust the host's
file-handle table, so bound the number of builds as well as their threads; see
[the troubleshooting chapter](manual/workflows/troubleshooting.md#diagnose-too-many-open-files-in-system).
Keep mutable build outputs separate between worktrees
(for example with `scripts/worktree.sh create <branch> [dir_name]`, which seeds `.lake/build` from
the root checkout and, when `<branch>` exists only on `origin`, checks it out tracking
`origin/<branch>`). Pass `--source-only` to skip the initial copy; the
[cache guide](scripts/cache/README.md#automatic-restoration) explains bootstrap and dependency costs.
Run `python3 scripts/check_hygiene.py` to audit `-- upstream:` markers,
forbidden proof tokens, `set_option` justifications, the key order of `references.bib`, that
every docstring citation key has an entry there and that `ROADMAP.md` entries are short scope
statements with inline links
(pass `--check-simp` to also run the heuristic check for non-terminal bare `simp` calls in
candidate modules). After a build,
`python3 scripts/check_changed_files.py` checks the files your branch adds or changes: each name
listed in a module docstring's "Main …" sections must exist, a new test file must do more
than restate signatures with `example … := name`, and an `@[expose] … section` header must have a
definition to expose; `--source-only` runs the last two without build outputs, as
`scripts/check.sh --quick` does. CI runs both, and also
`python3 scripts/check_encoding_readability.py`, the ratchet on repeated compound encodings in
public statements and check against compound-encoding `local notation`s
([#1656](https://github.com/cslib-community/cslib-frontier/issues/1656)). It
enforces its baseline and the `local notation` rule only in the modules a pull request changes,
and merge groups only report,
so `main` can drift above the baseline; the next change to a drifted module names the encoding
or records it with `--update-baseline --allow-increase`. Its docstring gives the rule and the
options. On pull requests CI also runs
`python3 scripts/parallel_defs.py`, an advisory notice (it never fails) that lists new or changed
public definitions sharing a large anonymized subterm with an existing one, or merely renaming one.
With `--theorems` it lists new or changed theorems, private ones included, whose statement another
library theorem or a Lean core, Batteries, Mathlib or cslib theorem already has, up to binder names,
universe levels, the order of hypotheses and instance arguments, and the notations `≥`, `>`, `≠`.
It also handles reversed equalities and built-in list lookup by a `Fin` index versus its natural
value, ignoring that lookup's bounds proof while retaining the list and index. It does not unfold
arbitrary definitions or custom indexing instances, or match specializations of a general theorem.
CI runs that notice too. `--all` examines the whole library: `python3 scripts/parallel_defs.py
--theorems --all --limit 1000` lists every such group, the candidates of #949 item A.2.
The reports link project declarations at the checked revision and disclose skipped or incomplete
comparisons. Reviewers inspect the notices and resolve relevant candidates before approval under
[the review cycle](AGENTS.md#review-cycle); a successful advisory exit alone is not a clean audit.
On pull requests CI also runs a third advisory notice, `python3 scripts/proof_copies.py`, which
reads only the sources. It lists tactic blocks of four or more lines, on lines a change adds or
modifies, that repeat a block of another proof, or of the same proof, in the same file or
directory up to local names and at most two renamed constants
([#3725](https://github.com/cslib-community/cslib-frontier/issues/3725)). If both blocks make the
same argument and a lemma would make both proofs clearer, prove it once and use it in both;
otherwise leave them. Its candidates, and those that `--all` lists for the whole library, are not
a count to drive down.

The helper hard-links package sources by default, copies root and dependency build caches with
independent files (including symlink targets), isolates dependency `.git` directories and pointer
files, dereferences any package symlink whose target escapes the package directory, and runs
`scripts/cache/ensure.sh` (`scripts/cache/get.sh`) before the first build. It never points a
worktree at the primary checkout and refuses targets or symlinks that do. Do not edit shared
package sources; use `--copy-cslib` or `--copy-packages` when those sources must change. Seeding
preserves existing destination caches and does not repair worktrees created with shared dependency
caches by an older helper; use a fresh worktree for isolated validation.

Coordinate with a run's owner before rescheduling it, preserve completed artifacts, and record
an interrupted run as incomplete. Full validation must cover the final source revision as
specified in [AGENTS.md](AGENTS.md#validation-sequence); a successful hosted run counts, and
required merge-group checks still apply.

Record validation and review in the PR, or in the commit description for work without a PR:
the tested revision (or base revision and exact diff), commands and outcomes, reviewer/tool and
scope, findings and their resolution, and any remaining limitations. Preserve enough evidence
there for another contributor to assess the change; a path into a local `.lake/` directory is not
a durable review record. Recheck changes made after review and identify the final reviewed revision.
Link the hosted CI run for the final revision rather than asserting which checks passed. Keep review
verdicts short: the revision, the verdict and the findings, linking evidence rather than pasting it.
For descriptions with Lean declaration names, `python3 scripts/check_pr_names.py --pr N` can
catch backticked names absent from the PR head. CI posts the same advisory notice; fix relevant
findings without requiring a duplicate local run.

## Documentation

Keep each fact in one maintained location. The README explains the purpose and points to useful
entry points; module docstrings explain the mathematics and API; checked Lean examples show usage.
ROADMAP lists accepted directions only, grouped by area.
Each entry states one direction's scope in a few sentences, one sentence per line, with its issue
linked inline as `[#N](https://github.com/cslib-community/cslib-frontier/issues/N)`.
Status and progress live on issues and PRs, so a PR edits ROADMAP only when it opens or closes a
direction, and a direction leaves ROADMAP only when it is completed or deliberately dropped.
`scripts/check_hygiene.py` rejects link reference definitions, nested bullets and entries over 600
characters of Markdown (a link counts as its text): definitions appended to the end of the file and
growing progress notes conflicted between PRs in the merge queue.
[Upstreaming](#upstreaming) lists live coordination threads, while source markers record module
status and module docstrings record provenance.
Batch measurements and validation/review evidence belong in commit or PR descriptions.
Link to these sources instead of repeating them in new guides. Add a separate document only when
it provides useful explanation that does not already have a suitable home.

The [Operator's Manual](manual/README.md) is the substantial codebase reference for human and
agent contributors: installation, first use, tactics, models and resource conventions, design
and proof patterns, development procedures and troubleshooting. The short
[Agent Operator's Manual](manual/AGENT_OPERATORS.md) explains to humans how to direct agents,
choose roles, assign work and judge review and handoffs. The Operator's Manual's tutorial layer
includes the guide (`guide/`): a chapter per area, written as a newcomer
should meet it, with checked Lean examples whose names link to the API documentation.
When a chapter needs proof plumbing or a missing lemma, improve the library rather than
documenting around it.

The [build instructions](manual/BUILD.md#build-the-api-reference) explain how to generate API
documentation using [doc-gen4](https://github.com/leanprover/doc-gen4) and how to build the guide
with [Verso](https://github.com/leanprover/verso). Their separate `docbuild` and `guide` projects share
the library's toolchain and dependency checkouts, and `docbuild` its bibliography. After changing
library dependencies, run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update cslib-frontier`
and the same with `-d guide`. When changing the Lean toolchain, also update the doc-gen4 tag in
`docbuild/lakefile.toml` and the Verso tag in `guide/lakefile.toml`, both named after the Lean
version, and run `MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d docbuild update doc-gen4` and
`MATHLIB_NO_CACHE_ON_UPDATE=1 lake -d guide update verso`. Commit the refreshed lockfiles and
run the documentation checks and builds.

### Maintaining the manuals

Every change must assess its effect on both manuals. Changes to a model,
encoding, theorem hypothesis or bound, public API, import, tactic, dependency, build command or
development procedure must update the affected instructions and reference material in the same
change. Changes to agent roles, delegation, review, coordination or human direction must update
the affected Agent Operator's Manual instructions too. If no edit is needed for one or both
manuals, give a short, concrete reason in the PR's Manual impact
section, or in the commit description when there is no PR. This assessment is required; needless
text changes are not. Update the assessment when the scope changes, and keep its evidence in one
place.

Write the Operator's Manual as a user manual in the ordinary sense: a human with basic Lean,
editor and terminal skills
should be able to set up the library, complete a first example, choose an appropriate model,
apply its API, diagnose a failed attempt, validate a change and prepare it for review. Assume no
agent tools or prior conversation. Each procedure should state its prerequisites and starting
point, give the necessary commands or code with their context, describe the expected result,
and explain how to check it and recover from likely failures. Include the model, encoding and
resource conventions that affect the user's choice, and explain particular proof considerations
where they teach a reusable method or a model boundary. Agents should be able to consult this
maintained account without repeating the investigation or relying on earlier conversations.
Keep the Agent Operator's Manual short and directed at the person driving the agents; put
participant procedures in the Operator's Manual and historical evidence in its supplement.
Place a new section where its topic belongs in a chapter rather than at the end: sections that
concurrent PRs append at the same place conflict in the merge queue. Put a new algorithm endpoint
on the matching topic page listed under `manual/algorithms-and-memory/index.md`, in topic order.

Keep executable Lean examples in `CslibFrontierTests/` or the checked Verso guide and link their
complete source, including imports and local context. Use checked excerpts rather than a second
independently maintained copy. Check new or changed examples with Lean; source comparison alone
does not establish that an example elaborates. The live checker and its controls are required
in CI and in both full and quick `scripts/check.sh` runs. For documentation-only validation, run
`python3 scripts/check_operator_manual.py` and `python3 scripts/test_operator_manual.py`
directly; they use only Python and need no generated data or publishing tools. See the manual's
build instructions for PDF generation; inspect affected rendered pages when changing its content
or rendering. The **Operator's Manual PDFs** workflow builds both books for pull requests that
change the manual or its scripts, so rendered pages can be inspected without local TeX tools.
Generated LaTeX, PDFs and research exports stay untracked; retain their scripts and
maintained source inputs. Keep historical measurements and transcript evidence explicitly dated;
do not present their frozen counts as current library state.

Impact on both manuals is a mandatory part of independent review before integration, and
coordinators are responsible for ensuring that this review happens. The reviewer checks
the assessment against the final revision, including the reason for no edit when applicable.
For an affected procedure, follow the documented starting point, inspect or run the example and
its validation as appropriate, and check that a human can understand the outcome and next step.
Check relevant API names, imports, assumptions, resource bounds, source credit and recovery
instructions, as well as affected role, delegation and handoff guidance. Record the verdict with
the existing code review; an additional reviewer is needed
only for an uncovered question. Compilation, excerpt checks and a completed PR field do not by
themselves establish that the manual is usable or correct.

## Upstreaming

```bash
python3 scripts/upstream.py CslibFrontier.Computability.DecisionTree.Basic --cslib ../cslib --dry-run
```

This previews copying a module to its mirrored CSLib path, rewriting imports, and removing the
upstream marker. Omit `--dry-run` to prepare the worktree and regenerate its root imports.
The script writes whole new files and refuses to overwrite an existing destination; integrate
additions to existing files and alternative destinations manually.
Validate there according to CSLib's current instructions before opening a PR. Record its number
and head SHA in the module's `-- upstream:` marker.

Coordinate cross-cutting abstractions with CSLib before proposing them upstream. Follow
[AGENTS.md](AGENTS.md#staying-current-with-upstream) for pin updates, synchronization checks,
and replacing superseded local files with deprecated shims.

Upstream status is recorded in source. Each module's `-- upstream:` marker gives its status, PR
number, copied revision and, when it is not the mirrored CSLib path, its destination; markers can
also introduce copied blocks. `-- vendored:` comments record local adaptations of copies, and
module docstrings and [NOTICE](NOTICE) record provenance and credit. `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` pin versions. `python3 scripts/upstream_sync.py --offline`
lists copies; without `--offline` it compares recorded revisions and the base pin with upstream
(head revisions only, not source equality).

### Coordination threads

These are pointers to upstream discussions that affect local work, not a record of live PR status;
check the thread before starting or submitting overlapping work. Add a line when a thread starts to
affect local work and remove it when it no longer does; keep details in the linked thread or the
module docstring. A destination named in a `candidate` marker is a proposal for upstream review,
not a decision.

* **Machine calculus (Christian Reitwiessner).** The calculus copies
  [`crei/tidy-universal`](https://github.com/crei/cslib/tree/crei/tidy-universal),
  [#1111](https://github.com/leanprover/cslib/pull/1111) and
  [#1138](https://github.com/leanprover/cslib/pull/1138); the branch's `IterateWhile` supersedes
  [#1112](https://github.com/leanprover/cslib/pull/1112). Shared encodings are coordinated in
  [#611](https://github.com/leanprover/cslib/issues/611) and
  [#590](https://github.com/leanprover/cslib/issues/590) (`TapeEncodable`). Markers at
  `@9cce4cc7` name an unpublished later revision of the branch, so `upstream_sync.py` reports them
  as moved until it is published.
* **Complexity classes.** [#767](https://github.com/leanprover/cslib/pull/767) proposes
  language-indexed `DTIME`/`DSPACE`. Check it before adding space-to-time inclusions or overlapping
  classes; once it lands, derive the local encoded-instance `DSPACE`, `L`, `DTIME` and `EXP` from
  it (see `Classes/Space`).
* **Probability and security games.** Local copies of
  [#1129](https://github.com/leanprover/cslib/pull/1129),
  [#1062](https://github.com/leanprover/cslib/pull/1062),
  [#1069](https://github.com/leanprover/cslib/pull/1069),
  [#1070](https://github.com/leanprover/cslib/pull/1070) and
  [#1072](https://github.com/leanprover/cslib/pull/1072). Coordinate `PFunctor.FreeM` with
  [#1086](https://github.com/leanprover/cslib/pull/1086)–[#1089](https://github.com/leanprover/cslib/pull/1089),
  the arbitrary-type metric with [#1065](https://github.com/leanprover/cslib/pull/1065), and
  `Crypto/Primitives/PRG/Game` with [#1071](https://github.com/leanprover/cslib/pull/1071).
* **Decision trees.** Align `Computability/DecisionTree` with
  [#925](https://github.com/leanprover/cslib/pull/925), and coordinate its certificate follow-up
  `D ≤ C₀ C₁`.
* **Word RAM and algorithm models.** `Computability/WordRAM` adapts Erik Demaine's
  [lean-trominoes](https://github.com/edemaine/lean-trominoes); coordinate submission and
  attribution with him. Before submitting WordRAM, GenericRAM or `DataStructure/StateTransition`,
  coordinate with Shreyas Srinivas's [#685](https://github.com/leanprover/cslib/pull/685) and his
  Algolean register models, and with the merged [#401](https://github.com/leanprover/cslib/pull/401).
* **PAC learning.** `PACLearning/Realizable` is an unchanged copy of
  [#858](https://github.com/leanprover/cslib/pull/858).
  [#966](https://github.com/leanprover/cslib/pull/966) would make `sampleComplexity` and `vcDim`
  `ℕ∞`-valued; if it lands, restate the bounds in `FiniteClass`, `VCUpperBound`,
  `AgnosticFiniteClass`, `AgnosticVC` and `GrowthFunction`. `PACLearning/SampleComplexityLower*`
  vendors the EHKV `Ω(d/ε)` lower bound from
  [`feat/pac-learning-ehkv-headline`](https://github.com/SamuelSchlesinger/cslib/tree/feat/pac-learning-ehkv-headline);
  submit or update it through that branch, not as a competing copy, and reconcile `VCLowerBound`
  and `FundamentalTheorem` with its names before submitting them.
* **Tree decompositions.** Upstream `SimpleGraph/TreeDecomposition` through Justin Lai's
  [mathlib4#38334](https://github.com/leanprover-community/mathlib4/pull/38334),
  [#39939](https://github.com/leanprover-community/mathlib4/pull/39939) and
  [#39864](https://github.com/leanprover-community/mathlib4/pull/39864), not as a competing
  candidate; the module docstring records the differences. Renaming to match the unmerged PRs is
  not required.
* **Oracle codes.** Upstream `Foundations/Computability/{RecursiveInCode,RecursiveInEvalnPrimrec,KleenePost,KleenePostJump}` by reconciling with
  [mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973) (oracle codes, a
  relativized `evaln` and the jump), not by competing with it; the module docstring records the
  design differences. The prefix-based `evaln`, the use principle and `KleenePost` / `KleenePostJump`
  are what that PR lacks.
* **Withdrawn submissions.** The redos of
  [#1099](https://github.com/leanprover/cslib/pull/1099)–[#1101](https://github.com/leanprover/cslib/pull/1101)
  (`Circuit/Boolean/{PPoly,MachineSimulation,PolynomialTime}`) should answer the review requests
  for abstract word encodings and textbook sources. The review of
  [#874](https://github.com/leanprover/cslib/pull/874) (series #869, #871–#875) asked for
  composition above the configuration level; `TransformsTapes`-style specifications are the local
  answer.

Earlier coordination notes, placement suggestions and the pre-release deprecation list are in
[`UPSTREAM.md` at its retirement](https://github.com/cslib-community/cslib-frontier/blob/0bbbdafaf2d44d77661d080b1edec5daac176cab/UPSTREAM.md).
