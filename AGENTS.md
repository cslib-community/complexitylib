# Project Instructions

cslib-frontier is the frontier formalization library for **cslib** (`leanprover/cslib`): a Lean 4
library covering computer science generally, including algorithms and data structures,
complexity, cryptography, logic and models of computation. Library modules must be upstreamable
unchanged apart from rewriting `CslibFrontier.` → `Cslib.`. General mathematics destined for Mathlib
and local project scaffolding are documented exceptions, recorded in each module's `-- upstream:`
marker.

Read the pinned cslib `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md` in
`.lake/packages/cslib` (or a checkout at the same revision). Follow its mathematical, API and
style conventions. This repository's workflow, validation and test layout are defined here and
in `CONTRIBUTING.md`; when submitting upstream, follow that repository's current process.
`ROADMAP.md` records outstanding directions; `CONTRIBUTING.md` (Upstreaming) lists live upstream
coordination threads.

At the start of work and when resuming, read the current checkout's instructions. Old task text
and copied policy snapshots may describe superseded decisions. Surface material conflicts with
current user instructions rather than silently following stale policy; explicit user directions
control. Keep policy changes focused on recurring problems, and update linked guidance and
templates together instead of adding another exception for each incident.

## Writing in issues and PRs

Write for human collaborators. Start with the point; use short paragraphs or a small flat list.
Use headings, tables and checklists only when they make the content easier to read. Give technical
detail where it explains a finding or decision; omit routine inspection narratives and boilerplate.

Small PRs usually need one or two paragraphs plus validation/review links and a brief AI
disclosure. State what changed, why, and important limitations. Keep evidence in one place;
link to it instead of copying full reports, hashes or logs across threads.

Comments should add a finding, answer, decision, blocker or useful handoff. Keep CI polling and
internal agent discussion out of public threads. Reply directly to questions and fixes; a short
"Fixed in <commit>" is enough when the change is clear. Be courteous, welcome disagreement, and
do not imply that an agent review is human review.

## Agent roles and task ownership

Each agent works as either a **coordinator** or a **worker**. Follow the role assigned by the
human or coordinating agent; otherwise default to worker. State your role when starting work.
Changing roles does not make an author eligible to approve their own changes.

Use parallel agents where their work can proceed independently. Give each a role, clear scope
and distinct ownership, branches and mutable build outputs. The delegating agent tracks the
work and brings it to completion. When review or integration is the bottleneck, prioritize
requested fixes, reviews and landing existing work before starting more PRs.

Use issues for substantial tasks, dependencies and remaining objectives; a small fix may use its
PR as the durable task record. Search existing issues and PRs before creating a duplicate.
Record smaller delegated subtasks in the parent task. Split work into independently useful,
reviewable changes; batch closely related mechanical fixes when they share a contract and
validation. Do not create a separate issue or PR for each incidental cleanup.

### Completion and scope

Code quality is part of the acceptance criteria. Authors must resolve avoidable duplication,
unnecessary proof plumbing, misplaced shared infrastructure and incomplete migration cleanup
affecting their changes and clients before requesting approval. Passing CI or preserving theorem
statements does not discharge this work. Deferral is exceptional under
[Improving library ergonomics](#improving-library-ergonomics).

Optimize for trustworthy, reusable results, not the number of closed issues or merged PRs.
When narrowing a task, preserve its original objective and record the bounded deliverable and
remaining gap prominently. A restricted model, conditional result, or partial theorem does not
complete a broader objective. Do not silently retitle an ambitious issue into an easier completed
task.

Distinguish these dispositions in the issue:

- **Completed:** the agreed acceptance criteria are satisfied.
- **Milestone completed:** a bounded deliverable is finished; link the remaining objective.
- **Not planned (dropped):** work is intentionally stopped; preserve its results, explain what
  remains unproved, and remove the direction from `ROADMAP.md`, which has no deferred tier.

Close a milestone issue as completed when its own criteria are met. Keep the broader objective
open, or, when authorized to drop it, close it as not planned and link the completed milestone.
PR descriptions must distinguish mathematical progress from infrastructure, refactoring, and
documentation progress.

### Durable records

When there is an issue, it owns scope, ownership and remaining work; the PR owns the final
change, validation and review. For small fixes without an issue, the PR holds both. Link between
records instead of mirroring reports. Record tested and reviewed revisions once,
in GitHub review/CI metadata or a concise PR record; link reusable evidence rather than reproducing
it. Without a PR, record evidence in the commit description and link it from the issue.
A local path alone is insufficient for a handoff.

At integration, briefly state what landed and any remaining gap. Keep the full objective visible
when a milestone completes only part of it.

### Workers

1. Before substantial implementation, claim the existing issue or create one with concrete scope
   and completion criteria. Identify your agent/session and branch in the task record; assign
   the issue when possible. For a small fix, record this in the PR instead. A shared GitHub
   account does not identify the active agent.
2. Update the task when scope changes, a blocker needs help, work is handed off, or you stop.
   Give the state and next step, linking code or evidence. Keep unchanged polling and internal
   agent discussion out of public threads. Do not promise unattended updates after stopping.
3. Before taking over, inspect the issue, linked PR, recent commits and available activity
   evidence; contact the owner or coordinating agent. Silence or elapsed time alone does not
   release ownership. Explicitly released work is available immediately; a coordinator may
   reassign stale work after checking activity and notifying the owner. Preserve work and credit,
   resolve overlapping claims before editing, and check ownership when returning.
4. Implement, self-review and validate. Assess both manuals for every change and update affected
   instructions, reference sections and checked examples in the same change, following
   [the manual requirements](CONTRIBUTING.md#maintaining-the-manuals).
5. Open a PR with validation and limitations; link its issue when there is one and request
   coordinator review. Record the handoff once. Awaiting review is not abandoned work. Keep
   linked issues open until integration or an explicit disposition.
6. Address requested changes on open PRs before starting more work. Request review of the delta
   after fixes; release work explicitly if unavailable. Do not approve or merge your own PR.

Plain comments such as `active`, `blocked`, `available`, `awaiting review` and `changes requested`
are sufficient; no custom labels or recurring heartbeat comments are required.

### Coordinators

Reviewing submitted PRs is the highest priority. Keep reviews moving alongside other work.

When choosing work, give simplification and usability real priority alongside new mathematics:
replacing repeated proof plumbing with a small lemma, finishing a migration and removing what it
superseded, removing unused scaffolding, fixing recurring build or search problems, and making
results easy to find, import and apply. Choose these from the friction met during ongoing work,
and carry each improvement through to the clients that benefit. In review, ask what the next
person will no longer have to figure out; the answer should be visible in the code, examples or
tooling.

- Read the PR and existing reviews. Arrange review of uncovered questions under the review cycle
  below; do not commission a fresh review merely because a new coordinator arrived.
- Give a clear verdict and a useful next step. Link requested changes from the task issue when
  needed for handoff; resolve unavailable ownership using the worker rules above.
- Resolve ownership and dependency conflicts, and help stale tasks reach a useful next step.
- Require review of both the Operator's Manual and the Agent Operator's Manual, including any
  reason that no edit is needed. Make this part of reviewing and integrating each change.
  Check affected `ROADMAP.md`, the [results inventory](results/README.md), upstream markers, the
  coordination threads in `CONTRIBUTING.md` and other documentation.
  Preserve source credit and the distinction between a completed milestone and its open objective.
- Merge only with required validation and independent review of the current revision. Reviewers
  queue the heads they approve ([Approve and queue](#approve-and-queue)); coordinators queue any
  approved head still waiting and keep the queue moving: do not treat a PR as done when it is
  merely queued. Monitor queued batches until they land on `main`, merge `main` into or re-queue
  PRs ejected by conflicts or transient failures, sequence broad tree-wide refactors so they do
  not stall smaller PRs behind cold cache rebuilds, and diagnose and fix merge-queue or CI
  bottlenecks when the queue jams. The queue squash-merges: a stacked PR that edits lines a lower
  PR introduces conflicts with that PR's squashed commit and is ejected, so queue it once the
  lower PRs land (GitHub then retargets it to `main`) and it has merged `main`. Close completed
  issues and link any remaining work once the change lands.
- For your own implementation, follow the worker rules and obtain non-author review under
  [Review cycle](#review-cycle). Changing roles does not make self-review independent.

If a shared GitHub account prevents formal approval, use one brief PR comment naming the reviewer
agent/session, revision and verdict. This is agent review, not platform or human approval.

## Working on changes

Use ordinary Git branches or isolated worktrees for substantial changes. Preserve other
contributors' work and keep mutable build outputs separate between worktrees. Agree substantial
scope through Issues or pull requests, and split large developments into independently useful,
reviewable milestones. Record unfinished work in `ROADMAP.md` without claiming it complete.

Contributors self-review and validate their changes. Maintainers arrange independent API and
correctness reviews of the exact revision before integration; reviewers report findings, and
fixes receive review of the affected delta under the review cycle below. Preserve source credit
and record contributors and review results in the pull request or commit description.

### Repository isolation

Treat the user's checkout and shared Git object database as protected infrastructure. Ordinary
worktrees share their Git object database. Never import reconstructed Git objects, install shallow
boundaries, or experiment with history repair in that shared database. Use an independent
repository with its own Git object database for such operations.

Before Git recovery or nonstandard object manipulation, verify the actual Git common directory,
object alternates, and storage sharing. The experimental repository must not use the shared
database through a gitfile, alternate object directory, or hard-linked object files. Never delete
objects, refs, worktree registrations, or metadata belonging to another session. Worktrees also
share one stash stack, so `git stash pop` can apply and drop another session's entry: never push,
pop, apply or drop stash entries in a shared checkout or its worktrees. Keep work in progress as a
commit on your own branch or as a patch file in your scratch directory
([procedure and recovery](manual/workflows/agent-operations.md#isolate-work-and-build-outputs)).

Keep mutable build outputs separate. Integration experiments must be contained so their failure
cannot damage the user's checkout or another worker's repository.

Machines are shared between agents. Stop only processes and tasks you started, by PID or task
ID; never use pattern-based kills such as `pkill -f`, which also hit other agents' builds. Keep
scratch files under a directory or name unique to your agent. Concurrent Lean builds can
exhaust the host's file handles before its processors; agree on a limit on concurrent builds
(see [the troubleshooting chapter](manual/workflows/troubleshooting.md#diagnose-too-many-open-files-in-system)).

### Placement and reuse

Place reusable definitions and general lemmas in the lowest suitable mathematical module.
Specialized theorem modules should import their prerequisites. During review, look for general
APIs buried in a particular application or proof. Extract them to their natural shared home and
update the affected clients in the same PR, applying the migration policy below. A second
application importing the first for general infrastructure is a concrete signal to do this.
Keep unrelated architectural redesign out of scope; use the exceptional deferral rule below when
a technical dependency prevents completing the extraction.

Do not prove a lemma that the library, CSLib, Mathlib or core already has, even privately or by
re-deriving it inline inside another proof: use it, or make a private original public. After a
build, `python3 scripts/parallel_defs.py --theorems` lists the theorems a change adds or modifies
whose statement already exists; CI posts the same notice. It cannot see a fact re-derived inside a
proof, so search for an existing lemma first. When a proof you add or change needs a substantial
argument that another proof makes, derive it once; the
[library quality standard](CONTRIBUTING.md#library-quality-standard) says when a shared lemma pays.

"Lowest suitable" does not mean the most widely imported file. Adding a public declaration changes
a module's public interface and can invalidate downstream build artifacts, even for clients that do
not use the new declaration. Prefer a small topic module imported by its consumers over appending
to a hub such as `Foundations/Data/List/Basic.lean` or `Probability/PMF.lean`; #569 records the
measured fan-out. Exposed definition bodies (`@[expose]`) belong to the interface too, so expose
only what downstream proofs must unfold.

### Improving library ergonomics

When work exposes library friction, improve the relevant API, lemma, proof strategy, documentation
or automation in the original PR and carry the improvement through to its affected clients. Search
existing APIs in this repository, Mathlib and CSLib before adding or re-proving anything, including
private helpers. Making a duplicate private does not resolve duplication.

Reviewers must consider whether a different statement, representation, invariant, decomposition or
proof strategy would make the mathematics more natural to state, prove and apply. Look beyond
local tactic edits: applying an existing theorem, choosing a better induction argument or adding a
small shared lemma can remove whole blocks of encoding, case or state-update bookkeeping. Assess
the resulting client proofs and required imports as well as the new API. Preserve the mathematical
claim, models, encodings, quantifiers and independent resource bounds when simplifying.

Require a concrete benefit from a proposed alternative: representative checked usage or a focused
proof comparison explaining what becomes clearer or easier. Prefer the smallest generally useful
change that fits the mathematical API and upstream design. Challenge speculative abstractions and
arbitrary conventions; proof length alone is not a finding, and a personal preference does not
justify rewriting an otherwise clear argument.

Defer cleanup only when a specific technical dependency or independently substantial redesign
prevents completing it with the PR. The reviewing coordinator must explicitly accept the reason,
and a linked issue must name the remaining declarations, affected clients, proposed approach and
responsible owner. A separate prerequisite PR may keep review focused, but the dependent PR waits
for it. Creating a follow-up issue or citing scheduling pressure does not discharge cleanup that
can be completed with the change.

Keep the evidence proportional. A small improvement needs a short explanation and a checked
client; broader API changes need representative affected clients and an in-repository migration
plan. Investigate elaboration time and other performance costs when material, without requiring
a benchmark campaign or separate design study for every small improvement.

### Check the API through its callers

Before handing off a changed API or reuse refactor, inspect a representative caller and the
nearby implementations of the same idea. Reviewers repeat this check against the final change:

- **Named access and semantic facts.** Use record fields or existing accessors in public
  statements. When callers decode a Boolean matcher, unfold an embedding's coordinate arithmetic,
  or rebuild field-projection certificates, provide the reusable characterization, range fact or
  generated certificate they need and use it in the caller. Preserve the encoding layout and
  resource bounds when migrating records; check a caller of the generated `enc_structure` rules.
- **One implementation of shared behavior.** A game or algorithm should call its named handler
  instead of repeating the same dispatch or transition code in its definition and proofs.
  Different representations may need distinct implementations; keep their differences explicit
  and connect them with the appropriate simulation or conversion lemma.
- **Shared mathematics across representations.** Before repeating an argument in a sibling
  module, look for a general statement and an existing bridge, such as PMF integration against
  its induced measure. Derive the specialization when the bridge preserves the hypotheses and
  intended dependencies. Put shared facts in a small topic module and migrate the existing
  consumers together; do not create an abstraction whose callers must reconstruct the proof.
- **Public API by purpose.** Keep expected properties of public objects available, including
  matcher characterizations and embedding range facts. Keep one-proof wrappers around casts,
  cache layouts or intermediate states private. Inspect references and automation before changing
  visibility, but do not use a zero reference count alone to remove useful mathematical API.

The handoff should identify the representative caller and the reasoning or representation work
it no longer repeats, or explain why separate implementations remain necessary. A concise
before/after example or source reference is enough; no separate audit report is required.

## Lean development: use the Lean MCP server first

Bootstrap a cold checkout with `scripts/cache/ensure.sh` before Lean elaboration or building.
Retry when needed artifacts are missing or toolchain/dependency changes require new ones;
a new commit or branch switch alone does not require a manual bootstrap if outputs are warm.
MCP's `lean_build(fetch_cache=true)` fetches Mathlib's cache, not cslib-frontier's. Cache misses
or download failures leave Lean to compile missing outputs. The helper's actual retry behavior
and opt-out for warm local builds are documented in [the cache guide](scripts/cache/README.md).

Use MCP goal inspection, diagnostics and theorem search while iterating; reserve builds for
validation checkpoints. `scripts/build.sh [Lake build arguments]`, `scripts/check.sh` and
`scripts/worktree.sh create` run the same bootstrap automatically. Bare `lake` and MCP commands do
not invoke it. If MCP tools are unavailable, say so and use the smallest shell check.

Use `scripts/worktree.sh` for isolated worktrees; follow its
[cache and isolation guidance](scripts/cache/README.md). Exported API changes can rebuild
dependents; proof edits can too when axiom dependencies change or a client uses `import all`.
See [the module-system guidance](CONTRIBUTING.md#public-surface-under-the-module-system).

## Validation sequence

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` first runs the live manual checker and its tooling tests, then restores
optional caches and runs every required step of CI's `ci-checks` job that can run locally, with
CI's commands (`scripts/full_check.py`): these six Lean gates, the Python tooling tests, source
hygiene, the encoding readability and projection chain ratchets, documentation pins, and the
post-build tidy statement ratchet, result registry and changed-file lints. Changed-file checks
compare with the merge base of `origin/main`, or of `--base REF`. `scripts/full_check.py` records
why each remaining step stays CI-only (advisory notices, cache plumbing, steps that need GitHub
context), and its test fails when the workflow gains a step that is neither mirrored nor recorded
there, or when a mirrored step runs a line or sets an option that the local run does not repeat.
After the Lean gates, full and quick modes also re-elaborate the changed library and test files
whose outputs Lake restored from the shared local artifact cache, which keeps no warnings
([troubleshooting](manual/workflows/troubleshooting.md#diagnose-warnings-that-only-ci-reports)).
Both full and quick modes require the manual checks; these stdlib-only checks need no PDF tools or
generated research data. They catch source/link drift and malformed visual markup; they do not
replace the required review of both manuals' meaning and usability.
For Lean, dependency or build changes, all of these must pass on the final source revision before
integration. A successful hosted run covering that revision supplies full validation; do not
repeat it locally merely to satisfy a second reporting requirement. Use local full validation
(`scripts/check.sh`) when hosted coverage is unavailable; changes to validation machinery also
need direct checks of the changed behavior. Required CI and merge-group checks still apply.

During development, check affected modules and representative clients before requesting review;
a PR may use CI for the full run. For documentation-only changes, check consistency, links and
any Lean examples introduced; a local whole-library rebuild is unnecessary.

For the edit loop, `scripts/check.sh --quick [--base REF]` builds changed Lean modules and their
transitive importing clients, then checks import aggregates. The comparison uses the merge base
with local `origin/main` by default, including committed, staged, unstaged and untracked changes;
it does not fetch. It also runs source hygiene on the changed library and test files and, when a
library module changed, the encoding readability and projection chain ratchets: all read only
sources and take seconds. Quick mode lints only the affected library modules, skips the global
test/style/init-import gates and the post-build audits, which need whole-library outputs, and is
not full validation. Non-Lean changes, deletions/renames, changed aggregates, unsupported layouts
and ambiguous change/import analysis fall back to the full check. The exceptions are the
ratchet baselines `scripts/encoding_readability_baseline.json` and
`scripts/projection_chains_baseline.json`, which no Lean gate reads: a change to one runs its
ratchet instead. Quick success alone does not satisfy the full validation requirement above;
documentation-only checks need not invoke quick mode.

`lake exe mk_all` regenerates `CslibFrontier.lean` after adding a file. New test files go in
`CslibFrontierTests/`; the test library is built from a Lake glob, so there is no aggregator to update.

## File rules

1. **Path and namespace mirror cslib.** `CslibFrontier/Foundations/Data/Encoding.lean` is destined
   for `Cslib/Foundations/Data/Encoding.lean`; multi-tape machine files use the upstream root
   namespace `Turing`, everything else `Cslib.*` as upstream does.
2. **File template:** use the Apache header below, `module`, an `-- upstream:` marker,
   `public import` for API dependencies and plain `import` for proof-only dependencies. Add a
   module docstring describing the actual API, with applicable `## Main definitions`,
   `## Main results` and `## References` sections; omit empty sections. Use `public section`
   with `private` helpers, or per-declaration `public`. Add `@[expose]` only to definitions
   whose bodies downstream clients need to unfold; do not default to blanket exposure.
   ```lean
   /-
   Copyright (c) <year> <authors>. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: <authors>
   -/

   module
   -- upstream: candidate

   public import CslibFrontier.Init

   /-!
   # <Module topic>

   <Purpose, public API and mathematical sources.>
   -/

   public section
   ```
   In a new file, `<authors>` names (a) the originator(s) of the issue or proposal the file
   implements: the person named in the issue's "Originated by" field when someone wrote the issue
   on their behalf, and otherwise the issue's author; and (b) the person whose agents did the
   implementation (the human, not a fleet or bot account). The rule applies going forward, not
   retroactively: existing headers stay unless someone asks for a correction. A port still keeps
   the original authors (rule 3).
3. **Upstream marker** values: `candidate`, `submitted #N @SHA` (a copy of an open cslib pull
   request at its head `SHA`), `vendored <owner>:<branch> @SHA (unsubmitted)` (a copy of a branch
   of a contributor's cslib fork that has no pull request yet), `merged @SHA` (a deprecated shim
   for a module that cslib provides from its commit `SHA`; see below), `local-only (reason)`.
   Nothing is `local-only` without a reason; valid reasons are project scaffolding and tests of
   local-only files.
   When the pin adopts a module, whether it was upstreamed from here or copied from upstream
   work, the commit that bumps the pin replaces the file with a deprecated shim instead of
   deleting it, so that downstream `import CslibFrontier.X` keeps working with a warning. The shim
   keeps the file's copyright header and otherwise contains only the following, where `Cslib.X`
   is the upstream module and the date is that of the pin bump:
   ```lean
   module -- shake: keep-all
   -- upstream: merged @SHA

   public import Cslib.X

   deprecated_module "upstreamed to cslib" (since := "YYYY-MM-DD")
   ```
   `deprecated_module` is Lean's core command, and Mathlib writes its stubs the same way:
   importing the shim warns and names `Cslib.X` as the replacement. Because `--wfail` builds fail
   on that warning, the same commit points every in-repository import at `Cslib.X`; only the
   generated `CslibFrontier.lean` imports the shim, under its `-- deprecated_module: ignore`
   pragma. Shims are the one exception to the rule against compatibility wrappers under
   [Proof hygiene](#proof-hygiene). Delete a shim once its `since` date is six months old,
   Mathlib's window for removing deprecations; a pin bump that moves or removes `Cslib.X`
   repoints or deletes the shim itself.
   A port keeps the authors of the files it is ported from: v1's PCP internals, Sipser–Lautemann
   and containment internals are by Bolton Bailey, so their ports carry
   `Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger` and `Authors: Bolton Bailey, Samuel
   Schlesinger`; ports of Christian Reitwiessner's work carry his name likewise. Check the v1
   file's `Authors:` line before porting.
4. **Every module publicly imports `Cslib.Init`** (through `CslibFrontier.Init`); the test driver
   runs `checkInitImports`.
5. **Reuse upstream first.** Before defining anything, search cslib (`.lake/packages/cslib/Cslib`,
   or the local `../cslib/Cslib` checkout) and the in-flight PRs recorded in source markers, and
   consult the coordination threads in `CONTRIBUTING.md` (Upstreaming). A thin local copy of an
   unmerged upstream PR (or an unsubmitted branch of an upstream contributor) is allowed at the
   mirrored path, keeping the
   original authors and declaration names, marked `-- upstream: submitted #N @SHA` (or
   `vendored …`). A copy holds only what the pinned cslib lacks: when a PR modifies an existing
   cslib file, the copy contains just its additions. When the pin adopts the merged work, the
   copy becomes a deprecated shim (rule 3).
6. **Bit strings.** Declarations about bit strings and the cube `ι → Bool` (operations, sampling,
   Fourier analysis, sensitivity, influence, codes) live in `Cslib.BitString`; only the named
   Boolean functions `parityOn`, `parity`, `threshold`, `majority`, `strictMajority` sit in `Cslib`
   beside cslib's `BooleanFunction`. Bit strings add with `+` (Mathlib's `BooleanRing Bool`),
   single bits with `^^`.
7. **Citations.** Cite textbook sources in docstrings via `references.bib` keys
   (`[AroraBarak09]`, `[Papadimitriou94]`, `[Sipser2013]`, `[Jukna2012]`, …). Add new entries in cslib's
   format at their place in key order (`scripts/check_hygiene.py` checks the order and that every
   cited key has an entry), keeping bibliography and project-documentation changes in focused
   commits.

## Staying current with upstream

Keep the cslib pin on an upstream `main` SHA. Coordinate updates in focused dependency PRs,
fixing breakage in the same change; update it within another task when that task needs new
upstream code or turns a merged module into its shim. Merely inspecting upstream does not
require a pin bump.

Run `scripts/upstream_sync.py` during synchronization work. Inspect changed, merged or closed
upstream PRs against source markers, `-- vendored:` comments and module docstrings; preserve
documented local adaptations and contributor work rather than blindly replacing copies. When
adopting merged work, advance the pin past it and, in the same commit, replace the superseded
local file with its deprecated shim ([file rule 3](#file-rules)). Record unresolved decisions in
the module's marker or docstring, the coordination threads in `CONTRIBUTING.md`, or a linked issue
instead of expanding an unrelated PR.

## Proof hygiene

These rules exist for readability and robustness. When following one would make a particular
proof or statement worse (longer, harder to read, or working against the automation), deviate,
say why in the PR, and propose amending the rule. Reviewers judge a deviation by the rule's
purpose, not its letter.

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment. A
  `maxHeartbeats` above the 200000 default, or zero (unlimited), also needs a reviewed entry in
  `scripts/heartbeat_allowlist.txt`, which `scripts/check_hygiene.py` enforces and keeps
  shrinking; prefer reducing the proof's cost.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`, so that later steps do not depend on the shape of a
  `simp` normal form, which changes as simp sets grow. A `simp` whose result is closed by a
  finishing tactic that does not depend on that shape (`omega`, `linarith`, `nlinarith`,
  `norm_num`, `ring`, `grind`, `tauto`), as in `simp [h]; omega`, counts as terminal, as in
  Mathlib's flexible-tactic linter.
- Definitions as terms, not `by` blocks, where possible.
- Prefer `do` notation for sequential monadic computations, including probabilistic experiments
  in theorem statements. Keep explicit `bind` in laws about bind and proof steps that use those
  laws directly, and for operations such as `PMF.bind` between different universes that the standard
  monad interface cannot express. Retain concise point-free composition and maps when naming an
  intermediate value would not improve readability. Check affected proofs when changing notation.
- Before the first supported release, do not add deprecated aliases or compatibility wrappers
  for renamed, moved, removed or privatized declarations. Update all in-repository clients
  (library, tests, results inventory and guide) and remove the superseded interface in the same change.
  Remove obsolete aliases as part of the relevant migration, not unrelated cleanup. Revisit
  compatibility guarantees before supporting external consumers.
- `CslibFrontierTests/Axioms.lean` audits all declarations stored in imported `CslibFrontier` modules
  for dependencies beyond `propext`, `Classical.choice` and `Quot.sound`. Because that audit
  already covers the standard set, add a named `#print axioms` guard only when a result is meant
  to depend on fewer axioms than these three, for example a choice-free result; place it in the
  epic's own test module.
- Watch for vacuous hypotheses: when a structure bundles bounds, provide at least one instance in
  the test suite.

## Review cycle

Maintainers arrange independent review of correctness and API quality (naming, reuse, placement,
documentation and source credit). One non-authoring reviewer may cover both. Add a reviewer for a
specific uncovered question or needed expertise, not to reach an approval count. Contributors do
not need a particular agent installation.

Read the actual definitions, statements and proof arguments, and inspect representative clients.
For substantive mathematics, explain briefly what is proved, its limiting hypotheses/model/resource
conventions, and a checked instance or edge case.
For a refactor, check declaration preservation, imports and a client using the intended API.
For changed APIs and reuse refactors, follow [Check the API through its callers](#check-the-api-through-its-callers):
inspect the actual caller and relevant sibling implementation, including generated certificates
and any representation bridge. Compilation alone does not check placement or duplicated behavior.
Check new and changed statements against
[Structures for domain objects and records](#structures-for-domain-objects-and-records) and
[Encodings in statements](#encodings-in-statements).
Read new and changed proofs against the rest of their file and nearby modules, not only the diff:
a new copy of an argument the library already makes is a finding when the
[library quality standard](CONTRIBUTING.md#library-quality-standard) says a shared lemma pays.
Lean acceptance under audited axioms does not establish that a definition matches its intended
mathematics; state material limits of the review.

Before approving library changes, read the **Parallel-definition**, **Duplicate-statement** and
**Repeated-proof-block** notices in the CI job summary or step logs for the reviewed revision. Inspect both
declarations or proof blocks for each relevant candidate. Record its resolution by reuse or
generalization, or the concrete mathematical or API difference that justifies keeping both; link
an existing author explanation rather than duplicating it. Locally, after a build, use
`python3 -B scripts/parallel_defs.py --base REF` and the same command with `--theorems`;
`python3 -B scripts/proof_copies.py --base REF` compares source proof blocks. `--limit N` expands
truncated reports. Resolve skipped or incomplete scans, or record their coverage limits and
perform targeted source checks. A successful exit, an empty report or a private declaration is
not evidence of uniqueness; the tools supplement source search and semantic review.

Review of both manuals is mandatory for every change. Follow
[Maintaining the manuals](CONTRIBUTING.md#maintaining-the-manuals): check the impact assessment
against the final revision. Check affected codebase procedures and examples from the Operator's
Manual's documented starting point; a human should be able to perform the task by hand, and an
agent should be able to reuse the account without reconstructing it from conversations. Check
human direction, roles and handoffs in the Agent Operator's Manual when the workflow changes.
A passing link or excerpt check does not replace this review.

Review API and proof quality for private helpers as well as public declarations, following
[Improving library ergonomics](#improving-library-ergonomics). Request changes for concrete,
avoidable complexity or duplication affecting the PR; reserve nits for optional preferences.
Use inline comments for local findings, explain the problem and a concrete change or question,
and group related points. Authors may disagree: discuss the technical reason and settle the point.

After fixes, review the delta and affected reasoning. Revisit more of the code when a change
invalidates earlier conclusions. Reuse existing reviews after verifying their scope and source
identity; do not repeat a full review of unchanged code. Before merging, confirm that the current
revision is covered and required validation passes.

A coordinator may fix conflicts and review findings directly when authorized to edit the branch.
Check its head and coordinate ownership first; add commits on top, or announce a necessary rebase.
Preserve author credit and record the delta and validation. Fixing a PR does not make self-review
independent.

Existing independent approval can carry across a mechanical delta when the coordinator verifies
that it preserves meaning, exported availability, attributes, imports and automation behavior,
and checks affected clients. Record that limited carry-forward decision. A typo fix may qualify,
and [Restacks](#restacks) gives a mechanical check for merging `main` or rebasing; a proof repair,
privatization, changed test coverage or a conflict resolution that changes the PR's own lines is
not automatically mechanical. Changed reasoning, API, source claims or security claims, and
uncertain cases, need fresh non-author review of the affected delta.

A non-authoring agent may independently review work from the same coordinator or account. It must
inspect the source and evidence in a separate review context and reach its own verdict; an
implementation agent's self-check or a coordinator's summary is not independent review. Reviewers
who participated in the implementation or its design cannot supply that review. The coordinator
may integrate after this review and required validation, but must not present it as self-approval
or human review. Add expertise for uncovered questions, not an approval count or agent affiliation.

Finish with a short approval or a clear request for changes. A substantive concern may need a
long explanation; a clean review does not need a checklist of everything inspected. Record the
reviewed revision, meaningful findings and resolutions once in the PR, following
[CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).

CSLib examples: [focused fixes and replies](https://github.com/leanprover/cslib/pull/1145),
[an architectural suggestion kept separate from approval](https://github.com/leanprover/cslib/pull/1120),
and [API review with explicit nonblocking nits](https://github.com/leanprover/cslib/pull/923#pullrequestreview-5560941186).

### Approve and queue

Approving a PR's exact current head and queueing it are one step. A non-authoring reviewer with
write access who approves runs `python3 scripts/queue_pr.py <PR> <approved head>`, which queues
exactly that head once the required check has passed there; `--wait 30` waits up to 30 minutes
for a check that is still running. Write access is sufficient authority to queue a head approved
under this cycle. Approve without queueing, and say why in the approval, when:

- human review has been requested in the PR, its comments or a linked issue; queueing is then left
  to that human or to whomever they name;
- the approval names a hold, such as an unlanded lower PR, a migration or an upstream dependency;
  queue once the hold clears.

The script refuses a head other than the approved one, a draft, a PR not based on `main`, a
conflicting PR and failed checks. When the reviewer cannot queue, any other non-author agent with
write access may run the same command for the approved head; coordinators sweep for approved heads
still waiting. Authors do not queue their own PRs.

### Restacks

Merge `main` into a PR only when it conflicts with `main`, needs a change on `main` to pass CI, or a
lower stacked PR has landed. The merge queue tests every PR on top of the current `main`, and `main`
does not require branches to be up to date, so refreshing an approved PR only replaces the approved
head. After the merge, regenerate the import aggregates with `lake exe mk_all`, or let the opt-in
[`leanagg` driver](CONTRIBUTING.md#proposing-and-contributing-work) merge them and then check them
with `lake exe mk_all --check`, since the driver sees only the aggregates and not the merged tree;
never trust a `merge=union` result, which keeps deleted imports and can misorder added ones.

GitHub declines every push to the branch of a PR that is in the merge queue ("protected branch
hook declined"), even when its entry is `UNMERGEABLE`. Whoever restacks a queued PR, by hand or
with `--push` below, first removes it with **Remove from queue** on the PR page or:

```bash
gh api graphql -f id="$(gh pr view <PR> --json id --jq .id)" -f query='
  mutation($id: ID!) { dequeuePullRequest(input: {id: $id}) { mergeQueueEntry { state } } }'
```

Dequeueing merges nothing, so the author may do it; the new head is queued again only by a
non-author, once the `check_restack.py` check below passes or the delta is reviewed.

When the only conflicts with `main` are in the aggregates or `references.bib`,
`python3 scripts/restack_mechanical.py <PR> --approved-head <approved head>` does the whole restack
without running the PR's code. It requires the `check_restack.py` check below to pass for the
current head, merges `origin/main` with both drivers, writes the aggregates as `lake exe mk_all`
would for the merged tree, and runs the check on the result, both times from a checkout of
`origin/main`. It refuses any other conflict and is a dry run unless given `--push`, which pushes
the merge only when the check passes and the PR's branch still points at the head it merged. It
never queues and never comments: post its result line, and queue the new head under the rules
below once CI passes.

A branch that forked before the module root was renamed from Complexity to CslibFrontier is
restacked with `python3 scripts/rename_module_root.py --restack` (from a checkout of current
`main`; `--onto` names the restacked head of a lower stacked branch). It merges the rename and
converts the branch's own module names and paths; `--verify-carry` compares the result with
the approved head. See the script's documentation.

A restack keeps its approval when `python3 scripts/check_restack.py <approved head> <new head>`
passes and CI passes at the new head. The script replays the approved change onto the `main` that
the new head is based on, which is what the merge queue would have built from the approved head,
and passes only when the new head's tree is exactly that replay. The one exception is the
`mk_all` import aggregates, which must instead be exactly what `lake exe mk_all` writes for the new
head's tree. A conflict in the replay elsewhere, and any other difference, fails it. The replay
merges `references.bib` entry by entry, as `scripts/resolve_bib_conflict.py` does, so a
bibliography merge written by that script, with nothing else changed, passes. After
`git fetch origin`, run the script from a checkout of current `origin/main`, not of the PR's
branch, which could change it.
An approval given while a PR is based on another branch also names that branch's head, and the
check then needs `--approved-base <that head>`. Without it, the lower branch's changes, which this
review did not cover, would carry the approval if the lower PR never landed. Pass that head even
when the approved head had also merged a newer `main`: the script then replays from the merge of
the lower head and that `main`, and names it in the result. Anyone, including
the author, may post the script's result line, which names both heads and the exact command. The
non-author who queues the new head runs that command again rather than relying on the posted line.
When the script reports differences, review the paths and diffs it prints as a delta, under the
carry-forward rule above.

## New statements and definitions

When a declaration claims to formalize a cited result, give its precise source version and locator
and map the source claim to Lean: quantifiers, hypotheses, models, encodings and resource
conventions. An accurate paraphrase is sufficient; identify material differences or weaker scope.
Reviewers check the primary source and mapping. If quoting, verify the exact words and locator
against that source; invented or misattributed quotations block approval. New mathematics and
new proof ideas need no source; label them as original without implying a cited endpoint was proved.

Whether a new definition needs checked examples on both sides (an instance where it holds and one
where it fails) is for the author and reviewers to judge; reviewers may ask for them when a
definition could be vacuous or trivially satisfied.

Search for existing notions before adding public definitions. Reuse or extend them when they
express the intended mathematics; explain a non-obvious decision to introduce a parallel notion.
Syntactic similarity is a prompt to inspect reuse, not proof that models should be identified.
Generalization should improve concrete clients without obscuring semantics or making inference
and usage harder.

### Structures for domain objects and records

Define domain objects, problem instances, certificates, configurations, and multi-field algorithm
contexts, states or records as documented `structure`s with named, documented fields—not as tuple
type synonyms (`abbrev HittingSetInstance := (List ℕ × List (List ℕ)) × ℕ`) or bare product types
in problem sets (`Set (List (ℕ × ℕ) × ℕ × ℕ)`, `Set (Graph × ℕ)`). A `structure` gives every
component a name and docstring in editor hover and `doc-gen4`, supports dot-notation, prevents
swapping homogeneous components, and avoids the `.1.2` positional projection chains banned by
[#1764](https://github.com/cslib-community/cslib-frontier/issues/1764). Encode field-tuple
structures with `enc_structure` under [Encodings in statements](#encodings-in-statements) below.

Keep plain `Prod` (`×`) where the pair is not a domain record: generic binary combinators,
mathematical Cartesian products, and uncurried multi-argument function inputs that merely pair an
instance with a witness or second operand (such as an NP verifier `Instance × List Bool → Bool` or
a binary operation `α × β → γ`). Existing tuple abbreviations and bare-product problem sets are
migrated under [#4385](https://github.com/cslib-community/cslib-frontier/issues/4385).

### Encodings in statements

An encoding is part of what a statement claims, so statements show every encoding; but a reader
should not have to parse the same nested encoding again and again. New declarations, and
declarations whose statements change, follow these rules. Existing code is brought into line by
a tracked sweep ([#1656](https://github.com/cslib-community/cslib-frontier/issues/1656)), and the
encoding-readability lint checks rule 1 against a per-module baseline that may only fall.

1. **Name repeated compound encodings.** A *compound encoding* is a term of type
   `α ↪ List Bool` in which one of the generic combinators `encPair`, `encList`, `encOption`,
   `encSum`, `encFramed`, `encPi` or `encDPi` is applied to another application of one of them,
   such as `encPair encS (encOption encBool)`. When the same compound encoding, up to the names of
   local variables, occurs in the types of three or more public declarations of a module, give it
   a named `abbrev` and write the name in those statements. Occurrences inside larger terms count,
   including bounds that restate an input encoding, such as
   `fun p => (encPair encS (encOption encBool) p).length`. The varying encodings become the
   `abbrev`'s parameters. Define it in that module, or in the lowest module its users share, and
   once a name exists, use it instead of restating its body.
2. **Document the layout.** The `abbrev`'s docstring says what is encoded and how: the order of
   the parts, which parts are framed, and any tag bits. For example, `QueryMachine.encStateRead`
   is "a state paired with the bit read; the state is framed".
3. **Keep it reducible.** Use `abbrev`, not `def`. The statement is definitionally identical to
   the spelled-out one: `enc_len`, `fun_prop`, instance search and `simp` with the combinators'
   lemmas such as `length_encPair` see through the name, and so does `rw`, except where the name
   heads the rewritten term. Syntactic tools may not: `omega` takes `(encX e p).length` and its
   spelled-out form as different atoms, so the facts it combines must use one form, which can
   need small proof edits. Do not abbreviate an encoding with a `local notation`: the lint reads
   it as an atom, so it hides a compound encoding, and the documentation shows its expansion.
   When you touch a module that abbreviates a compound encoding with one, replace it with a
   documented `abbrev`.
4. **Name domain encodings.** Encode a mathematical object (a formula, graph, circuit or problem
   instance) by a named, documented definition, not by a compound spelled out inside a larger
   encoding, even where it occurs only once.
5. **Declare structure encodings with `enc_structure`.** When a structure is encoded as the
   tuple of its fields in declaration order, declare the encoding with `enc_structure`, which
   generates the embedding, its `_apply` equation and its `fun_prop` certificates (for degree,
   `ComputableInO`, workspace budgets and `ComputableInPolyTime`), rather than writing a `.trans`
   embedding and proving the certificates by hand. The
   [Operator's Manual](manual/workflows/choosing-models.md#write-the-contract-before-the-proof)
   shows the declaration and what it generates.
6. **Show meaning-bearing choices.** Unary versus binary numbers, the representation of graphs
   and matrices, and framing that changes a length bound stay visible: the name or the first line
   of its docstring states the choice (`encUnaryPair`, not `encArgs`). A name must not hide one.
7. **No hidden defaults.** Do not let an elaborator or typeclass choose an encoding for a type;
   the `enc%` proposal (#1830) is parked.

## Design commitments (do not re-litigate casually)

- Base pin is upstream cslib `main` at a SHA; never a fork.
- One parametric machine extending upstream `Turing.Cfg`/`Turing.Action`, with `Choose := Id`
  recovering `MultiTapeTM` and `Choose := Set` recovering `MultiTapeNTM`, step-exactly.
- Computability predicates are `@[fun_prop]`-registered; loops go through Hoare-style
  `iterate_spec` rules and the Aesop `polytime` set.
- Definitions and public results use plain computability with independent time and space bounds:
  upstream `ComputableInTimeAndSpace…` and the notions built on it, such as `ComputableInPolyTime`.
  The tidy computability calculus is being deleted (#862); tidiness survives only as a machine-level
  kernel inside the Machines layer, used inside proofs of plain rules.
- Programs are `PFunctor.FreeM` values; a machine's clocked run is itself a program.
- The universal machine is an interpreter program certified by the calculus, not a hand-built
  machine.
- Do not cite the unpublished draft "A Small Calculus of Finite Computation" in source or PR text.

## PR titles (for upstream PRs and here)

`type(scope): description`, type ∈ `feat|fix|doc|style|refactor|test|chore|perf|ci`, no trailing
period. Disclose AI assistance in the PR description, as cslib's policy requires.
