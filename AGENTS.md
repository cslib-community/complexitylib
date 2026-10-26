# Project Instructions

Complexitylib is a Lean 4 library of computational complexity theory built on **cslib**
(`leanprover/cslib`). Its defining constraint: **every module must be upstreamable into cslib
unchanged**, apart from rewriting the import prefix `Complexity.` → `Cslib.`. cslib's own rules
therefore apply here verbatim; read cslib's `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md`
(pinned checkout: `.lake/packages/cslib`, or a local clone at `../cslib`) and follow them.
`ROADMAP.md` records outstanding work;
`UPSTREAM.md` records coordination and exceptional integration decisions.

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

Maximize useful parallel progress: both coordinators and workers may handle multiple tasks
and spawn subagents. Roles define responsibilities, not concurrency limits. Give each subagent
a role and a clear scope; use separate issues for independently deliverable tasks and record
smaller delegated subtasks in the parent issue. Keep ownership, branches, and mutable build
outputs distinct where concurrent edits could conflict. The delegating agent remains responsible
for tracking delegated work, keeping issue status current, and bringing results to completion.

Issues are the task queue and durable record of ownership and progress. Humans, coordinators,
and workers may create tasks. Search existing issues and PRs before creating a duplicate; use
an existing human-created issue when it describes the work. Give each task a concrete scope,
completion criteria, and relevant dependencies.

### Completion and scope

Optimize for trustworthy, reusable results, not the number of closed issues or merged PRs.
When narrowing a task, preserve its original objective and record the bounded deliverable and
remaining gap prominently. A restricted model, conditional result, or partial theorem does not
complete a broader objective. Do not silently retitle an ambitious issue into an easier completed
task.

Distinguish these dispositions in the issue:

- **Completed:** the agreed acceptance criteria are satisfied.
- **Milestone completed:** a bounded deliverable is finished; link the remaining objective.
- **Deferred / not planned:** work is intentionally stopped; preserve its results and explain
  what remains unproved.

Close a milestone issue as completed when its own criteria are met. Keep the broader objective
open, or, when authorized to defer it, close it as not planned and link the completed milestone.
PR descriptions must distinguish mathematical progress from infrastructure, refactoring, and
documentation progress.

### Durable records

The issue owns scope, ownership and remaining work; the PR owns the final change, validation and
review. Link between them instead of mirroring reports. Record tested and reviewed revisions once,
in GitHub review/CI metadata or a concise PR record; link reusable evidence rather than reproducing
it. Without a PR, record evidence in the commit description and link it from the issue.
A local path alone is insufficient for a handoff.

At integration, briefly state what landed and any remaining gap. Keep the full objective visible
when a milestone completes only part of it.

### Workers

1. Before implementation, create or claim an issue and assign it to yourself. Post a claim
   comment identifying your agent/session, scope, and branch or worktree. Agents sharing a
   GitHub account must use distinct agent/session IDs in comments; the assignee alone does not
   identify the active worker. A worker may own multiple active issues; identify the responsible
   agent for each delegated task in its issue.
2. Post a brief issue update at least hourly while active or retaining blocked work, and when
   blocked, handing off or stopping. Give the agent/session, state and next step; link the branch
   or PR for code and evidence. One line suffices when nothing changed. A delegating agent may
   report for its workers. Do not promise unattended updates after stopping.
3. If active work has had no status report from its owner or delegating agent for **three hours**,
   another worker may claim it. Re-read the issue and linked PR immediately before taking over,
   post a takeover comment, update the assignment, and verify ownership before editing.
   Preserve existing work and credit.
   If claims overlap, ask a coordinator to resolve ownership; do not work competing versions.
   A returning worker must check ownership before resuming. Explicitly released work is
   available immediately.
4. Implement, self-review, and validate according to the requirements below. Include documentation
   changes caused by your work and assess the headline abstract catalogue before submitting the PR.
5. When ready, open a PR linked to the issue, record validation and remaining limitations, and
   request coordinator review. Post an `awaiting review` status with the PR link in the issue.
   Keep the issue open until the work is merged or explicitly dispositioned by a coordinator.
   Awaiting review is a handoff, not abandoned active work: hourly worker reports and the
   three-hour takeover rule are suspended while the PR waits in the coordinator's queue.
6. Await coordinator review for that PR while progressing other tasks; do not approve or merge
   your own PR. Address requested changes on your open PRs before opening new ones, post an
   `active` status when resuming,
   restart hourly reports, and request fresh review of the updated revision. If unavailable,
   release the task explicitly so another worker can take over.

Use plain issue comments for states such as `active`, `blocked`, `available`,
`awaiting review`, and `changes requested`; this workflow does not depend on custom labels or
automation. Blocked work must have a status update or be released, rather than retaining
ownership indefinitely.

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
- Give a clear verdict. For requested changes, post a short link in the task issue. This ends the
  review-wait exemption and starts a fresh three-hour response window; the worker reports active,
  blocked or released status, with the usual reporting and takeover rules thereafter.
- Resolve ownership and dependency conflicts, and help stale tasks reach a useful next step.
- Check affected `ROADMAP.md`, `abstracts/catalogue.json`, `UPSTREAM.md` and other documentation.
  Preserve source credit and the distinction between a completed milestone and its open objective.
- Merge only with maintainer authority, required validation and independent review of the current
  revision. Shepherding approved PRs through the merge queue and keeping the queue moving is a
  coordinator responsibility: do not treat a PR as done when it is merely queued. Monitor queued
  batches until they land on `main`, rebase or re-queue PRs ejected by conflicts or transient
  failures, sequence broad tree-wide refactors so they do not stall smaller PRs behind cold cache
  rebuilds, and diagnose and fix merge-queue or CI bottlenecks when the queue jams. Close
  completed issues and link any remaining work once the change lands.
- For your own implementation, follow the worker rules and obtain another coordinator's review.
  Changing roles or delegating authorship never makes an author eligible to approve their work.
  The exceptions are validated coordinator fixes and the delegated-review exception for changes
  that preserve every public statement's meaning, both described under
  [Review cycle](#review-cycle).

If a shared GitHub account prevents formal approval, use one brief PR comment naming the reviewer
agent/session, revision and verdict. This is agent review, not platform or human approval.

## Working on changes

Use ordinary Git branches or isolated worktrees for substantial changes. Preserve other
contributors' work and keep mutable build outputs separate between worktrees. Agree substantial
scope through Issues or pull requests, and split large developments into independently useful,
reviewable milestones. Record unfinished work in `ROADMAP.md` without claiming it complete.

Contributors self-review and validate their changes. Maintainers arrange independent API and
correctness reviews of the exact revision before integration; reviewers report findings, and
fixes receive a fresh review. Preserve source credit and record all contributors and review
results in the pull request or commit description.

### Repository isolation

Treat the user's checkout and shared Git object database as protected infrastructure. Ordinary
worktrees share their Git object database. Never import reconstructed Git objects, install shallow
boundaries, or experiment with history repair in that shared database. Use an independent
repository with its own Git object database for such operations.

Before Git recovery or nonstandard object manipulation, verify the actual Git common directory,
object alternates, and storage sharing. The experimental repository must not use the shared
database through a gitfile, alternate object directory, or hard-linked object files. Never delete
objects, refs, worktree registrations, or metadata belonging to another session.

Keep mutable build outputs separate. Integration experiments must be contained so their failure
cannot damage the user's checkout or another worker's repository.

Machines are shared between agents. Stop only processes and tasks you started, by PID or task
ID; never use pattern-based kills such as `pkill -f`, which also hit other agents' builds. Keep
scratch files under a directory or name unique to your agent.

### Placement and reuse

Place reusable definitions and general lemmas in the lowest suitable mathematical module.
Specialized theorem modules should import their prerequisites. During review, look for general
APIs buried in a particular application or proof. Extract them when the dependency improvement is
concrete and the change is small; otherwise record a specific follow-up with declaration names,
consumers, and a proposed home. Preserve public interfaces under the compatibility rules below.
Do not expand a bounded PR into an unbounded architectural cleanup.

"Lowest suitable" does not mean the most widely imported file. Adding a public declaration changes
a module's public interface and can invalidate downstream build artifacts, even for clients that do
not use the new declaration. Prefer a small topic module imported by its consumers over appending
to a hub such as `Foundations/Data/List/Basic.lean` or `Probability/PMF.lean`; #569 records the
measured fan-out. Exposed definition bodies (`@[expose]`) belong to the interface too, so expose
only what downstream proofs must unfold.

### Improving library ergonomics

When work exposes library friction, workers should improve the relevant API, lemma, documentation
or automation within the agreed scope, or record a concrete follow-up. Identify the affected
client and declarations, search existing and upstream APIs, and prefer the smallest generally
useful fix. Show representative before/after usage and explain what becomes clearer or easier.

Coordinators should be satisfied that the examples demonstrate a real improvement, that the
proposal fits the mathematical API and upstream design, and that its benefit justifies the added
maintenance and migration cost. Challenge arbitrary programming conventions and speculative
abstractions; a familiar pattern alone is not a reason to adopt it. Reuse the placement,
compatibility and review rules here.

Keep the evidence proportional. A small friction fix usually needs a short explanation and a
checked example; broader API changes need representative affected clients and a compatibility
plan. Investigate performance when it is material to the change, without requiring a benchmark
campaign or separate design study for every small improvement.

## Lean development: use the Lean MCP server first

Before the first Lean MCP operation that can elaborate or build in a checkout, run
`scripts/cache/ensure.sh`. Run it again after pulling, switching branches, or changing the
toolchain or dependency pins. This applies regardless of the agent client: MCP's
`lean_build(fetch_cache=true)` fetches Mathlib's cache, not the Complexitylib cache.
The bootstrap attempts both and suppresses repeated downloads for the same checkout state
for ten minutes; `scripts/cache/ensure.sh --refresh` retries immediately. A miss or download
failure leaves Lean to compile the missing outputs.

Use MCP goal inspection, diagnostics and theorem search while iterating; reserve builds for
validation checkpoints. `scripts/build.sh [Lake build arguments]`, `scripts/check.sh` and
`scripts/worktree.sh create` run the same bootstrap automatically. Bare `lake` and MCP commands do
not invoke it. If MCP tools are unavailable, say so and use the smallest shell check.

`scripts/worktree.sh` never points a worktree at the primary checkout, refuses targets or cache
symlinks that do, and isolates dependency Git control files and external symlinks so worktree
operations cannot write into the primary checkout. Lake's local artifact cache then shares
Complexitylib outputs between checkouts on the same machine with the same inputs. Proof-only edits
do not rebuild dependents; statement and definition changes in widely imported modules do.
[scripts/cache/README.md](scripts/cache/README.md) describes the caches and the deliberate opt-out
for builds that must not download artifacts.

## Validation sequence

```bash
lake build --wfail --iofail
lake exe mk_all --check
lake test --wfail --iofail
lake lint
lake exe lint-style
lake exe checkInitImports
```

`scripts/check.sh` restores optional caches and runs this sequence. CI runs the same checks.

For the edit loop, `scripts/check.sh --quick [--base REF]` builds changed Lean modules and their
transitive importing clients, then checks import aggregates. The comparison uses the merge base
with local `origin/main` by default, including committed, staged, unstaged and untracked changes;
it does not fetch. Quick mode skips the global test/lint/style/init-import gates and is not full
validation. Non-Lean changes, deletions/renames, changed aggregates, unsupported layouts and
ambiguous change/import analysis fall back to all six gates. Run the default command before
submitting a PR; quick success does not satisfy that requirement.

`lake exe mk_all` regenerates `Complexity.lean` after adding a file. New test files go in
`ComplexityTests/`; the test library is built from a Lake glob, so there is no aggregator to update.

## File rules

1. **Path and namespace mirror cslib.** `Complexity/Foundations/Data/Encoding.lean` is destined
   for `Cslib/Foundations/Data/Encoding.lean`; multi-tape machine files use the upstream root
   namespace `Turing`, everything else `Cslib.*` as upstream does.
2. **Template** (cslib's): Apache header with the exact wording below, `module`, an
   `-- upstream:` marker line, `public import` of API dependencies (plain `import` for proof-only
   ones), a module docstring with `## Main definitions` / `## Main results` / `## References`,
   then `@[expose] public section` or per-declaration `public`.
   ```lean
   /-
   Copyright (c) <year> <authors>. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: <authors>
   -/

   module
   -- upstream: candidate

   public import Complexity.Init
   ```
3. **Upstream marker** values: `candidate`, `submitted #N @SHA` (a copy of an open cslib pull
   request at its head `SHA`), `vendored <owner>:<branch> @SHA (unsubmitted)` (a copy of a branch
   of a contributor's cslib fork that has no pull request yet), `merged @SHA` (delete the file and
   bump the pin in the same commit), `local-only (reason)`. Nothing is `local-only` without a
   reason; valid reasons are project scaffolding and tests of local-only files.
   A port keeps the authors of the files it is ported from: v1's PCP internals, Sipser–Lautemann
   and containment internals are by Bolton Bailey, so their ports carry
   `Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger` and `Authors: Bolton Bailey, Samuel
   Schlesinger`; ports of Christian Reitwiessner's work carry his name likewise. Check the v1
   file's `Authors:` line before porting.
4. **Every module publicly imports `Cslib.Init`** (through `Complexity.Init`); the test driver
   runs `checkInitImports`.
5. **Reuse upstream first.** Before defining anything, search cslib (`.lake/packages/cslib/Cslib`,
   or the local `../cslib/Cslib` checkout) and the
   in-flight PRs recorded in source markers, and consult `UPSTREAM.md`. A thin local copy of an
   unmerged upstream PR (or an unsubmitted branch of an upstream contributor) is allowed at the
   mirrored path, keeping the
   original authors and declaration names, marked `-- upstream: submitted #N @SHA` (or
   `vendored …`). A copy holds only what the pinned cslib lacks: when a PR modifies an existing
   cslib file, the copy contains just its additions. Copies are deleted when the work merges.

## Staying current with upstream

- `lakefile.toml` pins cslib `main`; move the pin forward whenever `main` moves, fixing breakage
  in the same commit.
- `scripts/upstream_sync.py` reports, for every copied module, whether its pull request has
  merged (bump the pin past it and delete the copy), whether its head has moved (re-sync the
  copy) or whether it was closed. Run it whenever upstream is checked, and act on every line that
  is not `CURRENT`.
6. **Bit strings.** Declarations about bit strings and the cube `ι → Bool` (operations, sampling,
   Fourier analysis, sensitivity, influence, codes) live in `Cslib.BitString`; only the named
   Boolean functions `parityOn`, `parity`, `threshold`, `majority`, `strictMajority` sit in `Cslib`
   beside cslib's `BooleanFunction`. Bit strings add with `+` (Mathlib's `BooleanRing Bool`),
   single bits with `^^`.
7. **Citations.** Cite textbook sources in docstrings via `references.bib` keys
   (`[AroraBarak09]`, `[Papadimitriou94]`, `[Sipser2013]`, `[Jukna2012]`, …). Add new entries in cslib's
   format at their place in key order (`scripts/check_hygiene.py` checks it), keeping bibliography
   and project-documentation changes in focused commits.

## Proof hygiene

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`; definitions as terms, not `by` blocks, where possible.
- Prefer `do` notation for sequential monadic computations, including probabilistic experiments
  in theorem statements. Keep explicit `bind` in laws about bind and proof steps that use those
  laws directly, and for operations such as `PMF.bind` between different universes that the standard
  monad interface cannot express. Retain concise point-free composition and maps when naming an
  intermediate value would not improve readability. Check affected proofs when changing notation.
- The library supports no downstream users yet, so renaming, moving, removing or privatizing a
  public declaration needs no deprecated alias: update every client in this repository (library,
  tests, abstracts and guide) in the same change. Delete existing deprecated aliases when touching
  their area. Revisit this rule before the first supported release.
- `ComplexityTests/Axioms.lean` audits all declarations stored in imported `Complexity` modules
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

Read the actual definitions and statements. For substantive mathematics, explain briefly what is
proved, its limiting hypotheses/model/resource conventions, and a checked instance or edge case.
For a refactor, check declaration preservation, imports and a client using the intended API.
Lean acceptance under audited axioms does not establish that a definition matches its intended
mathematics; state material limits of the review.

Use inline comments for local findings. Explain the problem and a concrete change or question;
mark optional suggestions as nits. Group related points. Keep unrelated cleanup as a follow-up,
and do not turn an optional preference into a moving merge requirement. Authors may disagree:
discuss the technical reason and settle the point.

After fixes, review the delta and affected reasoning. Revisit more of the code when a change
invalidates earlier conclusions. Reuse existing reviews after verifying their scope and source
identity; do not repeat a full review of unchanged code. Before merging, confirm that the current
revision is covered and required validation passes.

A coordinator may push a fix to a PR directly, instead of passing it back, when they are confident
in it and have validated it. Typical cases are rebases and conflict resolution, refreshed generated
baselines, imports, lint, proof repairs that leave statements unchanged, and corrections to
documentation, citations or `ROADMAP.md`. Check the head first and add commits on top; force-push
only for an announced rebase. Preserve the author's credit, and name the commits and their
validation in the PR. Such a fix needs no second reviewer: the coordinator who made it may approve
the resulting revision. Other reviewers, and coordinators for everything else, send findings back to
the author as review comments. That includes changes to public statements, the meaning of
definitions or the API, and any fix the coordinator is less sure of.

**Delegated-review exception (coordinators only).** A coordinator may approve a PR authored under
its own delegation when the change leaves the meaning of every public statement and definition
unchanged: proof-only, documentation-only and test-only changes, mechanical refactors,
privatizations, restacks and generated-baseline updates. The review is performed by a reviewing
agent that did not author the change, working in a context separate from the one that briefed the
author, and the verdict names this delegated-review exception and the classification. A reviewer
outside the delegating fleet must still approve any PR that introduces or changes a public theorem
statement or definition, a curated abstract or a security claim, and any PR whose classification is
in doubt. Another coordinator audits a sample of these approvals. Workers and non-coordinator
reviewers never approve work from their own fleet.

Finish with a short approval or a clear request for changes. A substantive concern may need a
long explanation; a clean review does not need a checklist of everything inspected. Record the
reviewed revision, meaningful findings and resolutions once in the PR, following
[CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).

CSLib examples: [focused fixes and replies](https://github.com/leanprover/cslib/pull/1145),
[an architectural suggestion kept separate from approval](https://github.com/leanprover/cslib/pull/1120),
and [API review with explicit nonblocking nits](https://github.com/leanprover/cslib/pull/923#pullrequestreview-5560941186).

## New statements and definitions

When a declaration claims to formalize a cited result, the PR quotes the source statement with its
exact locator and maps the source's notation to the Lean statement: quantifiers, models, encodings
and resource conventions. Reviewers check that mapping rather than an impression. Text presented as
a quotation is copied from the pinned source version, with its locator checked there rather than
taken from an issue, a PR or other library text; anything else is labeled as a paraphrase. Reviewers
check quotations against the source, and a quoted passage that is not in the source blocks approval.
New mathematics and new proof ideas need no source; label them as original.

Whether a new definition needs checked examples on both sides (an instance where it holds and one
where it fails) is for the author and reviewers to judge; reviewers may ask for them when a
definition could be vacuous or trivially satisfied.

Reuse existing definitions rather than adding parallel notions; extend or generalize them instead.
A PR that adds a public definition states in its description the existing notions it considered
and why none could be reused or generalized, and reviewers treat a definition whose body matches an
existing one up to its carrier or argument types as a finding.

## Curated formal abstracts

`abstracts/catalogue.json` selects the public headline results. Each selected group has a checked
`*Abstract.lean` and `*Bridge.lean` under `abstracts/ComplexityAbstracts/`, imported by the
dedicated `ComplexityAbstracts` library. `ComplexityTests/Abstracts/All.lean` imports that library,
and its regression tests sit beside it. Existing declaration namespaces remain stable across the
source relocation. The Lean definitions and statements are the source of truth; PDFs are generated
from them, with proof bodies omitted. There is no separately maintained paper/TeX index.

Selection has a higher bar than inclusion in the library: a headline must be a substantial proved
endpoint with conventional, inspectable semantics, hypotheses that are satisfiable or are standard
open assumptions stated as such, explicit models and encodings, and honest quantitative bounds.
Partial constructions, conditional substitutes for a standard theorem, bounded experiments and
helper APIs do not become headlines by acquiring an abstract. Prefer a small coherent selection.
Preserve Samuel's editorial choices and source credit; keep outstanding endpoints in `ROADMAP.md`.

Before opening or updating **every AI-authored PR**, assess the selected abstracts against the
final Lean changes. Update affected statements, definitions, scope notes and catalogue entries.
New library theorems need not become headlines. Record a no-impact assessment when appropriate,
including proof-only refactors with unchanged statements and scope.

Follow the local `lean-abstract` skill and run `#check_abstract`. An allowlist may expose narrowly
identified foundational models with their meaning explained; it must not hide the result or its
complexity-class semantics. The audit checks elaborated dependencies, not human interpretation.
Independent review must cover API quality, correctness and each changed abstract against the final
Lean sources, including quantifiers, encoding, resource bounds, nonvacuity and readability. This may
be part of the same review above; reuse unchanged evidence. Record revisions and findings once in
the PR. Do not imply human editorial approval.

`scripts/build_abstracts.py` generates individual PDFs, a combined catalogue and provenance with
source digests and exact declaration links. The **Formal abstract PDFs** workflow uploads review
and main artifacts, and the **API documentation** workflow publishes main builds under
`https://www.cslib.io/complexitylib/abstracts/`. When abstracts or rendering
change, inspect affected rendered pages and declaration links before integration; record the
artifact/run and revisions. If abstracts and rendering are unaffected, record no impact; no new
PDF review is needed. Local generation is supported. Generated TeX, PDFs and auxiliary products
are not versioned.

## Design commitments (do not re-litigate casually)

- Base pin is upstream cslib `main` at a SHA; never a fork.
- One parametric machine extending upstream `Turing.Cfg`/`Turing.Action`, with `Choose := Id`
  recovering `MultiTapeTM` and `Choose := Set` recovering `MultiTapeNTM`, step-exactly.
- Computability predicates (`PolyTime`, `InTimeSpace`, …) are `@[fun_prop]`-registered; loops
  go through Hoare-style `iterate_spec` rules and the Aesop `polytime` set.
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
