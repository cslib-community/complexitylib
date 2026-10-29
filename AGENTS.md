# Project Instructions

Complexitylib is a Lean 4 library of computational complexity theory built on **cslib**
(`leanprover/cslib`). Library modules must be upstreamable unchanged apart from rewriting
`Complexity.` → `Cslib.`. General mathematics destined for Mathlib and local project scaffolding
are documented exceptions; see `UPSTREAM.md` and the source markers.

Read the pinned cslib `AGENTS.md`, `CONTRIBUTING.md` and `CODESTYLE.md` in
`.lake/packages/cslib` (or a checkout at the same revision). Follow its mathematical, API and
style conventions. This repository's workflow, validation and test layout are defined here and
in `CONTRIBUTING.md`; when submitting upstream, follow that repository's current process.
`ROADMAP.md` records outstanding directions; `UPSTREAM.md` records coordination decisions.

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
4. Implement, self-review and validate. Update documentation and selected abstracts when the
   change affects them, according to the requirements below.
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
- Check affected `ROADMAP.md`, `abstracts/catalogue.json`, `UPSTREAM.md` and other documentation.
  Preserve source credit and the distinction between a completed milestone and its open objective.
- Merge only with maintainer authority, required validation and independent review of the current
  revision. Shepherding approved PRs through the merge queue and keeping the queue moving is a
  coordinator responsibility: do not treat a PR as done when it is merely queued. Monitor queued
  batches until they land on `main`, rebase or re-queue PRs ejected by conflicts or transient
  failures, sequence broad tree-wide refactors so they do not stall smaller PRs behind cold cache
  rebuilds, and diagnose and fix merge-queue or CI bottlenecks when the queue jams. The queue
  squash-merges: a stacked PR that edits lines a lower PR introduces conflicts with that PR's
  squashed commit and is ejected, so queue it once the lower PRs land and it has merged `main`.
  Close completed issues and link any remaining work once the change lands.
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
consumers, and a proposed home. Apply the migration policy below when changing public interfaces.
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
checked example; broader API changes need representative affected clients and an in-repository
migration plan. Investigate performance when it is material to the change, without requiring a
benchmark campaign or separate design study for every small improvement.

## Lean development: use the Lean MCP server first

Bootstrap a cold checkout with `scripts/cache/ensure.sh` before Lean elaboration or building.
Retry when needed artifacts are missing or toolchain/dependency changes require new ones;
a new commit or branch switch alone does not require a manual bootstrap if outputs are warm.
MCP's `lean_build(fetch_cache=true)` fetches Mathlib's cache, not Complexitylib's. Cache misses
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

`scripts/check.sh` restores optional caches and runs this sequence. CI runs the same checks.
For Lean, dependency or build changes, all six gates must pass on the final source revision before
integration. A successful hosted run covering that revision supplies full validation; do not
repeat it locally merely to satisfy a second reporting requirement. Use local full validation
when hosted coverage is unavailable; changes to validation machinery also need direct checks of
the changed behavior. Required CI and merge-group checks still apply.

During development, check affected modules and representative clients before requesting review;
a PR may use CI for the full run. For documentation-only changes, check consistency, links and
any Lean examples introduced; a local whole-library rebuild is unnecessary.

For the edit loop, `scripts/check.sh --quick [--base REF]` builds changed Lean modules and their
transitive importing clients, then checks import aggregates. The comparison uses the merge base
with local `origin/main` by default, including committed, staged, unstaged and untracked changes;
it does not fetch. Quick mode skips the global test/lint/style/init-import gates and is not full
validation. Non-Lean changes, deletions/renames, changed aggregates, unsupported layouts and
ambiguous change/import analysis fall back to all six gates. Quick success alone does not satisfy
the full validation requirement above; documentation-only checks need not invoke quick mode.

`lake exe mk_all` regenerates `Complexity.lean` after adding a file. New test files go in
`ComplexityTests/`; the test library is built from a Lake glob, so there is no aggregator to update.

## File rules

1. **Path and namespace mirror cslib.** `Complexity/Foundations/Data/Encoding.lean` is destined
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

   public import Complexity.Init

   /-!
   # <Module topic>

   <Purpose, public API and mathematical sources.>
   -/

   public section
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
   cslib file, the copy contains just its additions. Copies are deleted when the pin adopts the merged work.
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
upstream code or removes a merged copy. Merely inspecting upstream does not require a pin bump.

Run `scripts/upstream_sync.py` during synchronization work. Inspect changed, merged or closed
upstream PRs against source markers and `UPSTREAM.md`; preserve documented local adaptations
and contributor work rather than blindly replacing copies. When adopting merged work, advance
the pin past it and remove the superseded local copy together. Record unresolved decisions in
`UPSTREAM.md` or a linked task instead of expanding an unrelated PR.

## Proof hygiene

- No `sorry` on `main`, no custom `axiom`, no `native_decide`.
- `set_option maxHeartbeats` / `maxRecDepth` overrides need a justifying comment. A
  `maxHeartbeats` above the 200000 default, or zero (unlimited), also needs a reviewed entry in
  `scripts/heartbeat_allowlist.txt`, which `scripts/check_hygiene.py` enforces and keeps
  shrinking; prefer reducing the proof's cost.
- Never put `[simp]` on machine step functions or transition tables (goals explode).
- Non-terminal `simp` only as `simp only`; definitions as terms, not `by` blocks, where possible.
- Prefer `do` notation for sequential monadic computations, including probabilistic experiments
  in theorem statements. Keep explicit `bind` in laws about bind and proof steps that use those
  laws directly, and for operations such as `PMF.bind` between different universes that the standard
  monad interface cannot express. Retain concise point-free composition and maps when naming an
  intermediate value would not improve readability. Check affected proofs when changing notation.
- Before the first supported release, do not add deprecated aliases or compatibility wrappers
  for renamed, moved, removed or privatized declarations. Update all in-repository clients
  (library, tests, abstracts and guide) and remove the superseded interface in the same change.
  Remove obsolete aliases as part of the relevant migration, not unrelated cleanup. Revisit
  compatibility guarantees before supporting external consumers.
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

A coordinator may fix conflicts and review findings directly when authorized to edit the branch.
Check its head and coordinate ownership first; add commits on top, or announce a necessary rebase.
Preserve author credit and record the delta and validation. Fixing a PR does not make self-review
independent.

Existing independent approval can carry across a mechanical delta when the coordinator verifies
that it preserves meaning, exported availability, attributes, imports and automation behavior,
and checks affected clients. Record that limited carry-forward decision. A clean rebase or typo
fix may qualify; a proof repair, privatization, changed test coverage or conflict resolution is
not automatically mechanical. Changed reasoning, API, source claims, security claims or abstracts,
and uncertain cases, need fresh non-author review of the affected delta.

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

Assess abstract impact when Lean statements, definitions, models, encodings, bounds or catalogue
selection change. Update affected statements and scope notes, and record the assessment once in
the PR. Reuse it while the relevant source is unchanged; metadata edits and unrelated changes
need no new no-impact report. New library theorems need not become headlines.

For abstract changes, follow the local `lean-abstract` skill and run the affected `#check_abstract`
audits. An allowlist may expose narrowly identified foundational models with their meaning
explained; it must not hide the result or its complexity-class semantics. The audit checks elaborated dependencies, not human interpretation.
Independent review must cover API quality, correctness and each changed abstract against the final
Lean sources, including quantifiers, encoding, resource bounds, nonvacuity and readability. This may
be part of the same review above; reuse unchanged evidence. Record revisions and findings once in
the PR. Do not imply human editorial approval.

`scripts/build_abstracts.py` generates individual PDFs, a combined catalogue and provenance with
source digests and exact declaration links. The **Formal abstract PDFs** workflow uploads review
and main artifacts, and the **API documentation** workflow publishes main builds under
`https://www.cslib.io/complexitylib/abstracts/`. When abstracts or rendering
change, inspect affected rendered pages and declaration links before integration; record the
artifact/run and revisions. Unaffected abstracts and rendering need no new PDF review. Local
generation is supported. Generated TeX, PDFs and auxiliary products are not versioned.

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
