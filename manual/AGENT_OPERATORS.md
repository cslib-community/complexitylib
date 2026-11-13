# cslib-frontier Agent Operator's Manual

This short manual is for people directing agents in cslib-frontier. It explains whom to ask,
what to ask for, and how to judge the handoff. The substantial [Operator's Manual](README.md)
explains how to work in the codebase: its tactics, models, proof patterns, examples and procedures.
Both humans and agents use that reference. You do not need an agent to follow it.

The current [project instructions](../AGENTS.md) and [contribution policy](../CONTRIBUTING.md)
govern the work. This manual explains how to use that process; it does not grant an agent
permission to merge, publish, or change another contributor's work.

## Choose the right assignment

An agent can investigate, implement, coordinate or review. State the assignment when starting
a session; the repository defaults an unspecified agent to **worker**.

| Assignment | What the agent does | What you should expect |
|---|---|---|
| Worker | Owns a bounded task, implements it on a branch, checks clients and documentation, and hands it over for review | A concrete change, actual validation results and a clear remaining gap, if any |
| Coordinator | Reviews submitted work, resolves ownership and dependencies, arranges independent review, and manages integration when authorized | A current account of what is ready, what is blocked and what actually landed |
| Independent reviewer | Inspects a change without having designed or implemented it | Specific findings or an approval of an identified revision, with the scope and limits of the review |

Reviewer is a review assignment, not an exemption from the worker/coordinator rules. An author
cannot become independent by changing their role name. Agents using the same account can be
independent reviewers, but an agent verdict is not human or platform approval.

Use a worker for one proof, API improvement or bounded investigation. Use a coordinator when
several tasks or PRs need sequencing, review and integration. Identify the coordinator responsible
for that scope so several sessions do not independently take over the same queue.

## Give the agent a useful starting point

Give the intended result, the issue or PR if one exists, the relevant checkout, and any important
constraints. For mathematics, specify the intended model and strength of the result. State merge
or publication authority explicitly when you want those actions. The agent should read the current
instructions, check ownership and existing work, and use the appropriate branch or worktree.

A bounded implementation request can be as simple as:

> Act as a worker on issue `<number>`. Read the current project instructions and inspect existing
> work first. Implement `<concrete result>` with a representative checked client. Preserve the
> intended model and hypotheses; report a narrower milestone as such. Update the affected
> Operator's Manual sections and assess the Agent Operator's Manual. Validate the change and
> prepare it for independent review.

For an investigation, ask for a decision you can use:

> Inspect how `<task>` is currently expressed in the library. Show the relevant definitions and a
> complete existing client, identify the main difficulty, and propose a bounded next step. State
> which conclusions come from source inspection and which were checked by running Lean.

For orientation, it is useful to ask an agent to summarize `AGENTS.md` for its assigned role and
point to the relevant manual sections. Require source locations for substantive claims. The
manuals provide a shared reference when a summary omits something or two agents disagree.

## Read a progress report

Ask for the result and the next decision, rather than a transcript of every tool call. A useful
report distinguishes these states:

| State | Meaning and useful next step |
|---|---|
| Active | A named agent owns the task; ask what has been established and what remains |
| Blocked | Progress needs a specific input or external change; ask for the exact obstacle and options |
| Awaiting review | Implementation has been handed off; keep the owner and arrange review |
| Changes requested | A reviewer found something to resolve; ask for the fix and review of the affected delta |
| Queued | Integration is pending; the coordinator should follow the queue through to a result |
| Landed | The change reached the target branch; check whether the broader objective is also complete |

A statement, its proof, a usable API, successful validation and completed integration are different
deliverables. For a mathematical milestone, ask what remains unproved. For a failed build, ask
which command failed and whether it was a proof failure, a resource problem or an environment
failure. The [codebase troubleshooting chapter](workflows/troubleshooting.md) explains the layers.

## Ask for review that answers the real question

Assign review to an agent that did not design or implement the change. For example:

> Independently review PR `<number>` at its current revision. Read the actual definitions and
> statements. Check the mathematical claim, API and representative client, including the model,
> encodings, hypotheses and resource bounds.
> Check public API usability in a representative `module` client with ordinary imports of the API.
> Read new and changed proofs against the rest of
> their files, and report any substantial argument the change repeats that another proof or an
> existing lemma already makes. Follow a representative caller: check whether named accessors,
> matcher/range facts and generated certificates remove representation work, and compare any
> sibling implementation or conversion bridge. Assess whether the proof strategy, invariant and
> helper statements fit that use. Review the impact on both manuals and any affected
> results-inventory entry. Report concrete findings and a verdict, stating what you checked and
> what remains uncertain. If queueing is authorized, first verify that named review holds are
> cleared and required CI/manual material is reviewed. Use the helper from trusted current `main` for the approved
> PR head; do not start `--wait` while completing CI will produce material still needing review.

Ask the reviewer to consider whether a different statement, API, invariant or proof strategy
would make the result clearer to state, prove and use, while preserving its mathematical strength.
Require inspection of the duplication notices and the declarations or proof blocks they identify;
an advisory check's successful exit does not establish that its candidates were reviewed. Concrete
cleanup affecting the contribution belongs in its original PR, under the
[quality and deferral rules](../AGENTS.md#improving-library-ergonomics).

Lean validation establishes the checked statements under their definitions and dependencies.
Review must also judge whether those statements express the intended mathematics and whether
someone can use the interface. Ask for a satisfying instance or meaningful edge case when a
contract may be vacuous. A diff shows a new copy of an argument but not the proof it repeats,
so ask for that comparison explicitly. For an API cleanup, ask which actual caller became simpler
and why; the [caller review procedure](../AGENTS.md#check-the-api-through-its-callers) gives concrete
checks. An approval must cover the final revision; substantive
fixes require review of the affected reasoning. Unchanged evidence can be reused after checking
its identity.

## Direct a coordinator

Make the scope and authority clear. A coordinator request can say:

> Coordinate `<issues or PRs>`. Inspect current ownership and existing reviews before assigning
> work. Prioritize reviewing and landing ready changes over starting more tasks. Check both
> manuals as part of every review, including any justified no-impact assessment. Arrange
> non-author review for your own changes. Report what landed, remaining objectives and blockers.

Reviewers with write access queue the exact heads they approve using the
[helper from trusted current main](workflows/agent-operations.md#queue-approved-work-and-keep-its-approval),
so an approved PR does not wait for a coordinator ([Approve and queue](../AGENTS.md#approve-and-queue)).
To keep a PR for your own review, say so in the PR or its linked issue: agents then approve it
without queueing, and you or someone you name queues it. Agents without write access can prepare
and review work but cannot queue it. Coordinators queue approved heads still waiting and monitor
the merge queue through
landing. [Coordinator duties](../AGENTS.md#coordinators) define the details.

An approval with review still pending is conditional. Ask for a final handoff that links the
earlier proof/API/caller judgment and resolves the named source, notice and manual-review holds.
The queue helper's `--wait` option queues automatically when CI passes; do not start it while
newly produced reports or pages still need inspection. A green check alone does not release
those holds. Updating `main` does not upgrade an already-running copy; have its owner stop an
old waiter before replacing it after hold clearance. This needs a coverage decision, not another
full review of unchanged code.

If discussion changes after a helper starts waiting, its final reread stops that enqueue.
Have the reviewer inspect the new or edited discussion and any holds before rerunning for the
still-approved head; no extra approval count is required. The guard covers the PR body,
comments, submitted reviews and inline threads, including edits and resolution changes. It does
not inspect linked issues or prevent a change racing with the enqueue mutation. Existing queue
entries are left in place, so coordinators still need to track review holds through landing.

When the queue ejects a PR whose only conflict is in `references.bib`, the coordinator or author
can run `python3 scripts/resolve_bib_conflict.py origin/<branch>` after `git fetch origin` to
write the merge with `main` instead of sending the PR back. It refuses any other conflict and
pushes nothing. Pushing its commit to the PR branch is a deliberate step by the author or a
coordinator acting for them, who records the push. Existing approval carries forward when
`scripts/check_restack.py` passes and CI passes at the new head, as
[Restacks](../AGENTS.md#restacks) describes. When the only conflicts are in `references.bib` or the
`mk_all` aggregates, `python3 scripts/restack_mechanical.py <PR> --approved-head <SHA>` does the
merge, the regeneration and that check in one step. It pushes only with `--push`, under the same
rule for who pushes, and prints the queue command without running it.

When several coordinators share one host, give them a single limit on concurrent Lean builds,
not only a thread count. Their builds can exhaust the kernel's file handles before its
processors, and then everyone's builds fail
([diagnosis](workflows/troubleshooting.md#diagnose-too-many-open-files-in-system)).
On Linux hosts and containers, local whole-library gates (`lake test`, `lake lint`,
`lake exe checkInitImports`, and full `scripts/check.sh`) also need `vm.max_map_count` well above
the stock `65530` kernel default (`262144` or higher; `python3 scripts/check_vm_map_count.py`
checks this before full runs) so single-process whole-library imports do not fail with misleading
`.olean` file-read errors
([diagnosis](workflows/troubleshooting.md#diagnose-failed-to-read-file-on-whole-library-imports)).
Have them run `scripts/check.sh --quick --no-full-fallback` during development: a change quick
mode cannot plan is reported instead of starting a full local check that holds a build slot for
hours, and CI on the pull request supplies the full run.
Agents on one host also share Lake's artifact cache, which restores a module that another
checkout built without its warnings. Full `scripts/check.sh` re-elaborates those built root-package
sources; quick mode checks affected sources, including unchanged clients, built import aggregates
and executable helpers.
Bare Lake commands still lack this audit. When a local check and CI disagree about a warning,
trust CI
([diagnosis](workflows/troubleshooting.md#diagnose-warnings-that-only-ci-reports)).

The manuals are part of this workflow. Changes to library usage belong in the Operator's Manual;
changes to roles, delegation, review or human direction may affect this Agent Operator's Manual.
Coordinators check both against the final change. A reasoned finding of no impact is valid;
an unchecked box or a passing build is not a usability review.

## Correct course and hand work over

When an agent drifts, name the mismatch: the theorem became conditional, the model changed, the
example cannot be followed, or the task expanded beyond the agreed scope. Ask it to preserve
the useful work, state the remaining objective and return to a concrete next step. When two
agents overlap, have the coordinator resolve ownership before either overwrites the other's work.

Ask for a PR description that explains the setting, central idea and result to someone who has
not followed the task. Use the [writing guidance and example](../AGENTS.md#writing-in-issues-and-prs)
to judge whether the explanation gives you enough context to understand the change.

For a handoff, request the issue and PR, branch and revision, actual validation, review state,
remaining work and the next action. Put that record in the issue/PR or commit, according to the
[durable-record rules](../AGENTS.md#durable-records). A new agent should inspect those records
and the current source before resuming. Silence alone does not release another agent's task.

To stop, specify which task or session should stop and ask for a preserved checkpoint and
handoff. Agents should stop only processes they own. An ended session cannot promise unattended
progress. You can resume from the recorded state with a new assignment.

Both manuals are maintained with the library under
[Maintaining the manuals](../CONTRIBUTING.md#maintaining-the-manuals). If an instruction here
cannot be followed, treat that as a documentation defect for the responsible worker and
coordinator to fix and review.
