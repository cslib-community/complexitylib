# Coordinate implementation and review

This chapter is the codebase coordination reference for participants and reviewers, whether
human or agent. It covers task ownership, isolated work, validation evidence and review handoffs.
The human directing agents should start with the separate
[Agent Operator's Manual](../AGENT_OPERATORS.md) for assignment and intervention procedures.
A short Lean proof can certify an unintended statement; a merged milestone can leave the
original objective unresolved. The [development study](../development-history/index.md)
supplies historical evidence separately. [complexitylib][complexitylib]

## Specify a bounded task and a visible endpoint

Before implementation, record the intended theorem or API, model, encoding, allowed hypotheses,
resource bound, existing source, representative client and owned files. Record the active
contributor or agent/session and branch in the issue or PR; a shared GitHub account does not
distinguish agents. Resolve an unclear contract with the task owner before extending its scope.

A task brief might request a named problem's membership in `NP` under a specified encoding, with a verifier and certificate-length bound. Say whether a reduction or completeness theorem is also required. That keeps a membership proof from silently becoming a report that completeness is done.

Choose parallel tasks with separate mutable files and build outputs. Prioritize fixes and landing existing work when review or integration is the bottleneck. Before taking over work, inspect its issue, PR and activity and contact its owner or coordinator. Silence alone does not release ownership. Follow the [role and ownership rules](../../AGENTS.md#agent-roles-and-task-ownership).

## Isolate work and build outputs

For a new branch based on the primary checkout’s current commit:

```bash
scripts/worktree.sh create feat/manual-example manual-example HEAD
```

The helper creates the worktree under `.worktrees/` and prepares caches. It resolves the shared repository’s primary root before interpreting `HEAD`; pass an explicit commit SHA to branch from another worktree’s revision. Choose a fresh task-specific branch and directory. Existing local and remote branches have different handling; read the helper's usage before takeover. Do not use reset options just to obtain a clean start.

Package sources may be hard-linked by default, while mutable build outputs are copied independently. Do not edit shared package sources. Use `--copy-cslib` or `--copy-packages` when dependencies must change. `--source-only` avoids initial `.lake` seeding when existing pins or artifacts are unsuitable. The [cache/isolation guide](../../scripts/cache/README.md#automatic-restoration) explains these modes.

Coordinate a thread budget on shared machines. `LEAN_NUM_THREADS=2 scripts/check.sh` is an example setting, not a hard process or memory limit. Stop only tasks you started, by recorded PID or task ID. Preserve completed artifacts when rescheduling. Ordinary worktrees share a Git object database; history-repair experiments require an independent repository.

## Separate implementation and review

Inspect existing definitions before introducing abstractions. Require the exact Lean contract and source-to-statement mapping for a claimed textbook endpoint. During implementation use focused diagnostics and clients; at handoff use the [contribution validation rules](contributing.md).

Assign review by the unanswered question. One non-authoring reviewer may cover correctness and API quality; add another for specific uncovered expertise. Give reviewers the revision, intended endpoint and validation evidence, and require inspection of definitions. Restating the author's summary is not independent source review.

The [semantic-withdrawal cases](../development-history/case-studies.md) explain why hypotheses, adversary power and realizability need attention after successful Lean checking. They are historical diagnoses, not asserted defects in the reviewed snapshot. The circuit-synthesis case illustrates a concrete API review question: does simplifying construction preserve wire sharing and charge the actual gates?

## Queue approved work and keep its approval

A reviewer with write access who approves a PR queues the approved head in the same step, with `python3 scripts/queue_pr.py <PR> <approved head>`. The script refuses any other head, a draft, a stacked PR still based on another branch, a conflict and failed checks. The reviewer does not queue when human review has been requested in the PR or its issue, or when the approval names a hold; [Approve and queue](../../AGENTS.md#approve-and-queue) gives the rule.

Merge `main` into an approved PR only when it conflicts, needs a change on `main` to pass CI, or a lower stacked PR has landed; the merge queue already tests each PR on top of the current `main`. After such a restack, `python3 scripts/check_restack.py <approved head> <new head>`, run from a checkout of current `origin/main` after `git fetch origin`, replays the approved change onto the new head's `main` and compares the result with the new head. When they match and CI passes, the approval carries over: post the result line, and the non-author who queues the new head reruns the command it names. Otherwise review the paths and diffs it prints. See [Restacks](../../AGENTS.md#restacks).

## Record evidence at the level of the claim

| Outcome | Evidence to retain |
|---|---|
| A client compiles | Revision/diff, command or hosted job, outcome |
| The intended theorem is formalized | Definitions, statement, source mapping and model/nonvacuity review |
| An API is easier to use | Representative before/after client and validation |
| A task is complete | Original acceptance criteria and remaining broader objective |
| A change is ready to integrate | Final revision's validation and independent review, maintainer authority |
| A development step took a given time | Defined endpoints, timestamps and measurement convention |

The issue owns scope and remaining work; the PR owns the final change, validation and review. Link evidence instead of repeating it. Keep polling and internal coordination out of public records. Distinguish completed milestones from the broader objective. A coordinator with authority monitors a queued PR until it lands or receives a concrete disposition: queued work is not integrated work.

## Interpret timing and transcript records

Commit times, provider completion durations, conversation spans, CI runtime and PR elapsed time measure different things. Concurrent sessions overlap; summed duration is not elapsed wall-clock time or human effort. The [timing chapter](../development-history/timings.md) retains units and denominators. Its selected runs and cases do not estimate an automation success rate or causal speedup.

For new records, retain the initial objective, task/session identities, parent-child links, source revisions, reviews, failed attempts and dispositions. Preserve emitted timestamps and define their event semantics before deriving durations. Retain appropriate excerpts and provenance. The [extraction methods](../development-history/methods.md) describe deduplication; [study design](../development-history/study-design.md) identifies evidence needed for comparisons. Desktop conversations remain absent, so this edition's historical corpus is explicitly incomplete.

[complexitylib]: ../sources.md#complexitylib

When using the hierarchy first-noise/payment and completed-preparation clients, keep
structural `Request HP.k` fixed and supply `HP.k_pos` where positivity is required.
Statistical precision indexes estimates and walk lengths independently; specializing
structure to precision does not identify a fixed recursive hierarchy. See the
[probabilistic workflow](probabilistic-workflows.md) for the quantitative contracts.

For genuine signed-stage review, inspect the actual normalized index and final structural
dispatch, inherited-terminal usage containment, and the single negative request in
`canonical_residual_bins_mean`. Finite cover/horizon hypotheses remain acceptance limits.
The [probabilistic workflow](probabilistic-workflows.md) separates this proved stage mean
from estimated-child induction and native resource objectives.

For estimated-child review, inspect `estimated_residual_bins_mean_error` and the actual
first-mean client linked from the [probabilistic workflow](probabilistic-workflows.md).
Check true-input bounded/canonical routing agreement, the estimated-left/canonical-right
product split, literal importance/midpoint factors and once-negative error accounting.
Finite absolute propagation does not discharge recursive relative budgets or the second
signal's full-terminal-rank maximum.
