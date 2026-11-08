# Automated development: evidence and interpretation

The available records support an account of rapid, heavily automated development with active human steering, reuse of earlier formalization, parallel agents, repeated review and integration, and documented semantic failures followed by correction. They do not support a percentage of the mathematics produced autonomously, a human-equivalent productivity multiplier, or a lifetime task-success rate.

- [Corpus and extraction methods](methods.md): inclusion, identity, deduplication, privacy and reproducibility.
- [Chronology and timing](timings.md): Git growth, observed turn durations, PR lead times and CI outcomes.
- [Development case studies](case-studies.md): semantic withdrawals, formal abstracts, circuit synthesis, RAM evolution and build infrastructure.
- [Selected transcript evidence](transcripts.md): 22 verified short excerpts from six conversations, with timestamps and record provenance.
- [Study design and remaining evidence](study-design.md): what a publishable empirical claim would require, including desktop records.

## Recorded scope

| Evidence | Observed amount | Meaning |
|---|---:|---|
| Fixed library source | 3,896 Lean files; 1,094,225 physical lines | Snapshot size including comments and scaffolding within `Complexity/` |
| Reachable Git history | 3,780 commits; 2,166 on first-parent path | Repository/integration history, including imports and refactors |
| Local Codex project-path cohort | 1,256 session IDs | 811 current-checkout identities and 445 predecessor identities |
| Local Claude project-path cohort | 621 record files | 473 current-checkout files and 148 predecessor files; files are not sessions |
| Current-path Codex roles | 22 editor, 89 spawned-worker, 700 guardian sessions | Guardian records are action-approval checks, not mathematical reviewers |
| Selected CI day | 231 merge-group run IDs on October 31 UTC | 225 success and six failure outcomes, all recorded as attempt 1 |

These are separate denominators. No row is an estimate of distinct theorem-development tasks. Source and Git counts can be regenerated from the fixed Git history. Session counts require private originals or separately retained exports. Current GitHub responses may differ from those observed in the survey; the raw exports are not shipped with the manual. [Source census script](../data/census.py), [Git history script](data/git_history.py), [Codex census script](data/session_census.py), [Claude census script](data/claude_census.py), [Timing analysis script](data/analyze.py).

## Observation boundary

The source baseline is `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. Transcript extraction uses its recorded committer timestamp, 2026-11-02 03:45:45 UTC, as a reproducible cutoff. This is not the merge time: PR #2228 merged at 04:01:01 UTC, after its merge-group checks. GitHub evidence about that revision was retrieved later and is identified separately.

Current-checkout Codex records observed locally end on October 24 at 00:14:18 UTC; Claude records extend to October 30 at 09:22:58 UTC. Both omit part of the final development interval. The predecessor cohort is kept separate, and its earlier timestamps cannot be used as current-library task measurements. Some current-path Claude records predate the earliest first-parent Git timestamp; path identity alone does not resolve that provenance discrepancy.

Read-only SSH to `samuel@desktop` was authorized and retried, but this environment's SSH executable failed with `No user exists for uid 501` before connecting. No desktop records were accessed. This is a material coverage gap for the requested exhaustive development history, not a reason to infer that no later conversations exist.

## Appropriate paper claims

The paper can report the observed corpus, the fixed source snapshot, concrete model and API decisions, dated qualitative examples of human steering, and precisely scoped measurements. It should discuss the failed claims and their correction alongside successful endpoints. It should describe automation as a development process with explicit roles and checks rather than equating Git volume with original mathematics. The [proposed empirical design](study-design.md) separates these supported observations from measurements still requiring evidence.
