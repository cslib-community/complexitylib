# Chronology and timing

All dates in this document are UTC. These are the November 2 survey results computed from the then-available exports with [analyze.py](data/analyze.py). Their meanings differ; they should not be combined into one estimate of effort. Generated exports are not versioned. Rechecking private-session measurements requires the original records.

The optional [history plotter](data/plot_history.py) produces an SVG and PNG under
`manual/_generated/` from regenerated census, Git and session summaries. It separates
repository growth, integration frequency and first-to-last log observations; observation
spans do not imply continuous coverage. It requires Matplotlib and the private-session
summaries. Neither generated figure is an input to the books.

## Recorded integration history

The first-parent history begins at 2026-10-15 02:58:56 and ends at the snapshot's recorded committer timestamp, 2026-11-02 03:45:45: 18 days, 46 minutes, 49 seconds. It contains 2,166 commits, within 3,780 commits reachable from the snapshot. This is the span of this Git history, not the time needed to invent or formalize the whole library. The early history imports earlier work; the local predecessor conversation cohort begins months earlier. [Git history script](data/git_history.py)

| UTC date | First-parent commits | UTC date | First-parent commits |
|---|---:|---|---:|
| Oct 15 | 189 | Oct 25 | 168 |
| Oct 16 | 115 | Oct 26 | 77 |
| Oct 17 | 68 | Oct 27 | 115 |
| Oct 18 | 60 | Oct 28 | 78 |
| Oct 19 | 119 | Oct 29 | 149 |
| Oct 20 | 108 | Oct 30 | 118 |
| Oct 21 | 87 | Oct 31 | 225 |
| Oct 22 | 41 | Nov 1 | 96 |
| Oct 23 | 120 | Nov 2, partial | 20 |
| Oct 24 | 213 | | |

The daily data also include additions and deletions for library, tests and all tracked paths. These should be used to show the scale and rhythm of integration, not to rank mathematical contribution. A large deletion may be a successful simplification or the withdrawal of a claim; a large addition may be a port or repeated proof plumbing. [Git history script](data/git_history.py)

Commit subjects contain 1,269 distinct terminal PR-number suffixes. This is a string-pattern count, not a complete PR census: earlier commits often lack such a suffix, and PR metadata must be fetched to establish creation, review or merge events. The first-parent authors field includes multiple human/contributor identities as well as shared-account conventions; it cannot allocate time or intellectual credit.

## Observed turn durations

The following table uses only the **current-checkout identity** cohort. p90 is the nearest-rank 90th percentile. Durations are seconds reported by the respective logging system, not measured CPU time or verified proof-development time.

| Record type | Timed completions | Median | p90 | Sum of reported seconds |
|---|---:|---:|---:|---:|
| Codex editor sessions | 393 | 453.735 | 2,533.656 | 439,231.408 |
| Codex spawned agents | 1,402 | 154.155 | 698.868 | 481,949.114 |
| Codex action-approval guardians | 7,388 | 1.888 | 3.231 | 16,948.359 |
| Claude turn-duration events | 677 | 26.179 | 337.240 | 202,997.512 |

A parent session may wait while several workers run, and their turns overlap. Summing them double-counts calendar time. A turn may include reading, discussion, API calls, builds or waiting and need not produce any code. Provider logging conventions differ, so the smaller Claude median is not evidence that one model or tool is faster. The role breakdown is necessary: treating approval checks as proof attempts would greatly inflate the number of apparent tasks and collapse the median.

The [timing analysis script](data/analyze.py) computes predecessor cohorts separately; they are not pooled into this table. Their usable Codex completion count is 995 and Claude duration count 240. Missing and noncompleted work remains a censoring risk. No stalled session is assigned a synthetic completion time, and no missing turn is treated as zero time.

## Traceable task intervals

| Episode | Recorded interval | Interpretation |
|---|---|---|
| Circuit builder #520 | Human implementation request 17:07:10.575 → PR creation 17:59:00, Oct 23: **51m49.425s** | Observed request-to-proposal interval; includes parallel work and interaction |
| Circuit builder #520 | PR creation → merge 18:35:22: **36m22s** | Review/CI/queue lead time after the proposal existed |
| Circuit builder #520 | Human request → merge: **1h28m11.425s** | Calendar interval for this bounded refactor, not all circuit-API work |
| Universal simulation #1852 | Oct 30 22:10:41 → Oct 31 15:12:40: **17h1m59s** | PR lead time; implementation began before PR creation |
| Named-cell Fibonacci insertion #2228 | Nov 1 23:46:44 → Nov 2 04:01:01: **4h14m17s** | PR lead time for a stacked milestone, not a complete Fibonacci-heap proof |

The transcript verifies #520's request timestamp and the public API verifies the PR dates. The other two rows have public PR evidence but no complete matched local authoring transcript. They cannot be labelled end-to-end autonomous completion times. [Excerpt verifier](data/transcript_excerpts.py), [PR #520](https://github.com/cslib-community/cslib-frontier/pull/520), [PR #1852](https://github.com/cslib-community/cslib-frontier/pull/1852), [PR #2228](https://github.com/cslib-community/cslib-frontier/pull/2228).

## Continuous integration

The complete selected-day cohort contains 231 merge-group runs created on October 31, all with latest recorded attempt 1: 225 succeeded and six failed. These runs occur after work has reached the merge queue. They exclude local failures, unsubmitted work, ordinary PR runs and rejected mathematical ideas, and therefore cannot estimate an automated-development success rate. Nor does CI failure identify a mathematical error: logs would need classification to distinguish build, tooling, resource and infrastructure causes. [CI collection methods](methods.md#github-evidence)

For the exact snapshot's successful merge-group job, explicit start/completion timestamps give **862 seconds**. Selected steps were:

| Step | Seconds |
|---|---:|
| `lake build` | 304 |
| `lake test` | 115 |
| `lake lint` | 52 |
| Restore Actions `.lake` cache | 65 |
| Reclaim hosted-runner SDK space | 91 |
| Stage merge-group outputs | 57 |

Other setup, hygiene, validation and bookkeeping steps fill the remainder. This is one observed cached CI job on a particular revision, not a cold-build benchmark or a measured cache speedup. The optional controlled handoff measurement was skipped in this job. Its measurement plan remains distinct from completed evidence. [Recorded CI run](https://github.com/cslib-community/cslib-frontier/actions/runs/41384852164), [measurement source](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/scripts/cache/MEASUREMENT.md)

No token-price, billing-cost or energy estimate is made. The available records do not supply a verified, uniformly defined all-provider/all-machine resource denominator.
