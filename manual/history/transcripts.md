# Selected transcript evidence

These are 22 purposively selected, verbatim substrings from six local conversations. They document instructions and one assistant report, not a representative sample or a complete transcript. Original spelling is preserved. The [verifier](data/transcript_excerpts.py) checks each substring and role against the private source and can export record lines, timestamps, source-file SHA-256 and record SHA-256 into the ignored output directory. Raw paths, tool arguments, account data and internal reasoning are omitted. Bulk transcript records are not included in the repository.

The [case studies](case-studies.md) connect the utterances to public issues, PRs and current source. A request shows human intent at that point; it does not by itself establish that the requested work was completed.

## Circuit construction and scope control

<a id="e01"></a>
**e01 — 2026-10-23T16:56:47.874Z — human** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 10).

> (work on a worktree) seek improvements in the way this codebase is structured that could lead to large red diffs. tell me your ideas.

<a id="e02"></a>
**e02 — 2026-10-23T17:07:10.575Z — human** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 224).

> Please pursue 1. Let synthesis proofs track available wires automatically.

<a id="e03"></a>
**e03 — 2026-10-23T17:19:00.530Z — human** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 390).

> Do you think we're going to be able to build circuits which are efficient this way, or are we going to be introducing a lot of subtle inefficiencies?

<a id="e04"></a>
**e04 — 2026-10-23T18:11:47.778Z — assistant-report** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 1637).

> Existing statements and size bounds are preserved. Requested budgets are checked; choosing cheaper constructions remains explicit.

<a id="e05"></a>
**e05 — 2026-10-23T18:27:32.483Z — human** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 1644).

> Is this clear to a human reader?

<a id="e06"></a>
**e06 — 2026-10-23T19:46:59.289Z — human** (codex, session `01a169b1-4495-7152-bd98-79d79092095a`, record 1748).

> I feel like the budget-guided synthesis isn't really helpful maybe, don't read too much into that.

## Headline curation

<a id="e07"></a>
**e07 — 2026-10-22T21:30:38.024Z — human** (codex, session `01a16585-a242-7713-91d3-431e60c353f4`, record 10).

> Please inspect the accuracy of our claims and the code quality and drift from possible human intent or meaning.

<a id="e08"></a>
**e08 — 2026-10-22T21:36:39.246Z — human** (codex, session `01a16585-a242-7713-91d3-431e60c353f4`, record 374).

> Let's build intuitive, high quality abstracts for all of the major headline results.

<a id="e09"></a>
**e09 — 2026-10-22T21:54:36.245Z — human** (codex, session `01a16585-a242-7713-91d3-431e60c353f4`, record 957).

> Let's also try to have a higher bar for the theorems we broadcast as headlines.

<a id="e10"></a>
**e10 — 2026-10-22T21:54:54.279Z — human** (codex, session `01a16585-a242-7713-91d3-431e60c353f4`, record 961).

> We should make the smaller number all have abstracts and potentially abandon the paper/ tex list too

## Recovering the intended theorem

<a id="e11"></a>
**e11 — 2026-10-23T00:44:40.467Z — human** (codex, session `01a1661d-bea5-7cf3-8863-7095a0b208dc`, record 516).

> Yes, indeed. Look at the roadmap and what we've closed off of it. We had some really ambitious theorems, some of which we botched and rolled back

<a id="e12"></a>
**e12 — 2026-10-23T01:47:39.542Z — human** (codex, session `01a1661d-bea5-7cf3-8863-7095a0b208dc`, record 1070).

> Let's recover each of the ambitious theorem goals in sequence, reestablishing the credibility of the autonomous review and development loop.

<a id="e13"></a>
**e13 — 2026-10-23T09:02:58.693Z — human** (codex, session `01a1661d-bea5-7cf3-8863-7095a0b208dc`, record 2487).

> And this time we're going to do each of them at a high standard where they actually encode the true statement of the theorem, we're going to take our time to get this work done instead of rushing and getting a hacky version of it out like happened before

## Ergonomics with review

<a id="e14"></a>
**e14 — 2026-10-23T10:27:05.085Z — human** (codex, session `01a1661d-bea5-7cf3-8863-7095a0b208dc`, record 4139).

> Coordinators should be fairly sure such ideas are good ones when accepting them, not just acceepting arbitrary programming conventions.

## RAM model integration and credit

<a id="e15"></a>
**e15 — 2026-10-20T17:17:47.191Z — human** (claude, session `0ee2da73-c178-4fc8-86c0-8241ee284c9b`, record 7).

> What is the current state of RAM computation in here and proof automation around it?

<a id="e16"></a>
**e16 — 2026-10-20T17:41:22.582Z — human** (claude, session `0ee2da73-c178-4fc8-86c0-8241ee284c9b`, record 545).

> So it sounds like we should integrate both definitions.

<a id="e17"></a>
**e17 — 2026-10-20T17:44:22.743Z — human** (claude, session `0ee2da73-c178-4fc8-86c0-8241ee284c9b`, record 566).

> Perfect. Let's become a worker and integrate Demain's work and credit him or whoever else is an author in the original work in the files as an author.

## Build infrastructure and preservation of work

<a id="e18"></a>
**e18 — 2026-10-23T16:53:31.351Z — human** (claude, session `397e0b7e-0e98-445f-a58e-013e72aafef3`, record 7).

> are there useful ways we could improve compilation speed and developer ergonomics in this system, especially for AIs

<a id="e19"></a>
**e19 — 2026-10-23T17:14:05.336Z — human** (claude, session `397e0b7e-0e98-445f-a58e-013e72aafef3`, record 410).

> We should probably scan those worktrees for interesting diffs that have work we don't want to lose.

<a id="e20"></a>
**e20 — 2026-10-23T17:24:04.303Z — human** (claude, session `397e0b7e-0e98-445f-a58e-013e72aafef3`, record 742).

> Can we deploy our own cache for complexitylib itself?

## Follow-up semantic and performance audit

<a id="e21"></a>
**e21 — 2026-10-23T23:01:24.933Z — human** (claude, session `99a1aa4d-7729-44fd-9fab-3fab6ee2dc0a`, record 129).

> Are there any misformalized things present on main now

<a id="e22"></a>
**e22 — 2026-10-23T23:34:43.029Z — human** (claude, session `99a1aa4d-7729-44fd-9fab-3fab6ee2dc0a`, record 1142).

> Yes, after this work let's look into profiling the longest proofs.

## Interpretation boundary

The circuit conversation includes questions about cost and human readability, followed by a withdrawal of interest in a proposed feature. The recovery and headline conversations show direct editorial intervention in theorem meaning and selection. The RAM and cache conversations show choices about model coexistence, source credit and preservation of existing work. These observations contradict a description of the process as entirely unattended. They do not quantify how much human contribution was necessary, nor establish a causal productivity benefit from automation.
