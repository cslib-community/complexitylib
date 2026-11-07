# Corpus and extraction methods

## Source and Git evidence

[`data/census.py`](../data/census.py) reads the fixed Git tree through `git archive`, hashes every inventoried Lean file, records imports, source authors and upstream markers, and counts lexical declaration headers after removing comments and strings. This avoids counting commented examples as declarations. It is still not an elaborated environment census: generated declarations, notation, aliases and mutually defined names do not correspond one-for-one to headers. The 42,236 `theorem` and 1,236 `lemma` headers must therefore not be presented as 43,472 independently novel mathematical theorems.

[`git_history.py`](data/git_history.py) exports the first-parent chronology, original metadata and `--no-renames` numstat. First-parent traversal gives a reproducible integration path; it intentionally excludes individual side-branch commits from that path's event count. Reachable commit count is exported separately. A merge may integrate many changes; a squash may condense many conversations; a refactor may delete and re-add the same mathematics. Additions/deletions measure textual churn. The net `Complexity/` line change reconciles exactly with the final physical line census: 1,094,225.

Git authorship is recorded metadata. It can represent the shared account committing an agent's work and does not authenticate who supplied the mathematical idea. Coauthor labels and Claude-session URLs are counted as disclosures. There are 611 first-parent commits with coauthor labels and 380 with Claude-session URLs, but only two distinct such URLs: the latter count clearly cannot be interpreted as 380 independently identified conversations. The [Git history script](data/git_history.py) can export the full public commit messages into the ignored output directory.

## Codex session extraction

[`session_census.py`](data/session_census.py) scans the local Codex session store, selecting metadata whose working directory or runtime workspace roots contain `complexitylib`. It reads both JSONL and Zstandard-compressed JSONL. The retained current cohort uses `/cslib-community/complexitylib` or a working directory ending in `/complexitylib2`; other matching identities are labelled predecessor. This is a transparent path rule, not a semantic classifier of every message.

Sessions are deduplicated by metadata ID, retaining the longer on-disk record if alternatives exist; none were duplicated in this extraction. Rows earlier than the session start or explicitly marked inherited by subagent-history ordinal are excluded when those fields permit it. Rows after the cutoff are excluded. These safeguards do not guarantee detection of all copied summaries or inherited text. Missing metadata, malformed rows, exclusions, raw-file digests and source kinds are retained as audit fields.

Completed-turn timing comes from `task_complete` event telemetry, with `duration_ms` retained separately from optional start/end and time-to-first-token fields. Completion means the turn ended, not that the requested mathematics succeeded. No missing duration is imputed. The analysis filters nonnegative numerical durations; 10,178 records across both cohorts meet that criterion. Three further exported completed-turn records have no usable duration and remain in the underlying data.

`subagent:guardian` is the action-approval subsystem. Its typically short turns must not be counted as independent theorem review or code-authoring sessions. `subagent:thread_spawn` denotes spawned agents but does not by itself distinguish author, coordinator and reviewer. Parent IDs permit some reconstruction of delegation; role assignment requires content inspection. The public exports retain IDs, hashes, event/tool-name counts and model-label strings, but omit absolute paths, messages, tool arguments and account/billing data.

The named model identifiers are labels in local records. They are not independently authenticated vendor/version attestations. Mixed model labels in one session can reflect switching; per-model file/session counts can overlap. They are not token usage, model costs or a benchmark of model quality.

## Claude record extraction

[`claude_census.py`](data/claude_census.py) scans only project-store directories whose name contains `complexitylib`. It uses the directory identity to assign current/predecessor cohorts, then deduplicates rows globally by UUID where available. It found 257,564 distinct UUIDs and excluded 6,189 repeated UUID rows. Rows without UUIDs cannot be deduplicated by that method. Because the first encountered copy owns the UUID, directory/cohort attribution of copied history is order-dependent; the extraction order is deterministic and the limitation is explicit.

Subagent files can share a top-level `sessionId`. The 473 current files contain 23 distinct reported session IDs; the 148 predecessor files contain ten. File counts, session-ID counts and independent work streams are different objects. The earliest current-path record is October 13, earlier than the current first-parent Git root's October 15 UTC timestamp. This may reflect earlier work or inherited records, but this pass did not establish the exact explanation.

Duration telemetry uses `system/turn_duration` records. These fields have a different logging contract from Codex completion events and are not pooled across providers. No model throughput or speed comparison is made from their distributions. Tool names and record counts are retained, while text, tool payloads and account data remain private.

## Qualitative transcript selection

The 22 excerpts in [the transcript chapter](transcripts.md) were purposively selected to illuminate design decisions and human intervention, not randomly sampled. [`transcript_excerpts.py`](data/transcript_excerpts.py) verifies each as an exact substring at its recorded source line and checks the message role. Its optional export includes source and record hashes, provider, session ID, timestamp, line, role and case label. Spelling is preserved. Surrounding content is omitted; no undisclosed textual rewriting is used.

Provider message roles need interpretation. A Claude `user` record can contain a tool result, command, continuation summary or delivered agent handoff rather than a human instruction. The selected records were inspected to exclude those cases. Codex final responses are explicitly labelled assistant reports; their claims are corroborated where possible with GitHub/source evidence instead of being treated as ground truth. Internal reasoning is not extracted.

Raw transcripts and path-selection provenance remain private. The maintained manual includes selected project excerpts and their interpretation; bulk metadata and transcript exports are not versioned. Regeneration requires access to the original logs and provenance. An academic study still needs an agreed archival/access arrangement before claiming public reproducibility of that corpus.

## GitHub evidence

The survey used issue and PR snapshots containing URLs, bodies, timestamps, state and selected metadata. These generated responses are not versioned; the chapters link their public sources. They describe recorded contributor claims and decisions, not independently replicated benchmark results. Issue closure is interpreted with its disposition: for example, #587 was wound down rather than completing its entire original quality programme.

The CI cohort consists of every merge-group Actions run returned for October 31 UTC across three pages, with 231 unique IDs matching the reported total. All happened to be named `Lean Action CI`. This was one chosen calendar day, not a random sample or a project-lifetime census. The exports contain each run's latest reported attempt and outcome at retrieval; all report attempt 1. No failure-cause classification was undertaken. `updated_at` is not used as a completion timestamp. The exact snapshot job's runtime uses its explicit `started_at` and `completed_at` fields.

## Reproduction levels

The source/Git analyses require the repository and its pinned history. The maintained books, link checks and model-map index need no research exports. Timing analysis requires the corresponding generated input files; recreating session inputs or verifying excerpts against originals requires private stores and provenance manifests. Refetching mutable GitHub responses cannot recover the exact historical bytes or expired runs. See [regeneration instructions](../BUILD.md#regenerating-research-outputs). Zstandard input needs Python 3.14's standard-library support or the optional `zstandard` package on an earlier Python. The raw files are hashed as their decompressed UTF-8 text, so their digests are not hashes of compressed container bytes.

The historical survey did not rerun Lean, run a cache experiment or perform a benchmark campaign. Later publication of this manual does not add such evidence.
