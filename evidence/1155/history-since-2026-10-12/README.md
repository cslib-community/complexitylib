# Systematic automation-history supplement, October 12 onward

Worker `audit_prerequisites`, additive history delta for #1155. The static inventory at `5bc08fe7` and worker560's method artifacts remain immutable. No Lean, bootstrap, cache, tactic/library source or production API changes; no new timing or mathematical audit.

## Search boundary and retrieved surfaces

- **Start:** 2026-10-12 00:00:00 UTC, inclusive. GitHub search date range ends October 26 inclusive. Primary retrieval ran **2026-10-26 18:53:24–18:57:45 UTC**; review/inline collection finished18:58:03, followed by one documented network recovery and explicit LiuPass follow-up snapshots. Every mutable body carries its own URL, timestamps and SHA-256.
- **Repository:** `cslib-community/complexitylib`. Sixteen explicit queries search **issue and PR titles, bodies and comments**, with `updated:2026-10-12..2026-10-26 in:title,body,comments`: `polytime`, `fun_prop`, `ppt`, `aesop`, `heartbeat`, `heartbeats`, `maxHeartbeats`, `maxSteps`, `timeout`, `encoding`, `"rule order"`, `"rule-order"`, `"manual composition"`, `"explicit composition"`, `"proof replacement"`, `regression`.
- [All 24 search pages](search-pages.json) preserve exact queries, returned IDs, totals and incomplete flags. No returned query was marked incomplete or exceeded the1,000-result API ceiling. [Search hits](search-hits.json) retain query membership. Known #608/#733/#862/#1063/#1137/#1148/#1155/#1168/#1171/#1184 surfaces are included independently of indexing.
- [648 retrieved issue/PR threads](github-corpus.json) provide **5,454 complete body/comment records**, retaining date-qualified comments and updated body context. No thread retrieval failed. This includes the full coordination threads, not only their first lines or a previous shortlist.
- [PR reviews](pr-review-corpus.json): **278 review bodies across417 selected PR surfaces**. [Repository-wide inline reviews](inline-review-corpus.json): **191 comments**, using the updated-since endpoint independently of search hits. One transient no-route error for PR240 was recovered by a single targeted retry; [the initial failure and recovery](review-targeted-recovery.json) remain recorded. [Review manifest](review-retrieval-manifest.json) distinguishes that recovery from a first-attempt success.
- [Pinned main diff scan](main-diff-index.json): **all1,344 first-parent transitions** through **5bffdf2f248bbbfddea6039ee25a953616dff15b**, filtered by the same start date, with explicit first-parent merge diffs. It finds603 commits/3,963 relevant Lean hunks. The131 removed-automation/added-composition hunks are **candidates**, not131 proved workarounds. Fourteen budget-directive hunks are retained. [Title matches](main-title-matches.json) are supplementary; the diff scan is not restricted to matching titles. Each result retains exact commit, raw-patch digest, path, hunk and lines. This covers proofs, tests, abstracts and guide Lean files. `--since-as-filter` was independently checked to return the same1,344 commits, avoiding a silent timestamp-order assumption.

GitHub activity can postdate the source pin: it is dated history evidence, not an advance of runtime source. A body updated in the window may discuss an older event. Reports of 'all checks pass' remain reports at their cited heads, not new validation by this survey.

## Deduplication and semantic classification

[Deduplicated evidence](deduplicated-evidence.json) merges identical **URL+body-SHA256** snapshots, preserving each source surface. It reuses all132 earlier recovered comment bodies and the previous13+3 curated records. Of6,057 retrieved/retained records, there are5,923 distinct URL/body snapshots and2,388 keyword-matching snapshots. These are **retrieval counts, not counts of regressions**. The lexical triage labels and matching paragraphs are an auditable search aid; e.g. the word 'regression' often describes a successful test, not a reported failure.

[29 curated case groups](curated-cases.json) separate actual cited reports/comparisons from performance hints, capability gaps, routine composition and mathematical elaboration budgets. Related reports are grouped rather than counted repeatedly across issues/PRs/reviews. Existing case groups can overlap; **29 is not an additive regression count**. [Citation-to-snapshot links](case-source-links.json) expose references not retrieved rather than silently calling them verified. [Classification summary](classification-summary.json) preserves the boundaries.

| Disposition | Concrete evidence and qualification |
|---|---|
| **Routine composition cleanup, not a workaround** | #71/#74 replace repeated AWPP/SBP `.comp`/`.prod` plumbing with existing automation and report no material module-level regression. Explicit composition alone proves no failed search. |
| **Reported performance bottleneck** | #267/#287 describe repeated local-context matching and historical before/after module timings. No current per-call cost or universal speedup follows. |
| **Documented bounded/conversion workaround** | #558/#567 explicitly report WPP slow default rejection and a bounded32-step attempt plus supplied-fact conversion under2k; verifier/counted arithmetic capability gaps are separate. This motivation is documented, not inferred from syntax. |
| **Slow positive replaced; coverage loss admitted** | #648 replaces three expensive `ppt` searches with `hrun.map (by fun_prop)`. It explicitly preserves theorem/runtime assertions but loses this `ppt` goal-shape coverage. Reported heartbeat units stay as authored, not pooled with current normalized events. Circuit evaluation materialization in the same PR is a separate runtime-test cost, not a tactic-search regression. |
| **Missing route/import, repaired** | #612 graph membership/negation; #627/#685 binary division/list length; #728 plain frontend selection; #756/#766 unsupported certificate diagnostics. A capability gap is not automatically a baseline-pass/new-fail or ordering regression. |
| **Corrected causal interpretation** | #813's fresh GMW/Oracle failures were closed by library-only #811+#823 support. Removing a raw registration alone was not the fix, and BEq was not required. The rejected early explanation is not revived. |
| **Actual unknown-private-rule failures** | #1037 reports a OneWayToSignature leak; #1205's broader repair is included in final5bff. These are related family occurrences, not automatically one event or a performance regression. |
| **Historical budget raises, now removed** | Main diffs show Bitonic `bool_min_bitonic`2M heartbeats/10k recursion introduced then removed by #349, and query-machine routines1.6M introduced then removed by #911. The Bitonic case concerns finite-proof enumeration, not `polytime` search. Current source's absence of raises does not erase these historical ones. Added200k test guards retain the default;12k/2k guards lower it, not raise it. |
| **Still-open arithmetic/search obligations** | #1137 ships named direct addition but leaves global automatic addition open; #1184's controlled attribute-location repair is distinct. Original LiuPass current positive/default-negative facts are below. |

The retained historical AddTrivial/Cloud/Extraction, nested Boolean, #1063, PPT114 preparation/apply and PPT59 shared-command records keep their exact revision/import, metric and causal qualifications. Their reported search thresholds/heartbeats/wall times are not transplanted to5bff. No source replacement, nearby commit, PR closure or chronology alone establishes causation.

## New LiuPass facts remain OPEN

[Current exact-pin facts](liupass-current-facts.json) and [supplier follow-up](liupass-supplier-facts.json), with [immutable failed/prototype packet7c2a9fdb](https://github.com/cslib-community/complexitylib/tree/7c2a9fdb/evidence/1155-regression-559):

- At both preserved d7d and fixed5bff, the original `unfold thresholdValue; fun_prop` on the original threshold expression **times out at unchanged200k**. Production explicit composition was not used as failure evidence.
- Three computed-operand unary add/sub/mul rules make the original positive and complete supplied-leaf positive pass at200k. This is separate draft #1215 supplier evidence, not a landed change to the frozen survey pin.
- The **full missing-leaf default negative still whnf-times out**, and its256-step version also times out. These are **OPEN**, not passing negatives or waived limits. Smaller three-operation missing-left/right controls pass at256steps/200k; they do not replace the full failed rejection control.
- The `Type*` attempt exposes the existing shared-universe composition limitation; the successful frontend diagnostic uses `Type`. No broader universe coverage is claimed. The trace reports a binary intermediate explored before the outer unary constraint; the proposed attribute-erasure A/B was not run because pinned Mathlib rejects erasure. No unique registration/order cause is established.

## Metadata qualification for dynamic synthesis

Worker560 identified a small static metadata qualification: in `5bc08fe7`, `module` is a **path-derived hint**, not a native module-validation result. For the configured guide source root it should omit `guide.`; for abstracts it should omit `abstracts.`. Preserve those immutable raw hints and use configured root + actual native metadata for validation. Verso snippet FileMaps can differ from the whole guide file; their local offsets/text must not be joined to whole-file spans merely from filename/line. This does not alter token identities or claim new AST verification.

## Verification and genuine residual limits

The evidence checks validate full body hashes, URL/body deduplication, query/page accounting and limits, date boundaries, all-source first-parent Git evidence, chronological budget introduction/removal, preserved old case IDs, current LiuPass open facts, and absence of invented timing. The tools perform read-only API/Git retrieval and standard-library Python data processing, no Lean/build execution.

This closes the old **unsystematic132-link-only search** limitation with an explicit repeatable range/surface corpus. It does **not** prove keyword search omniscience. GitHub indexing/tokenization can omit synonyms or newly indexed text; page results are not an atomic snapshot; deleted/inaccessible/edited-away text and private/pending reviews are unavailable. Review bodies are collected on selected PR surfaces, while inline reviews are repository-wide. Unknown/unreported failures and cases using none of the terms can remain undiscovered. Lexical candidates without a supported concrete report are not promoted to verified regressions. The original all-call runtime/rule/reachability work and missing rejection controls remain open.

Reproduce data retrieval with `collect.py`, `collect_reviews.py`; source diffs with `scan_git.py`; deduplication/case synthesis with `classify.py`. Live mutable results can change; the committed body digests/pin are the reproducible captured dataset. Existing artifacts and author credit remain intact.

**Subsequent metadata correction:** the LiuPass universe limitation is specifically in `pair`/`prod`; general composition has independent universe binders. See [the cited correction](CORRECTIONS.md). Historical captured reports/data remain unchanged; no measurement was recollected.
