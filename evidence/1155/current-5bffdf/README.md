# Current-source automation index for #1155

Worker `audit_prerequisites`, [delegated static scope](https://github.com/cslib-community/complexitylib/issues/1155#issuecomment-6424027545). Final source pin: **5bffdf2f248bbbfddea6039ee25a953616dff15b**. This includes #1205's private-registry repair and #1207. The earlier [d7d preparation](../current-d7d78b/README.md) remains frozen. No further main advance is folded into this collection.

## What is complete

Every exact live-code `polytime`, `fun_prop`, and `ppt` token in **all 2,955 Lean files** under the four requested roots has a source-hash/UTF-8-byte identity, module/import context, enclosing command and lexical declaration/namespace, full command source, classification, option information and immutable source link. Arguments, nesting, tactic combinators, term proofs and non-bare forms are included; the index is not restricted to standalone tactic lines.

| Root | Lean files | `polytime` authored candidates | `fun_prop` authored candidates | `ppt` authored candidates |
|---|---:|---:|---:|---:|
| Complexity | 2,257 | 220 | 2,301 | 93 |
| ComplexityTests | 642 | 356 | 976 | 231 |
| abstracts | 51 | 0 | 6 | 2 |
| guide | 5 | 4 | 6 | 0 |
| Total | 2,955 | 580 | 3,289 | 326 |

Thus **4,195 authored tactic candidates**, nine quoted candidates, 1,798 attribute registrations and four quoted-name references account for **all 6,006 live-code target tokens**. There are 93 authored candidates with explicit argument syntax, including discharge tactics/configuration and theorem lists. Comment/string/character literals are masked while preserving coordinates. No matching documentation-text tokens were found in the scanned Markdown/text files.

These are **lexical classifications, not 4,195 parser-confirmed or executed invocations**. The exact Lean syntax kind, full parsed span, alias expansion, generated invocations, branch reachability and actual goal/property require the native forwarding collection. Candidate syntax extents are conservative source heuristics; the full original command is retained for correction. Source property names in an enclosing proof do not establish each tactic's elaborated goal. No syntax-directed coverage fraction follows from these counts.

## Auditable data and reproduction

- [Compact call/reference CSV](index/calls.csv) and [all token records](index/all-target-tokens.json): no omitted exclusions or silently discarded non-bare forms.
- [All source files/imports/hashes](index/files.json), [9,186 relevant full command contexts](index/commands.json), [all options](index/options.json), and [source pattern groups](index/command-signals.json).
- [Every composition/view/fallback/control occurrence](index/proof-plumbing.json): 17,999 masked-code occurrences with exact locations and command links. These include ordinary mathematical/data operations; they are **not 17,999 workarounds**.
- [Entry and forwarding signals](index/automation-entry-routes.json): 144 occurrences of `aesop`, `evalTactic`, `funProp`, or `solveTagged`, including direct `PolyTime`/`PPT` rule-set contexts that do not spell a target tactic. Attributes and generated/quoted/meta routes are distinguished lexically, not counted as extra executed calls. [Implementation contexts](index/automation-routes.json) retain the in-repository dispatch chain.
- [Summary](index/summary.json), [tool/dependency provenance](provenance.json), [validation](validation.txt), [seven executable Python checks](test_survey.py).

```sh
python3 evidence/1155/current-5bffdf/survey.py \
  --archive /path/to/immutable-c0e03da-evidence-worktree
python3 -m unittest discover -s evidence/1155/current-5bffdf -p 'test_*.py'
```

The source scanner reads `git archive` at the pin; it never reads Lean build artifacts or invokes Lean/Lake. The `--archive` tree supplies only tracked historical artifacts, read-only. Tests independently reconcile every source hash, byte slice and target occurrence, cover nested comments/strings/characters, non-bare arguments, registration/quotation distinctions, stable IDs, and strict full-parser-span joins/rejections.

## Options, shared budgets and manual composition

All **40 source option directives** are indexed: 27 command prefixes, eight source settings tracked through lexical section/namespace boundaries, and five nested non-budget setters explicitly unresolved. The source has 22 `maxHeartbeats` setters: 17 at 200,000, four at 12,000 and one at 2,000. **None raises heartbeats above Lean's 200,000 default**; explicit default retention is not a raise. The package's lakefile has no heartbeat override. Separate `maxRecDepth` setters and all other options remain visible. Source-selected authored-candidate limits are 4,189 at 200k, four at 12k and two at 2k. The two 2k calls share their enclosing command's budget; calls are not assigned fresh independent budgets.

Eighteen authored candidates carry lexical search configuration arguments. Effective values/consumption remain runtime-unconfirmed: command-local default selection is different from actual elaborator/CLI state, discharger/nested search limits, or shared command consumption. The five unresolved nested setters concern `synthInstance.maxSize`/linters, not heartbeat setters.

At the command level, source patterns identify composition, fallback alternatives, negative controls and raw/plain views. The detailed records retain all of them, including commands with no target tactic. `first`, `try`, `<|>`, `.comp`, `.prod`, etc. alone do not prove a failed search, successful fallback, manual repair, or necessity. Only the cited historical comparisons in the regression index support those semantic claims. No original proof/script/budget was changed to make collection convenient.

## Historical results and current dynamic join

[Archived artifact manifest](index/archived-artifacts.json) records every tracked worker560 artifact's hash and immutable `c0e03da5365cbf7b8b3050e315807ae0903478a7` URL. Its old manifests were not rewritten. [All 47 parsed historical observations](index/archived-observations.json) retain their actual source pin, run/sidecar/event context, outcome and units. [The explicit source join](index/dynamic-source-join.json) matches **46 of 47** historical selected calls by complete original source hash, UTF-8 token span and tactic name. The remaining MonotoneCircuitValue/Completeness source changed and is explicitly unmatched.

**Zero current-pin runtime observations were collected by this static worker.** Even the 46 identical source files may have different imported registries/dependencies/options at the new pin. Their old costs are not current measurements. Historical wall time, raw/user heartbeats and search-step intervals are not pooled or normalized into a ranking.

Worker560's native hook supplies actual syntax kinds/full parsed spans and authored/generated/context information without rewriting tactic grammar. [The source-join interface](join_runtime.py) distinguishes the static *head-token ID* from the runtime *full-syntax ID*. It validates pin, complete file hash, UTF-8 bytes/text, parser kind and provenance, then joins the exact source anchor. It rejects historical pins, mismatched hashes/text, invalid spans, missing kind/provenance and duplicate event identities. It does not certify run freshness or whole-file acceptance; those remain the dynamic collector's checks. The synthetic unit input is only a join test, never measured evidence.

## Regression/fallback history and remaining work

[Regression dispositions](regression-index.json) retain all 13 previously curated records and three later concrete developments. [Full historical comment corpus](historical-comment-corpus.json) recovers all 132 linked comment bodies behind the old keyword index, plus its two non-comment references; two mutable coordinator comments have changed body hashes, explicitly recorded rather than silently replaced. [PR/source dispositions](historical-pr-dispositions.json) and [#1155 thread](survey-thread-records.json) retain the evidence/limits behind the classifications. Keyword candidates are not 132 distinct verified regressions; this corpus does not prove every report on GitHub in fourteen days was discovered.

- **#1148 is resolved**, not pending: #1168 added the missing captured binary `≤` route and normal-module import exposure. Binary `≤`/callback failed while unary `≤` and binary `<` passed; selecting filter explicitly still failed at the callback. No established #1137/#1146 ordering cause is claimed. The original guide and meaningful negative controls remain in CI.
- AddTrivial/#1063 and Boolean/import controls are present in the current representative tests. Historical explicit-composition repairs remain distinguished from unchanged original automatic fixtures. Worker559 owns the remaining original LiuPass representative fixture; this static index reports no new runtime outcome for it.
- Default/global automatic **binary addition remains an open obligation**, explicitly retained by #1137; its named direct proof and local opt-in tests are not global successes. #1184's attribute-location A/B preserves the multiplication registration at its old facade. Neither is silently called a solved general ordering policy.
- Full native grammar/generated-call reconciliation, actual per-call options/goals/outcomes, rule firing, preparation/matching splits and current-pin runtime coverage remain the dynamic collection work. Each candidate starts unmeasured; absence of an event cannot yet distinguish unsupported syntax, unreachable branch, failed import/declaration, generated route or simply uncollected scope. No cases are excluded from the source index on those grounds.

This completes the static source-token/context/options/history index, not all of #1155's measurement or CI goals, and makes no production/API/math, S1/S4-completion, parser-completeness or performance claim. No Lean, bootstrap, cache, build or production source edits were performed.
