# LARGER supported batch preparation ONLY — 12 files / 20 calls

Pin **3a6d770645c1217689da774f519cd785c253d8a2**. **NO Lean, elaboration, bootstrap, cache or build operation.** No runtime-sidecar/results/event metrics exist for this batch. Explicit later sole-builder handoff and review are required before execution; current source-fix/build ownership is untouched.

The authorized ceiling is25 complete original files/100 authored calls. This deliberate conservative subset selects **12 files/20 calls**:6polytime,7fun_prop,7ppt. It does NOT assert that other files are ineligible or compute any new global4003 coverage percentage.

## Selection and verified source context

Used the OLD67c6 census to triage an explicit26-file shortlist, then inspected actual complete3a6 source and target contexts. `selection-manifest.json` records selected and deferred candidates, not a fresh global census. Selected:

| Original file under Complexity/ | Targets |
|---|---:|
| Computability/PCP/Encoded/AddTrivial |1polytime|
| Computability/PCP/Encoded/Amplification |1fun_prop|
| Computability/PCP/Encoded/Amplification/Enumeration |1fun_prop|
| Computability/PCP/Encoded/Constraints |2polytime|
| Computability/PCP/Encoded/Preprocess |1fun_prop|
| Computability/Complexity/Problems/ExactThreeSAT |2fun_prop|
| Computability/Complexity/Problems/Partition |2fun_prop|
| Crypto/Computational/GeneratorPadding |1polytime,1ppt|
| Crypto/Computational/Prediction |3ppt|
| Crypto/Computational/Pseudoentropy/ExtractionSchedule |2polytime|
| Crypto/Computational/Pseudoentropy/RepeatedExtraction |2ppt|
| Crypto/Computational/Pseudoentropy/WordSeedExtraction |1ppt|

Every target occurrence in each selected file is a manually verified standalone bare theorem-body line, with no args/config, nested/quoted/generated target, custom syntax declaration or aggregate-only import source. No file is partially instrumented. Ordinary existing attributes, program_certificate registrations and imported facades remain unchanged; they are not calls. All unselected tactics remain individually unmeasured.

Deferred candidates are honestly distinguished: nested-proof target indentation; existing scoped/local fun_prop attribute contexts conservatively left for later; and two raw backtick-parenthesis hits that are actually DOCUMENTATION, not established Lean quotation syntax. Those two files may be eligible after refinement; no false unsupported-syntax claim is made. No automatic wider search to fill25 was attempted.

All original source bytes, credits, programs, resource/security/semantic claims, full captured encodings/assumptions, local facts, proof ordering and existing attributes are retained. Original AddTrivial's selected call is **isPolyTime_addLoops84**, not a reconstructed older AddTrivial proof. Whole full-source baseline is byte-identical to git. Import-only adds only the existing diagnostic import. Wrapped prefixes only the20 exact bare children. Reversal of wrappers/import yields exact original bytes for every file. No goal/proof reconstruction or baseline change.

## Module / declaration / import / option expectations

`mapping.json` contains original whole-file hashes, verified UTF-8 spans/lines, full IDs and globally collision-checked compact tokens, import order, exact namespace/variable/section lines and source declaration-header lines. These are SOURCE expectations, not an unelaborated native environment inventory. Future execution must preserve original relative paths with --root and confirm actual original main-module names, original imports(+onlyDiag) and matching actual source declaration sets across baseline/import-only/wrapped modes.

Private-bearing files are explicitly recorded: Preprocess5, ExactThreeSAT2, ExtractionSchedule1 private declarations. All private source/context remains; stable module names are intended, but identical generated auxiliary/macro names or selected opaque data identity are NOT promised. If actual native declaration/context checks differ, STOP rather than rename/transport/reconstruct anything. No new semantic/data assumption is authorized.

Selected files have NO option directives, heartbeat/recursion overrides or scoped target-option cases. Original package leanOptions and shared default200000/tactic defaults are recorded in config and must be identical across future modes. No async forcing, rule preference, budget increase, changed discharger or normalizer. Existing wrapper source hash is unchanged from b83; exactly one parsed-child evalTactic call and existing Except behavior, no registry mutation.

## Strict future acceptance, NOT actual results

`acceptance.py` is the previously reviewed fixed-batch checker logic, adapted ONLY to the explicitly enumerated12 cases/20 calls:36 complete whole-file commands and40 begin/end records expected. It keeps exact source/module/variant/run/sidecar provenance, valid present UInt64-range threads on BOTH records, global per-run event ownership, matching expected child kind/budget, returned/zero-goal outcome and nonnegative cost checks. Any partial/censored/unobserved/repeated/duplicate/unmatched/failed whole-file dataset rejects. This is consistency checking, not authentication against forged sidecars. Old Cloud/3call/limited3file parsers are untouched.

Data-only preflight verifies all hashes/spans and one SYNTHETIC full-contract smoke plus15 rejection controls (including both reviewed thread/eventID holes). No synthetic event/cost rows are saved as real measurements. `preflight-results.json` explicitly says NOT_RUN. These tests do not establish runtime restoration, concurrency, censor handling or collector scaling.

Validated driver/parser SOURCE from06e is copied byte-identically as run_after_handoff.py/parse_after_handoff.py (hashes in execution-contract.json). **They were NOT invoked.** This is reuse for one explicit data/config batch, not a new collector framework/AST rewriter. After explicit authorization they would execute each full baseline/import-only/wrapped once and stop on first mismatch. No compiler outputs may be published.

## Artifact-only reproduction now

```sh
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/larger-source-prep-3a6d/prepare.py
PYTHONDONTWRITEBYTECODE=1 python3 evidence/1155/larger-source-prep-3a6d/preflight.py
```

These run git/file/Python checks only. Do NOT invoke run_after_handoff.py, Lean, package/bootstrap/cache/build commands from this preparation task. All prior real accepted/rejected source/raw/parsed evidence remains byte-identical. No production PR or full survey completion. Full1155 and LiuPass gap remain OPEN. All jobs terminal; stop for review and explicit builder handoff.
