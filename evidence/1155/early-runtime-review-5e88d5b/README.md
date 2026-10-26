# Early independent raw-data sanity check

Snapshot: **5e88d5bedc4aa8187298284d09e346f612056b61**; runtime source pin5bffdf2f. Reviewer `audit_prerequisites`, nonauthor of the runtime implementation. This check **excludes the reviewer's static census/classifications/joins** and is not collector/framework or full647-file approval. No Lean/build/cache rerun, producer/input change or interruption of the ongoing collection.

Exactly three completed immutable file pipelines are checked: AC0, TFNP/Subclasses/Completeness, and Crypto/Computational/Basic. `check.py` reads Git objects only. It checks33snapshot artifact hashes; sidecar-bound producer/runner/parser/plan/header bytes; exact5bff originals; source-hash and insertion reversibility for all12variants; all four successful whole-command modes per file; same native module/import/source-declaration lists; unchanged nontrace flags; empty ordinary logs; complete unique event pairs, same-thread counters, full actual FileMap/UTF8 text/spans and inverse inserted offsets; run/provenance identities, trace event ownership/counts and per-thread nesting. No static call ID or guessed syntax extent is used as evidence.

Results: **12whole-file commands PASS**,22unique complete returned/zero-local-goal pairs (11measured and11traced), and23retained trace-message records. Native declaration counts are22/11/14 respectively, equal across each file's four modes. [Machine-readable check](result.json) and [qualified raw observations](observations.json) are retained for reuse in final reconciliation; do not repeat this bounded check unnecessarily.

Interpretation limits:

- Raw current-thread heartbeat counts /1000 give user heartbeat units. Body wall values are nanoseconds; process wall includes imports and shared-host scheduling. Instrumentation overhead still consumes the unchanged command budget. No cross-file/variant timing ranking is made.
- AC0's observed syntactic heads are `PolynomiallyBounded`; TFNP uses `ComputableTidilyInPolyTime`; Basic includes `IsPPT` and raw PT. The logged heads are explicitly unnormalized. The tactic spelling does not establish a plain-PT goal.
- TFNP contains a synthetic nested `fun_prop` dispatch whose actual source text/span is the outer `polytime`. It is a legitimate native event, not a second authored `fun_prop` site. Original source info can be true with macro-stack depth1; depth alone is not a generated/authored classifier. This does not assess the separately authored static-to-runtime mapper.
- Parent/child, repeated, synthetic, traced/untraced attempts and duplicated retained trace content cannot be summed as distinct authored call costs. Native traces are search-attempt observations, not a count of rules that fired in a final retained proof. Returned/zero-local-goal is not final-proof attribution.
- No hash mismatch, malformed pair, cross-thread raw cost, source-span mismatch, context mismatch or rejected whole-file variant was found in this subset. Private compiled-output hashes remain declared digests, not independent recompilation evidence. Raw logs are unchanged.

This is **3completed files only**. Unobserved/unsupported/censored/failing/generated/guide-local cases elsewhere remain the collector's explicit ledger; no full647coverage or blanket automation parity follows.
