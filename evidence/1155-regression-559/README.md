# Liu–Pass original automation checkpoint

Worker `review_559`; source pin `5bffdf2f248bbbfddea6039ee25a953616dff15b`.
Historical source pin `d7d78b18a8e9cd7e84212459c6074776b9da8208` and failed fixture commit
`886ca5b3` remain preserved. The byte-identical fixture on the current pin is `3662ebda`.
This is failed/prototype evidence, not a delivered library API or passing regression PR.

## Commands and outcomes

- `scripts/cache/get.sh` ran before each pin's first build. Mutable outputs are isolated in
  `complexitylib-codex/liu-pass-automation-1155`; pinned package sources were not edited.
- `lake build --wfail --iofail +ComplexityTests.AutomationLiuPass` failed at both pins.
  The original threshold positive, complete supplied-leaf positive and complete missing-leaf
  guard each reached the unchanged 200,000 heartbeat bound. The private-module warning is
  additional; it does not explain or waive those proof failures.
- `lake env lean -DwarningAsError=true /tmp/559-LiuPassThresholdTrace.lean` ran the original
  positive at the historical pin with theorem-local `trace.Meta.Tactic.fun_prop`. It timed out.
  The trace is attempted-rule evidence, not per-rule timing or final-proof attribution.
- `lake env lean -DwarningAsError=true /tmp/559-LiuPassUnaryFrontends.lean` first rejected the
  proposed `Type*` API bodies: existing composition infers a shared universe with the Nat pair
  primitive. Those failed bodies are not claimed valid; see the preserved source and log.
- `LEAN_NUM_THREADS=2 lake env lean -DwarningAsError=true
  /tmp/559-LiuPassUnaryFrontends.lean` with `Type` telescopes and three generic computed-operand
  unary add/subtract/multiply rules produces no error for either complete positive, but the
  complete missing-leaf guard still times out. The WHOLE command exits 1. This is positive-route
  sufficiency only, not a successful negative/control run or complete candidate validation.

No heartbeat/tactic/goal/encoding preference or production registration/backend was changed.
The original positive remains `unfold thresholdValue; fun_prop`; the generic supplied-leaf
positive is also automatic. The new rules use existing plain `.comp` and `.prod` only.
No local `[-fun_prop] trans` A/B was run: pinned Mathlib `FunProp/Attr.lean` explicitly throws
on attribute erasure. No invalid erasure experiment is counted.

The complete missing-leaf failure is OPEN. The smaller missing-operand alternative has not been
substituted or executed. Existing #1171/#1168/Extraction/PPT/Cloud controls are unchanged, not
freshly rerun or claimed covered by this prototype. The initial `lake env lean --wfail` trace
attempt stopped on the unsupported CLI option before elaboration and is excluded.

No local full build/six-gate run or comparative performance claim follows from these artifacts.
Process elapsed figures in Lake logs are not per-call heartbeat costs or program runtime.
Outside review is required for any eventual new public API; nothing here is that approval.
