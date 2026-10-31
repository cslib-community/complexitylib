# Temporary handoff measurement (#1728)

This milestone installs dormant machinery. It authorizes no experiment, activation, repository
variable change, large snapshot or build-artifact download. [#1197](https://github.com/cslib-community/complexitylib/issues/1197)
remains open for the controlled measurement and net-cost decision. A coordinator must separately
authorize execution after independent CI/provenance/isolation review. Remove the workflow hooks,
`scripts/cache_handoff_measurement.py`, its tests and any plan after the study, or by
**2026-11-15**. The driver refuses plans beyond that hard expiry.

## Plan and prospective population

An absent `HANDOFF_MEASUREMENT_PLAN` repository variable is disabled. `{"mode":"disabled"}` is
also inert. The implementation PR does not set that variable. A future authorized plan has exactly
these fields (this example is a schema illustration, not an instruction to activate it):

```json
{
  "mode": "paired",
  "start": "2026-11-01T00:00:00Z",
  "end": "2026-11-08T00:00:00Z",
  "seed": "registered-before-timing",
  "sample_denominator": 4,
  "max_samples": 8,
  "max_bytes": 17179869184,
  "max_seconds": 1800
}
```

`mode` is `paired` or `randomized`. The window is at most seven days; limits are 16 intended
samples, 32 GiB of initial cache contents and a work deadline of at most 7,200 seconds per paired
case. Smaller explicit budgets should be registered. The driver hashes `seed:sample:run_id` modulo `sample_denominator`
over **all main-push runs created in the window**, then takes the earliest `max_samples` selected
runs. Failed, cancelled and unallocated runs consume slots; they are never replaced with successful
or slow cases. Hashes with separate `order` and `assignment` tags select BT/TB order and
restore/bypass assignment. The exact event SHA is bound at runtime. No future SHA whitelist or
performance-based manual selection is needed.

Keep the window, seed, sampling rate, cap, resource budget and source-stratum rules fixed before
timing. Preserve the plan and its changes in #1197. A cap reached early narrows exposure; it does
not justify extrapolating to the rest of the week. The driver fails closed on incomplete listings
or more than 1,000 main runs. A future plan needing larger coverage must predeclare shorter
windows/quotas and inventory them completely, rather than silently relying on API truncation.

## Same-runner paired pilot

1. The `prepare` hook accepts only a real canonical main push, attempt 1, with clean tracked
   sources and the unmodified `cache_handoff.source_context` checks. It records source SHA,
   toolchain, dependency pins, input digests, image/platform and selection. A HEAD request must
   show the target's public mapping is absent. Dispatch and already-published targets are excluded.
2. Normal Actions-cache, toolchain, Mathlib and Complexitylib bootstrap run once. The selected
   case captures the existing remote-cache helper's output. Before any arm, the driver verifies
   the reported remote revision and Actions matched-key revision are strict ancestors, records
   cold/unknown cases explicitly, and repeats the target-publication check. Source code and pins
   remain unchanged.
3. The snapshot includes **all mutable `.lake`, including dependency outputs**, and the actual
   Lake artifact cache. Each arm uses an isolated `LAKE_CACHE_DIR`, populated from that initial
   cache. Before **each** arm the driver resets both trees at the same checkout path and checks
   content/mode/mtime manifests. Baseline-generated root, dependency and cached artifacts must
   therefore disappear before treatment. External/absolute symlinks, Git control files, special
   files, nested cache roots and unsupported layouts are exclusions. No hard-linked mutable arm
   copies are shared. The pinned Lake cache layout and `LAKE_CACHE_DIR` are used; no invented
   cache-disabling flag is involved.
4. B bypasses the optional handoff; T invokes the existing restore CLI in its real event context.
   Its producer/run-attempt, source, configuration, platform, quota, archive and rerun checks are
   unchanged. A successful CLI exit is not a hit: the report retains the actual restore message
   and accepted producer ID/attempt. Both arms run the workflow's identical library targets,
   strict tests, lint, tidy checks, import generation, style and init-import checks.
5. The driver resets the initial state again before the normal production restore and required
   validation. These production gates remain outside the optional hook. A failed/excluded trial
   must not supply a validation success or suppress a required gate. A recovery failure is
   recorded and the ordinary workflow still validates whatever outputs remain through Lake's
   input checks. Experimental copies, resets and repeated validation are study overhead, not
   costs of the ordinary handoff policy.

The pilot makes ordinary copies and reserves space for rollback and the existing bounded
handoff. Large real caches can exceed the disk budget; record the exclusion and do not substitute
a root-only snapshot. Only tiny unit fixtures are exercised in this milestone. The optional
workflow timeout is a final guard; interrupted cases remain censored, never successful samples.
Timeout cleanup targets only the process group the driver created.

The work deadline covers snapshot creation, resets between arms and validation commands. File
operations check the deadline between files, so one filesystem operation can overrun it. Recovery
and cleanup may continue after the deadline to restore the initial state before production;
`max_seconds` is not a hard limit on the hook's total wall time.

Filesystem reset does not reset OS page cache, CPU frequency, background load or network state.
Counterbalance BT/TB order, repeat reversed-order cases on a small prespecified subset, and report
order sensitivity. Do not flush machine-global caches. Record `LEAN_NUM_THREADS` (including an
unset value), CPU count and image; keep the per-pair settings fixed.

## Randomized main cohort and publication

Paired trials measure conditional build/check effects, not the entire publication counterfactual.
`randomized` mode takes no snapshot and runs no extra validation arm: it records the same
prospective selection and uses its independent assignment hash to bypass or retain only the
ordinary optional restore. All normal required validation, Actions-cache saves and main-only GCS
authentication/publication remain in place. Missing producers remain in the assignment population.
This estimates marginal effects at the observed initial cache states; feedback through later
caches and the main queue remains a limitation.

Measure both Actions-cache save and GCS publication. Baseline builds can generate setup JSON
absent from restored outputs, changing `.lake` archive size. Never publish twice to the same
target and call the second upload a baseline: `upload.sh` uses create-only objects and writes its
mapping last, so the first upload changes the second one's work. It has no prepare-only option;
Actions-cache save has no dry-run input. Any future manifest/preparation-only comparison must
prove equal work before treating transfer cost as common. No dispatch may spoof push variables,
restore unverified artifacts or acquire the GCS writer role.

## Full ledger, exclusions and conclusion

Inventory two separate populations for the registered window, using paginated official API
run/job/attempt metadata and timestamped logs where needed:

- Every Lean Action CI main push: successful, failed, cancelled, superseded/unallocated,
  disabled, pre-restore failure, sampled/unselected, excluded and unknown cases. Creation time
  defines the cohort; retain and flag completions after the window. Do not infer individual
  cancellation reasons from `cancelled` alone.
- **Every eligible merge-group producer attempt**, including guard declines, failures,
  cancellations and successful artifacts that are never consumed. Link exact SHA, repository,
  workflow, run and attempt; classify unconsumed, in-flight, carried-in and carried-out cases.
  Reconcile source/workflow/kill-switch epochs. Current expiration does not establish historical
  availability. Do not condition staging/upload costs on a successful consumer.

For each population query `actions/workflows/lean_action_ci.yml/runs` with `event=push&branch=main`
or `event=merge_group` and the registered creation window, paginate all pages, and verify
`total_count` before filtering strict end-exclusivity. Split queries by predeclared day/time
windows if needed to stay below the API's 1,000-result limit. Fetch `jobs?filter=all` and exact
attempt metadata; do not replace failed attempts with their eventual successful rerun. The report
artifact contains metadata only. Official step timestamps supply production, staging, upload,
restore, post-check and publication times; the pilot also records its arm command walltimes.

Report main latency separately from summed runner seconds. Use paired differences or the
prespecified randomized estimator and actual sampling probabilities, not differences of medians.
Subtract **all** producer staging/upload costs for the chosen estimand, including unused work.
For a whole-feature keep/remove decision, also account separately for dedicated handoff regression
tests across CI events. Keep boundary costs/benefits visible rather than assigning an artifact
to whichever week looks favorable. Snapshot/reset costs and the extra pilot arm are experimental
overhead and must not masquerade as ordinary policy cost.

Predeclare documentation, proof-only, interface/import-fanout and pin-change strata using source
review, not timing outcomes. Retain fast cases, pin/hub outliers, budget failures and censored
cases; provide sensitivity results without deleting outliers. Report uncertainty and an
inconclusive result when the net benefit is small or uncontrolled publication/cache feedback
dominates. The pilot or a successful restore does not complete #1197. Archive the full ledger,
selection plan, exclusions and estimator in its issue before making the net-cost decision.
