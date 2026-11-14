# Diagnose proof and build failures

First identify the failed layer: elaboration, a mathematical obligation, certificate search, or the build environment. A tactic timeout does not identify which definition is wrong; a missing compiled import does not refute a theorem. Reduce the failure to the smallest relevant client before changing the interface. [cslib-frontier][complexitylib]

## Read the remaining goal

Use editor or MCP diagnostics and goal inspection. A partial diagnostic response means elaboration is still running. A missing search result is informative only when its index was actually consulted. When those tools are unavailable, use the smallest focused check supported by the checkout.

| Symptom | Inspect first | Next action |
|---|---|---|
| Unknown declaration or tactic | Import, namespace, revision | Compare the full checked client's imports and openings |
| `fun_prop` or `polytime` cannot close a composition | Each routine's certificate and encodings | Supply the missing certificate or expose a local wrapper's registered head |
| `polytime` cannot certify a length guard such as `if w.length = n then … else …` | Whether the comparison's natural-number encoding is ambiguous | Import [`PolyTime/Nat/Eq.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Eq.lean), whose `unary_eq'` fixes both operands to unary |
| A loop leaves obligations | Iteration count, invariant, encoded state growth | Prove the growth/count premise and use the appropriate iteration rule |
| A projection fails despite a supplied certificate | Its input/output representations | Match the encodings or supply the conversion certificate |
| `Expected a definition with an exposed body`, or `omega`, `decide` or a projection cannot see through an imported definition | Whether the definition's module exposes its body | Use the module's characterizing lemmas, or add `@[expose]` to that definition alone ([module surface](../../CONTRIBUTING.md#public-surface-under-the-module-system)) |
| `ppt` fails after a bind | Sampled-value and continuation encodings | Find a common encoding and the continuation's joint certificate |
| `ppt` is slow or exhausts Aesop's rule limit on a sample-then-call routine | Whether every definition the program unfolds through was passed as a hint | Pass the hints, or [compose the rules explicitly](probabilistic-workflows.md#certify-a-closed-randomized-routine) |
| `ppt` fails on an oracle goal | Whether the program is unfolded, and each query keeps a bounded `List.take` prefix | Pass the program's definition as a hint (`ppt [handler]`); for handler substitution or adaptive loops, apply the explicit rule and its invariant |
| A query bound does not imply runtime | Which operations the cost counts | Supply native realization and time/answer-length obligations |
| Logspace composition needs a large temporary string | Whether the rule stores or recomputes it | Use the appropriate replay rule and stated output-bound hypotheses |
| A RAM theorem does not apply to a Turing-time goal | Word width, basis and simulation | Apply a bridge and account for its overhead |
| An endpoint needs a powerful added assumption | Whether it supplies the desired result | Locate the missing construction and reassess the claim |
| `failed to read file … .olean` on `lake test`, `lake lint` or `checkInitImports` while focused builds succeed | Per-process Linux mapping limit `/proc/sys/vm/max_map_count` | Run `python3 scripts/check_vm_map_count.py` ([diagnosis](#diagnose-failed-to-read-file-on-whole-library-imports)) |

The [automation reference](../design-and-assurance/automation.md) documents the tactics. The [plain `polytime` implementation](../../CslibFrontier/Tactic/PolyTime.lean) and [`ppt`](../../CslibFrontier/Tactic/PPT.lean) may report a failed compositional attempt. This is a search hint, not a theorem of inefficiency or noncomputability. When `degree`, `logspace`, `space`, `fo_qf`, `fo_iso_closed` or `fo_definable` fails, the backend's error ends with a note saying what to supply: a certificate for the named routine, an unfolded definition, an input-length allowance, a bound on an answer vector or a registered rule. `degree` and `logspace` reject a goal of another kind before searching. The [failure tests](../../CslibFrontierTests/TacticFailureNotes.lean) show each failure next to the input that then closes the goal.

## Separate algorithmic growth from search cost

A loop needs both an iteration bound and a bound on state sizes. Doubling a list at every iteration has different growth from consing one bit. Before raising heartbeats, inspect the growth certificate and the representation the tactic selected.

For a large simplification goal, check whether a machine step or transition table was unfolded too early. Prefer its semantic lemma when possible. The repository forbids `[simp]` attributes on machine transitions because unrestricted unfolding can expand proof goals. Nonterminal simplification uses `simp only` when later steps depend on the result's form. These are robustness measures, not a replacement for the invariant. [Proof hygiene](../../AGENTS.md#proof-hygiene)

If several clients repeatedly need the same proof plumbing, search for a reusable lemma at the lowest suitable layer. Include a representative client with the improvement. A new abstraction should make that client clearer, not merely rename its difficult obligation.

## Diagnose missing or stale artifacts

Confirm that `lean-toolchain`, `lake-manifest.json` and dependency sources belong to the same intended revision. A warm `.lake` directory is not evidence of agreement. Handle intentional pin changes as dependency updates with client repairs. For immediate cache retry:

```bash
scripts/cache/ensure.sh --refresh
```

This retries restoration; it does not assert network or cache availability. The default reader
tries GCS, then MIT on a miss, failure or timeout. A GCS `403` can mean its budget kill switch
removed public access; the cache guide gives the maintainer recovery procedure. An explicit
`COMPLEXITYLIB_CACHE_URL` selects just that origin and disables mirror fallback. On a warm local
checkout, `COMPLEXITYLIB_CACHE_AUTO=0` opts out of automatic downloads for the wrappers while
retaining Lake's input checks. The [cache guide](../../scripts/cache/README.md#automatic-restoration)
specifies stamps, retries and seeding.

If a small change causes a large rebuild, inspect its imports and exported interface. Public declarations and exposed definition bodies can invalidate dependents. The [build fan-out case study](../history/case-studies.md) explains why widely imported hubs can be costly. A slow rebuild alone does not demonstrate a cache defect.

The output-based audits (`audit_queries.py`, `check_changed_files.py`, `check_tidy_surface.py`
and `check_tidy_usage.py`) need a complete build of the library and tests. Their shared
[`lean_outputs.py`](../../scripts/lean_outputs.py) preflight checks the physical output inventory
before invoking Lake: current source modules, including the root aggregate and glob-built tests,
must have their recorded module artifacts. The test-inclusive inventory also includes its
root-package `CslibFrontierResults` dependency, its aggregate and current result source modules.
Ordinary single-part modules and split module-system
outputs are distinguished by their traces. A cache entry or local `.ltar` archive does not count
as an unpacked artifact. A cold or partial tree is refused as missing or stale without asking
Lake to restore its missing outputs. `parallel_defs.py` uses the same guard with its existing
library-only scope; it does not require test or results outputs. Run `scripts/check.sh` explicitly when the checkout and
resources are ready for full validation, then retry the audit. `--no-build-check` disables
freshness verification; it does not repair missing artifacts or certify a partial audit.
`check_changed_files.py --source-only` skips its output-based module-doc name lint and needs
no build.

This inventory guard is a bounded mitigation, not a read-only Lake mode. For a complete output
tree, the retained `lake build --no-build` freshness check can still restore or replace outputs,
or publish artifacts to the local cache, even when the outputs are current. `--no-cache` does
not disable a package's explicitly enabled local artifact cache. Exact freshness without these
mutations remains tracked in [#4700](https://github.com/cslib-community/cslib-frontier/issues/4700).

## Diagnose warnings that only CI reports

Sometimes `lake build --wfail --iofail` or `lake test --wfail --iofail` passes locally while CI fails the same revision on a warning, such as a `longLine` lint in a new test file. This happens when another checkout on the same machine already built the module with the warning. Lake saves the outputs to the shared [local artifact cache](../../scripts/cache/README.md) even when the build logged warnings, but it does not save the messages. When your checkout builds the same source, Lake restores the outputs and writes a trace with `"synthetic": true` and an empty `"log"`, so there is nothing for `--wfail` to reject. CI fills its remote cache only from `main`, so it elaborates the new source and reports the warning.

After the Lean gates, full and quick `scripts/check.sh` both run `scripts/check_cache_restores.py`. Full mode checks all built sources in the root package, including unchanged clients, tests and executables. This conservative scope also covers deletions and configuration changes that cannot use quick mode's import graph. Quick mode passes its affected source files, including unchanged importing clients. It also checks built aggregates on those clients' import paths: an aggregate can warn about a deprecated import even when its importing client elaborates silently. Unused library aggregates are omitted. Selected executables add their built helpers and affected built aggregates conservatively because their helper imports are outside the library graph. These optional paths are audited only when outputs exist. A synthetic, missing or unreadable trace triggers re-elaboration; an ordinary trace has already replayed its messages during the build.

The audit fails on any message or elaboration failure. A reported message can also come from one of the file's imports, because `lake lean` replays their logs. Files are elaborated one at a time, so each restored file adds its elaboration time to the check; a full check after a large restore can take appreciably longer. To check one file yourself, run `lake -q lean <file>` and treat any output as a failure, because `lake lean` exits 0 after warnings. This closes the local audit's affected-client gap, but does not change Lake's cache format or cover dependency packages outside the root package. Bare Lake commands still need upstream Lake to store each entry's messages and replay them on restore ([#4523](https://github.com/cslib-community/cslib-frontier/issues/4523)).

Full and quick checks stream the restored-source audit's selected count, current source and
elapsed time before each elaboration, while retaining the complete output in their failure logs.
The final summary also reports total elapsed time. Successful audits currently leave synthetic
traces unchanged, so repeating the check can repeat that elaboration; ordinary targeted builds
do not run this audit. Follow the [focused validation workflow](getting-started.md#prerequisites-and-the-checkouts-version)
and use hosted CI for full validation when available.

When running the audit directly with `CI` set, per-file progress is quiet by default; use
`python3 -B scripts/check_cache_restores.py --progress` to request it, or `--quiet` to suppress
it locally. Both modes retain all selected checks, failure messages and the final summary;
the full and quick wrappers explicitly request progress.

## Diagnose "failed to read file" on whole-library imports

On Linux hosts and containers with the stock kernel default `vm.max_map_count = 65530`, focused module builds and `lake build CslibFrontier` can succeed while whole-library importers (`CslibFrontierTests/Smoke.lean`, `CslibFrontierTests/Axioms.lean`, `lake lint`, and `lake exe checkInitImports`) fail with bare errors such as `uncaught exception: failed to read file … .olean` or `.olean.private`, even though the named file is intact, readable, has a matching toolchain header, and imports cleanly in isolation ([#5012](https://github.com/cslib-community/cslib-frontier/issues/5012)).

Under the `module` system, importing a compiled module maps up to five files into the `lean` process (`.olean`, `.olean.server`, `.olean.private`, `.ir`, and `.ir.sig`). Importing `CslibFrontierResults` alone creates about 46,400 virtual memory areas (VMAs) across ~9,267 transitive modules, and importing `CslibFrontier` (as `Smoke.lean`, `Axioms.lean`, `lake lint`, and `checkInitImports` do) creates about 70,800 VMAs across ~14,133 transitive modules in one process. When a single `lean` process reaches `/proc/sys/vm/max_map_count`, `mmap` fails with `ENOMEM`; Lean's `src/library/module.cpp` heap-copy fallback then calls `malloc` and passes an unchecked `NULL` buffer to `read` (`EFAULT`), hiding VMA exhaustion behind a file-read exception. Inspecting `/proc/<pid>/maps` on the parent `lake` launcher (~6,000 mappings) misses this limit because the mappings belong to the child `lean`, `runLinter`, or `checkInitImports` executable. Keep this failure mode distinct from host-wide file-handle exhaustion (`fs.file-max`, below) and from `setImportedIREntries` segmentation faults on hosts that already have a large `vm.max_map_count` ([#4122](https://github.com/cslib-community/cslib-frontier/issues/4122)).

Full `scripts/check.sh` and `scripts/full_check.py` run [`scripts/check_vm_map_count.py`](../../scripts/check_vm_map_count.py) before whole-library steps; quick mode (`scripts/check.sh --quick`) does not require this headroom. To check the host limit or measure the live VMA breakdown inside a child `lean` importer process:

```bash
python3 scripts/check_vm_map_count.py
python3 scripts/check_vm_map_count.py --measure CslibFrontierResults
python3 scripts/check_vm_map_count.py --measure CslibFrontier
```

When an operator controls the host or VM kernel configuration, raise `vm.max_map_count` to `262144` or higher (for example `sudo sysctl -w vm.max_map_count=262144` or a persistent `/etc/sysctl.d/` setting; GitHub-hosted Ubuntu runners use `2097152`, and unprivileged containers inherit the host kernel's sysctl). Do not silently modify shared-host kernel settings without operator authorization, and do not claim a local full `scripts/check.sh` run passed when whole-library steps were skipped or blocked: validate affected modules with `scripts/check.sh --quick --no-full-fallback` (and targeted `lake build` commands), record the `vm.max_map_count` blocker in the PR or issue, and rely on hosted CI for whole-library validation.

## Diagnose "Too many open files in system"

On a shared host, concurrent builds can exhaust the kernel's file-handle table before they exhaust processors or memory. Each `lean` process maps the `.olean` files of every module it imports (several files per module), and each mapping holds a file handle until the process exits. A module that imports much of Mathlib holds tens of thousands. These handles appear in `/proc/<pid>/maps`, not among the process's file descriptors, so `ulimit -n` and `/proc/<pid>/fd` do not show them. They count toward the system-wide limit `fs.file-max`, whose value depends on the host configuration. Where it is about one million, a few dozen deep `lean` processes across all checkouts can reach it. The symptoms are `Too many open files in system` (`ENFILE`) from Lake, Lean or Git, and crashes in unrelated tools on the same host. On Linux, compare the allocated handles with the limit:

```bash
cut -f1,3 /proc/sys/fs/file-nr
```

One Lake build runs roughly as many `lean` processes at once as its thread pool allows, which `LEAN_NUM_THREADS` sets. Bound both that setting and the number of builds running at the same time on the host; CPU quotas do not reduce the handles. Build the changed modules and their clients rather than the whole library, and use hosted CI for the full validation run. Rerun the failed command once the count has dropped. Lake reuses the modules that completed.

## Distinguish the checks that passed

A focused build, quick changed-client check, whole-library build, full `scripts/check.sh` run and axiom audit have different scopes. Record the actual command and revision. Quick mode can fall back to the full suite; inspect its report. The [contribution chapter](contributing.md) specifies integration requirements.

If generated API documentation alone is stale after a module was removed, use the targeted cleanup in [the build instructions](../BUILD.md#build-the-api-reference). A library-wide clean discards unrelated warm outputs and does not repair an incorrect statement.

## Profile slow cache publication

If a `main` run builds quickly but takes much longer to publish its cache, inspect the staging
phase timings and archive counts in `CACHE_STAGING_METRICS`. The mapping-producing build can
pack missing module archives even when no Lean source needs recompilation. The
[cache publication profiling procedure](../../scripts/cache/README.md#profile-cache-publication)
gives the clean-checkout command, metric meanings and controls for a comparison. Separate this
preparation from upload time: both publishers consume the same complete staged files, while
MIT can transfer only missing archive payloads. Its `CACHE_HTTP_PUBLICATION` log reports the
request body sizes and whether it used incremental transfer or a full compatibility/race
fallback. The [protocol contract](../../tools/cache-origin/README.md#publication-contract)
explains those modes; a smaller upload does not mean staging became cheaper.

[complexitylib]: ../sources.md#complexitylib
