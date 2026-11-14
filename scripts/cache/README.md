# Build caches

cslib-frontier's build has two caches. Both are optional: `lake build` without them compiles
everything it needs.

**Local artifact cache.** `lakefile.toml` enables Lake's content-addressed artifact cache, so a
module built in one checkout (a worktree, an agent sandbox, a second clone) is reused by every
other checkout on the same machine with the same inputs. Outputs are hard-linked back into
`.lake/build`. `lake cache clean` empties it; it lives in the Lean toolchain's directory under
`~/.elan` unless `LAKE_CACHE_DIR` says otherwise. Individual-artifact restores can lose diagnostic
logs, so `--wfail` can pass locally where CI fails. Full `scripts/check.sh` re-elaborates built
root-package sources restored this way; quick mode checks affected sources, including unchanged
clients, built import aggregates and executable helpers
([troubleshooting](../../manual/workflows/troubleshooting.md#diagnose-warnings-that-only-ci-reports)).

This audit recovers warning/info diagnostics; it is not an ordinary build or a proof-trust check.
Both check modes show its source count, current file and elapsed time while retaining failure
logs. A clean audit does not currently update the restored traces, so repeating it can repeat
the work. During ordinary edits, use MCP diagnostics or
`scripts/build.sh <affected modules and representative clients> --wfail --iofail`. At a local
checkpoint, use `scripts/check.sh --quick --no-full-fallback`; status 3 calls for focused checks
and hosted full validation. Run a full local check only when explicitly requested or hosted
coverage is unavailable, and do not repeat successful CI covering the final revision.

**Remote cache.** CI uploads the build outputs of every commit on `main`; `scripts/cache/get.sh`
downloads them for the nearest cached ancestor of your `HEAD`:

```bash
scripts/build.sh --wfail --iofail   # restore caches, then build changed or missing modules
```

A complete set of library and test outputs is about 200 MB compressed (November 2026). Outputs
are platform independent (`platformIndependent = true`), so Linux CI builds serve macOS checkouts.
The default reader tries GCS first, then MIT if GCS misses, fails or times out.
`COMPLEXITYLIB_CACHE_URL` overrides the entire list with one origin; set it to an empty string
to skip the cslib-frontier download. `COMPLEXITYLIB_CACHE_URLS` replaces the default ordered list
when the single-URL override is unset. To test MIT first with GCS fallback, use:

```bash
COMPLEXITYLIB_CACHE_URLS='https://complexitycache.csail.mit.edu https://storage.googleapis.com/complexitylib-lake-cache' \
  scripts/cache/get.sh
```

The ordered list applies only when the single-URL override is unset. Each origin gets a finite
attempt, including revision lookup and artifact downloads; partial downloads remain available
for the next origin. If every origin misses or fails, the normal build compiles the remainder.
This wrapper uses the native Lake reader and mapping/archive format. CI can override the same
ordered list through the repository variable `COMPLEXITYLIB_CACHE_URLS`; this setting does not
enable publication. GCS remains the preferred origin. MIT fallback is enabled so a GCS budget
shutdown does not force an otherwise cacheable build to compile from source.

`COMPLEXITYLIB_CACHE_ORIGIN_TIMEOUT` bounds each Complexitylib origin attempt (default 180
seconds; accepted range 0.1–600). Mapping lookups made by the missing-only helper also have
five-second connection and twenty-second request limits, within that origin's overall budget.
These limits cover lookup and transfer work together, including a stalled server.

Each origin reports its elapsed time and whether the native request completed, failed or timed
out. Completion means that request succeeded, not that the checkout is fully built or that all
artifacts were downloaded anew. Missing-only lookups retain the revision/module counts and
report the final HTTP/curl status when no usable mapping was found; a denied lookup is not
evidence that no uploaded artifacts exist.

CI reads the cache too. After restoring `.lake` from the GitHub Actions cache, Lean CI runs
`scripts/cache/get-missing.sh`, which downloads the same outputs except those of modules whose
input hash already matches a build trace in `.lake`. A fresh runner would otherwise download a
complete set on every run, although `.lake` usually has most of it.

Mathlib downloads are retried in the same checkout by `scripts/cache/get_mathlib.py`: at most
three ordinary `lake exe cache get` attempts, each limited to three minutes, with two-second
pauses. Completed archives remain in place, so the pinned Mathlib client retries only missing
downloads. Exhausted attempts warn and leave the strict build/check commands to compile what is
missing. On UNIX, shutdown sends SIGTERM to the attempt's own process group, allowing Git's
signal handlers to remove their locks, then waits up to five seconds before escalating to
SIGKILL and waiting up to five more seconds. Linux supervisors reap orphaned descendants too.
Windows and Cygwin use an owned Windows Job Object; the wrapper enrolls before launching a
downloader, and all descendants, including native Windows children, must stop before fallback.
The same installed Python is used; WSL or a second Python installation is not required.
Cancellation is deferred while cleanup drains the owned process tree. Parent exit alone is
not proof of shutdown. If cleanup cannot be confirmed, exit status **125** stops the build
instead of allowing a downloader to race compilation; ordinary cache misses and completed
timeouts remain optional. The helpers never remove Git locks; forced termination can still
leave one behind.

Lean CI and API docs call this helper with `--lean-action`, preserving the Mathlib URL
handling that lean-action had: unset `MATHLIB_CACHE_GET_URL` selects
`https://cache.mathlib.org/mathlib4`, an empty value selects the Mathlib client's default, and an
explicit URL is retained. Local `get.sh` and the Guide workflow use the same retries while retaining
their existing client-default/environment behavior. API docs also use the existing missing-only
cslib-frontier restore before generation. The Guide workflow restores Lean CI's `.lake` entry from
the Actions cache and then uses the same missing-only restore. Cache failures remain optional;
installation and validation failures remain strict.

The Lean workflows also restore elan and the toolchain named in `lean-toolchain` (`~/.elan`,
about 600 MB) from the Actions cache, so that no run depends on a GitHub release download. Lean CI,
the guide and API docs no longer run `leanprover/lean-action`: with every feature off it only
reinstalled elan from GitHub releases, without retries, so a release outage failed every run. On a
miss, `.github/actions/install-lean` installs them with bounded
retries and saves the entry before any Lake command runs, so it never contains the local artifact
cache above.

## Hosted-runner disk space

Before restoring `.lake`, Lean CI runs `scripts/ci/prepare-runner.sh` to report available disk
space. On GitHub-hosted Linux runners it removes the unused Android and .NET SDKs only when less
than 100 GiB is available, or the free-space measurement is unavailable. This conservative
headroom policy retains cleanup on constrained runners while avoiding several minutes of SDK
deletion on larger runners that already have ample space; it is not an exact build-size estimate.
Local and self-hosted invocations skip cleanup. The Lean toolchain, compiler, Python, Node
actions, repository and caches are retained. Cleanup is optional; all validation still runs if
it fails.

## Merge-queue handoff

After all required checks pass, a merge-group run packages its root `.lake/build` outputs in a
GitHub Actions artifact retained for two days. A `push` to `main` can restore that artifact before
building, avoiding a second compilation of the exact revision just validated by the merge queue.
The existing build, test and lint commands still run, and Lake checks its normal input traces.

The handoff accepts only the latest run's current successful attempt of `lean_action_ci.yml` in
this repository, triggered by `merge_group` for the exact landed commit. It checks the source,
run and attempt, toolchain, Lake configuration, dependency manifest and runner platform before
installing outputs. Native validation tools are included, so unlike the public per-module cache,
this handoff requires a matching runner OS, architecture and image version. A missing artifact, a rerun
still in progress, a changed commit or incompatible metadata leaves the normal build in place.
It never waits for another run to finish and does not reuse artifacts from pull-request runs.

`scripts/cache_handoff.py` creates a compressed archive with its digest and provenance, validates
the complete archive before restoration, and swaps the root build directory without modifying
existing hard-linked cache objects. Merge groups do not publish to GCS: the normal successful
`main` run remains the only public-cache writer. This makes its outputs available sooner to
following builds while preserving the public cache's authorization boundary.

- **Payload.** The archive keeps compiled outputs (including private/server OLeans, IR and native
  code), hashes and traces. It omits only `ir/**/*.setup.json` and `ir/**/*.irsetup.json`: Lake's
  transient compiler setup inputs. Lake writes these inside a compilation action and does not
  require them to reuse completed modules. Other JSON files are retained. File-type/link checks
  still cover omitted entries. The payload limits are 300,000 files, 12 GiB unpacked and 4 GiB
  compressed; a full build measured 101,848 files, 4.64 GB and 1.67 GB on November 8, 2026. The
  earlier 100,000-file, 4 GiB and 1 GiB limits had been outgrown, which silently disabled the
  handoff. Packing reports retained and omitted counts/sizes, and in Actions a limit miss or any
  other unavailable handoff is a workflow warning on the run summary.
- **Kill switch.** Setting the repository variable `DISABLE_BUILD_HANDOFF` to `1` or `true`
  (`gh variable set DISABLE_BUILD_HANDOFF --body 1`) disables both merge-group staging and `main`
  restoration without a commit; `scripts/cache_handoff.py` also honors `DISABLE_BUILD_HANDOFF` in
  its environment (treating any value other than empty, `0`, `false`, or `no` as disabled) as a
  defence in depth.
- **Trace and warning retention.** The handoff archive preserves `.trace` files, which record both
  the input hashes and each module's build log. Lake replays a saved log when it treats a restored
  module as up to date, so `main` still shows the merge-group warnings and `lake build --wfail`
  still fails on them. The producer also stages the handoff only after its own `--wfail --iofail`
  build and tests have passed on the same commit and platform.
- **Interrupted swap fallback.** `install_build` moves any existing `.lake/build` aside to a
  staging backup before renaming the unpacked directory into place, rolling back if the rename
  fails. If the process is killed between moving the previous `.lake/build` aside and completing
  either the new rename or the rollback, `.lake/build` is absent (with the original outputs
  retained in the temporary staging directory) and the subsequent `lake build` safely recompiles
  from source and the local artifact cache.
- **Superseded merge-group runs.** Each merge-group run has its own concurrency group, so GitHub
  does not cancel a run whose entry has left the queue: the entry landed inside a later group, or
  its group was rebuilt after an ejection. The *Merge-queue cleanup* workflow
  (`scripts/ci/cancel_stale_merge_groups.py`) cancels such runs after each push to `main` and every
  10 minutes. It skips runs younger than 5 minutes and runs for the current `main` commit, and
  cancels a run only after a fresh read of its queue branch returns 404 or another commit; any
  other error keeps the run. The handoff above is not affected, since it only uses a completed
  successful run for the landed commit. Run the script without `--apply` for a dry-run list.

## Automatic restoration

`scripts/build.sh` runs `scripts/cache/ensure.sh`, then forwards its arguments and exit status to
`lake build`. `scripts/check.sh` uses the same bootstrap before full or quick validation; a quick
check that falls back to the full check does not download twice. Bare `lake` commands do not
bootstrap. Before using Lean MCP diagnostics or another operation that can elaborate/build in a
cold checkout, restore available outputs with:

```bash
scripts/cache/ensure.sh
```

This guidance applies to every agent client. Retry for missing outputs or new toolchain/dependency
inputs; a new commit or branch switch alone does not require a manual bootstrap when outputs are
warm. MCP's `lean_build(fetch_cache=true)` only fetches Mathlib's cache, so it does not replace
cslib-frontier cache restoration.

The bootstrap records a completed **attempt**, not a successful cache hit, in
`.lake/cache-bootstrap/attempt.json`. For ten minutes it skips another attempt with the same
checkout path, `HEAD`, toolchain, manifest, Lake configuration, ordered origins/single-URL override,
download deadlines, recovery generation and `LAKE_CACHE_DIR`.
Working proof edits do not trigger another download. A changed `HEAD`, pin or configuration
triggers a new attempt; an unchanged state is retried after ten minutes, including a previous miss or
network failure. The stamp is written atomically after the fetch command finishes.
The bootstrap prints when it starts and finishes an attempt, and when it reuses a recent
attempt record. These messages include elapsed time or record age and the fetch exit status;
an optional fetch can exit zero after a miss, so neither a zero exit nor the stamp certifies a hit.

```bash
scripts/cache/ensure.sh --refresh             # retry now, e.g. after clearing caches
COMPLEXITYLIB_CACHE_AUTO=0 scripts/build.sh    # skip automatic downloads deliberately
```

For warm local builds, the opt-out avoids unnecessary remote attempts without disabling Lake's
normal source/input checks. It also applies to `scripts/check.sh`, `scripts/worktree.sh` and direct
bootstrap calls.
It leaves existing build outputs and Lake's local cache in place. `scripts/cache/get.sh` remains
the explicit, unstamped fetch command. Cache misses and download failures are optional: builds
compile what is missing, and the bootstrap never claims that all requested artifacts were
available.

The whole bootstrap has a watchdog as well. Its default budget is 630 seconds plus
`number_of_origins × (origin_timeout + 10)` seconds, allowing for Mathlib retries and cleanup.
`COMPLEXITYLIB_CACHE_BOOTSTRAP_TIMEOUT` can override that budget (0.1–7200 seconds). A normal
timeout leaves the build to compile missing outputs after child cleanup; an unconfirmed
shutdown returns 125 and stops the build/worktree preparation rather than racing a live writer.

By default, `scripts/worktree.sh create` and `scripts/worktree.sh seed` run
`scripts/cache/ensure.sh` in the worktree after seeding `.lake` caches. The helper never points a
worktree at the primary checkout, refuses targets or destination cache symlinks that do,
isolates dependency `.git` directories and
`gitdir:` pointer files so Git operations in a worktree cannot modify the primary checkout's `HEAD`
or `index`, and dereferences any package symlink whose target is absolute or escapes the package
directory. Pass `--copy-cslib` or `--copy-packages` when package sources must change.

When the primary checkout's outputs are changing or use different pins, create a worktree without
copying its initial `.lake` contents:

```bash
scripts/worktree.sh create feature/example example origin/main --source-only
```

`--source-only` skips initial root and dependency outputs, package sources and package Git controls.
The same target and cache isolation checks still run before bootstrap. Both modes refuse existing
symlinks anywhere in root cache trees or dependency `.lake` trees, including nested output paths;
package source and Git-control trees are not traversed by this check. Bootstrap remains automatic
unless `COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP=1` or the usual cache opt-out is set; it may
populate the new checkout with independently materialized dependencies and restored outputs.
Lake can reuse its immutable artifact cache, but expect dependency downloads and disk use for
independent package checkouts, and compilation when outputs are unavailable. This option cannot
be combined with `--copy-cslib` or `--copy-packages`; the default seeded behavior is unchanged.

## Trust and privacy

Downloaded `.olean` files are trusted by Lean: imported modules are not re-checked by the
kernel, and their compiled code (tactics, macros, initializers) runs during your build. Whoever
can write to the cache could therefore make a false theorem appear proved or run code on your
machine. Both default origins receive the same staged outputs from validated `main` builds,
but have different publication credentials and operators:

- Only push runs on `main` in this repository can obtain the GCS writer identity. It uses
  GitHub OIDC through Workload Identity Federation, restricted to this repository, main ref and
  push event. Pull requests, forks, merge groups and other branches cannot obtain that identity.
- The GCS writer can create objects but cannot delete them, so it cannot replace existing
  objects. The MIT publisher instead receives an upload password only in its final protected
  job step. MIT fallback also trusts that credential and the MIT origin operator, as described
  in the migration section below.
  Lake checks every downloaded artifact against the hash recorded in its mapping.

Merge-gating CI also reuses these outputs. Lean CI on pull requests, merge-queue groups and
`main` pushes restores modules that earlier `main` runs uploaded instead of compiling them, so a
module restored this way is not re-checked by the kernel in that run. CI already restores
`.lake` from the GitHub Actions cache, where runs on `main` save the copies that other branches
and pull requests fall back to, and Lake reuses those outputs in the
same way. Both remote publishers normally receive only validated `main` outputs; this does
not protect against a compromised publisher or origin (the Actions cache also holds a pull
request's own earlier runs).

Lake reuses an output only for a module whose input hash (its source, the outputs of its
imports, its options and the toolchain) matches the one uploaded. Every module that differs from
what `main` CI built, which includes every module a pull request changes and every module that
imports one, is still compiled and kernel-checked in the run. `lake test` rebuilds every such
test module, and `lake lint`, `mk_all --check`, `lint-style` and `checkInitImports` run as
before. Lake replays no build log for a restored module, so `--wfail` cannot see its warnings;
this loses nothing, because `main` uploads only outputs whose build and tests passed `--wfail`.
When nothing is cached, CI compiles everything, as before.

The cache contains only build outputs of commits on `main` (sources that are public in this
repository); build logs and machine paths are not uploaded. Downloads remain anonymous HTTPS
requests to GCS or, when GCS restoration fails, MIT. An explicit origin override can change
that order or select a single origin.

## MIT origin migration

The fallback [HTTP origin](../../tools/cache-origin/README.md) uses nginx for HTTPS,
upload authentication and public file serving, plus a small Linux Go executable for synchronous
publication and garbage collection. MIT owns the VM, operating-system updates, DNS/TLS,
credentials, bounded storage and monitoring. The repository supplies source and operator examples,
not automatic provisioning. There is no SSH upload or S3 service dependency.

The deployed MIT origin is **https://complexitycache.csail.mit.edu**. The
[dated deployment status](../../tools/cache-origin/README.md#mit-deployment-status) records the
installed source and completed host checks. As of November 7, 2026, main CI publishes real builds
successfully to MIT and GCS, and `cache-server-publish` is restricted to `main`. GCS remains the
preferred reader, with MIT as the default fallback. Making MIT the preferred origin remains a
separate decision; the real MIT cold restore and recovery exercise remain tracked in
[#2503](https://github.com/cslib-community/cslib-frontier/issues/2503).

After all required Lean checks, `publish.py stage` records the exact clean producer revision
and SHA-256 inventory once. GCS and the separate MIT publisher job consume those same staged bytes.
The MIT job verifies this run's artifact ID and producer revision before obtaining its upload
password for the final step. It sends the complete SHA-256 inventory and mapping in a small
USTAR probe to `PUT /publish/<commit>` over HTTPS, then uploads only missing archive payloads
alongside that same complete metadata. The server rechecks every omitted retained object under
its publication/GC lock before making the mapping visible. An old server's 415 triggers a full
upload; a GC race's 412 triggers one full retry. See the
[protocol and compatibility contract](../../tools/cache-origin/README.md#publication-contract).
curl retries transient failures; credentials travel through its stdin configuration rather
than URLs or command-line arguments.

The handler validates the whole package before publishing anything, installs artifacts before
the mapping and rejects conflicting existing keys even when the client omits conditional headers.
Identical retries succeed. HTTP credentials allow publication only: there is no remote deletion
or administration route. Anonymous `GET`/`HEAD` expose exact artifact/mapping keys without listing.
GC locally preserves the newest publication across all toolchains, expires other mappings after
two days and deletes artifacts immediately when no retained mapping refers to them. See the
[retention contract](../../tools/cache-origin/README.md#retention-and-cleanup).

The GitHub environment restricts when Actions receives the password; the server does not establish
that a request came from a main push. The publisher, credential and origin operator are trusted.
A stolen password can publish malicious bytes under unused or collected keys, and the origin
operator can change served bytes. Hashes establish transfer consistency, not producer provenance;
Lake's native artifact hash is 64-bit and not cryptographically secure. Existing keys reject
conflicting writes, but GC retains no permanent key ledger. Retention frees server storage and
does not revoke downloaded outputs. The [security contract and recovery procedure](../../tools/cache-origin/SECURITY.md)
explain this boundary and cleanup of **both origins, Actions caches/handoffs and local caches**
before rebuilding with restoration disabled. These MIT trust requirements apply whenever a
reader reaches the fallback, as well as to an explicit MIT-first override.

For a new installation, commission the actual server before enabling publication: verify TLS,
upload authentication, Unix-socket permissions, service restart, storage limits and GC; prove
concurrent conflicting uploads cannot replace a key; test unauthorized PUT and all DELETE requests.
Before making MIT the preferred reader, cold-restore a real build through the public HTTPS
origin and exercise recovery. CI checks the same nginx routes over loopback TLS, but cannot establish
the target host's identity, permissions or disk configuration.

A repository administrator can prepare the GitHub environment `cache-server-publish`, restrict it
to `main`, and configure the following using the privately supplied publisher password. On a new
installation, keep publication disabled until the commissioning evidence and integration are approved.

| Kind | Name |
|---|---|
| Environment secret | `CACHE_SERVER_PASSWORD` (43-character base64url encoding of 32 generated random bytes) |
| Environment variable | `CACHE_SERVER_USER=cache-publisher` |
| Environment variable | `CACHE_SERVER_URL=https://complexitycache.csail.mit.edu` (origin without a path) |
| Repository variable | `CACHE_SERVER_PUBLISH_ENABLED` (`false` until commissioning passes) |

Enabling publication does not change readers. The checked-in reader order is GCS first, MIT
second. Keep both publishers enabled so either origin can serve the same validated revision.
Making MIT primary or removing GCS requires a separate reviewed change after the cold-restore
and recovery checks; enabling fallback does not complete those checks. At every stage, an
empty cache remains an optional performance loss rather than a build failure.

For emergency recovery, `DISABLE_CACHE_RESTORE=true` disables the updated restoration helpers,
Actions `.lake` restoration/saving and merge-group handoffs. Updated workflows also disable
Lake's automatic cache use in this mode. `CACHE_RECOVERY_GENERATION` (default `0`) separates
Actions cache keys and handoff metadata from previous incidents. These controls do not delete
old data, revoke an origin, stop old workflow revisions or disable publishers: follow the
[full recovery sequence](../../tools/cache-origin/SECURITY.md#if-a-publisher-origin-or-restored-output-is-compromised).
Neither variable changes Lake's artifact IDs or ordinary retention.

This PR does not complete repository-managed provisioning or automated upgrades. Those remain
open under [#2503](https://github.com/cslib-community/cslib-frontier/issues/2503); the
[milestone scope](../../tools/cache-origin/SECURITY.md#scope-of-2506-and-remaining-2503-work) separates
the source/host checks from remaining cold-restore, recovery and preferred-reader decisions.

The HTTP publisher reports `CACHE_HTTP_PUBLICATION`: `mode` is `incremental`, `legacy-full`
(old server), or `race-full` (GC removed an omitted object). `archives_sent` counts payloads in
the final package; `request_body_bytes` lists every protocol package, including the probe and
any full fallback. It excludes curl's automatic retransmissions and HTTP/TLS overhead. This
measures transfer reduction, not archive preparation: the complete local staging directory
and its digest verification are still required. A 409 remains a hard conflict, not a cache miss.

## Profile cache publication

Publication reports separate wall times for the mapping/archive build, archive staging and
inventory hashing. Each phase prints its start and outcome; a successful stage also emits one
`CACHE_STAGING_METRICS` JSON line. A failed phase keeps its textual diagnostic and command failure.
The report records the source revision, toolchain, platform,
explicit `LEAN_NUM_THREADS` value (or null when unset), mapping entries and root `.ltar`
counts/bytes before and after the mapping build. Archive sizes are logical sizes, including
hard-linked files; they are not physical disk usage.

From a clean checkout with its dependencies and validated outputs available, stage into a new
directory outside the checkout and optionally keep the same metrics as JSON:

```bash
publication_dir=$(mktemp -d)
python3 -B scripts/cache/publish.py stage "$publication_dir/outputs" \
  --report "$publication_dir/metrics.json"
```

This stages local files. The report is kept outside the publication inventory. Wall time and
the Python process's CPU time are recorded on every platform; completed-child user/system CPU
times are included where Python's `resource` module is available. Child CPU includes the waited
command and its waited descendants, not a separate measurement of each subprocess or peak memory.

`lake build ... -o` can create missing per-module archives even when the Lean outputs are warm.
The pinned Lake implementation calls `packLtar` when output tracking finds no archive
([source](https://github.com/leanprover/lean4/blob/v4.36.0-rc2/src/lake/Lake/Build/Module.lean#L1336)).
Compare archive counts, phase CPU/wall time and unchanged compiled outputs before attributing
a long mapping build to recompilation. The real-Lake publication test checks missing versus
retained archives with fixed tiny sources and verifies that OLean hashes and mtimes stay unchanged.
It establishes that mechanism, not a speedup estimate for a full CI build.

By default, CI saves its Actions `.lake` snapshot before publication staging, so newly packed
archives can be absent from that snapshot. The repository variable
`RETAIN_PUBLICATION_ARCHIVES=true` enables a reversible experiment: the ordinary save is skipped
and the same `.lake` path and key are saved after staging and the publisher handoff. Actions string
comparisons are case-insensitive, so any capitalization of `true` enables the experiment; an absent
variable or every other value disables it. Retention is best-effort because the pinned cache-save
action reports ordinary save failures as warnings.

Use adjacent, representative `main` pushes with the same toolchain, thread settings, recovery
generation and comparable source changes:

1. With the variable absent or unequal to `true` under the case-insensitive comparison, record the
   source SHA, Actions restore/save duration and bytes, and `CACHE_STAGING_METRICS` archive counts
   and mapping-build time.
2. Set the variable to `true` in any capitalization for one `main` push. Record its late save
   duration and bytes as well as the staging metrics; this run creates the snapshot that can retain
   new archives.
3. Keep it at `true` for the next representative `main` push. Compare restore duration and bytes,
   `archives_before`, and mapping-build wall time with the baseline. Actions cache keys include the
   commit SHA, so rerunning the first activated SHA cannot replace its already-created key.
4. Roll back by deleting the variable or setting it to a value other than `true`, ignoring case.
   The ordinary pre-publication save resumes immediately. A retained snapshot may still be restored
   until a newer matching snapshot displaces or evicts it; rollback does not delete Actions cache
   entries.

This protocol tests the ordering change; it does not establish a speedup. Both remote publishers
consume the same staged files, so the mapping/archive phase still delays fresh outputs on both
origins.

## Maintainer runbook

The cache runs in a dedicated Google Cloud project maintained by Samuel Schlesinger.

**Setup.** `PROJECT=<id> BILLING_ACCOUNT=<id> ALERT_EMAIL=<address> scripts/cache/setup-gcs.sh`
creates, in order (each step can be rerun alone, e.g. `setup-gcs.sh alert`):

| Step | Creates |
| --- | --- |
| `project` | the project, billing link and APIs |
| `bucket` | `gs://complexitylib-lake-cache` (`us-east1`), public read by object name without listing, no soft delete or versioning, revision mappings expire after 180 days |
| `writer` | the GitHub identity pool and provider, and the `lake-cache-writer` service account (create + read on the bucket only) |
| `budget` | a monthly budget (default 100 USD, overridden by `BUDGET_USD`) with alerts at 50/90/100 % and a Pub/Sub topic |
| `killswitch` | a Cloud Run function that removes public read when the budget is reached or the egress alert fires |
| `alert` | an alert on more than 20 GB sent per hour, to the kill switch and `ALERT_EMAIL` |
| `variables` | prints the `gh variable set` commands for the three repository variables |

CI skips the upload until the repository variable `LAKE_CACHE_BUCKET` is set.

**Costs.** Storage is small: each `main` push uploads only modules whose outputs changed. CI
downloads only what its restored `.lake` lacks: nothing when the Actions cache is current, about
12 MB when it is a few hundred modules behind, and a complete set (about 200 MB) when it misses.
Cloud Storage's free tier covers 5 GB of storage and 100 GB of egress per month in `us-east1`;
at 150–200 CI runs a day, a complete download on every run would exceed that several times over
and soon reach the budget. Workflows that read the bucket therefore restore `.lake` from the
Actions cache first and download only what it lacks. The budget alerts and the kill switch bound
abuse of the public bucket.

**After the kill switch fires.** GCS downloads fail and readers try MIT; if it also misses or
fails, builds compile the remaining outputs. The switch keeps objects and writer permissions,
so successful uploads do not establish public-reader health. Check the egress graph and the
function's log before restoring public read:

```bash
gcloud storage buckets add-iam-policy-binding gs://complexitylib-lake-cache \
  --member=allUsers --role=roles/storage.legacyObjectReader
```

**Pruning.** Artifacts are shared between revisions, so they are not expired by age. When storage
grows, delete the artifacts that no revision mapping still in the bucket refers to.

**Layout.** `a0/cslib-community/complexitylib/<hash>.art` holds module archives and
`r0/cslib-community/complexitylib/tc/<toolchain>/<commit>.jsonl` the input-to-output mappings of
each commit, as written by `scripts/cache/upload.sh` and read by `lake cache get`.
