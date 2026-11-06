# Build caches

Complexitylib's build has two caches. Both are optional: `lake build` without them compiles
everything it needs.

**Local artifact cache.** `lakefile.toml` enables Lake's content-addressed artifact cache, so a
module built in one checkout (a worktree, an agent sandbox, a second clone) is reused by every
other checkout on the same machine with the same inputs. Outputs are hard-linked back into
`.lake/build`. `lake cache clean` empties it; it lives in the Lean toolchain's directory under
`~/.elan` unless `LAKE_CACHE_DIR` says otherwise.

**Remote cache.** CI uploads the build outputs of every commit on `main`; `scripts/cache/get.sh`
downloads them for the nearest cached ancestor of your `HEAD`:

```bash
scripts/build.sh --wfail --iofail   # restore caches, then build changed or missing modules
```

A complete set of library and test outputs is about 200 MB compressed (November 2026). Outputs
are platform independent (`platformIndependent = true`), so Linux CI builds serve macOS checkouts.
`COMPLEXITYLIB_CACHE_URL` overrides the location; set it to an empty string to skip the
Complexitylib download.

CI reads the cache too. After restoring `.lake` from the GitHub Actions cache, Lean CI runs
`scripts/cache/get-missing.sh`, which downloads the same outputs except those of modules whose
input hash already matches a build trace in `.lake`. A fresh runner would otherwise download a
complete set on every run, although `.lake` usually has most of it.

Mathlib downloads are retried in the same checkout by `scripts/cache/get_mathlib.py`: at most
three ordinary `lake exe cache get` attempts, each limited to three minutes, with two-second
pauses. Completed archives remain in place, so the pinned Mathlib client retries only missing
downloads. Exhausted attempts warn and leave the strict build/check commands to compile what is
missing. On POSIX, shutdown sends SIGTERM to the attempt's own process group, allowing Git's
signal handlers to remove their locks, then waits up to five seconds before escalating to
SIGKILL and waiting up to five more seconds. Parent exit alone does not establish descendant
exit: retries stop early if the group still exists (including unreaped zombies). On Windows,
the same bounded terminate/kill sequence applies to the direct child only. The helper never
removes Git locks; forced termination can still leave one behind.

Lean CI, API docs and Comparator disable only lean-action's built-in Mathlib fetch and call this helper
with `--lean-action`, preserving that action's URL handling: unset `MATHLIB_CACHE_GET_URL` selects
`https://cache.mathlib.org/mathlib4`, an empty value selects the Mathlib client's default, and an
explicit URL is retained. Local `get.sh` and the Guide workflow use the same retries while retaining
their existing client-default/environment behavior. API docs also use the existing missing-only
Complexitylib restore before generation. The Guide workflow restores Lean CI's `.lake` entry from
the Actions cache and then uses the same missing-only restore. Cache failures remain optional;
installation and validation failures remain strict.

The Lean workflows also restore elan and the toolchain named in `lean-toolchain` (`~/.elan`,
about 600 MB) from the Actions cache before `leanprover/lean-action` runs, so that the action does
not download the toolchain. On a miss, `.github/actions/install-lean` installs them with bounded
retries and saves the entry before any Lake command runs, so it never contains the local artifact
cache above.

## Hosted-runner disk space

Before restoring `.lake`, Lean CI runs `scripts/ci/prepare-runner.sh` to remove the unused
Android and .NET SDKs and report available disk space. It runs only on GitHub-hosted Linux
runners; local and self-hosted invocations skip cleanup. The Lean toolchain, compiler, Python,
Node actions, repository and caches are retained. Cleanup is optional; all validation still runs
if it fails.

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
  still cover omitted entries; the 100,000-file, 4 GiB unpacked and 1 GiB compressed payload limits
  are unchanged. Packing reports retained and omitted counts/sizes, including on a limit miss.
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

## Automatic restoration

Temporary controlled measurement is specified in [MEASUREMENT.md](MEASUREMENT.md) (#1728).
Its hooks are disabled without an explicit plan and expire on 2026-11-15. Installing them does
not authorize study activation or complete #1197's net-benefit requirement.

`scripts/build.sh` runs `scripts/cache/ensure.sh`, then forwards its arguments and exit status to
`lake build`. `scripts/check.sh` uses the same bootstrap before full or quick validation; a quick
check that falls back to all six gates does not download twice. Bare `lake` commands do not
bootstrap. Before using Lean MCP diagnostics or another operation that can elaborate/build in a
cold checkout, restore available outputs with:

```bash
scripts/cache/ensure.sh
```

This guidance applies to every agent client. Retry for missing outputs or new toolchain/dependency
inputs; a new commit or branch switch alone does not require a manual bootstrap when outputs are
warm. MCP's `lean_build(fetch_cache=true)` only fetches Mathlib's cache, so it does not replace
Complexitylib cache restoration.

The bootstrap records a completed **attempt**, not a successful cache hit, in
`.lake/cache-bootstrap/attempt.json`. For ten minutes it skips another attempt with the same
checkout path, `HEAD`, toolchain, manifest, Lake configuration, endpoint and `LAKE_CACHE_DIR`.
Working proof edits do not trigger another download. A changed `HEAD`, pin or configuration
triggers a new attempt; an unchanged state is retried after ten minutes, including a previous miss or
network failure. The stamp is written atomically after the fetch command finishes.

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
machine. For the current GCS-only reader default, this is no more trust than building `main`
already requires:

- Only push runs on `main` in this repository can obtain the GCS writer identity. It uses
  GitHub OIDC through Workload Identity Federation, restricted to this repository, main ref and
  push event. Pull requests, forks, merge groups and other branches cannot obtain that identity.
- The GCS writer can create objects but cannot delete them, so it cannot replace existing
  objects. The optional MIT publisher instead receives an upload password only in its final
  protected job step. Its additional trust roots are described in the migration section below.
  Lake checks every downloaded artifact against the hash recorded in its mapping.

Merge-gating CI also reuses these outputs. Lean CI on pull requests, merge-queue groups and
`main` pushes restores modules that earlier `main` runs uploaded instead of compiling them, so a
module restored this way is not re-checked by the kernel in that run. Reading GCS adds no party to
trust. CI already restores `.lake` from the GitHub Actions cache, where runs on `main` save the
copies that other branches and pull requests fall back to, and Lake reuses those outputs in the
same way. The GCS remote cache's writers are a subset of those runs, so both caches hold what code
already on `main` built (the Actions cache also holds a pull request's own earlier runs).

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
requests to Google Cloud Storage until a separately reviewed reader cutover.

## MIT origin migration

The optional [HTTP origin](../../tools/cache-origin/README.md) uses nginx for HTTPS,
upload authentication and public file serving, plus a small Linux Go executable for synchronous
publication and garbage collection. MIT owns the VM, operating-system updates, DNS/TLS,
credentials, bounded storage and monitoring. The repository supplies source and operator examples,
not automatic provisioning. There is no SSH upload or S3 service dependency.

The deployed MIT origin is **https://complexitycache.csail.mit.edu**. The
[dated deployment status](../../tools/cache-origin/README.md#mit-deployment-status) records the
installed source and completed host checks. A real-build publication/cold restore and integration
approval remain; keep MIT CI publication disabled and GCS readers active during these checks.

After all required Lean checks, `publish.py stage` records the exact clean producer revision
and SHA-256 inventory once. GCS and the separate MIT publisher job consume those same staged bytes.
The MIT job verifies this run's artifact ID and producer revision before obtaining its upload
password for the final step. It packs the inventory and files into an uncompressed USTAR package
and sends `PUT /publish/<commit>` over HTTPS. curl retries transient failures; credentials travel
through its stdin configuration rather than URLs or command-line arguments.

The handler validates the whole package before publishing anything, installs artifacts before
the mapping and rejects conflicting existing keys even when the client omits conditional headers.
Identical retries succeed. HTTP credentials allow publication only: there is no remote deletion
or administration route. Anonymous `GET`/`HEAD` expose exact artifact/mapping keys without listing.
GC locally preserves the newest publication across all toolchains, expires other mappings after
two days and deletes artifacts immediately when no retained mapping refers to them. See the
[retention contract](../../tools/cache-origin/README.md#retention-and-cleanup).

The GitHub environment restricts when Actions receives the password; the server does not establish
that a request came from a main push. A stolen password can publish malicious bytes under unused
keys, and the MIT origin operator can control served bytes. Both are additional trust roots once
clients use this origin. Hashes establish transfer consistency, not producer provenance. Imported
Lean outputs can execute code during a build. If compromised, disable MIT publication and reader
use, revoke the password, discard poisoned origin and retained local outputs, and rebuild from
trusted sources. The GCS-only trust description above applies until the explicit reader cutover.

Before activation, commission the actual server: verify TLS, upload authentication, Unix-socket
permissions, service restart, storage limits and GC; prove concurrent conflicting uploads cannot
replace a key; test unauthorized PUT and all DELETE requests; then cold-restore a real build through
the public HTTPS origin. CI checks the same nginx routes over loopback TLS, but cannot establish
the target host's identity, permissions or disk configuration.

A repository administrator can prepare the GitHub environment `cache-server-publish`, restrict it
to `main`, and configure the following using the privately supplied publisher password. Keep the
publication switch disabled until the commissioning evidence and integration are approved.

| Kind | Name |
|---|---|
| Environment secret | `CACHE_SERVER_PASSWORD` (nonempty, no control characters) |
| Environment variable | `CACHE_SERVER_USER=cache-publisher` |
| Environment variable | `CACHE_SERVER_URL=https://complexitycache.csail.mit.edu` (origin without a path) |
| Repository variable | `CACHE_SERVER_PUBLISH_ENABLED` (`false` until commissioning passes) |

Enabling publication does not change readers. Keep GCS publication and the GCS default URL during
commissioning. A later small PR can change the single default `COMPLEXITYLIB_CACHE_URL` after a
cold restore from the public MIT URL succeeds; retain GCS long enough to observe the new origin,
then disable and remove it in another reviewed change. At every stage, an empty cache remains an
optional performance loss rather than a build failure.

## Maintainer runbook

The cache runs in a dedicated Google Cloud project maintained by Samuel Schlesinger.

**Setup.** `PROJECT=<id> BILLING_ACCOUNT=<id> ALERT_EMAIL=<address> scripts/cache/setup-gcs.sh`
creates, in order (each step can be rerun alone, e.g. `setup-gcs.sh alert`):

| Step | Creates |
| --- | --- |
| `project` | the project, billing link and APIs |
| `bucket` | `gs://complexitylib-lake-cache` (`us-east1`), public read by object name without listing, no soft delete or versioning, revision mappings expire after 180 days |
| `writer` | the GitHub identity pool and provider, and the `lake-cache-writer` service account (create + read on the bucket only) |
| `budget` | a monthly budget (default 10 USD) with alerts at 50/90/100 % and a Pub/Sub topic |
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

**After the kill switch fires.** Downloads fail and builds fall back to compiling. Check the egress
graph and the function's log, then restore public read:

```bash
gcloud storage buckets add-iam-policy-binding gs://complexitylib-lake-cache \
  --member=allUsers --role=roles/storage.legacyObjectReader
```

**Pruning.** Artifacts are shared between revisions, so they are not expired by age. When storage
grows, delete the artifacts that no revision mapping still in the bucket refers to.

**Layout.** `a0/cslib-community/complexitylib/<hash>.art` holds module archives and
`r0/cslib-community/complexitylib/tc/<toolchain>/<commit>.jsonl` the input-to-output mappings of
each commit, as written by `scripts/cache/upload.sh` and read by `lake cache get`.
