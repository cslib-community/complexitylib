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

A complete set of library and test outputs is about 75 MB compressed. Outputs are platform
independent (`platformIndependent = true`), so Linux CI builds serve macOS checkouts.
`COMPLEXITYLIB_CACHE_URL` overrides the location; set it to an empty string to skip the
Complexitylib download.

CI reads the cache too. After restoring `.lake` from the GitHub Actions cache, Lean CI runs
`scripts/cache/get-missing.sh`, which downloads the same outputs except those of modules whose
input hash already matches a build trace in `.lake`. A fresh runner would otherwise download a
complete set on every run, although `.lake` usually has most of it.

The Lean workflows also restore elan and the toolchain named in `lean-toolchain` (`~/.elan`,
about 600 MB) from the Actions cache before `leanprover/lean-action` runs, so that the action does
not download the toolchain. On a miss, `.github/actions/install-lean` installs them with bounded
retries and saves the entry before any Lake command runs, so it never contains the local artifact
cache above.

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

`scripts/worktree.sh create` and `scripts/worktree.sh seed` run `scripts/cache/ensure.sh` in the
worktree after seeding `.lake` caches. The helper never points a worktree at the primary checkout,
refuses targets or destination cache symlinks that do, isolates dependency `.git` directories and
`gitdir:` pointer files so Git operations in a worktree cannot modify the primary checkout's `HEAD`
or `index`, and dereferences any package symlink whose target is absolute or escapes the package
directory. Pass `--copy-cslib` or `--copy-packages` when package sources must change.

## Trust and privacy

Downloaded `.olean` files are trusted by Lean: imported modules are not re-checked by the
kernel, and their compiled code (tactics, macros, initializers) runs during your build. Whoever
can write to the cache could therefore make a false theorem appear proved or run code on your
machine. The cache is set up so that this is no more trust than building `main` already
requires:

- Only push runs on `main` in this repository can write. They authenticate with GitHub's OIDC
  token through Workload Identity Federation, restricted to this repository's numeric id, the
  `main` ref and the `push` event; no credentials are stored in GitHub. Pull requests, forks,
  merge-queue groups and other branches cannot obtain write access. The condition does not name
  a workflow, so any workflow run by a push to `main` that requests an OIDC token could write;
  today only the Lean CI job requests one.
- The writer can create objects but not delete them, so a published artifact can never be
  replaced. Lake checks every downloaded artifact against the hash recorded in the mapping.

Merge-gating CI also reuses these outputs. Lean CI on pull requests, merge-queue groups and
`main` pushes restores modules that earlier `main` runs uploaded instead of compiling them, so a
module restored this way is not re-checked by the kernel in that run. This adds no party to
trust. CI already restores `.lake` from the GitHub Actions cache, where runs on `main` save the
copies that other branches and pull requests fall back to, and Lake reuses those outputs in the
same way. The remote cache's writers are a subset of those runs, so both caches hold what code
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
repository); build logs and machine paths are not uploaded. Downloads are anonymous HTTPS
requests to Google Cloud Storage; the bucket keeps no access logs.

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
12 MB when it is a few hundred modules behind, and a complete set (about 75 MB) when it misses.
Cloud Storage's free tier covers 5 GB of storage and 100 GB of egress per month in `us-east1`;
at 150–200 CI runs a day, a complete download on every run would exceed that several times over
and soon reach the budget. The budget alerts and the kill switch bound abuse of the public
bucket.

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
