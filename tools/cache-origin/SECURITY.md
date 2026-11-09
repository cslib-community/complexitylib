# Security contract and cache recovery

The CI publisher, its upload credential and the origin operator are trusted to supply correct
compiled outputs. HTTPS authenticates the origin and protects transport; the SHA-256 publication
inventory detects corruption and inconsistent uploads. Neither proves that an output came from
the claimed source. Lake's native artifact identifiers and download checks use a nonsecure
64-bit hash. This service preserves that protocol; it adds no cryptographic producer attestation.

The service rejects changes to keys that still exist. After GC removes a key it retains no
permanent commitment or retirement record, so an authorized writer can publish that key again.
This is intentional under the trusted-writer contract. The normal publisher uploads only new
validated `main` builds. GC retention is a storage policy, not a reader authorization deadline:
already downloaded artifacts remain usable. The nginx example sends `Cache-Control: no-store`
instead of promising that a collected URL is immutable for a year.

A stolen publisher credential violates the contract. It can publish malicious mappings and
artifacts under unused keys even if old keys are protected forever. An origin operator can also
change the bytes served. A permanent ledger would constrain replacement after GC, but would not
establish a trustworthy cache in either case; it is not part of this design. If that stronger
threat model becomes required, revisit authenticated provenance and reader verification together,
rather than treating a server-side ledger as protection against a compromised writer.

## If a publisher, origin or restored output is compromised

Treat this as a cache incident across every propagation path. MIT outputs can enter a local
Lake cache, `.lake`, the shared Actions `.lake` cache, merge-queue handoffs and staged publication
artifacts, and can subsequently be republished to **both MIT and GCS**. Disabling one URL or
changing only the HTTP password is insufficient. Compiled Lean outputs can execute code, so
also assess affected build machines and credentials; use fresh trusted runners or reimage a
machine when its integrity cannot be established.

The repository maintainer and both origin operators must coordinate the following sequence.
These are incident actions, not normal deployment steps. Preserve evidence privately before
deleting suspect objects; do not copy the suspect outputs into a replacement cache.

1. **Stop propagation.** Disable cache-consuming/build/publishing workflows and cancel their
   running and queued runs before cleanup. Stop MIT nginx, publisher and GC services; quarantine
   GCS public reads and its writer identity too. Record the existing nonsecret configuration,
   set `CACHE_SERVER_PUBLISH_ENABLED=false`, remove `LAKE_CACHE_BUCKET`, and set
   `DISABLE_BUILD_HANDOFF=1` and `DISABLE_CACHE_RESTORE=true`. The latter prevents restoration
   and shared-cache saving in updated workflows and causes the local restoration helpers and
   handoff tool to skip their work. Older workflow revisions do not implement this switch;
   disabling/canceling them is essential. On the dedicated MIT VM, stopping nginx also stops
   anonymous reads. For the GCS policy installed by `setup-gcs.sh`, revoke
   `allUsers`/`roles/storage.legacyObjectReader` and the cache writer's object permissions;
   inspect the live policy for additional access rather than assuming these are the only grants.
2. **Invalidate secondary copies.** Delete the repository's Actions caches after every old run
   is stopped. In an authenticated maintainer shell:

   ```bash
   gh cache delete --repo cslib-community/complexitylib --all --succeed-on-no-caches
   gh api --paginate repos/cslib-community/complexitylib/actions/artifacts \
     --jq '.artifacts[] | [.id, .name] | @tsv'
   ```

   Inspect that artifact list and delete all compiled build handoffs and staged publication
   artifacts from the incident window, using `gh api --method DELETE
   repos/cslib-community/complexitylib/actions/artifacts/<id>` for each selected ID. Include
   merge-group and `main` runs, not just the run that first downloaded MIT bytes. Do not rerun
   an old producer attempt to manufacture a replacement. Keep the original origins quarantined;
   a lifecycle policy is not an immediate purge, and GC will not purge its newest mapping.
3. **Rotate recovery identity and credentials.** Set `CACHE_RECOVERY_GENERATION` to a new,
   never-used value of 1–64 letters, digits, dots, underscores or hyphens, such as
   `incident-20261106-1`. Updated Lean CI, Guide and Comparator include this value in both the
   exact Actions cache key and its restore prefix; merge-group handoffs include it in their
   checked metadata. Pre-incident or unmarked handoffs are rejected. This is an emergency
   invalidation token, not a change to Lake's URLs or an ordinary GC epoch. Rotate the HTTP
   password, revoke compromised GCP access and rotate any other credentials exposed to code
   running on affected builders. Create fresh origin namespaces (for example a new GCS bucket
   and a replacement HTTPS origin) and update every consumer's origin list so external copies
   of old URLs cannot be mistaken for the replacement. Do not restore private credentials from
   an affected build cache.
4. **Discard local copies.** Every affected operator must discard suspect `.lake` outputs in
   all worktrees/clones and any shared `LAKE_CACHE_DIR` or toolchain artifact cache. Removing
   only `.lake/build` leaves shared artifacts and dependency build outputs available. Use a
   fresh source checkout and verified toolchain; quarantine the old checkout/cache rather than
   running its potentially cached Lake configuration to clean itself. Notify consumers that
   server-side deletion cannot revoke copies they already downloaded.
5. **Rebuild without restoration.** On a fresh trusted builder, keep all publishers and remote
   readers disabled. Set:

   ```bash
   export DISABLE_CACHE_RESTORE=true
   export DISABLE_BUILD_HANDOFF=1
   export COMPLEXITYLIB_CACHE_AUTO=0
   export LAKE_NO_CACHE=true
   export LAKE_ARTIFACT_CACHE=false
   export MATHLIB_NO_CACHE_ON_UPDATE=1
   ```

   Obtain dependencies from their pinned source repositories and run the full validation
   sequence from `CONTRIBUTING.md`. `lake --no-cache` also disables Lake cache use for a direct
   command. Do not download Mathlib/Complexitylib compiled outputs, restore Actions caches or
   consume handoffs for this rebuild. Check that logs show compilation rather than restoration.
   The cache VM does not run Lean; use a separate builder with sufficient RAM.
6. **Resume deliberately.** Review the clean build and new infrastructure, publish only those
   clean outputs to the replacement origins, and perform a real cold restore from them. Keep
   old origins inaccessible. Restore the desired publisher configuration and mirror list only
   after that review, clear `DISABLE_CACHE_RESTORE` for normal builds, and re-enable handoffs
   last. The new recovery generation remains in place. Confirm that publication artifacts
   belong to the clean run and that Actions cache keys and handoff metadata carry the new
   generation.

Exercise recovery with isolated fixture caches before reader cutover: a pre-incident handoff
must be rejected after a generation change, all restoration paths must be disabled by the
recovery switch, and source builds must still run. An actual incident additionally requires
the coordinated quarantine/purge and trusted rebuild above; unit tests do not prove those
operator actions occurred.

## Scope of #2506 and remaining #2503 work

This PR is a bounded milestone: HTTP origin source, operator configuration examples, validated
publication, bounded ordered restoration, retention and recovery. The MIT host was installed
and commissioned manually; the repository does not yet reproduce that installation or perform
automated upgrades. Repository-managed, repeatable provisioning and upgrade/rollback validation
remain open under [#2503](https://github.com/cslib-community/cslib-frontier/issues/2503). Neither
source approval nor the host checks close that broader issue. Reader activation, a real-build
cold restore, a recovery exercise and exact-head human maintainer approval remain separate gates.
