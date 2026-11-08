# HTTP cache origin

Optional MIT cache origin for [#2503](https://github.com/cslib-community/complexitylib/issues/2503)
and [#2506](https://github.com/cslib-community/complexitylib/pull/2506). The
[migration guide](../../scripts/cache/README.md#mit-origin-migration) describes CI publication.
GCS remains an active CI publisher and the default reader. MIT CI publication is enabled;
reader cutover remains a separate decision. The source and examples do not provision infrastructure
or install credentials automatically.

One Linux Go executable has three commands: `serve` accepts synchronous PUTs over a Unix socket,
`pack` streams a publication package to stdout, and `gc` runs separately under a systemd timer.
They share a store and a permanent interprocess lock. nginx supplies HTTPS, upload authentication,
request buffering, and public GET/HEAD. There is no SSH upload path, database, watcher, publication queue,
custom TLS implementation, shell execution by the handler, or third-party Go dependency.

The publisher and origin are trusted to supply correct compiled outputs. Create-only enforcement
applies while a key is present; GC does not retain a permanent ledger, and an authorized writer
can republish a collected key. There is no claim of safety against a malicious writer or origin.
See the [security contract, incident recovery and milestone scope](SECURITY.md) before activation.
The [operator runbook](OPERATIONS.md) covers identities, credentials, limits, email alerts and updates.
It also covers [usage statistics](OPERATIONS.md#usage-statistics): a separate bounded journal of
downloads, misses, response bytes and durations, with commands to inspect and summarize requests.
The [dashboard prototype](DASHBOARD.md) presents aggregate traffic, storage, publication and GC
statistics as a static public page without changing artifact uploads or downloads.

## MIT deployment status

As of November 5, 2026, the operator has deployed the origin at
**https://complexitycache.csail.mit.edu**, using the binary built from
`9066223954493c21dc24c90f1be10d67d1a8f122`.

- All 16 GiB of the separate data disk is ext4, mounted persistently at `/srv/cache-origin`.
- The publisher and daily GC timer are enabled. Socket permissions, restart, remount and
  empty-store GC checks passed.
- nginx serves trusted HTTPS with a Let's Encrypt certificate; automatic renewal and nginx
  reload passed a dry run. The `cache-publisher` account has an installed bcrypt password hash;
  its password is available for private handoff to the repository administrator.
- Tests through the VM's production nginx HTTPS listener passed: unauthorized PUT returned 401,
  publication and identical retry returned 201, conflicting artifacts and mappings returned 409
  with existing bytes and timestamps unchanged, anonymous GET/HEAD matched, and private paths,
  listing and DELETE were rejected. Public-origin authentication also passed. Test fixtures were
  removed under the publication/GC lock, leaving the store empty.
- Initial hardening included the exclusive proxy group, request/connection limits, an egress
  shaper, bounded journal, Fail2ban and queued email alerts. Rate/concurrency, capacity and ACME renewal
  tests passed; the reserved test IP was unbanned. Service-failure email reached the operator's
  inbox. Fail2ban bans remain enabled with journal logging; its email notifications are disabled.

Deployment also verified the underscore syslog tags, `nohostname`, later journal drop-in and
outbound Postfix transports documented in the operator examples.

Usage logging was installed on November 6, 2026. All five isolated nginx tests passed on the VM;
production GET/HEAD probes matched recorded status/body bytes and privacy rules. Namespace-only
rotation and service restart preserved history and accepted new records. Services stayed healthy,
with no new mail. The collector preserves the host's kernel audit policy.

Initial commissioning used small synthetic packages. By November 7, 2026, main CI was publishing
real builds successfully to both MIT and GCS. Reader cutover still requires a real MIT cold
restore and recovery exercise. The
[migration checklist](../../scripts/cache/README.md#mit-origin-migration) gives the repository
administrator's configuration and the separate publication/reader cutover steps. Credentials
and host-specific private configuration must stay outside this repository.

## Build and test locally

Prerequisites: Linux, a supported patched Go release (the module currently requires 1.27.3),
and a local filesystem supporting hard links, directory fsync, and flock. From this directory:

```bash
go test -race -count=1 ./...
go vet ./...
go test -run='^$' -fuzz=FuzzMapping -fuzztime=10s -parallel=2
go build -o /tmp/cache-origin .
```

The tests use temporary directories and local HTTP servers. No real server, cloud account,
repository credential, or Complexitylib build is needed. Linux-only source is intentional.
The Lean CI workflow also runs these checks and a real loopback nginx HTTPS test. To run that
test by hand, install nginx, OpenSSL and curl locally, then from the repository root run:

```bash
CACHE_ORIGIN_NGINX_TEST=1 CACHE_ORIGIN_BIN=/tmp/cache-origin \
  NGINX_BIN=/usr/sbin/nginx python3 -B -m unittest discover \
  -s scripts -p 'test_cache_origin_nginx.py'
```

It uses a temporary self-signed certificate and upload password and starts only loopback listeners.

To prepare real bytes, start from a reviewed, clean Complexitylib checkout with its dependencies
and toolchain available, and use an absolute scratch directory outside the source checkout:

```bash
publication_dir=$(mktemp -d)
lake build Complexity ComplexityTests -o "$publication_dir/mapping.jsonl"
lake cache stage "$publication_dir/mapping.jsonl" "$publication_dir/archives"
cache_revision=$(git rev-parse HEAD)
cache_toolchain=$(tr -d '[:space:]' < lean-toolchain | sed 's#/#--#; s#:#---#')
/tmp/cache-origin pack --mapping "$publication_dir/mapping.jsonl" \
  --archives "$publication_dir/archives" --revision "$cache_revision" \
  --toolchain "$cache_toolchain" > "$publication_dir/package.tar"
```

`pack` deliberately does not certify the producer; it is a local packaging helper. CI instead uses
`scripts/cache/publish.py stage` to check clean source state and stage the exact revision after
its required checks. Both paths use the same SHA-256 inventory, wrapped in an uncompressed USTAR package
with `publication.json` first. The .ltar payloads are already compressed and stay opaque.
Only the pinned Lake module-output subset is accepted: header `"2026-03-17"` followed by
`["<16-hex input>","<16-hex artifact>.ltar"]` rows. Unfamiliar versions/shapes stop publication
and GC. Lake's 64-bit artifact IDs are separate from the inventory's SHA-256 digests.

A mapping is the index for one repository revision and toolchain. Its URL contains the Git
revision and toolchain; each row associates a module's build-input fingerprint with its compiled
artifact archive. Different revisions can reference the same artifact when those inputs match.
The first string is a format version, not an expiration date. GC only needs these references;
it neither fetches Git history nor runs Lean.

## Publication contract

The sole application route is `PUT /publish/<40-hex revision>` with `Content-Type: application/x-tar`.
The socket is an authenticated-proxy boundary: only the operator and nginx may connect to it.
After an operator configures nginx authentication, a CI upload would look like:

```bash
curl --fail-with-body --user cache-publisher --header 'Content-Type: application/x-tar' \
  --upload-file "$publication_dir/package.tar" \
  "https://complexitycache.csail.mit.edu/publish/$cache_revision"
```

curl prompts for the password in this example; CI must use its protected secret facility.
Do not embed a password in the URL or a checked-in command. Authentication is nginx's job;
the application intentionally has no public TCP listener or independent credential store.

A 201 response means all referenced artifacts and the mapping have been installed. A retry with
identical bytes succeeds; a conflicting existing key returns 409. A held publication/GC lock
returns 503 with Retry-After; storage exhaustion returns 507. A timeout can leave the outcome
unknown: retry the same package. Successful retries do not refresh mapping retention timestamps.
Malformed packages are fully rejected before anything enters the public namespace. A failure
during installation may leave unreferenced complete artifacts, but installs the mapping last.

Uploads stream to private, server-created staging files, with limits of 4 GiB per request,
256 MiB per artifact, 8 MiB per mapping and 16 MiB inventory. The inventory-entry limit derives
from the 100,000-entry store budget, including its mapping. That store budget also counts
directories and all retained publications, so admission still requires free entry capacity.
The metadata bound covers the full supported inventory and matches the Python publisher.
Uploads are also buffered by nginx on the data disk; leave room for buffering, staging and
retained objects. The Go services retain their 256 MiB memory limits. Links,
unexpected paths/files, duplicate tar entries, missing references and unknown mapping versions
are rejected. Only regular USTAR entries are accepted. The handler never executes uploaded bytes.

Only the program/operator may modify the store. nginx gets read access to `public/`, no write
access to it, and its own separate `nginx-tmp/` for request buffering. Application files are
installed read-only using atomic hard-link creation; completed files are never edited in place.
The program uses `os.Root` to confine filesystem access. This is not a sandbox against a
compromised operator or program: publication and GC currently run as the same Unix user.

## Retention and cleanup

```bash
sudo -u cache-origin /usr/local/bin/cache-origin gc --root /srv/cache-origin          # dry run
sudo -u cache-origin /usr/local/bin/cache-origin gc --root /srv/cache-origin --apply  # apply
```

GC keeps the single newest publication across all toolchains, even during idle periods.
Every other mapping expires two days after its first installation on this server. Publishing a
new toolchain therefore lets old toolchains' mappings expire; there is no pin per toolchain.
The newest publication is selected by server installation time (ties by object key), not Git
history or a Lean release-date lookup. Identical retries preserve that installation time and
cannot make an old mapping newest. CI serializes main runs, so normal uploads follow build order.
Every remaining mapping marks its artifacts live, including artifacts shared across toolchains.
GC deletes every unreferenced artifact in the same pass that deletes its final referring mapping;
there is no additional grace period. It also deletes orphaned artifacts from interrupted uploads,
regardless of their age. References are recomputed each pass, with no persistent reference counts
or deletion timers. The `state/` directory holds only the permanent publication/GC lock.
GC validates all mappings, including ones due to expire, before deleting anything. An unreadable
mapping, missing reference, unsupported format or unexpected public entry stops
the pass. Publication admission caps the public store at 100,000 entries, counting directories
as well as files and allowing for new parents before installing anything. GC prunes empty
namespace directories under the same lock, so successive toolchains do not permanently leak
directory inodes. The filesystem quota separately bounds bytes/inodes.

The `--retain` option sets superseded-mapping retention (default `48h`). Expiration and deletion occur on
GC runs; the example timer runs daily. nginx downloads do not hold the publication/GC lock:
a client that fetched a mapping just before its expiration can miss an artifact deleted by GC
and compile that module instead. An already-open artifact file remains readable after unlinking.
Abandoned application staging directories are removed after 24 hours under the same lock;
nginx's own request-body temporary files remain nginx/operator-managed.

The lock spans each complete upload/validation/installation and each GC pass, so no scan races
a new mapping referencing an old artifact. This intentionally serializes the small write workload;
public nginx reads continue. The timer retries on its next run if the store is busy.
GC deletion is restartable, not an all-or-nothing filesystem transaction. Dry runs are local
inspection; the lock file and empty store control directories may be created on first use.

## Operator-owned deployment examples and remaining gaps

The [nginx fragment](examples/nginx.conf) and [systemd units](examples/cache-origin.service)
are opt-in examples. The [GC timer](examples/cache-origin-gc.timer) invokes the separate
[GC service](examples/cache-origin-gc.service). They require an operator-created `cache-origin`
user, an exclusive `cache-origin-proxy` socket group, a dedicated bounded filesystem mounted at `/srv/cache-origin`,
operator-managed DNS/TLS and an upload password file. Set the store root owner to `cache-origin`
with mode 0711, its `public/` to 0755, and `staging/` and `state/` to 0700. Create `nginx-tmp/`
owned by nginx on the same bounded filesystem. The application creates its own control directories.
Only the publisher and nginx may use the socket group. Use a dedicated cache host; do not cohost
untrusted nginx applications or add unrelated processes to that group. The store and its public
directories must be owned by `cache-origin` without group/other write bits; `state/`, `staging/`
and the permanent regular lock file are private. Unsafe ownership, modes, namespace entries or
lock files stop publication/GC. Run administrative GC as `cache-origin`, not root. Check nginx
configuration and real identity/permission behavior before any activation.

Passing source and loopback tests does not establish production commissioning. Not included:
cryptographic producer attestations, automatic provisioning, OS quota setup, TLS/certificate lifecycle,
historical backfill, or reader cutover. A stolen publisher credential can still publish malicious
bytes under unused or collected keys; the origin operator controls served bytes. SHA-256 detects
package corruption, not authorized provenance. Keep GCS readers/publication until a separately
reviewed deployment and cold restore succeed. Follow [incident recovery](SECURITY.md) for every
propagation path. Do not put Lean or private operator keys on this host.

Review references: [Go filesystem confinement](https://pkg.go.dev/os#Root),
[nginx Unix-socket proxying](https://nginx.org/en/docs/http/ngx_http_proxy_module.html#proxy_pass),
[pinned Lake mapping producer](https://github.com/leanprover/lean4/blob/v4.36.0-rc2/src/lake/Lake/Build/Module.lean#L1336).

Manual impact: the Operator's Manual reaches the updated canonical cache guide, security recovery
procedure and operator examples; local restoration now supports bounded ordered mirrors. The Agent Operator's Manual needs no edit:
roles, authorization and handoffs are unchanged. No Lean/API/abstract/roadmap/upstream impact.
AI assistance: OpenAI Codex wrote the origin and its tests. Agent review is not human approval.
