# Optional cache origin

This directory provisions a small public artifact server on hardware supplied by Erik Demaine.
It is an opt-in alternative to the existing Google Cloud Storage origin. Nothing is deployed by
checking out or merging these files, and GCS remains the production cache until maintainers
explicitly change publication and reader configuration.

`CACHE_SERVER_DEPLOY_ENABLED` opts into automatic infrastructure deployment;
`CACHE_SERVER_PUBLISH_ENABLED` independently opts into artifact publication and the daily health
check. Leave both unset while reviewing this proposal. Changing one does not enable the other or
switch readers.

GitHub CI still compiles and stages the artifacts. nginx streams those files over HTTPS; the
server needs neither Lean nor a copy of the library's build tree. The same files serve users and
CI. Start with one core and 1 GB RAM, then size connectivity from observed use. Cache data must
live on its own pre-mounted ext4 filesystem at `/srv/complexitylib-cache`, separate from `/` and
bounded to the byte and inode limits reviewed in `vars.yml`. The default ceiling is 64 GiB and
4,194,304 inodes, with at least 2 GiB and 65,536 inodes free at deployment. The approximately
200 MB compressed per revision in the [cache guide](../../scripts/cache/README.md) remains only a
planning estimate; deployment and publication fail closed when the reviewed storage boundary is
missing or exhausted.

## Before bootstrap

Use a **dedicated Debian or Ubuntu VM with systemd**, Python 3.9 or newer, an SSH administrator with
passwordless sudo, and supported OS security updates. Before running the playbook, provision and
mount the dedicated ext4 data filesystem described above. The playbook manages nginx, Certbot,
its own virtual host, the `cache-upload` account, and a narrowly scoped sshd `Match` policy for
that account; it leaves existing administrator keys, unrelated SSH policy, other virtual hosts
and firewall policy in the operator's control. Reserve this account and the
`/srv/complexitylib-cache`, `/var/lib/complexitylib-cache-*` and `/opt/complexitylib-rsync` paths
for this service. Do not reuse a pre-existing upload account.

The operator provides:

1. A stable public DNS name with A/AAAA records pointing to the VM. Publish AAAA only when IPv6
   works. TCP 80 and 443 must be reachable from the Internet for HTTP-01 certificate issuance,
   renewal and downloads; expose the SSH port according to the institution's access policy.
2. An administrator/deployment SSH key, separate from the artifact upload key. This key has
   root-equivalent access through sudo. Keep personal recovery access and a console available.
3. A bare SSH public key for trusted `main` CI artifact publication. Add it to the reviewed
   `upload-keys.yml` allowlist; only its private counterpart belongs in the publishing
   environment. Per-key restrictions and the account-level sshd policy both force the reviewed
   upload wrapper, with no shell, forwarding, PTY, overwrite or delete capability.
4. The server's SSH host public key or fingerprint, obtained from the console or a trusted
   administrator. Verify it out of band before recording it in `known_hosts`. An unauthenticated
   `ssh-keyscan` result alone does not establish the host's identity. For a nondefault SSH port,
   use a `[hostname]:port` entry.

The [repository deployment workflow](../../.github/workflows/cache-server.yml) uses the same
playbook as manual operation. Its admin and publishing environments must be configured before
enabling either path; see that workflow and the [cache runbook](../../scripts/cache/README.md).
Use environment protection to restrict credentials and target configuration to trusted `main`
deployments. The administrative environment must require an independent operator approval and
must not permit the initiating administrator to bypass it. This infrastructure does not broaden
the current GCS writer permissions.

## Configure GitHub deployment

These are **operator actions for activation**, not steps to run while reviewing the proposal.
Use a repository administrator account and an authenticated GitHub CLI. Under Settings →
Environments create **`cache-server-admin`** and **`cache-server-publish`**. For each, select
**Selected branches and tags**, add the branch rule **`main`**, and add no other branch or tag
rules. Do this **before installing secrets or variables**. On `cache-server-admin`, configure at
least one required reviewer independent of the change and disable self-review and administrator
bypass where the repository's GitHub plan exposes those controls. Treat inability to enforce
that approval as a deployment blocker. Verify both environments and their policies:

```bash
cache_repo=cslib-community/complexitylib
gh api "repos/$cache_repo/environments/cache-server-admin"
gh api "repos/$cache_repo/environments/cache-server-admin/deployment-branch-policies"
gh api "repos/$cache_repo/environments/cache-server-publish"
gh api "repos/$cache_repo/environments/cache-server-publish/deployment-branch-policies"
```

Expect `custom_branch_policies: true`, `protected_branches: false`, and exactly the `main`
rule of type `branch` in each policy list. The admin environment must also report its required
reviewer protection, `prevent_self_review: true` and `can_admins_bypass: false`. Ordinary branch
workflows must not obtain either identity. Install distinct private keys only in their respective
environments:

```bash
gh secret set CACHE_SERVER_ADMIN_KEY --repo "$cache_repo" --env cache-server-admin \
  < /path/to/cache-admin-key
gh secret set CACHE_SERVER_UPLOAD_KEY --repo "$cache_repo" --env cache-server-publish \
  < /path/to/cache-upload-key
```

Put host-specific deployment and publication targets in their named **environment Actions
variables**. Environment variables take precedence when the jobs enter those environments, so a
repository-variable edit cannot redirect a protected credential. Only the two activation flags
and the public health-check domain need repository scope because job conditions are evaluated
before an environment is entered. None contains a private key.

| Environment variable | Environment | Value |
|---|---|---|
| `CACHE_SERVER_HOST` | both | SSH DNS name or IPv4 address |
| `CACHE_SERVER_SSH_PORT` | both | SSH port; omit for 22 |
| `CACHE_SERVER_KNOWN_HOSTS` | both | Independently verified OpenSSH `known_hosts` entry |
| `CACHE_SERVER_ADMIN_USER` | `cache-server-admin` | Existing administrator with passwordless sudo |
| `CACHE_SERVER_DOMAIN` | `cache-server-admin` | Public HTTPS DNS name |
| `CACHE_SERVER_ACME_EMAIL` | `cache-server-admin` | Certificate operator email |

| Repository variable | Value |
|---|---|
| `CACHE_SERVER_DOMAIN` | Public HTTPS DNS name, for the uncredentialed health check |
| `CACHE_SERVER_DEPLOY_ENABLED` | Initially `false`; requests an approved infrastructure deployment |
| `CACHE_SERVER_PUBLISH_ENABLED` | Initially `false`; artifact publication and daily public health check |

After replacing the host-specific values:

```bash
for cache_env in cache-server-admin cache-server-publish; do
  gh variable set CACHE_SERVER_HOST --repo "$cache_repo" --env "$cache_env" \
    --body cache.example.edu
  gh variable set CACHE_SERVER_SSH_PORT --repo "$cache_repo" --env "$cache_env" --body 22
  gh variable set CACHE_SERVER_KNOWN_HOSTS --repo "$cache_repo" --env "$cache_env" \
    --body "$(cat /path/to/verified-known-hosts)"
done
gh variable set CACHE_SERVER_ADMIN_USER --repo "$cache_repo" --env cache-server-admin \
  --body cache-admin
gh variable set CACHE_SERVER_DOMAIN --repo "$cache_repo" --env cache-server-admin \
  --body cache.example.edu
gh variable set CACHE_SERVER_ACME_EMAIL --repo "$cache_repo" --env cache-server-admin \
  --body operator@example.edu
gh variable set CACHE_SERVER_DOMAIN --repo "$cache_repo" --body cache.example.edu
gh variable set CACHE_SERVER_DEPLOY_ENABLED --repo "$cache_repo" --body false
gh variable set CACHE_SERVER_PUBLISH_ENABLED --repo "$cache_repo" --body false
```

Add the publication public key to `upload-keys.yml` in a reviewed PR. The committed list is the
only source of upload authorization; neither a repository variable nor a workflow dispatch can
add a key.

Keep existing `LAKE_CACHE_*` GCS settings intact. Bootstrap by hand below, or enable only
infrastructure deployment and dispatch the checked-in workflow:

```bash
gh variable set CACHE_SERVER_DEPLOY_ENABLED --repo "$cache_repo" --body true
gh workflow run cache-server.yml --repo "$cache_repo" --ref main
```

The workflow tests configuration and the Linux data plane before deployment, then checks public
HTTPS `/healthz` against the deployed commit. Later changes to infrastructure, cache scripts or
their workflows on `main` reapply the configuration. A failed deployment can be retried through
the failed job or another dispatch. Both CI tests and publication use the same pinned rsync
installer and reuse its verified compiled installation through the Actions cache.

## Bootstrap by hand

From a reviewed checkout, create a controller environment outside the repository. The checked
wheel hashes target Ubuntu x86-64 with CPython 3.13, matching the hosted workflow; use that exact
controller platform for manual operation. The remote host needs distribution Python 3.9 or newer
(for example, Debian 12 or Ubuntu 24.04).

```bash
python3.13 -m venv /tmp/complexitylib-cache-ansible
/tmp/complexitylib-cache-ansible/bin/pip install --require-hashes \
  --requirement infra/cache-server/requirements.txt
cd infra/cache-server

export CACHE_SERVER_DOMAIN=cache.example.edu
export CACHE_SERVER_ACME_EMAIL=operator@example.edu
export CACHE_SERVER_REVISION="$(git rev-parse HEAD)"

# Your SSH config/agent must supply the administrator identity and verified known_hosts entry.
/tmp/complexitylib-cache-ansible/bin/ansible-playbook -i inventory.example.yml playbook.yml --syntax-check
/tmp/complexitylib-cache-ansible/bin/ansible-playbook -i inventory.example.yml playbook.yml
curl --fail --show-error "https://$CACHE_SERVER_DOMAIN/healthz"
```

Before this command, add the desired bare upload public key to the checked-in
`upload-keys.yml` allowlist and review that change. The playbook accepts no environment override
for the list. It also validates the dedicated mounted filesystem before it creates service paths;
change storage or upload limits only through a reviewed `vars.yml` change.

The committed inventory targets an SSH alias, `cache-server`. Configure that alias in the
controller's SSH config (the deployment workflow generates an equivalent private config from
`CACHE_SERVER_HOST`, `CACHE_SERVER_ADMIN_USER`, `CACHE_SERVER_SSH_PORT` and its protected secrets):

```text
Host cache-server
    HostName cache.example.edu
    User cache-admin
    Port 22
    IdentityFile /path/to/cache-admin-key
    IdentitiesOnly yes
    StrictHostKeyChecking yes
```

No private key appears in the inventory. An agent-loaded key can replace `IdentityFile`.
For multiple controllers, keep one authoritative operator configuration and serialize deployments
to this host.

The first run enables an HTTP virtual host for Certbot's webroot challenge, obtains the
certificate, then enables HTTPS. Until the certificate exists, artifact requests return 503.
Subsequent runs keep HTTPS active, update configuration and keys, and skip certificate issuance.
nginx's configuration is checked before each reload, and a failed apply restores its previous
on-disk virtual host file. The packaged Certbot timer renews the
certificate; a deploy hook validates and reloads nginx after renewal. If issuance fails, fix DNS
or reachability and rerun the playbook. Do not repeatedly request new certificates while testing
DNS. Verify renewal once after bootstrap:

```bash
sudo certbot renew --dry-run
systemctl list-timers certbot.timer
```

The playbook installs current distribution versions of the listed serving/build packages. Its
Python controller dependencies are fully resolved and hash-locked; installations use
`--require-hashes` and binary distributions only. It builds the pinned upstream rsync release
once with `make -j1`, keeping its matching `rrsync` in a versioned `/opt` prefix that identifies
the upstream version, archive digest and installer recipe. Recipe or source changes therefore
build a new installation while retaining the old one for rollback. The sole source adjustment
sets `rrsync`'s executable path to that matching binary. This is deliberate: older `rrsync`
implementations lack the required hardened write restrictions. The upstream archive's SHA-256
is pinned in `vars.yml`; source and build outputs stay in a separate versioned `/usr/local/src`
directory. No shared library or Lean build outputs are used. OS updates, kernel reboots, storage
and institutional network policy remain the host operator's responsibility.

## Publication and cutover

The upload identity is **`cache-upload`**. Its SSH destination is the root of its restricted
namespace: `cache-upload@host:.`, not an absolute filesystem path. Publish recursively with no
archive, permission-preservation, `--inplace`, append, backup, partial-directory, delay-update or
delete options. The [repository publisher](../../scripts/cache/upload.sh) owns staging and
orders artifact uploads before revision mappings. `rrsync` enforces `--ignore-existing` on the
server; the client cannot replace a published artifact or mapping by omitting that option.
Ordinary rsync writes temporary files beside their destination and renames completed uploads.
The account-level sshd policy forces the same wrapper even if another SSH authorization source is
configured for the account. Deployment also rejects an effective `AcceptEnv` beyond `LANG` and
`LC_*`: client-controlled loader, interpreter or path variables would run before the forced
wrapper could clear them. The wrapper rechecks the dedicated data mount for every connection and
caps each uploaded file at 1 GiB. These are containment limits, not a guarantee that a writer
cannot fill the reviewed data filesystem with many allowed files.

nginx serves only these exact public namespaces, with immutable cache headers:

```text
a0/cslib-community/complexitylib/<16 lowercase hex digits>.art
r0/cslib-community/complexitylib/tc/<toolchain>/<40 lowercase hex digits>.jsonl
```

Directories, hidden files, in-progress rsync files, other repository scopes and symbolic links
are inaccessible. There are no nginx access logs; warning/error logs can still contain client
addresses. The origin serves public build outputs and its deployed Git revision at `/healthz`.
The health response proves that the web server is running with that configuration revision; it
does not prove that any particular build is cached. Use a known published mapping and artifact,
then perform a real cache restoration before changing readers.

Keep GCS publication and current reader defaults while commissioning the new mirror. Enable
mirror publication only after provisioning and upload restriction tests pass. A new mirror
initially contains only newly published revisions: historical backfill is an explicit admin
operation. If backfilling from GCS, use a read-only cloud identity, copy artifacts first, and
verify every mapping's artifact references before making that mapping visible. Do not copy an
arbitrary directory tree into the public root. To migrate safely, test a clean user download,
a cold CI restoration and simultaneous downloads during an upload before changing the default
endpoint. Retain GCS until the operator and maintainers agree that recovery and capacity suffice.

After commissioning, enable publication and rerun a successful `main` Lean CI run, or wait for
the next push:

```bash
gh variable set CACHE_SERVER_PUBLISH_ENABLED --repo "$cache_repo" --body true
gh run list --repo "$cache_repo" --workflow lean_action_ci.yml --branch main --event push --status success --limit 5
gh run rerun MAIN_RUN_ID --repo "$cache_repo"
```

The source run must be a `main` **push**, not a dispatch, PR or merge group. Publication artifacts
are named per attempt and consumed by their exact ID, so rerunning the producer or only a failed
publisher does not collide with earlier attempts. A failed server publisher leaves GCS usable.

From an ordinary client checkout with its dependencies/toolchain available, test a complete
published revision against the new server alone. Replace the revision with the successful
publisher's commit and use a fresh temporary Lake cache:

```bash
cache_test_dir="$(mktemp -d)"
cache_revision=REPLACE_WITH_PUBLISHED_40_HEX_COMMIT
cache_toolchain="$(tr -d '[:space:]' < lean-toolchain | sed 's#/#--#; s#:#---#')"
cache_url=https://cache.example.edu
curl --fail --show-error "$cache_url/r0/cslib-community/complexitylib/tc/$cache_toolchain/$cache_revision.jsonl" -o "$cache_test_dir/mapping.jsonl"
LAKE_CACHE_DIR="$cache_test_dir/lake" LAKE_CACHE_ARTIFACT_ENDPOINT="$cache_url/a0" LAKE_CACHE_REVISION_ENDPOINT="$cache_url/r0" \
  lake cache get --repo=cslib-community/complexitylib "$cache_test_dir/mapping.jsonl"
```

The final command must succeed for all requested files. Optional build wrappers can fall back to
compilation and therefore are not a strict cache-completeness check. Then test missing-only CI
restoration and concurrent downloads during publication. In a separate PR, put the new HTTPS
address first in `scripts/cache/endpoints.json`, retaining GCS second. Unset local
`COMPLEXITYLIB_CACHE_URL` overrides when testing that ordered configuration.

## Updates, keys and rollback

Change configuration, templates or the rsync version/digest in a PR, run the checks below, and
review the diff. Deployment from the repository reapplies that revision's configuration. Use the
manual workflow dispatch for the first deployment or recovery, and the opt-in deployment workflow
for subsequent changes; both use this playbook. No shell commands need to be copied into a second
configuration management system. For rsync upgrades, check the upstream security notices,
release digest and restriction tests together. Keep the old versioned prefix until rollback is
no longer needed. The controller pin in `requirements.txt` is updated through the same review.

To rotate publication keys, add the old and new public keys as separate entries in
`upload-keys.yml` in a reviewed PR, deploy that revision, update the protected publisher secret,
and prove a new revision can be uploaded. Then remove the old public key in a second reviewed PR
and deploy again. The checked-in list is the complete authoritative set, so removal revokes that
authorization path. Rotate the administrator key through the institution's SSH management
process; this playbook deliberately does not manage that key or remove recovery access. Rotate a
changed server host key only after verifying its new fingerprint out of band.

To stop using the origin, disable mirror publication and restore the GCS reader endpoint using
the cache runbook. Published files are left intact. To roll back configuration, check out the
last reviewed working revision and rerun its playbook with the same host inputs and that
revision's `CACHE_SERVER_REVISION`. Avoid concurrent deployments. A failed `nginx -t` leaves the
running nginx instance on its previous configuration and restores the previous virtual host file.
Inspect the failed task before restarting the service. Package upgrades are not undone by a Git
rollback. For a failed OS
upgrade, restore the VM snapshot or use the distribution's recovery process. Do not roll back
to an rsync release with known upload-boundary vulnerabilities.

## Capacity and recovery

Before a manual configuration rollback, disable automatic deployment and publication:

```bash
gh variable set CACHE_SERVER_DEPLOY_ENABLED --repo "$cache_repo" --body false
gh variable set CACHE_SERVER_PUBLISH_ENABLED --repo "$cache_repo" --body false
```

This also stops the daily health check but does not cancel already-running jobs. Wait for those
jobs to finish or cancel their specific run IDs. Disabling publication does not switch readers:
restore the GCS-only endpoint configuration in a PR if readers already cut over. Apply the
known-good playbook, then re-enable only the paths the operator intends to use.

Monitor disk bytes and inodes (`df -h`, `df -i`), `/healthz`, HTTPS certificate expiry, transfer
throughput and errors. The playbook refuses a missing, oversized or nearly full data filesystem,
and the upload wrapper refuses new sessions if that mount disappears, but those checks do not
replace alerts or capacity planning. The repository's hosted health check is useful; the
institution may also provide external monitoring. A 1 GB VM should be load-tested on the actual
network before relying on it. Extra RAM helps the filesystem cache; bandwidth and storage growth
may be the first constraints. Alert before either the reviewed byte or inode reserve is reached.
nginx logs use the distribution's nginx log rotation policy.

There is **no automatic artifact garbage collection** in this first deployment. Never delete
artifacts merely because they are old: multiple revisions share them. When pruning is needed,
pause publication, choose the retained revision mappings, compute their referenced artifact
set, dry-run the deletion and keep a backup before deleting unreferenced objects as an
administrator. The upload identity cannot prune. Stale hidden temporary upload files can be
removed separately after publication is paused and active transfers are checked. Keep policy
and any future collector in this repository so users and CI share one implementation.

Back up operator configuration, verified host-key records, SSH recovery access and any private
keys according to institutional practice. Cache payloads can be copied from a verified mirror
or regenerated by trusted CI, so do not make them the only recovery path. A host loss should
allow clients to use GCS or compile locally while a fresh VM is provisioned from this playbook.

### Compromised writer or poisoned cache

Follow the cache guide's canonical
[poison-recovery procedure](../../scripts/cache/README.md#suspected-writer-compromise-or-cache-poisoning).
For this host, set both activation variables to `false`, cancel only identified runs, withhold
pending environment approvals, and land a reviewed GCS-only endpoint change if readers use it.
Remove affected keys from `upload-keys.yml` and protected secrets; rotate administrator, host and
GCS credentials if their trust boundary was crossed, preserving relevant logs first.

Treat the data root as untrusted. Prefer a fresh VM or empty replacement dedicated filesystem,
then reapply a reviewed playbook revision and the reduced key allowlist. Before reactivation,
complete the canonical retained-cache eviction, clean rebuild and replacement-namespace steps;
then validate the effective sshd policy and mount boundary, fetch a known mapping and every
referenced artifact, and perform a cold restore. Record the incident boundary, discarded data,
rotated identities and validation in the handoff. `/healthz` alone is not recovery evidence.

## Validation

The Python tests render the real nginx and sshd templates. On Linux, their integration mode
starts nginx with a temporary self-signed certificate, validates the effective `cache-upload`
sshd policy with `sshd -T -C`, including rejection of a dangerous global `AcceptEnv`, and runs
real uploads through the pinned `rrsync` and forced wrapper. It checks downloads and cache
headers, namespace/temporary-file/symlink exclusions, immutable files, prohibited deletion and
arbitrary commands, the per-file limit, and refusal after the data mount disappears. The test
never contacts a production host.

```bash
python3 -m unittest discover -s scripts -p test_cache_server.py

# Linux test machine only. First install nginx, openssh-server, util-linux and the controller.
cache_test_prefix="$(mktemp -d)"
cd infra/cache-server
ansible-playbook -i localhost, -c local test-install-rsync.yml --become \
  -e "cache_server_rsync_prefix=$cache_test_prefix/install"
cd ../..
CACHE_SERVER_RSYNC_PREFIX="$cache_test_prefix/install" CACHE_SERVER_INTEGRATION=1 \
  python3 -m unittest discover -s scripts -p test_cache_server.py
```

The Linux integration check covers the generated account policy and data plane, not live DNS,
unrelated institutional SSH policy, ACME issuance, Certbot's timer or the actual VM's mount and
capacity. Check those explicitly during bootstrap.
Before enabling automatic upgrades, run the production playbook twice against the dedicated
test host and confirm that the second application makes no configuration changes (a package
repository refresh or newly available package can legitimately change package tasks). `--check`
alone cannot validate an unprovisioned host because the certificate and compiled binaries do
not exist yet.

The implementation follows [nginx static file configuration](https://nginx.org/en/docs/http/ngx_http_core_module.html),
[Certbot's webroot and renewal documentation](https://eff-certbot.readthedocs.io/en/stable/using.html),
and [upstream rrsync](https://www.samba.org/ftp/rsync/rrsync.1), originally by Joe Smith and ported
to Python by Wayne Davison. Consult the [rsync security notices](https://rsync.samba.org/security.html)
when updating the pinned release. The Ansible controller follows its
[release/support policy](https://docs.ansible.com/projects/ansible-core/devel/reference_appendices/release_and_maintenance.html).
