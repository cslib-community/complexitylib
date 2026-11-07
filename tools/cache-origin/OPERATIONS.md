# Operating the MIT cache

Use a dedicated Linux cache host. The existing MIT deployment is
`https://complexitycache.csail.mit.edu`; `/srv/cache-origin` is a separate ext4 mount, and TLS
and its renewal are operator-owned. These are manual hardening/update steps, not automated
provisioning. Read the [security contract and incident recovery](SECURITY.md) first. Run the
commands from a reviewed source checkout; build the Go binary on a separate builder.

## Filesystem and socket identities

Create the `cache-origin` service account and the exclusive `cache-origin-proxy` group. The
nginx worker account (`www-data` on Ubuntu) must be a member of that group. The publisher/GC
units run as `cache-origin:cache-origin-proxy`; no unrelated account/process may use the group.
Do not cohost applications under the nginx identity. Inspect `id www-data`,
`getent group cache-origin-proxy`, running processes and `/run/cache-origin/http.sock` after restart.

The root mount is `cache-origin`-owned mode `0711`; `public/` is `0755`, and `staging/` and
`state/` are `0700`. All public parents/files must be service-owned without group/other write
bits. The permanent `state/lock` must be one regular file owned by `cache-origin`, mode `0600`,
with one hard link. Do not replace/unlink that lock. The service also validates safe path
ancestors. `nginx-tmp/` is separately nginx-owned on the same bounded filesystem. Run GC via
`sudo -u cache-origin /usr/local/bin/cache-origin gc --root /srv/cache-origin [--apply]`.

## Storage and layout

Keep the existing separate ext4 data filesystem. Its directory-index feature supports the
flat hash-key artifact namespace; the current few thousand entries do not justify a storage
schema change. Public objects and staging must remain on the same filesystem for atomic
hard-link installation, and nginx's upload buffers belong on the data disk rather than the
small OS disk. A 4 GiB upload can temporarily need space for both its nginx buffer and staged
files in addition to retained objects. Monitor free bytes as well as the 100,000-entry budget.

The host uses `relatime`, so reads already avoid an access-time update on every request.
Changing to another filesystem, adding directory shards or using a RAM disk needs a measured
bottleneck first. SSD backing can matter for cold reads, but a virtual disk's rotational flag
does not establish its physical backing. Preserve ext4 and the current layout while measuring
download behavior after removing bandwidth limits; do not drop system caches on the live host.

## Publication credential and rotation

Install `apache2-utils` for `htpasswd`. Use [publisher-credential.py](examples/publisher-credential.py)
to generate a fresh 32-byte CSPRNG token, install its bcrypt cost-4 hash and write a private
handoff. The 43-character base64url shape checked by the client is not proof of entropy: do
not choose a password manually or reuse a token. The installed hash file is
`root:cache-origin-proxy 0640`; only the hash is kept there. Plaintext belongs only in the
private operator handoff and GitHub's protected Environment secret.
Cost 4 is intentional for this generated 256-bit token: password stretching adds little
protection against guessing such a token, while nginx verifies bcrypt synchronously in a worker.
This policy is unsuitable for human-chosen passwords. Existing cost-12 installations can rehash
the same generated token privately through `htpasswd -niBC 4` using stdin, then atomically replace
the hash file with the same owner/group/mode; the token and GitHub secret do not need to change.

```bash
sudo install -d -m 0700 /root/cache-origin-handoff
sudo python3 tools/cache-origin/examples/publisher-credential.py \
  --handoff /root/cache-origin-handoff/publisher-initial.txt
sudo nginx -t
```

The helper refuses to replace an existing account unless `--rotate` is supplied. Rotation uses
the same command with `--rotate` and a **new** private handoff filename. It writes/fsyncs the
handoff before atomically switching the active hash. Coordinate a paused publisher, replace
GitHub's `CACHE_SERVER_PASSWORD`, test the new credential and verify the previous password
fails before resuming. Never print credentials, put them in URLs/argv, or commit handoffs.
To revoke immediately, stop publication and replace the auth file with an empty root-owned
`0640` file of the same group. Do not revoke authentication by disabling the nginx auth directive.

## Limits, logs and notifications

Install nginx, `apache2-utils`, `fail2ban`, `python3-systemd`, `nftables`, `whois` and Postfix.
Configure Postfix as an outbound-only local mailer: apply the settings in
[cache-origin-postfix.cf](examples/cache-origin-postfix.cf) to the distro's `main.cf` with
`postconf -e`, then run `postfix check` and restart Postfix. Inspect listeners to confirm port 25
is bound only to loopback. This host can deliver directly to MIT's MX without SMTP credentials;
inbox receipt of the commissioning test was confirmed on November 5, 2026. Postfix queues
temporary failures and retries for up to one day. Check `postqueue -p` and the journal if
notifications stop arriving. A successful local submission is not proof of inbox delivery.

Install the reviewed files as follows (root-owned, non-writable by other accounts):

| Source in `examples/` | Destination |
|---|---|
| `nginx.conf` | The host's single nginx cache HTTPS configuration; replace `cache.example.edu` with the actual hostname |
| `cache-origin.service`, `cache-origin-gc.service`, `cache-origin-gc.timer` | `/etc/systemd/system/` |
| `cache-origin-alert.py`, `cache-origin-health.py` | `/usr/local/libexec/` (mode `0644`) |
| `cache-origin-alert@.service`, `cache-origin-health.service`, `cache-origin-health.timer` | `/etc/systemd/system/` |
| `nginx-cache-origin.conf` | `/etc/systemd/system/nginx.service.d/cache-origin.conf` |
| `cache-origin-journald.conf` | `/etc/systemd/journald.conf.d/zz-cache-origin.conf` (after vendor `syslog.conf`) |
| `cache-origin-usage-journald.conf` | `/etc/systemd/journald@cache-origin-usage.conf.d/zz-cache-origin-usage.conf` |
| `cache-origin-usage-service.conf` | `/etc/systemd/system/systemd-journald@cache-origin-usage.service.d/cache-origin.conf` |
| `cache-origin-fail2ban.conf` | `/etc/fail2ban/jail.d/cache-origin.local` |

nginx's upload request/connection limits apply before password verification; rejected
requests return `429`. Read limits allow the native Lake curl client's parallel transfers.
Upload limits are per IP; there is no small shared upload bucket or connection pool that
anonymous clients can consume instead of the legitimate publisher. Broader server-wide
request/connection limits still protect the host, so this does not promise immunity to a
large traffic flood. Bandwidth is uncapped: neither nginx `limit_rate` nor a cache-owned traffic
shaper is installed. The upload-size bound is 4 GiB, buffered and staged on the data filesystem;
allow space for both copies plus retained objects. Byte/count/memory limits remain independent.
Aggregate authentication work has no small shared upload bound: many source IPs can still
occupy nginx workers despite per-IP limits and Fail2ban. Cost 4 makes each comparison cheaper
without solving general CPU or traffic exhaustion. If IPv6 is enabled, limits/bans apply to
individual addresses rather than a client's whole prefix; rotating addresses can evade them.

The 4 GiB upload limit is a size ceiling, not a promise that every 4 GiB upload finishes in
time. curl allows 360 seconds per attempt with a 600-second retry window; the GitHub publisher
job has a 15-minute ceiling. The Go origin has five-minute read/write deadlines after nginx
starts forwarding its buffered body. nginx's body timeout is 60 seconds between reads, and its
proxy read/send timeouts are six minutes between operations. These cover different phases and
must be considered together when changing them. Keep the current deadlines while successful
publications remain comfortably below them; investigate network, staging/fsync and size growth
before increasing budgets together. The usage journal's PUT duration measures the whole nginx
request, while the CI publish step also includes local packaging. Neither response-body bytes
in usage records nor the configured size ceiling measures uploaded package bytes.

When updating an older installation that has the previous bandwidth cap, inspect its actual
default-route interface and queue configuration before removing anything:

```bash
ip route show default
sudo tc -s qdisc show dev <primary-interface>
```

Save that output and the old unit privately for rollback. Remove nginx's old
`Requires`/`After=cache-origin-egress.service` dependency, reload systemd, and disable/stop the
obsolete `cache-origin-egress.service`. Stopping that service alone leaves its queue in place.
Only after confirming the root queue is the cache-owned TBF (128 Mbit/s, handle `1:`, 256 KB
burst, 400 ms latency) and there is no unrelated policy, replace that specific queue with
the recorded uncapped queue (or the kernel default when no prior policy was recorded).
For the MIT host's recorded queue, after the ownership checks above:

```bash
sudo tc qdisc replace dev ens3 root pfifo_fast
sudo tc -s qdisc show dev ens3
```

To choose the kernel default instead, use `sudo tc qdisc del dev <primary-interface> root`
and verify it with `sudo tc -s qdisc show dev <primary-interface>`. Remove the obsolete unit
file and reload systemd again. Never delete or replace an unknown shaper; resolve ownership first. Keep SSH
and an operator console available, and verify the live queue and nginx dependency list after
the change. On fresh installations these migration steps are unnecessary.

The dedicated-host journal policy caps persistent logs at 64 MiB and runtime logs at 16 MiB,
retaining at most seven days. Do not leave an additional unbounded nginx/rsyslog file sink.
Replace the existing main-context nginx `error_log /var/log/...` with the reviewed syslog sink
too; the dedicated-host HTTP fragment disables global access logging and supplies a bounded
error sink, including HTTP 80/ACME. HTTPS adds selective error records and a separate usage sink.
Check the **complete** `nginx -T` output for other file sinks, not just the new HTTPS fragment.
The default journal records authentication failures and server errors, omitting successful
downloads and routine throttling rejections. Check suppression notices: dropped authentication
records weaken Fail2ban detection. The supplied jail bans three failed authentications within
ten minutes for one hour. Ban/unban events are recorded in the journal without email;
email to `edemaine@mit.edu` is reserved for service failures and capacity trouble.
Use underscore-only syslog tags and `nohostname` as in the example so journald records
`SYSLOG_IDENTIFIER=cache_origin_error`, matching the jail. Check effective ordering with
`systemd-analyze cat-config systemd/journald.conf`: a later vendor drop-in can otherwise undo
`ForwardToSyslog=no`. Inspect rsyslog pulling inputs such as `imjournal` too; disabling journal
forwarding alone does not stop them. The dedicated MIT host uses journald with rsyslog disabled.
The hourly health timer checks mount presence and 80% byte/inode use on both data and OS
filesystems. Publisher, GC, nginx and health failures invoke the alert service. nginx's
service drop-in also bounds its memory and task count; the Go services retain their own limits.

## Usage statistics

The second nginx access sink writes one JSON record per completed HTTPS request into the
**separate** `cache-origin-usage` journal namespace. It includes timestamp, method, object path,
HTTP status, response-body bytes and request duration. It records successful downloads, HEADs,
missing objects, publications and throttled requests without filling the security/error journal.
Only valid cache/publication paths are retained; other paths become `/other`, and methods
outside GET/HEAD/PUT become `OTHER`. This bounds untrusted fields below the syslog message limit.
Authorization, passwords, client IPs, query strings and bodies are omitted. Numeric values are
JSON strings; convert them when aggregating. Duration includes response pacing and client speed;
byte counts exclude HTTP/TLS overhead. HEAD contributes zero body bytes.

This uses systemd's existing namespace service/socket templates, with no new package or network
listener. Install both usage drop-ins above and keep nginx's `LogNamespace` unset: moving all
nginx logging into this namespace would break the default-journal Fail2ban source. Before
reloading nginx, check the effective namespace configuration and start its socket/service:

```bash
sudo systemd-analyze cat-config systemd/journald@cache-origin-usage.conf
sudo systemctl daemon-reload
sudo systemctl start systemd-journald@cache-origin-usage.socket systemd-journald@cache-origin-usage.service
sudo nginx -t
sudo systemctl reload nginx
sudo journalctl --namespace=cache-origin-usage --identifier=cache_usage --since '1 hour ago' --output=cat
sudo journalctl --namespace=cache-origin-usage --disk-usage
```

nginx's service drop-in pulls in the socket on subsequent boots. The namespace service has a
64 MiB memory limit and sends the existing operational alert if it fails. Usage events do not
send email. The namespace has its own **64 MiB persistent / 16 MiB runtime retention budget**,
8/4 MiB files, daily file rotation and a seven-day age policy. It uses OS-disk space in addition
to the default journal's budget. These are journal rotation policies, not filesystem quotas or
an exact deletion deadline: active files can exceed the target and age cleanup uses whole files.
Busy traffic shortens the available history. Rate suppression and forwarding are disabled for
this namespace; no successful-download records are copied into the default journal.
Keep the kernel audit policy unchanged: the example's empty `Audit=` value is the portable
equivalent of `Audit=keep` on current systemd. Do not use `Audit=no`, which can disable kernel
auditing globally. Some installations may have a later `Audit=keep` override. Inspect later
drop-ins when updating; remove a redundant override only after confirming it has no other
unique settings and the effective policy is unchanged.

For a small daily summary, stream the retained records through Python (constant memory):

```bash
sudo journalctl --namespace=cache-origin-usage --identifier=cache_usage --since '24 hours ago' --output=cat |
python3 -c '
from collections import Counter
import json, sys
totals = Counter()
for line in sys.stdin:
    record = json.loads(line)
    status = int(record["status"])
    totals["requests"] += 1
    totals["body_bytes"] += int(record["bytes"])
    totals["successful_gets"] += record["method"] == "GET" and status in (200, 206)
    totals["mapping_gets"] += record["method"] == "GET" and record["uri"].startswith("/r0/") and status == 200
    totals["not_found"] += status == 404
    totals["throttled"] += status == 429
    totals["server_errors"] += status >= 500
print(json.dumps(dict(totals), indent=2))
'
```

These are retained request statistics, not counts of people or complete builds. Retries and
partial restores create multiple requests; a client with local artifacts may make very few.
Nonblocking syslog can lose records under pressure or a collector outage, and rotation removes
older data, so use this for operational usage estimates rather than exact accounting. To keep
long-term trends, export summaries before the underlying records rotate away.

## Validate, activate and roll back

Back up the existing binary/configuration privately before applying a reviewed update. Install
the binary and root-owned examples, run `systemd-analyze verify` and `nginx -t`, reload systemd,
restart the publisher/nginx where group membership changed, and enable the GC and
health timers/services. Apply the journald policy and start/reload Fail2ban only after its
filter matches an actual nginx failure record with the expected journal identifier. Start the
usage namespace before nginx and verify a real GET, HEAD and missing-object request produce
valid records with matching bytes/status, without credentials or query strings. Inspect both
journals to confirm isolation and the effective usage limits; rotate/restart only this namespace
when testing persistence, preserving the security journal.

Test trusted TLS, socket/hash-file permissions, missing/incorrect authentication, valid PUT and
identical retry, conflicting mapping/artifact rejection, matching GET/HEAD, `no-store`, rejected
DELETE/private/listing paths, and `429` rate/connection responses. Use an isolated fixture for
abuse/GC tests; do not ban the operator's SSH source or shorten production retention. Test a
controlled service-failure notification through the installed alert unit and confirm inbox
delivery; inspect the Postfix queue. Test byte/inode threshold behavior in a fixture without
filling production disks. Verify bandwidth caps are absent and journal storage remains bounded.

Rollback means restoring the saved binary/configuration and permissions, removing only these
new unit drop-ins if necessary, inspecting any queue policy before restoring a saved one, running `nginx -t` and restarting
the affected services. Keep the original mounted store intact; neither update nor rollback
formats disks, deletes real build objects or replaces `state/lock`. Never roll back to exposed
credentials. For a new installation, obtain exact-head human review and complete host
commissioning before enabling CI publication. Before selecting MIT as the default reader,
complete a real-build cold restore, exercise recovery and obtain separate cutover approval. Keep GCS
publication and the opt-in MIT-first/GCS-second mirror list during testing.

References: [nginx request limits](https://nginx.org/en/docs/http/ngx_http_limit_req_module.html),
[connection limits](https://nginx.org/en/docs/http/ngx_http_limit_conn_module.html),
[bcrypt/stdin options](https://httpd.apache.org/docs/2.4/programs/htpasswd.html).
Usage fields and namespaces follow [nginx access logging](https://nginx.org/en/docs/http/ngx_http_log_module.html)
and [systemd journal namespaces](https://www.freedesktop.org/software/systemd/man/systemd-journald.service.html).
