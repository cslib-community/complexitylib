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

## Publication credential and rotation

Install `apache2-utils` for `htpasswd`. Use [publisher-credential.py](examples/publisher-credential.py)
to generate a fresh 32-byte CSPRNG token, install its bcrypt cost-12 hash and write a private
handoff. The 43-character base64url shape checked by the client is not proof of entropy: do
not choose a password manually or reuse a token. The installed hash file is
`root:cache-origin-proxy 0640`; only the hash is kept there. Plaintext belongs only in the
private operator handoff and GitHub's protected Environment secret.

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
| `cache-origin-journald.conf` | `/etc/systemd/journald.conf.d/cache-origin.conf` |
| `cache-origin-fail2ban.conf` | `/etc/fail2ban/jail.d/cache-origin.local` |

nginx's upload request/connection limits apply before expensive password verification; rejected
requests return `429`. Read limits allow the native Lake curl client's parallel transfers.
`limit_rate` paces each response, but is **not** a hard aggregate egress cap for short requests.
Install the separate [tc egress unit](examples/cache-origin-egress.service) only after inspecting
the actual default-route interface and its current queue discipline:

```bash
ip route show default
sudo tc -s qdisc show dev <primary-interface>
```

Save that output privately for rollback. If the host has an existing custom shaper, do not
overwrite it; integrate an equivalent bound with its owner. For a dedicated host with only its
distro-default qdisc, set `CACHE_INTERFACE` in the unit to the inspected interface, install the
unit under `/etc/systemd/system/`, and enable it. It uses a token bucket at **128 Mbit/s** with a
256 KiB burst and bounded queue latency for the entire interface, including short requests.
nginx requires this unit before starting. Check `tc -s qdisc show` after restart and measure
long and short download bursts; record the rate, burst and drops rather than claiming an
instantaneous byte-per-second ceiling. Stopping the unit leaves its cap in place. For rollback,
inspect the current qdisc and explicitly restore the saved configuration; do not delete a
replacement shaper installed by another operator. This shapes SSH/mail too, so retain an operator console during
the initial change. No extra network listener is installed.

The dedicated-host journal policy caps persistent logs at 64 MiB and runtime logs at 16 MiB,
retaining at most seven days. Do not leave an additional unbounded nginx/rsyslog file sink.
Replace the existing main-context nginx `error_log /var/log/...` with the reviewed syslog sink
too; the dedicated-host HTTP fragment disables global access logging and supplies a bounded
error sink, including HTTP 80/ACME. The HTTPS server overrides access logging selectively.
Check the **complete** `nginx -T` output for other file sinks, not just the new HTTPS fragment.
nginx logs authentication failures and server errors, omitting successful anonymous downloads
and routine throttling rejections. Check journal suppression notices: dropped authentication
records weaken Fail2ban detection. The supplied jail bans three failed authentications within
ten minutes for one hour and emails `edemaine@mit.edu`; the mailer is the local Postfix queue.
The hourly health timer checks mount presence and 80% byte/inode use on both data and OS
filesystems. Publisher, GC, nginx, egress and health failures invoke the alert service. nginx's
service drop-in also bounds its memory and task count; the Go services retain their own limits.

## Validate, activate and roll back

Back up the existing binary/configuration privately before applying a reviewed update. Install
the binary and root-owned examples, run `systemd-analyze verify` and `nginx -t`, reload systemd,
restart the publisher/nginx where group membership changed, and enable the GC, egress and
health timers/services. Apply the journald policy and start/reload Fail2ban only after its
filter matches an actual nginx failure record with the expected journal identifier.

Test trusted TLS, socket/hash-file permissions, missing/incorrect authentication, valid PUT and
identical retry, conflicting mapping/artifact rejection, matching GET/HEAD, `no-store`, rejected
DELETE/private/listing paths, and `429` rate/connection responses. Use an isolated fixture for
abuse/GC tests; do not ban the operator's SSH source or shorten production retention. Test a
controlled service-failure notification through the installed alert unit and confirm inbox
delivery; inspect the Postfix queue. Test byte/inode threshold behavior in a fixture without
filling production disks. Verify actual egress shaping and bounded journal storage too.

Rollback means restoring the saved binary/configuration and permissions, removing only these
new unit drop-ins if necessary, explicitly restoring the saved qdisc after inspection, running `nginx -t` and restarting
the affected services. Keep the original mounted store intact; neither update nor rollback
formats disks, deletes real build objects or replaces `state/lock`. Never roll back to exposed
credentials. Before enabling CI publication or default MIT readers, obtain exact-head human
review, complete a real-build cold restore and exercise the recovery procedure. Keep GCS
publication and the opt-in MIT-first/GCS-second mirror list during testing.

References: [nginx request limits](https://nginx.org/en/docs/http/ngx_http_limit_req_module.html),
[connection limits](https://nginx.org/en/docs/http/ngx_http_limit_conn_module.html),
[bcrypt/stdin options](https://httpd.apache.org/docs/2.4/programs/htpasswd.html).
