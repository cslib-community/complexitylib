# Cache dashboard prototype

This is a local prototype for the MIT origin, developed and committed without a PR or push.
The public page is a static nginx site at `/`; a five-minute systemd timer exports aggregate
statistics to `/stats.json`. It adds no database, API listener or cache administration route.
The cache publisher and reader protocol stay unchanged.

## What the numbers mean

- Downloads count successful artifact GET requests, including retries and range requests;
  they do not count distinct people or complete restores. Mapping requests show interest in
  a build, including automated probes. HTTP HEAD and dashboard views are not downloads.
- Served bytes count successful cache GET response bodies, not uploaded request bodies or
  HTTP/TLS overhead. Average traffic rate is those bytes × 8 divided by the observed
  wall-clock window, including idle time. It is not the mean speed of individual transfers.
- Latency is the elapsed nginx request time of successful cache GETs, including response
  transfer and client speed. It is not time to first byte or isolated server processing time.
- Traffic covers retained usage records. Journal rotation, downtime and nonblocking syslog can
  remove records, so the page exposes coverage and describes the statistics as observations,
  not exact accounting. Recent deliberate benchmark downloads also appear in the totals.
- Storage sharing compares the sum of compressed artifacts referenced by every retained build
  with the unique artifacts actually stored. The prominent sharing factor is the former
  divided by the latter; saved bytes appear beside it. It does not estimate uncompressed build size or
  compilation time saved. Disk usage includes staging and upload buffers as well as artifacts.
- GC counts and removed bytes come from successful applied collections. Bytes cover removed
  artifact/mapping payloads, excluding directory metadata and abandoned staging directories.
  Historical collections without byte accounting show an unavailable value.

## Install from a reviewed local commit

Transfer the exact local source bundle over the existing authenticated deployment connection;
verify its digest and recorded Git revision. A public GitHub push is unnecessary. Preserve a
private rollback copy of the current binary, nginx configuration and any existing dashboard
files. Build the Linux Go binary on the separate builder if the GC reporting changes are new;
do not run Lean or compile on the cache VM. Preserve the mounted store and permanent lock.

Install these root-owned files:

| Source | Destination | Mode |
|---|---|---|
| `dashboard/index.html`, `dashboard/app.js`, `dashboard/style.css` | `/usr/local/share/cache-dashboard/` | `0644` |
| `dashboard/collect.py` | `/usr/local/libexec/cache-dashboard-collect.py` | `0644` |
| `examples/cache-dashboard.service`, `examples/cache-dashboard.timer` | `/etc/systemd/system/` | `0644` |

Only the three static assets are installed in the web directory. Test fixtures and the collector
source are not served. The service creates `/var/lib/cache-dashboard/`, which contains only its
bounded public aggregate JSON. It runs with a read-only view of the cache, restricted write
access, a 128 MiB memory ceiling and a 90-second timeout. A busy store keeps the previous storage
snapshot rather than waiting on the publication lock. A failed collector leaves the last good
JSON in place; the page marks old data stale. The prototype adds no new email notifications.

Merge only the dashboard locations from `examples/nginx.conf` into the existing host site,
preserving actual TLS paths, upload authentication, limits, temporary directories and usage/error
journal sinks. Serve exactly `/`, `/app.js`, `/style.css` and `/stats.json`; other unknown paths
remain 404. Dashboard routes accept only GET/HEAD. Their aliases point outside the cache's
artifact namespace. The HTML policy permits only same-origin scripts, styles and data requests.

```bash
sudo systemctl daemon-reload
sudo systemd-analyze verify cache-dashboard.service cache-dashboard.timer
sudo systemctl start cache-dashboard.service
sudo python3 -m json.tool /var/lib/cache-dashboard/stats.json >/dev/null
sudo nginx -t
sudo systemctl reload nginx
sudo systemctl enable --now cache-dashboard.timer
```

Inspect `/` at desktop and phone widths, switching each time window and checking empty/stale
states. Verify that real aggregates agree with the journal/store, page refreshes do not inflate
cache download counts, private paths remain blocked, and ordinary artifact/mapping GET/HEAD and
publication still work. Confirm the collector's peak memory and runtime on the actual VM.

## Rollback

Disable/stop only `cache-dashboard.timer`, wait for its owned collector process to stop, restore
the saved nginx configuration, run `nginx -t` and reload nginx. Remove only this prototype's
installed assets/unit files and aggregate output after checking their ownership. Restore the
saved Go binary if rolling back the reporting addition as well. Do not remove build artifacts,
replace `state/lock`, change credentials, alter the data filesystem or reset journal history.

The Operator's Manual reaches this page through the origin runbook. Agent roles and handoffs
are unchanged; the Agent Operator's Manual needs no update for this prototype.
