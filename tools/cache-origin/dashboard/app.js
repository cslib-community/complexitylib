/* Copyright (c) 2026 Erik Demaine. Apache-2.0. */
(() => {
  "use strict";

  const byId = (id) => document.getElementById(id);
  const SVG = "http://www.w3.org/2000/svg";
  const windows = {hour: 3600, day: 86400, week: 604800};
  const windowLabels = {hour: "1 hour", day: "24 hours", week: "7 days"};
  const countFormat = new Intl.NumberFormat(undefined, {maximumFractionDigits: 0});
  let snapshot = null;
  let selectedWindow = "day";
  let selectedChart = "body_bytes";
  let expandedBuilds = false;
  let loading = false;
  let refreshTimer;
  let fetchFailed = false;

  function finite(value) { return typeof value === "number" && Number.isFinite(value) && value >= 0; }
  function count(value) { return finite(value) ? countFormat.format(value) : "—"; }
  function date(value) { const n = typeof value === "string" ? Date.parse(value) : NaN; return Number.isFinite(n) ? n : null; }
  function text(id, value) { byId(id).textContent = value; }
  function decimal(value, digits = 1) { return new Intl.NumberFormat(undefined, {maximumFractionDigits: digits}).format(value); }
  function bytes(value) {
    if (!finite(value)) return "—";
    if (value < 1000) return count(value) + " B";
    const units = ["kB", "MB", "GB", "TB"];
    let scaled = value / 1000, i = 0;
    while (scaled >= 1000 && i < units.length - 1) { scaled /= 1000; i++; }
    return decimal(scaled, scaled >= 100 ? 0 : 1) + " " + units[i];
  }
  function bitrate(mbps) {
    if (!finite(mbps)) return "—";
    if (mbps === 0) return "0 bit/s";
    if (mbps < 0.001) return decimal(mbps * 1e6, 0) + " bit/s";
    if (mbps < 1) return decimal(mbps * 1000) + " kbit/s";
    if (mbps >= 1000) return decimal(mbps / 1000) + " Gbit/s";
    return decimal(mbps) + " Mbit/s";
  }
  function duration(seconds) {
    if (!finite(seconds)) return "—";
    return seconds < 1 ? decimal(seconds * 1000, seconds < 0.01 ? 1 : 0) + " ms" : decimal(seconds, 2) + " s";
  }
  function age(value, now = Date.now()) {
    const timestamp = date(value);
    if (timestamp === null) return "Not recorded";
    const seconds = Math.max(0, (now - timestamp) / 1000);
    if (seconds < 60) return "just now";
    if (seconds < 3600) return count(Math.floor(seconds / 60)) + " min ago";
    if (seconds < 86400) return decimal(seconds / 3600) + " hours ago";
    return decimal(seconds / 86400) + " days ago";
  }
  function interval(seconds) {
    if (seconds < 3600) return count(Math.max(1, Math.round(seconds / 60))) + " min";
    if (seconds < 86400) return decimal(seconds / 3600) + " hours";
    return decimal(seconds / 86400) + " days";
  }
  function leanVersion(value) {
    if (typeof value !== "string") return "Lean version unavailable";
    return value.replace(/^leanprover--lean4---/, "Lean ").replace(/^leanprover\/lean4:/, "Lean ");
  }
  function commitLink(revision) {
    const valid = typeof revision === "string" && /^[0-9a-f]{40}$/.test(revision);
    const node = document.createElement(valid ? "a" : "span");
    node.className = "commit";
    node.textContent = valid ? revision.slice(0, 8) : "Unavailable";
    if (valid) { node.href = "https://github.com/cslib-community/complexitylib/commit/" + revision; node.title = revision; }
    return node;
  }
  function svgNode(tag, attributes = {}, content) {
    const node = document.createElementNS(SVG, tag);
    for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, String(value));
    if (content !== undefined) node.textContent = content;
    return node;
  }
  function validate(data) {
    const object = (value) => value !== null && typeof value === "object" && !Array.isArray(value);
    const optionalDate = (value) => value === null || date(value) !== null;
    const optionalNumber = (value) => value === null || finite(value);
    const validBuild = (build) => object(build) && typeof build.revision === "string" && /^[0-9a-f]{40}$/.test(build.revision)
      && typeof build.toolchain === "string" && build.toolchain.length <= 160 && optionalDate(build.published_at)
      && [build.module_count, build.artifact_count, build.artifact_bytes].every(finite);
    if (!data || data.schema !== 1 || date(data.generated_at) === null || date(data.generated_at) > Date.now() + 600000 || !data.windows || !data.coverage || !Array.isArray(data.series) || data.series.length > 200) throw new Error("Invalid snapshot");
    const fields = ["seconds", "requests", "artifact_downloads", "mapping_downloads", "body_bytes", "average_mbps", "successes", "misses", "errors", "throttled", "auth_failures", "publication_successes"];
    for (const key of Object.keys(windows)) {
      const win = data.windows[key];
      if (!win || fields.some((field) => !finite(win[field])) || !object(win.status_counts) || Object.values(win.status_counts).some((value) => !finite(value)) || [win.median_seconds, win.p95_seconds].some((value) => !optionalNumber(value))) throw new Error("Invalid time window");
    }
    if (!data.storage || !data.storage.disk || !Array.isArray(data.builds) || data.builds.length > 20 || !Array.isArray(data.popular_builds) || data.popular_builds.length > 10 || !data.gc) throw new Error("Incomplete snapshot");
    if (!optionalDate(data.coverage.since) || !optionalDate(data.coverage.until) || ![data.coverage.records, data.coverage.invalid_records, data.coverage.excluded_requests].every(finite) || typeof data.coverage.limited !== "boolean") throw new Error("Invalid coverage");
    const store = data.storage;
    if (typeof store.stale !== "boolean" || !optionalDate(store.snapshot_at)
        || ![store.entry_count, store.artifact_count, store.mapping_count, store.artifact_bytes, store.mapping_bytes, store.logical_retained_bytes, store.saved_bytes, store.dedup_ratio, store.missing_artifacts].every(optionalNumber)
        || ![store.disk.total_bytes, store.disk.used_bytes, store.disk.available_bytes, store.disk.inodes_total, store.disk.inodes_available].every(optionalNumber)) throw new Error("Invalid storage");
    if (data.latest !== null && !validBuild(data.latest)) throw new Error("Invalid latest build");
    if (data.builds.some((build) => !validBuild(build) || !finite(build.mapping_requests))) throw new Error("Invalid builds");
    if (data.popular_builds.some((build) => !object(build) || !/^[0-9a-f]{40}$/.test(build.revision) || typeof build.toolchain !== "string" || build.toolchain.length > 160 || !finite(build.mapping_requests))) throw new Error("Invalid popular builds");
    if (!["ok", "failed", "unknown"].includes(data.gc.status) || !optionalDate(data.gc.last_run_at) || !optionalDate(data.gc.last_success_at)
        || ![data.gc.deleted_artifacts, data.gc.deleted_mappings, data.gc.deleted_bytes].every(optionalNumber)) throw new Error("Invalid collection result");
    for (const row of data.series) if (!row || date(row.time) === null || [row.requests, row.downloads, row.body_bytes, row.average_mbps].some((value) => !finite(value))) throw new Error("Invalid traffic history");
    return data;
  }

  function renderFreshness() {
    if (!snapshot) return;
    const secondsOld = (Date.now() - date(snapshot.generated_at)) / 1000;
    const stale = fetchFailed || secondsOld > Math.max(900, (snapshot.refresh_seconds || 300) * 3);
    byId("live-dot").className = "live-dot " + (stale ? "stale" : "live");
    text("freshness", (stale ? "Snapshot from " : "Updated ") + age(snapshot.generated_at));
    const notice = byId("notice");
    if (fetchFailed) {
      notice.textContent = "The latest snapshot could not be loaded. Showing the last available data.";
      notice.className = "notice warning";
      notice.hidden = false;
    } else if (stale) {
      notice.textContent = "These statistics have not refreshed recently. Cache downloads may still be available.";
      notice.className = "notice warning";
      notice.hidden = false;
    } else if (snapshot.storage.missing_artifacts > 0) {
      notice.textContent = "The storage snapshot contains references to missing artifacts. Some downloads may be unavailable.";
      notice.className = "notice warning";
      notice.hidden = false;
    } else notice.hidden = true;
  }

  function renderChart() {
    const svg = byId("traffic-chart");
    svg.replaceChildren();
    const end = date(snapshot.generated_at);
    const start = end - windows[selectedWindow] * 1000;
    const rows = snapshot.series.filter((row) => date(row.time) >= start - 3600000 && date(row.time) <= end);
    const outerWidth = Math.max(280, svg.clientWidth || 720);
    const outerHeight = Math.max(190, svg.clientHeight || 230);
    svg.setAttribute("viewBox", `0 0 ${outerWidth} ${outerHeight}`);
    const x0 = 54, y0 = 15, width = outerWidth - 68, height = outerHeight - 56;
    const format = selectedChart === "body_bytes" ? bytes : selectedChart === "average_mbps" ? bitrate : count;
    const labels = {body_bytes: "Response-body bytes per hour", average_mbps: "Average traffic rate per hour, including idle time", requests: "Cache requests per hour"};
    text("chart-label", labels[selectedChart]);
    const total = selectedChart === "body_bytes" ? bytes(snapshot.windows[selectedWindow].body_bytes) : selectedChart === "average_mbps" ? bitrate(snapshot.windows[selectedWindow].average_mbps) : count(snapshot.windows[selectedWindow].requests);
    text("chart-total", total + (selectedChart === "average_mbps" ? " observed average" : " in this window"));
    const peak = Math.max(...rows.map((row) => row[selectedChart]), 0);
    const max = peak > 0 ? peak * 1.12 : 1;
    for (let n = 0; n <= 3; n++) {
      const y = y0 + height * n / 3;
      svg.append(svgNode("line", {x1: x0, x2: x0 + width, y1: y, y2: y, class: "chart-grid"}));
      svg.append(svgNode("text", {x: x0 - 10, y: y + 4, "text-anchor": "end", class: "chart-axis"}, peak > 0 ? format(max * (1 - n / 3)) : (n === 3 ? "0" : "")));
    }
    if (!rows.length) {
      svg.append(svgNode("text", {x: x0 + width / 2, y: y0 + height / 2, "text-anchor": "middle", class: "chart-empty"}, "No traffic history in this window yet"));
      svg.setAttribute("aria-label", "No traffic history in the selected window");
    } else {
      const first = Math.max(start, date(rows[0].time));
      const span = Math.max(end - first, 1);
      const points = rows.map((row) => [x0 + Math.max(0, date(row.time) - first) / span * width, y0 + height * (1 - row[selectedChart] / max)]);
      const commands = points.map((point, i) => (i ? "L" : "M") + point[0].toFixed(2) + "," + point[1].toFixed(2)).join(" ");
      const area = commands + ` L${points[points.length - 1][0]},${y0 + height} L${points[0][0]},${y0 + height} Z`;
      svg.append(svgNode("path", {d: area, class: "chart-area"}));
      svg.append(svgNode("path", {d: commands, class: "chart-line"}));
      for (let i = 0; i < points.length; i++) {
        const point = svgNode("circle", {cx: points[i][0], cy: points[i][1], r: points.length === 1 ? 3.5 : 2, fill: "var(--accent)"});
        point.append(svgNode("title", {}, new Date(rows[i].time).toLocaleString() + ": " + format(rows[i][selectedChart])));
        svg.append(point);
      }
      for (let n = 0; n <= 3; n++) {
        const stamp = first + span * n / 3;
        const label = new Date(stamp).toLocaleString(undefined, selectedWindow === "week" ? {month: "short", day: "numeric", hour: "numeric"} : {hour: "numeric", minute: "2-digit"});
        svg.append(svgNode("text", {x: x0 + width * n / 3, y: y0 + height + 27, "text-anchor": n === 0 ? "start" : n === 3 ? "end" : "middle", class: "chart-axis"}, label));
      }
      svg.setAttribute("aria-label", labels[selectedChart] + "; peak " + format(peak) + "; " + rows.length + " hourly samples");
    }
  }

  function renderResponses(win) {
    const groups = [win.successes, win.misses, win.throttled + win.auth_failures, win.errors];
    groups.push(Math.max(0, win.requests - groups.reduce((a, b) => a + b, 0)));
    const ids = ["response-success", "response-miss", "response-reject", "response-error", "response-other"];
    const classes = ["successful", "missed", "rejected", "failed", "other"];
    const svg = byId("response-chart");
    svg.replaceChildren();
    let x = 0;
    groups.forEach((value, i) => {
      text(ids[i], count(value));
      const width = win.requests > 0 ? value / win.requests * 400 : 0;
      if (width > 0) svg.append(svgNode("rect", {x, y: 0, width, height: 16, class: classes[i]}));
      x += width;
    });
    if (!win.requests) svg.append(svgNode("rect", {x: 0, y: 0, width: 400, height: 16, class: "other"}));
    svg.setAttribute("aria-label", win.requests ? groups.map((value, i) => classes[i] + ": " + count(value)).join(", ") : "No cache requests yet");
    text("response-total", count(win.requests) + " requests");
    text("latency-median", duration(win.median_seconds));
    text("latency-p95", duration(win.p95_seconds));
  }

  function renderStorage() {
    const store = snapshot.storage;
    const disk = store.disk;
    const percent = finite(disk.total_bytes) && disk.total_bytes > 0 && finite(disk.used_bytes) ? Math.min(100, disk.used_bytes / disk.total_bytes * 100) : null;
    text("disk-percent", percent === null ? "—" : decimal(percent, 1) + "% used");
    byId("disk-meter").value = percent || 0;
    text("disk-used", bytes(disk.used_bytes) + " of " + bytes(disk.total_bytes) + " used");
    text("disk-free", bytes(disk.available_bytes) + " available");
    text("artifact-size", bytes(store.artifact_bytes));
    text("artifact-count", count(store.artifact_count));
    text("inode-free", count(disk.inodes_available));
    text("sharing-label", finite(store.mapping_count) && finite(store.artifact_count) ? count(store.mapping_count) + " retained builds sharing " + count(store.artifact_count) + " artifact files" : "The storage snapshot will appear when the cache is idle.");
    text("retained-count", count(store.mapping_count) + " builds");
    text("storage-freshness", store.stale ? (date(store.snapshot_at) === null ? "Waiting for first snapshot" : "Storage snapshot is stale") : "");
    text("saved-bytes", bytes(store.saved_bytes) + " saved");
    text("dedup-ratio", finite(store.dedup_ratio) ? decimal(store.dedup_ratio, 1) + "×" : "—");
    text("physical-bytes", bytes(store.artifact_bytes) + " actual");
    text("logical-bytes", bytes(store.logical_retained_bytes) + " separate copies");
    const svg = byId("reuse-chart");
    svg.replaceChildren();
    const fraction = finite(store.logical_retained_bytes) && store.logical_retained_bytes > 0 ? Math.min(1, store.artifact_bytes / store.logical_retained_bytes) : 0;
    svg.append(svgNode("rect", {x: 0, y: 0, width: 500, height: 12, rx: 4, fill: "var(--line)"}));
    if (fraction > 0) svg.append(svgNode("rect", {x: 0, y: 0, width: 500 * fraction, height: 12, rx: 4, fill: "var(--accent)"}));
    svg.setAttribute("aria-label", bytes(store.artifact_bytes) + " actual artifact storage versus " + bytes(store.logical_retained_bytes) + " if each retained build had separate copies");
    text("missing-artifacts", count(store.missing_artifacts));
  }

  function renderBuilds() {
    const rows = byId("builds-body");
    rows.replaceChildren();
    const builds = expandedBuilds ? snapshot.builds : snapshot.builds.slice(0, 6);
    for (const build of builds) {
      const row = document.createElement("tr");
      const identity = document.createElement("td");
      identity.append(commitLink(build.revision));
      const toolchain = document.createElement("span");
      toolchain.className = "build-toolchain";
      toolchain.textContent = leanVersion(build.toolchain);
      identity.append(toolchain);
      row.append(identity);
      for (const [value, numeric] of [[age(build.published_at), false], [count(build.module_count), true], [bytes(build.artifact_bytes), true]]) {
        const cell = document.createElement("td");
        cell.textContent = value;
        if (numeric) cell.className = "number-cell";
        if (!numeric && date(build.published_at) !== null) cell.title = new Date(build.published_at).toLocaleString();
        row.append(cell);
      }
      rows.append(row);
    }
    if (!builds.length) {
      const row = document.createElement("tr"), cell = document.createElement("td");
      cell.colSpan = 4; cell.className = "empty-cell"; cell.textContent = "No retained builds in this snapshot.";
      row.append(cell); rows.append(row);
    }
    byId("show-builds").hidden = snapshot.builds.length <= 6;
    byId("show-builds").textContent = expandedBuilds ? "Show fewer builds" : "Show all " + count(snapshot.builds.length) + " snapshots";
    const popular = byId("popular-builds");
    popular.replaceChildren();
    snapshot.popular_builds.slice(0, 6).forEach((build, i) => {
      const item = document.createElement("li"), rank = document.createElement("span"), identity = document.createElement("div"), total = document.createElement("span");
      rank.className = "popular-rank"; rank.textContent = String(i + 1).padStart(2, "0");
      identity.className = "popular-item"; identity.append(commitLink(build.revision));
      const toolchain = document.createElement("span"); toolchain.className = "build-toolchain"; toolchain.textContent = leanVersion(build.toolchain); identity.append(toolchain);
      total.className = "popular-count"; total.textContent = count(build.mapping_requests); total.title = "Mapping requests in retained history";
      item.append(rank, identity, total); popular.append(item);
    });
    if (!snapshot.popular_builds.length) { const item = document.createElement("li"); item.className = "empty-cell"; item.textContent = "No build mapping requests in retained history yet."; popular.append(item); }
  }

  function render() {
    const win = snapshot.windows[selectedWindow];
    text("delivered", bytes(win.body_bytes));
    text("bitrate", bitrate(win.average_mbps));
    text("downloads", count(win.artifact_downloads));
    text("mapping-count", count(win.mapping_downloads) + " mapping downloads");
    text("success-rate", win.requests > 0 ? decimal(win.successes / win.requests * 100, 1) + "%" : "—");
    text("request-count", count(win.requests) + " cache requests");
    const covered = Math.min(windows[selectedWindow], win.seconds);
    text("coverage-label", covered > 0 ? "Observed " + interval(covered) + " of the last " + windowLabels[selectedWindow] + (snapshot.coverage.limited ? " · retained sample" : "") : "No observed requests in this window yet");
    const latest = snapshot.latest;
    byId("latest-commit").hidden = !latest || !/^[0-9a-f]{40}$/.test(latest.revision);
    if (latest) {
      const link = byId("latest-commit");
      if (/^[0-9a-f]{40}$/.test(latest.revision)) { link.textContent = latest.revision.slice(0, 8); link.href = "https://github.com/cslib-community/complexitylib/commit/" + latest.revision; }
      text("latest-age", age(latest.published_at));
      text("latest-detail", leanVersion(latest.toolchain) + " · " + count(latest.module_count) + " modules");
    } else { text("latest-age", "No publication yet"); text("latest-detail", "The first published build will appear here."); }
    renderFreshness(); renderChart(); renderResponses(win); renderStorage(); renderBuilds();
    const gc = snapshot.gc;
    text("gc-status", {ok: "Successful", failed: "Needs attention", unknown: "Not recorded"}[gc.status] || "Not recorded");
    text("gc-last", date(gc.last_success_at) !== null ? "Last successful collection " + age(gc.last_success_at) : "No successful collection recorded in available history.");
    text("gc-artifacts", gc.deleted_artifacts === null ? "Not recorded" : count(gc.deleted_artifacts));
    text("gc-bytes", gc.deleted_bytes === null ? "Not recorded" : bytes(gc.deleted_bytes));
    text("gc-mappings", gc.deleted_mappings === null ? "Not recorded" : count(gc.deleted_mappings));
    text("record-count", count(snapshot.coverage.records));
    text("excluded-count", count(snapshot.coverage.excluded_requests));
    text("invalid-count", count(snapshot.coverage.invalid_records));
    text("publication-count", count(win.publication_successes));
  }

  async function readSnapshot(response) {
    const maxBytes = 2 * 1024 * 1024;
    if (Number(response.headers.get("content-length")) > maxBytes) throw new Error("Snapshot too large");
    const reader = response.body.getReader(), decoder = new TextDecoder();
    let size = 0, value = "";
    try {
      for (;;) {
        const chunk = await reader.read();
        if (chunk.done) break;
        size += chunk.value.byteLength;
        if (size > maxBytes) throw new Error("Snapshot too large");
        value += decoder.decode(chunk.value, {stream: true});
      }
      return JSON.parse(value + decoder.decode());
    } finally { await reader.cancel(); }
  }
  async function refresh() {
    if (loading) return;
    loading = true; byId("refresh").disabled = true;
    const controller = new AbortController(), timeout = setTimeout(() => controller.abort(), 12000);
    try {
      const response = await fetch("/stats.json", {cache: "no-store", credentials: "omit", signal: controller.signal});
      if (!response.ok) throw new Error("Snapshot unavailable");
      const data = validate(await readSnapshot(response));
      snapshot = data; fetchFailed = false; render();
    } catch (_) {
      fetchFailed = true;
      if (snapshot) renderFreshness();
      else { const notice = byId("notice"); notice.hidden = false; notice.className = "notice"; notice.textContent = "The first statistics snapshot is not available yet. Downloads can still be available; this page will try again automatically."; }
    } finally {
      clearTimeout(timeout); loading = false; byId("refresh").disabled = false;
      clearTimeout(refreshTimer);
      const seconds = snapshot && finite(snapshot.refresh_seconds) ? Math.max(60, Math.min(3600, snapshot.refresh_seconds)) : 300;
      refreshTimer = setTimeout(refresh, seconds * 1000);
    }
  }
  document.querySelectorAll("[data-window]").forEach((button) => button.addEventListener("click", () => {
    selectedWindow = button.dataset.window;
    document.querySelectorAll("[data-window]").forEach((node) => node.setAttribute("aria-pressed", String(node === button)));
    if (snapshot) render();
  }));
  document.querySelectorAll("[data-chart]").forEach((button) => button.addEventListener("click", () => {
    selectedChart = button.dataset.chart;
    document.querySelectorAll("[data-chart]").forEach((node) => node.setAttribute("aria-pressed", String(node === button)));
    if (snapshot) renderChart();
  }));
  byId("show-builds").addEventListener("click", () => { expandedBuilds = !expandedBuilds; if (snapshot) renderBuilds(); });
  byId("refresh").addEventListener("click", refresh);
  if (typeof ResizeObserver !== "undefined") new ResizeObserver(() => { if (snapshot) renderChart(); }).observe(byId("traffic-chart"));
  setInterval(() => { if (snapshot) renderFreshness(); }, 60000);
  refresh();
})();
