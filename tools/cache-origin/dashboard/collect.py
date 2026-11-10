#!/usr/bin/env python3
"""Produce a bounded public cache snapshot without serving HTTP or changing objects.

Only aggregates and already-public cache identities leave this program. Traffic
statistics cover retained journal records, not all-time accounting or unique users.
GET latency is total nginx request duration; bitrate divides successful GET body
bytes by observed wall time, including idle periods. No token, IP, request query,
raw log message, filesystem path or subprocess error is exported.
"""

from __future__ import annotations

import argparse
from array import array
from collections import Counter
from contextlib import contextmanager
from datetime import datetime, timezone
import json
import math
import os
from pathlib import Path
import re
import selectors
import stat
import subprocess
import tempfile
import time

SCOPE = "cslib-community/complexitylib"
ARTIFACT = re.compile(r"a0/" + SCOPE + r"/([0-9a-f]{16})\.art\Z")
MAPPING = re.compile(r"r0/" + SCOPE + r"/tc/([A-Za-z0-9_.+-]{1,160})/([0-9a-f]{40})\.jsonl\Z")
PUBLISH = re.compile(r"publish/[0-9a-f]{40}\Z")
ROW = re.compile(r"[0-9a-f]{16}\Z")
SUMMARY = re.compile(r"cache_gc_summary applied=true artifacts=([0-9]+) mappings=([0-9]+) bytes=([0-9]+)\Z")
HOUR, DAY, WEEK = 3600, 86400, 604800
MAX_ENTRIES = 100000
MAX_RECORDS = 250000
MAX_MAPPING_BYTES = 8 << 20
MAX_MAPPING_TOTAL = 64 << 20
MAX_OUTPUT_BYTES = 1 << 20
MAX_JOURNAL_BYTES = 96 << 20
MAX_POPULAR_KEYS = 10000
STORE_SECONDS = 5
COMMAND_SECONDS = 25


def iso(timestamp):
    return datetime.fromtimestamp(timestamp, timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z")


def parse_time(value):
    if not isinstance(value, str) or len(value) > 64:
        raise ValueError("invalid timestamp")
    parsed = datetime.fromisoformat(value.replace("Z", "+00:00"))
    if parsed.tzinfo is None:
        raise ValueError("timestamp requires a zone")
    return parsed.timestamp()


def integer(value, maximum=1 << 60):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError("invalid integer")
    if isinstance(value, str) and (not value.isascii() or not value.isdecimal() or len(value) > 20):
        raise ValueError("invalid integer")
    result = int(value)
    if not 0 <= result <= maximum:
        raise ValueError("integer out of range")
    return result


def route(uri):
    if not isinstance(uri, str) or len(uri) > 320 or not uri.startswith("/"):
        return None
    key = uri[1:]
    if ARTIFACT.fullmatch(key):
        return "artifact"
    if MAPPING.fullmatch(key):
        return "mapping"
    if PUBLISH.fullmatch(key):
        return "publication"
    return None


def parse_usage(raw, now):
    if not isinstance(raw, dict) or set(raw) != {"time", "method", "uri", "status", "bytes", "seconds"}:
        raise ValueError("unexpected record")
    timestamp = parse_time(raw["time"])
    if timestamp > now or timestamp < 0:
        raise ValueError("record outside the clock")
    method = raw["method"]
    if method not in ("GET", "HEAD", "PUT", "OTHER"):
        raise ValueError("unexpected method")
    status_code = integer(raw["status"], 599)
    if status_code < 100:
        raise ValueError("unexpected status")
    body_bytes = integer(raw["bytes"])
    if isinstance(raw["seconds"], bool) or not isinstance(raw["seconds"], (str, float, int)):
        raise ValueError("unexpected latency")
    seconds = float(raw["seconds"])
    if not math.isfinite(seconds) or not 0 <= seconds <= 86400:
        raise ValueError("unexpected latency")
    kind = route(raw["uri"])
    if kind is None or method == "OTHER" or (kind == "publication") != (method == "PUT"):
        return timestamp, None
    return timestamp, (method, kind, raw["uri"], status_code, body_bytes, seconds)


class Window:
    def __init__(self, span):
        self.span = span
        self.counts = Counter()
        self.statuses = Counter()
        self.durations = array("d")

    def add(self, record):
        method, kind, _, status_code, body_bytes, seconds = record
        self.counts["requests"] += 1
        self.statuses[str(status_code)] += 1
        self.counts["successes"] += 200 <= status_code < 300
        self.counts["misses"] += status_code == 404
        self.counts["errors"] += status_code >= 500
        self.counts["throttled"] += status_code == 429
        self.counts["auth_failures"] += status_code == 401
        self.counts["publication_successes"] += kind == "publication" and status_code == 201
        if method == "GET" and status_code in (200, 206):
            self.counts["body_bytes"] += body_bytes
            self.counts["artifact_downloads"] += kind == "artifact"
            self.counts["mapping_downloads"] += kind == "mapping"
            self.durations.append(seconds)

    def result(self, now, earliest):
        since = max(now - self.span, earliest if earliest is not None else now)
        elapsed = max(0, now - since)
        values = sorted(self.durations)
        median = None
        if values:
            middle = len(values) // 2
            median = values[middle] if len(values) % 2 else (values[middle - 1] + values[middle]) / 2
        return {"since": iso(since), "seconds": round(elapsed, 3),
                **{key: self.counts[key] for key in (
                    "requests", "artifact_downloads", "mapping_downloads", "body_bytes", "successes",
                    "misses", "errors", "throttled", "auth_failures", "publication_successes")},
                "average_mbps": round(self.counts["body_bytes"] * 8 / elapsed / 1e6, 6) if elapsed else 0,
                "median_seconds": median,
                "p95_seconds": values[math.ceil(len(values) * 0.95) - 1] if values else None,
                "status_counts": dict(sorted(self.statuses.items()))}


class Traffic:
    def __init__(self, now):
        self.now = now
        self.windows = {"hour": Window(HOUR), "day": Window(DAY), "week": Window(WEEK)}
        self.earliest = self.latest = None
        self.records = self.invalid = self.excluded = 0
        self.limited = False
        self.hours = {}
        self.mapping_requests = Counter()

    def add(self, raw):
        if self.records >= MAX_RECORDS:
            self.limited = True
            return
        self.records += 1
        try:
            timestamp, record = parse_usage(raw, self.now)
        except (ValueError, TypeError, OverflowError):
            self.invalid += 1
            return
        if timestamp < self.now - WEEK:
            return
        # Include non-cache events when determining observed journal coverage;
        # dashboard polling itself never increases cache request/byte totals.
        self.earliest = timestamp if self.earliest is None else min(timestamp, self.earliest)
        self.latest = timestamp if self.latest is None else max(timestamp, self.latest)
        if record is None:
            self.excluded += 1
            return
        for window in self.windows.values():
            if timestamp >= self.now - window.span:
                window.add(record)
        method, kind, uri, status_code, body_bytes, _ = record
        hour = int(timestamp // HOUR) * HOUR
        bucket = self.hours.setdefault(hour, Counter())
        bucket["requests"] += 1
        if method == "GET" and status_code in (200, 206):
            bucket["downloads"] += kind == "artifact"
            bucket["body_bytes"] += body_bytes
            if kind == "mapping":
                if uri in self.mapping_requests or len(self.mapping_requests) < MAX_POPULAR_KEYS:
                    self.mapping_requests[uri] += 1
                else:
                    self.limited = True

    def journal_line(self, line):
        try:
            journal = json.loads(line)
            message = journal.get("MESSAGE")
            if not isinstance(message, str):
                raise ValueError("not a usage message")
            self.add(json.loads(message))
        except (ValueError, TypeError, AttributeError):
            self.invalid += 1

    def result(self):
        since = self.earliest
        series = []
        if since is not None:
            for hour in range(int(since // HOUR) * HOUR, int(self.now // HOUR) * HOUR + 1, HOUR):
                bucket = self.hours.get(hour, Counter())
                elapsed = max(0, min(hour + HOUR, self.now) - max(hour, since))
                series.append({"time": iso(hour), "requests": bucket["requests"],
                               "downloads": bucket["downloads"], "body_bytes": bucket["body_bytes"],
                               "average_mbps": round(bucket["body_bytes"] * 8 / elapsed / 1e6, 6) if elapsed else 0})
        popular = []
        for uri, count in self.mapping_requests.most_common(10):
            match = MAPPING.fullmatch(uri[1:])
            popular.append({"revision": match[2], "toolchain": match[1], "mapping_requests": count})
        return {"coverage": {"since": iso(since) if since is not None else None,
                             "until": iso(self.latest) if self.latest is not None else None,
                             "records": self.records, "invalid_records": self.invalid,
                             "excluded_requests": self.excluded, "limited": self.limited},
                "windows": {name: window.result(self.now, since) for name, window in self.windows.items()},
                "series": series, "popular_builds": popular}


class SnapshotUnavailable(Exception):
    pass


def safe_directory(path, owner=None):
    info = path.lstat()
    if not stat.S_ISDIR(info.st_mode) or info.st_mode & 0o022 or owner is not None and info.st_uid != owner:
        raise SnapshotUnavailable("unsafe directory")
    return info


@contextmanager
def store_lock(root):
    import fcntl
    owner = safe_directory(root).st_uid
    safe_directory(root / "state", owner)
    path = root / "state/lock"
    descriptor = os.open(path, os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        current = path.lstat()
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != owner or stat.S_IMODE(info.st_mode) != 0o600
                or info.st_nlink != 1 or (info.st_dev, info.st_ino) != (current.st_dev, current.st_ino)):
            raise SnapshotUnavailable("unsafe lock")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise SnapshotUnavailable("store busy") from error
        yield owner
    finally:
        os.close(descriptor)


def storage_snapshot(root, now, mapping_requests):
    """Read a snapshot under the existing lock, never create it or block a writer."""
    deadline = time.monotonic() + STORE_SECONDS
    with store_lock(root) as owner:
        public = root / "public"
        safe_directory(public, owner)
        artifacts = {}
        mappings = []
        count = 1
        queue = [public]
        while queue:
            directory = queue.pop()
            with os.scandir(directory) as entries:
                for entry in entries:
                    count += 1
                    if count > MAX_ENTRIES or time.monotonic() > deadline:
                        raise SnapshotUnavailable("scan limit")
                    info = entry.stat(follow_symlinks=False)
                    if info.st_uid != owner or info.st_mode & 0o022:
                        raise SnapshotUnavailable("unsafe entry")
                    path = Path(entry.path)
                    if stat.S_ISDIR(info.st_mode):
                        queue.append(path)
                        continue
                    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                        raise SnapshotUnavailable("unexpected entry")
                    key = path.relative_to(public).as_posix()
                    if match := ARTIFACT.fullmatch(key):
                        artifacts[match[1]] = info.st_size
                    elif match := MAPPING.fullmatch(key):
                        if info.st_size > MAX_MAPPING_BYTES or info.st_mtime > now:
                            raise SnapshotUnavailable("invalid mapping")
                        mappings.append((path, info.st_size, info.st_mtime, match[1], match[2]))
                    else:
                        raise SnapshotUnavailable("unexpected entry")
        if sum(item[1] for item in mappings) > MAX_MAPPING_TOTAL:
            raise SnapshotUnavailable("mapping scan limit")
        builds, logical, missing = [], 0, 0
        for path, size, modified, toolchain, revision in mappings:
            if time.monotonic() > deadline:
                raise SnapshotUnavailable("scan deadline")
            refs, inputs, modules = set(), set(), 0
            with path.open("rb") as stream:
                if stream.readline(4097) != b'"2026-03-17"\n':
                    raise SnapshotUnavailable("unsupported mapping")
                total = stream.tell()
                while line := stream.readline(4097):
                    total += len(line)
                    if total > size or len(line) > 4096 or modules >= MAX_ENTRIES:
                        raise SnapshotUnavailable("mapping limit")
                    row = json.loads(line)
                    if (not isinstance(row, list) or len(row) != 2 or not all(isinstance(x, str) for x in row)
                            or not ROW.fullmatch(row[0]) or row[0] in inputs
                            or not re.fullmatch(r"[0-9a-f]{16}\.ltar", row[1])):
                        raise SnapshotUnavailable("invalid mapping row")
                    modules += 1
                    inputs.add(row[0])
                    refs.add(row[1][:16])
                    if modules % 128 == 0 and time.monotonic() > deadline:
                        raise SnapshotUnavailable("scan deadline")
            if not refs or total != size:
                raise SnapshotUnavailable("invalid mapping size")
            referenced_bytes = sum(artifacts.get(ref, 0) for ref in refs)
            missing += sum(ref not in artifacts for ref in refs)
            logical += referenced_bytes
            builds.append({"revision": revision, "toolchain": toolchain, "published_at": iso(modified),
                           "module_count": modules, "artifact_count": len(refs), "artifact_bytes": referenced_bytes,
                           "mapping_requests": mapping_requests.get("/" + path.relative_to(public).as_posix(), 0)})
        usage = os.statvfs(root)
        total_bytes, free_bytes = usage.f_blocks * usage.f_frsize, usage.f_bfree * usage.f_frsize
        artifact_bytes = sum(artifacts.values())
        builds.sort(key=lambda build: (build["published_at"], build["revision"]), reverse=True)
        storage = {"snapshot_at": iso(now), "stale": False, "entry_count": count,
                   "artifact_count": len(artifacts), "mapping_count": len(mappings), "artifact_bytes": artifact_bytes,
                   "mapping_bytes": sum(item[1] for item in mappings), "logical_retained_bytes": logical,
                   "saved_bytes": max(0, logical - artifact_bytes),
                   "dedup_ratio": logical / artifact_bytes if artifact_bytes else None, "missing_artifacts": missing,
                   "disk": {"total_bytes": total_bytes, "used_bytes": total_bytes - free_bytes,
                            "available_bytes": usage.f_bavail * usage.f_frsize,
                            "inodes_total": usage.f_files, "inodes_available": usage.f_favail}}
        return {"storage": storage, "latest": builds[0] if builds else None, "builds": builds[:20]}


def unavailable_storage(previous):
    if isinstance(previous, dict) and isinstance(previous.get("storage"), dict):
        result = {key: previous.get(key) for key in ("storage", "latest", "builds")}
        result["storage"] = {**result["storage"], "stale": True}
        return result
    fields = ("entry_count", "artifact_count", "mapping_count", "artifact_bytes", "mapping_bytes",
              "logical_retained_bytes", "saved_bytes", "dedup_ratio", "missing_artifacts")
    return {"storage": {"snapshot_at": None, "stale": True, **dict.fromkeys(fields),
                        "disk": dict.fromkeys(("total_bytes", "used_bytes", "available_bytes", "inodes_total", "inodes_available"))},
            "latest": None, "builds": []}


def stream_command(command, consume, *, max_records=MAX_RECORDS, max_bytes=MAX_JOURNAL_BYTES):
    """Bound line size, total bytes, records and elapsed time; reap our process."""
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                               env={**os.environ, "LC_ALL": "C", "TZ": "UTC"})
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    pending, records, consumed, complete = b"", 0, 0, False
    deadline = time.monotonic() + COMMAND_SECONDS
    try:
        while time.monotonic() < deadline:
            if not selector.select(min(1, max(0, deadline - time.monotonic()))):
                continue
            block = os.read(process.stdout.fileno(), 65536)
            if not block:
                complete = not pending and process.wait(timeout=1) == 0
                break
            consumed += len(block)
            if consumed > max_bytes:
                break
            pending += block
            while b"\n" in pending:
                line, pending = pending.split(b"\n", 1)
                if len(line) > 16384 or records >= max_records:
                    return False
                records += 1
                consume(line)
            if len(pending) > 16384:
                break
        return complete
    finally:
        selector.close()
        process.stdout.close()
        if process.poll() is None:
            process.terminate()
            try:
                process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait(timeout=2)


def gc_snapshot(now, previous=None):
    result = {"status": "unknown", "last_run_at": None, "last_success_at": None,
              "deleted_artifacts": None, "deleted_mappings": None, "deleted_bytes": None}
    if isinstance(previous, dict) and isinstance(previous.get("gc"), dict):
        result.update({key: previous["gc"].get(key) for key in result if key != "status"})
    latest = None

    def consume(line):
        nonlocal latest
        try:
            record = json.loads(line)
            timestamp = integer(record["__REALTIME_TIMESTAMP"]) / 1e6
            if not now - WEEK <= timestamp <= now or latest is not None and timestamp <= latest:
                return
            message = record["MESSAGE"]
            if not isinstance(message, str):
                return
            tail = message[message.find("cache_gc_summary "):] if "cache_gc_summary " in message else ""
            if match := SUMMARY.fullmatch(tail):
                artifacts, mappings, body_bytes = (integer(value, 1 << 60) for value in match.groups())
            else:
                report = json.loads(message)
                if not isinstance(report, dict) or report.get("applied") is not True:
                    return
                arts, maps = report.get("delete_artifacts"), report.get("expired_mappings")
                if not isinstance(arts, (list, type(None))) or not isinstance(maps, (list, type(None))):
                    return
                artifacts, mappings = len(arts or []), len(maps or [])
                body_bytes = integer(report["deleted_bytes"]) if "deleted_bytes" in report else None
            latest = timestamp
            result.update(last_success_at=iso(timestamp), deleted_artifacts=artifacts,
                          deleted_mappings=mappings, deleted_bytes=body_bytes)
        except (ValueError, KeyError, TypeError, OverflowError):
            return

    try:
        query = ["journalctl", "--unit=cache-origin-gc.service", "--since", "@" + str(int(now - WEEK)),
                 "--reverse", "--no-pager", "--output=json", "--output-fields=MESSAGE,__REALTIME_TIMESTAMP"]
        # Filter before streaming: an enormous legacy report must not hide its
        # preceding compact summary when reading the journal in reverse order.
        stream_command([*query, "--grep=cache_gc_summary "], consume, max_records=5000, max_bytes=8 << 20)
        if latest is None:
            stream_command(query, consume, max_records=5000, max_bytes=8 << 20)
        shown = subprocess.run(["systemctl", "show", "cache-origin-gc.service", "--property=Result",
                                "--property=ExecMainStatus", "--property=ExecMainExitTimestamp"],
                               env={**os.environ, "LC_ALL": "C", "TZ": "UTC"}, capture_output=True,
                               text=True, timeout=5, check=True)
        properties = dict(line.split("=", 1) for line in shown.stdout.splitlines() if "=" in line)
        stamp = properties.get("ExecMainExitTimestamp", "")
        if stamp:
            timestamp = datetime.strptime(stamp, "%a %Y-%m-%d %H:%M:%S %Z").replace(tzinfo=timezone.utc).timestamp()
            if timestamp <= now:
                result["last_run_at"] = iso(timestamp)
                result["status"] = "ok" if properties.get("Result") == "success" and properties.get("ExecMainStatus") == "0" else "failed"
                if result["status"] == "ok" and latest is None:
                    result["last_success_at"] = iso(timestamp)
                    # The service exit establishes success but cannot supply
                    # deletion counts. Never relabel old counts as a new run.
                    result.update(deleted_artifacts=None, deleted_mappings=None, deleted_bytes=None)
    except (OSError, ValueError, subprocess.SubprocessError):
        pass
    return result


def safe_output(path):
    parent = safe_directory(path.parent, os.geteuid())
    if parent.st_mode & 0o022:
        raise ValueError("unsafe output directory")
    if path.exists() or path.is_symlink():
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_uid != os.geteuid() or info.st_mode & 0o022 or info.st_nlink != 1:
            raise ValueError("unsafe output file")


def read_previous(path):
    safe_output(path)
    try:
        with path.open("rb") as stream:
            raw = stream.read(MAX_OUTPUT_BYTES + 1)
        if len(raw) <= MAX_OUTPUT_BYTES:
            previous = json.loads(raw)
            if isinstance(previous, dict) and previous.get("schema") == 1:
                return previous
    except (FileNotFoundError, ValueError):
        pass
    return None


def write_snapshot(path, snapshot):
    safe_output(path)
    raw = json.dumps(snapshot, separators=(",", ":"), allow_nan=False).encode() + b"\n"
    if len(raw) > MAX_OUTPUT_BYTES:
        raise ValueError("public snapshot exceeds bound")
    descriptor, temporary = tempfile.mkstemp(prefix=".stats-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as output:
            os.fchmod(output.fileno(), 0o644)
            output.write(raw)
            output.flush()
            os.fsync(output.fileno())
        os.replace(temporary, path)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.lexists(temporary):
            os.unlink(temporary)


def collect(root, output, *, now=None):
    now = time.time() if now is None else now
    previous = read_previous(output)
    traffic = Traffic(now)
    try:
        complete = stream_command(["journalctl", "--namespace=cache-origin-usage", "--identifier=cache_usage",
                                   "--since", "@" + str(int(now - WEEK)), "--reverse", "--no-pager",
                                   "--output=json", "--output-fields=MESSAGE,__REALTIME_TIMESTAMP"], traffic.journal_line)
        traffic.limited = traffic.limited or not complete
    except (OSError, subprocess.SubprocessError):
        traffic.limited = True
    snapshot = {"schema": 1, "generated_at": iso(now), "refresh_seconds": 300, **traffic.result()}
    try:
        snapshot.update(storage_snapshot(root, now, traffic.mapping_requests))
    except (OSError, ValueError, SnapshotUnavailable):
        snapshot.update(unavailable_storage(previous))
    snapshot["gc"] = gc_snapshot(now, previous)
    write_snapshot(output, snapshot)
    return snapshot


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("/srv/cache-origin"))
    parser.add_argument("--output", type=Path, default=Path("/var/lib/cache-dashboard/stats.json"))
    args = parser.parse_args()
    try:
        collect(args.root, args.output)
    except (OSError, ValueError, SnapshotUnavailable, subprocess.SubprocessError):
        parser.exit(1, "Cache statistics unavailable; inspect collector permissions and local services\n")


if __name__ == "__main__":
    main()
