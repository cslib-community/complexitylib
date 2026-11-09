"""Dashboard collectors: measured traffic, privacy and non-mutating snapshots."""

from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


REPO = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("cache_dashboard", REPO / "tools/cache-origin/dashboard/collect.py")
collector = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(collector)
NOW = datetime(2026, 11, 7, 12, tzinfo=timezone.utc).timestamp()
ART = "/a0/" + collector.SCOPE + "/0000000000000001.art"
MAP = "/r0/" + collector.SCOPE + "/tc/lean-toolchain/" + "a" * 40 + ".jsonl"


def usage(offset=0, method="GET", uri=ART, status=200, body_bytes=1000, seconds=0.1):
    return {"time": collector.iso(NOW - offset), "method": method, "uri": uri,
            "status": str(status), "bytes": str(body_bytes), "seconds": str(seconds)}


class TrafficTests(unittest.TestCase):
    def test_bitrate_uses_observed_wall_time_and_successful_get_bytes(self):
        traffic = collector.Traffic(NOW)
        traffic.add(usage(100, body_bytes=1_000_000, seconds=2))
        traffic.add(usage(50, uri=MAP, body_bytes=500_000, seconds=1))
        traffic.add(usage(10, method="HEAD", body_bytes=999_999))
        traffic.add(usage(5, method="PUT", uri="/publish/" + "a" * 40, status=201, body_bytes=10000))
        window = traffic.result()["windows"]["hour"]
        self.assertEqual(window["body_bytes"], 1_500_000)
        self.assertEqual(window["seconds"], 100)
        self.assertEqual(window["average_mbps"], 0.12)
        self.assertEqual(window["artifact_downloads"], 1)
        self.assertEqual(window["mapping_downloads"], 1)
        self.assertEqual(window["publication_successes"], 1)
        self.assertEqual(window["median_seconds"], 1.5)
        self.assertEqual(window["p95_seconds"], 2)

    def test_windows_include_idle_time_but_exclude_older_records(self):
        traffic = collector.Traffic(NOW)
        traffic.add(usage(2 * collector.DAY, body_bytes=200))
        traffic.add(usage(2 * collector.HOUR, body_bytes=300))
        traffic.add(usage(30, body_bytes=400))
        result = traffic.result()
        self.assertEqual(result["windows"]["hour"]["body_bytes"], 400)
        self.assertEqual(result["windows"]["hour"]["seconds"], collector.HOUR)
        self.assertEqual(result["windows"]["day"]["body_bytes"], 700)
        self.assertEqual(result["windows"]["week"]["seconds"], 2 * collector.DAY)
        self.assertTrue(any(row["requests"] == 0 for row in result["series"]))

    def test_status_and_mapping_rankings_are_distinct_from_people_or_builds(self):
        traffic = collector.Traffic(NOW)
        for status in (200, 200, 404, 429, 500, 503, 401):
            traffic.add(usage(100, uri=MAP, status=status))
        result = traffic.result()
        day = result["windows"]["day"]
        self.assertEqual((day["requests"], day["successes"], day["misses"], day["errors"], day["throttled"], day["auth_failures"]), (7, 2, 1, 2, 1, 1))
        self.assertEqual(result["popular_builds"], [{"revision": "a" * 40, "toolchain": "lean-toolchain", "mapping_requests": 2}])

    def test_dashboard_requests_and_raw_private_fields_never_reach_public_json(self):
        traffic = collector.Traffic(NOW)
        for path in ("/", "/stats.json", "/other", ART + "?password=secret", "/private/secret"):
            traffic.add(usage(200, uri=path))
        bad = usage(100)
        bad["Authorization"] = "secret"
        traffic.add(bad)
        result = traffic.result()
        self.assertEqual(result["windows"]["day"]["requests"], 0)
        self.assertEqual(result["coverage"]["excluded_requests"], 5)
        self.assertEqual(result["coverage"]["invalid_records"], 1)
        serialized = json.dumps(result)
        for secret in ("Authorization", "secret", "password", "/private", "/stats.json"):
            self.assertNotIn(secret, serialized)

    def test_malformed_future_and_nonfinite_records_are_rejected(self):
        records = [usage(-10), usage(seconds="nan"), usage(seconds="inf"), usage(seconds=-1),
                   usage(body_bytes=-1), usage(status=99), usage(status=600), usage()]
        records[-1]["time"] = "2026-11-07T12:00:00"
        traffic = collector.Traffic(NOW)
        for record in records:
            traffic.add(record)
        self.assertEqual(traffic.result()["coverage"]["invalid_records"], len(records))

    def test_empty_and_capped_data_are_explicit(self):
        traffic = collector.Traffic(NOW)
        self.assertIsNone(traffic.result()["coverage"]["since"])
        self.assertIsNone(traffic.result()["windows"]["day"]["median_seconds"])
        with patch.object(collector, "MAX_RECORDS", 1):
            traffic.add(usage(20))
            traffic.add(usage(10))
        self.assertTrue(traffic.result()["coverage"]["limited"])
        self.assertEqual(traffic.result()["coverage"]["records"], 1)


@unittest.skipUnless(sys.platform == "linux", "collector targets the Linux cache server")
class StoreTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cache-dashboard-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.root.chmod(0o700)
        for name in ("public", "state", "output"):
            (self.root / name).mkdir(mode=0o700)
        self.lock = self.root / "state/lock"
        self.lock.write_bytes(b"")
        self.lock.chmod(0o600)
        self.old_inode = self.lock.stat().st_ino

    def artifact(self, number, data):
        path = self.root / f"public/a0/{collector.SCOPE}/{number:016x}.art"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        path.chmod(0o444)

    def mapping(self, revision, references, offset=0):
        path = self.root / f"public/r0/{collector.SCOPE}/tc/lean-toolchain/{revision}.jsonl"
        path.parent.mkdir(parents=True, exist_ok=True)
        data = '"2026-03-17"\n' + "".join(json.dumps([f"{n:016x}", f"{ref:016x}.ltar"]) + "\n" for n, ref in enumerate(references))
        path.write_text(data)
        path.chmod(0o444)
        os.utime(path, (NOW - offset, NOW - offset))
        return path

    def test_shared_outputs_latest_build_and_missing_artifacts(self):
        self.artifact(1, b"one")
        self.artifact(2, b"second")
        self.mapping("a" * 40, [1], 100)
        self.mapping("b" * 40, [1, 2, 3])
        snapshot = collector.storage_snapshot(self.root, NOW, {MAP: 7})
        storage = snapshot["storage"]
        self.assertEqual((storage["artifact_count"], storage["mapping_count"]), (2, 2))
        self.assertEqual(storage["artifact_bytes"], 9)
        self.assertEqual(storage["logical_retained_bytes"], 12)
        self.assertEqual(storage["saved_bytes"], 3)
        self.assertAlmostEqual(storage["dedup_ratio"], 12 / 9)
        self.assertEqual(storage["missing_artifacts"], 1)
        self.assertEqual(snapshot["latest"]["revision"], "b" * 40)
        self.assertEqual(snapshot["latest"]["module_count"], 3)
        self.assertEqual(snapshot["builds"][1]["mapping_requests"], 7)
        self.assertEqual(self.lock.stat().st_ino, self.old_inode)

    def test_busy_lock_is_nonblocking_and_previous_snapshot_remains_stale(self):
        import fcntl
        with self.lock.open("rb") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaises(collector.SnapshotUnavailable):
                collector.storage_snapshot(self.root, NOW, {})
        previous = {"storage": {"snapshot_at": collector.iso(NOW - 100), "artifact_count": 8, "stale": False},
                    "latest": {"revision": "a" * 40}, "builds": []}
        stale = collector.unavailable_storage(previous)
        self.assertTrue(stale["storage"]["stale"])
        self.assertEqual(stale["storage"]["artifact_count"], 8)
        self.assertFalse(previous["storage"]["stale"])

    def test_unknown_entries_symlinks_and_bad_lock_fail_closed(self):
        bad = self.root / "public/unknown"
        bad.write_text("private path must not leak")
        with self.assertRaises(collector.SnapshotUnavailable):
            collector.storage_snapshot(self.root, NOW, {})
        bad.unlink()
        bad.symlink_to(self.root / "state/lock")
        with self.assertRaises(collector.SnapshotUnavailable):
            collector.storage_snapshot(self.root, NOW, {})
        bad.unlink()
        self.lock.chmod(0o666)
        with self.assertRaises(collector.SnapshotUnavailable):
            collector.storage_snapshot(self.root, NOW, {})

    def test_entry_and_mapping_limits_preserve_source_contents(self):
        self.artifact(1, b"one")
        path = self.mapping("a" * 40, [1])
        before = path.read_bytes()
        with patch.object(collector, "MAX_ENTRIES", 2), self.assertRaises(collector.SnapshotUnavailable):
            collector.storage_snapshot(self.root, NOW, {})
        self.assertEqual(path.read_bytes(), before)
        with patch.object(collector, "MAX_MAPPING_TOTAL", 1), self.assertRaises(collector.SnapshotUnavailable):
            collector.storage_snapshot(self.root, NOW, {})
        self.assertEqual(self.lock.stat().st_ino, self.old_inode)

    def test_output_is_atomic_private_parent_and_public_file_only(self):
        output = self.root / "output/stats.json"
        collector.write_snapshot(output, {"schema": 1, "message": "safe"})
        self.assertEqual(stat.S_IMODE(output.stat().st_mode), 0o644)
        self.assertEqual(collector.read_previous(output), {"schema": 1, "message": "safe"})
        self.assertEqual(list(output.parent.glob(".stats-*")), [])
        before = output.read_bytes()
        with patch.object(collector, "MAX_OUTPUT_BYTES", 4), self.assertRaises(ValueError):
            collector.write_snapshot(output, {"unsafe": "oversized output"})
        self.assertEqual(output.read_bytes(), before)
        output.unlink()
        output.symlink_to(self.lock)
        with self.assertRaises(ValueError):
            collector.write_snapshot(output, {"schema": 1})
        self.assertEqual(self.lock.read_bytes(), b"")


class CommandAndGCTests(unittest.TestCase):
    @unittest.skipUnless(sys.platform == "linux", "uses selectable Linux pipes")
    def test_streamed_command_is_bounded_and_reaped(self):
        rows = []
        self.assertTrue(collector.stream_command([sys.executable, "-c", "print('one');print('two')"], rows.append))
        self.assertEqual(rows, [b"one", b"two"])
        self.assertFalse(collector.stream_command([sys.executable, "-c", "print('one');print('two')"], rows.append, max_records=1))
        with patch.object(collector, "COMMAND_SECONDS", 0.1):
            self.assertFalse(collector.stream_command([sys.executable, "-c", "import time;time.sleep(10)"], rows.append))

    def gc(self, messages, status="success", exit_status="0"):
        def stream(command, consume, **options):
            for offset, text in messages:
                consume(json.dumps({"MESSAGE": text, "__REALTIME_TIMESTAMP": str(int((NOW - offset) * 1e6))}).encode())
            return True
        shown = "Result=" + status + "\nExecMainStatus=" + exit_status + "\nExecMainExitTimestamp=Sat 2026-11-07 11:59:00 UTC\n"
        with patch.object(collector, "stream_command", side_effect=stream), patch.object(collector.subprocess, "run", return_value=SimpleNamespace(stdout=shown)):
            return collector.gc_snapshot(NOW)

    def test_gc_compact_summary_counts_not_raw_paths(self):
        result = self.gc([(100, "2026/11/07 cache_gc_summary applied=true artifacts=4 mappings=2 bytes=123456")])
        self.assertEqual(result["status"], "ok")
        self.assertEqual((result["deleted_artifacts"], result["deleted_mappings"], result["deleted_bytes"]), (4, 2, 123456))
        self.assertNotIn("path", json.dumps(result))
        self.assertEqual(result["last_success_at"], collector.iso(NOW - 100))

    def test_gc_filters_large_reports_before_streaming_summaries(self):
        commands = []

        def stream(command, consume, **options):
            commands.append(command)
            self.assertIn("--grep=cache_gc_summary ", command)
            consume(json.dumps({"MESSAGE": "cache_gc_summary applied=true artifacts=20000 mappings=3 bytes=999",
                                "__REALTIME_TIMESTAMP": str(int((NOW - 100) * 1e6))}).encode())
            return True

        with patch.object(collector, "stream_command", side_effect=stream), patch.object(
                collector.subprocess, "run", return_value=SimpleNamespace(stdout="")):
            result = collector.gc_snapshot(NOW)
        self.assertEqual(len(commands), 1)
        self.assertEqual(result["deleted_artifacts"], 20000)

    def test_new_success_without_summary_does_not_relabel_old_counts(self):
        previous = {"gc": {"last_success_at": collector.iso(NOW - collector.DAY),
                           "deleted_artifacts": 99, "deleted_mappings": 2, "deleted_bytes": 123}}
        shown = "Result=success\nExecMainStatus=0\nExecMainExitTimestamp=Sat 2026-11-07 11:59:00 UTC\n"
        with patch.object(collector, "stream_command", return_value=True), patch.object(
                collector.subprocess, "run", return_value=SimpleNamespace(stdout=shown)):
            result = collector.gc_snapshot(NOW, previous)
        self.assertEqual(result["last_success_at"], collector.iso(NOW - 60))
        self.assertIsNone(result["deleted_artifacts"])
        self.assertIsNone(result["deleted_mappings"])
        self.assertIsNone(result["deleted_bytes"])

    def test_gc_legacy_report_has_unknown_bytes_and_failed_unit_stays_failed(self):
        legacy = json.dumps({"applied": True, "delete_artifacts": ["private/one"], "expired_mappings": None})
        result = self.gc([(100, legacy)], status="exit-code", exit_status="1")
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["deleted_artifacts"], 1)
        self.assertIsNone(result["deleted_bytes"])
        self.assertEqual(result["last_success_at"], collector.iso(NOW - 100))
        self.assertNotIn("private", json.dumps(result))


if __name__ == "__main__":
    unittest.main()
