"""Exercise shared local/CI cache restoration with HTTP mirrors and a recording Lake client."""

import hashlib
import http.server
import json
import os
from pathlib import Path
import shutil
import ssl
import subprocess
import tempfile
import threading
import time
import unittest

REPO = Path(__file__).resolve().parent.parent
SCOPE = "cslib-community/complexitylib"
TOOLCHAIN = "leanprover--lean4---v4.36.0-rc1"
FAKE_LAKE = r'''#!/usr/bin/env python3
import hashlib, json, os, pathlib, subprocess, sys, time
args = sys.argv[1:]
event = {"args": args, "cwd": os.getcwd(),
         "artifact_endpoint": os.environ.get("LAKE_CACHE_ARTIFACT_ENDPOINT"),
         "revision_endpoint": os.environ.get("LAKE_CACHE_REVISION_ENDPOINT"),
         "curl_home": os.environ.get("CURL_HOME")}
if event["curl_home"]:
    event["curl_config"] = (pathlib.Path(event["curl_home"]) / ".curlrc").read_text()
if args[:3] != ["cache", "get", "--repo=cslib-community/complexitylib"]:
    event["kind"] = "mathlib"
    with open(os.environ["RESTORE_LOG"], "a") as log:
        log.write(json.dumps(event) + "\n")
    raise SystemExit(0)
lines = pathlib.Path(args[3]).read_text().splitlines()
entries = [json.loads(line) for line in lines[1:]]
event.update({"kind": "artifacts", "inputs": [entry[0] for entry in entries]})
with open(os.environ["RESTORE_LOG"], "a") as log:
    log.write(json.dumps(event) + "\n")
if event["artifact_endpoint"] == os.environ.get("RESTORE_HANG_ENDPOINT"):
    pathlib.Path(os.environ["RESTORE_PID"]).write_text(str(os.getpid()))
    time.sleep(60)
cache = pathlib.Path(os.environ["LAKE_CACHE_DIR"])
cache.mkdir(parents=True, exist_ok=True)
failed = False
for _, outputs in entries:
    for name in outputs:
        path = cache / name
        if path.exists():
            continue
        try:
            result = subprocess.run([
                os.environ.get("CURL", "curl"), "--silent", "--show-error", "--location", "--fail",
                event["artifact_endpoint"] + "/cslib-community/complexitylib/" + name,
            ], capture_output=True, timeout=2)
            if result.returncode != 0:
                raise RuntimeError(result.stderr.decode(errors="replace"))
            data = result.stdout
            # Model Lake's content check and persistence: failures never become completed files.
            if hashlib.sha256(data).hexdigest() != name.split(".")[0]:
                failed = True
            else:
                path.write_bytes(data)
        except Exception:
            failed = True
raise SystemExit(1 if failed else 0)
'''


@unittest.skipUnless(shutil.which("git") and shutil.which("curl"), "git and curl are required")
class CacheRestoreTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="cache restore ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name).resolve()
        self.root = self.temp / "checkout"
        self.root.mkdir()
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "COMPLEXITYLIB_CACHE_", "LAKE_CACHE_", "RESTORE_"))}
        self.env.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                         "GIT_AUTHOR_NAME": "Cache fixture", "GIT_COMMITTER_NAME": "Cache fixture",
                         "GIT_AUTHOR_EMAIL": "cache@example.invalid", "GIT_COMMITTER_EMAIL": "cache@example.invalid",
                         "RESTORE_LOG": str(self.temp / "events.jsonl"),
                         "LAKE_CACHE_DIR": str(self.temp / "artifacts"),
                         "RESTORE_PID": str(self.temp / "lake.pid"),
                         "NO_PROXY": "127.0.0.1", "no_proxy": "127.0.0.1"})
        self.real_path = self.env["PATH"]
        for name in ("restore.py", "get_mathlib.py", "get.sh", "get-missing.sh"):
            target = self.root / "scripts/cache" / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(REPO / "scripts/cache" / name, target)
        self.git("init", "-q")
        self.write("lean-toolchain", "leanprover/lean4:v4.36.0-rc1\n")
        self.git("add", "lean-toolchain")
        self.git("commit", "-qm", "first")
        self.ancestor = self.git("rev-parse", "HEAD")
        self.git("commit", "--allow-empty", "-qm", "second")
        self.head = self.git("rev-parse", "HEAD")
        self.bin_dir = self.temp / "bin"
        self.bin_dir.mkdir()
        lake = self.bin_dir / "lake"
        lake.write_text(FAKE_LAKE)
        lake.chmod(0o755)
        self.env["PATH"] = str(self.bin_dir) + os.pathsep + self.env["PATH"]
        self.routes = {}
        self.redirects = {}
        self.requests = []
        owner = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                owner.requests.append(self.path)
                if self.path in owner.redirects:
                    self.send_response(302)
                    self.send_header("Location", owner.redirects[self.path])
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
                status, body, delay = owner.routes.get(self.path, (404, b"", 0))
                if delay:
                    time.sleep(delay)
                try:
                    self.send_response(status)
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                except (BrokenPipeError, ConnectionResetError):
                    pass

            def log_message(self, *args):
                pass

        self.handler = Handler
        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), self.handler)
        self.server.daemon_threads = True
        thread = threading.Thread(target=self.server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        self.base = f"http://127.0.0.1:{self.server.server_port}"
        self.primary = self.base + "/primary"
        self.secondary = self.base + "/secondary"
        self.config([self.primary, self.secondary])
        self.artifacts = [hashlib.sha256(value).hexdigest() + ".art" for value in (b"first", b"second")]
        self.entries = [("1" * 16, [self.artifacts[0]]), ("2" * 16, [self.artifacts[1]])]

    def start_https_server(self):
        openssl = shutil.which("openssl")
        if openssl is None:
            self.skipTest("OpenSSL is required for redirect-policy integration tests")
        tls = self.temp / "tls"
        tls.mkdir()
        key, certificate = tls / "key.pem", tls / "certificate.pem"
        result = subprocess.run([
            openssl, "req", "-x509", "-newkey", "rsa:2048", "-sha256", "-nodes",
            "-days", "1", "-subj", "/CN=127.0.0.1", "-addext",
            "subjectAltName=IP:127.0.0.1", "-keyout", str(key), "-out", str(certificate),
        ], capture_output=True, text=True)
        if result.returncode != 0:
            self.skipTest("OpenSSL cannot create a local test certificate: " + result.stderr)
        server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), self.handler)
        context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        context.load_cert_chain(certificate, key)
        server.socket = context.wrap_socket(server.socket, server_side=True)
        server.daemon_threads = True
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        return f"https://127.0.0.1:{server.server_port}", certificate

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, env=self.env, text=True).strip()

    def config(self, urls):
        return self.write("scripts/cache/endpoints.json", json.dumps({"version": 1, "read": urls}))

    def mapping_path(self, mirror, revision):
        return f"/{mirror}/r0/{SCOPE}/tc/{TOOLCHAIN}/{revision}.jsonl"

    def mapping(self, mirror, revision, entries=None):
        body = ('"2026-03-17"\n' + "\n".join(json.dumps(entry) for entry in
                (self.entries if entries is None else entries)) + "\n").encode()
        self.routes[self.mapping_path(mirror, revision)] = (200, body, 0)

    def artifact(self, mirror, index, body=None):
        body = (b"first", b"second")[index] if body is None else body
        self.routes[f"/{mirror}/a0/{SCOPE}/{self.artifacts[index]}"] = (200, body, 0)

    def events(self):
        path = Path(self.env["RESTORE_LOG"])
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def run_restore(self, *args, script="restore.py", **env):
        target = self.root / "scripts/cache" / script
        command = ["python3", str(target)] if script.endswith(".py") else [str(target)]
        result = subprocess.run([*command, *args], cwd=self.temp,
                                env={**self.env, **env, "COMPLEXITYLIB_CACHE_CHECKOUT": str(self.root)},
                                capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def test_nearest_revision_across_mirrors_precedes_endpoint_priority(self):
        self.mapping("primary", self.ancestor, [self.entries[0]])
        self.mapping("secondary", self.head)
        for i in range(2):
            self.artifact("secondary", i)
        result = self.run_restore()
        self.assertIn(f"Remote cache: {self.head} (0 commits back", result.stdout)
        self.assertEqual(self.events()[0]["artifact_endpoint"], self.secondary + "/a0")
        self.assertNotIn(self.mapping_path("primary", self.ancestor), self.requests)

    def test_partial_artifact_failure_reuses_completed_files_on_other_mirror(self):
        self.mapping("primary", self.head)
        self.artifact("primary", 0)
        self.artifact("secondary", 0)
        self.artifact("secondary", 1)
        self.run_restore(LAKE_CACHE_ARTIFACT_ENDPOINT="https://wrong.invalid/a0",
                         LAKE_CACHE_REVISION_ENDPOINT="https://wrong.invalid/r0")
        events = self.events()
        self.assertEqual([e["artifact_endpoint"] for e in events],
                         [self.primary + "/a0", self.secondary + "/a0"])
        self.assertEqual([e["revision_endpoint"] for e in events],
                         [self.primary + "/r0", self.secondary + "/r0"])
        self.assertEqual(events[0]["inputs"], events[1]["inputs"])
        self.assertNotIn(f"/secondary/a0/{SCOPE}/{self.artifacts[0]}", self.requests)
        self.assertEqual(len(list(Path(self.env["LAKE_CACHE_DIR"]).iterdir())), 2)
        self.assertTrue(all('proto = "=http"' in event["curl_config"] for event in events))
        self.assertTrue(all("max-redirs = 0" in event["curl_config"] for event in events))

    def test_corrupt_artifact_is_retried_from_secondary(self):
        self.mapping("primary", self.head)
        self.artifact("primary", 0, b"corrupt")
        self.artifact("primary", 1)
        self.artifact("secondary", 0)
        self.run_restore()
        self.assertIn(f"/secondary/a0/{SCOPE}/{self.artifacts[0]}", self.requests)
        self.assertEqual((Path(self.env["LAKE_CACHE_DIR"]) / self.artifacts[0]).read_bytes(), b"first")

    def test_missing_only_skips_root_dep_hash_but_not_dependency_or_broken_traces(self):
        self.mapping("primary", self.head)
        self.artifact("primary", 1)
        self.write(".lake/build/lib/lean/Current.trace", json.dumps({"depHash": self.entries[0][0]}))
        self.write(".lake/packages/cslib/.lake/build/Other.trace", json.dumps({"depHash": self.entries[1][0]}))
        self.write(".lake/build/lib/lean/Broken.trace", "not json")
        result = self.run_restore(script="get-missing.sh")
        self.assertEqual(self.events()[0]["inputs"], [self.entries[1][0]])
        self.assertIn("2 modules; 1 of them are not current in .lake.", result.stdout)

    def test_full_local_restore_does_not_apply_missing_only_filter(self):
        self.mapping("primary", self.head)
        for i in range(2):
            self.artifact("primary", i)
        self.write(".lake/build/Current.trace", json.dumps({"depHash": self.entries[0][0]}))
        self.run_restore(script="get.sh")
        self.assertEqual(self.events()[0]["kind"], "mathlib")
        self.assertEqual(self.events()[1]["inputs"], [entry[0] for entry in self.entries])

    def test_all_current_needs_no_lake_download(self):
        self.mapping("primary", self.head)
        for i, (input_hash, _) in enumerate(self.entries):
            self.write(f".lake/build/{i}.trace", json.dumps({"depHash": input_hash}))
        self.run_restore("--missing-only")
        self.assertEqual(self.events(), [])

    def test_url_override_replaces_config_and_empty_disables(self):
        self.mapping("secondary", self.head)
        for i in range(2):
            self.artifact("secondary", i)
        self.run_restore(COMPLEXITYLIB_CACHE_URL=self.secondary)
        self.assertTrue(all(path.startswith("/secondary/") for path in self.requests))
        count = len(self.requests)
        self.run_restore(COMPLEXITYLIB_CACHE_URL="")
        self.assertEqual(len(self.requests), count)

    def test_plain_http_outside_loopback_and_credential_urls_are_rejected(self):
        for url in ("http://cache.example.invalid", "http://127.0.0.1.evil.invalid",
                    "https://user:secret@cache.example.invalid", "https://cache.example.invalid?query=1"):
            with self.subTest(url=url):
                result = self.run_restore(COMPLEXITYLIB_CACHE_URL=url)
                self.assertIn("cache endpoints require HTTPS", result.stderr)
        self.assertEqual(self.requests, [])

    def test_https_mapping_redirect_to_http_is_rejected(self):
        secure, certificate = self.start_https_server()
        self.config([secure + "/secure"])
        source = self.mapping_path("secure", self.head)
        target = self.mapping_path("primary", self.head)
        self.redirects[source] = self.base + target
        self.mapping("primary", self.head)
        result = self.run_restore(CURL_CA_BUNDLE=str(certificate))
        self.assertIn("revision lookup failed", result.stderr)
        self.assertIn(source, self.requests, result.stdout + result.stderr)
        self.assertNotIn(target, self.requests)
        self.assertEqual(self.events(), [])

    def test_lake_artifact_redirect_to_http_is_rejected(self):
        secure, certificate = self.start_https_server()
        self.config([secure + "/secure"])
        self.mapping("secure", self.head)
        targets = []
        for index, artifact in enumerate(self.artifacts):
            source = f"/secure/a0/{SCOPE}/{artifact}"
            target = f"/primary/a0/{SCOPE}/{artifact}"
            self.redirects[source] = self.base + target
            self.artifact("primary", index)
            targets.append((source, target))
        result = self.run_restore(CURL_CA_BUNDLE=str(certificate))
        self.assertIn("artifact download failed", result.stderr)
        event = self.events()[0]
        self.assertEqual(event["artifact_endpoint"], secure + "/secure/a0")
        self.assertIn('proto-redir = "=https"', event["curl_config"])
        for source, target in targets:
            self.assertIn(source, self.requests)
            self.assertNotIn(target, self.requests)

    def test_real_lake_artifact_redirect_to_http_is_rejected(self):
        if shutil.which("lake", path=self.real_path) is None:
            self.skipTest("Lake is required for redirect-policy integration tests")
        secure, certificate = self.start_https_server()
        self.config([secure + "/secure"])
        artifact = "0123456789abcdef.art"
        self.mapping("secure", self.head, [(self.entries[0][0], [artifact])])
        source = f"/secure/a0/{SCOPE}/{artifact}"
        target = f"/primary/a0/{SCOPE}/{artifact}"
        self.redirects[source] = self.base + target
        self.routes[target] = (200, b"artifact", 0)
        self.write("lakefile.toml", '''name = "fixture"
enableArtifactCache = true
platformIndependent = true
[[lean_lib]]
name = "Fixture"
''')
        result = self.run_restore(CURL_CA_BUNDLE=str(certificate), PATH=self.real_path)
        self.assertIn("artifact download failed", result.stderr)
        self.assertIn(source, self.requests, result.stdout + result.stderr)
        self.assertNotIn(target, self.requests)

    def test_missing_and_malformed_config_are_optional_without_network(self):
        path = self.root / "scripts/cache/endpoints.json"
        path.unlink()
        result = self.run_restore()
        self.assertIn("lake build will compile missing outputs", result.stderr)
        path.write_text('{"version": 2, "read": []}')
        result = self.run_restore()
        self.assertIn("must have version 1", result.stderr)
        self.assertEqual(self.requests, [])

    def test_malformed_mapping_falls_back_to_same_revision_on_other_mirror(self):
        self.mapping("secondary", self.head)
        for i in range(2):
            self.artifact("secondary", i)
        for body in (b"<html>unavailable</html>", b'"2026-03-17"\n["1", []]\n',
                     b'"not-a-date"\n', b'"2026-02-30"\n'):
            with self.subTest(body=body):
                self.routes[self.mapping_path("primary", self.head)] = (200, body, 0)
                result = self.run_restore()
                self.assertIn("invalid revision mapping", result.stderr)
                self.assertEqual(self.events()[-1]["artifact_endpoint"], self.secondary + "/a0")

    def test_shallow_checkout_is_deepened_before_ancestor_lookup(self):
        upstream = self.temp / "upstream.git"
        shallow = self.temp / "shallow"
        subprocess.run(["git", "clone", "--quiet", "--bare", str(self.root), str(upstream)],
                       env=self.env, check=True)
        subprocess.run(["git", "clone", "--quiet", "--depth=1", upstream.as_uri(), str(shallow)],
                       env=self.env, check=True)
        shutil.copytree(self.root / "scripts", shallow / "scripts")
        self.root = shallow
        self.assertEqual(self.git("rev-parse", "--is-shallow-repository"), "true")
        self.mapping("primary", self.ancestor)
        for i in range(2):
            self.artifact("primary", i)
        result = self.run_restore()
        self.assertIn(f"Remote cache: {self.ancestor} (1 commits back", result.stdout)
        self.assertEqual(self.git("rev-parse", "--is-shallow-repository"), "false")

    def test_unavailable_manifest_endpoint_is_not_retried_for_every_ancestor(self):
        self.routes[self.mapping_path("primary", self.head)] = (503, b"unavailable", 0)
        self.mapping("secondary", self.ancestor)
        for i in range(2):
            self.artifact("secondary", i)
        result = self.run_restore()
        self.assertIn(f"Remote cache: {self.ancestor} (1 commits back", result.stdout)
        self.assertEqual(sum(path.startswith("/primary/r0/") for path in self.requests), 1)

    def test_slow_manifest_has_bounded_failover(self):
        self.routes[self.mapping_path("primary", self.head)] = (200, b"late", .6)
        self.mapping("secondary", self.head)
        for i in range(2):
            self.artifact("secondary", i)
        started = time.monotonic()
        self.run_restore("--request-timeout", ".1")
        self.assertLess(time.monotonic() - started, 2)
        self.assertEqual(self.events()[0]["artifact_endpoint"], self.secondary + "/a0")

    def test_timed_out_lake_is_stopped_before_fallback(self):
        self.mapping("primary", self.head)
        for i in range(2):
            self.artifact("secondary", i)
        result = self.run_restore("--artifact-timeout", "1",
                                  RESTORE_HANG_ENDPOINT=self.primary + "/a0")
        self.assertEqual(len(self.events()), 2, result.stderr)
        pid = int(Path(self.env["RESTORE_PID"]).read_text())
        with self.assertRaises(ProcessLookupError):
            os.kill(pid, 0)

    def test_all_misses_and_exhausted_artifacts_leave_source_build_available(self):
        result = self.run_restore()
        self.assertIn("No outputs uploaded for the last 2 commits", result.stdout)
        self.mapping("primary", self.head)
        result = self.run_restore()
        self.assertIn("lake build will compile those modules", result.stderr)
        self.assertEqual(len(self.events()), 2)

    def test_hundred_missing_revisions_share_one_total_time_budget(self):
        real_git = shutil.which("git", path=self.env["PATH"])
        git = self.bin_dir / "git"
        git.write_text("#!/usr/bin/env python3\nimport os, sys\n"
                       "if sys.argv[1:2] == ['rev-list']:\n"
                       "    print('\\n'.join(f'{i:040x}' for i in range(100)))\n"
                       "else:\n    os.execv(os.environ['RESTORE_REAL_GIT'], sys.argv)\n")
        git.chmod(0o755)
        started = time.monotonic()
        result = self.run_restore("--timeout", ".5", RESTORE_REAL_GIT=real_git)
        self.assertLess(time.monotonic() - started, 2)
        self.assertIn("No outputs uploaded for the last ", result.stdout)
        self.assertLess(len(self.requests), 200)
        self.assertEqual(self.events(), [])

    def test_endpoint_resolver_is_importable_as_a_namespace_package(self):
        result = subprocess.run(["python3", "-c", "from cache.restore import endpoints; "
                                 "from pathlib import Path; "
                                 "assert endpoints(Path('.'), {'COMPLEXITYLIB_CACHE_URL': ''}) == []"],
                                cwd=self.root / "scripts", env=self.env,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_invalid_timeout_arguments_do_not_fetch(self):
        target = self.root / "scripts/cache/restore.py"
        for value in ("0", "nan", "inf", "-1"):
            result = subprocess.run(["python3", str(target), "--timeout", value],
                                    env=self.env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
        self.assertEqual(self.requests, [])


if __name__ == "__main__":
    unittest.main()
