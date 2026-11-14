"""Opt-in end-to-end tests of the real nginx example and Go cache origin.

Run on Linux with CACHE_ORIGIN_NGINX_TEST=1, CACHE_ORIGIN_BIN and NGINX_BIN.
No Lean, external listener, production credential or root access is required.
"""

import base64
from datetime import datetime
from http.client import HTTPConnection, HTTPSConnection
from http.server import BaseHTTPRequestHandler
from socketserver import UnixStreamServer
import threading
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import secrets
import signal
import socket
import ssl
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from urllib.error import HTTPError, URLError
from urllib.request import HTTPSHandler, ProxyHandler, Request, build_opener

REPO = Path(__file__).resolve().parents[1]
SCOPE = "cslib-community/complexitylib"


def nginx_string(value):
    return '"' + str(value).replace("\\", "\\\\").replace('"', '\\"') + '"'


@unittest.skipUnless(os.environ.get("CACHE_ORIGIN_NGINX_TEST") == "1", "opt in to real nginx tests")
class RealNginxCacheTests(unittest.TestCase):
    def setUp(self):
        self.assertEqual(sys.platform, "linux", "the cache origin requires Linux")
        self.origin_bin = os.environ.get("CACHE_ORIGIN_BIN") or shutil.which("cache-origin")
        self.nginx_bin = os.environ.get("NGINX_BIN") or shutil.which("nginx")
        for name, command in (("cache-origin", self.origin_bin), ("nginx", self.nginx_bin),
                              ("openssl", shutil.which("openssl")), ("curl", shutil.which("curl")),
                              ("htpasswd", shutil.which("htpasswd"))):
            self.assertTrue(command and Path(command).is_file(), f"required executable missing: {name}")
        temporary = tempfile.TemporaryDirectory(prefix="cache-nginx-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.store = self.root / "store"
        self.store.mkdir()
        (self.store / "nginx-tmp").mkdir()
        self.dashboard = self.root / "dashboard"
        self.dashboard.mkdir()
        (self.dashboard / "index.html").write_text("<!doctype html><title>Cache dashboard fixture</title>")
        (self.dashboard / "app.js").write_text("'use strict';")
        (self.dashboard / "style.css").write_text("body { margin: 0; }")
        (self.dashboard / "stats.json").write_text('{"schema":1}')
        self.socket = self.root / "origin.sock"
        self.cert, key = self.root / "cert.pem", self.root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "1",
                        "-keyout", str(key), "-out", str(self.cert), "-subj", "/CN=localhost",
                        "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost"],
                       check=True, capture_output=True, timeout=15)
        self.user, self.password = "fixture-publisher", secrets.token_urlsafe(32)
        password_record = subprocess.check_output(["htpasswd", "-niBC", "4", self.user],
                                                  input=(self.password + "\n").encode()).decode().strip()
        self.assertTrue(password_record.startswith(self.user + ":$2y$04$"))
        password_file = self.root / "htpasswd"
        password_file.write_text(password_record + "\n")
        password_file.chmod(0o640)
        with socket.socket() as listener:
            listener.bind(("127.0.0.1", 0))
            port = listener.getsockname()[1]
        self.endpoint = f"https://127.0.0.1:{port}"
        tls = ssl.create_default_context(cafile=str(self.cert))
        self.http = build_opener(ProxyHandler({}), HTTPSHandler(context=tls))
        self.toolchain = (REPO / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
        self.publications = 0
        self.syslog = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.syslog.bind(("127.0.0.1", 0))
        self.syslog.settimeout(0.1)
        self.addCleanup(self.syslog.close)
        self.usage_syslog = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.usage_syslog.bind(("127.0.0.1", 0))
        self.usage_syslog.settimeout(0.1)
        self.addCleanup(self.usage_syslog.close)
        self.start([self.origin_bin, "serve", "--root", str(self.store), "--socket", str(self.socket)], "origin")
        self.wait_for(lambda: self.socket.exists(), "origin socket")

        # Exercise the checked-in route/auth/buffering configuration, changing only
        # host-specific addresses and paths for this isolated fixture.
        fragment = (REPO / "tools/cache-origin/examples/nginx.conf").read_text()
        replacements = {
            "listen 443 ssl;": f"listen 127.0.0.1:{port} ssl;",
            "server_name cache.example.edu;": "server_name localhost;",
            "/etc/letsencrypt/live/cache.example.edu/fullchain.pem": nginx_string(self.cert),
            "/etc/letsencrypt/live/cache.example.edu/privkey.pem": nginx_string(key),
            "/srv/cache-origin/public": nginx_string(self.store / "public"),
            "/srv/cache-origin/nginx-tmp": nginx_string(self.store / "nginx-tmp"),
            "/usr/local/share/cache-dashboard": nginx_string(self.dashboard),
            "/var/lib/cache-dashboard/stats.json": nginx_string(self.dashboard / "stats.json"),
            "/etc/nginx/cache-publish.htpasswd": nginx_string(password_file),
            "http://unix:/run/cache-origin/http.sock": nginx_string(f"http://unix:{self.socket}"),
            # Keep the real syslog options/tags. Changing only the transport
            # avoids needing a system journal while exercising nginx's parser.
            "syslog:server=unix:/dev/log":
                f"syslog:server=127.0.0.1:{self.syslog.getsockname()[1]}",
            "syslog:server=unix:/run/systemd/journal.cache-origin-usage/dev-log":
                f"syslog:server=127.0.0.1:{self.usage_syslog.getsockname()[1]}",
        }
        for old, new in replacements.items():
            self.assertIn(old, fragment)
            fragment = fragment.replace(old, new)
        # A root-run local test must not drop its worker to a different UID that
        # cannot traverse TemporaryDirectory. Unprivileged nginx ignores user=.
        import pwd
        user = pwd.getpwuid(os.geteuid()).pw_name
        config = self.root / "nginx.conf"
        config.write_text(
            f"user {user};\npid {nginx_string(self.root / 'nginx.pid')};\n"
            f"error_log {nginx_string(self.root / 'nginx-error.log')} info;\n"
            "events { worker_connections 64; }\nhttp {\naccess_log off;\n" +
            "".join(f"{kind}_temp_path {nginx_string(self.root / (kind + '-tmp'))};\n"
                    for kind in ("proxy", "fastcgi", "uwsgi", "scgi")) + fragment + "\n}\n")
        command = [self.nginx_bin, "-p", str(self.root) + "/", "-c", str(config)]
        checked = subprocess.run([*command, "-t"], capture_output=True, text=True, timeout=10)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        self.start([*command, "-g", "daemon off;"], "nginx", signal.SIGQUIT)
        self.wait_for(self.nginx_ready, "nginx HTTPS listener")

    def start(self, command, name, stop_signal=signal.SIGTERM):
        log = (self.root / (name + ".log")).open("w+")
        self.addCleanup(log.close)
        process = subprocess.Popen(command, stdout=log, stderr=subprocess.STDOUT)

        def stop():
            if process.poll() is None:
                process.send_signal(stop_signal)
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=5)
        self.addCleanup(stop)

    def wait_for(self, ready, description):
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            if ready():
                return
            time.sleep(0.05)
        logs = "\n".join(p.read_text() for p in self.root.glob("*.log"))
        self.fail(f"timed out waiting for {description}\n{logs}")

    def nginx_ready(self):
        try:
            return self.request("GET", "/")[0] == 200
        except (URLError, OSError):
            return False

    def request(self, method, path, body=None, credentials=None, source_ip=None):
        headers = {"Content-Type": "application/x-tar"} if body is not None else {}
        if credentials is not None:
            headers["Authorization"] = "Basic " + base64.b64encode(credentials.encode()).decode()
        if source_ip is not None:
            connection = HTTPSConnection("127.0.0.1", int(self.endpoint.rsplit(":", 1)[1]), timeout=5,
                context=ssl.create_default_context(cafile=str(self.cert)), source_address=(source_ip, 0))
            try:
                connection.request(method, path, body=body, headers=headers)
                response = connection.getresponse()
                return response.status, response.read(), response.headers
            finally:
                connection.close()
        request = Request(self.endpoint + path, data=body, headers=headers, method=method)
        try:
            response = self.http.open(request, timeout=5)
        except HTTPError as error:
            response = error
        with response:
            return response.status, response.read(), response.headers

    def publication(self, revision, artifacts):
        self.publications += 1
        directory = self.root / f"publication-{self.publications}"
        directory.mkdir()
        mapping = f"r0/{SCOPE}/tc/{self.toolchain}/{revision}.jsonl"
        mapping_bytes = ('"2026-03-17"\n' + "".join(
            json.dumps([f"{index:016x}", f"{number:016x}.ltar"], separators=(",", ":")) + "\n"
            for index, number in enumerate(artifacts, 1))).encode()
        files = {f"a0/{SCOPE}/{number:016x}.art": data for number, data in artifacts.items()}
        files[mapping] = mapping_bytes
        for name, data in files.items():
            path = directory / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        metadata = {"version": 1, "revision": revision, "toolchain": self.toolchain,
                    "files": {name: hashlib.sha256(data).hexdigest() for name, data in files.items()}}
        (directory / "publication.json").write_text(json.dumps(metadata))
        body = io.BytesIO()
        with tarfile.open(fileobj=body, mode="w", format=tarfile.USTAR_FORMAT) as archive:
            for name in ["publication.json", *sorted(files)]:
                archive.add(directory / name, arcname=name, recursive=False)
        return directory, body.getvalue(), mapping, mapping_bytes

    def publish(self, directory):
        environment = {**os.environ, "CACHE_SERVER_USER": self.user,
                       "CACHE_SERVER_PASSWORD": self.password, "CURL_CA_BUNDLE": str(self.cert),
                       "NO_PROXY": "127.0.0.1", "no_proxy": "127.0.0.1"}
        result = subprocess.run([sys.executable, str(REPO / "scripts/cache/publish.py"), "http",
                                 self.endpoint, str(directory)], env=environment,
                                capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result.stdout

    def observe_uploads(self, legacy=False):
        """Count bytes behind real nginx; optionally emulate the old 415 contract.

        The legacy gate rejects vendor media types exactly as the old Go handler
        did; accepted full packages still reach the real origin's validation.
        """
        upstream = self.root / "upstream.sock"
        self.socket.rename(upstream)
        requests = []
        class Gate(BaseHTTPRequestHandler):
            def log_message(self, *args):
                pass

            def do_PUT(self):
                body = self.rfile.read(int(self.headers["Content-Length"]))
                media_type = self.headers["Content-Type"]
                requests.append((media_type, len(body)))
                if legacy and media_type != "application/x-tar":
                    self.send_response(415)
                    self.end_headers()
                    return
                connection = HTTPConnection("local")
                connection.sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                connection.sock.connect(str(upstream))
                try:
                    connection.request("PUT", self.path, body, {"Content-Type": media_type})
                    response = connection.getresponse()
                    payload = response.read()
                    self.send_response(response.status)
                    self.send_header("Content-Length", str(len(payload)))
                    self.end_headers()
                    self.wfile.write(payload)
                finally:
                    connection.close()
        gate = UnixStreamServer(str(self.socket), Gate)
        thread = threading.Thread(target=gate.serve_forever, daemon=True)
        thread.start()
        def stop():
            gate.shutdown()
            gate.server_close()
            thread.join(timeout=5)
        self.addCleanup(stop)
        return requests

    def test_incremental_publication_transfers_only_missing_payloads_through_nginx(self):
        uploads = self.observe_uploads()
        old = b"existing archive" * 65536
        stage, full, _, _ = self.publication("a" * 40, {1: old})
        credentials = self.user + ":" + self.password
        self.assertEqual(self.request("PUT", "/publish/" + "a" * 40, full, credentials)[0], 201)
        stage, _, mapping, contents = self.publication("b" * 40, {1: old, 2: b"new archive"})
        output = self.publish(stage)
        self.assertIn('"mode": "incremental"', output)
        self.assertIn('"archives_sent": 1', output)
        self.assertEqual(len(uploads), 3)
        self.assertLess(sum(size for _, size in uploads[1:]), len(old) // 10)
        metrics = json.loads(next(line.split(" ", 1)[1] for line in output.splitlines()
                                 if line.startswith("CACHE_HTTP_PUBLICATION ")))
        self.assertEqual(metrics["request_body_bytes"], [size for _, size in uploads[1:]])
        self.assertEqual(self.request("GET", "/" + mapping)[:2], (200, contents))

    def test_new_client_falls_back_through_unchanged_nginx_to_legacy_handler(self):
        uploads = self.observe_uploads(legacy=True)
        stage, full, mapping, contents = self.publication("a" * 40, {1: b"legacy archive"})
        output = self.publish(stage)
        self.assertIn('"mode": "legacy-full"', output)
        self.assertEqual([kind for kind, _ in uploads],
                         ["application/vnd.cslib.cache-probe.v1+tar", "application/x-tar"])
        self.assertEqual(uploads[1][1], len(full))
        self.assertEqual(self.request("GET", "/" + mapping)[:2], (200, contents))

    def test_failed_auth_syslog_matches_the_jail_identifier_without_hostname(self):
        jail = (REPO / "tools/cache-origin/examples/cache-origin-fail2ban.conf").read_text()
        identifier = re.search(r"^journalmatch = SYSLOG_IDENTIFIER=(\w+)$", jail, re.MULTILINE).group(1)
        self.assertEqual(self.request("PUT", "/publish/" + "a" * 40, b"invalid",
                                      self.user + ":wrong")[0], 401)
        messages = []
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            try:
                message = self.syslog.recv(65535).decode()
            except socket.timeout:
                continue
            messages.append(message)
            if f" {identifier}: " in message:
                # RFC3164 timestamp immediately followed by the identifier:
                # no hostname that journald could mistake for the program tag.
                self.assertRegex(message, rf"^<\d+>\w{{3}}\s+\d{{1,2}} \d{{2}}:\d{{2}}:\d{{2}} {re.escape(identifier)}: ")
                self.assertIn("password mismatch", message)
                self.assertNotIn(self.password, message)
                break
        else:
            self.fail("No matching auth syslog message: " + repr(messages))

    def usage_records(self):
        records = []
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            try:
                message = self.usage_syslog.recv(65535).decode()
            except socket.timeout:
                if records:
                    break
                continue
            self.assertIn(" cache_usage: ", message)
            records.append(json.loads(message.split(" cache_usage: ", 1)[1]))
        self.assertTrue(records, "no usage records received")
        for record in records:
            self.assertEqual(set(record), {"time", "method", "uri", "status", "bytes", "seconds"})
            datetime.fromisoformat(record["time"])
            self.assertGreaterEqual(int(record["bytes"]), 0)
            self.assertGreaterEqual(float(record["seconds"]), 0)
        return records

    def test_usage_logs_downloads_misses_and_bytes_without_secrets_or_oversized_records(self):
        contents = b"usage fixture\n"
        directory, _, mapping, mapping_bytes = self.publication("e" * 40, {1: contents})
        self.publish(directory)
        artifact = f"/a0/{SCOPE}/{1:016x}.art"
        missing = f"/a0/{SCOPE}/{2:016x}.art"
        credentials = self.user + ":" + self.password
        self.assertEqual(self.request("GET", artifact + "?secret-query=omit", credentials=credentials)[0], 200)
        self.assertEqual(self.request("HEAD", artifact)[0], 200)
        self.assertEqual(self.request("GET", "/" + mapping)[0], 200)
        self.assertEqual(self.request("GET", missing)[0], 404)
        self.assertEqual(self.request("GET", "/usage-%22-%5C?secret-query=omit")[0], 404)
        self.assertEqual(self.request("GET", "/private-path-" + "x" * 3000)[0], 404)
        records = self.usage_records()
        get = next(r for r in records if r["uri"] == artifact and r["method"] == "GET")
        head = next(r for r in records if r["uri"] == artifact and r["method"] == "HEAD")
        self.assertEqual((get["status"], int(get["bytes"])), ("200", len(contents)))
        self.assertEqual((head["status"], int(head["bytes"])), ("200", 0))
        mapped = next(r for r in records if r["uri"] == "/" + mapping)
        self.assertEqual(int(mapped["bytes"]), len(mapping_bytes))
        self.assertTrue(any(r["uri"] == missing and r["status"] == "404" for r in records))
        self.assertGreaterEqual(sum(r["uri"] == "/other" and r["status"] == "404" for r in records), 2)
        serialized = json.dumps(records)
        for private in ("secret-query", self.user, self.password, "Authorization", "private-path", "usage-"):
            self.assertNotIn(private, serialized)
        self.assertTrue(all(len(json.dumps(record)) < 1024 for record in records))

    def test_publication_downloads_and_immediate_gc(self):
        revision_a, revision_b = "a" * 40, "b" * 40
        stage_a, body_a, map_a, map_a_bytes = self.publication(revision_a, {1: b"shared", 2: b"old unique"})
        path_a = "/publish/" + revision_a
        self.assertEqual(self.request("PUT", path_a, body_a)[0], 401)
        self.assertEqual(self.request("PUT", path_a, body_a, self.user + ":wrong")[0], 401)
        credentials = self.user + ":" + self.password
        import fcntl
        with (self.store / "state/lock").open("a+") as lock:
            os.fchmod(lock.fileno(), 0o600)
            fcntl.flock(lock, fcntl.LOCK_EX)
            busy = self.request("PUT", path_a, body_a, credentials)
            self.assertEqual(busy[0], 503)
            self.assertEqual(busy[2]["Retry-After"], "5")
            fcntl.flock(lock, fcntl.LOCK_UN)
        self.publish(stage_a)
        self.assertEqual(self.request("PUT", path_a, body_a, credentials)[0], 201)
        self.assertEqual(self.request("GET", "/" + map_a)[:2], (200, map_a_bytes))
        shared = f"/a0/{SCOPE}/{1:016x}.art"
        unique_a = f"/a0/{SCOPE}/{2:016x}.art"
        self.assertEqual(self.request("GET", shared)[:2], (200, b"shared"))
        self.assertEqual(self.request("GET", shared)[2]["Cache-Control"], "no-store")
        self.assertEqual(self.request("GET", "/" + map_a)[2]["Cache-Control"], "no-store")
        head = self.request("HEAD", shared)
        self.assertEqual(head[:2], (200, b""))
        self.assertEqual(head[2]["Content-Length"], str(len(b"shared")))
        for path in (f"/a0/{SCOPE}/", "/private"):
            self.assertEqual(self.request("GET", path)[0], 404)
        self.assertEqual(self.request("DELETE", shared)[0], 403)
        self.assertEqual(self.request("DELETE", path_a, credentials=credentials)[0], 403)
        _, conflict, _, _ = self.publication(revision_a, {1: b"shared", 2: b"different"})
        self.assertEqual(self.request("PUT", path_a, conflict, credentials)[0], 409)
        self.assertEqual(self.request("GET", unique_a)[:2], (200, b"old unique"))
        self.assertEqual(self.request("GET", "/" + map_a)[:2], (200, map_a_bytes))

        stage_b, _, map_b, map_b_bytes = self.publication(revision_b, {1: b"shared", 3: b"new unique"})
        self.publish(stage_b)
        # Even after an idle weekend, preserve the globally newest publication.
        old = time.time() - 3 * 24 * 3600
        os.utime(self.store / "public" / map_a, (old - 60, old - 60))
        os.utime(self.store / "public" / map_b, (old, old))
        result = subprocess.run([self.origin_bin, "gc", "--root", str(self.store), "--apply"],
                                capture_output=True, text=True, timeout=15)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads(result.stdout)
        self.assertEqual(report["expired_mappings"], [map_a])
        self.assertEqual(report["delete_artifacts"], [unique_a[1:]])
        self.assertEqual(self.request("GET", "/" + map_a)[0], 404)
        self.assertEqual(self.request("GET", unique_a)[0], 404)
        self.assertEqual(self.request("GET", "/" + map_b)[:2], (200, map_b_bytes))
        self.assertEqual(self.request("GET", shared)[:2], (200, b"shared"))
        self.assertEqual(self.request("GET", f"/a0/{SCOPE}/{3:016x}.art")[:2], (200, b"new unique"))

    def test_upload_rate_limit_rejects_abuse(self):
        path = "/publish/" + "c" * 40
        statuses = [self.request("PUT", path, b"not a package")[0] for _ in range(12)]
        self.assertIn(401, statuses)
        self.assertIn(429, statuses)
        # Access logs preserve failed-auth evidence but omit rate rejections,
        # avoiding a request flood turning into an unbounded log flood.
        messages = []
        deadline = time.monotonic() + 3
        while time.monotonic() < deadline:
            try:
                messages.append(self.syslog.recv(65535).decode())
            except socket.timeout:
                if any(" 401 PUT " in message for message in messages):
                    break
        lines = "\n".join(messages)
        self.assertIn(" 401 PUT ", lines)
        self.assertNotIn(" 429 ", lines)
        self.assertNotIn(self.password, lines)
        # Usage still counts rejected requests without flooding the error sink.
        records = self.usage_records()
        self.assertTrue(any(r["status"] == "429" and r["method"] == "PUT" for r in records))

    def test_dashboard_is_static_read_only_and_confined(self):
        status, html, headers = self.request("GET", "/")
        self.assertEqual(status, 200)
        self.assertIn(b"Cache dashboard fixture", html)
        self.assertIn("script-src 'self'", headers["Content-Security-Policy"])
        self.assertEqual(headers["X-Content-Type-Options"], "nosniff")
        self.assertEqual(self.request("GET", "/stats.json")[:2], (200, b'{"schema":1}'))
        self.assertEqual(self.request("GET", "/stats.json")[2]["Cache-Control"], "no-store")
        self.assertIn("javascript", self.request("GET", "/app.js")[2]["Content-Type"])
        self.assertIn("text/css", self.request("GET", "/style.css")[2]["Content-Type"])
        self.assertEqual(self.request("HEAD", "/stats.json")[:2], (200, b""))
        for path in ("/", "/stats.json", "/app.js", "/style.css"):
            self.assertEqual(self.request("PUT", path, b"replacement")[0], 403)
        for path in ("/collect.py", "/preview-data.json", "/dashboard/", "/state", "/stats.json/extra"):
            self.assertEqual(self.request("GET", path)[0], 404)

    def hold_upload(self, source_ip="127.0.0.1"):
        tls = ssl.create_default_context(cafile=str(self.cert))
        raw = socket.create_connection(("127.0.0.1", int(self.endpoint.rsplit(":", 1)[1])), timeout=5,
                                       source_address=(source_ip, 0))
        held = tls.wrap_socket(raw, server_hostname="127.0.0.1")
        self.addCleanup(held.close)
        authorization = base64.b64encode((self.user + ":" + self.password).encode()).decode()
        path = "/publish/" + "d" * 40
        # Complete headers but hold the body open, occupying the one per-IP
        # upload slot while nginx buffers the authenticated request.
        held.sendall((f"PUT {path} HTTP/1.1\r\nHost: localhost\r\n"
                      f"Authorization: Basic {authorization}\r\n"
                      "Content-Type: application/x-tar\r\nContent-Length: 100000\r\n"
                      "Expect: 100-continue\r\n\r\n").encode())
        self.assertIn(b"100 Continue", held.recv(4096))
        return path

    def test_simultaneous_upload_connection_limit(self):
        path = self.hold_upload()
        self.assertEqual(self.request("PUT", path, b"small", self.user + ":" + self.password)[0], 429)

    def test_anonymous_rate_exhaustion_does_not_starve_another_publisher(self):
        path = "/publish/" + "c" * 40
        # Several sources exhaust their own allowances. A shared 12/min bucket
        # would let them exhaust CI's allowance too, without knowing a password.
        for address in ("127.0.0.2", "127.0.0.3", "127.0.0.4"):
            statuses = [self.request("PUT", path, b"invalid", source_ip=address)[0] for _ in range(12)]
            self.assertIn(401, statuses)
            self.assertIn(429, statuses)
        _, package, _, _ = self.publication("f" * 40, {1: b"independent publisher"})
        self.assertEqual(self.request("PUT", "/publish/" + "f" * 40, package,
                                      self.user + ":" + self.password)[0], 201)

    def test_other_sources_cannot_reserve_all_upload_connections(self):
        # Pending bodies from two other IPs must not consume a special shared
        # two-upload pool. They have not reached the Go publication lock yet.
        self.hold_upload("127.0.0.2")
        self.hold_upload("127.0.0.3")
        _, package, _, _ = self.publication("f" * 40, {1: b"third source"})
        self.assertEqual(self.request("PUT", "/publish/" + "f" * 40, package,
                                      self.user + ":" + self.password)[0], 201)


if __name__ == "__main__":
    unittest.main()
