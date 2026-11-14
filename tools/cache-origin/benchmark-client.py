#!/usr/bin/env python3
"""Measure HTTP publisher bytes/client costs with a synthetic HTTPS loopback sink.

python3 tools/cache-origin/benchmark-client.py --baseline <pre-change revision> --output /tmp/cache-benchmark.json
Requires openssl, curl and Python 3.11+. Never contacts a real cache or uses its credentials.
The sink verifies uploaded digests but omits origin retained-object hashing, storage and fsync;
these are client/transfer measurements, not a prediction of production end-to-end speedup.
"""

import argparse
import base64
import hashlib
from http.server import BaseHTTPRequestHandler, HTTPServer
import io
import json
import os
from pathlib import Path
import resource
import secrets
import ssl
import subprocess
import sys
import tarfile
import tempfile
import threading
import time

REPO = Path(__file__).resolve().parents[2]
SCOPE = "cslib-community/complexitylib"
PROBE = "application/vnd.cslib.cache-probe.v1+tar"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, help="Git revision containing the full-upload publisher")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--archives", type=int, default=9533)
    parser.add_argument("--missing", type=int, default=17)
    parser.add_argument("--archive-bytes", type=int, default=37400)
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if not 0 <= args.missing <= args.archives or args.archives < 1 or min(args.archive_bytes, args.repeats) < 1:
        parser.error("require positive archives/bytes/repeats and 0 <= missing <= archives")
    baseline = subprocess.check_output(["git", "rev-parse", "--verify", "--end-of-options",
                                        args.baseline + "^{commit}"], cwd=REPO, text=True).strip()
    with tempfile.TemporaryDirectory(prefix="cache-client-benchmark-") as temporary:
        root = Path(temporary)
        legacy = root / "baseline" / "scripts" / "cache" / "publish.py"
        legacy.parent.mkdir(parents=True)
        legacy.write_bytes(subprocess.check_output(["git", "show", baseline + ":scripts/cache/publish.py"], cwd=REPO))
        stage = root / "stage"
        files = {}
        mapping = f"r0/{SCOPE}/tc/fixture/{'a' * 40}.jsonl"
        rows = ['"2026-03-17"']
        for i in range(args.archives):
            name = f"a0/{SCOPE}/{i:016x}.art"
            payload = secrets.token_bytes(args.archive_bytes)
            path = stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            files[name] = hashlib.sha256(payload).hexdigest()
            rows.append(json.dumps([f"{i:016x}", f"{i:016x}.ltar"], separators=(",", ":")))
        path = stage / mapping
        path.parent.mkdir(parents=True)
        path.write_text("\n".join(rows) + "\n")
        files[mapping] = hashlib.sha256(path.read_bytes()).hexdigest()
        metadata = {"version": 1, "revision": "a" * 40, "toolchain": "fixture", "files": files}
        (stage / "publication.json").write_text(json.dumps(metadata, sort_keys=True) + "\n")
        cert, key = root / "cert.pem", root / "key.pem"
        subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "1",
                        "-keyout", str(key), "-out", str(cert), "-subj", "/CN=localhost",
                        "-addext", "subjectAltName=IP:127.0.0.1"], check=True, capture_output=True)
        password = secrets.token_urlsafe(32)
        authorization = "Basic " + base64.b64encode(("fixture:" + password).encode()).decode()
        sent, runs = [], []

        class Sink(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def log_message(self, *args):
                pass

            def do_PUT(self):
                if self.headers.get("Authorization") != authorization:
                    self.send_error(401)
                    return
                body = self.rfile.read(int(self.headers["Content-Length"]))
                sent.append(len(body))
                missing = [f"a0/{SCOPE}/{i:016x}.art"
                           for i in range(args.archives - args.missing, args.archives)]
                expected = {"application/x-tar": set(files), PROBE: {mapping},
                            "application/vnd.cslib.cache-delta.v1+tar": {mapping, *missing}}
                with tarfile.open(fileobj=io.BytesIO(body)) as package:
                    assert package.getnames() == ["publication.json", *sorted(expected[self.headers["Content-Type"]])]
                    assert json.load(package.extractfile("publication.json")) == metadata
                    for name in package.getnames()[1:]:
                        assert hashlib.sha256(package.extractfile(name).read()).hexdigest() == files[name]
                if self.headers["Content-Type"] == PROBE:
                    response = json.dumps({"version": 1, "revision": "a" * 40, "missing": missing}).encode()
                    self.send_response(200)
                else:
                    response = b"{}"
                    self.send_response(201)
                self.send_header("Content-Length", str(len(response)))
                self.end_headers()
                self.wfile.write(response)

        server = HTTPServer(("127.0.0.1", 0), Sink)
        tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        tls.load_cert_chain(cert, key)
        server.socket = tls.wrap_socket(server.socket, server_side=True)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        environment = {**os.environ, "CACHE_SERVER_USER": "fixture", "CACHE_SERVER_PASSWORD": password,
                       "CURL_CA_BUNDLE": str(cert), "NO_PROXY": "127.0.0.1", "no_proxy": "127.0.0.1"}
        try:
            for _ in range(args.repeats):
                for mode, client in (("full", legacy), ("delta", REPO / "scripts/cache/publish.py")):
                    sent.clear()
                    before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    started = time.monotonic()
                    subprocess.run([sys.executable, str(client), "http", f"https://127.0.0.1:{server.server_port}",
                                    str(stage)], env=environment, check=True, capture_output=True, timeout=120)
                    wall = time.monotonic() - started
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    runs.append({"mode": mode, "wall_seconds": wall,
                                 "client_cpu_seconds": after.ru_utime + after.ru_stime - before.ru_utime - before.ru_stime,
                                 "actual_received_bytes": list(sent)})
                    print(json.dumps(runs[-1]), flush=True)
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
        args.output.write_text(json.dumps({"baseline": baseline, "archives": args.archives,
            "missing": args.missing, "archive_bytes": args.archive_bytes, "runs": runs,
            "limitation": "HTTPS loopback sink omits origin retained-object hashing, storage and fsync"}, indent=2) + "\n")


if __name__ == "__main__":
    main()
