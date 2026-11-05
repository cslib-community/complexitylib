"""Render the origin configuration; opt in to actual nginx and hardened rrsync on Linux."""

from contextlib import contextmanager
import http.client
import os
from pathlib import Path
import re
import shutil
import socket
import ssl
import subprocess
import sys
import tempfile
import time
import unittest

try:
    from jinja2 import Environment, FileSystemLoader, StrictUndefined
except ImportError:
    Environment = None


ROOT = Path(__file__).resolve().parents[1]
INFRA = ROOT / "infra/cache-server"
INTEGRATION = os.environ.get("CACHE_SERVER_INTEGRATION") == "1"
REVISION = "a" * 40
ARTIFACT = "a0/cslib-community/complexitylib/0123456789abcdef.art"
MAPPING = "r0/cslib-community/complexitylib/tc/leanprover--lean4---v4.36.0-rc2/" + REVISION + ".jsonl"
RSYNC_PREFIX = Path(os.environ.get("CACHE_SERVER_RSYNC_PREFIX", "/opt/complexitylib-rsync/3.5.2"))


def accept_env_pattern():
    settings = (INFRA / "vars.yml").read_text()
    match = re.search(
        r"^cache_server_upload_accept_env_pattern: '(.+)'$", settings, re.MULTILINE)
    if match is None:
        raise AssertionError("Missing upload-account AcceptEnv policy")
    return re.compile(match[1])


def render(name, **overrides):
    if Environment is None:
        raise RuntimeError("Install infra/cache-server/requirements.txt to render templates")
    values = {
        "cache_server_domain": "cache.example.edu",
        "cache_server_revision": REVISION,
        "cache_server_http_port": 18080,
        "cache_server_https_port": 18443,
        "cache_server_acme_root": "/var/lib/complexitylib-cache-acme",
        "cache_server_certificate_directory": "/etc/letsencrypt/live/cache.example.edu",
        "cache_server_data_root": "/srv/complexitylib-cache",
        "cache_server_rsync_prefix": str(RSYNC_PREFIX),
        "cache_server_https": True,
        "cache_server_upload_command": "/usr/local/libexec/complexitylib-cache-upload",
        "cache_server_upload_home": "/var/lib/complexitylib-cache-upload",
        "cache_server_upload_keys": ["ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAIExample publisher"],
        "cache_server_upload_max_file_bytes": 1073741824,
        "cache_server_upload_pubkey_algorithms": (
            "ssh-ed25519,rsa-sha2-512,rsa-sha2-256,ecdsa-sha2-nistp256,"
            "ecdsa-sha2-nistp384,ecdsa-sha2-nistp521"),
        "cache_server_upload_user": "cache-upload",
        **overrides,
    }
    env = Environment(loader=FileSystemLoader(INFRA / "templates"),
                      undefined=StrictUndefined, keep_trailing_newline=True, trim_blocks=True)
    return env.get_template(name).render(**values)


@unittest.skipUnless(Environment is not None, "Ansible/Jinja controller dependencies not installed")
class TemplateTests(unittest.TestCase):
    def test_certificate_bootstrap_does_not_serve_payloads_over_http(self):
        bootstrap = render("nginx.conf.j2", cache_server_https=False)
        self.assertIn("/.well-known/acme-challenge/", bootstrap)
        self.assertIn("return 503;", bootstrap)
        self.assertNotIn("ssl_certificate", bootstrap)
        self.assertNotIn("/srv/complexitylib-cache", bootstrap)
        self.assertIn(REVISION, bootstrap)

    def test_all_rotating_keys_keep_the_forced_restrictions(self):
        keys = ["ssh-ed25519 AAAA old", "ssh-ed25519 BBBB new"]
        lines = render("authorized_keys.j2", cache_server_upload_keys=keys).splitlines()
        self.assertEqual(len(lines), 2)
        for line, key in zip(lines, keys):
            self.assertTrue(line.startswith(
                'restrict,command="/usr/local/libexec/complexitylib-cache-upload"'))
            self.assertTrue(line.endswith('" ' + key))

    def test_empty_reviewed_allowlist_authorizes_no_keys(self):
        self.assertEqual(render("authorized_keys.j2", cache_server_upload_keys=[]), "")
        allowlist = (INFRA / "upload-keys.yml").read_text()
        self.assertIn("cache_server_upload_keys: []", allowlist)
        self.assertNotIn("CACHE_SERVER_UPLOAD_KEYS", (INFRA / "vars.yml").read_text())
        self.assertIn("upload-keys.yml", (INFRA / "playbook.yml").read_text())

    def test_upload_command_checks_mount_and_limits_each_file(self):
        command = render("upload-command.sh.j2")
        syntax = subprocess.run(
            ["/bin/sh", "-n"], input=command, capture_output=True, text=True, timeout=5)
        self.assertEqual(syntax.returncode, 0, syntax.stdout + syntax.stderr)
        self.assertIn("/usr/bin/mountpoint --quiet -- /srv/complexitylib-cache", command)
        self.assertIn("ulimit -f 2097152", command)
        self.assertIn("/bin/rrsync -wo -no-del -no-overwrite -munge ", command)


class SecurityPolicyTests(unittest.TestCase):
    def test_accept_env_allowlist_excludes_code_loading_and_path_controls(self):
        pattern = accept_env_pattern()
        for safe in ("acceptenv", "acceptenv LANG", "acceptenv LC_*",
                     "acceptenv LANG LC_*"):
            with self.subTest(safe=safe):
                self.assertIsNotNone(pattern.fullmatch(safe))
        for dangerous in ("acceptenv PATH", "acceptenv LD_*", "acceptenv LD_PRELOAD",
                          "acceptenv PYTHONPATH", "acceptenv LANG LC_* PATH"):
            with self.subTest(dangerous=dangerous):
                self.assertIsNone(pattern.fullmatch(dangerous))
        policy = (INFRA / "configure-sshd.yml").read_text()
        self.assertIn("reject('match', cache_server_upload_accept_env_pattern)", policy)


@unittest.skipUnless(shutil.which("ansible-playbook"),
                     "Install infra/cache-server/requirements.txt for Ansible invariant tests")
class AnsibleInvariantTests(unittest.TestCase):
    def test_checksum_and_storage_boundaries(self):
        result = subprocess.run(
            [shutil.which("ansible-playbook"), "-i", "localhost,", "-c", "local",
             "test-host-security.yml"], cwd=INFRA, capture_output=True, text=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


@unittest.skipUnless(INTEGRATION, "Set CACHE_SERVER_INTEGRATION=1 for Linux host-boundary checks")
class HostBoundaryIntegrationTests(unittest.TestCase):
    def setUp(self):
        if not sys.platform.startswith("linux"):
            self.fail("The SSH and mount-boundary integration tests require Linux")
        if Environment is None:
            self.fail("Install infra/cache-server/requirements.txt before integration tests")
        self.sshd = shutil.which("sshd")
        self.ssh_keygen = shutil.which("ssh-keygen")
        self.temp = tempfile.TemporaryDirectory(prefix="complexitylib-cache-host-boundary-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)

    def install_fake_rrsync(self, body):
        prefix = self.base / "rsync"
        (prefix / "bin").mkdir(parents=True)
        rrsync = prefix / "bin/rrsync"
        rrsync.write_text(f"#!{sys.executable}\n{body}")
        rrsync.chmod(0o755)
        return prefix

    def write_upload_command(self, prefix, data_root, max_file_bytes=1048576):
        command = self.base / "upload-command"
        command.write_text(render(
            "upload-command.sh.j2", cache_server_rsync_prefix=str(prefix),
            cache_server_data_root=str(data_root),
            cache_server_upload_max_file_bytes=max_file_bytes))
        command.chmod(0o755)
        return command

    def test_upload_command_refuses_a_missing_dedicated_mount(self):
        if not os.access("/usr/bin/mountpoint", os.X_OK):
            self.fail("Install util-linux for upload mount-boundary tests")
        marker = self.base / "rrsync-ran"
        prefix = self.install_fake_rrsync(
            "from pathlib import Path\nPath(" + repr(str(marker)) + ").touch()\n")
        data_root = self.base / "ordinary-directory"
        data_root.mkdir()
        result = subprocess.run(
            [self.write_upload_command(prefix, data_root)], capture_output=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(marker.exists())

    def test_upload_command_caps_one_file(self):
        if not os.access("/usr/bin/mountpoint", os.X_OK):
            self.fail("Install util-linux for upload mount-boundary tests")
        output = self.base / "oversized"
        prefix = self.install_fake_rrsync(
            "import os\nwith open(os.environ['CACHE_SERVER_TEST_OUTPUT'], 'wb') as stream:\n"
            "    stream.write(b'x' * 2097152)\n")
        env = {**os.environ, "CACHE_SERVER_TEST_OUTPUT": str(output)}
        result = subprocess.run(
            [self.write_upload_command(prefix, Path("/"))], env=env,
            capture_output=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertLessEqual(output.stat().st_size, 1048576)

    def test_sshd_policy_is_valid_and_effective_only_for_upload_account(self):
        if self.sshd is None or self.ssh_keygen is None:
            self.fail("Install openssh-server and openssh-client for SSH policy tests")
        host_key = self.base / "host-key"
        subprocess.run(
            [self.ssh_keygen, "-q", "-t", "ed25519", "-N", "", "-f", host_key],
            check=True, capture_output=True, timeout=10)
        policy = render("sshd-cache-upload.conf.j2")
        config = self.base / "sshd_config"
        config.write_text(
            f"HostKey {host_key}\nPidFile {self.base / 'sshd.pid'}\n"
            "AuthorizedKeysFile none\nUsePAM no\nPermitUserEnvironment no\n"
            "AcceptEnv LANG LC_*\n" + policy)
        checked = subprocess.run(
            [self.sshd, "-t", "-f", config], capture_output=True, text=True, timeout=5)
        self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)

        def effective(user, source=config):
            result = subprocess.run(
                [self.sshd, "-T", "-f", source, "-C",
                 f"user={user},host=cache-server,addr=127.0.0.1"],
                capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            return result.stdout.splitlines()

        upload = effective("cache-upload")
        for setting in (
                "authenticationmethods publickey",
                "pubkeyacceptedalgorithms ssh-ed25519,rsa-sha2-512,rsa-sha2-256,"
                "ecdsa-sha2-nistp256,ecdsa-sha2-nistp384,ecdsa-sha2-nistp521",
                "authorizedkeysfile /var/lib/complexitylib-cache-upload/.ssh/authorized_keys",
                "authorizedkeyscommand none", "authorizedprincipalsfile /dev/null",
                "trustedusercakeys none",
                "hostbasedauthentication no",
                "forcecommand /usr/local/libexec/complexitylib-cache-upload",
                "disableforwarding yes", "permittty no", "permituserrc no",
                "permituserenvironment no"):
            self.assertIn(setting, upload)
        allowed = accept_env_pattern()
        accepted = [line for line in upload if line.startswith("acceptenv")]
        self.assertTrue(accepted)
        self.assertTrue(all(allowed.fullmatch(line) for line in accepted))
        self.assertIn("forcecommand none", effective("ordinary-user"))

        dangerous_config = self.base / "sshd_config_dangerous"
        dangerous_config.write_text(
            f"HostKey {host_key}\nPidFile {self.base / 'dangerous-sshd.pid'}\n"
            "AuthorizedKeysFile none\nUsePAM no\nPermitUserEnvironment no\n"
            "AcceptEnv LANG LC_* LD_PRELOAD PYTHONPATH PATH\n" + policy)
        dangerous = effective("cache-upload", dangerous_config)
        self.assertTrue(any(line.startswith("acceptenv") and allowed.fullmatch(line) is None
                            for line in dangerous))


def free_port():
    with socket.socket() as listener:
        listener.bind(("127.0.0.1", 0))
        return listener.getsockname()[1]


@unittest.skipUnless(INTEGRATION, "Set CACHE_SERVER_INTEGRATION=1 for Linux data-plane checks")
class IntegrationTests(unittest.TestCase):
    def setUp(self):
        if not sys.platform.startswith("linux"):
            self.fail("The restricted origin integration test requires Linux")
        if Environment is None:
            self.fail("Install infra/cache-server/requirements.txt before integration tests")
        self.rsync = RSYNC_PREFIX / "bin/rsync"
        self.rrsync = RSYNC_PREFIX / "bin/rrsync"
        for path in (self.rsync, self.rrsync):
            if not os.access(path, os.X_OK):
                self.fail(f"Missing pinned uploader {path}; run test-install-rsync.yml first")
        self.temp = tempfile.TemporaryDirectory(prefix="complexitylib-cache-origin-test-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.data = self.base / "data"
        self.data.mkdir()
        self.source = self.base / "source"
        self.source.mkdir()

        # Exercise the real rsync protocol through the forced rrsync command. Only the SSH
        # transport is replaced: no test needs a login account, private key or network service.
        self.remote_shell = self.base / "remote-shell"
        self.remote_shell.write_text(
            "#!/usr/bin/env python3\n"
            "import os, shlex, sys\n"
            "os.environ['SSH_ORIGINAL_COMMAND'] = shlex.join(sys.argv[2:])\n"
            f"os.execv({str(self.rrsync)!r}, [{str(self.rrsync)!r}, "
            f"'-wo', '-no-del', '-no-overwrite', '-munge', {str(self.data)!r}])\n")
        self.remote_shell.chmod(0o755)

    def put(self, relative, content):
        path = self.source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)

    def upload(self, *options, destination=".", expect_success=True):
        env = {key: value for key, value in os.environ.items()
               if key not in ("RSYNC_PROTECT_ARGS", "RSYNC_RSH", "RSYNC_OLD_ARGS")}
        command = [str(self.rsync), "-r", "-e", str(self.remote_shell), *options,
                   str(self.source) + "/", "test-origin:" + destination]
        result = subprocess.run(command, env=env, capture_output=True, timeout=20)
        if expect_success:
            self.assertEqual(result.returncode, 0, result.stderr.decode(errors="replace"))
        else:
            self.assertNotEqual(result.returncode, 0, "Unsafe upload unexpectedly succeeded")
        return result

    def test_real_uploads_are_immutable_and_deny_destructive_options(self):
        self.put(ARTIFACT, b"trusted artifact")
        self.upload()
        self.assertEqual((self.data / ARTIFACT).read_bytes(), b"trusted artifact")
        self.put(ARTIFACT, b"replacement must not appear")
        self.put(MAPPING, b"mapping is published after its artifact\n")
        self.upload()
        self.assertEqual((self.data / ARTIFACT).read_bytes(), b"trusted artifact")
        self.assertEqual((self.data / MAPPING).read_bytes(), b"mapping is published after its artifact\n")

        # Inplace/append do not override the server's forced --ignore-existing. They need
        # not be rejected: the property is that published bytes remain unchanged.
        for options in (("--inplace",), ("--append",)):
            with self.subTest(options=options):
                self.upload(*options)
                self.assertEqual((self.data / ARTIFACT).read_bytes(), b"trusted artifact")
                self.assertEqual((self.data / MAPPING).read_bytes(), b"mapping is published after its artifact\n")
        for options in (("--delete",), ("--backup",), ("--partial-dir=partial",), ("--delay-updates",)):
            with self.subTest(options=options):
                self.upload(*options, expect_success=False)
                self.assertEqual((self.data / ARTIFACT).read_bytes(), b"trusted artifact")
        self.upload(destination="../outside", expect_success=False)
        self.assertFalse((self.base / "outside").exists())

        # A plain --log-file on the sender logs locally and never reaches rrsync. Exercise
        # the receiver option directly to verify that it cannot append to a published file.
        env = {**os.environ, "SSH_ORIGINAL_COMMAND": f"rsync --server -r --log-file={ARTIFACT} . ."}
        result = subprocess.run([str(self.rrsync), "-wo", "-no-del", "-no-overwrite", "-munge", str(self.data)],
                                env=env, capture_output=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual((self.data / ARTIFACT).read_bytes(), b"trusted artifact")

    def test_arbitrary_commands_reads_and_symlink_overwrites_are_denied(self):
        marker = self.base / "arbitrary-shell-marker"
        env = {**os.environ, "SSH_ORIGINAL_COMMAND": f"touch {marker}"}
        result = subprocess.run([str(self.rrsync), "-wo", "-no-del", "-no-overwrite",
                                 "-munge", str(self.data)], env=env, capture_output=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(marker.exists())
        env["SSH_ORIGINAL_COMMAND"] = "rsync --server --sender -r . ."
        result = subprocess.run([str(self.rrsync), "-wo", "-no-del", "-no-overwrite",
                                 "-munge", str(self.data)], env=env, capture_output=True, timeout=5)
        self.assertNotEqual(result.returncode, 0)

        self.put(ARTIFACT, b"immutable")
        self.upload()
        (self.source / ARTIFACT).unlink()
        (self.source / ARTIFACT).symlink_to(marker)
        self.upload("-l")
        self.assertFalse((self.data / ARTIFACT).is_symlink())
        self.assertEqual((self.data / ARTIFACT).read_bytes(), b"immutable")

    @contextmanager
    def nginx(self):
        binary = shutil.which("nginx") or "/usr/sbin/nginx"
        openssl = shutil.which("openssl")
        if not os.access(binary, os.X_OK) or openssl is None:
            self.fail("nginx and openssl are required for origin integration tests")
        certificate = self.base / "certificate"
        certificate.mkdir()
        subprocess.run([openssl, "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "1",
                        "-subj", "/CN=cache.example.edu", "-keyout", str(certificate / "privkey.pem"),
                        "-out", str(certificate / "fullchain.pem")],
                       check=True, capture_output=True, timeout=20)
        http_port, https_port = free_port(), free_port()
        site = render("nginx.conf.j2", cache_server_http_port=http_port,
                      cache_server_https_port=https_port, cache_server_data_root=str(self.data),
                      cache_server_acme_root=str(self.base / "acme"),
                      cache_server_certificate_directory=str(certificate))
        # Put only the log destination under the temporary prefix; all routing and TLS
        # directives are the production template. The test owns exactly this nginx process.
        site = site.replace("/var/log/nginx/complexitylib-cache-error.log", str(self.base / "error.log"))
        config = self.base / "nginx.conf"
        config.write_text(f"pid {self.base / 'nginx.pid'};\n"
                          f"error_log {self.base / 'error.log'};\n"
                          "worker_processes 1;\nevents { worker_connections 64; }\n"
                          "http {\n"
                          + "".join(f"{kind}_temp_path {self.base / kind};\n" for kind in
                                    ("client_body", "proxy", "fastcgi", "uwsgi", "scgi"))
                          + site + "}\n")
        command = [binary, "-p", str(self.base), "-c", str(config)]
        checked = subprocess.run([*command, "-t"], capture_output=True, timeout=5)
        self.assertEqual(checked.returncode, 0, checked.stderr.decode(errors="replace"))
        with (self.base / "nginx-output.log").open("wb") as output:
            process = subprocess.Popen([*command, "-g", "daemon off;"], stdout=output, stderr=output)
            try:
                for _ in range(100):
                    if process.poll() is not None:
                        self.fail((self.base / "nginx-output.log").read_text())
                    try:
                        with socket.create_connection(("127.0.0.1", https_port), timeout=0.1):
                            break
                    except OSError:
                        time.sleep(0.05)
                else:
                    self.fail("The isolated nginx process did not become ready")
                yield http_port, https_port
            finally:
                process.terminate()
                try:
                    process.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    process.kill()
                    process.wait(timeout=5)

    def request(self, port, path, method="GET", tls=True):
        if tls:
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
            # Only this temporary self-signed integration fixture skips CA validation.
            context.check_hostname = False
            context.verify_mode = ssl.CERT_NONE
            connection = http.client.HTTPSConnection("127.0.0.1", port, context=context, timeout=5)
        else:
            connection = http.client.HTTPConnection("127.0.0.1", port, timeout=5)
        try:
            connection.request(method, path, headers={"Host": "cache.example.edu"})
            response = connection.getresponse()
            return response.status, dict(response.getheaders()), response.read()
        finally:
            connection.close()

    def test_nginx_serves_completed_objects_and_excludes_other_files(self):
        self.put(ARTIFACT, b"artifact bytes")
        self.put(MAPPING, b"mapping bytes\n")
        plus_mapping = MAPPING.replace("v4.36.0-rc2", "v4.36.0-rc2+fixture")
        self.put(plus_mapping, b"toolchain build metadata\n")
        self.upload()
        symlink = ARTIFACT.replace("0123456789abcdef", "fedcba9876543210")
        (self.data / symlink).symlink_to(self.base / "outside.txt")
        (self.base / "outside.txt").write_bytes(b"must not leak")
        hidden = str(Path(ARTIFACT).with_name(".0123456789abcdef.art.partial"))
        (self.data / hidden).write_bytes(b"incomplete")
        with self.nginx() as (http_port, https_port):
            for path, payload in ((ARTIFACT, b"artifact bytes"), (MAPPING, b"mapping bytes\n"),
                                  (plus_mapping, b"toolchain build metadata\n")):
                status, headers, body = self.request(https_port, "/" + path)
                self.assertEqual((status, body), (200, payload))
                self.assertEqual(headers["Cache-Control"], "public, max-age=31536000, immutable")
                self.assertEqual(self.request(https_port, "/" + path, method="HEAD")[0], 200)
                self.assertEqual(self.request(https_port, "/" + path, method="POST")[0], 403)
            for path in ("/", "/a0/", "/a0/cslib-community/complexitylib/", "/" + hidden,
                         "/.ssh/authorized_keys", "/" + ARTIFACT + ".tmp",
                         "/" + ARTIFACT.replace("cslib-community", "other-owner"),
                         "/" + ARTIFACT.replace("0123456789abcdef", "not-a-hash"),
                         "/" + MAPPING.replace(REVISION, "a" * 39), "/" + symlink):
                with self.subTest(path=path):
                    self.assertIn(self.request(https_port, path)[0], (403, 404))
            status, headers, body = self.request(https_port, "/healthz")
            self.assertEqual((status, body), (200, (REVISION + "\n").encode()))
            self.assertEqual(headers["Cache-Control"], "no-store")
            status, headers, _ = self.request(http_port, "/" + ARTIFACT, tls=False)
            self.assertEqual(status, 301)
            self.assertEqual(headers["Location"], "https://cache.example.edu/" + ARTIFACT)


if __name__ == "__main__":
    unittest.main()
