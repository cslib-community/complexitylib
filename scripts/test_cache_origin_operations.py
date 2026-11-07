"""Controls for publisher credentials, local capacity checks and queued alerts."""

import argparse
import base64
from email import message_from_bytes
import importlib.util
import io
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch


EXAMPLES = Path(__file__).resolve().parents[1] / "tools/cache-origin/examples"


def load(name, filename):
    spec = importlib.util.spec_from_file_location(name, EXAMPLES / filename)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


health = load("cache_health", "cache-origin-health.py")
alert = load("cache_alert", "cache-origin-alert.py")


class CapacityAndAlertTests(unittest.TestCase):
    def test_mount_bytes_and_inode_failures_are_visible(self):
        good = SimpleNamespace(f_bavail=30, f_blocks=100, f_favail=40, f_files=100)
        full_bytes = SimpleNamespace(f_bavail=20, f_blocks=100, f_favail=40, f_files=100)
        full_inodes = SimpleNamespace(f_bavail=30, f_blocks=100, f_favail=0, f_files=100)
        with patch.object(health.os.path, "ismount", return_value=False), patch("sys.stdout", io.StringIO()) as out:
            self.assertEqual(health.main(), 1)
            self.assertIn("not mounted", out.getvalue())
        for usage, expected in ((good, 0), (full_bytes, 1), (full_inodes, 1)):
            with (patch.object(health.os.path, "ismount", return_value=True),
                  patch.object(health.os, "statvfs", return_value=usage, create=True),
                  patch("sys.stdout", io.StringIO())):
                self.assertEqual(health.main(), expected)

    def test_failed_unit_uses_local_queue_without_log_or_secret_contents(self):
        with (patch.object(alert.sys, "argv", ["alert", "cache-origin-gc.service"]),
              patch.object(alert.socket, "getfqdn", return_value="fixture.invalid"),
              patch.object(alert.subprocess, "run") as run):
            alert.main()
        self.assertEqual(run.call_args.args[0], ["/usr/sbin/sendmail", "-t", "-oi"])
        mail = message_from_bytes(run.call_args.kwargs["input"])
        self.assertEqual(mail["To"], "edemaine@mit.edu")
        self.assertIn("cache-origin-gc.service", mail["Subject"])
        self.assertNotIn("auth.json", mail.get_payload())
        with patch.object(alert.sys, "argv", ["alert", "bad\nTo: injected"]), self.assertRaises(SystemExit):
            alert.main()

    def test_failed_mail_submission_is_not_reported_as_success(self):
        with (patch.object(alert.sys, "argv", ["alert", "cache-origin.service"]),
              patch.object(alert.subprocess, "run", side_effect=subprocess.CalledProcessError(1, "sendmail")),
              self.assertRaises(subprocess.CalledProcessError)):
            alert.main()


@unittest.skipUnless(os.name == "posix", "credential installer uses Unix ownership")
class CredentialTests(unittest.TestCase):
    def setUp(self):
        self.credential = load("cache_credential", "publisher-credential.py")

    def test_nonroot_and_unsafe_existing_paths_fail_before_generation(self):
        args = argparse.Namespace(user="cache-publisher", group="root", handoff=Path("unused"),
                                  password_file=Path("unused"), rotate=False)
        with patch.object(self.credential.os, "geteuid", return_value=1000), self.assertRaisesRegex(ValueError, "root"):
            self.credential.install(args)

    @unittest.skipUnless(shutil.which("htpasswd"), "apache2-utils required")
    @unittest.skipUnless(hasattr(os, "geteuid") and os.geteuid() == 0, "root required for installed file owner test")
    def test_generation_rotation_hash_and_private_handoff(self):
        import grp
        group = grp.getgrgid(os.getegid()).gr_name
        with tempfile.TemporaryDirectory(prefix="cache-credential-") as temporary:
            root = Path(temporary)
            root.chmod(0o700)
            args = argparse.Namespace(user="cache-publisher", group=group, handoff=root / "handoff",
                                      password_file=root / "htpasswd", rotate=False)
            with patch("sys.stdout", io.StringIO()) as out:
                self.credential.install(args)
                text = args.handoff.read_text()
                token = next(line.split("=", 1)[1] for line in text.splitlines() if line.startswith("CACHE_SERVER_PASSWORD="))
                self.assertEqual(len(base64.urlsafe_b64decode(token + "=")), 32)
                self.assertNotIn(token, out.getvalue())
            self.assertEqual(stat.S_IMODE(args.handoff.stat().st_mode), 0o600)
            self.assertEqual(stat.S_IMODE(args.password_file.stat().st_mode), 0o640)
            self.assertTrue(args.password_file.read_text().startswith("cache-publisher:$2y$12$"))
            verified = subprocess.run(["htpasswd", "-vi", str(args.password_file), args.user],
                                      input=(token + "\n").encode(), capture_output=True)
            self.assertEqual(verified.returncode, 0)
            old = args.password_file.read_bytes()
            args.handoff = root / "second-handoff"
            with self.assertRaisesRegex(ValueError, "rotate"):
                self.credential.install(args)
            self.assertEqual(args.password_file.read_bytes(), old)
            args.rotate = True
            with patch("sys.stdout", io.StringIO()):
                self.credential.install(args)
            rejected = subprocess.run(["htpasswd", "-vi", str(args.password_file), args.user],
                                      input=(token + "\n").encode(), capture_output=True)
            self.assertNotEqual(rejected.returncode, 0)
            with self.assertRaisesRegex(ValueError, "new handoff"):
                self.credential.install(args)


if __name__ == "__main__":
    unittest.main()
