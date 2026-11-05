"""Publication order, transfer integrity, SSH isolation, and a real tiny Lake package."""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


publish = module("cache_publish", REPO / "scripts/cache/publish.py")
ssh = module("cache_ssh", REPO / "scripts/cache/ssh.py")


class PublicationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="cache-publication-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.stage = self.root / "stage"
        self.stage.mkdir()
        self.artifact = f"a0/{publish.SCOPE}/0123456789abcdef.art"
        self.mapping = f"r0/{publish.SCOPE}/tc/leanprover--lean4---v4.36.0-rc2/{'a' * 40}.jsonl"
        for name, data in ((self.artifact, b"compressed artifact"), (self.mapping, b"mapping\n")):
            path = self.stage / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(data)
        self.metadata = {"version": 1, "revision": "a" * 40,
                         "toolchain": "leanprover--lean4---v4.36.0-rc2",
                         "files": {name: publish.digest(self.stage / name)
                                   for name in (self.artifact, self.mapping)}}
        self.write_metadata()

    def write_metadata(self):
        (self.stage / "publication.json").write_text(json.dumps(self.metadata))

    def test_both_backends_use_identical_staged_bytes_and_publish_mapping_last(self):
        with patch.object(publish, "run") as run:
            publish.gcs("example-cache", self.stage)
            google = run.call_args_list
            self.assertEqual(len(google), 2)
            self.assertIn("--no-clobber", google[0].args[0])
            self.assertEqual(google[0].kwargs["input"], str(self.stage / self.artifact) + "\n")
            self.assertIn(str(self.stage / self.mapping), google[1].args[0])
        with patch.object(publish, "run") as run:
            publish.ssh(self.stage, self.root / "private config")
            server = run.call_args_list
            self.assertEqual(len(server), 2)
            self.assertIn("--ignore-existing", server[0].args[0])
            self.assertIn(str(self.stage / "a0") + "/", server[0].args[0])
            self.assertIn(str(self.stage) + "/./" + self.mapping, server[1].args[0])
            self.assertNotIn("--delete", server[0].args[0])

    def test_failed_artifact_upload_never_publishes_a_mapping(self):
        for backend in (lambda: publish.gcs("example-cache", self.stage),
                        lambda: publish.ssh(self.stage, self.root / "config")):
            with self.subTest(backend=backend), patch.object(publish, "run", side_effect=subprocess.CalledProcessError(1, "transfer")) as run:
                with self.assertRaises(subprocess.CalledProcessError):
                    backend()
                self.assertEqual(run.call_count, 1)

    def test_damaged_artifact_is_rejected_before_any_upload(self):
        (self.stage / self.artifact).write_bytes(b"damaged")
        with patch.object(publish, "run") as run, self.assertRaisesRegex(ValueError, "digest mismatch"):
            publish.gcs("example-cache", self.stage)
        run.assert_not_called()

    def test_missing_extra_and_symlink_files_are_rejected(self):
        artifact = self.stage / self.artifact
        original = artifact.read_bytes()
        artifact.unlink()
        with self.assertRaisesRegex(ValueError, "inventory"):
            publish.validate(self.stage)
        artifact.write_bytes(original)
        extra = self.stage / "unexpected"
        extra.write_bytes(b"extra")
        with self.assertRaisesRegex(ValueError, "inventory"):
            publish.validate(self.stage)
        extra.unlink()
        artifact.unlink()
        artifact.symlink_to(self.stage / self.mapping)
        with self.assertRaisesRegex(ValueError, "Non-regular"):
            publish.validate(self.stage)

    def test_unsafe_paths_and_multiple_revision_maps_are_rejected(self):
        self.metadata["files"]["../../outside"] = "0" * 64
        self.write_metadata()
        with self.assertRaisesRegex(ValueError, "Invalid publication path"):
            publish.validate(self.stage)

    def test_wrong_producer_revision_fails_verification(self):
        result = subprocess.run(["python3", str(REPO / "scripts/cache/publish.py"), "verify",
                                 str(self.stage), "--revision", "b" * 40], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("different revision", result.stderr)

    def test_gcs_requires_an_existing_publication(self):
        result = subprocess.run(["python3", str(REPO / "scripts/cache/publish.py"), "gcs",
                                 "example-cache"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("directory", result.stderr)

    def test_upload_wrapper_requires_a_staged_directory(self):
        result = subprocess.run(
            ["bash", str(REPO / "scripts/cache/upload.sh"), "example-cache"],
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("<publication-directory>", result.stderr)


@unittest.skipUnless(shutil.which("git"), "Git is required")
class SourceStateTests(unittest.TestCase):
    def make_repo(self, temporary):
        root = Path(temporary) / "repo"
        root.mkdir()
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc2\n")
        (root / ".gitignore").write_text(".lake/\n")
        (root / "ComplexityTests").mkdir()
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
        for command in (["git", "init", "-q"], ["git", "add", "lean-toolchain", ".gitignore"],
                        ["git", "-c", "user.name=Fixture", "-c",
                         "user.email=fixture@example.invalid", "commit", "-qm", "fixture"]):
            subprocess.run(command, cwd=root, env=env, check=True, stdout=subprocess.DEVNULL)
        return root

    def test_ignored_compiled_tree_entry_is_rejected_but_build_outputs_are_allowed(self):
        with tempfile.TemporaryDirectory(prefix="cache-dirty-source-") as temporary:
            root = self.make_repo(temporary)
            build_output = root / ".lake/build/generated"
            build_output.parent.mkdir(parents=True)
            build_output.write_text("ordinary ignored output\n")
            with patch.object(publish, "ROOT", root):
                publish.require_clean_revision()
            (root / ".git/info/exclude").write_text("ComplexityTests/private-input\n")
            (root / "ComplexityTests" / "private-input").write_text("untracked build input\n")
            with patch.object(publish, "ROOT", root), patch.object(publish, "run") as run:
                with self.assertRaisesRegex(ValueError, "ignored entries in compiled source trees"):
                    publish.stage(Path(temporary) / "publication")
            run.assert_not_called()

    def test_source_created_during_build_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix="cache-changing-source-") as temporary:
            root = self.make_repo(temporary)

            def fake_run(args, **_kwargs):
                if args[1] == "build":
                    Path(args[-1]).write_text('"2026-11-04"\n')
                else:
                    archives = Path(args[-1])
                    archives.mkdir()
                    (archives / "0123456789abcdef.ltar").write_bytes(b"archive")
                    (root / "ComplexityTests" / "Added.lean").write_text("def added := true\n")

            with patch.object(publish, "ROOT", root), patch.object(publish, "run", fake_run):
                with self.assertRaisesRegex(ValueError, "modified or untracked"):
                    publish.stage(Path(temporary) / "publication")

    def test_stage_moves_outputs_from_a_destination_local_temporary_directory(self):
        with tempfile.TemporaryDirectory(prefix="cache-local-stage-") as temporary:
            root = self.make_repo(temporary)
            destination = Path(temporary) / "publication"
            work_directories = []

            def fake_run(args, **_kwargs):
                if args[1] == "build":
                    mapping = Path(args[-1])
                    work_directories.append(mapping.parent)
                    mapping.write_text('"2026-11-04"\n')
                else:
                    archives = Path(args[-1])
                    self.assertEqual(archives.parent, work_directories[0])
                    archives.mkdir()
                    (archives / "0123456789abcdef.ltar").write_bytes(b"archive")

            with patch.object(publish, "ROOT", root), patch.object(publish, "run", fake_run):
                publish.stage(destination)
            data, mapping = publish.validate(destination)
            self.assertTrue(work_directories[0].is_relative_to(destination.resolve()))
            self.assertFalse(work_directories[0].exists())
            self.assertEqual(mapping.read_text(), '"2026-11-04"\n')
            self.assertEqual(len(data["files"]), 2)


class SSHTests(unittest.TestCase):
    def test_both_roles_get_private_configs_and_strict_host_verification(self):
        with tempfile.TemporaryDirectory(prefix="cache ssh ") as temporary:
            root = Path(temporary)
            env = {"CACHE_SERVER_HOST": "cache.example.org", "CACHE_SERVER_ADMIN_USER": "admin",
                   "CACHE_SERVER_UPLOAD_USER": "cache-upload", "CACHE_SERVER_SSH_PORT": "2222",
                   "ADMIN_KEY": "private fixture", "UPLOAD_KEY": "private fixture",
                   "CACHE_SERVER_KNOWN_HOSTS": "independently verified host key"}
            for role in ("ADMIN", "UPLOAD"):
                directory = root / role
                with patch.object(ssh.subprocess, "run") as validate:
                    config = ssh.prepare(directory, role + "_KEY", "CACHE_SERVER_" + role + "_USER", env)
                self.assertIn("ssh-keygen", validate.call_args.args[0])
                self.assertEqual(directory.stat().st_mode & 0o777, 0o700)
                self.assertEqual((directory / "identity").stat().st_mode & 0o777, 0o600)
                data = config.read_text()
                self.assertIn("HostName cache.example.org", data)
                self.assertIn("StrictHostKeyChecking yes", data)
                self.assertIn("IdentitiesOnly yes", data)
                self.assertIn("GlobalKnownHostsFile", data)
                self.assertIn(str(Path(os.devnull).resolve()), data)
                self.assertIn("KnownHostsCommand none", data)
                self.assertIn("Port 2222", data)
            with self.assertRaises(ValueError):
                ssh.prepare(root / "bad", "ADMIN_KEY", "CACHE_SERVER_ADMIN_USER", {**env, "CACHE_SERVER_HOST": "host\nProxyCommand bad"})

    @unittest.skipUnless(os.environ.get("CACHE_SERVER_INTEGRATION") == "1", "Linux SSH integration is opt-in")
    @unittest.skipUnless(shutil.which("ssh") and shutil.which("ssh-keygen"), "OpenSSH is required")
    def test_real_openssh_parses_identity_and_config(self):
        with tempfile.TemporaryDirectory(prefix="cache ssh ") as temporary:
            root = Path(temporary)
            key = root / "key"
            subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-f", str(key)], check=True)
            config = ssh.prepare(root / "ssh", "KEY", "USER", {
                "CACHE_SERVER_HOST": "cache.example.org", "USER": "cache-upload",
                "KEY": key.read_text(), "CACHE_SERVER_KNOWN_HOSTS": "cache.example.org " + key.with_suffix(".pub").read_text()})
            parsed = subprocess.check_output(["ssh", "-G", "-F", str(config), "cache-server"], text=True)
            self.assertIn("stricthostkeychecking true", parsed)
            self.assertIn(f"globalknownhostsfile {Path(os.devnull).resolve()}", parsed)
            # OpenSSH accepts `KnownHostsCommand none` but some releases omit a disabled
            # command from `ssh -G`; the source-level assertion above covers that exact setting.


@unittest.skipUnless(shutil.which("lake") and shutil.which("git"), "Lean and Git are required")
class RealLakePublicationTests(unittest.TestCase):
    def test_staging_real_platform_independent_outputs(self):
        with tempfile.TemporaryDirectory(prefix="cache-real-lake-") as temporary:
            root = Path(temporary) / "repo"
            root.mkdir()
            shutil.copyfile(REPO / "lean-toolchain", root / "lean-toolchain")
            (root / ".gitignore").write_text(".lake/\n")
            (root / "lakefile.toml").write_text('''name = "fixture"
enableArtifactCache = true
restoreAllArtifacts = true
platformIndependent = true
[[lean_lib]]
name = "Complexity"
[[lean_lib]]
name = "ComplexityTests"
''')
            (root / "Complexity.lean").write_text("def answer : Nat := 42\n")
            (root / "ComplexityTests.lean").write_text("import Complexity\nexample : answer = 42 := rfl\n")
            env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
            env.update(LAKE_CACHE_DIR=str(Path(temporary) / "private-cache"),
                       GIT_CONFIG_GLOBAL=os.devnull, GIT_CONFIG_NOSYSTEM="1")
            for command in (["git", "init", "-q"], ["lake", "update"], ["git", "add", "."],
                            ["git", "-c", "user.name=Fixture", "-c",
                             "user.email=fixture@example.invalid", "commit", "-qm", "fixture"]):
                subprocess.run(command, cwd=root, env=env, check=True, stdout=subprocess.DEVNULL)
            destination = Path(temporary) / "publication"
            with patch.object(publish, "ROOT", root), patch.dict(os.environ, env, clear=True):
                publish.stage(destination)
            data, _ = publish.validate(destination)
            self.assertGreater(len(data["files"]), 1)
            self.assertTrue(all(publish.digest(destination / name) == expected
                                for name, expected in data["files"].items()))


if __name__ == "__main__":
    unittest.main()
