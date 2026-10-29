"""Exact-attempt cache selection, archive safety and transactional build restoration."""

import contextlib
import copy
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest
from unittest.mock import patch

import cache_handoff as handoff


REPOSITORY = "cslib-community/complexitylib"


class API:
    def __init__(self, sha):
        self.workflow = {"id": 7, "path": handoff.WORKFLOW_PATH, "state": "active"}
        self.runs = [{"id": 101, "run_number": 20, "run_attempt": 1, "workflow_id": 7,
                      "path": handoff.WORKFLOW_PATH, "head_sha": sha, "event": "merge_group",
                      "head_branch": "gh-readonly-queue/main/pr-1-parent",
                      "status": "completed", "conclusion": "success",
                      "repository": {"id": 9, "full_name": REPOSITORY},
                      "head_repository": {"id": 9, "full_name": REPOSITORY}}]
        self.artifact = {
            "id": 303, "name": handoff.artifact_name(sha, 101, 1), "expired": False,
            "size_in_bytes": 1000,
            "workflow_run": {"id": 101, "head_sha": sha, "repository_id": 9,
                             "head_repository_id": 9},
        }
        self.current = None
        self.calls = []

    def __call__(self, endpoint, *, paginate=False):
        self.calls.append((endpoint, paginate))
        if endpoint.endswith(handoff.WORKFLOW_FILE):
            return copy.deepcopy(self.workflow)
        if "/workflows/7/runs?" in endpoint:
            return copy.deepcopy([{"total_count": len(self.runs), "workflow_runs": self.runs}])
        if "/artifacts?" in endpoint:
            artifacts = [] if self.artifact is None else [self.artifact]
            return copy.deepcopy([{"total_count": len(artifacts), "artifacts": artifacts}])
        if "/actions/runs/" in endpoint:
            return copy.deepcopy(self.current or next(
                run for run in self.runs if endpoint.endswith(str(run["id"]))))
        raise AssertionError(f"Unexpected API request: {endpoint}")


class HandoffTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="build-handoff-test-")
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.root = self.base / "checkout"
        self.root.mkdir()
        for name in handoff.INPUTS:
            (self.root / name).write_text(name + "\n")
        (self.root / ".gitignore").write_text(".lake/\n")
        for command in (["git", "init", "-q"], ["git", "add", "."],
                        ["git", "-c", "commit.gpgsign=false", "-c", "user.name=Test",
                         "-c", "user.email=test@example.invalid",
                         "commit", "-qm", "Fixture"]):
            subprocess.run(command, cwd=self.root, check=True, capture_output=True)
        sha = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.root, text=True).strip()
        self.env = {"GITHUB_REPOSITORY": REPOSITORY, "GITHUB_SHA": sha,
                    "GITHUB_EVENT_NAME": "merge_group", "GITHUB_RUN_ID": "101",
                    "GITHUB_RUN_ATTEMPT": "1", "RUNNER_OS": "Linux", "RUNNER_ARCH": "X64",
                    "ImageOS": "ubuntu24", "ImageVersion": "20261017.1",
                    "GITHUB_OUTPUT": str(self.base / "outputs")}
        self.build = self.root / ".lake/build"
        (self.build / "lib/lean").mkdir(parents=True)
        (self.build / "lib/lean/Example.olean").write_bytes(b"compiled")
        os.utime(self.build / "lib/lean/Example.olean", (1_700_000_000, 1_700_000_000))
        (self.build / "lib/lean/Example.trace").write_bytes(b"trace")
        (self.build / "bin").mkdir()
        (self.build / "bin/check").write_bytes(b"executable")
        (self.build / "bin/check").chmod(0o755)
        self.output = self.base / "packed"
        self.api = API(sha)

    def pack(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return handoff.pack(self.root, self.output, self.env)

    def download(self, repository, run_id, name, destination):
        self.assertEqual((repository, run_id, name),
                         (REPOSITORY, 101, handoff.artifact_name(self.env["GITHUB_SHA"], 101, 1)))
        for source in self.output.iterdir():
            shutil.copyfile(source, destination / source.name)

    def restore(self, downloader=None):
        env = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main"}
        with contextlib.redirect_stdout(io.StringIO()):
            handoff.restore(self.root, env, api=self.api, downloader=downloader or self.download)

    def metadata(self, change):
        path = self.output / "metadata.json"
        data = json.loads(path.read_text())
        change(data)
        path.write_text(json.dumps(data))

    def replace_archive(self, members):
        archive = self.output / "build.tar.gz"
        size = 0
        with tarfile.open(archive, "w:gz") as bundle:
            for name, kind, data in members:
                member = tarfile.TarInfo(name)
                member.type = kind
                member.size = len(data) if kind == tarfile.REGTYPE else 0
                member.linkname = "/tmp/outside" if kind in (tarfile.SYMTYPE, tarfile.LNKTYPE) else ""
                size += member.size
                bundle.addfile(member, io.BytesIO(data))
        self.metadata(lambda meta: meta.update(archive={
            "sha256": handoff.digest(archive), "files": len(members), "bytes": max(1, size),
            "compressed_bytes": archive.stat().st_size,
        }))

    def test_roundtrip_preserves_executable_and_replaces_hardlinks_without_modifying_cache(self):
        shared = self.base / "shared-artifact"
        shared.write_bytes(b"shared")
        os.link(shared, self.build / "lib/lean/Linked.olean")
        name = self.pack()
        self.assertIn(f"artifact-name={name}", (self.base / "outputs").read_text())
        with tarfile.open(self.output / "build.tar.gz") as bundle:
            self.assertTrue(all(member.isfile() for member in bundle))
        # The consumer's old output is another hardlink to an immutable cache entry.
        old = self.base / "old-artifact"
        old.write_bytes(b"old")
        (self.build / "lib/lean/Example.olean").unlink()
        os.link(old, self.build / "lib/lean/Example.olean")
        (self.build / "stale-file").write_text("old output absent from producer")
        self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual((self.build / "lib/lean/Example.olean").stat().st_mtime, 1_700_000_000)
        self.assertEqual(old.read_bytes(), b"old")
        self.assertEqual(shared.read_bytes(), b"shared")
        self.assertEqual((self.build / "lib/lean/Linked.olean").read_bytes(), b"shared")
        self.assertTrue(os.access(self.build / "bin/check", os.X_OK))
        self.assertFalse((self.build / "stale-file").exists())
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])
        listings = [url for url, paginate in self.api.calls if "/runs?" in url]
        self.assertEqual(len(listings), 2)
        self.assertTrue(all("event=merge_group" in url and "status=" not in url for url in listings))

    def test_pack_requires_clean_matching_checkout_and_known_platform(self):
        for changes in ({"GITHUB_SHA": "f" * 40}, {"GITHUB_EVENT_NAME": "pull_request"},
                        {"ImageOS": ""}, {"GITHUB_RUN_ATTEMPT": "0"},
                        {"DISABLE_BUILD_HANDOFF": "1"}, {"DISABLE_BUILD_HANDOFF": "true"}):
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                handoff.pack(self.root, self.output, {**self.env, **changes})
        for index, allowed in enumerate(("0", "false", "FALSE", "no")):
            with self.subTest(allowed=allowed), contextlib.redirect_stdout(io.StringIO()):
                self.assertTrue(handoff.pack(
                    self.root, self.base / f"packed-{index}-{allowed}",
                    {**self.env, "DISABLE_BUILD_HANDOFF": allowed}))
        (self.base / "outputs").unlink()
        (self.root / "lean-toolchain").write_text("changed")
        with self.assertRaises(handoff.Rejected):
            self.pack()
        self.assertFalse((self.base / "outputs").exists())

    def test_kill_switch_disables_restore_before_contacting_api(self):
        for value in ("1", "true", "TRUE", "yes"):
            env = {**self.env, "GITHUB_EVENT_NAME": "push", "GITHUB_REF": "refs/heads/main",
                   "DISABLE_BUILD_HANDOFF": value}
            with self.subTest(value=value), self.assertRaises(handoff.Rejected):
                handoff.restore(
                    self.root, env,
                    api=lambda *args, **kwargs: self.fail("API called when handoff disabled"),
                    downloader=lambda *args: self.fail("Downloaded when handoff disabled"),
                )

    def test_pack_rejects_symlinks_and_empty_build(self):
        link = self.build / "linked-dir"
        link.symlink_to(self.base, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.pack()
        link.unlink()
        shutil.rmtree(self.build)
        self.build.mkdir()
        with self.assertRaises(handoff.Rejected):
            self.pack()

    def test_identity_mismatch_or_unsuccessful_run_never_downloads(self):
        cases = ({"head_sha": "f" * 40}, {"event": "pull_request"},
                 {"event": "workflow_dispatch"}, {"workflow_id": 8},
                 {"path": ".github/workflows/fake.yml"}, {"head_branch": "feature"},
                 {"head_repository": {"id": 10, "full_name": REPOSITORY}},
                 {"repository": {"id": 9, "full_name": "other/repo"}},
                 {"run_attempt": 0}, {"status": "in_progress", "conclusion": None},
                 {"conclusion": "failure"}, {"conclusion": "cancelled"})
        for changes in cases:
            self.api = API(self.env["GITHUB_SHA"])
            self.api.runs[0].update(changes)
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                self.restore(lambda *args: self.fail("Downloaded before validating the run"))

    def test_latest_failed_run_and_current_rerun_override_old_success(self):
        self.api.runs.append({**self.api.runs[0], "id": 102, "run_number": 21,
                              "conclusion": "failure"})
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.api = API(self.env["GITHUB_SHA"])
        self.api.current = {**self.api.runs[0], "run_attempt": 2,
                            "status": "in_progress", "conclusion": None}
        with self.assertRaises(handoff.Rejected):
            self.restore()

    def test_missing_expired_or_wrong_attempt_artifact_is_a_miss(self):
        for changes in (None, {"expired": True}, {"name": "old-attempt"},
                        {"size_in_bytes": handoff.MAX_ARCHIVE_BYTES + handoff.MAX_METADATA_BYTES + 1},
                        {"workflow_run": {"id": 100}}):
            self.api = API(self.env["GITHUB_SHA"])
            if changes is None:
                self.api.artifact = None
            else:
                self.api.artifact.update(changes)
            with self.subTest(changes=changes), self.assertRaises(handoff.Rejected):
                self.restore(lambda *args: self.fail("Downloaded invalid artifact"))

    def test_configuration_platform_attempt_and_digest_mismatch_leave_old_outputs(self):
        self.pack()
        original = (self.output / "metadata.json").read_bytes()
        changes = (lambda meta: meta.update(source_sha="f" * 40),
                   lambda meta: meta["inputs"].update({"lean-toolchain": "different"}),
                   lambda meta: meta["platform"].update(RUNNER_ARCH="ARM64"),
                   lambda meta: meta["platform"].update(ImageVersion="different"),
                   lambda meta: meta["producer"].update(run_attempt=2),
                   lambda meta: meta["archive"].update(sha256="0" * 64),
                   lambda meta: meta["archive"].update(files=handoff.MAX_FILES + 1))
        for change in changes:
            (self.output / "metadata.json").write_bytes(original)
            self.metadata(change)
            with self.assertRaises(handoff.Rejected):
                self.restore()
            self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_unsafe_tar_members_are_rejected_before_install(self):
        self.pack()
        bad = [("/tmp/escape", tarfile.REGTYPE, b"x"),
               (".lake/build/../../escape", tarfile.REGTYPE, b"x"),
               (".lake/build/./dot", tarfile.REGTYPE, b"x"),
               (".lake/build//double", tarfile.REGTYPE, b"x"),
               (".lake/build/a\\b", tarfile.REGTYPE, b"x"),
               (".lake/packages/injection", tarfile.REGTYPE, b"x"),
               (".lake/build/link", tarfile.SYMTYPE, b""),
               (".lake/build/link", tarfile.LNKTYPE, b""),
               (".lake/build/device", tarfile.CHRTYPE, b""),
               (".lake/build/fifo", tarfile.FIFOTYPE, b""),
               (".lake/build/directory", tarfile.DIRTYPE, b"")]
        for member in bad:
            self.replace_archive([member])
            with self.subTest(member=member), self.assertRaises(handoff.Rejected):
                self.restore()
        duplicate = (".lake/build/repeated", tarfile.REGTYPE, b"x")
        self.replace_archive([duplicate, duplicate])
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_run_or_artifact_change_during_download_does_not_install(self):
        self.pack()
        for kind in ("run", "attempt", "failure", "artifact", "expired"):
            self.api = API(self.env["GITHUB_SHA"])
            def download(*args):
                self.download(*args)
                if kind == "run":
                    self.api.runs.append({**self.api.runs[0], "id": 102, "run_number": 21})
                elif kind == "attempt":
                    self.api.runs[0]["run_attempt"] = 2
                elif kind == "failure":
                    self.api.runs[0]["conclusion"] = "failure"
                elif kind == "artifact":
                    self.api.artifact["id"] = 304
                else:
                    self.api.artifact["expired"] = True
            with self.subTest(kind=kind), self.assertRaises(handoff.Rejected):
                self.restore(download)
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"trace")

    def test_symlink_build_boundary_is_not_followed(self):
        self.pack()
        target = self.base / "outside"
        self.build.rename(target)
        self.build.symlink_to(target, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertTrue(self.build.is_symlink())
        self.assertEqual((target / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_symlink_lake_boundary_is_not_followed(self):
        self.pack()
        target = self.base / "outside-lake"
        self.build.parent.rename(target)
        self.build.parent.symlink_to(target, target_is_directory=True)
        with self.assertRaises(handoff.Rejected):
            self.restore()
        self.assertEqual((target / "build/lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual([path.name for path in target.iterdir()], ["build"])

    def test_missing_consumer_build_is_restored(self):
        self.pack()
        shutil.rmtree(self.build)
        self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")

    def test_download_failure_and_truncated_archive_leave_complete_old_build(self):
        self.pack()
        def failed_download(*args):
            raise subprocess.TimeoutExpired("gh", 120)
        with self.assertRaises(subprocess.TimeoutExpired):
            self.restore(failed_download)
        archive = self.output / "build.tar.gz"
        archive.write_bytes(archive.read_bytes()[:20])
        self.metadata(lambda meta: meta["archive"].update(
            sha256=handoff.digest(archive), compressed_bytes=archive.stat().st_size))
        with self.assertRaises((EOFError, tarfile.TarError)):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"compiled")
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"trace")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def test_failed_install_rolls_back_complete_old_build(self):
        self.pack()
        (self.build / "lib/lean/Example.olean").write_bytes(b"old compiled")
        (self.build / "lib/lean/Example.trace").write_bytes(b"old trace")
        rename = Path.rename
        def fail_install(path, target):
            if "unpacked" in path.parts and path.name == "build":
                raise OSError("simulated install failure")
            return rename(path, target)
        with patch.object(Path, "rename", fail_install), self.assertRaises(OSError):
            self.restore()
        self.assertEqual((self.build / "lib/lean/Example.olean").read_bytes(), b"old compiled")
        self.assertEqual((self.build / "lib/lean/Example.trace").read_bytes(), b"old trace")
        self.assertEqual([path.name for path in self.build.parent.iterdir()], ["build"])

    def test_cli_errors_are_optional_cache_misses(self):
        for error in (handoff.Rejected("not green"), OSError("transport"),
                      subprocess.TimeoutExpired("gh", 60), ValueError("invalid JSON")):
            with self.subTest(error=error), patch("sys.argv", ["cache_handoff.py", "restore"]), \
                    patch.object(handoff, "restore", side_effect=error), \
                    contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(handoff.main(), 0)
                self.assertIn("continuing without this optional cache", output.getvalue())


if __name__ == "__main__":
    unittest.main()
