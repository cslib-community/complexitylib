"""Publication order, transfer integrity, and a real tiny Lake package."""

import importlib.util
import base64
from contextlib import redirect_stdout
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import tarfile
import unittest
from unittest.mock import patch

REPO = Path(__file__).resolve().parents[1]
TEST_PASSWORD = base64.urlsafe_b64encode(bytes(range(32))).decode().rstrip("=")


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


publish = module("cache_publish", REPO / "scripts/cache/publish.py")


class WorkflowContractTests(unittest.TestCase):
    def test_publication_archive_retention_is_default_off_and_reversible(self):
        text = (REPO / ".github/workflows/lean_action_ci.yml").read_text()
        guide = (REPO / "scripts/cache/README.md").read_text()
        lean = text.split("  lean-checks:\n", 1)[1].split("\n  ci-checks:\n", 1)[0]
        build = lean.split('      - name: "lake build"', 1)[1].split("      - name:", 1)[0]
        test = lean.split('      - name: "lake test"', 1)[1].split("      - name:", 1)[0]
        lint = lean.split('      - name: "lake lint"', 1)[1].split("      - name:", 1)[0]
        ordinary = lean.split("      - name: Save .lake to the Actions cache", 1)[1].split(
            "      - name:", 1)[0]
        experiment = lean.split(
            "      - name: Save .lake after cache publication (experiment)", 1)[1].split(
            "      - name:", 1)[0]
        self.assertIn("id: build", build)
        self.assertIn("id: test", test)
        self.assertIn("id: lint", lint)
        ordinary_at = lean.index("      - name: Save .lake to the Actions cache")
        stage_at = lean.index("      - name: Stage cache publication")
        handoff_at = lean.index("      - name: Hand off staged files to the enabled publishers")
        experiment_at = lean.index(
            "      - name: Save .lake after cache publication (experiment)")
        self.assertLess(ordinary_at, stage_at)
        self.assertLess(stage_at, handoff_at)
        self.assertLess(handoff_at, experiment_at)
        self.assertIn("vars.RETAIN_PUBLICATION_ARCHIVES != 'true'", ordinary)
        self.assertIn("steps.test.outcome == 'failure'", ordinary)
        self.assertIn("steps.lint.outcome == 'failure'", ordinary)
        self.assertIn("vars.RETAIN_PUBLICATION_ARCHIVES == 'true'", experiment)
        self.assertIn("Actions string comparisons are case-insensitive", text)
        self.assertIn("case-insensitive, so any capitalization", guide)
        self.assertIn("!cancelled()", experiment)
        self.assertIn("steps.build.outcome == 'success'", experiment)
        action = "uses: actions/cache/save@caa296126883cff596d87d8935842f9db880ef25"
        for save in (ordinary, experiment):
            self.assertIn(action, save)
            self.assertIn("path: ./.lake", save)
            self.assertIn("key: ${{ steps.lake-cache.outputs.cache-primary-key }}", save)


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
        def inspect_upload(args, **kwargs):
            self.assertEqual(args[0], "curl")
            self.assertIn("--retry", args)
            self.assertIn("--fail-with-body", args)
            self.assertEqual(args[-1], "https://cache.example.edu/publish/" + "a" * 40)
            self.assertNotIn(TEST_PASSWORD, " ".join(args))
            self.assertEqual(kwargs["input"], f'user = "publisher:{TEST_PASSWORD}"\n')
            package = Path(args[args.index("--upload-file") + 1])
            probe = "Content-Type: " + publish.HTTP_PROBE in args
            names = [self.mapping] if probe else sorted(self.metadata["files"])
            with tarfile.open(package) as archive:
                self.assertEqual(archive.getnames(), ["publication.json", *names])
                for name in archive.getnames():
                    self.assertEqual(archive.extractfile(name).read(), (self.stage / name).read_bytes())
            return subprocess.CompletedProcess(args, 22 if probe else 0, stdout="415" if probe else "201")
        with (
            patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD),
            patch.object(publish, "run", side_effect=inspect_upload) as run,
        ):
            publish.http("https://cache.example.edu", self.stage)
            self.assertEqual(run.call_count, 2)

    def test_failed_artifact_upload_never_publishes_a_mapping(self):
        for backend in (lambda: publish.gcs("example-cache", self.stage),
                        lambda: publish.http("https://cache.example.edu", self.stage)):
            with self.subTest(backend=backend), patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD), patch.object(publish, "run", side_effect=subprocess.CalledProcessError(1, "transfer")) as run:
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
        result = subprocess.run([sys.executable, str(REPO / "scripts/cache/publish.py"), "verify",
                                 str(self.stage), "--revision", "b" * 40], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("different revision", result.stderr)

    def test_gcs_requires_an_existing_publication(self):
        result = subprocess.run([sys.executable, str(REPO / "scripts/cache/publish.py"), "gcs",
                                 "example-cache"], capture_output=True, text=True)
        self.assertEqual(result.returncode, 2)
        self.assertIn("directory", result.stderr)

    def test_upload_wrapper_requires_a_staged_directory(self):
        result = subprocess.run(
            ["bash", (REPO / "scripts/cache/upload.sh").as_posix(), "example-cache"],
            capture_output=True, text=True)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertIn("<publication-directory>", result.stderr)

    def test_http_rejects_insecure_or_credentialed_endpoints_before_upload(self):
        for endpoint in ("http://cache.example.edu", "https://user@cache.example.edu",
                         "https://cache.example.edu/a/path", "https://cache.example.edu?query"):
            with self.subTest(endpoint=endpoint), patch.object(publish, "run") as run:
                with self.assertRaisesRegex(ValueError, "HTTPS origin"):
                    publish.http(endpoint, self.stage)
                run.assert_not_called()

    def test_http_rejects_missing_or_injected_credentials_without_upload(self):
        for user, password in (("", "secret"), ("publisher", ""), ("bad:user", "secret"),
                               ("publisher", "secret\nurl = injected"), ("publisher", "short"),
                               ("publisher", TEST_PASSWORD + "="), ("publisher", TEST_PASSWORD[:-1] + "B"),
                               ("publisher", "x" * 44), ("publisher", "?" * 43)):
            with (
                self.subTest(user=user),
                patch.dict(os.environ, CACHE_SERVER_USER=user, CACHE_SERVER_PASSWORD=password),
                patch.object(publish, "run") as run,
            ):
                with self.assertRaisesRegex(ValueError, "CACHE_SERVER"):
                    publish.http("https://cache.example.edu", self.stage)
                run.assert_not_called()

    def test_http_keeps_generated_token_out_of_error_command(self):
        password = TEST_PASSWORD
        def failed_upload(args, **kwargs):
            self.assertNotIn(password, " ".join(args))
            self.assertEqual(kwargs["input"], f'user = "publisher:{password}"\n')
            raise subprocess.CalledProcessError(22, args)
        with (
            patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=password),
            patch.object(publish, "run", side_effect=failed_upload),
        ):
            with self.assertRaises(subprocess.CalledProcessError) as caught:
                publish.http("https://cache.example.edu", self.stage)
            self.assertNotIn(password, str(caught.exception))

    def test_http_requires_exact_201_acknowledgement(self):
        for status in ("200", "301", "302", "201"):
            with (
                self.subTest(status=status),
                patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD),
                patch.object(publish, "run", side_effect=[subprocess.CompletedProcess([], 22, stdout="415"),
                                                        subprocess.CompletedProcess([], 0, stdout=status)]) as run,
            ):
                if status == "201":
                    publish.http("https://cache.example.edu", self.stage)
                else:
                    with self.assertRaisesRegex(ValueError, "HTTP 201"):
                        publish.http("https://cache.example.edu", self.stage)
                self.assertNotIn("--location", run.call_args.args[0])

    def test_incremental_upload_omits_existing_payload_but_keeps_complete_inventory(self):
        requests = []
        def upload(args, **kwargs):
            media_type = args[args.index("--header") + 1]
            requests.append(media_type)
            with tarfile.open(args[args.index("--upload-file") + 1]) as archive:
                self.assertEqual(archive.getnames(), ["publication.json", self.mapping])
                self.assertEqual(json.load(archive.extractfile("publication.json")), self.metadata)
            if len(requests) == 1:
                Path(args[args.index("--output") + 1]).write_text(json.dumps({
                    "version": 1, "revision": self.metadata["revision"], "missing": []}))
            return subprocess.CompletedProcess(args, 0, stdout="200" if len(requests) == 1 else "201")
        with patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD), \
                patch.object(publish, "run", side_effect=upload):
            publish.http("https://cache.example.edu", self.stage)
        self.assertEqual(requests, ["Content-Type: " + publish.HTTP_PROBE,
                                    "Content-Type: " + publish.HTTP_DELTA])

    def test_gc_race_retries_one_full_publication(self):
        requests = []
        def upload(args, **kwargs):
            with tarfile.open(args[args.index("--upload-file") + 1]) as archive:
                requests.append(archive.getnames())
            Path(args[args.index("--output") + 1]).write_text(json.dumps({
                "version": 1, "revision": self.metadata["revision"], "missing": []}))
            status = ["200", "412", "201"][len(requests) - 1]
            return subprocess.CompletedProcess(args, 22 if status == "412" else 0, stdout=status)
        with patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD), \
                patch.object(publish, "run", side_effect=upload):
            publish.http("https://cache.example.edu", self.stage)
        self.assertEqual(requests, [["publication.json", self.mapping]] * 2 +
                         [["publication.json", *sorted(self.metadata["files"])]])

    def test_probe_rejections_never_downgrade_except_unsupported_media_type(self):
        for status in ("201", "301", "400", "401", "403", "404", "409", "412", "500"):
            with self.subTest(status=status), \
                    patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD), \
                    patch.object(publish, "run", return_value=subprocess.CompletedProcess([], 22, stdout=status)) as run:
                with self.assertRaisesRegex(ValueError, "probe failed"):
                    publish.http("https://cache.example.edu", self.stage)
                self.assertEqual(run.call_count, 1)

    def test_probe_response_must_name_only_unique_inventory_archives(self):
        for missing in ([self.mapping], ["../../secret"], [self.artifact, self.artifact], [None]):
            with self.subTest(missing=missing):
                response = self.root / "response"
                response.write_text(json.dumps({"version": 1, "revision": self.metadata["revision"],
                                                "missing": missing}))
                with self.assertRaisesRegex(ValueError, "missing-archive"):
                    publish.missing_archives(response, self.metadata, self.mapping)

    def test_transport_failure_cannot_be_mistaken_for_unsupported_server(self):
        with patch.dict(os.environ, CACHE_SERVER_USER="publisher", CACHE_SERVER_PASSWORD=TEST_PASSWORD), \
                patch.object(publish, "run", return_value=subprocess.CompletedProcess([], 60, stdout="415")) as run:
            with self.assertRaises(subprocess.CalledProcessError):
                publish.http("https://cache.example.edu", self.stage)
            self.assertEqual(run.call_count, 1)


@unittest.skipUnless(shutil.which("git"), "Git is required")
class SourceStateTests(unittest.TestCase):
    def test_report_inside_publication_is_rejected_before_staging(self):
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary) / "publication"
            with self.assertRaisesRegex(ValueError, "outside the publication"):
                publish.stage(destination, destination / "metrics.json")
            self.assertFalse(destination.exists())

    def make_repo(self, temporary):
        root = Path(temporary) / "repo"
        root.mkdir()
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc2\n")
        (root / ".gitignore").write_text(".lake/\n")
        (root / "CslibFrontierTests").mkdir()
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
            (root / ".git/info/exclude").write_text("CslibFrontierTests/private-input\n")
            (root / "CslibFrontierTests" / "private-input").write_text("untracked build input\n")
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
                    (root / "CslibFrontierTests" / "Added.lean").write_text("def added := true\n")

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
name = "CslibFrontier"
[[lean_lib]]
name = "CslibFrontierTests"
''')
            (root / "CslibFrontier.lean").write_text("def answer : Nat := 42\n")
            (root / "CslibFrontierTests.lean").write_text("import CslibFrontier\nexample : answer = 42 := rfl\n")
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
            # Simulate a restored Actions build tree without its module archives or shared cache.
            # The mapping build must pack these warm outputs without recompiling them.
            outputs = {path: (path.stat().st_mtime_ns, publish.digest(path))
                       for path in (root / ".lake/build").rglob("*.olean")}
            self.assertEqual(len(outputs), 2)
            for path in (root / ".lake/build").rglob("*.ltar"):
                path.unlink()
            shutil.rmtree(env["LAKE_CACHE_DIR"])
            reports = []
            for name in ("missing-archives", "retained-archives"):
                # Actions retains build outputs but excludes the toolchain's mutable cache.
                shutil.rmtree(env["LAKE_CACHE_DIR"], ignore_errors=True)
                retained = {path: (path.stat().st_mtime_ns, publish.digest(path))
                            for path in (root / ".lake/build").rglob("*.ltar")}
                target = Path(temporary) / name
                report = Path(temporary) / (name + ".json")
                with (patch.object(publish, "ROOT", root),
                      patch.dict(os.environ, env, clear=True)):
                    publish.stage(target, report)
                measured = json.loads(report.read_text())
                reports.append(measured)
                self.assertEqual(measured["mapping_entries"], 2)
                self.assertEqual(measured["staged_artifacts"], 2)
                self.assertEqual(measured["archives_after"]["count"], 2)
                self.assertTrue(all(phase["status"] == "success"
                                    and phase["wall_seconds"] >= 0 for phase in measured["phases"]))
                publish.validate(target)  # Diagnostic JSON must never enter the public inventory.
                self.assertEqual(outputs, {path: (path.stat().st_mtime_ns, publish.digest(path))
                                           for path in outputs})
                self.assertEqual(retained, {path: (path.stat().st_mtime_ns, publish.digest(path))
                                            for path in retained})
            self.assertEqual(reports[0]["archives_before"]["count"], 0)
            self.assertEqual(reports[1]["archives_before"]["count"], 2)


class StagePhaseTests(unittest.TestCase):
    def test_failed_command_keeps_its_exception_and_reports_the_phase(self):
        phases, output = [], io.StringIO()
        failure = subprocess.CalledProcessError(23, ["lake", "build"])
        with redirect_stdout(output), self.assertRaises(subprocess.CalledProcessError) as raised:
            with publish.stage_phase("mapping and archive build", phases):
                raise failure
        self.assertIs(raised.exception, failure)
        self.assertEqual(phases[0]["status"], "failed")
        self.assertIn("mapping and archive build failed", output.getvalue())

    def test_resource_module_is_optional(self):
        phases = []
        with patch.object(publish, "resource", None), redirect_stdout(io.StringIO()):
            with publish.stage_phase("fixture", phases):
                pass
        self.assertEqual(phases[0]["status"], "success")
        self.assertNotIn("child_user_seconds", phases[0])


if __name__ == "__main__":
    unittest.main()
