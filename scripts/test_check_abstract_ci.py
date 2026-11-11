"""Exact-source CI policy, provenance verification and workflow boundary regressions (#432, #673)."""

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import check_abstract_ci as gate


REPOSITORY = "cslib-community/complexitylib"
SHA = "a" * 40
ROOT = Path(__file__).resolve().parents[1]


def run(**changes):
    result = {
        "id": 101, "run_number": 20, "run_attempt": 1, "workflow_id": 7,
        "path": gate.WORKFLOW_PATH, "head_sha": SHA, "event": "push", "head_branch": "main",
        "status": "completed", "conclusion": "success",
        "repository": {"id": 9, "full_name": REPOSITORY},
        "head_repository": {"id": 9, "full_name": REPOSITORY},
    }
    result.update(changes)
    return result


def abstracts_run(**changes):
    return run(
        id=202, run_number=30, workflow_id=8, path=gate.ABSTRACTS_WORKFLOW_PATH, **changes,
    )


class API:
    def __init__(self, runs=None, abstract_runs=None):
        self.runs = [run()] if runs is None else runs
        self.abstract_runs = [abstracts_run()] if abstract_runs is None else abstract_runs
        self.workflow = {"id": 7, "path": gate.WORKFLOW_PATH,
                         "name": gate.WORKFLOW_NAME, "state": "active"}
        self.abstracts_workflow = {"id": 8, "path": gate.ABSTRACTS_WORKFLOW_PATH,
                                   "name": gate.ABSTRACTS_WORKFLOW_NAME, "state": "active"}
        self.listings = []
        self.current = None
        self.main_reads = []
        self.calls = []

    def __call__(self, endpoint, *, paginate=False):
        self.calls.append((endpoint, paginate))
        if endpoint.endswith("git/ref/heads/main"):
            return self.main_reads.pop(0) if self.main_reads else {
                "ref": "refs/heads/main", "object": {"sha": SHA}}
        if endpoint.endswith("/" + gate.WORKFLOW_FILE):
            return self.workflow
        if endpoint.endswith("/" + gate.ABSTRACTS_WORKFLOW_FILE):
            return self.abstracts_workflow
        if "/workflows/7/runs?" in endpoint:
            if self.listings:
                return self.listings.pop(0)
            return [{"total_count": len(self.runs), "workflow_runs": self.runs}]
        if "/workflows/8/runs?" in endpoint:
            return [{"total_count": len(self.abstract_runs), "workflow_runs": self.abstract_runs}]
        if "/actions/runs/" in endpoint:
            if self.current is not None and endpoint.endswith(str(self.current["id"])):
                return self.current
            if self.current is not None and len(self.runs) == 1 and endpoint.endswith(str(self.runs[0]["id"])):
                return self.current
            all_runs = [*self.runs, *self.abstract_runs]
            return next(r for r in all_runs if endpoint.endswith(str(r["id"])))
        raise AssertionError(f"Unexpected API request: {endpoint}")


class ExactSourceTests(unittest.TestCase):
    def check(self, api):
        return gate.check_once(REPOSITORY, SHA, api=api)

    def test_success_uses_authoritative_workflow_and_unfiltered_exact_sha_list(self):
        api = API()
        self.assertEqual(self.check(api)["id"], 101)
        lists = [(url, paginate) for url, paginate in api.calls if "runs?" in url]
        self.assertEqual(len(lists), 2)
        for url, paginate in lists:
            self.assertIn(f"head_sha={SHA}&event=push&branch=main", url)
            self.assertNotIn("status=", url)  # Older green runs must not hide a later failure.
            self.assertTrue(paginate)

    def test_all_identity_mismatches_reject(self):
        cases = {
            "different SHA": {"head_sha": "b" * 40},
            "PR merge": {"event": "pull_request"},
            "manual Lean run": {"event": "workflow_dispatch"},
            "different branch": {"head_branch": "feature"},
            "different workflow ID": {"workflow_id": 8},
            "same name wrong file": {"path": ".github/workflows/fake.yml"},
            "different repository": {"repository": {"id": 10, "full_name": "fork/repo"}},
            "fork head": {"head_repository": {"id": 10, "full_name": REPOSITORY}},
            "missing head": {"head_repository": {}},
            "invalid attempt": {"run_attempt": 0},
            "boolean ID": {"id": True},
        }
        for label, changes in cases.items():
            with self.subTest(label=label), self.assertRaises(gate.Rejected):
                self.check(API([run(**changes)]))

    def test_workflow_metadata_must_match(self):
        for key, value in [("path", "fake.yml"), ("name", "PDFs"),
                           ("state", "disabled_manually"), ("id", 0)]:
            api = API()
            api.workflow[key] = value
            with self.subTest(key=key), self.assertRaises(gate.Rejected):
                self.check(api)

    def test_missing_and_pending_never_authorize(self):
        with self.assertRaises(gate.Pending):
            self.check(API([]))
        for status in ["queued", "in_progress", "waiting", "pending", "requested"]:
            with self.subTest(status=status), self.assertRaises(gate.Pending):
                self.check(API([run(status=status, conclusion=None)]))

    def test_every_unsuccessful_completed_conclusion_rejects(self):
        for conclusion in ["failure", "cancelled", "timed_out", "skipped", "neutral",
                           "action_required", "stale", None]:
            with self.subTest(conclusion=conclusion), self.assertRaises(gate.Rejected):
                self.check(API([run(conclusion=conclusion)]))

    def test_latest_run_number_wins_over_older_success_and_opaque_id(self):
        older = run(id=900, run_number=19)
        latest = run(id=101, run_number=20, conclusion="failure")
        with self.assertRaises(gate.Rejected):
            self.check(API([older, latest]))

    def test_current_attempt_overrides_stale_success_in_listing(self):
        api = API()
        api.current = run(run_attempt=2, status="in_progress", conclusion=None)
        with self.assertRaises(gate.Pending):
            self.check(api)
        api.current = run(run_attempt=2, conclusion="cancelled")
        with self.assertRaises(gate.Rejected):
            self.check(api)

    def test_successful_rerun_is_allowed_after_latest_listing_confirms_it(self):
        api = API()
        api.current = run(run_attempt=2)
        api.listings = [[{"total_count": 1, "workflow_runs": [run()]}],
                        [{"total_count": 1, "workflow_runs": [run(run_attempt=2)]}]]
        self.assertEqual(self.check(api)["run_attempt"], 2)

    def test_new_run_or_attempt_during_check_rejects(self):
        for later in [run(id=102, run_number=21), run(run_attempt=2),
                      run(status="queued", conclusion=None)]:
            api = API()
            api.listings = [[{"total_count": 1, "workflow_runs": [run()]}],
                            [{"total_count": 1, "workflow_runs": [later]}]]
            with self.subTest(later=later), self.assertRaises(gate.Rejected):
                self.check(api)

    def test_pagination_and_incomplete_response(self):
        api = API([run(id=100, run_number=19, conclusion="failure"), run()])
        pages = [{"total_count": 2, "workflow_runs": [api.runs[0]]},
                 {"total_count": 2, "workflow_runs": [api.runs[1]]}]
        api.listings = [pages, pages]
        self.assertEqual(self.check(api)["id"], 101)
        api = API()
        api.listings = [[{"total_count": 2, "workflow_runs": [run()]}]]
        with self.assertRaises(gate.Rejected):
            self.check(api)

    def test_duplicate_or_ambiguous_runs_reject(self):
        for runs in [[run(), run()], [run(), run(id=102)]]:
            with self.assertRaises(gate.Rejected):
                self.check(API(runs))

    def test_main_freshness_before_and_after_ci_read(self):
        stale = {"ref": "refs/heads/main", "object": {"sha": "b" * 40}}
        for reads in [[stale], [{"ref": "refs/heads/main", "object": {"sha": SHA}}, stale]]:
            api = API()
            api.main_reads = reads
            with self.subTest(reads=reads), self.assertRaises(gate.Rejected):
                self.check(api)

    def test_pending_wait_is_bounded_and_failure_does_not_wait(self):
        now = [0.0]
        def sleep(seconds):
            now[0] += seconds
        with self.assertRaises(gate.Pending):
            gate.wait_for_success(REPOSITORY, SHA, 31, api=API([]),
                                  clock=lambda: now[0], sleep=sleep)
        self.assertEqual(now[0], 31)
        with self.assertRaises(gate.Rejected):
            gate.wait_for_success(REPOSITORY, SHA, 1200, api=API([run(conclusion="failure")]),
                                  clock=lambda: now[0], sleep=sleep)
        self.assertEqual(now[0], 31)

    def test_pending_attempt_can_finish_during_bounded_wait(self):
        api = API([run(run_attempt=2, status="in_progress", conclusion=None)])
        now = [0.0]
        def finish(seconds):
            now[0] += seconds
            api.runs = [run(run_attempt=2)]
        result = gate.wait_for_success(REPOSITORY, SHA, 60, api=api,
                                       clock=lambda: now[0], sleep=finish)
        self.assertEqual(result["run_attempt"], 2)
        self.assertEqual(now[0], 30)

    def test_cli_fails_closed_when_api_transport_or_json_fails(self):
        for error in [subprocess.CalledProcessError(1, ["gh", "api"]),
                      subprocess.TimeoutExpired(["gh", "api"], 60), ValueError("Invalid JSON")]:
            with self.subTest(error=error), patch.object(gate, "wait_for_success", side_effect=error), \
                    patch("sys.argv", ["check_abstract_ci.py", "--repository", REPOSITORY, "--sha", SHA]), \
                    contextlib.redirect_stderr(io.StringIO()) as stderr:
                self.assertEqual(gate.main(), 1)
                self.assertIn("publication denied", stderr.getvalue())

    def test_transport_only_uses_get_and_paginates(self):
        with patch.object(subprocess, "run") as invoke:
            invoke.return_value.stdout = "[]"
            gate.gh_get("repos/example/repo/actions/runs", paginate=True)
        command = invoke.call_args.args[0]
        self.assertIn("GET", command)
        self.assertIn("--paginate", command)
        self.assertIn("--slurp", command)
        self.assertEqual(command[command.index("--hostname") + 1], "github.com")


def write_fixture_artifact(
    directory: Path,
    *,
    sha: str = SHA,
    repository: str = REPOSITORY,
    event: str = "push",
    ref: str = "refs/heads/main",
    dirty: bool = False,
    run_id: int = 202,
    run_attempt: int | str = 1,
    run_url: str | None = None,
    only_cook_levin: bool = False,
    inputs: list[dict] | None = None,
    tamper_input: bool = False,
    tamper_pdf: bool = False,
    extra_file: str | None = None,
    marker: bytes = b"",
) -> None:
    manifest_data = json.loads((ROOT / "abstracts/catalogue.json").read_text(encoding="utf-8"))
    entries = manifest_data["entries"]
    if only_cook_levin:
        entries = [entry for entry in entries if entry["id"] == "cook-levin"]
    cat = directory / "catalogue.pdf"
    cat.write_bytes(b"%PDF-catalogue" + marker)
    cat_digest = hashlib.sha256(cat.read_bytes()).hexdigest()
    documents = []
    for entry in entries:
        doc_id = entry["id"]
        pdf = directory / f"{doc_id}.pdf"
        pdf.write_bytes(f"%PDF-{doc_id}".encode("utf-8") + marker)
        pdf_digest = hashlib.sha256(pdf.read_bytes()).hexdigest()
        documents.append({"id": doc_id, "pdf": pdf.name, "pdf_sha256": pdf_digest})
    if tamper_pdf:
        (directory / "cook-levin.pdf").write_bytes(b"%PDF-tampered")
    if extra_file:
        (directory / extra_file).write_bytes(b"extra")
    if inputs is None:
        rel_inputs = ("abstracts/catalogue.json", *gate.REQUIRED_PRODUCER_INPUTS)
        inputs = [
            {
                "path": rel,
                "sha256": ("0" * 64 if tamper_input and rel == "abstracts/catalogue.json"
                           else hashlib.sha256((ROOT / rel).read_bytes()).hexdigest()),
            }
            for rel in rel_inputs
        ]
    provenance = {
        "source_sha": sha,
        "repository": repository,
        "event": event,
        "ref": ref,
        "source_dirty": dirty,
        "run_url": (f"https://github.com/{repository}/actions/runs/{run_id}"
                    if run_url is None else run_url),
        "run_attempt": str(run_attempt),
        "catalogue": {"pdf": "catalogue.pdf", "pdf_sha256": cat_digest},
        "documents": documents,
        "inputs": inputs,
    }
    (directory / "provenance.json").write_text(json.dumps(provenance))


class DownloadAndProvenanceTests(unittest.TestCase):
    def test_download_verified_abstracts_succeeds_and_populates_destination(self):
        api = API()
        downloads = []

        def fake_downloader(repository, run_id, artifact_name, destination):
            downloads.append((repository, run_id, artifact_name))
            write_fixture_artifact(destination)

        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "abstracts"
            lean_r, abs_r = gate.download_verified_abstracts(
                REPOSITORY, SHA, dest, 0, api=api, downloader=fake_downloader,
            )
            self.assertEqual(lean_r["id"], 101)
            self.assertEqual(abs_r["id"], 202)
            self.assertEqual(downloads, [(REPOSITORY, 202, f"formal-abstracts-{SHA}-1")])
            self.assertTrue((dest / "catalogue.pdf").is_file())
            self.assertTrue((dest / "cook-levin.pdf").is_file())
            self.assertTrue((dest / "provenance.json").is_file())

    def test_download_waits_for_pending_abstracts_or_lean_run(self):
        api = API(
            runs=[run(status="in_progress", conclusion=None)],
            abstract_runs=[abstracts_run(run_attempt=2, status="in_progress", conclusion=None)],
        )
        now = [0.0]

        def finish(seconds):
            now[0] += seconds
            api.runs = [run()]
            api.abstract_runs = [abstracts_run(run_attempt=2)]

        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "abstracts"
            _, abs_r = gate.download_verified_abstracts(
                REPOSITORY, SHA, dest, 60, api=api,
                downloader=lambda _r, _id, _name, d: write_fixture_artifact(d, run_attempt=2),
                clock=lambda: now[0], sleep=finish,
            )
            self.assertEqual(abs_r["run_attempt"], 2)
            self.assertEqual(now[0], 30)

    def test_provenance_and_digest_mismatches_reject_and_leave_no_unverified_output(self):
        cases = {
            "wrong sha": {"sha": "b" * 40},
            "wrong repo": {"repository": "fork/repo"},
            "pull request": {"event": "pull_request"},
            "wrong ref": {"ref": "refs/heads/feature"},
            "dirty source": {"dirty": True},
            "incomplete catalogue": {"only_cook_levin": True},
            "wrong run_attempt": {"run_attempt": 99},
            "wrong run_url": {"run_url": "https://example.com/build"},
            "empty inputs": {"inputs": []},
            "tampered input digest": {"tamper_input": True},
            "tampered pdf": {"tamper_pdf": True},
            "unexpected file": {"extra_file": "retired.pdf"},
        }
        for label, kwargs in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                dest = Path(tmp) / "abstracts"
                with self.assertRaises(gate.Rejected):
                    gate.download_verified_abstracts(
                        REPOSITORY, SHA, dest, 0, api=API(),
                        downloader=lambda _r, _id, _name, d, kw=kwargs: write_fixture_artifact(d, **kw),
                    )
                self.assertFalse(dest.exists())

    def test_existing_destination_survives_rename_or_verification_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "abstracts"
            dest.mkdir()
            write_fixture_artifact(dest, marker=b"-previous")
            previous_bytes = (dest / "catalogue.pdf").read_bytes()

            with patch.object(Path, "rename", side_effect=OSError("simulated rename failure")), \
                    self.assertRaises(OSError):
                gate.download_verified_abstracts(
                    REPOSITORY, SHA, dest, 0, api=API(),
                    downloader=lambda _r, _id, _name, d: write_fixture_artifact(d, marker=b"-new"),
                )
            self.assertTrue(dest.is_dir())
            self.assertEqual((dest / "catalogue.pdf").read_bytes(), previous_bytes)

            with self.assertRaises(gate.Rejected):
                gate.download_verified_abstracts(
                    REPOSITORY, SHA, dest, 0, api=API(),
                    downloader=lambda _r, _id, _name, d: write_fixture_artifact(
                        d, tamper_pdf=True, marker=b"-bad",
                    ),
                )
            self.assertTrue(dest.is_dir())
            self.assertEqual((dest / "catalogue.pdf").read_bytes(), previous_bytes)

    def test_rerun_during_download_rejects_failure_and_installs_newer_attempt(self):
        # Probe 1: downloader starts Lean attempt 2 (in_progress) and Abstracts attempt 2 (failure).
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "abstracts"
            api = API()

            def failing_rerun_downloader(_r, _id, _name, d):
                write_fixture_artifact(d, run_attempt=1)
                api.runs = [run(run_attempt=2, status="in_progress", conclusion=None)]
                api.abstract_runs = [abstracts_run(run_attempt=2, conclusion="failure")]

            with self.assertRaises(gate.Rejected):
                gate.download_verified_abstracts(
                    REPOSITORY, SHA, dest, 60, api=api, downloader=failing_rerun_downloader,
                )
            self.assertFalse(dest.exists())

        # Probe 2: downloader sees Abstracts rerun complete at attempt 2 during attempt 1 download;
        # the gate re-downloads attempt 2 and installs attempt 2 rather than attempt 1.
        with tempfile.TemporaryDirectory() as tmp:
            dest = Path(tmp) / "abstracts"
            api = API()
            downloads = []

            def upgrading_downloader(repository, run_id, artifact_name, d):
                downloads.append((repository, run_id, artifact_name))
                attempt = 1 if len(downloads) == 1 else 2
                write_fixture_artifact(d, run_attempt=attempt, marker=f"-attempt{attempt}".encode())
                if len(downloads) == 1:
                    api.abstract_runs = [abstracts_run(run_attempt=2)]

            _, abs_r = gate.download_verified_abstracts(
                REPOSITORY, SHA, dest, 0, api=api, downloader=upgrading_downloader,
            )
            self.assertEqual(abs_r["run_attempt"], 2)
            self.assertEqual(
                downloads,
                [
                    (REPOSITORY, 202, f"formal-abstracts-{SHA}-1"),
                    (REPOSITORY, 202, f"formal-abstracts-{SHA}-2"),
                ],
            )
            self.assertIn(b"-attempt2", (dest / "catalogue.pdf").read_bytes())


FAKE_GH = r'''#!/usr/bin/env python3
import json, os, pathlib, shutil, sys
root = pathlib.Path(os.environ["FAKE_ROOT"])
config = json.loads((root / "config.json").read_text())
args = sys.argv[1:]
if args[0] == "api":
    endpoint = next(a for a in args if a.startswith("repos/"))
    if endpoint.endswith("git/ref/heads/main"):
        print(json.dumps({"ref": "refs/heads/main", "object": {"sha": config["sha"]}}))
    elif endpoint.endswith("/lean_action_ci.yml"):
        print(json.dumps(config["lean_workflow"]))
    elif endpoint.endswith("/abstracts.yml"):
        print(json.dumps(config["abstracts_workflow"]))
    elif "/workflows/7/runs?" in endpoint:
        print(json.dumps([{"total_count": 1, "workflow_runs": [config["lean_run"]]}]))
    elif "/workflows/8/runs?" in endpoint:
        print(json.dumps([{"total_count": 1, "workflow_runs": [config["abstracts_run"]]}]))
    elif endpoint.endswith("/actions/runs/101"):
        print(json.dumps(config["lean_run"]))
    elif endpoint.endswith("/actions/runs/202"):
        print(json.dumps(config["abstracts_run"]))
    else:
        raise SystemExit("Unexpected API: " + endpoint)
elif args[:2] == ["run", "download"]:
    run_id = args[2]
    name = args[args.index("--name") + 1]
    dest = pathlib.Path(args[args.index("--dir") + 1])
    (root / "downloads").write_text(json.dumps({"run_id": run_id, "name": name}))
    for src in (root / "artifact-src").iterdir():
        shutil.copy2(src, dest / src.name)
else:
    raise SystemExit("Unexpected gh command: " + " ".join(args))
'''


class WorkflowBoundaryTests(unittest.TestCase):
    def test_abstracts_workflow_is_read_only_and_never_publishes_releases(self):
        workflow = (ROOT / ".github/workflows/abstracts.yml").read_text()
        self.assertIn("  pull_request:\n", workflow)
        self.assertIn('- "scripts/proof_lengths.py"', workflow)
        self.assertIn("permissions:\n  contents: read", workflow)
        self.assertNotIn("contents: write", workflow)
        self.assertNotIn("\n  publish:\n", workflow)
        self.assertNotIn("gh release", workflow)
        self.assertIn("name: formal-abstracts-${{ github.sha }}-${{ github.run_attempt }}", workflow)
        self.assertIn("abstracts/build/*.pdf", workflow)
        self.assertIn("abstracts/build/provenance.json", workflow)
        for rel in ("README.md", "AGENTS.md", "CONTRIBUTING.md", "abstracts/README.md",
                    "guide/CslibFrontierGuide.lean", ".github/workflows/docs.yml"):
            text = (ROOT / rel).read_text()
            self.assertNotIn("releases/download/formal-abstracts", text)
            self.assertIn("https://www.cslib.io/cslib-frontier/abstracts/", text)

    def test_cli_download_dir_boundary_with_fake_gh(self):
        cases = [
            ("lean_failed", {"lean_run": run(conclusion="failure")}, False),
            ("abstracts_failed", {"abstracts_run": abstracts_run(conclusion="failure")}, False),
            ("tampered_pdf", {"tamper_pdf": True}, False),
            ("success", {}, True),
        ]
        for label, overrides, ok in cases:
            with self.subTest(label=label), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "bin").mkdir()
                gh = root / "bin/gh"
                gh.write_text(FAKE_GH)
                gh.chmod(0o755)
                src = root / "artifact-src"
                src.mkdir()
                write_fixture_artifact(
                    src, run_attempt=2, tamper_pdf=overrides.get("tamper_pdf", False),
                )
                api = API()
                (root / "config.json").write_text(json.dumps({
                    "sha": SHA,
                    "lean_workflow": api.workflow,
                    "abstracts_workflow": api.abstracts_workflow,
                    "lean_run": overrides.get("lean_run", run()),
                    "abstracts_run": overrides.get("abstracts_run", abstracts_run(run_attempt=2)),
                }))
                dest = root / "doc/abstracts"
                env = {**os.environ, "PATH": str(root / "bin") + os.pathsep + os.environ["PATH"],
                       "FAKE_ROOT": tmp, "GITHUB_REPOSITORY": REPOSITORY, "GITHUB_SHA": SHA}
                result = subprocess.run(
                    ["python3", "-B", str(Path(gate.__file__).resolve()),
                     "--download-dir", str(dest)],
                    cwd=root, env=env, capture_output=True, text=True, timeout=20,
                )
                self.assertEqual(result.returncode == 0, ok, result.stderr)
                self.assertEqual((dest / "catalogue.pdf").is_file(), ok)
                if ok:
                    recorded = json.loads((root / "downloads").read_text())
                    self.assertEqual(recorded, {"run_id": "202", "name": f"formal-abstracts-{SHA}-2"})


if __name__ == "__main__":
    unittest.main()
