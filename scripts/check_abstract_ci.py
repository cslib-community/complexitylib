#!/usr/bin/env python3
"""Require authoritative exact-source CI and provenance before publishing formal-abstract PDFs.

Use the workflow-file endpoint, not a check name or a success-filtered run list. The
largest workflow run_number selects the latest run; its current run_attempt must
have completed successfully. A previous green attempt never overrides a rerun.
Only push/main validation from this repository counts. When --download-dir is given,
also require the exact-source Formal abstract PDFs run, download its immutable
run-attempt artifact, and verify provenance.json and every PDF's SHA-256 digest.

Source: the two codebase reviews recorded in issue #432, issue #673, and GitHub's REST API:
https://docs.github.com/en/rest/actions/workflow-runs
https://docs.github.com/en/actions/reference/workflows-and-actions/variables
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from urllib.parse import urlencode


WORKFLOW_FILE = "lean_action_ci.yml"
WORKFLOW_PATH = f".github/workflows/{WORKFLOW_FILE}"
WORKFLOW_NAME = "Lean Action CI"

ABSTRACTS_WORKFLOW_FILE = "abstracts.yml"
ABSTRACTS_WORKFLOW_PATH = f".github/workflows/{ABSTRACTS_WORKFLOW_FILE}"
ABSTRACTS_WORKFLOW_NAME = "Formal abstract PDFs"

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_MANIFEST = ROOT / "abstracts/catalogue.json"
REQUIRED_PRODUCER_INPUTS = (
    "scripts/build_abstracts.py",
    "scripts/abstract_to_tex.py",
    "scripts/proof_lengths.py",
)


class Rejected(RuntimeError):
    """The available evidence does not authorize publication."""


class Pending(Rejected):
    """Evidence is missing or a current attempt is still running."""


def gh_get(endpoint: str, *, paginate: bool = False):
    command = [
        "gh", "api", "--hostname", "github.com", "--method", "GET",
        "-H", "Accept: application/vnd.github+json",
        "-H", "X-GitHub-Api-Version: 2022-11-28", endpoint,
    ]
    if paginate:
        command += ["--paginate", "--slurp"]
    result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=60)
    return json.loads(result.stdout)


def gh_download_artifact(repository: str, run_id: int, artifact_name: str, destination: Path,
                         timeout: int = 120) -> None:
    command = [
        "gh", "run", "download", str(run_id),
        "--repo", repository,
        "--name", artifact_name,
        "--dir", str(destination),
    ]
    subprocess.run(command, check=True, capture_output=True, text=True, timeout=timeout)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def positive(value) -> bool:
    return type(value) is int and value > 0


def check_identity(
    run: dict,
    repository: str,
    sha: str,
    workflow_id: int,
    workflow_path: str = WORKFLOW_PATH,
    label: str = "Lean",
) -> None:
    require(run.get("head_sha") == sha, f"{label} run source SHA mismatch")
    require(run.get("event") == "push" and run.get("head_branch") == "main",
            f"{label} run is not a push to main")
    require(run.get("workflow_id") == workflow_id, f"Wrong {label} workflow ID")
    require(run.get("path", "").split("@", 1)[0] == workflow_path, f"Wrong {label} workflow path")
    repo, head = run.get("repository", {}), run.get("head_repository", {})
    require(repo.get("full_name") == repository and head.get("full_name") == repository,
            f"{label} run repository mismatch")
    require(positive(repo.get("id")) and repo.get("id") == head.get("id"),
            f"{label} run head is from another repository")
    require(all(positive(run.get(field)) for field in ("id", "run_number", "run_attempt")),
            f"Malformed {label} run identity")


def latest_run(
    api,
    repository: str,
    sha: str,
    workflow_id: int,
    workflow_path: str = WORKFLOW_PATH,
    label: str = "Lean",
) -> dict:
    query = urlencode({"head_sha": sha, "event": "push", "branch": "main", "per_page": 100})
    pages = api(f"repos/{repository}/actions/workflows/{workflow_id}/runs?{query}", paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed workflow-run pages")
    runs = []
    for page in pages:
        require(isinstance(page.get("workflow_runs"), list), "Malformed workflow-run list")
        runs.extend(page["workflow_runs"])
    require(all(page.get("total_count") == len(runs) for page in pages),
            "Incomplete or changing workflow-run listing")
    if not runs:
        raise Pending(f"No exact-source {label} push/main run exists")
    for run in runs:
        check_identity(run, repository, sha, workflow_id, workflow_path, label)
    require(len({run["id"] for run in runs}) == len(runs), "Duplicate workflow runs")
    require(len({run["run_number"] for run in runs}) == len(runs), "Ambiguous latest workflow run")
    return max(runs, key=lambda run: run["run_number"])


def check_workflow_once(
    repository: str,
    sha: str,
    workflow_file: str = WORKFLOW_FILE,
    workflow_path: str = WORKFLOW_PATH,
    workflow_name: str = WORKFLOW_NAME,
    label: str = "Lean",
    *,
    api=gh_get,
    require_current_main: bool = True,
) -> dict:
    require(bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)),
            "Invalid repository")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", sha)), "Invalid source SHA")
    if require_current_main:
        main = api(f"repos/{repository}/git/ref/heads/main")
        require(main.get("ref") == "refs/heads/main" and main.get("object", {}).get("sha") == sha,
                "Artifact source is no longer current main")
    workflow = api(f"repos/{repository}/actions/workflows/{workflow_file}")
    require(workflow.get("path") == workflow_path and workflow.get("name") == workflow_name
            and workflow.get("state") == "active" and positive(workflow.get("id")),
            f"Authoritative {label} workflow is missing, disabled or changed")
    workflow_id = workflow["id"]
    selected = latest_run(api, repository, sha, workflow_id, workflow_path, label)
    # A run-list response can lag the latest rerun. GET the run, not a historical
    # /attempts/{number} endpoint, before accepting its current conclusion.
    current = api(f"repos/{repository}/actions/runs/{selected['id']}")
    check_identity(current, repository, sha, workflow_id, workflow_path, label)
    require(current["id"] == selected["id"] and current["run_number"] == selected["run_number"]
            and current["run_attempt"] >= selected["run_attempt"], f"{label} run changed identity")
    if current.get("status") != "completed":
        raise Pending(f"{label} run {current['id']} attempt {current['run_attempt']} is not complete")
    require(current.get("conclusion") == "success",
            f"{label} run {current['id']} attempt {current['run_attempt']} did not succeed")
    # Do not accept an older success if another run/rerun appeared during the read.
    latest = latest_run(api, repository, sha, workflow_id, workflow_path, label)
    require((latest["id"], latest["run_attempt"], latest.get("status"), latest.get("conclusion"))
            == (current["id"], current["run_attempt"], "completed", "success"),
            f"{label} validation changed while checking; retry publication")
    if require_current_main:
        main = api(f"repos/{repository}/git/ref/heads/main")
        require(main.get("object", {}).get("sha") == sha, f"Main changed while checking {label} CI")
    return current


def check_once(repository: str, sha: str, *, api=gh_get) -> dict:
    return check_workflow_once(repository, sha, api=api, require_current_main=True)


def wait_for_success(repository: str, sha: str, wait_seconds: float, *, api=gh_get,
                     clock=time.monotonic, sleep=time.sleep) -> dict:
    deadline = clock() + wait_seconds
    while True:
        try:
            return check_once(repository, sha, api=api)
        except Pending as error:
            remaining = deadline - clock()
            if remaining <= 0:
                raise
            print(f"{error}; waiting for exact-source validation", flush=True)
            sleep(min(30, remaining))


def verify_provenance(
    directory: Path,
    repository: str,
    sha: str,
    *,
    run_id: int | None = None,
    run_attempt: int | str | None = None,
    manifest: Path = DEFAULT_MANIFEST,
    repo_root: Path = ROOT,
) -> dict:
    root = Path(directory).resolve()
    checkout_root = Path(repo_root).resolve()
    manifest_path = Path(manifest).resolve()
    require(manifest_path.is_file(), f"Missing abstract catalogue manifest: {manifest_path}")
    manifest_data = json.loads(manifest_path.read_text(encoding="utf-8"))
    entries = manifest_data.get("entries") if isinstance(manifest_data, dict) else None
    require(isinstance(entries, list) and bool(entries), "Malformed abstract catalogue manifest")

    prov_path = root / "provenance.json"
    require(prov_path.is_file(), "Missing provenance.json in abstract artifact")
    source = json.loads(prov_path.read_text(encoding="utf-8"))
    require(isinstance(source, dict), "Malformed provenance.json")
    require(source.get("source_sha") == sha, "Source SHA mismatch")
    require(source.get("repository") == repository, "Repository mismatch")
    require(source.get("event") == "push" and source.get("ref") == "refs/heads/main",
            "Not a main build")
    require(source.get("source_dirty") is False, "Artifact was built from modified sources")

    if run_id is not None:
        require(source.get("run_url") == f"https://github.com/{repository}/actions/runs/{run_id}",
                "Provenance run_url mismatch")
    else:
        run_url = source.get("run_url")
        require(isinstance(run_url, str)
                and run_url.startswith(f"https://github.com/{repository}/actions/runs/"),
                "Malformed provenance run_url")
    raw_attempt = source.get("run_attempt")
    require(not isinstance(raw_attempt, bool) and str(raw_attempt or "").isdigit()
            and int(str(raw_attempt)) > 0, "Malformed provenance run_attempt")
    if run_attempt is not None:
        require(str(raw_attempt) == str(run_attempt), "Provenance run_attempt mismatch")

    catalogue = source.get("catalogue")
    docs = source.get("documents")
    require(isinstance(catalogue, dict) and isinstance(docs, list) and bool(docs),
            "Malformed document inventory in provenance.json")
    require(catalogue.get("pdf") == "catalogue.pdf",
            "Catalogue entry in provenance.json must reference catalogue.pdf")
    require(len(docs) == len(entries),
            "Document count in provenance.json does not match catalogue.json")
    for document, entry in zip(docs, entries):
        expected_id = entry.get("id")
        require(isinstance(document, dict) and document.get("id") == expected_id
                and document.get("pdf") == f"{expected_id}.pdf",
                f"Document inventory mismatch for {expected_id}")

    inputs = source.get("inputs")
    require(isinstance(inputs, list) and bool(inputs), "Missing or empty inputs in provenance.json")
    input_map: dict[str, str] = {}
    for record in inputs:
        require(isinstance(record, dict) and isinstance(record.get("path"), str)
                and isinstance(record.get("sha256"), str)
                and bool(re.fullmatch(r"[0-9a-f]{64}", record["sha256"])),
                "Malformed input record in provenance.json")
        rel_path = record["path"]
        require(rel_path not in input_map, f"Duplicate input record in provenance.json: {rel_path}")
        target = (checkout_root / rel_path).resolve()
        require(target.is_relative_to(checkout_root) and target.is_file()
                and not target.is_symlink(), f"Missing or invalid input file: {rel_path}")
        actual_sha = hashlib.sha256(target.read_bytes()).hexdigest()
        require(actual_sha == record["sha256"], f"Input digest mismatch for {rel_path}")
        input_map[rel_path] = record["sha256"]
    manifest_rel = str(manifest_path.relative_to(checkout_root))
    for required_input in (manifest_rel, *REQUIRED_PRODUCER_INPUTS):
        require(required_input in input_map,
                f"Missing required input in provenance.json: {required_input}")

    documents = [catalogue, *docs]
    expected_pdfs = set()
    for document in documents:
        require(isinstance(document, dict) and isinstance(document.get("pdf"), str)
                and isinstance(document.get("pdf_sha256"), str),
                "Malformed document entry in provenance.json")
        if "source" in document or "source_sha256" in document:
            require(isinstance(document.get("source"), str)
                    and input_map.get(document["source"]) == document.get("source_sha256"),
                    f"Document source digest mismatch for {document.get('id')}")
        name = document["pdf"]
        require(bool(re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*\.pdf", name)),
                f"Invalid PDF filename in provenance.json: {name}")
        expected_pdfs.add(name)
    actual_pdfs = {p.name for p in root.glob("*.pdf")}
    require(actual_pdfs == expected_pdfs, "PDF inventory mismatch")
    require({p.name for p in root.iterdir()} == expected_pdfs | {"provenance.json"},
            "Unexpected files in abstract artifact")
    for document in documents:
        pdf = (root / document["pdf"]).resolve()
        require(pdf.parent == root and pdf.is_file() and not pdf.is_symlink(), "Invalid PDF path")
        digest = hashlib.sha256(pdf.read_bytes()).hexdigest()
        require(digest == document["pdf_sha256"], f"PDF digest mismatch for {document['pdf']}")
    return source


def check_both_workflows(repository: str, sha: str, *, api=gh_get) -> tuple[dict, dict]:
    pending_error: Pending | None = None
    lean_run = None
    try:
        lean_run = check_workflow_once(
            repository, sha,
            WORKFLOW_FILE, WORKFLOW_PATH, WORKFLOW_NAME, "Lean",
            api=api, require_current_main=False,
        )
    except Pending as error:
        pending_error = error
    abstracts_run = check_workflow_once(
        repository, sha,
        ABSTRACTS_WORKFLOW_FILE, ABSTRACTS_WORKFLOW_PATH, ABSTRACTS_WORKFLOW_NAME,
        "Abstracts",
        api=api, require_current_main=False,
    )
    if pending_error is not None:
        raise pending_error
    assert lean_run is not None
    return lean_run, abstracts_run


def download_verified_abstracts(
    repository: str,
    sha: str,
    output_dir: Path,
    wait_seconds: float,
    *,
    api=gh_get,
    downloader=gh_download_artifact,
    clock=time.monotonic,
    sleep=time.sleep,
) -> tuple[dict, dict]:
    deadline = clock() + wait_seconds
    dest = Path(output_dir)
    staging = dest.parent / f".{dest.name}-staging"
    authority_retries = 0
    while True:
        if staging.exists():
            shutil.rmtree(staging)
        try:
            lean_run, abstracts_run = check_both_workflows(repository, sha, api=api)
            artifact_name = f"formal-abstracts-{sha}-{abstracts_run['run_attempt']}"
            staging.mkdir(parents=True, exist_ok=True)
            downloader(repository, abstracts_run["id"], artifact_name, staging)
            verify_provenance(
                staging, repository, sha,
                run_id=abstracts_run["id"],
                run_attempt=abstracts_run["run_attempt"],
            )
            post_lean, post_abstracts = check_both_workflows(repository, sha, api=api)
            if ((post_lean["id"], post_lean["run_attempt"]) != (lean_run["id"], lean_run["run_attempt"])
                    or (post_abstracts["id"], post_abstracts["run_attempt"])
                    != (abstracts_run["id"], abstracts_run["run_attempt"])):
                authority_retries += 1
                require(authority_retries <= 3,
                        "Workflow authority changed repeatedly during artifact download")
                continue
            break
        except Pending as error:
            if staging.exists():
                shutil.rmtree(staging)
            remaining = deadline - clock()
            if remaining <= 0:
                raise
            print(f"{error}; waiting for exact-source validation", flush=True)
            sleep(min(30, remaining))
        except Exception:
            if staging.exists():
                shutil.rmtree(staging)
            raise

    try:
        backup = dest.parent / f".{dest.name}-backup"
        if backup.exists():
            shutil.rmtree(backup)
        had_dest = dest.exists()
        if had_dest:
            os.replace(dest, backup)
        try:
            staging.rename(dest)
        except Exception:
            if had_dest and backup.exists() and not dest.exists():
                os.replace(backup, dest)
            raise
        else:
            if backup.exists():
                shutil.rmtree(backup)
    finally:
        if staging.exists():
            shutil.rmtree(staging)
    return lean_run, abstracts_run


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--sha", default=os.environ.get("GITHUB_SHA", ""))
    parser.add_argument("--wait-seconds", type=float, default=0)
    parser.add_argument("--download-dir", type=Path, default=None,
                        help="download and verify the formal-abstracts artifact into this directory")
    args = parser.parse_args()
    try:
        require(0 <= args.wait_seconds <= 1200, "Wait must be between zero and 1200 seconds")
        if args.download_dir is not None:
            lean_run, abstracts_run = download_verified_abstracts(
                args.repository, args.sha, args.download_dir, args.wait_seconds,
            )
            print(f"Lean validation: https://github.com/{args.repository}/actions/runs/{lean_run['id']} "
                  f"attempt {lean_run['run_attempt']} succeeded for {args.sha}")
            print(f"Abstracts artifact: https://github.com/{args.repository}/actions/runs/{abstracts_run['id']} "
                  f"attempt {abstracts_run['run_attempt']} verified in {args.download_dir}")
        else:
            run = wait_for_success(args.repository, args.sha, args.wait_seconds)
            print(f"Lean validation: https://github.com/{args.repository}/actions/runs/{run['id']} "
                  f"attempt {run['run_attempt']} succeeded for {args.sha}")
    except (Rejected, subprocess.SubprocessError, OSError, ValueError, KeyError, TypeError,
            AttributeError) as error:
        print(f"Abstract publication denied: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
