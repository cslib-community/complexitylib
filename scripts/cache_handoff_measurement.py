#!/usr/bin/env python3
"""Private, temporary #1728 pilot. Absent/disabled plans perform no operations.

Remove this driver and its workflow hooks after the #1197 study or HARD_EXPIRY.
It never authorizes a dispatch restore, publishes caches, or changes repository variables.
"""

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import time
from urllib.error import HTTPError
from urllib.parse import urlencode
from urllib.request import Request, urlopen

import cache_handoff as handoff

ROOT = Path(__file__).resolve().parents[1]
REPOSITORY = "cslib-community/complexitylib"
HARD_EXPIRY = "2026-11-15T00:00:00Z"
MAX_SAMPLES = 16
MAX_BYTES = 32 * 1024 ** 3
MAX_SECONDS = 7200
CHECKS = [
    ["lake", "build", "--wfail", "--iofail", "@complexitylib", "@/mk_all",
     "@/checkInitImports", "@mathlib/lint-style"],
    ["lake", "test", "--wfail", "--iofail"],
    ["lake", "lint"],
    ["python3", "-B", "-m", "unittest", "scripts/test_check_tidy_surface.py"],
    ["python3", "-B", "scripts/check_tidy_surface.py"],
    ["lake", "exe", "mk_all", "--check"],
    ["python3", "-B", "-m", "unittest", "discover", "-s", "scripts", "-p", "test_mk_all.py"],
    ["lake", "exe", "lint-style"],
    ["lake", "exe", "checkInitImports"],
]


def require(ok, message):
    handoff.require(ok, message)


def utc(value):
    require(isinstance(value, str) and re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z", value), "Expected UTC timestamp")
    return dt.datetime.fromisoformat(value[:-1] + "+00:00")


def plan_of(text, now):
    if not text:
        return None
    plan = json.loads(text)
    require(isinstance(plan, dict), "Expected measurement plan object")
    if plan.get("mode", "disabled") == "disabled":
        return None
    require(plan.get("mode") in ("paired", "randomized"), "Unknown measurement mode")
    start, end = utc(plan["start"]), utc(plan["end"])
    require(start <= now < end <= utc(HARD_EXPIRY), "Measurement window inactive or expired")
    require(dt.timedelta(0) < end - start <= dt.timedelta(days=7), "Window exceeds seven days")
    require(re.fullmatch(r"[A-Za-z0-9_-]{1,64}", plan.get("seed", "")), "Invalid study seed")
    for key, cap in (("max_samples", MAX_SAMPLES), ("sample_denominator", 1000),
                     ("max_bytes", MAX_BYTES), ("max_seconds", MAX_SECONDS)):
        require(type(plan.get(key)) is int and 0 < plan[key] <= cap, f"Invalid {key}")
    require(set(plan) == {"mode", "start", "end", "seed", "max_samples",
                          "sample_denominator", "max_bytes", "max_seconds"}, "Unknown plan fields")
    return plan


def coin(plan, tag, run_id):
    return int(hashlib.sha256(f"{plan['seed']}:{tag}:{run_id}".encode()).hexdigest(), 16)


def selection(plan, run, pages):
    runs = [r for page in pages for r in page["workflow_runs"]]
    require(pages and all(p["total_count"] == len(runs) for p in pages), "Incomplete population listing")
    require(len(runs) <= 1000 and len({r["id"] for r in runs}) == len(runs), "Population listing limit")
    require(any(r["id"] == run["id"] for r in runs), "Current run missing from population")
    scoped = [r for r in runs if plan["start"] <= r["created_at"] < plan["end"]]
    candidates = sorted((r for r in scoped if coin(plan, "sample", r["id"]) % plan["sample_denominator"] == 0),
                        key=lambda r: (r["created_at"], r["id"]))
    # No-job, failed and cancelled runs consume slots too: never replace them with successes.
    chosen = [r["id"] for r in candidates[:plan["max_samples"]]]
    return {"selected": run["id"] in chosen, "sampled_run_ids": chosen,
            "population_count": len(scoped), "order": "BT" if coin(plan, "order", run["id"]) % 2 else "TB",
            "assignment": "bypass" if coin(plan, "assignment", run["id"]) % 2 else "restore"}


def context(root, env):
    ctx = handoff.source_context(root, env, "push")
    require(ctx["repository"] == REPOSITORY, "Measurement is canonical-repository only")
    require(env.get("GITHUB_RUN_ATTEMPT") == "1", "Measurement excludes reruns")
    require(re.fullmatch(r"[1-9][0-9]*", env.get("GITHUB_RUN_ID", "")), "Invalid run id")
    return ctx


def location(env):
    temp = Path(env["RUNNER_TEMP"])
    require(temp.is_absolute() and temp.is_dir() and not temp.is_symlink(), "Unsafe runner temporary directory")
    require("\n" not in str(temp) and "\r" not in str(temp), "Invalid temporary path")
    return temp / f"handoff-measurement-{env['GITHUB_RUN_ID']}-{env['GITHUB_RUN_ATTEMPT']}"


def save(path, data):
    temp = path.with_suffix(".pending")
    temp.write_text(json.dumps(data, indent=2) + "\n")
    temp.replace(path)


def output(env, name, value):
    if env.get("GITHUB_OUTPUT"):
        with Path(env["GITHUB_OUTPUT"]).open("a") as target:
            target.write(f"{name}={value}\n")


def published(root, env):
    url = env.get("COMPLEXITYLIB_CACHE_URL", "https://storage.googleapis.com/complexitylib-lake-cache")
    require(url.startswith("https://"), "Unknown cache endpoint")
    toolchain = (root / "lean-toolchain").read_text().strip().replace("/", "--").replace(":", "---")
    request = Request(f"{url}/r0/{REPOSITORY}/tc/{toolchain}/{env['GITHUB_SHA']}.jsonl", method="HEAD")
    try:
        with urlopen(request, timeout=15) as response:
            require(response.status == 404, "Target already published: contaminated baseline")
    except HTTPError as error:
        require(error.code == 404, f"Unknown target-cache status: HTTP {error.code}")


def prepare(root, env, now=None, api=handoff.gh_get):
    plan = plan_of(env.get("HANDOFF_MEASUREMENT_PLAN", ""), now or dt.datetime.now(dt.timezone.utc))
    if plan is None:
        return  # Default-disabled must not inspect Git, access caches/network or create files.
    ctx = context(root, env)
    run_id = int(env["GITHUB_RUN_ID"])
    run = api(f"repos/{REPOSITORY}/actions/runs/{run_id}")
    require(run["id"] == run_id and run["head_sha"] == ctx["source_sha"] and run["event"] == "push"
            and run["head_branch"] == "main" and run["run_attempt"] == 1
            and run["path"] == ".github/workflows/lean_action_ci.yml"
            and run["repository"]["full_name"] == REPOSITORY, "Wrong main run")
    query = urlencode({"event": "push", "branch": "main", "created": f"{plan['start']}..{plan['end']}", "per_page": 100})
    pages = api(f"repos/{REPOSITORY}/actions/workflows/lean_action_ci.yml/runs?{query}", paginate=True)
    choice = selection(plan, run, pages)
    state = location(env)
    require(not state.resolve().is_relative_to(root.resolve()), "Measurement state overlaps checkout")
    state.mkdir(mode=0o700)  # A collision is an exclusion, never permission to overwrite state.
    report = {"version": 1, "plan": plan, "context": ctx, "run_id": run_id,
              "main": {key: run.get(key) for key in ("id", "run_attempt", "created_at", "head_sha", "event", "head_branch", "workflow_id")},
              "selection": choice, "status": "unselected", "arms": [],
              "toolchain": (root / "lean-toolchain").read_text().strip(),
              "dependency_pins": [{key: package.get(key) for key in ("name", "rev", "url")}
                                  for package in json.loads((root / "lake-manifest.json").read_text())["packages"]],
              "scope": "Build/check pilot or randomized main assignment; not a net-benefit conclusion"}
    save(state / "report.json", report)
    output(env, "report", state / "report.json")
    if choice["selected"]:
        try:
            published(root, env)
        except Exception as error:
            report.update(status="excluded", reason=str(error))
            save(state / "report.json", report)
            return
        report["status"] = "prepared"
        save(state / "report.json", report)
        output(env, "selected", "true")
        with Path(env["GITHUB_ENV"]).open("a") as target:
            target.write(f"HANDOFF_MEASUREMENT_LOG={state / 'bootstrap.log'}\n")


def ancestor(root, sha, target):
    require(re.fullmatch(r"[0-9a-f]{40}", sha) and sha != target, "Initial cache is not an ancestor")
    result = subprocess.run(["git", "merge-base", "--is-ancestor", sha, target], cwd=root)
    require(result.returncode == 0, "Initial cache ancestry unproved")


def initial(root, env, state, target):
    text = (state / "bootstrap.log").read_text()
    revisions = re.findall(r"Remote cache: ([0-9a-f]{40}) ", text)
    require(len(revisions) <= 1, "Ambiguous initial remote revision")
    require(revisions or "No outputs uploaded for the last " in text, "Initial cache result unknown")
    if revisions:
        ancestor(root, revisions[0], target)
    key = env.get("HANDOFF_MEASUREMENT_ACTIONS_KEY", "")
    if key:
        match = re.search(r"([0-9a-f]{40})$", key)
        require(match is not None, "Initial Actions-cache key unknown")
        ancestor(root, match[1], target)
    return {"remote_revision": revisions[0] if revisions else None, "actions_matched_key": key,
            "bootstrap_log_sha256": handoff.digest(state / "bootstrap.log"),
            "lean_num_threads": env.get("LEAN_NUM_THREADS"), "cpu_count": os.cpu_count(),
            "changed_paths": subprocess.check_output(["git", "diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD"], cwd=root, text=True).splitlines()}


def tree(path, max_bytes, deadline=None, links=True):
    require(path.is_dir() and not path.is_symlink(), f"Not a real cache directory: {path}")
    total, digest = 0, hashlib.sha256()
    for base, dirs, files in os.walk(path, followlinks=False):
        dirs.sort()
        for name in sorted(dirs + files):
            require(deadline is None or time.monotonic() < deadline, "Measurement time budget exceeded")
            item = Path(base) / name
            info = item.lstat()
            relative = item.relative_to(path).as_posix()
            record = [relative, info.st_mode, info.st_mtime_ns]
            if stat.S_ISLNK(info.st_mode):
                require(links and not Path(os.readlink(item)).is_absolute()
                        and item.resolve().is_relative_to(path.resolve()), "External or unsupported cache symlink")
                record.append(os.readlink(item))
            elif stat.S_ISREG(info.st_mode):
                require(name != ".git", "External Git control files are unsupported in paired snapshots")
                total += info.st_size
                require(total <= max_bytes, f"Measurement byte budget exceeded: {total} > {max_bytes}")
                record.append(handoff.digest(item))
            else:
                require(stat.S_ISDIR(info.st_mode), "Non-regular cache entry")
            digest.update(json.dumps(record).encode())
    require(deadline is None or time.monotonic() < deadline, "Measurement time budget exceeded")
    return {"bytes": total, "sha256": digest.hexdigest()}


def copy_file(src, dst, deadline=None):
    require(deadline is None or time.monotonic() < deadline, "Measurement time budget exceeded")
    result = shutil.copy2(src, dst)
    require(deadline is None or time.monotonic() < deadline, "Measurement time budget exceeded")
    return result


def cache_path(env):
    if "LAKE_CACHE_DIR" in env:
        require(bool(env["LAKE_CACHE_DIR"]), "System artifact cache disabled")
        return Path(env["LAKE_CACHE_DIR"]).resolve()
    lake = Path(subprocess.check_output(["elan", "which", "lake"], env=env, text=True).strip())
    require(lake.is_absolute() and lake.parent.name == "bin", "Unknown Lake cache layout")
    return lake.parent.parent / "lake/cache"  # Pinned Lake Config/Env.lean:119-120.


class Snapshot:
    def __init__(self, root, cache, state, plan, deadline):
        self.live = [root / ".lake", state / "private-cache"]
        self.saved = [state / "initial-lake", state / "initial-cache"]
        require(not cache.is_relative_to(root / ".lake") and not (root / ".lake").is_relative_to(cache), "Nested cache roots")
        sources = [root / ".lake", cache]
        require(all(not state.resolve().is_relative_to(p.resolve()) and not p.resolve().is_relative_to(state.resolve())
                    for p in sources), "Measurement state overlaps initial caches")
        self.inventory = [tree(p, plan["max_bytes"], deadline, links=(i == 0)) if p.exists() else {"bytes": 0, "sha256": None} for i, p in enumerate(sources)]
        size = sum(x["bytes"] for x in self.inventory)
        require(size <= plan["max_bytes"], f"Combined cache byte budget exceeded: {size} > {plan['max_bytes']}")
        # Ordinary copies; reserve space for rollback copies and the existing bounded handoff.
        reserve = 2 * size + self.inventory[1]["bytes"] + handoff.MAX_BYTES + handoff.MAX_ARCHIVE_BYTES
        free = shutil.disk_usage(state).free
        require(free >= reserve, f"Insufficient measurement/rollback disk budget: need {reserve}, free {free}")
        try:
            for src, dst in zip(sources, self.saved):
                if src.exists():
                    shutil.copytree(src, dst, symlinks=True,
                                    copy_function=lambda src, dst: copy_file(src, dst, deadline))
                else:
                    dst.mkdir()
            self.expected = [tree(p, plan["max_bytes"], deadline, links=(i == 0)) for i, p in enumerate(self.saved)]
        except BaseException:
            self.close()
            raise
        self.max_bytes = plan["max_bytes"]

    def reset(self, deadline=None):
        staged, backups, installed = [], [], []
        try:
            for i, saved in enumerate(self.saved):
                dest = saved.parent / f"next-{i}"
                staged.append(dest)
                shutil.copytree(saved, dest, symlinks=True,
                                copy_function=lambda src, dst: copy_file(src, dst, deadline))
            for i, (live, new) in enumerate(zip(self.live, staged)):
                backup = new.parent / f"previous-{i}"
                if live.exists():
                    live.rename(backup)
                    backups.append((live, backup))
                new.rename(live)
                installed.append(live)
            require([tree(p, self.max_bytes, deadline) for p in self.live] == self.expected, "Initial cache reset mismatch")
        except BaseException:
            for live in reversed(installed):
                if live.exists():
                    shutil.rmtree(live)
            for live, backup in reversed(backups):
                backup.rename(live)
            raise
        finally:
            for path in staged + [p for _, p in backups]:
                if path.exists():
                    shutil.rmtree(path)

    def close(self):
        for path in self.saved:
            if path.exists():
                shutil.rmtree(path)


def command(args, root, env, deadline, log=None):
    remaining = deadline - time.monotonic()
    require(remaining > 0, "Measurement time budget exceeded")
    start = time.monotonic()
    started_at = dt.datetime.now(dt.timezone.utc).isoformat()
    print(f"Handoff measurement command: {json.dumps(args)}", flush=True)
    handle = log.open("w") if log else None
    process = subprocess.Popen(args, cwd=root, env=env, stdout=handle, stderr=subprocess.STDOUT if handle else None, start_new_session=True)
    try:
        code = process.wait(timeout=remaining)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)  # Only the child process group created above.
        except ProcessLookupError:
            pass
        process.wait()
        raise
    finally:
        if handle:
            handle.close()
    result = {"command": args, "seconds": time.monotonic() - start, "returncode": code,
              "started_at": started_at, "completed_at": dt.datetime.now(dt.timezone.utc).isoformat()}
    if log:
        with log.open() as source:
            text = source.read(65536)
        print(text, end="", flush=True)
        result["log"] = text
    return result


def observe_producer(ctx, api=handoff.gh_get):
    workflow = api(f"repos/{REPOSITORY}/actions/workflows/lean_action_ci.yml")
    require(workflow.get("path") == handoff.WORKFLOW_PATH and workflow.get("state") == "active"
            and handoff.positive(workflow.get("id")), "Authoritative workflow unavailable")
    pages = api(f"repos/{REPOSITORY}/actions/workflows/{workflow['id']}/runs?{urlencode({'head_sha': ctx['source_sha'], 'event': 'merge_group', 'per_page': 100})}", paginate=True)
    runs = [r for p in pages for r in p["workflow_runs"]]
    require(runs and all(p["total_count"] == len(runs) for p in pages), "Producer listing unavailable")
    require(len({r["id"] for r in runs}) == len(runs)
            and len({r["run_number"] for r in runs}) == len(runs), "Ambiguous producer listing")
    for run in runs:
        handoff.check_run(run, ctx, workflow["id"])
    run = max(runs, key=lambda r: r["run_number"])
    handoff.check_run(run, ctx, workflow["id"])
    current = api(f"repos/{REPOSITORY}/actions/runs/{run['id']}")
    handoff.check_run(current, ctx, workflow["id"])
    require(current["id"] == run["id"] and current["run_number"] == run["run_number"]
            and current["run_attempt"] >= run["run_attempt"], "Producer identity changed")
    run = current
    return {key: run[key] for key in ("id", "run_attempt", "head_sha", "event", "status", "conclusion")}


def measure(root, env, api=handoff.gh_get, now=None):
    state = location(env)
    report = json.loads((state / "report.json").read_text())
    require(report["status"] == "prepared", "Measurement was not prepared")
    require(report["run_id"] == int(env["GITHUB_RUN_ID"]), "Measurement run changed")
    snapshot = None
    try:
        require(context(root, env) == report["context"], "Measurement context changed")
        plan = plan_of(json.dumps(report["plan"]), now or dt.datetime.now(dt.timezone.utc))
        require(plan is not None, "Measurement disabled")
        published(root, env)
        report["initial"] = initial(root, env, state, env["GITHUB_SHA"])
        try:
            report["producer"] = observe_producer(report["context"], api)
        except Exception as error:
            report["producer"] = {"status": "unknown", "reason": str(error)}
        if plan["mode"] == "randomized":
            report["status"] = "randomized_assignment"
            save(state / "report.json", report)  # Persist the assignment before changing restore policy.
            output(env, "bypass_restore", str(report["selection"]["assignment"] == "bypass").lower())
            return
        deadline = time.monotonic() + plan["max_seconds"]
        report["initial"]["free_disk_bytes"] = shutil.disk_usage(state).free
        snapshot = Snapshot(root, cache_path(env), state, plan, deadline)
        report["initial"]["inventory"] = snapshot.inventory
        child_env = {**env, "LAKE_CACHE_DIR": str(snapshot.live[1]), "COMPLEXITYLIB_CACHE_AUTO": "0"}
        report["status"] = "paired_running"
        report["arms"] = [{"arm": arm, "checks": [], "success": False, "status": "not_started"}
                          for arm in report["selection"]["order"]]
        for result in report["arms"]:
            arm = result["arm"]
            snapshot.reset(deadline)
            require(context(root, env) == report["context"], "Tracked source changed")
            result["status"] = "running"
            save(state / "report.json", report)
            if arm == "T":
                result["restore"] = command(["python3", "-B", "scripts/cache_handoff.py", "restore"], root, child_env, min(deadline, time.monotonic() + 180), state / "restore.log")
                matches = re.findall(r"Build handoff restored from run ([0-9]+) attempt ([0-9]+);", result["restore"].get("log", ""))
                result["accepted_producer"] = {"run_id": int(matches[0][0]), "attempt": int(matches[0][1])} if len(matches) == 1 else None
                save(state / "report.json", report)
            for args in CHECKS:
                result["active_command"] = args
                save(state / "report.json", report)
                checked = command(args, root, child_env, deadline)
                result["checks"].append(checked)
                result["active_command"] = None
                save(state / "report.json", report)
                require(checked["returncode"] == 0, "Experimental validation arm failed")
            result["success"] = True
            result["status"] = "success"
        report["status"] = "paired_checks_complete"
    except Exception as error:
        report.update(status="excluded", reason=str(error))
        for arm in report["arms"]:
            if not arm["success"]:
                arm["status"] = "failed" if arm["status"] == "running" else "not_run"
                arm["reason"] = str(error)
    finally:
        if snapshot:
            try:
                snapshot.reset()  # Also on timeout/failure: normal production starts from I.
                with Path(env["GITHUB_ENV"]).open("a") as target:
                    target.write(f"LAKE_CACHE_DIR={snapshot.live[1]}\n")
                if report["status"] == "paired_checks_complete":
                    report["status"] = "paired_complete"
            except Exception as error:
                report.update(status="excluded", recovery_error=str(error))
            snapshot.close()
        save(state / "report.json", report)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("prepare", "measure"))
    phase = parser.parse_args().phase
    try:
        (prepare if phase == "prepare" else measure)(ROOT, os.environ)
    except Exception as error:
        # Workflow marks this optional hook continue-on-error. Production gates remain outside it.
        print(f"Handoff measurement excluded: {error}", flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
