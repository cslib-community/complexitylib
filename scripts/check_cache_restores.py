#!/usr/bin/env python3
"""Re-elaborate local Lean files whose build outputs came from Lake's artifact cache (#4523).

Usage: python3 scripts/check_cache_restores.py [--files-from JSON] [--built-under PATH ...]
                                            [--jobs N] [--progress | --quiet]

`lakefile.toml` enables Lake's local artifact cache, which checkouts on the same machine share.
Lake stores a module's outputs there even when the build logged warnings. Individual-artifact
(`.arts`) restoration without the original trace writes `"synthetic": true` with an empty log,
so `lake build --wfail --iofail` and `lake test --wfail --iofail` can pass without showing those
warnings. An ordinary `.ltar` archive can preserve the original trace and its messages; such a
restore need not be re-elaborated by this audit. Later individual-artifact reuse can lose those
messages again. CI publishes its remote cache only from `main`; this local check recovers
diagnostics rather than establishing artifact provenance or proof trust.

After the Lean gates, `scripts/full_check.py` runs this check for all built sources of the root
package, including unchanged clients, tests and executables. This also covers deletions and
configuration changes, which cannot use quick mode's bounded import graph. `scripts/quick_check.py`
passes its affected source files as a JSON list, plus built import aggregates and executable
source directories whose helpers may import the edited library indirectly. Missing or unreadable
traces are checked too.

It runs `lake -q lean` on each selected file whose trace is synthetic and fails when the command
fails or prints anything at all: `lake lean` exits 0 after warnings, and `--iofail` rejects
informational output too. `lake lean` first builds the file's imports and replays their logs, so
a reported message can also come from an import; run parallel audits after building the selected
targets so concurrent workers do not race rebuilding shared imports. Up to 8 files are elaborated
concurrently by default (`--jobs N` or `CSLIB_FRONTIER_CACHE_AUDIT_JOBS=N`, `N >= 1`, also capped
by a positive `LEAN_NUM_THREADS` when unset), with `LEAN_NUM_THREADS=1` in each worker when
running multiple workers so parallel processes do not multiply Lean's internal thread pool, and
failures are reported in deterministic source-path order. A successful audit leaves traces
unchanged and records no receipt, so repeating it can re-elaborate the same sources. It does not
repair the missing diagnostic metadata in Lake's individual-artifact cache. Outside CI, progress
lists the selected count, worker mode and each source before elaboration, with elapsed audit time.
`--progress` enables those lines in CI; `--quiet` suppresses them locally. Failures and the final
summary are always printed.
"""

from __future__ import annotations

import argparse
from collections.abc import Mapping, Sequence
import concurrent.futures
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
JOBS_ENV = "CSLIB_FRONTIER_CACHE_AUDIT_JOBS"
DEFAULT_JOBS_CAP = 8


def layout(root: Path) -> tuple[Path, list[Path]]:
    """The root package's Lean build directory, and the source directories of its libraries and
    executables relative to `root`, most specific first (`lakefile.toml`)."""
    config = tomllib.loads((root / "lakefile.toml").read_text())
    lib_dir = root / config.get("buildDir", ".lake/build") / config.get("leanLibDir", "lib/lean")
    package = Path(config.get("srcDir", "."))
    targets = config.get("lean_lib", []) + config.get("lean_exe", [])
    dirs = {(root / package / target.get("srcDir", ".")).resolve().relative_to(root.resolve())
            for target in targets} | {(root / package).resolve().relative_to(root.resolve())}
    return lib_dir, sorted(dirs, key=lambda path: len(path.parts), reverse=True)


def trace_path(rel: str, lib_dir: Path, dirs: list[Path]) -> Path | None:
    """The existing build trace of source file `rel`, if any."""
    for directory in dirs:
        if Path(rel).is_relative_to(directory):
            trace = lib_dir / Path(rel).relative_to(directory).with_suffix(".trace")
            if trace.is_file():
                return trace
    return None


def restored(trace: Path) -> bool:
    """Whether Lake wrote `trace` when it restored the outputs from a cache rather than building
    them. An unreadable trace counts as restored, so the file is checked."""
    try:
        data = json.loads(trace.read_text())
    except (OSError, ValueError):
        return True
    return not isinstance(data, dict) or data.get("synthetic") is True


def built_files(root: Path, lib_dir: Path, dirs: list[Path]) -> set[str]:
    """Sources corresponding to root-package outputs, without scanning dependency checkouts.

    Include `.olean` files as well as traces: losing a trace must not silently omit an output.
    Stale outputs whose source was deleted are ignored; the build gates check their clients.
    """
    modules = {path.relative_to(lib_dir).with_suffix(".lean")
               for suffix in ("*.trace", "*.olean") for path in lib_dir.rglob(suffix)}
    return {(directory / module).as_posix() for directory in dirs for module in modules
            if (root / directory / module).is_file()}


def restored_files(root: Path, files: list[str] | None = None,
                   built_under: Sequence[str] = ()) -> list[str]:
    """Selected sources with restored, missing or unreadable build traces.

    Without an explicit list, cover all root-package build outputs. Extra paths select built
    aggregates or executable helper directories without forcing unbuilt sources into the audit.
    """
    lib_dir, dirs = layout(root)
    built = built_files(root, lib_dir, dirs) if files is None or built_under else set()
    selected = built if files is None else set(files)
    selected |= {rel for rel in built if any(Path(rel).is_relative_to(path) for path in built_under)}
    for rel in selected:
        path = Path(rel)
        if (path.is_absolute() or ".." in path.parts or path.suffix != ".lean"
                or not (root / path).is_file()):
            raise ValueError(f"not an existing checkout-relative Lean source: {rel!r}")
    return [rel for rel in sorted(selected)
            if (trace := trace_path(rel, lib_dir, dirs)) is None or restored(trace)]


def available_cpus() -> int:
    """Usable CPU count respecting process affinity when supported."""
    if hasattr(os, "process_cpu_count"):
        count = os.process_cpu_count()
    elif hasattr(os, "sched_getaffinity"):
        try:
            count = len(os.sched_getaffinity(0))
        except OSError:
            count = os.cpu_count()
    else:
        count = os.cpu_count()
    return max(1, count or 1)


def resolve_jobs(cli_jobs: int | None, env: Mapping[str, str] = os.environ) -> int:
    """Worker limit from `--jobs`, `CSLIB_FRONTIER_CACHE_AUDIT_JOBS`, or bounded CPU/thread cap."""
    if cli_jobs is not None:
        source, jobs = "--jobs", cli_jobs
    elif raw := env.get(JOBS_ENV, "").strip():
        source = JOBS_ENV
        try:
            jobs = int(raw)
        except ValueError as error:
            raise ValueError(f"{JOBS_ENV} must be an integer >= 1, got {raw!r}") from error
    else:
        source = "--jobs"
        jobs = min(DEFAULT_JOBS_CAP, available_cpus())
        if lean_threads := env.get("LEAN_NUM_THREADS", "").strip():
            try:
                parsed = int(lean_threads)
            except ValueError:
                parsed = 0
            if parsed >= 1:
                jobs = min(jobs, parsed)
    if jobs < 1:
        raise ValueError(f"{source} must be >= 1, got {jobs}")
    return jobs


def _proc_children(pid: int) -> list[int]:
    """Return direct child PIDs of `pid` by inspecting /proc/<pid>/task/*/children,
    falling back to /proc scanning or pgrep."""
    children: list[int] = []
    task_dir = Path(f"/proc/{pid}/task")
    read_children_file = False
    try:
        if task_dir.is_dir():
            for entry in task_dir.iterdir():
                children_file = entry / "children"
                if children_file.is_file():
                    try:
                        children.extend(int(p) for p in children_file.read_text().split())
                        read_children_file = True
                    except OSError:
                        pass
    except OSError:
        pass
    if not read_children_file:
        # Fallback for systems/containers without /proc/<pid>/task/*/children:
        # scan /proc for processes whose ppid equals pid.
        proc_root = Path("/proc")
        try:
            if proc_root.is_dir():
                for entry in proc_root.iterdir():
                    if not entry.name.isdigit():
                        continue
                    try:
                        stat_text = (entry / "stat").read_text()
                        rparen = stat_text.rfind(")")
                        if rparen != -1:
                            fields = stat_text[rparen + 1:].split()
                            if fields and int(fields[1]) == pid:
                                children.append(int(entry.name))
                                read_children_file = True
                    except (OSError, ValueError, IndexError):
                        pass
        except OSError:
            pass
    if not read_children_file and shutil.which("pgrep"):
        # Portable POSIX fallback (e.g. macOS):
        try:
            res = subprocess.run(["pgrep", "-P", str(pid)], capture_output=True, text=True)
            if res.returncode == 0:
                children.extend(int(p) for p in res.stdout.split() if p.isdigit())
        except OSError:
            pass
    return children


def _descendant_pids(pid: int) -> list[int]:
    """Return all descendant process IDs of `pid` in breadth-first order."""
    descendants: list[int] = []
    queue = [pid]
    visited = {pid}
    while queue:
        curr = queue.pop(0)
        for child in _proc_children(curr):
            if child not in visited:
                visited.add(child)
                descendants.append(child)
                queue.append(child)
    return descendants


def _parse_proc_stat_state(stat: bytes) -> str | None:
    """Parse the state field after `/proc/PID/stat`'s final parenthesized command name."""
    rparen = stat.rfind(b")")
    fields = stat[rparen + 1:].split() if rparen != -1 else []
    state = fields[0] if fields else b""
    if len(state) != 1 or not state.isascii():
        return None
    return chr(state[0])


def _process_state(pid: int) -> str | None:
    """The Linux process-state letter for `pid`, `?` when it exists but the state is unavailable,
    or `None` when it no longer exists.

    `os.kill(pid, 0)` reports a zombie as present even though it has already stopped executing.
    Read `/proc` first where available so cleanup checks can distinguish that state. On systems
    without `/proc`, fall back to the portable presence probe.
    """
    proc_root = Path("/proc")
    try:
        stat = (proc_root / str(pid) / "stat").read_bytes()
    except FileNotFoundError:
        if proc_root.is_dir():
            return None
    except OSError:
        pass
    else:
        if state := _parse_proc_stat_state(stat):
            return state
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return None
    except PermissionError:
        return "?"
    except OSError:
        return None
    return "?"


def _process_is_running(pid: int) -> bool:
    """Whether `pid` can still execute, as opposed to being absent, zombie or dead."""
    return _process_state(pid) not in (None, "Z", "X")


def terminate_process(proc: subprocess.Popen) -> None:
    """Terminate `proc` and its descendant process tree without leaving orphaned children."""
    pid = getattr(proc, "pid", None)
    if pid is None:
        return
    descendants = _descendant_pids(pid)
    for child in reversed(descendants):
        try:
            os.kill(child, signal.SIGTERM)
        except OSError:
            pass
    terminate_fn = getattr(proc, "terminate", None)
    if callable(terminate_fn):
        try:
            terminate_fn()
        except OSError:
            pass
    else:
        try:
            os.kill(pid, signal.SIGTERM)
        except OSError:
            pass

    time.sleep(0.05)

    survivors = set(descendants) | set(_descendant_pids(pid))
    for child in reversed(list(survivors)):
        if not _process_is_running(child):
            continue
        try:
            os.kill(child, signal.SIGKILL)
        except OSError:
            pass
    kill_fn = getattr(proc, "kill", None)
    if callable(kill_fn):
        try:
            kill_fn()
        except OSError:
            pass
    else:
        try:
            os.kill(pid, signal.SIGKILL)
        except OSError:
            pass


def elaborate(root: Path, rel: str, env: Mapping[str, str] | None = None,
              active: set[subprocess.Popen] | None = None,
              active_lock: threading.Lock | None = None,
              stopping: threading.Event | None = None) -> subprocess.CompletedProcess:
    """Elaborate `rel` with its library's options, without writing build outputs."""
    base_env = os.environ if env is None else env
    parent = next((Path(value) for key in ("TMPDIR", "TEMP", "TMP")
                   if (value := base_env.get(key)) and Path(value).is_dir()), None)
    cmd = ["lake", "-q", "lean", f"./{rel}"]
    if active_lock is not None and stopping is not None:
        with active_lock:
            if stopping.is_set():
                # Placeholder result for aborted workers; only consumed when re-raising an exception.
                return subprocess.CompletedProcess(cmd, -15, "")
    # `lake lean` creates a temporary `--setup` file via `IO.FS.createTempFile` without removing
    # it; scoping temporary directories per invocation prevents `/tmp` growth across large audits.
    with tempfile.TemporaryDirectory(prefix="cslib-frontier-lean-", dir=parent) as tmpdir:
        run_env = {**base_env, "TMPDIR": tmpdir, "TEMP": tmpdir, "TMP": tmpdir}
        with subprocess.Popen(cmd, cwd=root, env=run_env, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT) as proc:
            if active is not None and active_lock is not None:
                with active_lock:
                    if stopping is not None and stopping.is_set():
                        terminate_process(proc)
                    else:
                        active.add(proc)
            try:
                output, _ = proc.communicate()
            except BaseException:
                terminate_process(proc)
                proc.wait()
                raise
            finally:
                if active is not None and active_lock is not None:
                    with active_lock:
                        active.discard(proc)
        return subprocess.CompletedProcess(cmd, proc.returncode, output)


def report_result(rel: str, result: subprocess.CompletedProcess, failed: list[str],
                  print_lock: threading.Lock | None) -> None:
    """Record and print any elaboration failure or message for `rel`."""
    if result.returncode or result.stdout.strip():
        failed.append(rel)
        # `lake lean` first builds the file's imports and replays their logs, so a message can
        # also come from an import that this checkout built with warnings.
        message = (f"FAIL  {rel} (restored or missing trace; messages from it or its "
                   f"imports)\n{result.stdout.rstrip()}")
        if print_lock is None:
            print(message, flush=True)
        else:
            with print_lock:
                print(message, flush=True)


def main(argv: list[str] | None = None, root: Path = ROOT) -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--files-from", type=Path,
                        help="JSON list of affected source paths; default: all built root sources")
    parser.add_argument("--built-under", action="append", default=[],
                        help="also check built sources at this file or under this directory")
    parser.add_argument("--jobs", "-j", type=int,
                        help=f"concurrent elaborations (>= 1; default: ${JOBS_ENV} or up to "
                             f"{DEFAULT_JOBS_CAP})")
    progress = parser.add_mutually_exclusive_group()
    progress.add_argument("--progress", action="store_true", dest="progress",
                          help="show source-by-source progress, including in CI")
    progress.add_argument("--quiet", action="store_false", dest="progress",
                          help="suppress progress lines, retaining failures and the summary")
    parser.set_defaults(progress=not os.environ.get("CI"))
    args = parser.parse_args(argv)
    started = time.monotonic()
    try:
        jobs = resolve_jobs(args.jobs)
        selected = json.loads(args.files_from.read_text()) if args.files_from else None
        if args.files_from and (not isinstance(selected, list)
                                or any(not isinstance(rel, str) for rel in selected)):
            raise ValueError("--files-from must contain a JSON list of source paths")
        files = restored_files(root, selected, args.built_under)
    except (OSError, ValueError) as error:
        print(f"Cannot audit restored sources: {error}", file=sys.stderr)
        return 1
    workers = min(jobs, max(1, len(files)))
    worker_env = ({**os.environ, "LEAN_NUM_THREADS": "1"}
                  if workers > 1 and os.environ.get("LEAN_NUM_THREADS") != "1" else None)
    if args.progress:
        mode = "serially" if workers == 1 else f"with {workers} worker(s)"
        print(f"Cache-restore audit: checking {len(files)} source(s) {mode}.", flush=True)
    failed: list[str] = []
    print_lock = threading.Lock() if workers > 1 else None
    active_procs: set[subprocess.Popen] | None = set() if workers > 1 else None
    active_lock = threading.Lock() if workers > 1 else None
    stopping = threading.Event() if workers > 1 else None

    def run_one(index: int, rel: str) -> subprocess.CompletedProcess:
        if stopping is not None and stopping.is_set():
            # Placeholder result for aborted workers; only consumed when re-raising an exception.
            return subprocess.CompletedProcess([], -15, "")
        if args.progress:
            line = (f"Cache-restore audit [{index + 1}/{len(files)}]: {rel} "
                    f"(elapsed {time.monotonic() - started:.1f}s)")
            if print_lock is None:
                print(line, flush=True)
            else:
                with print_lock:
                    if stopping is None or not stopping.is_set():
                        print(line, flush=True)
        if workers == 1:
            return elaborate(root, rel)
        kwargs: dict[str, object] = {}
        if worker_env is not None:
            kwargs["env"] = worker_env
        if active_procs is not None and active_lock is not None and stopping is not None:
            kwargs["active"] = active_procs
            kwargs["active_lock"] = active_lock
            kwargs["stopping"] = stopping
        return elaborate(root, rel, **kwargs)

    if workers == 1:
        for index, rel in enumerate(files):
            report_result(rel, run_one(index, rel), failed, None)
    else:
        previous_sigterm = None
        def handle_sigterm(signum, frame):
            raise KeyboardInterrupt

        try:
            previous_sigterm = signal.signal(signal.SIGTERM, handle_sigterm)
        except (ValueError, OSError):
            pass

        next_submit = 0
        next_report = 0
        completed: dict[int, subprocess.CompletedProcess] = {}
        in_flight: dict[concurrent.futures.Future[subprocess.CompletedProcess], int] = {}
        executor = concurrent.futures.ThreadPoolExecutor(max_workers=workers)
        try:
            while next_submit < len(files) and len(in_flight) < workers:
                in_flight[executor.submit(run_one, next_submit, files[next_submit])] = next_submit
                next_submit += 1
            while in_flight:
                done, _ = concurrent.futures.wait(
                    in_flight, return_when=concurrent.futures.FIRST_COMPLETED)
                for future in sorted(done, key=in_flight.__getitem__):
                    index = in_flight.pop(future)
                    completed[index] = future.result()
                while next_report in completed:
                    report_result(files[next_report], completed.pop(next_report), failed,
                                  print_lock)
                    next_report += 1
                while next_submit < len(files) and len(in_flight) < workers:
                    in_flight[executor.submit(run_one, next_submit,
                                              files[next_submit])] = next_submit
                    next_submit += 1
        except BaseException:
            if active_procs is not None and active_lock is not None and stopping is not None:
                with active_lock:
                    stopping.set()
                    running = list(active_procs)
                for proc in running:
                    terminate_process(proc)
            executor.shutdown(wait=True, cancel_futures=True)
            raise
        else:
            executor.shutdown(wait=True)
        finally:
            if previous_sigterm is not None:
                try:
                    signal.signal(signal.SIGTERM, previous_sigterm)
                except (ValueError, OSError):
                    pass
    elapsed = time.monotonic() - started
    if failed:
        print(f"Re-elaborating {len(failed)} file(s) with restored or missing traces "
              "printed messages that `lake build --wfail --iofail` did not replay; "
              f"see #4523. Audit elapsed {elapsed:.1f}s.",
              file=sys.stderr)
        return 1
    print(f"Files with restored or missing traces re-elaborated cleanly ({len(files)}) "
          f"in {elapsed:.1f}s.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
