"""Bound optional cache commands and drain their owned process groups before returning."""

from contextlib import contextmanager
import ctypes
import os
import signal
import subprocess
import sys
import tempfile
import time


class UnsafeShutdown(RuntimeError):
    """The caller must not start another cache writer or source build."""


def note_unsafe(env):
    marker = env.get("COMPLEXITYLIB_CACHE_SHUTDOWN_MARKER")
    if marker:
        try:
            descriptor = os.open(marker, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            os.close(descriptor)
        except FileExistsError:
            pass


@contextmanager
def interruptible():
    """Let an outer watchdog interrupt this supervisor without abandoning its children."""
    def cancelled(*_):
        raise KeyboardInterrupt

    previous = signal.signal(signal.SIGTERM, cancelled)
    try:
        yield
    finally:
        signal.signal(signal.SIGTERM, previous)


@contextmanager
def cleanup_signals():
    pending = []
    previous = {sig: signal.signal(sig, lambda *_: pending.append(True))
                for sig in (signal.SIGTERM, signal.SIGINT)}
    try:
        yield
    finally:
        for sig, handler in previous.items():
            signal.signal(sig, handler)
        if pending and sys.exc_info()[0] is None:
            raise KeyboardInterrupt


def stop_group(process, grace):
    with cleanup_signals():
        if not _stop_group(process, grace):
            raise UnsafeShutdown("cache process group did not stop")
    return True


def _stop_group(process, grace):
    def finished():
        process.poll()
        # Linux subreaping lets us reap grandchildren orphaned by the command itself.
        while True:
            try:
                if os.waitpid(-process.pid, os.WNOHANG)[0] == 0:
                    break
            except ChildProcessError:
                break
        try:
            os.killpg(process.pid, 0)
        except ProcessLookupError:
            return True
        return False

    if finished():
        return True
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(process.pid, sig)
        except ProcessLookupError:
            pass
        deadline = time.monotonic() + grace
        while True:
            if finished():
                return True
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                break
            time.sleep(min(.05, remaining))
    return False


def run(args, *, timeout, cwd=None, env=None, grace=5, capture_output=False):
    """Run one command, preserving files it completed, and stop all of its descendants.

    POSIX uses an owned process group; Windows/Cygwin uses a Job Object whose
    wrapper enrolls before launching any downloader, including native children.
    """
    if os.name == "nt" or sys.platform == "cygwin":
        from windows_job import JobShutdownError, run as run_job
        with tempfile.TemporaryDirectory(prefix="cache-supervision-") as temporary:
            child_env = dict(os.environ if env is None else env)
            marker = child_env.setdefault("COMPLEXITYLIB_CACHE_SHUTDOWN_MARKER", temporary + "/unsafe")
            try:
                result = run_job(args, timeout=timeout, cwd=cwd, env=child_env, grace=grace,
                                 capture_output=capture_output, cleanup_context=cleanup_signals)
            except JobShutdownError as error:
                try:
                    note_unsafe(child_env)
                except OSError:
                    pass
                raise UnsafeShutdown(str(error)) from error
            if os.path.exists(marker):
                raise UnsafeShutdown("nested cache shutdown is unconfirmed")
            return result
    if sys.platform.startswith("linux"):
        libc = ctypes.CDLL(None, use_errno=True)
        if libc.prctl(36, 1, 0, 0, 0) != 0:  # PR_SET_CHILD_SUBREAPER, scoped to this supervisor.
            raise OSError(ctypes.get_errno(), "cannot supervise cache descendants")
    with tempfile.TemporaryDirectory(prefix="cache-supervision-") as temporary:
        child_env = dict(os.environ if env is None else env)
        marker = child_env.setdefault("COMPLEXITYLIB_CACHE_SHUTDOWN_MARKER", temporary + "/unsafe")
        process = subprocess.Popen(args, cwd=cwd, env=child_env, start_new_session=True,
                                   stdout=subprocess.PIPE if capture_output else None,
                                   stderr=subprocess.PIPE if capture_output else None,
                                   text=capture_output)
        status, stdout, stderr = 124, None, None
        try:
            try:
                stdout, stderr = process.communicate(timeout=timeout)
                status = process.returncode
            except subprocess.TimeoutExpired:
                print(f"warning: optional cache command exceeded {timeout:g}s", file=sys.stderr,
                      flush=True)
        finally:
            try:
                stopped = stop_group(process, grace)
            except (OSError, UnsafeShutdown):
                stopped = False
            if not stopped:
                try:
                    note_unsafe(child_env)
                except OSError:
                    pass
            # A nested supervisor can fail after its shell has already been killed.
            # Preserve its unsafe result even when our direct child only reports timeout.
            if not stopped or os.path.exists(marker):
                raise UnsafeShutdown("cache process group shutdown unconfirmed; refusing concurrent build/download")
        return subprocess.CompletedProcess(args, status, stdout, stderr)


def seconds(env, name, default, maximum=600):
    try:
        value = float(env.get(name, default))
    except (TypeError, ValueError) as error:
        raise ValueError(f"{name} must be a finite positive number") from error
    if not .1 <= value <= maximum:
        raise ValueError(f"{name} must be between 0.1 and {maximum} seconds")
    return value
