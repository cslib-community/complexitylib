"""Windows/Cygwin cache process supervision; the child enrolls before starting a downloader."""

import ctypes
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid


DWORD = ctypes.c_uint32
HANDLE = ctypes.c_void_p
SIZE_T = ctypes.c_size_t


class BasicLimits(ctypes.Structure):
    _fields_ = [("process_time", ctypes.c_int64), ("job_time", ctypes.c_int64),
                ("flags", DWORD), ("minimum_working_set", SIZE_T), ("maximum_working_set", SIZE_T),
                ("active_limit", DWORD), ("affinity", SIZE_T), ("priority", DWORD), ("scheduling", DWORD)]


class IOCounters(ctypes.Structure):
    _fields_ = [(name, ctypes.c_uint64) for name in
                ("read_operations", "write_operations", "other_operations", "read_bytes", "write_bytes", "other_bytes")]


class ExtendedLimits(ctypes.Structure):
    _fields_ = [("basic", BasicLimits), ("io", IOCounters), ("process_memory", SIZE_T),
                ("job_memory", SIZE_T), ("peak_process_memory", SIZE_T), ("peak_job_memory", SIZE_T)]


class Accounting(ctypes.Structure):
    _fields_ = [(name, ctypes.c_int64) for name in ("user", "kernel", "period_user", "period_kernel")] + [
        (name, DWORD) for name in ("faults", "total", "active", "terminated")]


def api():
    # Cygwin's c_ulong is 64-bit: use explicit Windows DWORDs in every ABI declaration.
    kernel = ctypes.WinDLL("kernel32", use_last_error=True) if os.name == "nt" else ctypes.CDLL("kernel32.dll")
    signatures = {
        "CreateJobObjectW": ([HANDLE, ctypes.c_wchar_p], HANDLE),
        "OpenJobObjectW": ([DWORD, ctypes.c_int, ctypes.c_wchar_p], HANDLE),
        "SetInformationJobObject": ([HANDLE, ctypes.c_int, HANDLE, DWORD], ctypes.c_int),
        "QueryInformationJobObject": ([HANDLE, ctypes.c_int, HANDLE, DWORD, HANDLE], ctypes.c_int),
        "AssignProcessToJobObject": ([HANDLE, HANDLE], ctypes.c_int),
        "TerminateJobObject": ([HANDLE, DWORD], ctypes.c_int),
        "GetCurrentProcess": ([], HANDLE),
        "GetLastError": ([], DWORD),
        "CloseHandle": ([HANDLE], ctypes.c_int),
    }
    for name, (arguments, result) in signatures.items():
        function = getattr(kernel, name)
        function.argtypes, function.restype = arguments, result
    return kernel


def checked(kernel, result, operation):
    if not result:
        code = ctypes.get_last_error() if os.name == "nt" else kernel.GetLastError()
        raise OSError(code, operation + " failed")
    return result


class JobShutdownError(RuntimeError):
    pass


class Job:
    def __init__(self):
        self.kernel = api()
        self.name = "Local\\ComplexityCache-" + uuid.uuid4().hex
        self.handle = checked(self.kernel, self.kernel.CreateJobObjectW(None, self.name), "CreateJobObject")
        try:
            limits = ExtendedLimits()
            limits.basic.flags = 0x2000  # JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE; no breakaway permission.
            checked(self.kernel, self.kernel.SetInformationJobObject(
                self.handle, 9, ctypes.byref(limits), ctypes.sizeof(limits)), "SetInformationJobObject")
        except BaseException:
            self.close()
            raise

    def active(self):
        counters = Accounting()
        checked(self.kernel, self.kernel.QueryInformationJobObject(
            self.handle, 1, ctypes.byref(counters), ctypes.sizeof(counters), None), "QueryInformationJobObject")
        return counters.active

    def stop(self, process, grace):
        deadline = time.monotonic() + grace
        while True:
            checked(self.kernel, self.kernel.TerminateJobObject(self.handle, 124), "TerminateJobObject")
            if process.poll() is None:
                # The wrapper may still be starting before it has enrolled. It cannot
                # start a downloader before enrollment, but reap that wrapper as well.
                process.kill()
            if self.active() == 0 and process.poll() is not None:
                return
            if time.monotonic() >= deadline:
                raise JobShutdownError("Windows cache job did not drain; refusing overlapping build/download")
            time.sleep(.025)

    def close(self):
        if self.handle:
            self.kernel.CloseHandle(self.handle)
            self.handle = None


def run(args, *, timeout, cwd, env, grace, capture_output, cleanup_context):
    job = Job()
    process = None
    try:
        # Isolated startup prevents user Python startup hooks from starting a downloader
        # before the wrapper has enrolled. This uses the already-running Python, including Cygwin.
        wrapper = [sys.executable, "-I", "-S", "-B", str(Path(__file__).resolve()), "--child", job.name, *args]
        process = subprocess.Popen(wrapper, cwd=cwd, env=env,
                                   stdout=subprocess.PIPE if capture_output else None,
                                   stderr=subprocess.PIPE if capture_output else None,
                                   text=capture_output)
        status, stdout, stderr = 124, None, None
        try:
            stdout, stderr = process.communicate(timeout=timeout)
            status = process.returncode
        except subprocess.TimeoutExpired:
            print(f"warning: optional cache command exceeded {timeout:g}s", file=sys.stderr, flush=True)
        finally:
            with cleanup_context():
                try:
                    job.stop(process, grace)
                except OSError as error:
                    raise JobShutdownError("cannot establish Windows cache shutdown") from error
        return subprocess.CompletedProcess(args, status, stdout, stderr)
    finally:
        job.close()  # Also kills enrolled descendants if cancellation interrupts the supervisor.


def child(name, command):
    kernel = api()
    handle = checked(kernel, kernel.OpenJobObjectW(0x0001, False, name), "OpenJobObject")
    try:
        # Assignment happens in this wrapper BEFORE launching the actual command.
        # Every descendant inherits the job, including native children of Cygwin tools.
        checked(kernel, kernel.AssignProcessToJobObject(handle, kernel.GetCurrentProcess()), "AssignProcessToJobObject")
    finally:
        kernel.CloseHandle(handle)
    # Only the supervising parent keeps a handle open. If it crashes, last-handle
    # close kills the entire job rather than leaving this wrapper holding it alive.
    return subprocess.call(command)


if __name__ == "__main__":
    try:
        if len(sys.argv) < 4 or sys.argv[1] != "--child":
            raise ValueError("private cache supervisor entry point")
        raise SystemExit(child(sys.argv[2], sys.argv[3:]))
    except (OSError, ValueError) as error:
        print(f"Cache process supervision unavailable: {error}", file=sys.stderr)
        raise SystemExit(126)  # Enrollment failed; no downloader was started.
