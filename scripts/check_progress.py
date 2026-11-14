"""Keep check logs while showing cache-audit progress before the command finishes."""

from __future__ import annotations

import subprocess
from typing import BinaryIO, TextIO


PROGRESS_PREFIXES = (b"Cache-restore audit", b"Files with restored or missing traces",
                     b"Re-elaborating ")


def run_logged(command, *, log: BinaryIO, progress: TextIO | None = None,
               **kwargs) -> subprocess.CompletedProcess:
    if progress is None:
        return subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, **kwargs)
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          **kwargs) as child:
        try:
            for line in child.stdout:
                log.write(line)
                log.flush()
                if line.startswith(PROGRESS_PREFIXES):
                    progress.write(line.decode(errors="replace"))
                    progress.flush()
            return subprocess.CompletedProcess(command, child.wait())
        except BaseException:
            # Match subprocess.run's interruption handling: reap the child and propagate the
            # exception rather than reporting a completed check or continuing to the next one.
            child.kill()
            child.wait()
            raise
