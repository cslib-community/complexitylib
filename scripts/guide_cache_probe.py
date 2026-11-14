"""Diagnostic branch only: measure example builds and changed-source validation."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

REPORT = Path(os.environ["RUNNER_TEMP"]) / "guide-cache-probe-report"
REPORT.mkdir(exist_ok=True)


def build(name, warning=False):
    args = ["lake", "-d", "guide", "build", "--log-level=info", "CslibFrontierGuide"]
    start = time.time()
    proc = subprocess.run(["/usr/bin/time", "-v", "-o", str(REPORT / f"{name}.time"), *args],
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    elapsed = time.time() - start
    print(proc.stdout, flush=True)
    (REPORT / f"{name}.log").write_text(proc.stdout)
    result = {"args": args, "elapsed_seconds": elapsed, "status": proc.returncode,
              "warning_expected": warning}
    (REPORT / f"{name}.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
    if warning:
        assert proc.returncode != 0 and "GUIDE_CACHE_WARNING_FIXTURE" in proc.stdout
    else:
        assert proc.returncode == 0
    return proc.stdout


def main():
    mode = sys.argv[1]
    if mode in ("writer", "reader"):
        assert not Path("guide/.lake/build").exists(), "fresh job must not restore Guide outputs"
        build(mode)
        inventory = {}
        for package in ("verso", "subverso", "MD4Lean", "illuminate"):
            files = [p for p in Path(f".lake/packages/{package}/.lake/build").rglob("*") if p.is_file()]
            inventory[package] = {"files": len(files), "bytes": sum(p.stat().st_size for p in files)}
        (REPORT / "inventory.json").write_text(json.dumps(inventory, indent=2))
    elif mode == "changed-source":
        path = Path("guide/CslibFrontierGuide/FirstSteps.lean")
        original = path.read_text()
        assert original.count("#doc (Manual)") == 1
        try:
            path.write_text(original.replace("#doc (Manual)", "example : True := by trivial\n\n#doc (Manual)", 1))
            output = build("changed-chapter")
            assert "Built CslibFrontierGuide.FirstSteps" in output
            path.write_text(original.replace("#doc (Manual)", 'run_cmd Lean.logWarning "GUIDE_CACHE_WARNING_FIXTURE"\n\n#doc (Manual)', 1))
            build("warning-chapter", warning=True)
        finally:
            path.write_text(original)
        build("restored-source")
        subprocess.run(["git", "diff", "--exit-code", "--", "guide"], check=True)
    else:
        raise ValueError(mode)
    (REPORT / "source.json").write_text(json.dumps({
        "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "guide_source": hashlib.sha256(Path("guide/CslibFrontierGuide/FirstSteps.lean").read_bytes()).hexdigest(),
        "image": os.environ.get("ImageVersion"),
    }, indent=2))


if __name__ == "__main__":
    main()
