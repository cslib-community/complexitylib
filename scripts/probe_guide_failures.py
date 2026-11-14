"""Diagnostic branch only: exercise the reviewed Guide helper's failure boundaries."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

REPORT = Path(os.environ["RUNNER_TEMP"]) / "guide-failure-probes"
REPORT.mkdir(exist_ok=True)
CHAPTER = Path("guide/CslibFrontierGuide/FirstSteps.lean")
MAIN = Path("guide/CslibFrontierGuideMain.lean")
HELPER = ["bash", "scripts/guide.sh"]


def save(name, data):
    (REPORT / f"{name}.json").write_text(json.dumps(data, indent=2) + "\n")


def hashes(path):
    return {str(p.relative_to(path)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(path.rglob("*")) if p.is_file()}


def run(name, command, status=0, marker=None):
    start = time.monotonic()
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (REPORT / f"{name}.log").write_text(result.stdout)
    summary = {"command": command, "seconds": time.monotonic() - start,
               "status": result.returncode, "expected_status": status, "marker": marker}
    save(name, summary)
    print(result.stdout, flush=True)
    print(json.dumps(summary), flush=True)
    assert result.returncode == status, summary
    if marker:
        assert marker in result.stdout, f"missing diagnostic {marker}"
    if status:
        assert "Guide written to" not in result.stdout, "failure reported success"
    return result.stdout


def chapter_fixture(original, code):
    assert original.count("#doc (Manual)") == 1
    return original.replace("#doc (Manual)", code + "\n\n#doc (Manual)", 1)


def main():
    mode = sys.argv[1]
    original_chapter, original_main = CHAPTER.read_text(), MAIN.read_text()
    try:
        if mode == "prepare":
            save("source", {
                "head": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                "production_head": "849ae53393f13cd106a3e48e255bf5073a7db35d",
                "helper_sha256": hashlib.sha256(Path("scripts/guide.sh").read_bytes()).hexdigest(),
                "chapter_sha256": hashlib.sha256(CHAPTER.read_bytes()).hexdigest(),
                "main_sha256": hashlib.sha256(MAIN.read_bytes()).hexdigest(),
                "root_cache": os.environ.get("PROFILE_ROOT_CACHE"),
            })
            run("unchanged-helper", HELPER)
            save("baseline-site", hashes(Path("guide/.lake/build/site")))
        elif mode == "chapter":
            CHAPTER.write_text(chapter_fixture(original_chapter,
                'run_cmd Lean.logWarning "GUIDE_CHAPTER_WARNING_FIXTURE"'))
            run("chapter-warning", HELPER, status=1, marker="error: GUIDE_CHAPTER_WARNING_FIXTURE")
            CHAPTER.write_text(chapter_fixture(original_chapter,
                'run_cmd Lean.logError "GUIDE_CHAPTER_ERROR_FIXTURE"'))
            run("chapter-error", HELPER, status=1, marker="error: GUIDE_CHAPTER_ERROR_FIXTURE")
        elif mode == "generator":
            # Same module frontend/options as native generation, without repeating C compilation.
            MAIN.write_text(original_main + '\nrun_cmd Lean.logWarning "GUIDE_GENERATOR_WARNING_FIXTURE"\n')
            run("generator-warning-native-frontend",
                ["lake", "-d", "guide", "build", "--log-level=info",
                 "+CslibFrontierGuideMain:leanArts"], marker="warning: GUIDE_GENERATOR_WARNING_FIXTURE")
            run("generator-warning-helper", HELPER, marker="warning: GUIDE_GENERATOR_WARNING_FIXTURE")
            before = json.loads((REPORT / "baseline-site.json").read_text())
            after = hashes(Path("guide/.lake/build/site"))
            save("warning-output", {"equal": before == after, "files": len(after), "hashes": after})
            assert before == after, "nonfatal warning changed generated output"
            MAIN.write_text(original_main + '\nrun_cmd Lean.logError "GUIDE_GENERATOR_ERROR_FIXTURE"\n')
            run("generator-error", HELPER, status=1, marker="error: GUIDE_GENERATOR_ERROR_FIXTURE")
            assert original_main.count("def main (options") == 1
            MAIN.write_text(original_main.split("def main (options", 1)[0] + '''def main (_options : List String) : IO UInt32 := do
  IO.eprintln "GUIDE_RUNTIME_EXIT_FIXTURE"
  return 23
''')
            run("generator-runtime-exit", HELPER, status=23, marker="GUIDE_RUNTIME_EXIT_FIXTURE")
        elif mode == "restored":
            run("restored-helper", HELPER)
            before = json.loads((REPORT / "baseline-site.json").read_text())
            after = hashes(Path("guide/.lake/build/site"))
            assert before == after, "restored source did not restore original output"
            save("restored-output", {"equal": True, "files": len(after)})
        else:
            raise ValueError(mode)
    finally:
        CHAPTER.write_text(original_chapter)
        MAIN.write_text(original_main)
    subprocess.run(["git", "diff", "--exit-code", "--", "guide", "scripts/guide.sh"], check=True)
    save(f"{mode}-passed", True)


if __name__ == "__main__":
    main()
