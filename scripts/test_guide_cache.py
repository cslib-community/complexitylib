"""Check Guide-cache compatibility, writer restrictions and failed-restore cleanup.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
"""

import importlib.util
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]
ACTION = ROOT / ".github/actions/cache-guide-deps"
SPEC = importlib.util.spec_from_file_location("guide_cache_key", ACTION / "key.py")
cache = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(cache)


def step(text, name):
    lines = text.splitlines(keepends=True)
    start = next(i for i, line in enumerate(lines) if line.strip() == "- name: " + name)
    indent = len(lines[start]) - len(lines[start].lstrip())
    end = next((i for i in range(start + 1, len(lines))
                if lines[i].strip() and len(lines[i]) - len(lines[i].lstrip()) <= indent), len(lines))
    return textwrap.dedent("".join(lines[start:end]))


class GuideCacheTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="guide-cache-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for name in cache.INPUTS:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((ROOT / name).read_bytes())
        self.env = {"RUNNER_OS": "Linux", "RUNNER_ARCH": "X64", "ImageOS": "ubuntu24",
                    "ImageVersion": "20261111.370.1", "GUIDE_CACHE_GENERATION": "0"}

    def test_every_compatibility_input_invalidates(self):
        original = cache.cache_key(self.root, self.env)
        for name in cache.INPUTS:
            with self.subTest(file=name):
                path = self.root / name
                content = path.read_bytes()
                path.write_bytes(content + b"\n")
                self.assertNotEqual(cache.cache_key(self.root, self.env), original)
                path.write_bytes(content)
        for name in (*cache.MACHINE, "GUIDE_CACHE_GENERATION"):
            with self.subTest(environment=name):
                self.assertNotEqual(cache.cache_key(self.root, self.env | {name: "changed"}), original)

    def test_library_chapters_and_run_ids_do_not_create_entries(self):
        original = cache.cache_key(self.root, self.env)
        for name in ("guide/CslibFrontierGuide.lean", "CslibFrontier.lean"):
            (self.root / name).write_text("changed source\n")
        self.assertEqual(cache.cache_key(self.root, self.env | {
            "GITHUB_SHA": "new commit", "GITHUB_RUN_ID": "123", "GITHUB_REF": "refs/pull/12/merge",
        }), original)

    def test_missing_native_identity_does_not_guess(self):
        for name in cache.MACHINE:
            with self.subTest(name=name), self.assertRaises(ValueError):
                cache.cache_key(self.root, self.env | {name: ""})

    def test_only_the_four_dependency_build_directories_are_cached(self):
        self.assertEqual(set(cache.PATHS), {
            f".lake/packages/{name}/.lake/build" for name in ("verso", "subverso", "MD4Lean", "illuminate")
        })

    def test_failed_restore_cleanup_preserves_sources_and_other_outputs(self):
        for name in (*cache.PATHS, ".lake/build", "guide/.lake/build"):
            target = self.root / name
            target.mkdir(parents=True, exist_ok=True)
            (target / "output").write_text("partial cache\n")
        source = self.root / ".lake/packages/verso/Source.lean"
        source.write_text("source remains\n")
        cleanup = step((ACTION / "action.yml").read_text(), "Discard an incomplete Guide cache restore")
        condition = cleanup.split("if: ", 1)[1].splitlines()[0]
        # actions/cache may catch extraction errors and report a successful miss. That case
        # must clean partial outputs too; only a confirmed exact hit keeps them.
        for outcome, hit, expected in (("failure", "", True), ("success", "", True),
                                        ("success", "false", True), ("success", "true", False)):
            with self.subTest(outcome=outcome, hit=hit):
                expression = condition.replace("steps.restore.outcome", repr(outcome))
                expression = expression.replace("steps.restore.outputs.cache-hit", repr(hit))
                self.assertEqual(eval(expression, {"__builtins__": {}}), expected)
        script = textwrap.dedent(cleanup.split("run: |\n", 1)[1])
        subprocess.run(["bash", "-eu", "-c", script], cwd=self.root, check=True)
        self.assertTrue(source.is_file())
        self.assertTrue((self.root / ".lake/build/output").is_file())
        self.assertTrue((self.root / "guide/.lake/build/output").is_file())
        self.assertTrue(all(not (self.root / name).exists() for name in cache.PATHS))

    def test_main_only_optional_writer_uses_exact_restored_key(self):
        docs = (ROOT / ".github/workflows/docs.yml").read_text()
        guide = (ROOT / ".github/workflows/guide.yml").read_text()
        save = step(docs, "Save Guide dependency builds")
        condition = save.split("if: >-\n", 1)[1].split("continue-on-error:", 1)[0].strip()
        values = {"github.ref": "refs/heads/main", "vars.DISABLE_CACHE_RESTORE": "",
                  "steps.guide-deps.outcome": "success", "steps.guide-deps.outputs.key": "key",
                  "steps.guide-deps.outputs.cache-hit": ""}

        def enabled(**overrides):
            expression = condition
            for key, value in (values | overrides).items():
                expression = expression.replace(key, repr(value))
            return eval(expression.replace("&&", " and ").replace("\n", " "), {"__builtins__": {}})

        self.assertTrue(enabled())
        for ref in ("refs/pull/12/merge", "refs/heads/topic", "refs/heads/gh-readonly-queue/main/test"):
            self.assertFalse(enabled(**{"github.ref": ref}))
        for disabled in ("true", "1"):
            self.assertFalse(enabled(**{"vars.DISABLE_CACHE_RESTORE": disabled}))
        for key, value in (("steps.guide-deps.outcome", "failure"),
                           ("steps.guide-deps.outputs.key", ""),
                           ("steps.guide-deps.outputs.cache-hit", "true")):
            self.assertFalse(enabled(**{key: value}))
        self.assertIn("continue-on-error: true", save)
        self.assertIn("key: ${{ steps.guide-deps.outputs.key }}", save)
        self.assertIn("path: ${{ steps.guide-deps.outputs.paths }}", save)
        self.assertNotIn("actions/cache/save", guide)
        self.assertNotIn("restore-keys:", (ACTION / "action.yml").read_text())
        self.assertLess(docs.index("run: python3 scripts/check_docs.py --trim --guide"), docs.index("- name: Save Guide"))

    def test_cache_never_conditions_guide_validation(self):
        for name in ("guide.yml", "docs.yml"):
            workflow = (ROOT / ".github/workflows" / name).read_text()
            restore = step(workflow, "Restore Guide dependencies")
            self.assertIn("continue-on-error: true", restore)
            self.assertIn("vars.DISABLE_CACHE_RESTORE != 'true'", restore)
            self.assertIn("vars.DISABLE_CACHE_RESTORE != '1'", restore)
            build = step(workflow, "Build the guide")
            self.assertNotIn("cache-hit", build)
            self.assertIn("run: scripts/guide.sh", build)
        guide = (ROOT / ".github/workflows/guide.yml").read_text()
        self.assertIn('".github/actions/cache-guide-deps/**"', guide)
        self.assertIn(".github/actions/cache-guide-deps", step(guide, "Select rendered guide build"))
        self.assertNotIn("if:", step(guide, "Compile guide examples"))


if __name__ == "__main__":
    unittest.main()
