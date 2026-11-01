"""Exercise Guide selection against real independent shallow Git checkouts.

Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
"""

import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest


ROOT = Path(__file__).resolve().parents[1]


def selector_script():
    """Run the workflow's actual shell block, rather than a second selector."""
    lines = (ROOT / ".github/workflows/guide.yml").read_text().splitlines(keepends=True)
    step = next(i for i, line in enumerate(lines)
                if line.strip() == "- name: Select rendered guide build")
    start = next(i + 1 for i in range(step, len(lines))
                 if lines[i].strip() == "run: |")
    block = []
    for line in lines[start:]:
        if line.strip() and not line.startswith("          "):
            break
        block.append(line)
    return textwrap.dedent("".join(block))


class GuideSelectionTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="guide-selector-test-")
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.env = dict(os.environ)
        for name in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE",
                     "GIT_OBJECT_DIRECTORY", "GIT_ALTERNATE_OBJECT_DIRECTORIES"):
            self.env.pop(name, None)
        self.env.update({
            "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0", "GIT_ALLOW_PROTOCOL": "file",
            "GIT_CONFIG_COUNT": "2", "GIT_CONFIG_KEY_0": "gc.auto",
            "GIT_CONFIG_VALUE_0": "0", "GIT_CONFIG_KEY_1": "maintenance.auto",
            "GIT_CONFIG_VALUE_1": "false",
        })

    def git(self, repo, *args, check=True):
        return subprocess.run(
            ["git", "-c", "gc.auto=0", "-c", "maintenance.auto=false",
             "-c", "user.name=Guide selector test",
             "-c", "user.email=guide-selector@example.invalid", "-C", str(repo), *args],
            env=self.env, text=True, capture_output=True, check=check)

    def checkout(self, changed_path, depth=1):
        """A two-commit origin; the checkout has its tip but initially lacks its base."""
        writer = self.root / "writer"
        writer.mkdir()
        self.git(writer, "init", "-q", "--initial-branch=main")
        (writer / "README.md").write_text("base\n")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "base")
        base = self.git(writer, "rev-parse", "HEAD").stdout.strip()
        target = writer / changed_path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("changed\n")
        self.git(writer, "add", ".")
        self.git(writer, "commit", "-qm", "head")
        head = self.git(writer, "rev-parse", "HEAD").stdout.strip()
        origin = self.root / "origin.git"
        origin.mkdir()
        self.git(origin, "init", "--bare", "-q")
        self.git(writer, "push", "-q", origin.as_uri(), "main")
        checkout = self.root / "checkout"
        checkout.mkdir()
        self.git(checkout, "init", "-q")
        self.git(checkout, "remote", "add", "origin", origin.as_uri())
        self.git(checkout, "fetch", "-q", "--depth=" + str(depth), "origin", "main")
        self.git(checkout, "checkout", "-q", "--detach", "FETCH_HEAD")
        common = Path(self.git(checkout, "rev-parse", "--path-format=absolute",
                               "--git-common-dir").stdout.strip())
        self.assertEqual(common, checkout / ".git")
        self.assertFalse((common / "objects/info/alternates").exists())
        self.assertTrue(all(p.stat().st_nlink == 1 for p in (common / "objects").rglob("*")
                            if p.is_file()))
        return checkout, base, head

    def run_selector(self, checkout, base, event="pull_request"):
        output = self.root / "github-output"
        env = {**self.env, "GITHUB_EVENT_NAME": event,
               "GUIDE_BASE_SHA": base, "GITHUB_OUTPUT": str(output)}
        result = subprocess.run(["bash", "-e", "-c", selector_script()], cwd=checkout,
                                env=env, text=True, capture_output=True, check=False)
        return result, output.read_text() if output.exists() else ""

    def assert_selected(self, changed_path, expected):
        checkout, base, head = self.checkout(changed_path)
        self.assertNotEqual(self.git(checkout, "cat-file", "-e", base + "^{commit}",
                                     check=False).returncode, 0)
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "render=" + expected + "\n")
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)
        self.assertEqual(self.git(checkout, "cat-file", "-e", base + "^{commit}").returncode, 0)
        self.assertEqual(self.git(checkout, "rev-list", "--count", "HEAD").stdout.strip(), "1")

    def test_missing_base_library_change_does_not_render(self):
        self.assert_selected("Complexity/Example.lean", "false")

    def test_missing_base_guide_change_renders(self):
        self.assert_selected("guide/Chapter.lean", "true")

    def test_missing_base_tooling_change_renders(self):
        self.assert_selected("scripts/check_docs.py", "true")

    def test_present_base_needs_no_remote(self):
        checkout, base, head = self.checkout("Complexity/Example.lean", depth=2)
        self.git(checkout, "remote", "remove", "origin")
        result, output = self.run_selector(checkout, base)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "render=false\n")
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)

    def test_unavailable_base_fails_without_selecting_a_mode(self):
        checkout, base, head = self.checkout("guide/Chapter.lean")
        empty = self.root / "unavailable.git"
        empty.mkdir()
        self.git(empty, "init", "--bare", "-q")
        self.git(checkout, "remote", "set-url", "origin", empty.as_uri())
        result, output = self.run_selector(checkout, base)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(output, "")
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)

    def test_manual_run_renders_without_base_or_remote(self):
        checkout, _, head = self.checkout("Complexity/Example.lean")
        self.git(checkout, "remote", "remove", "origin")
        result, output = self.run_selector(checkout, "", event="workflow_dispatch")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(output, "render=true\n")
        self.assertEqual(self.git(checkout, "rev-parse", "HEAD").stdout.strip(), head)


if __name__ == "__main__":
    unittest.main()

