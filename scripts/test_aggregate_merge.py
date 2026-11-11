#!/usr/bin/env python3
"""Real Git fixtures for the report-only aggregate verifier; no Lean build is needed."""

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import aggregate_merge as verifier


class AggregateMergeTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="test-aggregate-merge-")
        self.addCleanup(temp.cleanup)
        self.repo = Path(temp.name)
        self.env = verifier.environment()
        self.env.update(GIT_AUTHOR_NAME="Fixture", GIT_AUTHOR_EMAIL="fixture@example.invalid",
                        GIT_COMMITTER_NAME="Fixture", GIT_COMMITTER_EMAIL="fixture@example.invalid")
        self.git("init", "--quiet", "--initial-branch=main")
        self.write("lakefile.toml", 'name = "fixture"\n[[lean_lib]]\nname = "CslibFrontier"\n')
        self.write(".gitattributes", "CslibFrontier.lean merge=union\n")
        for name in ("Init", "Zed"):
            self.write(f"CslibFrontier/{name}.lean", f"-- fixture {name}\n")
        self.aggregate()
        self.base = self.commit("base")

    def git(self, *args):
        return subprocess.run(["git", "-c", "gc.auto=0", "-c", "maintenance.auto=false", *args],
                              cwd=self.repo, env=self.env, check=True,
                              capture_output=True).stdout.decode().strip()

    def write(self, path, content):
        target = self.repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)

    def aggregate(self):
        modules = sorted(".".join(p.relative_to(self.repo).with_suffix("").parts)
                         for p in (self.repo / "CslibFrontier").rglob("*.lean"))
        self.write("CslibFrontier.lean", verifier.MODULE_HEADER.decode() +
                   "".join(f"public import {name}\n" for name in modules))

    def commit(self, message):
        self.git("add", ".")
        self.git("commit", "--quiet", "-m", message)
        return self.git("rev-parse", "HEAD")

    def additions(self, prefix_name="Able", source_name="Beta"):
        self.write(f"CslibFrontier/{prefix_name}.lean", "-- accepted prefix payload\n")
        self.write("prefix-doc.md", "accepted prefix documentation\n")
        self.aggregate()
        prefix = self.commit("prefix")
        self.git("switch", "--quiet", "--detach", self.base)
        self.write(f"CslibFrontier/{source_name}.lean", "-- reviewed feature payload\n")
        self.write("review-doc.md", "reviewed feature documentation\n")
        self.write("CslibFrontierTests/Feature.lean", "-- reviewed fixture\n")
        self.aggregate()
        return prefix, self.commit("reviewed feature")

    def report(self, prefix, source, reviewed=None, base=None):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            status = verifier.main(["--repo", str(self.repo), "--prefix", prefix,
                                    "--source", source, "--reviewed-base", base or self.base,
                                    "--reviewed-head", reviewed or source])
        return status, json.loads(output.getvalue())

    def snapshot(self):
        # Include objects and the fixture's index/refs/config/working files, not just status.
        return {str(p.relative_to(self.repo)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in self.repo.rglob("*") if p.is_file()}

    def test_adjacent_additions_exact_default_and_whole_feature_recovery(self):
        prefix, source = self.additions()
        before = self.snapshot()
        status, report = self.report(prefix, source)
        self.assertEqual(status, 0, report)
        self.assertEqual(report["status"], "verified")
        self.assertEqual(report["conflicts"], ["CslibFrontier.lean"])
        self.assertEqual(report["candidate_tree"], report["default_merge_tree"])
        self.assertEqual(report["recovered_prefix_tree"], self.git("rev-parse", prefix + "^{tree}"))
        self.assertEqual(report["reviewed_paths"],
                         ["CslibFrontier/Beta.lean", "CslibFrontierTests/Feature.lean", "review-doc.md"])
        self.assertEqual(report["canonical_import_count"], 4)
        self.assertTrue(report["isolation"]["no_shared_object_inodes"])
        self.assertEqual(before, self.snapshot(), "verifier mutated inspected repository")

    def test_actual_temporary_git_storage_is_independent(self):
        prefix, source = self.additions()
        with verifier.scratch_git(self.repo, (prefix, source)) as scratch:
            self.assertNotEqual(scratch.root, self.repo / ".git")
            self.assertFalse((scratch.root / ".git").exists())
            self.assertFalse((scratch.root / "objects/info/alternates").exists())
            self.assertFalse((scratch.root / "objects/info/http-alternates").exists())
            self.assertFalse((scratch.root / "shallow").exists())
            source_inodes = {(p.stat().st_dev, p.stat().st_ino)
                             for p in (self.repo / ".git/objects").rglob("*") if p.is_file()}
            temporary_objects = [p for p in (scratch.root / "objects").rglob("*") if p.is_file()]
            self.assertTrue(temporary_objects)
            self.assertTrue(all((p.stat().st_dev, p.stat().st_ino) not in source_inodes
                                for p in temporary_objects))
            # Read a real reviewed payload through the independent fetched objects.
            self.assertIn("CslibFrontier/Beta.lean", scratch.entries(source))

    def test_adjacent_deletions_reconstruct_but_default_union_is_a_limitation(self):
        for name in ("Able", "Beta"):
            self.write(f"CslibFrontier/{name}.lean", "-- removal fixture\n")
        self.aggregate()
        base = self.commit("deletion base")
        (self.repo / "CslibFrontier/Able.lean").unlink()
        self.aggregate()
        prefix = self.commit("remove Able")
        self.git("switch", "--quiet", "--detach", base)
        (self.repo / "CslibFrontier/Beta.lean").unlink()
        self.aggregate()
        source = self.commit("remove Beta")
        status, report = self.report(prefix, source, base=base)
        self.assertEqual(status, 1)
        self.assertEqual(report["status"], "limitation", report)
        self.assertEqual(report["canonical_import_count"], 2)
        self.assertEqual(report["reviewed_entries"], {"CslibFrontier/Beta.lean": None})
        self.assertEqual(report["recovered_prefix_tree"], self.git("rev-parse", prefix + "^{tree}"))
        self.assertNotEqual(report["candidate_tree"], report["default_merge_tree"])

    def test_noncanonical_default_merge_fails_closed(self):
        prefix, source = self.additions("Beta", "Able")
        status, report = self.report(prefix, source)
        self.assertEqual(status, 1)
        self.assertEqual(report["status"], "limitation", report)
        self.assertIn("cannot represent", report["reason"])

    def test_reviewed_feature_after_ordinary_main_merge(self):
        self.write("CslibFrontier/Mid.lean", "-- already landed dependency\n")
        self.aggregate()
        old_main = self.commit("older main")
        self.write("CslibFrontier/Able.lean", "-- accepted prefix addition\n")
        self.aggregate()
        prefix = self.commit("prefix")
        self.git("switch", "--quiet", "--detach", self.base)
        self.write("CslibFrontier/Beta.lean", "-- reviewed feature\n")
        self.aggregate()
        reviewed = self.commit("reviewed feature")
        self.git("merge", "--quiet", "--no-edit", old_main)
        source = self.git("rev-parse", "HEAD")
        status, report = self.report(prefix, source, reviewed=reviewed)
        self.assertEqual(status, 0, report)
        self.assertEqual(report["reviewed_paths"], ["CslibFrontier/Beta.lean"])
        self.assertIn("CslibFrontier/Mid.lean", report["candidate_entries"])

    def test_without_tracked_union_default_conflict_is_a_limitation(self):
        self.write(".gitattributes", "# no aggregate merge driver\n")
        self.base = self.commit("no union base")
        prefix, source = self.additions()
        _, report = self.report(prefix, source)
        self.assertEqual(report["status"], "limitation", report)
        self.assertEqual(report["default_conflicts"], ["CslibFrontier.lean"])

    def test_another_conflicted_file_is_rejected_even_with_union_for_it(self):
        self.write(".gitattributes", "CslibFrontier.lean merge=union\n*.md merge=union\n")
        self.write("shared.md", "base\n")
        self.base = self.commit("shared base")
        prefix, source = self.additions()
        self.write("shared.md", "source\n")
        source = self.commit("source conflict")
        self.git("switch", "--quiet", "--detach", prefix)
        self.write("shared.md", "prefix\n")
        prefix = self.commit("prefix conflict")
        _, report = self.report(prefix, source)
        self.assertEqual(report["status"], "rejected")
        self.assertEqual(report["conflicts"], ["CslibFrontier.lean", "shared.md"])

    def test_changed_preamble_and_hidden_commands_and_invalid_inventories(self):
        prefix, source = self.additions()
        valid = (self.repo / "CslibFrontier.lean").read_text()
        mutations = {
            "preamble": valid.replace("module  -- shake: keep-all", "module -- shake: keep-all"),
            "declaration": valid + "def hidden := 1\n",
            "option": valid + "set_option maxHeartbeats 0\n",
            "comment spoof": valid + "-- public import CslibFrontier.Hidden\n",
            "malformed": valid.replace("public import CslibFrontier.Beta", "public import CslibFrontier..Beta"),
            "duplicate": valid + "public import CslibFrontier.Beta\n",
            "missing": valid.replace("public import CslibFrontier.Beta\n", ""),
            "nonexistent": valid + "public import CslibFrontier.Absent\n",
            "unsorted": valid.replace("public import CslibFrontier.Beta\n", "") +
                        "public import CslibFrontier.Beta\n",
        }
        for label, text in mutations.items():
            with self.subTest(label=label):
                self.git("switch", "--quiet", "--detach", source)
                self.write("CslibFrontier.lean", text)
                bad = self.commit(label)
                status, report = self.report(prefix, bad)
                self.assertEqual(status, 1)
                self.assertEqual(report["status"], "rejected", report)
                self.assertIn("aggregate", report["reason"])

    def test_unreviewed_extra_payload_cannot_hide_behind_aggregate_conflict(self):
        prefix, reviewed = self.additions()
        self.write("unreviewed.md", "not in reviewed feature\n")
        source = self.commit("extra unreviewed payload")
        _, report = self.report(prefix, source, reviewed=reviewed)
        self.assertEqual(report["status"], "rejected", report)
        self.assertIn("forward replay", report["reason"])

    def test_reviewed_payload_byte_and_mode_drift_are_rejected(self):
        prefix, reviewed = self.additions()
        for mode_only in (False, True):
            with self.subTest(mode_only=mode_only):
                self.git("switch", "--quiet", "--detach", reviewed)
                path = self.repo / "CslibFrontier/Beta.lean"
                if mode_only:
                    path.chmod(0o755)
                else:
                    path.write_text("-- changed payload\n")
                source = self.commit("drift")
                _, report = self.report(prefix, source, reviewed=reviewed)
                self.assertEqual(report["status"], "rejected", report)
                self.assertIn("mode/blob changed", report["reason"])

    def test_nonimmutable_reference_and_missing_review_history_are_rejected(self):
        prefix, source = self.additions()
        _, report = self.report("HEAD", source)
        self.assertIn("immutable", report["reason"])
        _, report = self.report(prefix, prefix, reviewed=source)
        self.assertIn("reviewed history", report["reason"])

    def test_no_aggregate_conflict_is_out_of_scope(self):
        _, source = self.additions()
        _, report = self.report(self.base, source)
        self.assertEqual(report["status"], "rejected", report)
        self.assertIn("complete neutral conflict set", report["reason"])

    def test_changed_library_layout_and_symlink_modules_are_rejected(self):
        prefix, source = self.additions()
        self.write("lakefile.toml", 'name = "fixture"\n[[lean_lib]]\n'
                   'name = "CslibFrontier"\nsrcDir = "elsewhere"\n')
        bad = self.commit("changed source directory")
        _, report = self.report(prefix, bad)
        self.assertIn("library layout", report["reason"])
        self.git("switch", "--quiet", "--detach", source)
        (self.repo / "CslibFrontier/Beta.lean").unlink()
        (self.repo / "CslibFrontier/Beta.lean").symlink_to("Init.lean")
        bad = self.commit("symlink module")
        _, report = self.report(prefix, bad)
        self.assertIn("nonregular Lean module", report["reason"])

    def test_local_info_attributes_and_merge_drivers_do_not_change_result(self):
        prefix, source = self.additions("Beta", "Able")
        self.write(".git/info/attributes", "CslibFrontier.lean merge=ours\n")
        self.git("config", "merge.ours.driver", "touch SHOULD_NOT_RUN")
        before = self.snapshot()
        _, report = self.report(prefix, source)
        self.assertEqual(report["status"], "limitation", report)
        self.assertEqual(before, self.snapshot())
        self.assertFalse((self.repo / "SHOULD_NOT_RUN").exists())

    def test_hostile_inherited_git_paths_cannot_redirect_temporary_writes(self):
        prefix, source = self.additions()
        control = self.repo / ".git"
        hostile = {"GIT_DIR": str(control), "GIT_COMMON_DIR": str(control),
                   "GIT_OBJECT_DIRECTORY": str(control / "objects"),
                   "GIT_ALTERNATE_OBJECT_DIRECTORIES": str(control / "objects"),
                   "GIT_INDEX_FILE": str(control / "index"), "GIT_WORK_TREE": str(self.repo)}
        before = self.snapshot()
        with patch.dict(os.environ, hostile):
            status, report = self.report(prefix, source)
        self.assertEqual(status, 0, report)
        self.assertEqual(before, self.snapshot())

    def test_noncanonical_accepted_prefix_is_rejected(self):
        prefix, source = self.additions()
        self.git("switch", "--quiet", "--detach", prefix)
        with (self.repo / "CslibFrontier.lean").open("a") as output:
            output.write("def hidden := 1\n")
        prefix = self.commit("noncanonical accepted prefix")
        _, report = self.report(prefix, source)
        self.assertEqual(report["status"], "rejected", report)
        self.assertIn("prefix: aggregate", report["reason"])


if __name__ == "__main__":
    unittest.main()
