"""Temporary-repository tests for worktree branch selection, cache bootstrap, and isolation."""

from __future__ import annotations

import os
import pathlib
import shutil
import stat
import subprocess
import tempfile
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parent / "worktree.sh"

GIT_ENV = {
    **os.environ,
    "GIT_AUTHOR_NAME": "Test",
    "GIT_AUTHOR_EMAIL": "test@example.com",
    "GIT_COMMITTER_NAME": "Test",
    "GIT_COMMITTER_EMAIL": "test@example.com",
    "GIT_CONFIG_GLOBAL": os.devnull,
    "GIT_CONFIG_NOSYSTEM": "1",
    "COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP": "1",
}


def git(cwd: pathlib.Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(cwd), *args],
        capture_output=True,
        text=True,
        check=True,
        env=GIT_ENV,
    ).stdout.strip()


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreeCreateTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.origin = self.tmp / "origin.git"
        subprocess.run(
            ["git", "init", "--quiet", "--bare", "-b", "main", str(self.origin)],
            check=True,
            env=GIT_ENV,
        )
        # A second clone plays the other worker, who pushes branches.
        self.other = self.clone("other")
        (self.other / "README").write_text("base\n", encoding="utf-8")
        git(self.other, "add", "README")
        git(self.other, "commit", "--quiet", "-m", "base")
        git(self.other, "push", "--quiet", "origin", "main")
        self.main_sha = git(self.other, "rev-parse", "HEAD")
        self.feature_sha = self.push_branch("feature/takeover")
        self.work = self.clone("work")
        (self.work / "scripts").mkdir()
        shutil.copy(SCRIPT, self.work / "scripts/worktree.sh")

    def clone(self, name: str) -> pathlib.Path:
        path = self.tmp / name
        subprocess.run(
            ["git", "clone", "--quiet", str(self.origin), str(path)],
            check=True,
            env=GIT_ENV,
            capture_output=True,
        )
        return path

    def push_branch(self, branch: str) -> str:
        git(self.other, "switch", "--quiet", "-c", branch, self.main_sha)
        (self.other / "work.txt").write_text(f"{branch}\n", encoding="utf-8")
        git(self.other, "add", "work.txt")
        git(self.other, "commit", "--quiet", "-m", f"work on {branch}")
        git(self.other, "push", "--quiet", "origin", branch)
        sha = git(self.other, "rev-parse", "HEAD")
        git(self.other, "switch", "--quiet", "main")
        return sha

    def create(self, *args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.work / "scripts/worktree.sh"), "create", *args],
            cwd=self.work,
            capture_output=True,
            text=True,
            check=False,
            env=env or GIT_ENV,
        )

    def upstream(self, wt: pathlib.Path) -> str | None:
        proc = subprocess.run(
            ["git", "-C", str(wt), "rev-parse", "--abbrev-ref", "@{upstream}"],
            capture_output=True,
            text=True,
            check=False,
            env=GIT_ENV,
        )
        return proc.stdout.strip() if proc.returncode == 0 else None

    def bootstrap_probe(self) -> dict[str, str]:
        ensure = self.work / "scripts/cache/ensure.sh"
        ensure.parent.mkdir(parents=True, exist_ok=True)
        ensure.write_text(
            '#!/usr/bin/env bash\nset -eu\n'
            'printf "%s\\n" "$PWD" >> "$BOOTSTRAP_LOG"\n'
            'printf "%s\\n" "$0" > .bootstrap-script\n'
            'if [ -e .lake ]; then printf seeded; else printf empty; fi > .bootstrap-entry\n'
            'mkdir -p .lake/build\n'
            'printf fetched > .lake/build/bootstrap-artifact\n',
            encoding="utf-8",
        )
        ensure.chmod(0o755)
        return {**GIT_ENV, "COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP": "0",
                "BOOTSTRAP_LOG": str(self.tmp / "bootstrap.log")}

    def primary_caches(self) -> pathlib.Path:
        package = self.work / ".lake/packages/cslib"
        package.mkdir(parents=True)
        git(package, "init", "--quiet", "-b", "main")
        (package / "Source.lean").write_text("package source\n", encoding="utf-8")
        git(package, "add", "Source.lean")
        git(package, "commit", "--quiet", "-m", "dependency")
        for path in (".lake/build/root-output", ".lake/config/lakefile.olean",
                     ".lake/packages/cslib/.lake/build/dependency-output"):
            target = self.work / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text("primary output\n", encoding="utf-8")
        return package

    def test_remote_only_branch_tracks_origin(self) -> None:
        proc = self.create("feature/takeover", "takeover")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/takeover"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), self.feature_sha)
        self.assertEqual(self.upstream(wt), "origin/feature/takeover")

    def test_branch_pushed_after_clone_is_fetched_and_tracked(self) -> None:
        late_sha = self.push_branch("feature/late")
        proc = self.create("feature/late", "late")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/late"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), late_sha)
        self.assertEqual(self.upstream(wt), "origin/feature/late")

    def test_remote_only_branch_with_base_ref_is_refused(self) -> None:
        proc = self.create("feature/takeover", "takeover", "origin/main")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("exists on origin", proc.stderr)
        self.assertFalse((self.work / ".worktrees/takeover").exists())
        self.assertEqual(git(self.work, "branch", "--list", "feature/takeover"), "")

    def test_new_branch_starts_from_origin_main_without_upstream(self) -> None:
        proc = self.create("feature/fresh", "fresh")
        self.assertEqual(proc.returncode, 0, proc.stderr)
        wt = self.work / ".worktrees/fresh"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), self.main_sha)
        self.assertIsNone(self.upstream(wt))

    def test_conflicting_copy_flags_are_refused(self) -> None:
        proc = self.create("feature/fresh", "fresh", "--copy-cslib", "--copy-packages")
        self.assertNotEqual(proc.returncode, 0)
        self.assertIn("mutually exclusive", proc.stderr)
        self.assertFalse((self.work / ".worktrees/fresh").exists())

    def test_source_only_conflicts_with_copy_flags_in_either_order(self) -> None:
        for flag in ("--copy-cslib", "--copy-packages"):
            for flags in (("--source-only", flag), (flag, "--source-only")):
                with self.subTest(flags=flags):
                    proc = self.create("feature/fresh", "fresh", *flags)
                    self.assertNotEqual(proc.returncode, 0)
                    self.assertIn("cannot be combined", proc.stderr)
                    self.assertFalse((self.work / ".worktrees/fresh").exists())
                    self.assertEqual(git(self.work, "branch", "--list", "feature/fresh"), "")

    def test_source_only_bootstraps_without_copying_sources_outputs_or_controls(self) -> None:
        package = self.primary_caches()
        before_head = (package / ".git/HEAD").read_bytes()
        env = self.bootstrap_probe()
        git(self.work, "add", "scripts/cache/ensure.sh")
        git(self.work, "commit", "--quiet", "-m", "fixture bootstrap")
        result = self.create("feature/source-only", "--source-only", "source-only", "HEAD", env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        wt = self.work / ".worktrees/source-only"
        self.assertEqual((wt / ".bootstrap-entry").read_text(), "empty")
        self.assertEqual((wt / ".lake/build/bootstrap-artifact").read_text(), "fetched")
        self.assertFalse((wt / ".lake/packages").exists())
        self.assertFalse((wt / ".lake/config").exists())
        self.assertFalse((wt / ".lake/build/root-output").exists())
        script = pathlib.Path((wt / ".bootstrap-script").read_text().strip())
        if not script.is_absolute():
            script = wt / script
        self.assertEqual(script.resolve(), wt / "scripts/cache/ensure.sh")
        self.assertEqual((package / ".git/HEAD").read_bytes(), before_head)
        for path in (".lake/build/root-output", ".lake/config/lakefile.olean",
                     ".lake/packages/cslib/.lake/build/dependency-output"):
            self.assertEqual((self.work / path).read_text(), "primary output\n")
        self.assertFalse((self.work / ".lake/build/bootstrap-artifact").exists())
        self.assertEqual(pathlib.Path(self.tmp / "bootstrap.log").read_text().strip(), str(wt))

    def test_default_create_still_seeds_before_bootstrap(self) -> None:
        package = self.primary_caches()
        env = self.bootstrap_probe()
        result = self.create("feature/seeded", "seeded", env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        wt = self.work / ".worktrees/seeded"
        self.assertEqual((wt / ".bootstrap-entry").read_text(), "seeded")
        for path in (".lake/build/root-output", ".lake/config/lakefile.olean",
                     ".lake/packages/cslib/.lake/build/dependency-output"):
            primary, copied = self.work / path, wt / path
            self.assertEqual(copied.read_bytes(), primary.read_bytes())
            self.assertFalse(os.path.samefile(primary, copied))
        copied_package = wt / ".lake/packages/cslib"
        self.assertTrue(os.path.samefile(package / "Source.lean", copied_package / "Source.lean"))
        self.assertNotEqual(git(package, "rev-parse", "--absolute-git-dir"),
                            git(copied_package, "rev-parse", "--absolute-git-dir"))
        self.assertFalse((self.work / ".lake/build/bootstrap-artifact").exists())

    def test_source_only_respects_explicit_bootstrap_opt_out(self) -> None:
        self.primary_caches()
        env = {**self.bootstrap_probe(), "COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP": "1"}
        result = self.create("feature/no-bootstrap", "no-bootstrap", "--source-only", env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        wt = self.work / ".worktrees/no-bootstrap"
        self.assertFalse((wt / ".lake").exists())
        self.assertFalse((self.tmp / "bootstrap.log").exists())

    def test_source_only_takeover_tracks_origin_without_initial_copies(self) -> None:
        self.primary_caches()
        result = self.create("feature/takeover", "takeover", "--source-only")
        self.assertEqual(result.returncode, 0, result.stderr)
        wt = self.work / ".worktrees/takeover"
        self.assertEqual(git(wt, "rev-parse", "HEAD"), self.feature_sha)
        self.assertEqual(self.upstream(wt), "origin/feature/takeover")
        self.assertFalse((wt / ".lake").exists())

    def test_both_create_modes_refuse_existing_target_and_cache_symlinks_before_bootstrap(self) -> None:
        env = self.bootstrap_probe()
        protected = self.work / "protected"
        protected.mkdir()
        sentinel = protected / "sentinel"
        sentinel.write_text("primary content\n", encoding="utf-8")
        for mode in ((), ("--source-only",)):
            for path in (".", ".lake", ".lake/packages", ".lake/build", ".lake/config",
                         ".lake/packages/cslib", ".lake/packages/cslib/.lake",
                         ".lake/packages/cslib/.lake/build", ".lake/packages/cslib/.lake/config",
                         ".lake/build/lib/lean", ".lake/packages/cslib/.lake/build/lib/lean"):
                with self.subTest(mode=mode, path=path):
                    name = f"existing-{len(mode)}-{path.replace('/', '-')}"
                    wt = self.work / ".worktrees" / name
                    link = wt if path == "." else wt / path
                    link.parent.mkdir(parents=True, exist_ok=True)
                    link.symlink_to(protected, target_is_directory=True)
                    before = git(self.work, "worktree", "list", "--porcelain")
                    result = self.create(f"feature/{name}", name, *mode, env=env)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("primary checkout" if path == "." else "symlink", result.stderr)
                    self.assertEqual(git(self.work, "worktree", "list", "--porcelain"), before)
                    self.assertFalse((self.tmp / "bootstrap.log").exists())
                    self.assertEqual(sentinel.read_text(), "primary content\n")

    def test_both_create_modes_refuse_checked_out_cache_symlinks_before_bootstrap(self) -> None:
        env = self.bootstrap_probe()
        protected = self.work / "protected"
        protected.mkdir()
        sentinel = protected / "sentinel"
        sentinel.write_text("primary content\n", encoding="utf-8")
        for index, path in enumerate((".lake/build", ".lake/packages/cslib/.lake/build")):
            link = self.work / path
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(protected, target_is_directory=True)
            git(self.work, "add", path)
            git(self.work, "commit", "--quiet", "-m", "fixture with unsafe cache link")
            for mode in ((), ("--source-only",)):
                with self.subTest(path=path, mode=mode):
                    name = f"checked-out-{index}-{len(mode)}"
                    result = self.create(f"feature/{name}", name, "HEAD", *mode, env=env)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("destination cache symlink", result.stderr)
                    self.assertTrue((self.work / ".worktrees" / name / path).is_symlink())
                    self.assertFalse((self.tmp / "bootstrap.log").exists())
                    self.assertEqual(sentinel.read_text(), "primary content\n")
            git(self.work, "rm", "--quiet", path)
            git(self.work, "commit", "--quiet", "-m", "remove unsafe fixture cache link")

    def test_nested_cache_links_cannot_redirect_bootstrap_writes_to_primary(self) -> None:
        env = self.bootstrap_probe()
        ensure = self.work / "scripts/cache/ensure.sh"
        with ensure.open("a", encoding="utf-8") as stream:
            stream.write('printf altered > "$BOOTSTRAP_WRITE_PATH/sentinel"\n')
        protected = self.work / "protected"
        protected.mkdir()
        sentinel = protected / "sentinel"
        for index, path in enumerate((".lake/build/lib/lean",
                                      ".lake/packages/cslib/.lake/build/lib/lean")):
            link = self.work / path
            link.parent.mkdir(parents=True, exist_ok=True)
            link.symlink_to(protected, target_is_directory=True)
            git(self.work, "add", path)
            git(self.work, "commit", "--quiet", "-m", "fixture with nested cache link")
            for mode in ((), ("--source-only",)):
                with self.subTest(path=path, mode=mode):
                    sentinel.write_text("primary content\n", encoding="utf-8")
                    log = self.tmp / "bootstrap.log"
                    log.unlink(missing_ok=True)
                    name = f"nested-{index}-{len(mode)}"
                    result = self.create(f"feature/{name}", name, "HEAD", *mode,
                                         env={**env, "BOOTSTRAP_WRITE_PATH": path})
                    self.assertEqual((result.returncode != 0, log.exists(), sentinel.read_text()),
                                     (True, False, "primary content\n"), result.stderr)
                    self.assertIn("destination cache symlink", result.stderr)
            git(self.work, "rm", "--quiet", path)
            git(self.work, "commit", "--quiet", "-m", "remove nested fixture cache link")

    def test_create_isolates_seeded_dependency_caches(self) -> None:
        paths = [pathlib.Path(".lake/packages/cslib/.lake") / part
                 for part in ("build/trace", "config/lakefile.olean")]
        for path in paths:
            cache = self.work / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_bytes(b"root cache\n")
        result = self.create("feature/fresh", "fresh")
        self.assertEqual(result.returncode, 0, result.stderr)
        for path in paths:
            root, worker = self.work / path, self.work / ".worktrees/fresh" / path
            self.assertFalse(os.path.samefile(root, worker))
            worker.write_bytes(b"worker cache\n")
            self.assertEqual(root.read_bytes(), b"root cache\n")

    def test_create_runs_cache_bootstrap_when_present(self) -> None:
        ensure = self.work / "scripts/cache/ensure.sh"
        ensure.parent.mkdir(parents=True, exist_ok=True)
        ensure.write_text(
            "#!/usr/bin/env bash\nprintf 'bootstrapped %s\\n' \"$PWD\" > .cache-bootstrapped\n",
            encoding="utf-8",
        )
        ensure.chmod(0o755)
        env = {**GIT_ENV, "COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP": "0"}
        result = self.create("feature/bootstrap", "bootstrap", env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        marker = self.work / ".worktrees/bootstrap/.cache-bootstrapped"
        self.assertTrue(marker.is_file())
        self.assertIn(".worktrees/bootstrap", marker.read_text(encoding="utf-8"))

    def test_create_fallback_cache_bootstrap_targets_worktree_not_root(self) -> None:
        repo_root = SCRIPT.parent.parent
        ensure_src = repo_root / "scripts/cache/ensure.sh"
        ensure = self.work / "scripts/cache/ensure.sh"
        ensure.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(ensure_src, ensure)
        ensure.chmod(0o755)
        get_sh = self.work / "scripts/cache/get.sh"
        get_sh.write_text(
            "#!/usr/bin/env bash\n"
            "set -euo pipefail\n"
            "target=\"${COMPLEXITYLIB_CACHE_CHECKOUT:-$PWD}\"\n"
            "mkdir -p \"$target/.lake/build\"\n"
            "printf '%s\\n' \"$PWD\" > \"$target/.lake/build/fetched-from\"\n",
            encoding="utf-8",
        )
        get_sh.chmod(0o755)
        env = {**GIT_ENV, "COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP": "0"}
        result = self.create("feature/fallback-bootstrap", "fallback-bootstrap", env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        wt = (self.work / ".worktrees/fallback-bootstrap").resolve()
        self.assertFalse((wt / "scripts/cache/ensure.sh").exists())
        fetched = wt / ".lake/build/fetched-from"
        self.assertTrue(fetched.is_file())
        self.assertEqual(pathlib.Path(fetched.read_text(encoding="utf-8").strip()).resolve(), wt)
        self.assertTrue((wt / ".lake/cache-bootstrap/attempt.json").is_file())
        self.assertFalse((self.work / ".lake/cache-bootstrap/attempt.json").exists())


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreeSeedTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.root = self.tmp / "root"
        self.root.mkdir()
        git(self.root, "init", "--quiet")
        (self.root / "scripts").mkdir()
        shutil.copy(SCRIPT, self.root / "scripts/worktree.sh")
        self.cache_paths = []
        for package in ("cslib", "mathlib"):
            source = self.root / ".lake/packages" / package / "Source.lean"
            source.parent.mkdir(parents=True)
            source.write_text("immutable source\n", encoding="utf-8")
            source.with_name("SourceLink.lean").symlink_to("Source.lean")
            self.cache_paths += [pathlib.Path("packages") / package / ".lake" / path
                                 for path in ("build/lib/Lean/Dependency.trace",
                                              "config/lakefile.olean")]
        self.cache_paths += [pathlib.Path("build/lib/Lean/Root.trace"),
                             pathlib.Path("config/lakefile.olean")]
        for path in self.cache_paths:
            cache = self.root / ".lake" / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text(f"root cache {path}\n", encoding="utf-8")
            cache.chmod(0o640)
            os.utime(cache, ns=(1_700_000_000_000_000_000, 1_700_000_000_000_000_000))

    def seed(self, target: pathlib.Path, *flags: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts/worktree.sh"), "seed", str(target), *flags],
            capture_output=True, text=True, check=False, env=GIT_ENV,
        )

    def assert_cache_isolated(self, target: pathlib.Path) -> None:
        for path in self.cache_paths:
            original = self.root / ".lake" / path
            seeded = target / ".lake" / path
            before = original.read_bytes()
            self.assertEqual(seeded.read_bytes(), before)
            self.assertNotEqual(original.stat().st_ino, seeded.stat().st_ino, str(path))
            self.assertEqual(stat.S_IMODE(seeded.stat().st_mode), 0o640)
            self.assertEqual(seeded.stat().st_mtime_ns, original.stat().st_mtime_ns)
            seeded.write_bytes(b"worker updated cache\n")
            self.assertEqual(original.read_bytes(), before, str(path))

    def test_all_copy_modes_isolate_root_and_dependency_caches(self) -> None:
        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / str(flag)
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_cache_isolated(target)
                for package in ("cslib", "mathlib"):
                    source = self.root / ".lake/packages" / package / "Source.lean"
                    seeded = target / ".lake/packages" / package / "Source.lean"
                    shared = flag != "--copy-packages" and not (
                        flag == "--copy-cslib" and package == "cslib")
                    self.assertEqual(source.stat().st_ino == seeded.stat().st_ino, shared)
                    link = seeded.with_name("SourceLink.lean")
                    self.assertTrue(link.is_symlink())
                    self.assertEqual(os.readlink(link), "Source.lean")
                    self.assertEqual(link.read_bytes(), source.read_bytes())

    def test_cache_symlinks_are_copied_without_sharing_their_targets(self) -> None:
        # Cover an internal cache link, the entire cache directory, and a package directory.
        original = self.root / ".lake/build/lib/Lean/Root.trace"
        external = self.tmp / "external.trace"
        original.rename(external)
        original.symlink_to(external)
        package = self.root / ".lake/packages/cslib"
        external_cache = self.tmp / "external-cache"
        (package / ".lake").rename(external_cache)
        (package / ".lake").symlink_to(external_cache, target_is_directory=True)
        package = self.root / ".lake/packages/mathlib"
        external_package = self.tmp / "external-package"
        package.rename(external_package)
        package.symlink_to(external_package, target_is_directory=True)
        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / str(flag)
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assert_cache_isolated(target)
                for path in ("build/lib/Lean/Root.trace", "packages/cslib/.lake",
                             "packages/mathlib"):
                    self.assertFalse((target / ".lake" / path).is_symlink())

    def test_existing_cache_is_preserved_on_repeated_seed(self) -> None:
        target = self.tmp / "worker"
        self.assertEqual(self.seed(target).returncode, 0)
        cache = target / ".lake" / self.cache_paths[0]
        cache.write_text("worker state\n", encoding="utf-8")
        self.assertEqual(self.seed(target, "--copy-packages").returncode, 0)
        self.assertEqual(cache.read_text(), "worker state\n")

    def test_destination_cache_symlinks_are_refused_before_writing(self) -> None:
        for path in (".lake", ".lake/packages", ".lake/build", ".lake/config",
                     ".lake/packages/cslib", ".lake/packages/cslib/.lake",
                     ".lake/packages/cslib/.lake/build", ".lake/packages/cslib/.lake/config"):
            with self.subTest(path=path):
                target = self.tmp / path.replace("/", "-")
                external = self.tmp / (target.name + "-external")
                external.mkdir()
                link = target / path
                link.parent.mkdir(parents=True, exist_ok=True)
                link.symlink_to(external, target_is_directory=True)
                result = self.seed(target)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("symlink", result.stderr)
                self.assertEqual(list(external.iterdir()), [])

    def test_refuses_seeding_primary_checkout_directly_or_via_symlink(self) -> None:
        direct = self.seed(self.root)
        self.assertNotEqual(direct.returncode, 0)
        self.assertIn("primary checkout", direct.stderr)

        link_to_root = self.tmp / "root-link"
        link_to_root.symlink_to(self.root, target_is_directory=True)
        via_link = self.seed(link_to_root)
        self.assertNotEqual(via_link.returncode, 0)
        self.assertIn("primary checkout", via_link.stderr)

        inside_lake = self.seed(self.root / ".lake")
        self.assertNotEqual(inside_lake.returncode, 0)
        self.assertIn("primary checkout", inside_lake.stderr)

    def test_refuses_seeding_primary_subdirectories_or_aliases_unless_registered_worktree(self) -> None:
        tracked = self.root / "tracked-subdir"
        tracked.mkdir()
        (tracked / "File.lean").write_text("tracked\n", encoding="utf-8")
        git(self.root, "add", "tracked-subdir/File.lean")
        git(self.root, "commit", "--quiet", "-m", "tracked subdir")

        direct_subdir = self.seed(tracked)
        self.assertNotEqual(direct_subdir.returncode, 0)
        self.assertIn("primary checkout", direct_subdir.stderr)
        self.assertFalse((tracked / ".lake").exists())

        alias = self.tmp / "subdir-alias"
        alias.symlink_to(tracked, target_is_directory=True)
        via_alias = self.seed(alias)
        self.assertNotEqual(via_alias.returncode, 0)
        self.assertIn("primary checkout", via_alias.stderr)
        self.assertFalse((tracked / ".lake").exists())

        unregistered = self.root / ".worktrees/unregistered"
        unregistered.mkdir(parents=True)
        unreg_res = self.seed(unregistered)
        self.assertNotEqual(unreg_res.returncode, 0)
        self.assertIn("primary checkout", unreg_res.stderr)

        registered = self.root / ".worktrees/registered"
        git(self.root, "worktree", "add", "--quiet", "-b", "nested-wt", str(registered))
        reg_res = self.seed(registered)
        self.assertEqual(reg_res.returncode, 0, reg_res.stderr)
        self.assert_cache_isolated(registered)

    def test_create_refuses_prohibited_targets_before_git_worktree_add(self) -> None:
        shutil.rmtree(self.root / ".lake", ignore_errors=True)
        before_wt_list = git(self.root, "worktree", "list", "--porcelain")

        for idx, bad_dir in enumerate(("..", "../.lake/forbidden", "../forbidden-subdir", ".")):
            with self.subTest(bad_dir=bad_dir):
                branch = f"fixture-invalid-target-{idx}"
                res = subprocess.run(
                    [str(self.root / "scripts/worktree.sh"), "create", branch, bad_dir, "HEAD"],
                    cwd=self.root, text=True, capture_output=True, env=GIT_ENV,
                )
                self.assertNotEqual(res.returncode, 0)
                self.assertIn("primary checkout", res.stderr)
                self.assertFalse((self.root / ".lake").exists())
                self.assertFalse((self.root / "forbidden-subdir").exists())
                self.assertEqual(git(self.root, "worktree", "list", "--porcelain"), before_wt_list)

    def test_source_symlinks_to_primary_checkout_are_dereferenced(self) -> None:
        primary_file = self.root / "PrimarySecret.lean"
        primary_file.write_text("primary content\n", encoding="utf-8")
        primary_dir = self.root / "PrimaryDir"
        primary_dir.mkdir()
        (primary_dir / "Inside.lean").write_text("primary dir content\n", encoding="utf-8")

        cslib = self.root / ".lake/packages/cslib"
        (cslib / "AbsFileLink.lean").symlink_to(primary_file)
        (cslib / "RelEscapeLink.lean").symlink_to("../../../PrimarySecret.lean")
        (cslib / "DirEscapeLink").symlink_to(primary_dir, target_is_directory=True)

        for flag in (None, "--copy-cslib", "--copy-packages"):
            with self.subTest(flag=flag):
                target = self.tmp / f"escape-{flag}"
                result = self.seed(target, *([flag] if flag else []))
                self.assertEqual(result.returncode, 0, result.stderr)
                seeded_cslib = target / ".lake/packages/cslib"
                for name in ("AbsFileLink.lean", "RelEscapeLink.lean", "DirEscapeLink"):
                    seeded_path = seeded_cslib / name
                    self.assertFalse(seeded_path.is_symlink(), name)
                (seeded_cslib / "AbsFileLink.lean").write_text("mutated\n", encoding="utf-8")
                (seeded_cslib / "RelEscapeLink.lean").write_text("mutated\n", encoding="utf-8")
                (seeded_cslib / "DirEscapeLink/Inside.lean").write_text(
                    "mutated dir\n", encoding="utf-8"
                )
                self.assertEqual(
                    primary_file.read_text(encoding="utf-8"), "primary content\n"
                )
                self.assertEqual(
                    (primary_dir / "Inside.lean").read_text(encoding="utf-8"),
                    "primary dir content\n",
                )

    def test_gitfile_dependency_control_metadata_isolated(self) -> None:
        origin = self.tmp / "dep-origin"
        origin.mkdir()
        git(origin, "init", "--quiet", "-b", "main")
        (origin / "Source.lean").write_bytes(b"tracked cslib\n")
        (origin / ".gitignore").write_text(".lake/\n", encoding="utf-8")
        git(origin, "add", "Source.lean", ".gitignore")
        git(origin, "commit", "--quiet", "-m", "dep")
        cslib_rev = git(origin, "rev-parse", "HEAD")

        pkg = self.root / ".lake/packages/cslib"
        shutil.rmtree(pkg)
        git(origin, "worktree", "add", "--quiet", "--detach", str(pkg), cslib_rev)
        (pkg / "SourceLink.lean").symlink_to("Source.lean")
        for path in ("build/lib/Lean/Dependency.trace", "config/lakefile.olean"):
            cache = pkg / ".lake" / path
            cache.parent.mkdir(parents=True, exist_ok=True)
            cache.write_text("root cache\n", encoding="utf-8")
        self.assertTrue((pkg / ".git").is_file())

        primary_gitdir = git(pkg, "rev-parse", "--absolute-git-dir")
        before_index = git(pkg, "ls-files", "-v", "--", "Source.lean")
        before_head = (pathlib.Path(primary_gitdir) / "HEAD").read_text(encoding="utf-8")

        for idx, flags in enumerate(((), ("--copy-cslib",), ("--copy-packages",))):
            with self.subTest(flags=flags):
                wt = self.tmp / f"gitfile-wt-{idx}"
                res = self.seed(wt, *flags)
                self.assertEqual(res.returncode, 0, res.stderr)
                copied = wt / ".lake/packages/cslib"
                self.assertTrue((copied / ".git").is_dir())
                self.assertFalse((copied / ".git").is_symlink())
                self.assertFalse((copied / ".git/objects").is_symlink())
                copy_gitdir = git(copied, "rev-parse", "--absolute-git-dir")
                self.assertNotEqual(primary_gitdir, copy_gitdir)
                subprocess.run(
                    ["git", "-C", str(copied), "update-index", "--assume-unchanged", "Source.lean"],
                    env=GIT_ENV, capture_output=True, text=True, check=False,
                )
                subprocess.run(
                    ["git", "-C", str(copied), "symbolic-ref", "HEAD", "refs/heads/copy-branch"],
                    env=GIT_ENV, capture_output=True, text=True, check=False,
                )
                self.assertEqual(git(pkg, "ls-files", "-v", "--", "Source.lean"), before_index)
                self.assertEqual(
                    (pathlib.Path(primary_gitdir) / "HEAD").read_text(encoding="utf-8"),
                    before_head,
                )

    def test_reftable_dependency_refs_are_copied(self) -> None:
        pkg = self.root / ".lake/packages/cslib"
        shutil.rmtree(pkg)
        pkg.mkdir()
        init = subprocess.run(
            ["git", "-C", str(pkg), "init", "--quiet", "--ref-format=reftable", "-b", "main"],
            env=GIT_ENV, capture_output=True, text=True, check=False,
        )
        if init.returncode != 0:
            self.skipTest("git does not support the reftable ref format")
        (pkg / "Source.lean").write_text("tracked cslib\n", encoding="utf-8")
        git(pkg, "add", "Source.lean")
        git(pkg, "commit", "--quiet", "-m", "dep")
        rev = git(pkg, "rev-parse", "HEAD")
        self.assertTrue((pkg / ".git/reftable").is_dir())
        wt = self.tmp / "reftable-wt"
        res = self.seed(wt)
        self.assertEqual(res.returncode, 0, res.stderr)
        copied = wt / ".lake/packages/cslib"
        self.assertEqual(git(copied, "rev-parse", "HEAD"), rev)
        # updating a ref in the copy leaves the primary package untouched
        git(copied, "update-ref", "refs/heads/copy-branch", rev)
        self.assertNotEqual(
            subprocess.run(
                ["git", "-C", str(pkg), "rev-parse", "--verify", "--quiet", "refs/heads/copy-branch"],
                env=GIT_ENV, capture_output=True, text=True, check=False,
            ).returncode,
            0,
        )

    def test_core_worktree_in_dependency_git_config_is_unset_in_copied_package(self) -> None:
        origin = self.tmp / "dep-origin-worktree"
        origin.mkdir()
        git(origin, "init", "--quiet", "-b", "main")
        (origin / "Source.lean").write_text("committed cslib\n", encoding="utf-8")
        (origin / ".gitignore").write_text(".lake/\n", encoding="utf-8")
        git(origin, "add", "Source.lean", ".gitignore")
        git(origin, "commit", "--quiet", "-m", "dep")
        cslib_rev = git(origin, "rev-parse", "HEAD")

        pkg = self.root / ".lake/packages/cslib"
        for git_kind in ("gitdir", "gitfile", "gitsymlink"):
            shutil.rmtree(pkg, ignore_errors=True)
            if git_kind == "gitdir":
                subprocess.run(
                    ["git", "clone", "--quiet", str(origin), str(pkg)],
                    check=True, env=GIT_ENV,
                )
            elif git_kind == "gitfile":
                wt_parent = self.tmp / f"wt-origin-{git_kind}"
                shutil.copytree(origin, wt_parent)
                git(wt_parent, "worktree", "add", "--quiet", "--detach", str(pkg), cslib_rev)
            else:
                ext_clone = self.tmp / f"ext-clone-{git_kind}"
                subprocess.run(
                    ["git", "clone", "--quiet", str(origin), str(ext_clone)],
                    check=True, env=GIT_ENV,
                )
                ext_git = self.tmp / f"ext-git-{git_kind}"
                shutil.move(str(ext_clone / ".git"), str(ext_git))
                shutil.move(str(ext_clone), str(pkg))
                (pkg / ".git").symlink_to(ext_git, target_is_directory=True)
            git(pkg, "config", "core.worktree", str(pkg.resolve()))
            (pkg / "Source.lean").write_text("primary dirty source\n", encoding="utf-8")
            for path in ("build/lib/Lean/Dependency.trace", "config/lakefile.olean"):
                cache = pkg / ".lake" / path
                cache.parent.mkdir(parents=True, exist_ok=True)
                cache.write_text("root cache\n", encoding="utf-8")

            for idx, flags in enumerate(((), ("--copy-cslib",), ("--copy-packages",))):
                with self.subTest(git_kind=git_kind, flags=flags):
                    wt = self.tmp / f"core-wt-{git_kind}-{idx}"
                    res = self.seed(wt, *flags)
                    self.assertEqual(res.returncode, 0, res.stderr)
                    copied = (wt / ".lake/packages/cslib").resolve()
                    self.assertEqual(
                        pathlib.Path(git(copied, "rev-parse", "--show-toplevel")).resolve(),
                        copied,
                    )
                    self.assertEqual(
                        pathlib.Path(git(copied, "rev-parse", "--absolute-git-dir")).resolve(),
                        (copied / ".git").resolve(),
                    )
                    self.assertEqual(
                        (copied / git(copied, "rev-parse", "--git-common-dir")).resolve(),
                        (copied / ".git").resolve(),
                    )
                    subprocess.run(
                        ["git", "-C", str(copied), "checkout-index", "--all", "--force"],
                        check=True, env=GIT_ENV,
                    )
                    self.assertEqual(
                        (pkg / "Source.lean").read_text(encoding="utf-8"),
                        "primary dirty source\n",
                    )


@unittest.skipUnless(shutil.which("git"), "git is required")
class WorktreePruneTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.tmp = pathlib.Path(tmp.name)
        self.root = self.tmp / "root"
        self.root.mkdir()
        git(self.root, "init", "--quiet", "-b", "main")
        (self.root / "scripts").mkdir()
        shutil.copy(SCRIPT, self.root / "scripts/worktree.sh")
        (self.root / ".gitignore").write_text("/.worktrees/\n/.worktrees-lookalike/\n.lake/\n")
        (self.root / "README").write_text("base\n")
        git(self.root, "add", ".")
        git(self.root, "commit", "--quiet", "-m", "fixture")
        self.branch_count = 0

    def registered(self, path: pathlib.Path) -> pathlib.Path:
        self.branch_count += 1
        git(self.root, "worktree", "add", "--quiet", "-b", f"worker-{self.branch_count}",
            str(path), "main")
        return self.cache(path)

    def cache(self, path: pathlib.Path) -> pathlib.Path:
        cache = path / ".lake/sentinel"
        cache.parent.mkdir(parents=True, exist_ok=True)
        cache.write_bytes(b"keep this cache\n")
        return cache

    def prune(self, *args: str, env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["bash", str(self.root / "scripts/worktree.sh"), "prune-merged", "main", *args],
            cwd=self.root, capture_output=True, text=True, check=False, env=env or GIT_ENV,
        )

    def test_unregistered_directory_retains_its_cache(self) -> None:
        cache = self.cache(self.root / ".worktrees/plain")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")

    def test_locked_worktree_retains_cache_and_does_not_block_other_pruning(self) -> None:
        locked = self.root / ".worktrees/locked"
        cache = self.registered(locked)
        git(self.root, "worktree", "lock", "--reason", "active worker", str(locked))
        removable = self.root / ".worktrees/removable"
        self.registered(removable)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("locked", result.stdout)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertFalse(removable.exists())
        self.assertIn(str(locked.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_merged_worktree_and_nested_git_cache_are_removed(self) -> None:
        for name in ("merged", "merged worker", "merged\nworker"):
            with self.subTest(name=name):
                target = self.root / ".worktrees" / name
                self.registered(target)
                dependency = target / ".lake/packages/demo"
                dependency.mkdir(parents=True)
                git(dependency, "init", "--quiet")
                result = self.prune()
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertFalse(target.exists())
                self.assertNotIn(str(target.resolve()),
                                 git(self.root, "worktree", "list", "--porcelain", "-z"))

    def test_dry_run_preserves_cache_and_registration(self) -> None:
        target = self.root / ".worktrees/merged"
        cache = self.registered(target)
        result = self.prune("--dry-run")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("Would remove", result.stdout)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertIn(str(target.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_git_refusal_after_a_late_edit_preserves_work_and_cache(self) -> None:
        target = self.root / ".worktrees/late-edit"
        cache = self.registered(target)
        wrapper = self.tmp / "bin/git"
        wrapper.parent.mkdir()
        wrapper.write_text('''#!/usr/bin/env bash
if [ "${1:-}" = "worktree" ] && [ "${2:-}" = "remove" ]; then
  printf 'late untracked work\\n' > "$LATE_FILE"
fi
exec "$REAL_GIT" "$@"
''')
        wrapper.chmod(0o755)
        late_file = target / "late-work"
        result = self.prune(env={**GIT_ENV, "REAL_GIT": shutil.which("git"),
                                 "LATE_FILE": str(late_file),
                                 "PATH": str(wrapper.parent) + os.pathsep + os.environ["PATH"]})
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertEqual(late_file.read_bytes(), b"late untracked work\n")
        self.assertIn(str(target.resolve()), git(self.root, "worktree", "list", "--porcelain"))

    def test_dirty_and_unmerged_worktrees_retain_caches(self) -> None:
        dirty = self.root / ".worktrees/dirty"
        dirty_cache = self.registered(dirty)
        (dirty / "README").write_text("uncommitted work\n")
        unmerged = self.root / ".worktrees/unmerged"
        unmerged_cache = self.registered(unmerged)
        (unmerged / "README").write_text("unmerged work\n")
        git(unmerged, "add", "README")
        git(unmerged, "commit", "--quiet", "-m", "worker change")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("dirty working tree", result.stdout)
        self.assertIn("unmerged commits", result.stdout)
        self.assertEqual(dirty_cache.read_bytes(), b"keep this cache\n")
        self.assertEqual(unmerged_cache.read_bytes(), b"keep this cache\n")

    def test_foreign_worktree_retains_cache(self) -> None:
        foreign = self.tmp / "foreign"
        foreign.mkdir()
        git(foreign, "init", "--quiet", "-b", "main")
        (foreign / ".gitignore").write_text(".lake/\n")
        git(foreign, "add", ".")
        git(foreign, "commit", "--quiet", "-m", "foreign fixture")
        target = self.root / ".worktrees/foreign"
        git(foreign, "worktree", "add", "--quiet", "-b", "worker", str(target))
        cache = self.cache(target)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(cache.read_bytes(), b"keep this cache\n")
        self.assertIn(str(target.resolve()), git(foreign, "worktree", "list", "--porcelain"))

    def test_symlinked_worktree_retains_cache(self) -> None:
        target = self.root / ".worktrees/linked"
        self.registered(target)
        moved = self.tmp / "moved-worker"
        target.rename(moved)
        target.symlink_to(moved, target_is_directory=True)
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual((moved / ".lake/sentinel").read_bytes(), b"keep this cache\n")
        self.assertTrue(target.is_symlink())

    def test_prefix_lookalike_and_nested_worktrees_stay_outside_scope(self) -> None:
        nearby = self.root / ".worktrees-lookalike/nearby"
        nearby_cache = self.registered(nearby)
        parent = self.root / ".worktrees/group"
        parent_cache = self.cache(parent)
        nested_cache = self.registered(parent / "nested")
        result = self.prune()
        self.assertEqual(result.returncode, 0, result.stderr)
        for cache in (nearby_cache, parent_cache, nested_cache):
            self.assertEqual(cache.read_bytes(), b"keep this cache\n")


if __name__ == "__main__":
    unittest.main()
