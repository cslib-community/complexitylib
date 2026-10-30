#!/usr/bin/env bash
# Manage isolated git worktrees under .worktrees/, optionally seeding .lake caches.
#
# Usage:
#   scripts/worktree.sh create <branch> [dir_name] [base_ref]
#                              [--copy-cslib | --copy-packages | --source-only] [--force-reset]
#   scripts/worktree.sh seed <worktree_path> [--copy-cslib | --copy-packages]
#   scripts/worktree.sh list
#   scripts/worktree.sh prune-merged [base_ref] [--dry-run]
#
# Branch selection for `create`:
#   * an existing local branch is checked out as is (`--force-reset` resets it to base_ref);
#   * a branch that exists only on `origin` (the usual takeover case) is created locally tracking
#     `origin/<branch>`, after fetching it; passing base_ref for such a branch is refused, because
#     it would silently discard the pushed work (`--force-reset` overrides the refusal; without a
#     base_ref, `--force-reset` still tracks `origin/<branch>` rather than discarding it). If the
#     fetch fails (offline, or the branch was deleted on origin), the local `origin/<branch>` ref,
#     possibly stale, is used when present;
#   * otherwise a new branch is created from base_ref (default `origin/main`) without upstream
#     tracking, so a plain `git push` cannot target the base branch.
#
# Cache seeding note:
#   Package sources are hard-linked (`cp -al`) by default. Root build/config caches and every
#   package's `.lake` cache are copied with independent inodes, preserving modes and mtimes.
#   Cache symlinks and any package symlinks whose targets are absolute or escape the package
#   directory are dereferenced so their targets are copied too; internal relative source symlinks
#   are preserved. Dependency `.git` directories and `gitdir:` pointer files are isolated so Git
#   operations inside a worktree cannot modify the primary checkout's `HEAD` or `index`.
#   `create` and `seed` also run `scripts/cache/ensure.sh` (`scripts/cache/get.sh`) in the
#   worktree unless `COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP=1` is set.
#   Do not edit shared package sources. `--copy-cslib` also copies cslib's sources
#   (for upstream edits or a pin bump); `--copy-packages` copies every package's sources.
#   `create --source-only` skips all initial .lake copies, including package sources and Git
#   controls; Lake materializes dependencies normally and may reuse its immutable artifact cache.
#   It still checks isolation and bootstraps, unless bootstrap is explicitly disabled as above.
#   It cannot be combined with either --copy-* flag.
#   Seeding refuses the primary checkout and skips existing destination caches.
#
# Pruning considers registered worktrees directly under `.worktrees/`, retaining locked,
# symlinked, dirty and unmerged worktrees. Git removes eligible worktrees and their caches.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
GIT_COMMON_DIR="$(git -C "$SCRIPT_DIR" rev-parse --path-format=absolute --git-common-dir)"
ROOT="$(cd "$GIT_COMMON_DIR/.." && pwd)"
cd "$ROOT"

resolve_path() {
  python3 - "$1" <<'PY'
import os, sys
print(os.path.realpath(sys.argv[1]))
PY
}

# isolate_git_dir <source_git> <dest_git>: materialize an independent .git directory so Git
# commands or control-file writes in the seeded package never mutate the primary checkout's
# HEAD, index, config, or refs (including when source_git is a `gitdir:` pointer file).
isolate_git_dir() {
  local source_git="$1" dest_git="$2"
  python3 - "$source_git" "$dest_git" <<'PY'
import os, pathlib, shutil, subprocess, sys

src = pathlib.Path(sys.argv[1])
dst = pathlib.Path(sys.argv[2])

if src.is_file() or (src.is_symlink() and src.resolve().is_file()):
    raw = src.read_text(encoding="utf-8").strip()
    if not raw.startswith("gitdir:"):
        raise SystemExit(f"Unsupported .git file format: {src}")
    gitdir_str = raw.split(":", 1)[1].strip()
    gitdir = (src.parent / gitdir_str).resolve()
else:
    gitdir = src.resolve()

commondir = gitdir
commondir_file = gitdir / "commondir"
if commondir_file.is_file():
    rel_common = commondir_file.read_text(encoding="utf-8").strip()
    commondir = (gitdir / rel_common).resolve()

if dst.exists() or dst.is_symlink():
    if dst.is_symlink() or dst.is_file():
        dst.unlink()
    else:
        shutil.rmtree(dst)
dst.mkdir(parents=True, exist_ok=True)

head_src = gitdir / "HEAD"
if head_src.is_file():
    shutil.copy2(head_src, dst / "HEAD")
else:
    (dst / "HEAD").write_text("ref: refs/heads/main\n", encoding="utf-8")

for name in ("config", "packed-refs", "shallow", "index"):
    cand = gitdir / name if (gitdir / name).is_file() else commondir / name
    if cand.is_file():
        shutil.copy2(cand, dst / name)

if (dst / "config").is_file():
    subprocess.run(
        ["git", "config", "--file", str(dst / "config"), "--unset-all", "core.worktree"],
        check=False,
    )
    subprocess.run(
        ["git", "config", "--file", str(dst / "config"), "core.bare", "false"],
        check=False,
    )

for dirname in ("refs", "info"):
    cand = gitdir / dirname if (gitdir / dirname).is_dir() else commondir / dirname
    if cand.is_dir():
        shutil.copytree(cand, dst / dirname, symlinks=False, dirs_exist_ok=True)
    else:
        (dst / dirname).mkdir(parents=True, exist_ok=True)

# A repository using the reftable ref format (`extensions.refstorage = reftable`) keeps HEAD and
# its refs in `reftable/`; without it the copy has no resolvable HEAD.
reftable_src = gitdir / "reftable" if (gitdir / "reftable").is_dir() else commondir / "reftable"
if reftable_src.is_dir():
    shutil.copytree(reftable_src, dst / "reftable", symlinks=False, dirs_exist_ok=True)

def link_or_copy(s: str, d: str) -> None:
    try:
        os.link(s, d)
    except OSError:
        shutil.copy2(s, d)

objects_src = commondir / "objects"
if objects_src.is_dir():
    shutil.copytree(
        objects_src, dst / "objects", copy_function=link_or_copy, symlinks=False, dirs_exist_ok=True
    )
else:
    (dst / "objects").mkdir(parents=True, exist_ok=True)

pkg_root = dst.parent.resolve()
dst_real = dst.resolve()
top = pathlib.Path(
    subprocess.check_output(
        ["git", "-C", str(pkg_root), "rev-parse", "--show-toplevel"], text=True
    ).strip()
).resolve()
abs_gitdir = pathlib.Path(
    subprocess.check_output(
        ["git", "-C", str(pkg_root), "rev-parse", "--absolute-git-dir"], text=True
    ).strip()
).resolve()
common_gitdir = pathlib.Path(
    subprocess.check_output(
        ["git", "-C", str(pkg_root), "rev-parse", "--path-format=absolute", "--git-common-dir"],
        text=True,
    ).strip()
).resolve()
if top != pkg_root or abs_gitdir != dst_real or common_gitdir != dst_real:
    raise SystemExit(
        f"Isolated git directory validation failed for {pkg_root}: "
        f"toplevel={top}, gitdir={abs_gitdir}, commondir={common_gitdir}"
    )
PY
}

# dereference_escaping_symlinks <source_pkg_dir> <dest_pkg_dir>: replace any symlink in
# dest_pkg_dir (outside .lake and .git) whose target is absolute or resolves outside
# source_pkg_dir with an independent copy of its target.
dereference_escaping_symlinks() {
  local source="$1" destination="$2"
  python3 - "$source" "$destination" <<'PY'
import os, pathlib, shutil, sys

src_root = pathlib.Path(os.path.realpath(sys.argv[1]))
dst_root = pathlib.Path(sys.argv[2])

def is_within(child: pathlib.Path, parent: pathlib.Path) -> bool:
    try:
        child.relative_to(parent)
        return True
    except ValueError:
        return False

def walk_dir(rel: pathlib.Path) -> None:
    cur_dst = dst_root / rel
    if not cur_dst.is_dir() or cur_dst.is_symlink():
        return
    for entry in list(cur_dst.iterdir()):
        if rel == pathlib.Path(".") and entry.name in (".lake", ".git"):
            continue
        entry_rel = rel / entry.name
        src_entry = src_root / entry_rel
        if entry.is_symlink():
            link_target = os.readlink(entry)
            resolved = pathlib.Path(os.path.realpath(src_entry))
            if os.path.isabs(link_target) or not is_within(resolved, src_root):
                entry.unlink()
                if resolved.is_dir():
                    shutil.copytree(resolved, entry, symlinks=False)
                elif resolved.exists():
                    shutil.copy2(resolved, entry, follow_symlinks=True)
            continue
        if entry.is_dir():
            walk_dir(entry_rel)

walk_dir(pathlib.Path("."))
PY
}

# seed_package <source> <destination> <copy_sources>. Copy caches without first hard-linking them.
seed_package() (
  local source="$1" destination="$2" copy_sources="$3" entry base
  mkdir -p "$destination"
  shopt -s dotglob nullglob
  for entry in "$source"/*; do
    base="$(basename "$entry")"
    if [ "$base" = ".lake" ]; then
      cp -aL "$entry" "$destination/.lake"
    elif [ "$base" = ".git" ]; then
      isolate_git_dir "$entry" "$destination/.git"
    elif [ "$copy_sources" = "true" ]; then
      cp -a "$entry" "$destination/"
    else
      cp -al "$entry" "$destination/"
    fi
  done
  dereference_escaping_symlinks "$source" "$destination"
)

bootstrap_worktree_cache() {
  local wt_path="$1"
  local wt_real
  wt_real="$(resolve_path "$wt_path")"
  if [ "${COMPLEXITYLIB_WORKTREE_SKIP_CACHE_BOOTSTRAP:-0}" = "1" ]; then
    return 0
  fi
  if [ -x "$wt_path/scripts/cache/ensure.sh" ]; then
    (cd "$wt_path" && COMPLEXITYLIB_CACHE_CHECKOUT="$wt_real" ./scripts/cache/ensure.sh) || true
  elif [ -x "$ROOT/scripts/cache/ensure.sh" ]; then
    (cd "$wt_path" && COMPLEXITYLIB_CACHE_CHECKOUT="$wt_real" "$ROOT/scripts/cache/ensure.sh" --checkout "$wt_real") || true
  fi
}

# refuse_primary_or_symlink_target <wt_path> [prospective|seed]
refuse_primary_or_symlink_target() {
  local wt_path="$1"
  local mode="${2:-seed}"
  local root_real wt_real
  root_real="$(resolve_path "$ROOT")"
  wt_real="$(resolve_path "$wt_path")"
  if [ "$wt_real" = "$root_real" ]; then
    echo "Refusing to seed primary checkout: $wt_path" >&2
    return 1
  fi
  case "$wt_real" in
    "$root_real/.lake"|"$root_real/.lake/"*)
      echo "Refusing to seed inside primary checkout .lake: $wt_path" >&2
      return 1
      ;;
    "$root_real/.git"|"$root_real/.git/"*)
      echo "Refusing to seed inside primary checkout .git: $wt_path" >&2
      return 1
      ;;
    "$root_real"/*)
      local wt_top=""
      if [ -d "$wt_real" ] && [ -e "$wt_real/.git" ]; then
        wt_top="$(git -C "$wt_real" rev-parse --show-toplevel 2>/dev/null || true)"
        if [ -n "$wt_top" ]; then
          wt_top="$(resolve_path "$wt_top")"
        fi
      fi
      if [ "$wt_top" != "$wt_real" ]; then
        if [ "$mode" = "prospective" ]; then
          case "$wt_real" in
            "$root_real/.worktrees/"*)
              ;;
            *)
              echo "Refusing to seed inside primary checkout subdirectory: $wt_path" >&2
              return 1
              ;;
          esac
        else
          echo "Refusing to seed inside primary checkout subdirectory: $wt_path" >&2
          return 1
        fi
      fi
      ;;
  esac
  local path
  for path in "$wt_path/.lake" "$wt_path/.lake/packages" \
      "$wt_path/.lake/build" "$wt_path/.lake/config"; do
    if [ -L "$path" ]; then
      echo "Refusing to seed through destination cache symlink: $path" >&2
      return 1
    fi
    if [ -e "$path" ]; then
      local path_real
      path_real="$(resolve_path "$path")"
      case "$path_real" in
        "$root_real"|"$root_real/.lake"|"$root_real/.lake/"*)
          echo "Refusing to seed destination path resolving into primary checkout: $path" >&2
          return 1
          ;;
      esac
    fi
  done
  # Check nested cache links without traversing package source or Git-control trees. Checking
  # only build/config themselves misses links such as .lake/build/lib/lean before bootstrap.
  python3 - "$wt_path/.lake" <<'PY'
import os, pathlib, sys

def refuse_link(path: pathlib.Path, kind: str = "cache") -> None:
    if path.is_symlink():
        raise SystemExit(f"Refusing to seed through destination {kind} symlink: {path}")

def fail_walk(error: OSError) -> None:
    raise error

def check_cache(root: pathlib.Path, skip_packages: bool = False) -> None:
    refuse_link(root)
    for directory, dirs, files in os.walk(root, followlinks=False, onerror=fail_walk):
        for name in dirs + files:
            refuse_link(pathlib.Path(directory) / name)
        if skip_packages and pathlib.Path(directory) == root:
            dirs[:] = [name for name in dirs if name != "packages"]

cache = pathlib.Path(sys.argv[1])
if cache.exists():
    check_cache(cache, skip_packages=True)
    packages = cache / "packages"
    if packages.is_dir():
        for package in packages.iterdir():
            refuse_link(package, "package")
            if (package / ".lake").exists() or (package / ".lake").is_symlink():
                check_cache(package / ".lake")
PY
}

# prepare_lake <worktree_path> <copy_mode> [source_only], where copy_mode is `none`, `cslib` or `all`.
prepare_lake() {
  local wt_path="$1"
  local copy_mode="${2:-none}"
  local source_only="${3:-false}"
  refuse_primary_or_symlink_target "$wt_path" "seed"
  if [ "$source_only" = "true" ]; then
    bootstrap_worktree_cache "$wt_path"
    return 0
  fi
  if [ ! -d "$ROOT/.lake" ]; then
    echo "No root .lake directory found at $ROOT/.lake; skipping cache seed."
    bootstrap_worktree_cache "$wt_path"
    return 0
  fi
  mkdir -p "$wt_path/.lake"
  if [ -d "$ROOT/.lake/packages" ] && [ ! -d "$wt_path/.lake/packages" ]; then
    mkdir -p "$wt_path/.lake/packages"
    local pkg name copy_sources
    for pkg in "$ROOT"/.lake/packages/*; do
      [ -d "$pkg" ] || continue
      name="$(basename "$pkg")"
      copy_sources="false"
      if [ "$copy_mode" = "all" ] || { [ "$copy_mode" = "cslib" ] && [ "$name" = "cslib" ]; }; then
        copy_sources="true"
      fi
      seed_package "$pkg" "$wt_path/.lake/packages/$name" "$copy_sources"
    done
  fi
  if [ -d "$ROOT/.lake/config" ] && [ ! -d "$wt_path/.lake/config" ]; then
    cp -aL "$ROOT/.lake/config" "$wt_path/.lake/config"
  fi
  if [ -d "$ROOT/.lake/build" ] && [ ! -d "$wt_path/.lake/build" ]; then
    cp -aL "$ROOT/.lake/build" "$wt_path/.lake/build"
  fi
  bootstrap_worktree_cache "$wt_path"
}

# copy_mode_flag <current_mode> <arg>: print the new copy mode, or fail on conflicting flags.
copy_mode_flag() {
  local current="$1" requested
  case "$2" in
    --copy-cslib) requested="cslib" ;;
    --copy-packages) requested="all" ;;
  esac
  if [ "$current" != "none" ] && [ "$current" != "$requested" ]; then
    echo "--copy-cslib and --copy-packages are mutually exclusive." >&2
    return 1
  fi
  echo "$requested"
}

cmd="${1:-list}"
shift || true

case "$cmd" in
  create)
    branch="${1:?Usage: scripts/worktree.sh create <branch> [dir_name] [base_ref] [--copy-cslib | --copy-packages | --source-only] [--force-reset]}"
    shift
    dir_name=""
    base_ref=""
    copy_mode="none"
    source_only="false"
    force_reset="false"
    for arg in "$@"; do
      if [ "$arg" = "--copy-cslib" ] || [ "$arg" = "--copy-packages" ]; then
        copy_mode="$(copy_mode_flag "$copy_mode" "$arg")"
      elif [ "$arg" = "--source-only" ]; then
        source_only="true"
      elif [ "$arg" = "--force-reset" ]; then
        force_reset="true"
      elif [ -z "$dir_name" ]; then
        dir_name="$arg"
      elif [ -z "$base_ref" ]; then
        base_ref="$arg"
      else
        echo "Unexpected argument: $arg" >&2
        exit 1
      fi
    done
    if [ "$source_only" = "true" ] && [ "$copy_mode" != "none" ]; then
      echo "--source-only cannot be combined with --copy-cslib or --copy-packages." >&2
      exit 1
    fi
    if [ -z "$dir_name" ]; then
      dir_name="${branch//\//-}"
    fi
    wt_path="$ROOT/.worktrees/$dir_name"
    refuse_primary_or_symlink_target "$wt_path" "prospective"
    if git show-ref --verify --quiet "refs/heads/$branch"; then
      if [ "$force_reset" = "true" ]; then
        effective_base="${base_ref:-origin/main}"
        git worktree add -B "$branch" "$wt_path" "$effective_base"
        prepare_lake "$wt_path" "$copy_mode" "$source_only"
        echo "Ready: $wt_path (branch $branch reset to $effective_base)"
      else
        if [ -n "$base_ref" ]; then
          echo "Branch '$branch' already exists locally; refusing to reset it to '$base_ref' without --force-reset." >&2
          exit 1
        fi
        git worktree add "$wt_path" "$branch"
        prepare_lake "$wt_path" "$copy_mode" "$source_only"
        echo "Ready: $wt_path (existing branch $branch)"
      fi
    else
      # Refresh origin/<branch> so a branch pushed by another worker is not mistaken for a new one.
      # A failed fetch (offline, or no such remote branch) falls back to the local remote refs.
      git fetch --quiet origin "+refs/heads/$branch:refs/remotes/origin/$branch" 2>/dev/null || true
      if git show-ref --verify --quiet "refs/remotes/origin/$branch"; then
        if [ -n "$base_ref" ] && [ "$force_reset" != "true" ]; then
          echo "Branch '$branch' exists on origin; refusing to create it from '$base_ref' (that would discard the pushed work)." >&2
          echo "hint: omit base_ref to track origin/$branch, or pass --force-reset to start '$branch' from '$base_ref' anyway." >&2
          exit 1
        fi
        if [ -n "$base_ref" ]; then
          git worktree add --no-track -b "$branch" "$wt_path" "$base_ref"
          prepare_lake "$wt_path" "$copy_mode" "$source_only"
          echo "Ready: $wt_path (new branch $branch from $base_ref; origin/$branch ignored by --force-reset)"
        else
          git worktree add --track -b "$branch" "$wt_path" "origin/$branch"
          prepare_lake "$wt_path" "$copy_mode" "$source_only"
          echo "Ready: $wt_path (branch $branch tracking origin/$branch)"
        fi
      else
        effective_base="${base_ref:-origin/main}"
        git worktree add --no-track -b "$branch" "$wt_path" "$effective_base"
        prepare_lake "$wt_path" "$copy_mode" "$source_only"
        echo "Ready: $wt_path (new branch $branch from $effective_base)"
      fi
    fi
    ;;
  seed)
    wt_path="${1:?Usage: scripts/worktree.sh seed <worktree_path> [--copy-cslib | --copy-packages]}"
    shift
    copy_mode="none"
    for arg in "$@"; do
      if [ "$arg" = "--copy-cslib" ] || [ "$arg" = "--copy-packages" ]; then
        copy_mode="$(copy_mode_flag "$copy_mode" "$arg")"
      else
        echo "Unexpected argument: $arg" >&2
        exit 1
      fi
    done
    prepare_lake "$wt_path" "$copy_mode"
    echo "Seeded .lake cache in $wt_path"
    ;;
  list)
    git worktree list
    ;;
  prune-merged)
    base_ref="origin/main"
    dry_run="false"
    for arg in "$@"; do
      if [ "$arg" = "--dry-run" ]; then
        dry_run="true"
      else
        base_ref="$arg"
      fi
    done
    if [ ! -d "$ROOT/.worktrees" ]; then
      exit 0
    fi
    wt=""
    locked="false"
    # NUL-delimited inventory keeps spaces/newlines in paths and excludes foreign directories.
    git worktree list --porcelain -z | while IFS= read -r -d '' record; do
      case "$record" in
        "worktree "*)
          wt="${record#worktree }"
          locked="false"
          continue
          ;;
        locked|locked\ *) locked="true"; continue ;;
        "") ;;
        *) continue ;;
      esac
      case "$wt" in
        "$ROOT/.worktrees/"*) ;;
        *) continue ;;
      esac
      # Match the former direct-child scope, excluding nested paths and prefix lookalikes.
      case "${wt#"$ROOT/.worktrees/"}" in
        ""|*/*) continue ;;
      esac
      if [ "$locked" = "true" ] || [ -L "$wt" ]; then
        echo "Keeping $wt (locked or symlinked worktree)"
        continue
      fi
      [ -d "$wt" ] || continue
      if [ -n "$(git -C "$wt" status --porcelain)" ]; then
        echo "Keeping $wt (dirty working tree)"
        continue
      fi
      unmerged="$(git -C "$wt" log --oneline "$base_ref..HEAD")"
      if [ -n "$unmerged" ]; then
        echo "Keeping $wt (has unmerged commits)"
        continue
      fi
      if [ "$dry_run" = "true" ]; then
        echo "Would remove merged worktree $wt"
      else
        echo "Removing merged worktree $wt"
        # Git checks registration, locks and cleanliness again before deleting anything.
        git worktree remove "$wt"
      fi
    done
    ;;
  *)
    echo "Unknown command: $cmd" >&2
    exit 1
    ;;
esac
