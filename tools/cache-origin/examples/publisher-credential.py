#!/usr/bin/env python3
"""Generate/install or rotate one publisher token, without printing its value.

Run as root after creating a private handoff directory. The handoff file must be
new, including during rotation. Only its bcrypt hash is installed in nginx's
password file. Revoke by replacing that file with an empty root-owned 0640 file.
"""

import argparse
import base64
import grp
import os
from pathlib import Path
import re
import secrets
import stat
import subprocess
import tempfile


def sync_directory(directory):
    descriptor = os.open(directory, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def atomic_hash(path, data, gid):
    descriptor, temporary = tempfile.mkstemp(prefix=".cache-publisher-", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as target:
            os.fchmod(target.fileno(), 0o640)
            os.fchown(target.fileno(), 0, gid)
            target.write(data)
            target.flush()
            os.fsync(target.fileno())
        os.replace(temporary, path)
        sync_directory(path.parent)
    finally:
        if os.path.lexists(temporary):
            os.unlink(temporary)


def install(args):
    if os.geteuid() != 0:
        raise ValueError("Run as root to install the protected nginx hash file")
    if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", args.user):
        raise ValueError("Invalid publisher account name")
    gid = grp.getgrnam(args.group).gr_gid
    for directory, private in ((args.handoff.parent, True), (args.password_file.parent, False)):
        info = directory.lstat()
        forbidden = 0o077 if private else 0o022
        if not stat.S_ISDIR(info.st_mode) or info.st_uid != 0 or info.st_mode & forbidden:
            raise ValueError("Directories must be root-owned, not symlinks, and appropriately private")
    if os.path.lexists(args.handoff):
        raise ValueError("Choose a new handoff filename; existing credentials are never overwritten")
    if os.path.lexists(args.password_file):
        info = args.password_file.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_uid != 0 or info.st_mode & 0o022:
            raise ValueError("Existing password file is unsafe")
        if info.st_size and not args.rotate:
            raise ValueError("An account is installed; explicit --rotate is required")
    password = base64.urlsafe_b64encode(secrets.token_bytes(32)).decode().rstrip("=")
    result = subprocess.run(["htpasswd", "-niBC", "12", args.user],
                            input=(password + "\n").encode(), capture_output=True, check=True)
    # htpasswd -n emits an additional blank line on some Apache versions.
    record = result.stdout.rstrip(b"\n") + b"\n"
    if not re.fullmatch(re.escape(args.user).encode() + rb":\$2[aby]\$12\$[./A-Za-z0-9]{53}\n", record):
        raise ValueError("htpasswd did not produce the required bcrypt cost-12 record")
    # Write/fsync the private handoff before switching the active password. A
    # failed installation leaves recoverable handoff material, never a lost key.
    descriptor = os.open(args.handoff, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(descriptor, "w") as target:
        target.write("CACHE_SERVER_URL=https://complexitycache.csail.mit.edu\n")
        target.write("CACHE_SERVER_USER=" + args.user + "\n")
        target.write("CACHE_SERVER_PASSWORD=" + password + "\n")
        target.write("\nSet these in the protected cache-server-publish GitHub Environment.\n")
        target.write("Keep repository CACHE_SERVER_PUBLISH_ENABLED=false until approved activation.\n")
        target.flush()
        os.fsync(target.fileno())
    sync_directory(args.handoff.parent)
    atomic_hash(args.password_file, record, gid)
    print("Installed bcrypt cost-12 publisher hash; private handoff: " + str(args.handoff))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--handoff", required=True, type=Path)
    parser.add_argument("--password-file", type=Path, default=Path("/etc/nginx/cache-publish.htpasswd"))
    parser.add_argument("--group", default="cache-origin-proxy")
    parser.add_argument("--user", default="cache-publisher")
    parser.add_argument("--rotate", action="store_true")
    args = parser.parse_args()
    try:
        install(args)
    except (OSError, KeyError, ValueError, subprocess.CalledProcessError):
        # Never stringify subprocess input or hash output in errors.
        parser.exit(1, "Credential installation failed; inspect private paths, permissions and htpasswd availability\n")


if __name__ == "__main__":
    main()
