#!/usr/bin/env python3
"""Prepare a private SSH config shared by cache publishing and infrastructure deployment."""

import argparse
import os
from pathlib import Path
import re
import subprocess


def prepare(directory, identity, user, env):
    host = env["CACHE_SERVER_HOST"]
    port = env.get("CACHE_SERVER_SSH_PORT") or "22"
    username = env[user]
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9.-]*", host):
        raise ValueError("CACHE_SERVER_HOST must be a DNS name or IPv4 address")
    if not re.fullmatch(r"[a-z_][a-z0-9_-]*", username):
        raise ValueError("Invalid SSH user")
    if not port.isdecimal() or not 1 <= int(port) <= 65535:
        raise ValueError("Invalid SSH port")
    key, hosts = env[identity], env["CACHE_SERVER_KNOWN_HOSTS"]
    if not key.strip() or not hosts.strip():
        raise ValueError("Both a private identity and independently verified known_hosts are required")
    directory.mkdir(mode=0o700, parents=True, exist_ok=False)
    for name, content in (("identity", key), ("known_hosts", hosts)):
        path = directory / name
        path.write_text(content.rstrip() + "\n")
        path.chmod(0o600)
    subprocess.run(["ssh-keygen", "-y", "-P", "", "-f", str(directory / "identity")],
                   check=True, stdout=subprocess.DEVNULL, stdin=subprocess.DEVNULL, timeout=10)
    def quote(path):
        if any(c in str(path) for c in "\r\n\x00"):
            raise ValueError("Invalid SSH configuration path")
        return '"' + str(path.resolve()).replace('\\', '\\\\').replace('"', '\\"') + '"'
    config = directory / "config"
    config.write_text(f"""Host cache-server
    HostName {host}
    User {username}
    Port {port}
    IdentityFile {quote(directory / 'identity')}
    UserKnownHostsFile {quote(directory / 'known_hosts')}
    GlobalKnownHostsFile {quote(Path(os.devnull))}
    KnownHostsCommand none
    StrictHostKeyChecking yes
    IdentitiesOnly yes
    BatchMode yes
    ConnectTimeout 10
    ServerAliveInterval 15
    ServerAliveCountMax 2
""")
    config.chmod(0o600)
    return config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--identity", required=True, help="Private-key environment variable name")
    parser.add_argument("--user", required=True, help="SSH-user environment variable name")
    args = parser.parse_args()
    try:
        print(prepare(args.directory, args.identity, args.user, os.environ))
    except (KeyError, OSError, ValueError, subprocess.SubprocessError) as error:
        parser.exit(1, f"Cache SSH configuration failed: {error}\n")


if __name__ == "__main__":
    main()
