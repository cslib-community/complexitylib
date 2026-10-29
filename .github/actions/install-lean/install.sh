#!/usr/bin/env bash
# Install elan and the toolchain named in `lean-toolchain`, retrying transient download failures
# (#1426). Each step is retried up to LEAN_INSTALL_ATTEMPTS times (default 4), waiting
# LEAN_INSTALL_DELAY seconds (default 15) before the second attempt and three times longer before
# each later one. An attempt that runs longer than LEAN_INSTALL_TIMEOUT seconds (default 180) is
# stopped and counts as a failure: elan can stall indefinitely on a failed TLS connection instead
# of exiting. An existing elan or toolchain is reused without contacting the network.
#
# Usage: install.sh [lean-toolchain path]   (default: ./lean-toolchain)
set -euo pipefail

toolchain_file="${1:-lean-toolchain}"
attempts="${LEAN_INSTALL_ATTEMPTS:-4}"
first_delay="${LEAN_INSTALL_DELAY:-15}"
attempt_timeout="${LEAN_INSTALL_TIMEOUT:-180}"
elan_home="${ELAN_HOME:-$HOME/.elan}"
elan="$elan_home/bin/elan"

retry() {
  local description="$1" attempt=1 delay="$first_delay"
  shift
  until timeout --kill-after=10 "$attempt_timeout" "$@"; do
    if ((attempt >= attempts)); then
      echo "::error::$description failed after $attempt attempts"
      return 1
    fi
    echo "::warning::$description failed (attempt $attempt of $attempts); retrying in ${delay}s"
    sleep "$delay"
    attempt=$((attempt + 1))
    delay=$((delay * 3))
  done
}

# `timeout` runs a command, not a shell function, so the installer runs in its own shell.
install_elan='init="$(mktemp)" &&
  curl --proto =https --tlsv1.2 -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$init" &&
  sh "$init" -y --default-toolchain none --no-modify-path; status=$?; rm -f "$init"; exit "$status"'

if [[ -x "$elan" ]]; then
  echo "Reusing elan at $elan"
else
  retry "elan installation" bash -c "$install_elan"
fi

toolchain="$(tr -d '[:space:]' < "$toolchain_file")"
# `elan toolchain install` fails on an installed toolchain, so check first.
if "$elan" toolchain list | awk '{print $1}' | grep -qxF "$toolchain"; then
  echo "Reusing installed toolchain $toolchain"
else
  retry "installation of $toolchain" "$elan" toolchain install "$toolchain"
fi
"$elan" run "$toolchain" lean --version
