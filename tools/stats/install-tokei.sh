#!/usr/bin/env bash
# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
# Pinned Linux x86-64 musl binary, used by the ubuntu-latest Pages job.
set -euo pipefail
if [[ $(uname -s)-$(uname -m) != Linux-x86_64 ]]; then
  echo 'This installer requires Linux x86-64; otherwise install tokei 12.1.2 manually.' >&2
  exit 1
fi
destination=${1:?Usage: install-tokei.sh DESTINATION_DIRECTORY}
mkdir -p "$destination"
destination=$(cd "$destination" && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
curl --fail --location --retry 3 --output "$scratch/tokei.tar.gz" \
  https://github.com/XAMPPRocky/tokei/releases/download/v12.1.2/tokei-x86_64-unknown-linux-musl.tar.gz
(cd "$scratch" && echo '331e77046935d655dce8d97ebb943fcc7e9684586dadf3d197f3df5e760cd31b  tokei.tar.gz' | sha256sum --check)
tar -xzf "$scratch/tokei.tar.gz" -C "$scratch" tokei
install -m 755 "$scratch/tokei" "$destination/tokei"
"$destination/tokei" --version
