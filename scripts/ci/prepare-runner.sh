#!/usr/bin/env bash
# Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Christian Reitwiessner
# Reclaim unused SDK space before restoring Lean caches on ephemeral hosted runners.
set -euo pipefail

if [[ "${GITHUB_ACTIONS:-}" != true || "${RUNNER_ENVIRONMENT:-}" != github-hosted ||
      "${RUNNER_OS:-}" != Linux ]]; then
  echo "Skipping SDK cleanup outside GitHub-hosted Linux runners."
  exit 0
fi

df -h /
# These preinstalled SDKs are not used by Lean, Python or the workflow's Node actions.
# Keep the tool cache, compiler, repository, Lean toolchain and build caches intact.
sudo rm -rf -- /usr/local/lib/android /usr/share/dotnet
df -h /
