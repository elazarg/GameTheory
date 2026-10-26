#!/bin/bash
# Setup script for a Claude Code cloud environment (claude.ai/code). It runs as
# root on Ubuntu 24.04 after the repository is cloned and before Claude starts.
#
# Installs elan, the toolchain pinned by `lean-toolchain`, and the prebuilt
# Mathlib cache, so a session never compiles Mathlib from source.
#
# The environment needs Custom network access, with the default list included
# plus these hosts:
#   release.lean-lang.org    elan's Lean release index
#   releases.lean-lang.org   Lean toolchain downloads
#   cache.mathlib.org        Mathlib build cache
set -euo pipefail

if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --no-modify-path --default-toolchain none
  # Expose the shims to every shell the session starts, login or not.
  ln -sf "$HOME"/.elan/bin/* /usr/local/bin/
fi

# The clone location is not documented, so look for the root lakefile.
lakefile=$(find "$PWD" /home /root -maxdepth 3 -name lakefile.lean \
  -exec grep -l '^package GameTheory where' {} + 2>/dev/null | head -n 1 || true)
if [ -z "$lakefile" ]; then
  echo "cloud-setup: GameTheory checkout not found; installed elan only." >&2
  exit 0
fi

cd "$(dirname "$lakefile")"
# Installs the pinned toolchain, clones the manifest's dependencies, and
# unpacks Mathlib's prebuilt .olean files.
lake exe cache get
lake env lean --version
