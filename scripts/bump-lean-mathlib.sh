#!/usr/bin/env bash
# Bump the Lean toolchain + pinned Mathlib rev, in lockstep, across the main
# repo and the fixed-point-theorems-lean4 submodule.
#
# Usage: scripts/bump-lean-mathlib.sh v4.32.0
#
# This only does the mechanical text substitution. After running it you
# still need to `lake build` and fix any resulting breakage.
set -euo pipefail

if [ $# -ne 1 ]; then
  echo "Usage: $0 <version>  (e.g. v4.32.0)" >&2
  exit 1
fi

version="$1"
case "$version" in
  v*) ;;
  *) echo "Version must look like 'v4.32.0' (leading 'v')" >&2; exit 1 ;;
esac

root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
submodule="$root/fixed-point-theorems-lean4"

update_toolchain() {
  local file="$1"
  printf 'leanprover/lean4:%s\n' "$version" > "$file"
  echo "updated $file"
}

update_mathlib_rev() {
  local file="$1"
  sed -i -E "s/(mathlib.*@ git \")v[0-9]+\.[0-9]+\.[0-9]+(\")/\1${version}\2/" "$file"
  echo "updated $file"
}

update_mathlib_rev_toml() {
  local file="$1"
  sed -i -E "0,/^rev = \"v[0-9]+\.[0-9]+\.[0-9]+\"\$/s//rev = \"${version}\"/" "$file"
  echo "updated $file"
}

# `lake update` shells out to git over HTTPS for every dependency and
# regularly hits transient "Failed to connect to github.com port 443"
# errors. Retry a bunch of times before giving up for good.
retry_lake_update() {
  local dir="$1"
  local max_attempts=10
  local attempt=1
  while [ "$attempt" -le "$max_attempts" ]; do
    echo "[$dir] lake update mathlib (attempt $attempt/$max_attempts)..."
    if (cd "$dir" && lake update mathlib); then
      echo "[$dir] lake update mathlib succeeded on attempt $attempt"
      return 0
    fi
    echo "[$dir] lake update mathlib failed on attempt $attempt"
    attempt=$((attempt + 1))
    sleep 5
  done
  echo "[$dir] lake update mathlib failed after $max_attempts attempts" >&2
  return 1
}

update_toolchain "$root/lean-toolchain"
update_mathlib_rev "$root/lakefile.lean"

if [ -f "$submodule/lean-toolchain" ]; then
  update_toolchain "$submodule/lean-toolchain"
fi
if [ -f "$submodule/lakefile.toml" ]; then
  update_mathlib_rev_toml "$submodule/lakefile.toml"
fi

echo
echo "Updating submodule manifest + cache..."
retry_lake_update "$submodule"
(cd "$submodule" && lake exe cache get)

echo
echo "Updating root manifest + cache..."
retry_lake_update "$root"
(cd "$root" && lake exe cache get)

echo
echo "Done."
