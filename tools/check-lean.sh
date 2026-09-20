#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
#
# Type-check every module in the Lean 4 port.
#
#   sh tools/check-lean.sh          find or install Lean, then check all
#   sh tools/check-lean.sh --check  report toolchain state, never download
#
# Environment overrides:
#   LEAN_VERSION  optional assertion; must match lean-toolchain
#   LEAN_BIN      use this Lean executable when set
#   LEAN_PREFIX   default $HOME/.local/opt (must be outside this directory)
#   LEAN_CACHE    default $HOME/.cache/lean
#   LEAN_SHA256   selected platform archive digest; empty disables the check
set -eu

LEAN_PREFIX="${LEAN_PREFIX:-$HOME/.local/opt}"
LEAN_CACHE="${LEAN_CACHE:-$HOME/.cache/lean}"

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/.." && pwd)
pinned_version=$(sed -n 's/.*:v//p' "$repo_root/lean-toolchain")
if [ "$pinned_version" != "4.32.0" ]; then
  echo "error: update check-lean.sh archive digests for lean-toolchain $pinned_version" >&2
  exit 1
fi
LEAN_VERSION="${LEAN_VERSION:-$pinned_version}"
if [ "$LEAN_VERSION" != "$pinned_version" ]; then
  echo "error: LEAN_VERSION $LEAN_VERSION does not match lean-toolchain $pinned_version" >&2
  exit 1
fi

system=$(uname -s)
machine=$(uname -m)
case "$system:$machine" in
  Linux:x86_64|Linux:amd64)
    platform="linux"
    tar_sha256="fca846f3588724a38ad19ee40292c67cb7438d7555903372e3308eef795ba516"
    zip_sha256="5320dc308f108775904d865b05df386e6bc7dee254e030a90177e8fcc36f0fbe"
    ;;
  Linux:aarch64|Linux:arm64)
    platform="linux_aarch64"
    tar_sha256="e5eb67e5f30c14d57e70bf7ca2ad880b09a52d75da1cf5e2deabb2418a84c8d1"
    zip_sha256="efc019f0403c77300497ea33415e18e46deac4c7c4f6423934e518fa60ee6fba"
    ;;
  Darwin:x86_64|Darwin:amd64)
    platform="darwin"
    tar_sha256="9b489c91ee107c5b76bb80c725731f4d370d85094c53bb45615517fb19a73a6a"
    zip_sha256="f6af4fcf34c2966032065f109557e7363e3bd84fed84a77137752a345a3b7da0"
    ;;
  Darwin:arm64|Darwin:aarch64)
    platform="darwin_aarch64"
    tar_sha256="4faa4757f7ca5e7d9588a9de779550fa58bdf01498edb966f15029e2ea117e4e"
    zip_sha256="ffd3410d554dcb2d83dd92f0b7b92a79a6d462d11765b2db4f291cdd66f90942"
    ;;
  *)
    echo "error: no pinned Lean archive for $system/$machine" >&2
    exit 1
    ;;
esac
download_home="$LEAN_PREFIX/lean-${LEAN_VERSION}-${platform}"

case "$LEAN_PREFIX" in
  "$repo_root"|"$repo_root"/*)
    echo "error: LEAN_PREFIX must lie outside the project directory ($repo_root)" >&2
    exit 2 ;;
esac

version_matches() {
  "$1" --version 2>/dev/null | grep -F "version $LEAN_VERSION" >/dev/null
}

lean_bin=""
if [ -n "${LEAN_BIN:-}" ]; then
  if [ ! -x "$LEAN_BIN" ]; then
    echo "error: LEAN_BIN is not executable: $LEAN_BIN" >&2
    exit 1
  fi
  if ! version_matches "$LEAN_BIN"; then
    echo "error: LEAN_BIN is not Lean $LEAN_VERSION: $LEAN_BIN" >&2
    exit 1
  fi
  lean_bin="$LEAN_BIN"
elif command -v lean >/dev/null 2>&1 && version_matches "$(command -v lean)"; then
  lean_bin=$(command -v lean)
elif [ -x "$download_home/bin/lean" ] && version_matches "$download_home/bin/lean"; then
  lean_bin="$download_home/bin/lean"
fi

if [ "${1:-}" = "--check" ]; then
  if [ -n "$lean_bin" ]; then
    "$lean_bin" --version
    echo "lean: ready at $lean_bin"
    exit 0
  fi
  echo "lean $LEAN_VERSION: not installed or not on PATH"
  exit 1
fi
if [ $# -ne 0 ]; then
  echo "usage: $0 [--check]" >&2
  exit 2
fi

if [ -z "$lean_bin" ]; then
  if command -v zstd >/dev/null 2>&1; then
    extension="tar.zst"
    default_sha256="$tar_sha256"
    unpack="zstd"
  elif command -v unzip >/dev/null 2>&1; then
    extension="zip"
    default_sha256="$zip_sha256"
    unpack="unzip"
  else
    echo "error: zstd or unzip is required to unpack the Lean toolchain" >&2
    exit 1
  fi
  LEAN_SHA256="${LEAN_SHA256-$default_sha256}"
  tarball="lean-${LEAN_VERSION}-${platform}.${extension}"
  mkdir -p "$LEAN_CACHE" "$LEAN_PREFIX"
  archive="$LEAN_CACHE/$tarball"
  if [ ! -f "$archive" ]; then
    url="https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/${tarball}"
    echo "downloading $url"
    curl_args=""
    if [ -n "${CURL_CA_BUNDLE:-}" ]; then
      curl_args="--cacert $CURL_CA_BUNDLE"
    fi
    # shellcheck disable=SC2086
    curl --fail --location --proto =https --retry 5 --retry-all-errors \
      $curl_args --output "$archive.part" "$url"
    mv "$archive.part" "$archive"
  fi
  if command -v sha256sum >/dev/null 2>&1; then
    actual=$(sha256sum "$archive" | cut -d' ' -f1)
  else
    actual=$(shasum -a 256 "$archive" | cut -d' ' -f1)
  fi
  echo "sha256 $actual  $tarball"
  if [ -n "$LEAN_SHA256" ] && [ "$actual" != "$LEAN_SHA256" ]; then
    echo "error: $tarball has digest $actual, not $LEAN_SHA256" >&2
    exit 1
  fi
  echo "extracting into $LEAN_PREFIX"
  if [ "$unpack" = "zstd" ]; then
    zstd -d -c "$archive" | tar -xf - -C "$LEAN_PREFIX"
  else
    unzip -q -o "$archive" -d "$LEAN_PREFIX"
  fi
  lean_bin="$download_home/bin/lean"
  if [ ! -x "$lean_bin" ] || ! version_matches "$lean_bin"; then
    echo "error: extracted toolchain is not Lean $LEAN_VERSION" >&2
    exit 1
  fi
fi

"$lean_bin" --version
python3 "$script_dir/check_lean.py" "$lean_bin"
