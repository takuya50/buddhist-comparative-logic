#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
#
# Reproducible Isabelle installation for this project.
#
#   sh tools/install-isabelle.sh          download (cached), verify, extract
#   sh tools/install-isabelle.sh --check  report state, never download
#
# Environment overrides:
#   ISABELLE_VERSION  default Isabelle2025-2
#   ISABELLE_PREFIX   default $HOME/.local/opt   (must be outside the repository)
#   ISABELLE_SHA256   platform tarball digest; empty string disables the check
#   ISABELLE_CACHE    default $HOME/.cache/isabelle
#   CURL_CA_BUNDLE    CA bundle handed to curl when set
set -eu

ISABELLE_VERSION="${ISABELLE_VERSION:-Isabelle2025-2}"
ISABELLE_PREFIX="${ISABELLE_PREFIX:-$HOME/.local/opt}"
ISABELLE_CACHE="${ISABELLE_CACHE:-$HOME/.cache/isabelle}"

script_dir=$(cd "$(dirname "$0")" && pwd)
# Tooling lives below the repository root.
repo_root=$(cd "$script_dir/.." && pwd)

system=$(uname -s)
machine=$(uname -m)
case "$system:$machine" in
  Linux:x86_64|Linux:amd64)
    tarball="${ISABELLE_VERSION}_linux.tar.gz"
    default_sha256="a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c"
    home="$ISABELLE_PREFIX/$ISABELLE_VERSION"
    ;;
  Linux:aarch64|Linux:arm64)
    tarball="${ISABELLE_VERSION}_linux_arm.tar.gz"
    default_sha256="650a9669b4a087675afb34294d82ded2f0704d47d580dd9ed45cddc9f1764bdd"
    home="$ISABELLE_PREFIX/$ISABELLE_VERSION"
    ;;
  Darwin:*)
    tarball="${ISABELLE_VERSION}_macos.tar.gz"
    default_sha256="8f187496e295f169952e944745af9e4ae00c9c1cd2ed4cadbcf7d898e444913e"
    home="$ISABELLE_PREFIX/$ISABELLE_VERSION.app"
    ;;
  *)
    echo "error: no pinned Isabelle archive for $system/$machine" >&2
    exit 1
    ;;
esac
# An explicitly empty override disables verification; an unset override uses
# the digest published for the selected Isabelle distribution.
if [ "$ISABELLE_VERSION" != "Isabelle2025-2" ] && [ -z "${ISABELLE_SHA256+x}" ]; then
  echo "error: set ISABELLE_SHA256 when overriding ISABELLE_VERSION" >&2
  exit 1
fi
ISABELLE_SHA256="${ISABELLE_SHA256-$default_sha256}"

case "$ISABELLE_PREFIX" in
  "$repo_root"|"$repo_root"/*)
    echo "error: ISABELLE_PREFIX must lie outside the repository ($repo_root)" >&2
    exit 2 ;;
esac

report() {
  if [ -x "$home/bin/isabelle" ]; then
    echo "isabelle: $home/bin/isabelle"
    version_text=$("$home/bin/isabelle" version 2>&1) || {
      echo "error: installed Isabelle cannot report its version" >&2
      return 1
    }
    echo "$version_text"
    echo "$version_text" | grep -F "$ISABELLE_VERSION" >/dev/null || {
      echo "error: installed Isabelle is not $ISABELLE_VERSION" >&2
      return 1
    }
    if ls "$home"/heaps/*/HOL >/dev/null 2>&1; then
      echo "HOL heap: present"
    else
      echo "HOL heap: MISSING (run: $home/bin/isabelle build -b HOL)"
    fi
    echo "export PATH=\"$home/bin:\$PATH\""
    return 0
  fi
  echo "isabelle: not installed under $home"
  return 1
}

if [ "${1:-}" = "--check" ]; then
  report
  exit $?
fi

if [ -x "$home/bin/isabelle" ]; then
  if report; then
    exit 0
  fi
  echo "error: refusing to overwrite an incompatible installation at $home" >&2
  exit 1
fi

mkdir -p "$ISABELLE_CACHE" "$ISABELLE_PREFIX"
archive="$ISABELLE_CACHE/$tarball"

ca_opt=""
if [ -n "${CURL_CA_BUNDLE:-}" ]; then
  ca_opt="--cacert $CURL_CA_BUNDLE"
fi

# The canonical /dist/ path currently redirects to a plain-HTTP mirror that
# answers 503; the website-<version> path serves the same file over HTTPS.
urls="https://isabelle.in.tum.de/website-$ISABELLE_VERSION/dist/$tarball
https://isabelle.in.tum.de/dist/$tarball"

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d' ' -f1
  else
    shasum -a 256 "$1" | cut -d' ' -f1
  fi
}

matches_pin() {
  [ -f "$1" ] || return 1
  [ -z "$ISABELLE_SHA256" ] || [ "$(sha256_file "$1")" = "$ISABELLE_SHA256" ]
}

if matches_pin "$archive"; then
  echo "using cached $tarball"
else
  if [ -f "$archive" ]; then
    actual=$(sha256_file "$archive")
    echo "discarding cached $tarball with unexpected sha256 $actual" >&2
    rm -f "$archive"
  fi
  partial="$archive.part"
  if matches_pin "$partial"; then
    mv "$partial" "$archive"
  fi
  downloaded=0
  if [ -f "$archive" ]; then
    downloaded=1
  else
    for url in $urls; do
      echo "downloading $url"
      # shellcheck disable=SC2086
      if curl --fail --location --proto =https --retry 5 --retry-all-errors \
          --continue-at - $ca_opt --output "$partial" "$url"; then
        mv "$partial" "$archive"
        downloaded=1
        break
      fi
      echo "download failed from $url" >&2
    done
  fi
  [ "$downloaded" = 1 ] || {
    echo "error: could not download $tarball" >&2
    exit 1
  }

  actual=$(sha256_file "$archive")
  echo "sha256 $actual  $tarball"
  if [ -n "$ISABELLE_SHA256" ]; then
    if [ "$actual" != "$ISABELLE_SHA256" ]; then
      echo "error: sha256 mismatch (expected $ISABELLE_SHA256)" >&2
      exit 1
    fi
    echo "sha256 matches the pinned digest"
  else
    echo "note: no digest pinned; record the value above in docs/STATUS.md"
  fi
fi

echo "extracting into $ISABELLE_PREFIX"
tar -xzf "$archive" -C "$ISABELLE_PREFIX"
report
