#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
#
# Build the Buddhist_Comparative_Logic Isabelle session.
#
#   sh tools/build.sh           check + build (no document)
#   sh tools/build.sh --pdf     build isabelle/document/root.tex too (implies --clean)
#   sh tools/build.sh --clean   discard cached results first (-c)
#
# Environment overrides: ISABELLE_VERSION, ISABELLE_PREFIX (see
# install-isabelle.sh for defaults).
set -eu

ISABELLE_VERSION="${ISABELLE_VERSION:-Isabelle2025-2}"
ISABELLE_PREFIX="${ISABELLE_PREFIX:-$HOME/.local/opt}"
case "$(uname -s)" in
  Darwin) default_isabelle_home="$ISABELLE_PREFIX/$ISABELLE_VERSION.app" ;;
  *) default_isabelle_home="$ISABELLE_PREFIX/$ISABELLE_VERSION" ;;
esac
ISABELLE_BIN="$default_isabelle_home/bin/isabelle"

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root=$(cd "$script_dir/.." && pwd)
isabelle_root="$repo_root/isabelle"

if [ -n "${ISABELLE_HOME:-}" ] && [ -x "$ISABELLE_HOME/bin/isabelle" ]; then
  ISABELLE_BIN="$ISABELLE_HOME/bin/isabelle"
fi
if [ ! -x "$ISABELLE_BIN" ]; then
  echo "error: isabelle not found at $ISABELLE_BIN (run tools/install-isabelle.sh first)" >&2
  exit 1
fi
version_text=$("$ISABELLE_BIN" version 2>&1) || {
  echo "error: $ISABELLE_BIN cannot report its version" >&2
  exit 1
}
if ! echo "$version_text" | grep -F "$ISABELLE_VERSION" >/dev/null; then
  echo "error: expected $ISABELLE_VERSION, got: $version_text" >&2
  exit 1
fi

# The environment injects a truststore/proxy JAVA_TOOL_OPTIONS for network
# access; the build needs no network, and the option only adds log noise.
unset JAVA_TOOL_OPTIONS 2>/dev/null || true

if grep -rn '\bsorry\b' "$isabelle_root" --include='*.thy' >/dev/null 2>&1; then
  echo "error: 'sorry' found in Isabelle theories -- no admitted proofs allowed" >&2
  grep -rn '\bsorry\b' "$isabelle_root" --include='*.thy' >&2
  exit 1
fi

python3 "$script_dir/check_text.py"
python3 "$script_dir/check_names.py"
python3 "$script_dir/make_index.py" --check

clean_opt=""
pdf_requested=0
for arg in "$@"; do
  case "$arg" in
    --clean) clean_opt="-c" ;;
    --pdf)
      # An up-to-date session is not rebuilt merely because document options
      # changed, which would leave a stale PDF; force a clean session build.
      clean_opt="-c"
      pdf_requested=1
      ;;
    *) echo "usage: $0 [--pdf] [--clean]" >&2; exit 2 ;;
  esac
done

if [ "$pdf_requested" -eq 1 ]; then
  # A stale PDF must not let a no-op or misconfigured executable report a
  # successful end-to-end build.
  rm -f "$repo_root/output/document.pdf"
fi

# Keep the document output option quoted so repositories below a path with
# spaces are passed to Isabelle as one argument.
if [ "$pdf_requested" -eq 1 ]; then
  # shellcheck disable=SC2086
  "$ISABELLE_BIN" build -v -D "$isabelle_root" -o threads=4 $clean_opt \
    -o document=pdf -o document_build=lualatex \
    -o "document_output=$repo_root/output"
else
  # shellcheck disable=SC2086
  "$ISABELLE_BIN" build -v -D "$isabelle_root" -o threads=4 $clean_opt
fi
status=$?

if [ "$status" -eq 0 ]; then
  if [ "$pdf_requested" -eq 1 ] && [ ! -s "$repo_root/output/document.pdf" ]; then
    echo "error: Isabelle returned success but produced no output/document.pdf" >&2
    exit 1
  fi
  echo
  echo "build OK on $(date +%F). Update the Isabelle receipt in docs/STATUS.md and README.md."
fi
exit "$status"
