#!/bin/sh
# SPDX-License-Identifier: Apache-2.0
#
# Reproduce every claim this directory makes, in one command.
#
#   sh verify.sh
#
# Runs, in order:
#   1. tools/install-isabelle.sh -- install the pinned platform distribution
#   2. tools/build.sh --pdf      -- 'sorry' gate, generated-data checks,
#                                  the Isabelle session, and the PDF
#   3. tools/check-lean.sh       -- the Lean 4 library
#   4. tools/check_audits.py    -- Lake build, representative dependencies,
#                                  Isabelle oracles, and source manifest
#   5. tools/check_publication.py -- links, catalogue, release partition,
#                                   metadata consistency, and text hygiene
#   6. tools/check_license.py/cffconvert -- licence and citation validation
#
# Each step prints its own output; the last line of this script is the
# verdict. A non-zero exit names the step that failed.
set -eu

script_dir=$(cd "$(dirname "$0")" && pwd)
repo_root="$script_dir"

step() { echo; echo "=== $1"; }

step "1/6 Isabelle toolchain"
sh "$script_dir/tools/install-isabelle.sh"

step "2/6 Isabelle session and document"
sh "$script_dir/tools/build.sh" --pdf

step "3/6 Lean 4 port"
sh "$script_dir/tools/check-lean.sh"

step "4/6 representative proof audits"
if [ -n "${CBETA_XML:-}" ]; then
  ( cd "$repo_root" && python3 tools/check_audits.py --cbeta-xml "$CBETA_XML" )
else
  ( cd "$repo_root" && python3 tools/check_audits.py )
fi

step "5/6 standalone release checks"
( cd "$repo_root" && python3 tools/check_publication.py )

step "6/6 licence and citation metadata"
command -v reuse >/dev/null 2>&1 || {
  echo "reuse is required; install the pinned release with: python3 -m pip install reuse==5.1.1" >&2
  exit 1
}
command -v cffconvert >/dev/null 2>&1 || {
  echo "cffconvert is required; install the pinned release with: python3 -m pip install cffconvert==2.0.0" >&2
  exit 1
}
( cd "$repo_root" && python3 tools/check_license.py && cffconvert --validate )

echo
echo "verify OK on $(date +%F): buddhist-comparative-logic reproduces its claims end to end"
