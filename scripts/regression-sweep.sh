#!/usr/bin/env bash
set -uo pipefail

# Regression sweep over the extended local sample corpus (.local_only, gitignored).
# A/B-compares the current working tree's `tla` binary against a baseline build,
# so specs that fail identically on both sides (e.g. missing constants) wash out
# and only genuine behavior CHANGES surface. Run before merging any checker change.
#
# Usage:
#   scripts/regression-sweep.sh [BASELINE_REF] [SAMPLES_DIR] [MAX_STATES]
#     BASELINE_REF  git ref to compare against (default: origin/main)
#     SAMPLES_DIR   directory of .tla samples (default: .local_only)
#     MAX_STATES    per-spec state budget (default: 20000)
# Exit code is non-zero if any spec's normalized output differs.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE_REF="${1:-origin/main}"
SAMPLES_DIR="${2:-.local_only}"
MAX_STATES="${3:-20000}"
PER_SPEC_TIMEOUT=30

if [ ! -d "$SAMPLES_DIR" ]; then
  echo "samples dir not found: $SAMPLES_DIR (nothing to sweep)"
  exit 0
fi

WORK="$(mktemp -d)"
BASE_TREE="$WORK/baseline"
trap 'git worktree remove --force "$BASE_TREE" >/dev/null 2>&1; rm -rf "$WORK"' EXIT

echo "building current binary..."
cargo build --release --bin tla >/dev/null 2>&1 || { echo "current build failed"; exit 2; }
CUR_BIN="$REPO_ROOT/target/release/tla"

echo "building baseline binary from $BASELINE_REF..."
git worktree add --detach "$BASE_TREE" "$BASELINE_REF" >/dev/null 2>&1 || { echo "cannot create baseline worktree for $BASELINE_REF"; exit 2; }
( cd "$BASE_TREE" && cargo build --release --bin tla >/dev/null 2>&1 ) || { echo "baseline build failed"; exit 2; }
BASE_BIN="$BASE_TREE/target/release/tla"

# Keep only the deterministic, outcome-relevant lines; drop timing/progress/paths.
normalize() {
  grep -aiE "reachable states:|transitions:|max depth:|model checking complete|invariant .* violated|deadlock|error:|these definitions look like|warning:" \
    | sed -E 's/[0-9]+\.[0-9]+s//g'
}

run_one() {
  timeout "$PER_SPEC_TIMEOUT" "$1" "$2" --max-states "$MAX_STATES" 2>&1 | normalize
}

total=0; diffs=0; diff_list=""
while IFS= read -r spec; do
  total=$((total+1))
  cur="$(run_one "$CUR_BIN" "$spec")"
  base="$(run_one "$BASE_BIN" "$spec")"
  if [ "$cur" != "$base" ]; then
    diffs=$((diffs+1))
    diff_list="$diff_list\n$spec"
  fi
done < <(find "$SAMPLES_DIR" -name '*.tla' | sort)

echo ""
echo "=== regression sweep: $SAMPLES_DIR vs $BASELINE_REF ==="
echo "specs=$total  differing=$diffs"
if [ "$diffs" -ne 0 ]; then
  echo -e "differing specs (investigate):$diff_list"
  echo ""
  echo "re-run a single spec side by side:"
  echo "  diff <($BASE_BIN <spec> --max-states $MAX_STATES) <($CUR_BIN <spec> --max-states $MAX_STATES)"
  exit 1
fi
echo "no regressions"
