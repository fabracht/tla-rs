#!/usr/bin/env bash
set -uo pipefail

# Re-derives the expected verdict of every case in tests/liveness_corpus/manifest.json
# by running real TLC, and fails if TLC disagrees with the recorded `expected`/`kind`.
# Local-only: CI runs tests/liveness_oracle.rs against the manifest without Java.
#
# Usage:
#   TLA2TOOLS=/path/to/tla2tools.jar scripts/liveness-oracle.sh [CASE_ID...]
#
# Verdict classification of TLC output:
#   "No error has been found"                  -> ok
#   "is violated by the initial state"         -> violated (init)
#   "Temporal propert(y|ies) ... violated"     -> violated (liveness)
#   "Action property ... is violated"          -> violated (action)
#   "Invariant ... is violated"                -> violated (invariant)
#   anything else                              -> tlc_unsupported
# Observed TLC exit codes: 0 ok, 12 invariant, 13 liveness / init / action, 255 unsupported.

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CORPUS="$REPO_ROOT/tests/liveness_corpus"
MANIFEST="$CORPUS/manifest.json"

if [ -z "${TLA2TOOLS:-}" ] || [ ! -f "${TLA2TOOLS}" ]; then
  echo "TLA2TOOLS must point to tla2tools.jar."
  echo "Download: curl -fLO https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar"
  exit 2
fi
command -v java >/dev/null 2>&1 || { echo "java not found on PATH (Java 11+ required)"; exit 2; }
command -v jq >/dev/null 2>&1 || { echo "jq not found on PATH"; exit 2; }

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

classify() {
  local out="$1"
  if grep -q "No error has been found" "$out"; then
    echo "ok -"
  elif grep -q "is violated by the initial state" "$out"; then
    echo "violated init"
  elif grep -Eq "Temporal propert(y|ies) .*violated" "$out"; then
    echo "violated liveness"
  elif grep -Eq "Action property .* is violated" "$out"; then
    echo "violated action"
  elif grep -Eq "Invariant .* is violated" "$out"; then
    echo "violated invariant"
  else
    echo "tlc_unsupported -"
  fi
}

if [ "$#" -gt 0 ]; then
  IDS=("$@")
else
  IDS=()
  while IFS= read -r id; do IDS+=("$id"); done < <(jq -r '.[].id' "$MANIFEST")
fi

disagreements=0
printf "%-6s %-17s %-10s %-17s %-10s %s\n" "id" "expected" "kind" "tlc" "tlc_kind" "exit"
for id in "${IDS[@]}"; do
  entry="$(jq -c --arg id "$id" '.[] | select(.id == $id)' "$MANIFEST")"
  if [ -z "$entry" ]; then
    echo "unknown case id: $id"
    disagreements=$((disagreements + 1))
    continue
  fi
  spec="$CORPUS/$(jq -r '.spec' <<<"$entry")"
  cfg="$CORPUS/$(jq -r '.cfg' <<<"$entry")"
  expected="$(jq -r '.expected' <<<"$entry")"
  expected_kind="$(jq -r '.kind // "-"' <<<"$entry")"
  run_dir="$WORK/$id"
  mkdir -p "$run_dir/states"
  cp "$CORPUS"/specs/*.tla "$run_dir"/
  cp "$cfg" "$run_dir/case.cfg"
  out="$WORK/$id.out"
  (cd "$run_dir" && java -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -workers 1 -nowarning \
    -cleanup -metadir "$run_dir/states" -config case.cfg "$(basename "$spec")" >"$out" 2>&1)
  code=$?
  read -r verdict kind <<<"$(classify "$out")"
  marker=""
  if [ "$verdict" != "$expected" ] || [ "$kind" != "$expected_kind" ]; then
    marker="  <-- DISAGREES"
    disagreements=$((disagreements + 1))
  fi
  printf "%-6s %-17s %-10s %-17s %-10s %s%s\n" "$id" "$expected" "$expected_kind" "$verdict" "$kind" "$code" "$marker"
done

if [ "$disagreements" -gt 0 ]; then
  echo "$disagreements case(s) disagree with TLC"
  exit 1
fi
echo "all ${#IDS[@]} case(s) agree with TLC"
