#!/usr/bin/env bash
#
# Rewrite a Homebrew formula in place for a new release: sets the version,
# updates every release-asset URL to the new tag, and replaces each sha256
# with the checksum for the asset named in the preceding url line, read from
# a SHA256SUMS file. Fails closed if any referenced asset is missing.

set -euo pipefail

if [[ $# -ne 3 ]]; then
    echo "usage: $0 <version> <formula-path> <sha256sums-path>" >&2
    echo "  version: release version, with or without leading v (e.g. 0.6.7)" >&2
    exit 2
fi

VERSION="${1#v}"
FORMULA="$2"
SUMS="$3"

for f in "$FORMULA" "$SUMS"; do
    if [[ ! -f "$f" ]]; then
        echo "error: file not found: $f" >&2
        exit 1
    fi
done

tmp="$(mktemp "${FORMULA}.XXXXXX")"
trap 'rm -f "$tmp"' EXIT

awk -v ver="$VERSION" -v sums="$SUMS" '
BEGIN {
    while ((getline line < sums) > 0) {
        n = split(line, a, / +/)
        if (n >= 2) sha[a[2]] = a[1]
    }
}
/^[[:space:]]*version "/ {
    sub(/version "[^"]*"/, "version \"" ver "\"")
    print; next
}
/^[[:space:]]*url "/ {
    gsub(/releases\/download\/v[^\/]+\//, "releases/download/v" ver "/")
    asset = $0
    sub(/.*\//, "", asset)
    sub(/".*/, "", asset)
    last_asset = asset
    print; next
}
/^[[:space:]]*sha256 "/ {
    if (last_asset == "") {
        print "error: sha256 line without a preceding release url" > "/dev/stderr"
        exit 3
    }
    if (!(last_asset in sha)) {
        print "error: no checksum for asset " last_asset " in " sums > "/dev/stderr"
        exit 3
    }
    sub(/sha256 "[^"]*"/, "sha256 \"" sha[last_asset] "\"")
    last_asset = ""
    print; next
}
{ print }
' "$FORMULA" > "$tmp"

cat "$tmp" > "$FORMULA"
rm -f "$tmp"
trap - EXIT
echo "updated $FORMULA to version $VERSION"
