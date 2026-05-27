#!/usr/bin/env bash
#
# Install tla and tla-mcp binaries from a GitHub release.
# Verifies SHA256 checksums against the release's SHA256SUMS asset
# before installing.

set -euo pipefail

REPO="fabracht/tla-rs"
INSTALL_DIR="${HOME}/.local/bin"
VERSION="latest"
BIN_CHOICE="both"

print_help() {
    cat <<'EOF'
Install tla and tla-mcp binaries from a GitHub release.

Usage:
  curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash
  curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash -s -- --bin tla-mcp
  curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash -s -- --version v0.4.2 --dir /usr/local/bin

Flags:
  --bin <tla|tla-mcp|both>  Which binary to install (default: both)
  --version <vX.Y.Z>        Release tag to install (default: latest)
  --dir <path>              Install directory (default: $HOME/.local/bin)
  -h, --help                Show this message

Each downloaded binary is verified against the SHA256SUMS asset attached
to the release. If SHA256SUMS is missing from the chosen release (older
versions before checksum publishing was added), the script fails closed.
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --bin)
            BIN_CHOICE="${2:?error: --bin requires a value}"
            shift 2
            ;;
        --version)
            VERSION="${2:?error: --version requires a value}"
            shift 2
            ;;
        --dir)
            INSTALL_DIR="${2:?error: --dir requires a value}"
            shift 2
            ;;
        -h|--help)
            print_help
            exit 0
            ;;
        *)
            echo "error: unknown flag '$1'" >&2
            echo "see --help for usage" >&2
            exit 2
            ;;
    esac
done

case "$BIN_CHOICE" in
    tla|tla-mcp|both) ;;
    *)
        echo "error: --bin must be one of: tla, tla-mcp, both (got '$BIN_CHOICE')" >&2
        exit 2
        ;;
esac

detect_platform() {
    local os arch
    case "$(uname -s)" in
        Linux*)  os="linux" ;;
        Darwin*) os="macos" ;;
        *)
            echo "error: unsupported OS '$(uname -s)'. Try cargo install tla-checker." >&2
            exit 1
            ;;
    esac
    case "$(uname -m)" in
        x86_64|amd64) arch="amd64" ;;
        arm64|aarch64)
            if [[ "$os" == "linux" ]]; then
                echo "error: linux-arm64 prebuilt binary is not produced yet. Try cargo install tla-checker." >&2
                exit 1
            fi
            arch="arm64"
            ;;
        *)
            echo "error: unsupported architecture '$(uname -m)'" >&2
            exit 1
            ;;
    esac
    echo "${os}-${arch}"
}

resolve_version() {
    if [[ "$VERSION" != "latest" ]]; then
        case "$VERSION" in
            v*) echo "$VERSION" ;;
            *)  echo "v$VERSION" ;;
        esac
        return
    fi
    local resolved
    resolved="$(curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" \
        | grep -E '^[[:space:]]*"tag_name":' \
        | head -1 \
        | cut -d'"' -f4)"
    if [[ -z "$resolved" ]]; then
        echo "error: failed to resolve latest release tag" >&2
        exit 1
    fi
    echo "$resolved"
}

pick_hasher() {
    if command -v sha256sum >/dev/null 2>&1; then
        echo "sha256sum"
    elif command -v shasum >/dev/null 2>&1; then
        echo "shasum -a 256"
    else
        echo "error: no sha256sum or shasum binary available; cannot verify download" >&2
        exit 1
    fi
}

PLATFORM="$(detect_platform)"
RESOLVED_VERSION="$(resolve_version)"
HASHER="$(pick_hasher)"

echo "platform: ${PLATFORM}"
echo "version:  ${RESOLVED_VERSION}"
echo "dir:      ${INSTALL_DIR}"

mkdir -p "$INSTALL_DIR"

CHECKSUMS_FILE="$(mktemp -t tla-checksums.XXXXXX)"
trap 'rm -f "$CHECKSUMS_FILE" "${INSTALL_DIR}"/.*.tmp.$$' EXIT
CHECKSUMS_URL="https://github.com/${REPO}/releases/download/${RESOLVED_VERSION}/SHA256SUMS"
if ! curl --fail --silent --show-error --location --output "$CHECKSUMS_FILE" "$CHECKSUMS_URL"; then
    echo "error: SHA256SUMS asset missing from ${RESOLVED_VERSION} release." >&2
    echo "       Releases v0.4.2 and earlier do not include this asset." >&2
    echo "       Pass --version v0.4.3 or later, or use cargo install tla-checker." >&2
    exit 1
fi
echo "fetched: SHA256SUMS"

verify_and_install() {
    local binary="$1"
    local asset="${binary}-${PLATFORM}"
    local url="https://github.com/${REPO}/releases/download/${RESOLVED_VERSION}/${asset}"
    local target="${INSTALL_DIR}/${binary}"
    local expected actual

    expected="$(grep -E "[[:space:]]${asset}\$" "$CHECKSUMS_FILE" | awk '{print $1}')"
    if [[ -z "$expected" ]]; then
        echo "error: no SHA256 entry for ${asset} in SHA256SUMS" >&2
        exit 1
    fi

    echo "  downloading ${asset}..."
    local tmp_target="${INSTALL_DIR}/.${binary}.tmp.$$"
    curl --fail --silent --show-error --location --output "$tmp_target" "$url"
    actual="$($HASHER "$tmp_target" | awk '{print $1}')"
    if [[ "$expected" != "$actual" ]]; then
        echo "error: checksum mismatch for ${asset}" >&2
        echo "  expected: ${expected}" >&2
        echo "  actual:   ${actual}" >&2
        rm -f "$tmp_target"
        exit 1
    fi
    chmod +x "$tmp_target"
    mv -f "$tmp_target" "$target"
    echo "  installed: ${target} (sha256 verified)"
}

case "$BIN_CHOICE" in
    tla)     verify_and_install tla ;;
    tla-mcp) verify_and_install tla-mcp ;;
    both)
        verify_and_install tla
        verify_and_install tla-mcp
        ;;
esac

echo
echo "Done."
echo
case ":${PATH}:" in
    *":${INSTALL_DIR}:"*) ;;
    *)
        echo "note: ${INSTALL_DIR} is not on your PATH."
        echo "      add it (e.g.) by appending to your shell rc:"
        echo "        export PATH=\"${INSTALL_DIR}:\$PATH\""
        ;;
esac
