#!/usr/bin/env bash
#
# Install tla and tla-mcp binaries from a GitHub release.
#
# Usage:
#   curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash
#   curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash -s -- --bin tla-mcp
#   curl -fsSL https://raw.githubusercontent.com/fabracht/tla-rs/main/scripts/install.sh | bash -s -- --version v0.4.2 --dir /usr/local/bin
#
# Flags:
#   --bin <tla|tla-mcp|both>  Which binary to install (default: both)
#   --version <vX.Y.Z>        Release tag to install (default: latest)
#   --dir <path>              Install directory (default: $HOME/.local/bin)

set -euo pipefail

REPO="fabracht/tla-rs"
INSTALL_DIR="${HOME}/.local/bin"
VERSION="latest"
BIN_CHOICE="both"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --bin)
            BIN_CHOICE="$2"
            shift 2
            ;;
        --version)
            VERSION="$2"
            shift 2
            ;;
        --dir)
            INSTALL_DIR="$2"
            shift 2
            ;;
        -h|--help)
            grep '^#' "$0" | sed 's/^# //;s/^#//' | head -20
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
        # Accept both "v0.4.2" and "0.4.2"
        case "$VERSION" in
            v*) echo "$VERSION" ;;
            *)  echo "v$VERSION" ;;
        esac
        return
    fi
    local resolved
    resolved="$(curl -fsSL "https://api.github.com/repos/${REPO}/releases/latest" \
        | grep -E '^\s*"tag_name":' \
        | head -1 \
        | cut -d'"' -f4)"
    if [[ -z "$resolved" ]]; then
        echo "error: failed to resolve latest release tag" >&2
        exit 1
    fi
    echo "$resolved"
}

download_binary() {
    local binary="$1" platform="$2" version="$3"
    local asset="${binary}-${platform}"
    local url="https://github.com/${REPO}/releases/download/${version}/${asset}"
    local target="${INSTALL_DIR}/${binary}"
    echo "  downloading ${asset} from ${version}..."
    curl --fail --silent --show-error --location --output "$target" "$url"
    chmod +x "$target"
    echo "  installed: ${target}"
}

PLATFORM="$(detect_platform)"
RESOLVED_VERSION="$(resolve_version)"

echo "platform: ${PLATFORM}"
echo "version:  ${RESOLVED_VERSION}"
echo "dir:      ${INSTALL_DIR}"

mkdir -p "$INSTALL_DIR"

case "$BIN_CHOICE" in
    tla)     download_binary tla     "$PLATFORM" "$RESOLVED_VERSION" ;;
    tla-mcp) download_binary tla-mcp "$PLATFORM" "$RESOLVED_VERSION" ;;
    both)
        download_binary tla     "$PLATFORM" "$RESOLVED_VERSION"
        download_binary tla-mcp "$PLATFORM" "$RESOLVED_VERSION"
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
