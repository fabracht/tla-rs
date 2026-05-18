# Homebrew formula for tla-rs

`tla-mcp.rb` is a Homebrew formula that installs both the `tla` model checker and the `tla-mcp` MCP server from prebuilt GitHub release binaries. It is **not** discoverable via `brew install` unless it lives in a tap repository.

## Setting up the tap (one-time, by the maintainer)

1. Create a new public GitHub repo named `homebrew-tla` under the same owner as `tla-rs`. The `homebrew-` prefix is required — without it `brew tap` will reject the URL.
2. Add a `Formula/` directory and copy this file into it:

   ```
   homebrew-tla/
   └── Formula/
       └── tla-mcp.rb
   ```

3. Commit and push. The tap is now usable as `<owner>/tla`.

## Installing (users)

```bash
brew tap fabracht/tla
brew install tla-mcp
```

Or in a single command:

```bash
brew install fabracht/tla/tla-mcp
```

Both `tla` and `tla-mcp` end up on the user's PATH.

## Updating the formula on each release

After tagging `vX.Y.Z` and verifying the release pipeline produced all eight assets:

1. Update `version` in the formula
2. Update each `url` to point at the new tag
3. Update each `sha256` with the corresponding asset's checksum

Compute the checksums with:

```bash
VERSION=v0.4.3  # replace with new tag
for asset in tla-macos-arm64 tla-macos-amd64 tla-linux-amd64 \
             tla-mcp-macos-arm64 tla-mcp-macos-amd64 tla-mcp-linux-amd64; do
    sha=$(curl -fsSL "https://github.com/fabracht/tla-rs/releases/download/$VERSION/$asset" \
        | shasum -a 256 | cut -d' ' -f1)
    printf "%s  %s\n" "$sha" "$asset"
done
```

Then commit the formula update to the tap repo and push. Long-term automation:

- `brew bump-formula-pr` can prepare the formula update PR
- `goreleaser` / `release-plz` style automation can keep the tap in sync with each release

## Why a tap and not homebrew-core?

`homebrew-core` requires the project to meet popularity / maintenance criteria (notable user base, stable release cadence, etc.). A personal tap has no such requirement and works identically for end users, just with a slightly longer install command.
