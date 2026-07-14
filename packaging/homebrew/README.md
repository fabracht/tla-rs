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

This is automated. The `update-homebrew-tap` job in `.github/workflows/release.yml`
runs after every `vX.Y.Z` tag: it downloads the release's `SHA256SUMS`, rewrites
`Formula/tla-mcp.rb` in the tap repo via `scripts/update-homebrew-formula.sh`
(version, URLs, and all six checksums), then commits and pushes to the tap.

**Prerequisite:** the tla-rs repo must have a `HOMEBREW_TAP_TOKEN` secret — a PAT
(or fine-grained token) with `contents: write` on `fabracht/homebrew-tla`. The
default `GITHUB_TOKEN` cannot push to a different repo, so without this secret the
job fails and the tap stays stale.

### Manual bump (fallback)

If the automation is disabled or you need to bump out of band, run the same script
against a checkout of the tap:

```bash
VERSION=0.6.7  # replace with new version (no leading v)
curl -fsSL "https://github.com/fabracht/tla-rs/releases/download/v${VERSION}/SHA256SUMS" -o /tmp/SHA256SUMS
bash scripts/update-homebrew-formula.sh "$VERSION" path/to/homebrew-tla/Formula/tla-mcp.rb /tmp/SHA256SUMS
```

Then commit the formula update to the tap repo and push.

## Why a tap and not homebrew-core?

`homebrew-core` requires the project to meet popularity / maintenance criteria (notable user base, stable release cadence, etc.). A personal tap has no such requirement and works identically for end users, just with a slightly longer install command.
