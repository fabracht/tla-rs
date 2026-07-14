class TlaMcp < Formula
  desc "TLA+ model checker (tla) and MCP server (tla-mcp)"
  homepage "https://github.com/fabracht/tla-rs"
  version "0.6.7"
  license "MIT OR Apache-2.0"

  livecheck do
    url :stable
    strategy :github_latest
  end

  on_macos do
    on_arm do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-macos-arm64"
      sha256 "39f8bf4cf4821f78cc11333007f72b7425d9c01270d520ebd5b0d579d9069ca8"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-mcp-macos-arm64"
        sha256 "99efd80a98b2b7ec98907f441791d0aa97f2329e53de12adfa8247740f1e2247"
      end
    end
    on_intel do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-macos-amd64"
      sha256 "ccabfdfda932ffe1ee4baecc68055b47f51390e013b4e007f857593c4224775f"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-mcp-macos-amd64"
        sha256 "8073165804ba7f63a2dbea2c8e010eeefb6dc5ccefdce0f16c79f5c39ba8af7a"
      end
    end
  end

  on_linux do
    url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-linux-amd64"
    sha256 "1e37cd87a289a0bced774f2aece4f5a44d771302ed9d7d471cd0e070ad3beaab"

    resource "tla-mcp-bin" do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.6.7/tla-mcp-linux-amd64"
      sha256 "504db6fc85abc820164310d3b0a0881949134829a6184566fac53930c06ef13c"
    end
  end

  def platform_suffix
    if OS.mac?
      Hardware::CPU.arm? ? "macos-arm64" : "macos-amd64"
    else
      "linux-amd64"
    end
  end

  def install
    bin.install "tla-#{platform_suffix}" => "tla"

    resource("tla-mcp-bin").stage do
      bin.install "tla-mcp-#{platform_suffix}" => "tla-mcp"
    end
  end

  test do
    assert_match "tla", shell_output("#{bin}/tla --help", 0)
    # tla-mcp is a stdio server; verify it loads without panic by feeding EOF
    output = shell_output("echo '' | #{bin}/tla-mcp 2>&1", 1)
    assert_match "ConnectionClosed", output
  end
end
