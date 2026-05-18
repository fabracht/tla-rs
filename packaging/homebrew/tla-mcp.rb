class TlaMcp < Formula
  desc "TLA+ model checker (tla) and MCP server (tla-mcp)"
  homepage "https://github.com/fabracht/tla-rs"
  version "0.4.3"
  license "MIT OR Apache-2.0"

  livecheck do
    url :stable
    strategy :github_latest
  end

  on_macos do
    on_arm do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-macos-arm64"
      sha256 "bb49168e25446add232239b06b3311a4d4e32fceca71c9fb8447dc1f35089030"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-mcp-macos-arm64"
        sha256 "c54945dc749562236331ff44f380b90eac31c0902fcf37bbbf68f0375f6f40b5"
      end
    end
    on_intel do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-macos-amd64"
      sha256 "dad438c186315c0f1fcd2439b2533b22e60425a2b6f43002e8b2f60f8205d426"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-mcp-macos-amd64"
        sha256 "4d8b82ae99ac0784e530b9ddd531a6da4b41d5897515b31df4d2654aef79922f"
      end
    end
  end

  on_linux do
    url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-linux-amd64"
    sha256 "c6bfa870849e149da1fcdff972a9908f7ea383d7acdc5ca8b324b6786447bbf4"

    resource "tla-mcp-bin" do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.3/tla-mcp-linux-amd64"
      sha256 "8849037a01aba6bf761039bc895bd66ae6772709d46d9007fbdaf92a90935e85"
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
