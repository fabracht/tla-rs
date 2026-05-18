class TlaMcp < Formula
  desc "TLA+ model checker (tla) and MCP server (tla-mcp)"
  homepage "https://github.com/fabracht/tla-rs"
  version "0.4.2"
  license "MIT OR Apache-2.0"

  livecheck do
    url :stable
    strategy :github_latest
  end

  on_macos do
    on_arm do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-macos-arm64"
      sha256 "13ea423628301e74f5ce3364ccd0a013c27a78bf07ba65bd402c4f6e599501e1"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-mcp-macos-arm64"
        sha256 "a1c3536d713e0649ffed9903ef621496c7bbc6d3d7aa932b54446bb65c9f9335"
      end
    end
    on_intel do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-macos-amd64"
      sha256 "943b7e54b73ae7196099909a8012c0956cf1c3ada0ebdb93b80af5f1d6bdee01"

      resource "tla-mcp-bin" do
        url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-mcp-macos-amd64"
        sha256 "0117c01eb8d03f2707d6f5ee46cf64345a637c98c602d641f98b58e24858d1e9"
      end
    end
  end

  on_linux do
    url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-linux-amd64"
    sha256 "d228cf356aa9d9998df55844015ce5bc83240899a5de7d4621f9bf6c0b69d009"

    resource "tla-mcp-bin" do
      url "https://github.com/fabracht/tla-rs/releases/download/v0.4.2/tla-mcp-linux-amd64"
      sha256 "f72281acb2c41b8a20f8b8edbd36f3f0870b45dd9d1b0be050e6a1a8eb09f32a"
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
