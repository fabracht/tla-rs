# Privacy

tla-rs and the tla-mcp MCP server run entirely on your local machine.

- No network requests are made.
- No telemetry, analytics, or usage data is collected.
- No data leaves your machine.
- Files are read only from paths you explicitly pass as arguments.

The MCP server communicates over stdio with the parent process (your MCP
client) and nowhere else. Source code: https://github.com/fabracht/tla-rs
