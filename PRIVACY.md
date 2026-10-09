# Privacy

tla-rs and the tla-mcp MCP server run entirely on your local machine.

- No network requests are made.
- No telemetry, analytics, or usage data is collected.
- No data leaves your machine.
- Files are read from the paths you pass as arguments and from files those
  paths imply: the `<spec>.cfg` next to a spec (when no cfg path is given),
  the `.tla` modules a spec `EXTENDS` or `INSTANCE`s, the spec, cfg and
  replay files a demo manifest references, and `trace.json` in the current
  directory when you load a trace in interactive mode (`l`).
- Files are written only when you ask: `append_beat` rewrites the manifest
  it is given, `export_demo_doc` and `export_demo_html` write their
  `out_path`, the CLI writes the files you name in its export options, and
  saving a trace in interactive mode (`s`) writes `trace.json` in the current
  directory, replacing any file of that name.

The MCP server communicates over stdio with the parent process (your MCP
client) and nowhere else. Source code: https://github.com/fabracht/tla-rs
