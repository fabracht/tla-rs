import { defineConfig, devices } from "@playwright/test";

const PORT = Number(process.env.EXPLORER_PORT ?? 8791);
const FIXTURES = process.env.EXPLORER_FIXTURES_DIR ?? "fixtures";

export default defineConfig({
  testDir: ".",
  timeout: 30_000,
  forbidOnly: !!process.env.CI,
  reporter: process.env.CI ? "list" : "line",
  use: {
    baseURL: `http://127.0.0.1:${PORT}`,
    ...devices["Desktop Chrome"],
  },
  webServer: {
    command: `python3 -m http.server ${PORT} --directory ${FIXTURES} --bind 127.0.0.1`,
    port: PORT,
    reuseExistingServer: !process.env.CI,
  },
});
