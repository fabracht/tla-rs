import { test, expect, Page } from "@playwright/test";

async function openExplorer(page: Page) {
  await page.goto("/explore.html");
  await page.locator("#tab-explore").click();
  await expect(page.locator("#explore-view")).not.toHaveClass(/hidden/);
  await expect(page.locator('[id^="arow-"]').first()).toBeVisible();
}

const crumbs = (page: Page) => page.locator("#explore-view .crumbs");
const yValue = (page: Page) =>
  page
    .locator("#explore-view table.state tr", {
      has: page.locator("td.vn", { hasText: /^y$/ }),
    })
    .locator("td.vv");
const fanVariants = (page: Page) =>
  page.locator("#explore-view .agroup", { has: page.locator("#arow-0") }).locator(".avariants");

test.describe("exported explorable demo explorer", () => {
  test.beforeEach(async ({ page }) => {
    await openExplorer(page);
  });

  test("renders one action row per enabled-action group", async ({ page }) => {
    await expect(page.locator('[id^="arow-"]')).toHaveCount(2);
    await expect(page.locator('#arow-0[data-group="Fan"]')).toBeVisible();
    await expect(page.locator("#arow-1[data-i]")).toBeVisible();
  });

  test("solo hotkey fires the transition and advances the state", async ({ page }) => {
    await expect(crumbs(page)).toHaveText("Init");
    await expect(yValue(page)).toHaveText("0");

    await page.keyboard.press("2");

    await expect(crumbs(page)).toContainText("Tick");
    await expect(yValue(page)).toHaveText("1");
  });

  test("Backspace steps back to the previous state", async ({ page }) => {
    await page.keyboard.press("2");
    await expect(crumbs(page)).toContainText("Tick");

    await page.keyboard.press("Backspace");

    await expect(crumbs(page)).toHaveText("Init");
    await expect(yValue(page)).toHaveText("0");
  });

  test("group hotkey expands the variant sublist", async ({ page }) => {
    await expect(fanVariants(page)).toHaveClass(/hidden/);

    await page.keyboard.press("1");

    await expect(fanVariants(page)).not.toHaveClass(/hidden/);
  });
});
