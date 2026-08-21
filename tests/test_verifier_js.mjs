// Golden tests for the browser verifier: it must agree exactly with the
// upstream dual-verified outputs on every vendored configuration.
import { test } from "node:test";
import assert from "node:assert";
import { createRequire } from "node:module";
import { readFileSync, readdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import path from "node:path";

const require = createRequire(import.meta.url);
const here = path.dirname(fileURLToPath(import.meta.url));
const { verify, parsePoints } = require(path.join(here, "..", "assets", "js", "verifier.js"));

const srcdir = path.join(here, "..", "data", "sources", "tejsteadqc");
const dirs = readdirSync(srcdir).filter(d => /^(square|triangle|convex)-n\d+$/.test(d));

for (const d of dirs) {
  test(`verifier.js matches upstream: ${d}`, () => {
    const variant = d.split("-")[0];
    const pts = parsePoints(readFileSync(path.join(srcdir, d, "coordinates.txt"), "utf8"));
    const expected = JSON.parse(readFileSync(path.join(srcdir, d, "verify_output.json"), "utf8")).a;
    const got = verify(variant, pts);
    // value_fraction must match after reduction (upstream may not reduce).
    const [gn, gd] = got.value_fraction.split("/").map(BigInt);
    const [en, ed] = expected.value_fraction.split("/").map(BigInt);
    assert.strictEqual(gn * ed, en * gd, "value fraction");
    assert.deepStrictEqual(got.min_triple, expected.min_triple);
    assert.strictEqual(got.num_min_ties, expected.num_min_ties);
    assert.strictEqual(got.feasible, true);
    assert.strictEqual(got.hull_vertex_count, expected.hull_vertex_count);
    assert.strictEqual(got.triples_checked, expected.triples_checked);
  });
}

test("equilateral frame gives the affine-invariant value", () => {
  // AlphaEvolve triangle n=11 in its native equilateral frame. One published
  // float64 point lies ~1.2e-17 OUTSIDE the true triangle, so exact
  // feasibility correctly fails — but only at boundary precision, and the
  // value must still come out right.
  const txt = readFileSync(path.join(here, "..", "data", "sources", "alphaevolve", "triangle_n11.txt"), "utf8");
  const got = verify("triangle-eq", parsePoints(txt));
  assert.strictEqual(got.feasible, false);
  assert.ok(got.violation_magnitude < 1e-15, String(got.violation_magnitude));
  assert.ok(Math.abs(parseFloat(got.value) - 0.036529889880030156) < 1e-12, got.value);
});
