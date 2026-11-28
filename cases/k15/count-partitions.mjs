// Usage: node count-partitions.mjs <profiles.json>
// Each record has a profile identifier and fifteen lists of seven vertex pairs.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

function countPartitions(colors) {
  const vertices = 15;
  const full = (1 << vertices) - 1;
  assert.equal(colors.length, vertices);
  const edges = new Set();
  for (const matching of colors) {
    assert.equal(matching.length, 7);
    assert.equal(new Set(matching.flat()).size, 14);
    for (const edge of matching) {
      assert.equal(edge.length, 2);
      assert(edge.every(v => Number.isInteger(v) && v >= 0 && v < vertices));
      edges.add((1 << edge[0]) | (1 << edge[1]));
    }
  }
  assert.equal(edges.size, 105);

  const closed = new Uint8Array(full + 1);
  const triples = Array.from({ length: vertices }, () => []);
  const first = mask => 31 - Math.clz32(mask & -mask);
  for (let mask = 1; mask <= full; mask++) {
    let size = 0;
    for (let rest = mask; rest; rest &= rest - 1) size++;
    if (size !== 3 && size !== 6) continue;
    if (size === 3) triples[first(mask)].push(mask);
    closed[mask] = colors.some(matching => matching.every(([a, b]) =>
      (((mask >> a) ^ (mask >> b)) & 1) === 0));
  }

  const blocks = [];
  let total = 0, singles = 0, winning = 0;
  function visit(remaining, singleCutsPass, allCutsPass) {
    if (remaining === 0) {
      total++;
      if (singleCutsPass) singles++;
      if (allCutsPass) winning++;
      return;
    }
    for (const block of triples[first(remaining)]) {
      if ((remaining & block) !== block) continue;
      const single = singleCutsPass && !closed[block];
      const all = single && allCutsPass && blocks.every(other => !closed[block | other]);
      blocks.push(block);
      visit(remaining ^ block, single, all);
      blocks.pop();
    }
  }
  visit(full, true, true);
  assert.equal(total, 1401400);
  return { singles, winning };
}

for (const { profile, colors } of JSON.parse(readFileSync(process.argv[2], 'utf8'))) {
  console.log(JSON.stringify({ profile, ...countPartitions(colors) }));
}
