"""Enumerate all starters for a rotation of order seven and check the templates.

Lean uses crossing-edge masks on the 105 edges. This independent checker uses
closed sets of three and six points. The only input is the list of proposed
partitions, read from the Lean file so they cannot drift out of sync.
"""
from ast import literal_eval
from collections import defaultdict
from itertools import combinations
from pathlib import Path


def orbit(a, b):
    """Tag an edge orbit. None denotes the invariant matching."""
    a, b = sorted((a, b))
    if (a, b) == (14, 15) or a < 7 and b == a + 7:
        return None
    if b >= 14:
        return 12 + 2 * (b - 14) + a // 7
    if a // 7 == b // 7:
        return 3 * (a // 7) + min(b - a, 7 - (b - a)) - 1
    return 5 + (b - a) % 7


def starters(root):
    """Yield all legal pairings of the other fourteen finite points."""
    def pair(left, used, edges):
        if not left:
            yield used, edges
            return
        head, *tail = left
        for i, other in enumerate(tail):
            tag = orbit(head, other)
            if tag is not None and not used & (1 << tag):
                yield from pair(tail[:i] + tail[i + 1:], used | (1 << tag),
                                edges + ((1 << head) | (1 << other),))
    yield from pair([p for p in range(15) if p != root],
                    1 << orbit(root, 15), ())


def rotate(side):
    def shift(seven):
        return ((seven << 1) & 127) | (seven >> 6)
    return (side & 16384) | shift(side & 127) | (shift((side >> 7) & 127) << 7)


def bad_sides(root, edges):
    for e in edges:
        yield (1 << root) | e
    for x, y, z in combinations(edges, 3):
        yield x | y | z


def read_patterns():
    text = Path(__file__).with_name("Seven.lean").read_text()
    data = text.split("def patterns : Array Pattern := #", 1)[1].split("def pts", 1)[0]
    return literal_eval(data.strip())


def check():
    patterns = read_patterns()
    all_wins = (1 << len(patterns)) - 1
    blocked = defaultdict(int)
    fixed = tuple((1 << v) | (1 << (v + 7)) for v in range(7))
    fixed_bad = set(bad_sides(14, fixed))
    for i, groups in enumerate(patterns):
        assert len(groups) == 5 and all(g.bit_count() == 3 for g in groups)
        assert sum(groups) == 32767 and len(set(groups)) == 5
        assert all(not (g & h) for g, h in combinations(groups, 2))
        for side in groups + [g | h for g, h in combinations(groups, 2)]:
            assert side not in fixed_bad
            for _ in range(7):
                blocked[side] |= 1 << i
                side = rotate(side)
    tables = []
    for root in (0, 7):
        table = defaultdict(list)
        for tag, edges in starters(root):
            misses = 0
            for side in bad_sides(root, edges):
                misses |= blocked[side]
            table[tag].append(all_wins ^ misses)
        assert sum(map(len, table.values())) == 19876
        tables.append(table)
    a, b = tables
    n = 0
    for tag, records in a.items():
        for left in records:
            for right in b[65535 ^ tag]:
                assert left & right
                n += 1
    assert n == 797448
    print(f"{n:,} compatible starter pairs, all covered by {len(patterns)} groupings.")


if __name__ == "__main__":
    check()
