"""Check simultaneous alternating-cycle switches at every listed order."""
import argparse
import json
from pathlib import Path


def factorization(m):
    """Partners in the two-layer round-robin construction on 2m vertices."""
    n = 2 * m
    table = [[None] * n for _ in range(n - 1)]

    def put(color, x, y):
        assert x != y and table[color][x] is None and table[color][y] is None
        table[color][x], table[color][y] = y, x

    def twist(v):
        return m - 1 - v if m % 2 and v % 2 == 0 else v

    ring = m if m % 2 else m - 1
    for c in range(ring):
        for layer in range(2):
            center = (c + layer) % ring
            if layer:
                center = twist(center)
            for step in range(1, ring // 2 + 1):
                x, y = (center + step) % ring, (center - step) % ring
                if layer:
                    x, y = twist(x), twist(y)
                put(c, layer * m + x, layer * m + y)
            if m % 2 == 0:
                put(c, layer * m + (c + layer) % ring, layer * m + m - 1)
        if m % 2:
            put(c, c, m + (c + 1) % m)

    for offset in range(m):
        if m % 2 and offset == 1:
            continue
        c = ring + offset - int(m % 2 and offset > 1)
        for v in range(m):
            put(c, v, m + (v + offset) % m)

    for v in range(n):
        assert {row[v] for row in table} == set(range(n)) - {v}
    return table


def cycles(first, second):
    unseen = set(range(len(first)))
    while unseen:
        start = min(unseen)
        x, path = start, []
        while True:
            unseen.remove(x)
            path.append(x)
            x = (first if len(path) % 2 else second)[x]
            if x == start:
                break
        assert len(path) >= 4 and len(path) % 2 == 0
        yield path


def merge(components, edges, group):
    """Components of the quotient graph, represented by disjoint bit masks."""
    result = list(components)
    for x, y in edges:
        i = next(i for i, block in enumerate(result) if block & (1 << group[x]))
        j = next(j for j, block in enumerate(result) if block & (1 << group[y]))
        if i != j:
            result[i] |= result[j]
            result.pop(j)
    return tuple(sorted(result))


def every_orientation(parts, choices, group):
    # Equal component partitions have identical possible continuations.
    states = {parts}
    for cycle in choices:
        edges = list(zip(cycle, cycle[1:] + cycle[:1]))
        states = {reached for state in states for take in (edges[::2], edges[1::2])
                  if len(reached := merge(state, take, group)) > 1}
        if not states:
            return True
    return False


def verify(row):
    n = row['n']
    assert n % 2 == 1
    groups = row['groups'] + [[n]]
    assert sorted(v for block in groups for v in block) == list(range(n + 1))
    assert all(groups) and sum(len(block) - 1 for block in groups) == (2 * n + 2) // 3
    group = {v: i for i, block in enumerate(groups) for v in block}
    parts = tuple(1 << i for i in range(len(groups)))
    table = factorization((n + 1) // 2)
    used = set()
    exponent = 0
    for a, b in row['pairs']:
        assert 0 <= a < b < n and a not in used and b not in used
        used.update((a, b))
        choices = list(cycles(table[a], table[b]))
        assert every_orientation(parts, choices, group), (n, a, b)
        exponent += len(choices) - 1
    for c, partners in enumerate(table):
        if c not in used:
            edges = [(v, w) for v, w in enumerate(partners) if v < w]
            assert len(merge(parts, edges, group)) == 1, (n, c)
    assert exponent == row['exponent']
    return exponent


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('run the verifier with Python assertions enabled')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('order', nargs='?', type=int, help='restrict to one odd order')
    args = parser.parse_args()
    data = Path(__file__).with_name('families.jsonl')
    rows = [json.loads(line) for line in data.read_text().splitlines()]
    assert [r['n'] for r in rows] == [15, *range(19, 77, 2)]
    if args.order is not None:
        rows = [r for r in rows if r['n'] == args.order]
        if not rows:
            parser.error('order absent from the certificate')
    for row in rows:
        print(f"K{row['n']} and K{row['n'] + 1}: 2^{verify(row)}", flush=True)
