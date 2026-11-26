"""Independent direct graph checks. Run with Python 3.10 or later."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

POINTS = set(range(15))
PATTERNS = [
    [[0, 5, 10], [1, 6, 11], [2, 7, 12], [3, 8, 13], [4, 9, 14]],
    [[1, 9, 11], [3, 5, 10], [6, 8, 13], [4, 12, 14], [0, 2, 7]],
    [[3, 8, 10], [2, 9, 12], [5, 11, 14], [4, 7, 13], [0, 1, 6]],
]


def require(statement, error):
    if not statement:
        raise ValueError(error)


def splits(left):
    if not left:
        yield []
        return
    first = min(left)
    for a, b in combinations(sorted(left - {first}), 2):
        group = [first, a, b]
        for rest in splits(left - set(group)):
            yield [group] + rest


def valid_colors(colors):
    edges = []
    for c, matching in enumerate(colors):
        ends = [v for pair in matching for v in pair]
        if sorted(ends) != sorted(POINTS - {c}):
            return False
        edges.extend(tuple(sorted(pair)) for pair in matching)
    return len(colors) == 15 and len(edges) == len(set(edges)) == 105


def works(colors, groups):
    require(len(groups) == 5 and all(len(g) == 3 for g in groups)
            and sorted(v for g in groups for v in g) == list(range(15)),
            "Invalid grouping")
    wild = [(g[0], g[1]) for g in groups] + [(g[1], g[2]) for g in groups]
    for matching in colors:
        neighbors = [[] for _ in POINTS]
        for a, b in wild + list(matching):
            neighbors[a].append(b)
            neighbors[b].append(a)
        reached, queue = {0}, [0]
        while queue:
            for v in neighbors[queue.pop()]:
                if v not in reached:
                    reached.add(v)
                    queue.append(v)
        if reached != POINTS:
            return False
    return True


def starters(left, used_lengths):
    if not left:
        yield []
        return
    a = min(left)
    for b in sorted(left - {a}):
        length = min(b - a, 15 - (b - a))
        if length in used_lengths:
            continue
        for rest in starters(left - {a, b}, used_lengths | {length}):
            yield [(a, b)] + rest


def check_cyclic():
    tallies = [0, 0, 0]
    for base in starters(POINTS - {0}, set()):
        colors = [[((a+c) % 15, (b+c) % 15) for a, b in base] for c in range(15)]
        require(valid_colors(colors), "Invalid starter")
        for i, pattern in enumerate(PATTERNS):
            if works(colors, pattern):
                tallies[i] += 1
                break
        else:
            raise ValueError(f"Uncovered cyclic coloring: {base}")
    require(tallies == [556, 73, 2], "Unexpected coverage")
    print("Cyclic starters covered by their first working pattern:", tallies)


def check_count():
    universe = set(range(12))
    all_splits = list(splits(universe))
    require(len(all_splits) == 15400, "Unexpected count of splits")
    weighted_loss = 0
    for multiplicity, shape, expected in [
            (3, [2]*6, (0, 10)), (3, [1, 1]+[2]*5, (10, 10)),
            (9, [1, 3]+[2]*4, (5, 4))]:
        parts = []
        start = 0
        for size in shape:
            parts.append(set(range(start, start+size)))
            start += size
        closed = [set().union(*m) for k in range(len(parts)+1) for m in combinations(parts, k)]
        singles = sum(len(u) == 3 for u in closed)
        halves = sum(len(u) == 6 and 0 in u for u in closed)
        require((singles, halves) == expected, "Unexpected cut count for a color")
        weighted_loss += multiplicity * (280*singles + 100*halves)
    require(weighted_loss == 30600 < 2*len(all_splits), "Averaging bound failed")
    print("Total cut failures with multiplicity:", weighted_loss, "over", len(all_splits), "splits")


def check_obstruction():
    doc = json.loads(Path(__file__).with_name("anchor-obstruction.json").read_text())
    colors, fixed = doc["colors"], doc["fixed_groups"]
    require(valid_colors(colors), "Invalid obstruction coloring")
    a, b = map(set, fixed)
    for side in [a, b, a | b]:
        require(all(any((x in side) != (y in side) for x, y in m) for m in colors),
                "One of the initial cuts was already closed")
    results = Counter(works(colors, fixed + rest) for rest in splits(POINTS-a-b))
    require(results == {False: 280}, "An anchored completion succeeded")
    require(works(colors, doc["working_groups"]), "Displayed solution failed")
    print("All 280 fixed-group completions failed; the alternate grouping connects all 15 colors.")


if __name__ == "__main__":
    check_count()
    check_cyclic()
    check_obstruction()
