"""Independent path checks for the single-line obstruction. Python 3.10+."""
from itertools import combinations
from pathlib import Path
import json

BASE = Path(__file__).resolve().parent


def require(ok, error):
    if not ok:
        raise ValueError(error)


def reached(mate, groups):
    neighbors = [set() for _ in range(15)]
    for x in range(15):
        if mate[x] != 15:
            neighbors[x].add(mate[x])
    for group in groups:
        for x, y in zip(group, group[1:]):
            neighbors[x].add(y)
            neighbors[y].add(x)
    queue, seen = [0], {0}
    for x in queue:
        for y in neighbors[x] - seen:
            queue.append(y)
            seen.add(y)
    return seen


def fails(mates, groups):
    return [c for c, m in enumerate(mates) if len(reached(m, groups)) < 15]


def wild(groups):
    return {tuple(sorted((x, y))) for g in groups for x, y in zip(g, g[1:])}


def main():
    case = json.loads((BASE / "line-trap.json").read_text())
    mates, old, new = case["colors"], case["old"], case["new"]
    require(len(mates) == 15, "Wrong number of colors")
    for mate in mates:
        require(sorted(mate) == list(range(16)) and
                all(mate[x] != x and mate[mate[x]] == x for x in range(16)),
                "Invalid perfect matching")
    for x in range(16):
        require(sorted(m[x] for m in mates) == [v for v in range(16) if v != x],
                "Incomplete or overlapping color classes")
    for g in [old, new]:
        require(sorted(x for group in g for x in group) == list(range(15)) and
                all(len(group) == 3 for group in g), "Invalid partition")
    require(fails(mates, old) == [6] and fails(mates, new) == [], "Repair failed")
    require(wild(old)-wild(new) == {(0, 6), (1, 9)}, "Wrong removals")
    require(wild(new)-wild(old) == {(0, 1), (6, 9)}, "Wrong additions")

    tested = 0
    for i, g in enumerate(old):
        for singleton in g:
            pieces = [[singleton], [v for v in g if v != singleton]]
            pieces += [group for j, group in enumerate(old) if j != i]
            # A removal breaks a triple into these first two pieces. An addition
            # can join two pieces or stay within one. Joining the first two
            # returns to the starting partition.
            options = [pieces]
            for a, b in combinations(range(6), 2):
                if (a, b) == (0, 1):
                    continue
                merged = [p for j, p in enumerate(pieces) if j not in (a, b)]
                options.append(merged + [pieces[a] + pieces[b]])
            for groups in options:
                require(any(c != 6 for c in fails(mates, groups)),
                        "One replacement escaped with all protected colors")
                tested += 1
    require(tested == 225, "Missing component patterns")
    print("Initially only color 6 fails. The two replacements connect every color.")
    print("Every one of the 225 ways to change the component pattern breaks a protected color.")


if __name__ == "__main__":
    main()
