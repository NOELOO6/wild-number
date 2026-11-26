"""Find ten wild lines on a supplied K15 or K16, or exhaust every candidate."""
import argparse
from itertools import combinations
import json
from pathlib import Path


def read_colors(path):
    obj = json.loads(path.read_text())
    rows = obj.get("mates", obj.get("colors")) if isinstance(obj, dict) else obj
    if not isinstance(rows, list) or len(rows) != 15:
        raise ValueError("Supply fifteen color rows under 'colors' or 'mates'.")
    result = []
    for row in rows:
        if not isinstance(row, list):
            raise ValueError("Each color must be a list.")
        if len(row) == 16 and all(type(v) is int and 0 <= v < 16 for v in row):
            mates = row
        elif len(row) in (7, 8):
            mates = [-1] * 16
            for edge in row:
                if not isinstance(edge, list) or len(edge) != 2 or not all(
                    type(v) is int and 0 <= v < (15 if len(row) == 7 else 16) for v in edge
                ):
                    raise ValueError("An edge has an invalid vertex or format.")
                a, b = edge
                if a == b or mates[a] != -1 or mates[b] != -1:
                    raise ValueError("Two lines of one color touch, or a line is a loop.")
                mates[a], mates[b] = b, a
            if len(row) == 7:
                a = mates.index(-1)
                mates[a], mates[15] = 15, a
        else:
            raise ValueError("Use sixteen partners, seven K15 edges, or eight K16 edges per color.")
        if any(mates[v] == v or mates[mates[v]] != v for v in range(16)):
            raise ValueError("The partners of a color do not form a matching.")
        result.append(mates)
    if any(len({m[v] for m in result}) != 15 for v in range(16)):
        raise ValueError("A line occurs in two colors.")
    return result


def forbidden_sides(colors):
    closed = set()
    for mates in colors:
        edges = [(1 << a) | (1 << b) for a, b in enumerate(mates) if a < b]
        for count in (2, 3):
            closed.update(sum(pairs) for pairs in combinations(edges, count))
    return closed


def search_root(root, closed, count_all):
    root_bit = 1 << root
    available = 65535 ^ root_bit
    triples = [[] for _ in range(16)]
    for a, b, c in combinations((v for v in range(16) if v != root), 3):
        t = (1 << a) | (1 << b) | (1 << c)
        if root_bit | t not in closed:
            triples[a].append(t)
    groups = []
    first = None
    count = 0

    def visit(left):
        nonlocal first, count
        if not left:
            count += 1
            if first is None:
                first = groups.copy()
            return
        a = (left & -left).bit_length() - 1
        for t in triples[a]:
            if t & left == t and all(t | h not in closed for h in groups):
                groups.append(t)
                visit(left ^ t)
                groups.pop()
                if first is not None and not count_all:
                    return

    visit(available)
    return count, first


def verify_witness(colors, wild, n):
    if len(wild) != 10 or len(set(wild)) != 10:
        raise ArithmeticError("Invalid wild-edge count.")
    for mates in colors:
        adj = [set() for _ in range(n)]
        for a, b in list(enumerate(mates)) + wild:
            if a < n and b < n:
                adj[a].add(b)
                adj[b].add(a)
        seen, stack = {0}, [0]
        while stack:
            for b in adj[stack.pop()] - seen:
                seen.add(b)
                stack.append(b)
        if len(seen) != n:
            raise ArithmeticError("The direct connectivity check failed.")


def solve(colors, n, count_all):
    closed = forbidden_sides(colors)
    counts = {}
    answer = {}
    for root in ([15] if n == 15 else range(16)):
        count, first = search_root(root, closed, count_all)
        counts[root] = count
        if first and not answer:
            groups = [[v for v in range(16) if t & (1 << v)] for t in first]
            wild = [edge for group in groups for edge in zip(group, group[1:])]
            verify_witness(colors, wild, n)
            answer = {"wild_number": 10, "groups": groups, "wild_lines": wild}
            if n == 16:
                answer["untouched_vertex"] = root
            if not count_all:
                break
    if not answer:
        answer = {"wild_number": 11, "ten_line_groupings": 0}
    if count_all:
        answer["ten_line_groupings"] = sum(counts.values())
        if n == 16:
            answer["groupings_by_untouched_vertex"] = counts
    return answer


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("vertices", type=int, choices=(15, 16))
    parser.add_argument("coloring", type=Path)
    parser.add_argument("--count", action="store_true", help="count all successful groupings")
    args = parser.parse_args()
    try:
        colors = read_colors(args.coloring)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    print(json.dumps(solve(colors, args.vertices, args.count), indent=2))
