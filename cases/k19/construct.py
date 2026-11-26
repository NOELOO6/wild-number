"""Find and check 13 or 14 wild edges for a supplied minimum proper K19 coloring."""
import argparse
import json
from math import factorial
from pathlib import Path

ORDINARY = range(19)
GROUPS = [(0, 1, 2, 3)] + [tuple(range(i, i + 3)) for i in range(4, 19, 3)]


def round_robin():
    return [[((c + i) % 19, (c - i) % 19) for i in range(1, 10)] for c in ORDINARY]


def complete(colors):
    if len(colors) != 19:
        raise ValueError("Expected nineteen colors.")
    partners = []
    used = set()
    for lines in colors:
        row = [-1] * 20
        if len(lines) != 9:
            raise ValueError("Each color needs nine edges.")
        for a, b in lines:
            if type(a) is not int or type(b) is not int or a not in ORDINARY or b not in ORDINARY:
                raise ValueError("Vertex labels must be integers from 0 through 18.")
            edge = tuple(sorted((a, b)))
            if a == b or row[a] != -1 or row[b] != -1 or edge in used:
                raise ValueError("Invalid, repeated or touching edge.")
            row[a], row[b] = b, a
            used.add(edge)
        missing = row.index(-1)
        row[19], row[missing] = missing, 19
        partners.append(row)
    return partners


def step(cells, vertex, slot, mate):
    # A cell holds its free slots and the names of its unplaced partners.
    free_cell = next(i for i, (slots, _) in enumerate(cells) if slot in slots)
    waiting_cell = next((i for i, (_, waiting) in enumerate(cells) if vertex in waiting), None)
    slots, waiting = cells[free_cell]
    if waiting_cell is None:
        new = (slots - {slot}, waiting | {mate})
    else:
        other_slots, other_waiting = cells[waiting_cell]
        new = ((slots | other_slots) - {slot}, (waiting | other_waiting) - {vertex})
    return [cell for i, cell in enumerate(cells) if i not in (free_cell, waiting_cell)] + [new]


def pieces(edges):
    parent = list(ORDINARY)

    def root(x):
        while parent[x] != x:
            x = parent[x]
        return x

    for a, b in edges:
        parent[root(a)] = root(b)
    return sorted({root(v) for v in ORDINARY})


def solve(colors):
    partners = complete(colors)
    table = {}
    source = Path(__file__).with_name("states.txt")
    for line in source.read_text().splitlines():
        value, *shape = map(int, line.split())
        table[tuple(shape)] = value

    positions = [[(frozenset(), frozenset([m[19]]))] +
                 [(frozenset(g), frozenset()) for g in GROUPS] for m in partners]
    slots = set(ORDINARY)
    placed = {}
    for v in ORDINARY:
        best = None
        for slot in sorted(slots):
            after = [step(cells, v, slot, m[v]) for cells, m in zip(positions, partners)]
            total = sum(table[tuple(sorted(32 * len(free) + len(wait) for free, wait in cells))]
                        for cells in after)
            if best is None or total < best[0]:
                best = (total, slot, after)
        total, slot, positions = best
        if total >= 2 * factorial(len(slots) - 1):
            raise AssertionError("The chosen placement exceeded the proved budget.")
        slots.remove(slot)
        placed[slot] = v

    wild = [(placed[a], placed[b]) for g in GROUPS for a, b in zip(g, g[1:])]
    missing = [pieces(wild + list(m)) for m in colors]
    if sum(len(cs) - 1 for cs in missing) > 1:
        raise AssertionError("The graph and the placement counts disagree.")
    for cs in missing:
        if len(cs) == 2:
            wild.append(tuple(cs))
    if len(set(tuple(sorted(e)) for e in wild)) != len(wild) or any(
            len(pieces(wild + list(m))) != 1 for m in colors):
        raise AssertionError("The final edges failed the independent graph check.")
    return wild


def lean_certificate(colors, wild):
    def edges(es):
        return "[" + ", ".join(f"({a},{b})" for a, b in es) + "]"

    rows = ",\n  ".join(edges(m) for m in colors)
    return f"""import EdgeWalk
open EdgeWalk WildDeletion
namespace SuppliedK19
def colors : List (List (Edge 19)) := [
  {rows}]
def wild : List (Edge 19) := {edges(wild)}
theorem certificate : wild.length = {len(wild)} ∧ ∀ m ∈ colors, Connected (Adj (wild ++ m)) := by
  have h : colors.all (fun m => passes 0 (wild ++ m)) = true := by native_decide
  exact ⟨by decide, fun m hm => connected_of_passes 0 _ (List.all_eq_true.mp h m hm)⟩
#print axioms certificate
end SuppliedK19
"""


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("coloring", type=Path, nargs="?", help="JSON list of 19 lists of nine edges")
    parser.add_argument("--lean-out", type=Path, help="write a Lean path certificate for this coloring")
    args = parser.parse_args()
    edges = json.loads(args.coloring.read_text()) if args.coloring else round_robin()
    wild = solve(edges)
    if args.lean_out:
        args.lean_out.write_text(lean_certificate(edges, wild))
    print(json.dumps({"wild_count": len(wild), "edges": wild, "colors_connected": 19}, indent=2))
