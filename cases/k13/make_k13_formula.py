"""Regenerate the exact K13 nine-point obstruction formula using Python 3.10+."""
from itertools import combinations
from pathlib import Path

TRIPLES = [sum(1 << i for i in triple) for triple in combinations(range(9), 3)]


class Formula:
    def __init__(self):
        self.variables = len(TRIPLES)
        self.clauses = []

    def fresh(self):
        self.variables += 1
        return self.variables

    def bound_count(self, inputs, limit):
        """The jth output of a node is forced if at least j inputs are true."""
        if len(inputs) <= limit:
            return

        def totalizer(items):
            if len(items) == 1:
                return items
            middle = len(items) // 2
            left = totalizer(items[:middle])
            right = totalizer(items[middle:])
            out = [self.fresh() for _ in range(min(len(items), limit + 1))]
            for i in range(len(left) + 1):
                for j in range(len(right) + 1):
                    if not 1 <= i + j <= len(out):
                        continue
                    clause = []
                    if i:
                        clause.append(-left[i - 1])
                    if j:
                        clause.append(-right[j - 1])
                    self.clauses.append(clause + [out[i + j - 1]])
            return out

        self.clauses.append([-totalizer(inputs)[limit]])

    def lex_leader(self, u, v):
        """A lexicographically maximal relabeling beats this transposition."""
        previous = []
        for i, triple in enumerate(TRIPLES):
            if not triple & (1 << u) or triple & (1 << v):
                continue
            j = TRIPLES.index(triple ^ (1 << u) ^ (1 << v))
            if i >= j:
                raise ValueError("Triples must be in lexicographic order.")
            a, b = i + 1, j + 1
            self.clauses.append(previous + [a, -b])
            flag = self.fresh()
            self.clauses.append([-flag] + previous + [a])
            self.clauses.append([-flag] + previous + [-b])
            previous = [flag]

    def save(self, path):
        with path.open("w", encoding="ascii", newline="\n") as handle:
            print("p cnf", self.variables, len(self.clauses), file=handle)
            for clause in self.clauses:
                print(*clause, 0, file=handle)


def main(path, symmetry=True):
    cnf = Formula()
    for a, b, c in combinations(range(len(TRIPLES)), 3):
        if TRIPLES[a] | TRIPLES[b] | TRIPLES[c] == 511:
            cnf.clauses.append([a + 1, b + 1, c + 1])
    cnf.bound_count(list(range(1, 85)), 35)
    for subset in range(512):
        for size, required, limit in [(1, 1, 23), (4, 2, 30), (7, 3, 33)]:
            if subset.bit_count() == size:
                inputs = [i + 1 for i, triple in enumerate(TRIPLES)
                          if (triple & subset).bit_count() >= required]
                cnf.bound_count(inputs, limit)
    if symmetry:
        for u, v in combinations(range(9), 2):
            cnf.lex_leader(u, v)
    cnf.save(path)


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, nargs="?", default=Path("ninesym.cnf"))
    parser.add_argument("--without-symmetry", action="store_true")
    args = parser.parse_args()
    main(args.output, symmetry=not args.without_symmetry)
