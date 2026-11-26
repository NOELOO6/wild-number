"""Rebuild the nine-point formulas for the K15 and K16 endgame checks."""
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "k13"))
from make_k13_formula import Formula, TRIPLES


RULES_38 = [
    (1, (0, 1, 0, 0), 24),
    (4, (0, 0, 1, 1), 29),
    (7, (0, 0, 0, 1), 30),
    (1, (1, 0, 0, 0), 31),
]


def build(path, cap, rules):
    formula = Formula()
    for i, triple in enumerate(TRIPLES):
        for j, second in enumerate(TRIPLES[:i]):
            if triple & second:
                continue
            k = TRIPLES.index(511 ^ triple ^ second)
            if k < j:
                formula.clauses.append([k + 1, j + 1, i + 1])
    formula.bound_count(list(range(1, 85)), cap)
    for size, weights, limit in rules:
        for subset in range(512):
            if subset.bit_count() == size:
                inputs = [i + 1 for i, triple in enumerate(TRIPLES)
                          for _ in range(weights[(triple & subset).bit_count()])]
                formula.bound_count(inputs, limit)
    for a, b in combinations(range(9), 2):
        formula.lex_leader(a, b)
    formula.save(Path(path))


if __name__ == "__main__":
    build(sys.argv[1], 38, RULES_38)
