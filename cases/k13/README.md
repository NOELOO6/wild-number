# Thirteen and fourteen points

**Nine wild lines suffice for every allowed coloring on thirteen points.** On fourteen points, deleting one vertex gives the thirteen-point case, and restoring it attaches it in each color. The known lower bound gives nine in both cases. [Three-page proof](../../reports/k13-wild-number.pdf)

The proof chooses four points and partitions the other nine into three triples. Each piece is connected by a chain of wild lines, using three plus two plus two plus two lines. The finite check rules out every way to block all of the possible partitions subject to the constraints proved in the report.

| Check | What it establishes |
| --- | --- |
| [Python enumeration](verify_k13.py) and [independent C++ enumeration](crosscheck_k13.cpp) | The nine-point obstruction search finds no counterexample. |
| [Formula generator](make_k13_formula.py) | Encodes the 280 partitions, concentration bounds and relabeling rules. |
| [Lean certificate](CertifiedNine.lean) | Proves that the supplied Boolean formula is unsatisfiable by checking its LRAT certificate. |
| [Runtime replay](Replay.lean) | Checks the same data by reading the two files at runtime. |

Run `./verification/graph-bounds.sh exact-k13` from the repository root to check the theorem for arbitrary colorings of K13 and K14. The replay constructs the four-point set, proves the restrictions on the blocked triples, checks a symmetry-free SAT certificate, converts a surviving partition into actual paths, and proves the lower bound. The theorem uses Lean’s native evaluator for finite computations. [Exact theorem](../../verification/exact/K13K14.lean) · [Replay instructions](../../verification/)

The original nine-point reduction is credited to an earlier investigation. The report and the Lean formalization in this repository build on that reduction. [Earlier reduction](https://raw.githubusercontent.com/1337isnot1337/solved-conjectures/main/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md)
