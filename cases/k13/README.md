# Thirteen and fourteen points

**Nine wild lines suffice for every allowed coloring on thirteen points.** On fourteen points, deleting one vertex gives the thirteen-point case, and restoring it attaches it in each color. The known lower bound gives nine in both cases. [Three-page proof](../../reports/k13-wild-number.pdf)

The proof chooses four points and partitions the other nine into three triples. Each piece is connected by a chain of wild lines, using three plus two plus two plus two lines. The finite check rules out every way to block all of the possible partitions subject to the constraints proved in the report.

| Check | What it establishes |
| --- | --- |
| [Python enumeration](verify_k13.py) and [independent C++ enumeration](crosscheck_k13.cpp) | The nine-point obstruction search finds no counterexample. |
| [Formula generator](make_k13_formula.py) | Encodes the 280 partitions, concentration bounds and relabeling rules. |
| [Lean certificate](CertifiedNine.lean) | Proves that the supplied Boolean formula is unsatisfiable by checking its LRAT certificate. |
| [Runtime replay](Replay.lean) | Checks the same data by reading the two files at runtime. |

The reduction from arbitrary graph colorings to the Boolean formula is a written proof. The compressed formula and certificate are included in this directory. [Replay instructions](../../verification/) · [Earlier reduction and credit](https://raw.githubusercontent.com/1337isnot1337/solved-conjectures/main/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md)
