# Periodic triples and local repairs

For every positive odd integer m, the standard round-robin coloring of K<sub>3m</sub> has wild number **2m**. Label the points from 0 to 3m − 1 and color each edge by the sum of its endpoints modulo 3m. Each row below specifies a repeating set of triples. Draw a chain of two wild edges in each triple. [Exact Lean theorem](RoundRobin.lean)

| Graph size n | Starting triples | How to repeat |
| --- | --- | --- |
| Odd multiple of 3 with 9 ∤ n | {0, 4, 5} | Add 3 modulo n to every entry, for n/3 translates. |
| Odd multiple of 9 | {0, 1, 6}, {3, 5, 11}, {4, 7, 8} | Add 9 modulo n to every entry, for n/9 translates of each triple. |

To see why the pattern repeats, follow one color edge from a point labeled x. It leads to c − x, where c is the color. At the point missing color c, this step stays in place. Two such steps, with a move inside a wild triple between them, cancel the dependence on c in the change of period. The proof supplies short paths that reach every type of triple and move ahead six periods in the first construction or two in the second. That step is coprime to the number of periods, so repeating it visits every period. The lower bound gives equality. Lean’s kernel checks the finite path lists and the theorem for arbitrary m. [Lifting argument](Periodic.lean) · [Path certificates](RoundRobin.lean)

## What a redraw can repair

Remove the wild edges inside two chosen groups. Keep all other wild edges and one color. A proposed split of those points into two nonempty groups connects that color exactly when both conditions below hold.

1. Temporarily joining all the chosen points connects the graph.
2. A path through the fixed edges already connects two chosen points on opposite sides of the proposed split.

This gives a test for every color using the same proposed split. It applies to any number of points and to any symmetric fixed graph. [Lean equivalence](TwoGroups.lean)

| Starting grouping | Color cut off | First exchange | Second exchange |
| --- | ---: | --- | --- |
| K15 sparse example | 3 | 0 ↔ 3 | 0 ↔ 13 |
| K21 round-robin, colors labeled by endpoint sum | 5 | 0 ↔ 19 | 0 ↔ 10 |

For each displayed grouping exactly one color fails. Every single exchange of two points still leaves a color disconnected. The two exchanges shown restore every color. Lean checks the paths and separating sets for these particular drawings. [Starting triples and proofs](SwapExamples.lean) · [K15 coloring](../k15/six-point-trap/sparse-fifteen.txt)

For arbitrary minimum proper K21 colorings the general lower bound gives 14 and a separate Lean counting argument gives an upper bound of 15. Determining whether 14 always suffices remains open here. [Upper bound](Bounds21.lean) · [Lower bound](../../verification/exact/UniversalLower.lean)

Run `./verification/graph-bounds.sh regrouping` with Lean 4.19.0 to replay these results.
