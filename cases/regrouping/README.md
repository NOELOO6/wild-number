# Round-robin constructions and local repairs

Every standard round-robin coloring of K<sub>n</sub>, n ≥ 3, has wild number ⌊4⌈n/2⌉/3⌋. At odd orders the vertices are residues modulo n and the edge between x and y has color x+y. To get the next even order, add a player whose opponent in each round is the player who previously had a bye. [Odd and even theorems in Lean](CyclicOrders.lean)

When n leaves remainder one or two on division by three, write n=3k+4 or n=3k+5. Take the k triples {3i, 3i+4, 3i+5} for 0 ≤ i < k, and put the remaining four or five vertices in one group. Join each group by a star. For example, on K₁₃ the triples are {0,4,5}, {3,7,8} and {6,10,11}. The last group is {1,2,9,12}.

For a fixed color c, its partner map reflects the labels by x ↦ c−x modulo n. A disconnected piece avoiding the last group would be a nonempty union of triples unchanged by this reflection. Each triple supplies one member of each residue class modulo three. The reflection acts separately on the intervals up to c and above c. It exchanges different pairs of residue classes on the two intervals, so their counts must agree on each interval. The entries in each class occur in the same order of triple indices, so the reflection splits no selected triple between the intervals. On either interval, the extreme endpoints of a nonempty collection of whole triples determine one center of reflection. The endpoints of residue class one require a different center. [Reflection lemma](Reflection.lean)

For every positive odd integer m, the standard round-robin coloring of K<sub>3m</sub> has wild number **2m**. Label the points from 0 to 3m − 1 and color each edge by the sum of its endpoints modulo 3m. Each row below specifies a repeating set of triples. Draw a chain of two wild edges in each triple. [Exact Lean theorem](RoundRobin.lean)

| Graph size n | Starting triples | How to repeat |
| --- | --- | --- |
| Odd multiple of 3 with 9 ∤ n | {0, 4, 5} | Add 3 modulo n to every entry, for n/3 translates. |
| Odd multiple of 9 | {0, 1, 6}, {3, 5, 11}, {4, 7, 8} | Add 9 modulo n to every entry, for n/9 translates of each triple. |

To see why the pattern repeats, follow one color edge from a point labeled x. It leads to c − x, where c is the color. At the point missing color c, this step stays in place. Two such steps, with a move inside a wild triple between them, cancel the dependence on c in the change of period. The proof supplies short paths that reach every type of triple and move ahead six periods in the first construction or two in the second. That step is coprime to the number of periods, so repeating it visits every period. The lower bound gives equality. Lean’s kernel checks the finite path lists and the theorem for arbitrary m. [Lifting argument](Periodic.lean) · [Path certificates](RoundRobin.lean)

## Choosing which triples to move

Suppose a layout consists of triples and the extra singleton used to complete an odd graph's colors to perfect matchings. Pick any two colors. One can merge exactly half of the groups, leaving the singleton untouched, and connect both colors. Every color already connected stays connected. [Lean theorem for arbitrary colorings](MergeColors.lean)

| Graph | Triples merged | Triples kept |
| --- | ---: | ---: |
| K9 | 2 | 1 |
| K15 | 3 | 2 |
| K21 | 4 | 3 |

In each color, every connected piece contains an even number of groups. Pair up the groups within each piece, once for each of the two colors. The two sets of pairs form alternating cycles. Choosing every other group in each cycle takes one from every pair and can exclude the singleton. Each piece now touches the proposed merge. Splitting the merged group into triples again is an additional requirement for the original wild-line budget. [Common bisection proof](CommonHalf.lean)

A balanced choice can still fail on K15. In the sparse example, start with {0,2,3}, {1,4,5}, {6,7,9}, {8,10,12}, {11,13,14}. Color 10 has two pieces. The last three triples meet each piece in exactly half its groups. Merging those triples connects every color. All 280 subsequent splits of those nine vertices fail. A different choice works by exchanging 5 and 7 between the second and third triples. [Checked cuts and paths](HalfTrap.lean)

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
