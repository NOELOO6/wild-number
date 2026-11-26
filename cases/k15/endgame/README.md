# Decide a 15-point or 16-point coloring from a seven-point start

**Ten wild lines work whenever the coloring has a start with a score of 38 or less.** You can calculate the score by looking at 21 lines on seven points. The other 99 lines may have any colors allowed by the puzzle.

## Try the test

On sixteen points, pick seven points and mark one of them as the root. On fifteen points, first add a sixteenth point. Join it to each old point using the unique color missing there. This new point must be the root. Each color now pairs up all sixteen points.

1. Choose seven points containing the root. Discard this choice if any color has three pairs inside the seven.
2. Split the other six points into two triples, A and B. Discard this split if one color pairs up all four points of either the root with A or the root with B.
3. Look at each color having **two** pairs inside the seven. Count it toward $h$ if one of the pairs touches the root. Count it toward $j$ if its four endpoints include two points of A and two points of B.
4. The score is $36+h+3j$. A score of 38 or less guarantees that this particular start can be finished. A higher score leaves this test inconclusive.

At least 1,540 choices through any specified root pass step 1. Existence of a choice passing all four steps is a separate question. [Seven-point counting proof](../../k16/seven-count.md)

## Why it works

The nine remaining points must be divided into three triples. Once we have five triples, draw two wild lines joining the points of each triple. On sixteen points the root stands alone. On fifteen points omit it. If one color cannot connect the result, it pairs up the root together with one triple, or it pairs up the six points of two triples. To see this, consider the connected pieces after contracting the triples. At least one side of a disconnection uses at most two of the five triples. Parity determines whether that side includes the root. The same disconnected cuts detect failure after deleting the root, whose only ordinary connection for this color was its matching edge.

Call a triple T of the remaining nine blocked for a color when the color pairs up one of the following sets.

| Set | Reason it matters |
| --- | --- |
| The root and T | T would be cut off |
| The other six of the nine | Two of the remaining triples would be cut off together |
| A and T | Two triples would be cut off together |
| B and T | Two triples would be cut off together |

The sets involving only the starting triples have already been checked. A partition of the nine into three unblocked triples therefore works.

Count a blocked triple once per color that blocks it. This total is exactly the score in step 4. For a single color, write $u$ for its number of blocked triples, $r$ for its number of root pairs inside the seven, $a,b$ for its numbers of pairs inside A and B, and $c$ for its number of A-to-B pairs. Its contribution satisfies $u+2r+c=3+2(a+b)+h+3j$. The finite matching check verifies this identity. Summing over the fifteen colors gives $36+h+3j$ because there are six root pairs, six pairs within the triples, and nine A-to-B pairs. [Lean matching check](../Endgame.lean)

If the score is at most 38, the individual matching checks also give the following limits on the set of distinct blocked triples. The proof assigns prices to the possible types of edges of a matching. Adding the prices over all colors counts each edge of the complete graph once. [Integer prices and certificate checks](../Endgame.lean)

| Count | Upper bound |
| --- | ---: |
| All blocked triples | 38 |
| Blocked triples containing any specified point | 24 |
| Blocked triples meeting any specified four points at least twice | 29 |
| Blocked triples entirely inside any specified seven points | 30 |
| Blocked triples avoiding any specified point | 31 |

There are 84 triples on nine points and 280 ways to divide the points into three triples. A set obeying those five limits cannot hit every division. The Boolean formula asks for precisely such a set hitting them all. Its 36 relabeling conditions are valid because the lexicographically largest labeling of any putative example satisfies all of them. Lean accepts an LRAT certificate that this formula is impossible. [Formula generator](make_formula.py) · [Lean certificate theorem](CertifiedEndgame.lean)

The reduction from the graph to blocked triples, the use of permutations to represent matching types, and the interpretation of the formula are written arguments. Lean checks the matching arithmetic and the exact generated formula. Run `./verification/replay.sh k15` from the repository root.

## A score of 40 that always works

Here is a specific seven-point start with root 0, A = {2, 4, 5} and B = {1, 3, 6}. In the table, 3–4 means the line between points 3 and 4. The color names can be changed freely. These 21 lines are the entire hypothesis on the coloring.

| Color | Pairs inside the seven | Color | Pairs inside the seven | Color | Pairs inside the seven |
| ---: | --- | ---: | --- | ---: | --- |
| 1 | 3–4 | 6 | 0–1, 2–5 | 11 | 0–4, 3–5 |
| 2 | 1–6 | 7 | 1–3, 4–6 | 12 | 0–6, 1–2 |
| 3 | 1–4 | 8 | 0–3 | 13 | 2–3 |
| 4 | 0–2 | 9 | 1–5, 2–4 | 14 | 3–6 |
| 5 | 0–5, 2–6 | 10 | 4–5 | 15 | 5–6 |

**Every legal completion of this table admits ten wild lines using these two starting triples.** The fifteen colors contribute exactly 40 occurrences of blocked triples. For these specific pairs, the seven integer price rules in the proof limit how concentrated those occurrences can be. Each of the possible obstructions violates at least one rule. [Matching bounds](../Endgame.lean) · [Lean exclusion of all candidates](Completion.lean)

## How the nine-point catalogue was checked

A **blocker** is a collection of triples that meets every division of the nine points into three triples. Removing redundant triples from a blocker leaves a minimal blocker. Every blocker of size at most 43 contains, up to a permutation of the points, one of the 899 entries below. Each entry hits all 280 divisions and removing any one of its triples spoils that property.

| Number of triples | Catalogue entries |
| ---: | ---: |
| 28 | 1 |
| 29–33 | 0 |
| 34 | 1 |
| 35 | 2 |
| 36 | 0 |
| 37 | 17 |
| 38 | 5 |
| 39 | 17 |
| 40 | 46 |
| 41 | 48 |
| 42 | 148 |
| 43 | 614 |

To check coverage, mark a point belonging to as many triples as possible. The triples using it give an ordinary graph on the other eight points. Each triple belongs to ten divisions, so a blocker needs at least 28 triples and its busiest point belongs to at least ten. The checker builds the possible graphs on eight points by adding a vertex and checking a relabeling certificate for every possible neighborhood.

The remaining triples form a vertex-cover problem. If two disjoint triples on the eight points leave a pair missing from the marked point's graph, at least one of the two triples must be selected. For a selected triple the search spends one unit of its budget. If that triple is excluded, the search must spend one unit for each of its outstanding neighbors. A collection of disjoint requirements gives a lower bound on the remaining budget. The checker also uses the maximum degree of the chosen point. Every accepted leaf either exceeds a bound or contains a displayed blocker under an explicitly checked permutation. The four-point and seven-point caps used here equal the total number of possible triples of the relevant kinds, so they place no extra restriction on the input.

The Lean program checks 12,346 eight-point graph representatives. The search certificate has 643,134 nodes and 42,492 leaves with an explicit contained blocker. Native evaluation is part of the trust base. The correspondence between this search and graph relabelings is explained above. [Lean tree checker](BlockCatalogue.lean) · [Minimality checks](Completion.lean) · [Download the 899 entries](cert43.blocks.gz)

Each downloaded row lists the triples as nine-bit integers. For example, 7 stands for points 0, 1 and 2 because $7=2^0+2^1+2^2$.
