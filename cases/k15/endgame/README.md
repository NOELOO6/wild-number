# Decide a 15-point or 16-point coloring from a seven-point start

**Ten wild lines work whenever the coloring has a start with a score of 38 or less.** You can calculate the score by looking at 21 lines on seven points. The other 99 lines may have any colors allowed by the puzzle.

## Try the test

On sixteen points, pick seven points and mark one of them as the root. On fifteen points, first add a sixteenth point. Join it to each old point using the unique color missing there. This new point must be the root. Each color now pairs up all sixteen points.

1. Choose seven points containing the root. Discard this choice if any color has three pairs inside the seven.
2. Split the other six points into two triples, A and B. Discard this split if one color pairs up all four points of either the root with A or the root with B.
3. Look at each color having **two** pairs inside the seven. Count it toward $h$ if one of the pairs touches the root. Count it toward $j$ if its four endpoints include two points of A and two points of B.
4. The score is $36+h+3j$. A score of 38 or less guarantees that this particular start can be finished. A higher score leaves this test inconclusive.

At least 1,330 choices through any specified root pass step 1. Existence of a choice passing all four steps is a separate question. [Seven-point counting proof](../../k16/SevenSet.lean)

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
