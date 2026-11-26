# Nineteen points

**Every minimum proper coloring has wild number 13 or 14. For every coloring that repeats around a nineteen-point circle, the exact answer is 13. Thirteen also suffice after any eight colors in the standard round-robin drawing are redrawn.** The unrestricted question is whether a fourteenth line is ever necessary.

| Coloring | Guaranteed result | Check |
| --- | ---: | --- |
| Every proper nineteen-color assignment | Thirteen lines leave at most one color in two pieces. Fourteen lines connect everything. | [Thirteen-line graph theorem](one-piece/) · [Fourteen-line bound](../../verification/graph-bounds/Bounds.lean) |
| Every rotational assignment | Thirteen lines connect all nineteen colors. | [Exact graph theorem](ExactRotation.lean) · [Graph paths](EdgeWalk.lean) |
| Every proper redraw of eight standard round-robin colors | Thirteen lines connect all nineteen colors. | [Eight-color proof and counts](redraw/) |

## Where the fourteenth line comes from

Set aside one group of four points and five groups of three. Connect the points in each group in a chain. This uses three lines in the big group and two in each small group, for thirteen in total. For each color, count how many extra pieces remain. A connected graph scores zero. A graph in two pieces scores one.

Temporarily add a twentieth point. For each color, join this point to the ordinary point missing that color. Each color now pairs up all twenty points. The added point is a leaf when viewing any one color, so removing it leaves the same number of connected pieces. It forms its own group and has no wild edge.

Randomly assign the nineteen ordinary points to the six groups. For a fixed color, its pairing on the twenty slots is uniform. Each possible pairing comes from exactly $2^9 9!$ assignments. The partner of the temporary point is forced, and the other nine pairs can be labeled and oriented freely. Pair the first remaining endpoint. Pairing inside its component removes two available endpoints. Pairing into another component merges them. When a component runs out of endpoints, count it once. The following totals also have a separate Lean calculation. [Matching recurrence](MatchingCount.lean)

| Quantity for one color | Exact count |
| --- | ---: |
| Pairings on twenty slots | 654,729,075 |
| Connected pieces added over every pairing | 723,411,000 |
| Extra pieces added over every pairing | 68,681,925 |

The mean number of extra pieces **over all nineteen colors together** is $19\times68{,}681{,}925/654{,}729{,}075=2609/1309$. This is strictly below two. Some grouping therefore has at most one extra piece in total. If one remains, join its two sides with one ordinary wild edge. Every earlier path still works.

Twelve wild lines cannot suffice. A lone point has a missing color. A wild component of just two points is isolated in the color of the line between them. Thus all wild components need at least three points. Nineteen points can make at most six such components, and joining points into six components takes at least thirteen lines. Lean also proves the lower bound directly for arbitrary nineteen-point colorings. In the checked count, a point with one wild neighbor contributes two tokens to its incident line, and every other point contributes one token per incident line. Each point contributes at least two. A line cannot have two endpoints of degree one, so each line gets at most three. Thirty-eight tokens require at least thirteen lines. The general lower bound is Theorem 3.4 in the original paper. [Lean lower bound](LowerBound.lean) [Dawkins, Nappo, Tong and Zimbizi](https://arxiv.org/abs/2610.22142)

## How to find the grouping

Place points one at a time. For each color, a piece records its empty slots and the colored partners it is still waiting for. When the next point lands, it either opens a new colored edge or completes one. Completing an edge can merge two pieces. Each free slot offers one choice, shared by all nineteen colors.

The table gives a score for each of the 11,305 possible descriptions. At every step the scores of the possible next placements add to the current score, separately for every color. This identity holds even when different colors make different moves. Choosing a slot with the smallest combined score gives the guarantee above. The executable checks the final answer by traversing the actual graphs. [State definitions](Placement.lean) · [Checked table and averaging theorem](PlacementCertificate.lean) · [Counting actual slots by component](SlotBridge.lean) · [Adding and closing an actual edge](ComponentUpdate.lean) · [Constructor](construct.py)

For the round-robin example run `python3 cases/k19/construct.py`. To supply a coloring, pass a JSON file containing nineteen lists of nine edges on points 0 through 18. Add `--lean-out MyColoring.lean` to also produce a Lean theorem checking paths in all nineteen supplied colors. The replay builds and checks one such theorem. An output of fourteen alone gives an upper bound for that input.

## Thirteen on a circle

Number the points 0 through 18. Take the color missing at 0 as the first color. Its nine lines pair the other eighteen points and have nine different circular distances. All other colors are its rotations. Conversely these conditions generate a proper coloring, since the rotations of one edge fill precisely the edges of its distance. Numbering colors by their missing points justifies this description for any rotation that permutes the colors.

Lean enumerates every such starter in least-unpaired-point order. It finds 25,905 labeled starters. For each one it checks all nineteen colors with one of 43 layouts, using actual graph walks. The witness file contains one layout choice per starter. [Enumeration](Rotations.lean) · [All starters and graph theorem](CyclicCertificate.lean)

For a concrete example, pair point $i$ with $19-i$ for $i=1,\ldots,9$ and rotate. Draw the lines between consecutive points in each row below.

| Group | Points in chain order |
| --- | --- |
| Four points | 1, 4, 8, 10 |
| Three points | 13, 17, 18 |
| Three points | 0, 9, 15 |
| Three points | 2, 14, 16 |
| Three points | 3, 6, 11 |
| Three points | 5, 7, 12 |

## Verification scope

Lean proves the path statement for every normalized rotational starter, the independent matching totals, the placement theorem for every game satisfying its slot rules, and the one-edge path repair. A separate end-to-end Lean proof now shows that thirteen lines leave at most one extra piece in the original colored graph. It counts the ways to split six groups and turns the winning placement into paths. [Proof and exact counts](one-piece/) The unrestricted 13-or-14 bound has a separate, end-to-end Lean proof. It starts with an arbitrary colored graph, counts closed cuts, and constructs paths in each color after one repair. Its numerical checks run in the kernel. [Read the graph proof and replay it](../../verification/graph-bounds/). Run `./verification/replay.sh k19` for the rotation and placement checks.
