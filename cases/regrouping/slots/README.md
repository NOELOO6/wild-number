# Reassigning movable points

Fix some wild edges, choose d movable points and choose d destinations. A move joins each point to a different destination, using one wild edge per point. A *palette* is a set of colors that must all be connected by the same move. Different palettes may use different moves. [Drawing and connectivity definitions](SlotCuts.lean)

## A general bound

For d ≥ 3, if every palette of at most **C(d) − 1** colors has a move, then one move connects every color. Here C(d) = binom(2d, d)/(d + 1) is the d-th Catalan number. The statement holds for every graph order and every fixed choice of movable points and destinations. [Closed-form theorem on ordinary colored complete graphs](CatalanBound.lean)

| Movable points | Possible moves | Colors sufficient to witness failure | Sharpness |
| ---: | ---: | ---: | --- |
| 2 | 2 | 2 | |
| 3 | 6 | 4 | Four are necessary on K9, K19, K21 and K23 |
| 4 | 24 | 13 | Thirteen are necessary at every order from K13 through K24 |
| 5 | 120 | 41 | Up to 23 are necessary in the examples below |
| 6 | 720 | 131 | |

A failed move leaves a cut with no edge of the failed color or of the drawing crossing it. Label each movable point and each destination by its side of the cut. The cut survives precisely when the move pairs equal labels throughout. In a smallest collection of blocking cuts, each cut has a move that survives all the others. This makes the cut indicators linearly independent. Rearranging three destinations in decreasing order gives a linear relation, so their values are determined by the permutations with no decreasing triple. Encoding those permutations as balanced paths gives the Catalan bound. When two blocking cuts rule out the same move, the constant function gives one additional independent row. Disjoint blocking cuts satisfy a separate, smaller bound. [Cuts and smallest witnesses](PaletteBound.lean) · [Linear independence](CutRank.lean) · [Three-destination identity](DecreasingTriples.lean) · [Overlapping and disjoint cuts](PaletteSizes.lean) · [Balanced-path proof](CatalanBound.lean)

## How to choose a move

For three points, first check that every component of each color, together with the fixed edges, contains a chosen point or destination. Then draw a three-by-three table. Allow a point and destination in a cell if, for every color, there is a path using that color and the fixed edges from one of these two endpoints to one of the other four. A move works exactly when all three of its cells are allowed. A missing matching on this board is witnessed by a missing row, column or two-by-two square. [Three-point rule](ThreeSlots.lean) · [Four-color proof](FourColors.lean)

In the previously checked K21 example every single swap fails from the specified start, even with a free choice of the split on the original six vertices. Freeing points 0, 8 and 18 gives the following table. The destination is a vertex in the named point’s original group. Both cyclic moves work and each spends exactly 14 wild edges. [Original obstruction](../../one-extra/Exchange21.lean) · [Table and two repairs](SlotCases.lean)

| Point | Destination 3 | Destination 6 | Destination 19 |
| ---: | :---: | :---: | :---: |
| 0 | — | ✓ | ✓ |
| 8 | ✓ | — | ✓ |
| 18 | ✓ | ✓ | — |

For more points, test every subset of at most half the movable points. A subset test temporarily allows every link from that subset to its assigned destinations, and every link from the remaining points to the remaining destinations. All colors must be connected in the temporary graph. With five points the exact test uses five singletons and ten pairs per proposed move. [Subset test and five-point theorem](SmallSides.lean)

## At the conjectured line count

Each row below gives explicit minimum proper colorings. In the four-point examples, thirteen designated colors block every move. Every palette omitting even one designated color works. In the five-point examples **every proper subset of the entire palette works**, although all 120 moves fail on the full palette. All 25 singleton tests pass for every color, so for each move a pair of points witnesses its failure. For each designated color there is a move that leaves just that color disconnected, in exactly two pieces. Each example also has a drawing at the same budget that connects all colors when other points can move. [Four-point examples](QuartetCases.lean) · [Five-point examples](QuintetCases.lean) · [Paths, cuts and palette characterization](ReassignmentCheck.lean)

| Orders | Wild edges | Colors needed to block four points | Colors needed to block five points |
| --- | ---: | ---: | ---: |
| K13, K14 | 9 | 13 | |
| K15, K16 | 10 | 13 | 15 |
| K17, K18 | 12 | 13 | 17 |
| K19, K20 | 13 | 13 | 19 |
| K21, K22 | 14 | 13 | 21 |
| K23, K24 | 16 | 13 | 23 |

### Changing the five-point start

In the K15 example, points 0–4 can move and the fixed pairs are {5,6}, {7,8}, {9,10}, {11,12} and {13,14}. Exchange one movable point with one member of a pair, then reassign the five movable points. **49 of the 50 exchanges admit a ten-line repair.** Exchanging 1 with 13 is the only failure. The same check on the larger odd examples allows an exchange with any member of one of the five destination groups. [Exchanges and exact counts](OneReplacement.lean)

| Coloring | Exchanges tested | Exchanges admitting a repair |
| --- | ---: | ---: |
| K15 | 50 | 49 |
| K17 | 60 | 60 |
| K19 | 55 | 50 |
| K21 | 50 | 50 |
| K23 | 60 | 60 |

On this K15 coloring, an exhaustive check of all 1,401,400 partitions into five triples finds **125,412** successful groupings and **1,275,988** failures. Each success is checked by paths and each failure by a separating set. [Full count for the supplied coloring](Count15.lean)

The unrestricted problem still requires a choice of fixed edges and movable points that works for every input coloring. These specific colorings attain the conjectured wild number. [Status by graph size](../../../README.md#results-by-graph-size)

## Verification

From the repository root, run `./verification/graph-bounds.sh slots` with Lean 4.19.0. Add `--count-k15` to replay the full count of K15 groupings. The ordinary Lean kernel verifies the universal theorems, including the Catalan formula. The explicit examples use Lean’s native evaluator to check the coloring, wild-edge budget, paths and separating cuts. Each coloring table is indexed by vertex, with labels starting at zero. Deleting its final vertex gives the preceding odd order. [Coloring tables](colorings/) · [Replay guide](../../../verification/)
