# Ten wild edges for every Steiner coloring of K15

In a Steiner triple system every pair of points lies on exactly one three-point line. Color the edge between two points by the color missing at the third point on their line. Every such coloring of K15 has wild number **10**. For any two named colors, the same ten edges work after every proper recoloring of that pair. The same holds for any minimum coloring of K16 with a vertex whose deletion yields a Steiner coloring. [Definition](../../../verification/exact/SteinerSystem.lean) · [Exact graph theorems](Steiner15.lean)

Choose one line and label it 0, 1, 2. The lines through 0 pair up the other twelve points. The lines through 1 give a second matching with no common edge. Their union has alternating cycles. Counting edges of the first matching on each cycle gives the following four possibilities. The counts are completions with these fixed coordinates. Isomorphic systems can occur several times. [Normalization](SteinerCoordinates.lean)

| Cycle half-lengths | Completions |
| --- | ---: |
| 6 | 72,776 |
| 2, 4 | 78,800 |
| 3, 3 | 65,088 |
| 2, 2, 2 | 95,808 |

The search chooses an uncovered pair and branches over its available third points. Lean proves that every actual Steiner system follows a branch. At a leaf, the checker uses a list of 66 partitions into five triples. On each cut, one vertex has its two named incident edges across the cut. Those two edges retain different colors under every proper redraw. All fifteen colors must cross every nonempty union of whole triples that omits point 0. Two edges drawn within each triple then connect the graph in every color. The universal lower bound gives equality. [Coverage proof](SteinerSystems.lean) · [Partitions and cuts](SteinerLayouts.lean) · [Finite check](SteinerCheck.lean)

Run `./verification/graph-bounds.sh steiner-k15` with Lean 4.19.0. The finite search uses Lean’s native evaluator.

## Three named colors in the projective example

On the fifteen nonzero vectors of the four-dimensional binary vector space, choose the three colors on one projective line. For every fixed set of ten wild edges, some proper recoloring of these three colors defeats it. A single set of eleven wild edges works for all such recolorings. Thus the minimum **common** witness for this family has eleven edges. An individual recoloring can have its own witness. The lower bound uses parity on the four components of the three-color subgraph. The upper bound constructs a common partition into four connected blocks and checks the crossings of all its cuts. [Both Lean proofs](SteinerParity.lean)
