# Alternating cycle conditions at K24, K30 and K36

Choose one color as an anchor. Its edges pair up the vertices. Together with any other color they form disjoint cycles alternating between the two colors. Count each cycle separately for each other color.

| Order | Sufficient condition on one anchor | Exact wild number |
| --- | --- | ---: |
| K24 | At most two or at least 105 alternating four-cycles in total | [16](CycleCounts24.lean) |
| K30 | No alternating four-cycle with any other color | [20](GraphCycles30.lean) |
| K36 | At most one alternating four-cycle in total | [24](Anchor36.lean) |

Each theorem applies to every minimum proper coloring with the stated cycle data. The unrestricted bounds at K24 and K30 are 16–17 and 20–21. A separate counting proof gives 24 at K36 for every minimum coloring. [General bounds](../one-extra/) · [Unrestricted K36](../k36/)

## Proof

Start with groups of three vertices arranged so that the anchor already connects all groups. Shuffle the anchor edges and independently exchange their endpoints. This gives one common random placement for all colors. For a color to fail, some union of groups must consist of whole edges of that color. The number of placements that can realize such a cut depends on how many anchor edges lie inside it, cross it or lie outside it. Summing the counts for all colors and all possible cuts gives a total smaller than the number of placements. At least one placement works. Drawing two wild edges per triple attains the general lower bound. [Placement count](PairFibers.lean) · [Paths in the ordinary graph](AnchoredGraph.lean)

At K30, if two disjoint pairs of groups are each closed, their union is also closed. Counting that union again overstates the number of losing placements. There are 630 choices of two disjoint pairs among the ten groups. Subtracting the simultaneous incidences gives a sufficient bound even if no companion forms a six-cycle. This includes every perfect one-factorization of K30, where each pair of colors forms a Hamiltonian cycle. The weighted bound also applies to some anchors that form four-cycles. [Pair count](PairCutCounts.lean) · [Weighted bound](NoFour30.lean)

Lean constructs alternating-cycle coordinates directly from the two matching involutions of the coloring. The K24 count and the K30 no-four-cycle condition can therefore be applied directly to the graph. At K24 each alternating square contributes four vertices of period two. [Square count](SquareVertices.lean) The other numerical bounds use a list of cycle lengths for each other color, in increasing order, and coordinates that identify the alternating edges with the edges of the supplied coloring. A length in the list counts anchor edges, so an entry of two represents a four-cycle. Lean proves that every such sorted list occurs in the enumeration and checks the numerical bound for every list required by the theorem. [Coordinates from a coloring](MatchingCycles.lean) · [Cycle lists and weighted bound](CycleLists.lean) · [Finite sums](MaskSum.lean)

Run `./verification/graph-bounds.sh anchored` with Lean 4.19.0. The finite counts use Lean’s native evaluator.
