# K36 has wild number 24

For every proper 35-coloring of the complete graph on 36 vertices, at least $10^{20}$ partitions into twelve triples pass every color cut. Choose any two edges forming a tree in each triple. Those 24 wild edges connect the graph in every color. The universal lower bound gives equality. Lean checks the counting argument and arithmetic in its ordinary kernel. [Graph theorem and partition count](Exact36.lean) · [Universal lower bound](../../verification/exact/UniversalLower.lean)

The possible smaller sides of a disconnected color have 6, 12 or 18 vertices. Each color is a perfect matching, so a closed union of triples has even size. For the 18-versus-18 split, counting the side that avoids a fixed vertex counts each cut once.

## Counting six-point failures

Call a six-set marked if some color closes it. Counting color labels gives $35\binom{18}{3}=28{,}560$ marks. Different colors can close the same set. Let $d$ be the difference between 28,560 and the number of distinct marked sets. In a given partition, make a graph on the twelve triples. Two triples are adjacent when their union is marked. If that graph has $r$ edges, the indicator of a six-point failure satisfies

$$
12\,\mathbf 1_{r>0}+5r(r-1)\ \le\ 12r+r(r-1)(r-2).
$$

For positive integers this follows from $(r-1)(r-3)(r-4)\ge0$. Counting ordered pairs and triples of distinct graph edges therefore gives an upper bound on partitions lost. [Overlap inequality](../sieve/OverlapCredit.lean) · [Moment bound](ShortMoment36.lean)

A given triple can have at most 80 neighbors. Its three internal edges have distinct colors. Each of the other 32 colors forces the entire neighboring triple. For each internal-edge color, the third vertex has a forced partner outside, and any of sixteen matching edges supplies the other two points. The proof also counts how many neighbors can contain each outside vertex. This gives a lower bound on pairs of neighbors disjoint from each other. [Color counts](TripleNeighbors36.lean) · [Neighbor intersections](WedgeCount36.lean)

Three distinct graph edges can be all separate, form an adjacent pair and a separate edge, form a path or star, or form a triangle. Their unions prescribe six, five, four or three triples of the layout. Counting completions with each shape gives the third moment. Repeated color labels are charged only to sets that can occur alongside them. [Shape classification](TripleMotifs36.lean) · [Counts for the five shapes](ChargeBounds36.lean) · [Repeated labels](Multiplicity36.lean)

## Counting larger cuts

A layout surviving the six-point test must avoid every marked six on both sides of a larger closed set. The complement of a closed twelve-set contains 24 points and is closed in the same color. It has at least 1,956 six-point marks counted with color labels. Bounds on their intersections give a second estimate for how many subdivisions of these 24 points can survive. Combining it with the single-color estimate is enough for every value of $d$. The proof adds the remaining losses from the 12- and 18-point cuts to the six-point loss. [24-point calculation](Region24.lean) · [Larger-cut bounds](LongCuts36.lean) · [Final inequality](Exact36.lean)

Run `./verification/graph-bounds.sh exact-k36` with Lean 4.19.0.
