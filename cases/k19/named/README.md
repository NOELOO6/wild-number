# Choose two K19 colors before drawing thirteen lines

Name any two colors in any minimum proper coloring of K19. There are at least **26,638,742** ways to group the points so that the thirteen wild lines connect both named colors and at least sixteen others. If a color is left over, it has exactly two pieces. A different layout can be used for each pair of names.

| Colors named | What the grouping guarantees | Groupings, at least |
| ---: | --- | ---: |
| One | All but possibly one color connected, with at most two pieces in that color | 222,700,716 |
| Two | All but possibly one color connected | 136,689,976 |
| Two | All but possibly one color connected, with at most two pieces in that color | 26,638,742 |

The five triples and one group of four use thirteen wild lines. There are 5,431,826,400 groupings. Joining the last two pieces without increasing the number of lines remains open for arbitrary colorings. [A concrete two-line repair](../two-moves/)

## Count what two colors do together

For a color with $k$ connected pieces, let $X,Y,Z$ count the ways to divide the pieces into two, three and four nonempty sets. These are Stirling numbers of the second kind. Write $I$ for its failure indicator and $d=k-1$ for its number of extra pieces. The following bounds hold for every possible pair of component counts.

$$I\le X-2Y+6Z,\qquad d\le X-Y+2Z.$$
$$I_A I_B\ge X_A X_B-2Y_A X_B-2X_A Y_B,\qquad
I_A d_B\ge X_A X_B-2Y_A X_B-X_A Y_B.$$

The single-color split counts from the earlier graph proof give sums over groupings of $X,Y,Z$ equal to 590,234,400, 20,932,800 and 252,000. Thus a color fails on at most 549,880,800 groupings, and its total number of extra pieces is at most 569,805,600. [Single-color enumeration](../one-piece/) · [Inequalities and final bounds](Named19Bound.lean)

Add a twentieth point and join it to the vertex missing each color. Two colors are now two disjoint perfect matchings. Their alternating cycle lengths, with the cycle containing the new point listed first, give 22 cases. Alternating around the corresponding cycles takes any pair into its listed representative. Return to nineteen points for counting.

To count $X_A X_B$ or $Y_A X_B$, fix one division of the six blocks into two or three sets for A. Parts are ordered by the first block they contain. For B, specify a nonempty union of triples on the side excluding the group of four. Each division specifies the sizes of cells lying on each side of B and in each part for A. The B-side must be a union of B's nine pairs and singleton. Its shape determines how many of A's pairs lie inside, outside, or straddle it, and where A's singleton lies. Distribute these distinct pairs and the singleton among the required cells. Multiply by the factorials of the cell sizes to count placements. Each grouping has $4!(3!)^5 5!$ placements.

Across all 22 rows the resulting lower bounds are 50,380,208 on the sum of $I_A I_B$, and 52,111,724 on the sum of $I_A d_B$. The checker also interchanges the roles of the two matchings. [Counting recurrence](PairCuts19.lean) · [All 22 checks](PairRows19.lean)

## Make space for the second named color

For the two named colors let $x$ be the number that fail. Let $y$ be the total extra pieces in the other seventeen colors. Write $E=y$ if exactly one named color fails, and zero otherwise. The following score is at most four times the indicator that both named colors pass and the others together have at most one extra piece.

$$4-4x-2y+4\binom{x}{2}+xy+E.$$

For three distinct colors A, B and C we can exhibit at least 5,246,080 groupings on which A and C fail and B passes. Take a triple T containing the point missing A and one full A-edge, and a disjoint triple U containing the point missing C and one full C-edge. Omit the point missing B from both. Discard choices where B closes the six vertices together. T and U are isolated for A and C respectively. A completed grouping determines both triples uniquely since the missing points identify them.

The other thirteen vertices can be put into a group of four and three triples in 200,200 ways. Up to relabeling, the B-matching on these two chosen triples depends only on its numbers of edges within T, within U and between them. After these edges are placed, every remaining vertex of T or U is paired to a different outside vertex. The outside vertices left over form pairs and B's singleton. This gives the following exhaustive list.

| Within T | Within U | Between | Completions connecting B |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 186,192 |
| 0 | 0 | 1 | 187,360 |
| 0 | 0 | 2 | 177,600 |
| 0 | 1 | 0 | 173,808 |
| 0 | 1 | 1 | 177,600 |
| 1 | 0 | 0 | 173,808 |
| 1 | 0 | 1 | 177,600 |
| 1 | 1 | 0 | 152,640 |

Fix A, B and the point missing C. Give every possible C-edge $uv$ a weight equal to the sum of the relevant completion counts over all eligible choices of T, with U determined by $uv$. The integer certificate assigns each vertex a price. For each eligible edge, twice its weight is at least the sum of its endpoint prices. C pairs every vertex except its missing point, whose price is zero. Thus summing the inequalities gives at least 5,246,080 distinct groupings for **every** choice of C. The checker tests all 22 types for A and B and all seventeen choices for C's missing point. [Completion and price checker](Separate19.lean) · [Lean checks](SeparateRows19.lean) · [Vertex prices](vertex-prices.txt)

Apply this with A one of the named colors, B the other and C any of the seventeen. These 34 contributions give a valid lower bound for the sum of $E$. In one grouping exactly one named color can play A, and each counted C contributes at least one extra piece. Substituting the single, pair and three-color bounds into the score gives at least 26,638,742 good groupings. For the first two rows of the opening table, the simpler scores in the arithmetic file suffice.

Lean checks the pair tables, the 200,200 completions for each triple shape, every required price inequality and the summed arithmetic. The interpretation of the counting recurrences as graph incidences and the relabeling arguments are written above. The earlier theorem with an unrestricted choice of the exceptional color and the separate concrete two-line repair both have end-to-end graph proofs. Run `./verification/replay.sh last-colors` for the new tables and arithmetic.
