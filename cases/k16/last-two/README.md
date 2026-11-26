# Can the last two colors spoil everything?

Choose any thirteen colors in any minimum proper coloring of K16. Split the points into five triples and one singleton. Draw two wild lines joining each triple. The following counts are lower bounds on distinct groupings.

| What the ten lines connect | Groupings guaranteed |
| --- | ---: |
| All thirteen colors you named | 449,107 |
| Those thirteen and at least one of the two others | 8,527 |

There are fifteen ways to specify a list of fourteen colors. For **at least fourteen of those lists**, at least **4,264** groupings connect the whole list. Otherwise two lists would each have at most 4,263, and their union could not account for 8,527. [Lean corollary](Fourteen.lean)

The earlier guarantee was 120,835 for the first row. If eleven lines really are necessary somewhere, then for any pair of colors A and B there are at least 8,527 groupings where just A or just B fails. At most one color can never occur as the sole failure. The case in which A and B take turns preventing a full win is open.

## What happens in one actual coloring

Leave out colors 0 and 4 in the repository's search example. These four rows account for every grouping that connects the thirteen named colors.

| Color 0 | Color 4 | Groupings |
| --- | --- | ---: |
| Connected | Connected | 1,731,000 |
| Disconnected | Connected | 393,550 |
| Connected | Disconnected | 393,550 |
| Disconnected | Disconnected | 75,521 |
| **Total** | | **2,593,621** |

Here the two outside colors really do spoil 862,621 candidates. Counting only 120,835 candidates would have left the outcome unclear. [Lean enumeration](PrefixExample.lean) · [Actual coloring](../../../examples/search-coloring.json)

## Counting the thirteen named colors

A color fails exactly when some pair of blocks is closed under its matching. A closed set has even size, so it contains an even number of odd-sized blocks. Any proper nonempty closed side or its complement therefore has two blocks. If two distinct block pairs are closed, their intersection cannot be a single odd block. They are disjoint, and their complement is the third closed pair. Lean proves both facts for actual graph paths and any placement of the sixteen points. [Graph theorem](GraphCuts.lean)

For a grouping with $k$ named failures, start with $1-k$ and return $2/k$ for each pair of failing named colors. This gives one when no color fails and zero otherwise. We lower-bound the return with integer prices for each pair and the other matchings. The recorded features and the cancellation of the three transfers per triple follow the earlier fixed-root argument. Here the singleton ranges over all sixteen points, the named set has size thirteen and the prices are new. Every one of the 78 named pairs contributes at least 229,757,771,206 after scaling by a million. There are 22,422,400 groupings and each named color fails 3,068,800 times. The resulting lower bound rounds up to 449,107. [Weighted counting method](../../k15/prescribed/) · [New prices](free-tangent.txt) · [All seven rows](LastTwoRows.lean)

## How many candidates lose both remaining colors?

The edges of the two outside colors form disjoint alternating cycles. Walking around the cycles relabels any pair of colors into one of the seven rows. The third column gives groupings where both outside colors fail **and** at least one of the thirteen named colors fails. Those groupings were already excluded when counting the candidates.

| Outside cycle lengths | Both outside colors fail | Already excluded, at least | Both fail among the candidates, at most |
| --- | ---: | ---: | ---: |
| 16 | 375,808 | 37,952 | 337,856 |
| 4, 12 | 420,352 | 44,224 | 376,128 |
| 6, 10 | 390,280 | 40,316 | 349,964 |
| 8, 8 | 375,296 | 37,952 | 337,344 |
| 4, 4, 8 | 464,576 | 49,608 | 414,968 |
| 4, 6, 6 | 450,448 | 47,472 | 402,976 |
| 4, 4, 4, 4 | 553,600 | 113,020 | 440,580 |

In the first six rows every possible third color supplies the displayed overlap. In the last row choose a third color M from the thirteen. There are 673,601 possible matchings for M. The checker covers them using 169 representatives and relabelings that preserve the pair of outside colors. For each representative, either M alone excludes enough groupings, or the certificate supplies a particular unused edge. The color N containing that edge also belongs to the thirteen. The checker tests every possible N and finds at least 113,020 groupings excluded by M or N. It upper-bounds their overlap by counting all the closed cuts witnessed by N in the layouts already excluded by M. Subtracting the last column's largest entry from 449,107 leaves 8,527. [Four-square checker](SquarePair.lean) · [Orbit and witness checks](SquareRows.lean) · [Final inequalities](LastTwoBound.lean)

Lean verifies the graph cut criterion, finite tables, orbit coverage, bounds on the returns and final arithmetic. The relabeling of an arbitrary coloring into the pair rows, the interpretation of the mask enumeration and the summing of the pair accounts for that coloring are written parts of the proof. Replay the tables with `./verification/replay.sh last-colors` and the graph lemmas with `./verification/graph-bounds.sh last-colors`.
