# Four colors can force ten wild lines on sixteen points

**In either of the two patterns below, the remaining eleven colors can be drawn in any legal way. Every completion has wild number ten.** The choice of the point that stays untouched can depend on those eleven colors.

Label the sixteen points with the four-digit binary numbers from 0000 to 1111. Each of the four specified colors has a rule for finding the other endpoint of a line. Flipping a digit means changing 0 to 1 or 1 to 0.

| Pattern | What its four colors flip | Number of possible individual remaining colors |
| --- | --- | ---: |
| Four-dimensional cube | One color for each of the four digits. Its lines flip only that digit. | 187,249 |
| Two halves | The last digit, the next-to-last digit, both of those digits together, or the third digit from the right. Each color follows one rule. | 190,289 |

For the cube, the four neighbors of 0000 are 0001, 0010, 0100 and 1000. The same four rules apply at every point. Any renaming that produces the stated pattern is sufficient. For the second pattern only the first digit stays fixed along all four colors. Within each half its eight points consist of two complete four-point graphs joined by four lines.

## Why covering all eleven missing colors is possible

A candidate chooses one point to stand alone and divides the other fifteen into five groups of three. Two wild lines join the three points in each group. The certificate assigns weights to many such candidates. Every candidate passes the four known colors. For the remaining lines it chooses integer prices. For any possible next color, the total weight of the candidates it spoils is at most the sum of the prices of its eight lines.

| Pattern | Starting candidates before renaming | Renamings per start | Total candidate weight | Total line prices |
| --- | ---: | ---: | ---: | ---: |
| Four-dimensional cube | 13 | 384 | 3,840,000,768 | 3,806,375,520 |
| Two halves | 19 | 768 | 7,680,000,000 | 7,668,597,968 |

Each remaining line belongs to exactly one color. Adding the eleven color budgets therefore charges each price once. In both rows the total candidate weight exceeds the total price. At least one candidate connects every color. The general lower bound then gives exact value ten.

## How Lean checks the arithmetic

For a fixed candidate there are fifteen cuts. Five are a singleton together with one group. Ten are unions of two groups. A color can disconnect the candidate precisely by pairing all points of one cut internally. To see why these cuts suffice, take the side of a separation with fewer of the five groups. A lone singleton cannot be paired, and every closed side must have even size.

A matching that closes two distinct cuts also closes a third. Two four-point cuts intersect only in the singleton. A four-point cut and a six-point cut either intersect in three points or are disjoint. Two six-point cuts either intersect in three points or are disjoint. An intersection of two closed sides is itself closed, hence has even size. The only possible pair of distinct closed cuts is therefore disjoint. Their complement gives the third cut and the resulting pieces have sizes 4, 6 and 6. No further candidate cut can be closed. So the exact spoiled weight is the sum of the closed-cut frequencies minus twice the frequency of these three-piece separations.

Lean constructs the weighted candidates from the small tables, checks the four known colors, and enumerates every perfect matching of the unused lines by pairing the smallest remaining vertex with each permitted partner. It checks the exact inequality on each matching and verifies that the candidate weight exceeds the price total. The cut argument above connects the computations with the graph statement. [Lean checker](FourColors.lean) · [Cube starts](1-seeds.txt) · [Two-halves starts](0-seeds.txt) · [Replay instructions](../../../verification/)
