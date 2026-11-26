# Pick nine colors to keep connected

Take any minimum proper coloring of K15 and name any nine colors. At least **666** groupings into five triples give ten wild lines that connect all nine named colors and at least five of the six others. Draw two lines in each triple. This improves the earlier guarantee of four colors that you could name in advance.

If a coloring needs eleven lines, look at its ten-line choices that miss just one color. There must be at least ten different possibilities for that missing color. Otherwise you could protect all of them by naming nine colors.

## How the count works

Complete the coloring on sixteen points by adding the missing-color point. Keep that point as the singleton. There are 1,401,400 groupings, and a given color fails on 191,800 of them. A color fails when it closes a pair of blocks. [General graph lemma](../../k16/last-two/GraphCuts.lean) · [Counting setup](../prescribed/)

For each grouping let $x$ be the number of named failures and $y$ the number of other failures. Its target score is one when $x=0$ and $y\le1$, and zero otherwise. Give each grouping a base score of one million plus a linear correction in $x$ and $y$. Add a correction for pairs of failures, which also depends on how many other colors failed. The eleven coefficients are the first line of the certificate. Lean checks the score is at most one million times the target for all seventy choices of $x,y$. [Score definitions](NineNamed.lean) · [Pointwise and summed inequalities](NineBound.lean)

There are 36 pairs of named colors, 54 mixed pairs and 15 pairs of other colors. For each category and each of the eleven possible cycle types, enumerate every disjoint third matching. If $T$ groupings fail all three matchings, the checker verifies
$$-cT \le \text{sum of the third matching's edge prices}+\text{offset}+\text{transfer}.$$
Here $c$ depends on the categories of the pair and the third color. Each remaining edge is used once across the thirteen other colors. The three transfers for any triple have a nonpositive sum. Thus the minimum gain per pair, after subtracting the edge prices and offsets, gives a lower bound on the total correction.

| Pair | Minimum gain, scaled by one million |
| --- | ---: |
| Both named | 119,975,001,749 |
| One named | −31,157,095,571 |
| Neither named | −120,008,954,672 |

The resulting score is at least 665,814,250. Dividing by a million and rounding up gives 666. Lean checks the matching tables, transfer inequalities, polynomial and arithmetic. Relabeling a coloring into its pair rows and translating the row sums into the graph count use the written counting argument. [Integer witness](nine-prices.txt) · [Eleven checked rows](NineRows.lean)

Run `./verification/replay.sh last-colors` from the repository root.
