# How many seven-point starts are available?

**At least 1,540 of the 5,005 seven-point sets through any chosen point contain at most two pairs of any color.** At least 875 also contain pairs from at least thirteen of the fifteen colors. These statements hold for every coloring. They apply when the chosen point is the extra point used to study a 15-point coloring.

For each seven-point set, let $x$ count colors absent inside it and let $y$ count colors with three pairs inside it. The other colors have one or two pairs. Since the seven points contain 21 edges, the numbers of colors with one and two pairs are $9-2x+y$ and $6+x-2y$. Their nonnegativity leaves only a short list of possible whole numbers $x,y$.

Let $I$ be 1 if $y=0$ and $x\le2$, and 0 otherwise. Let $J$ be 1 when $y=0$ and 0 otherwise. Checking the possible whole numbers gives

$$15I+17y+5\binom{x}{2}\ \ge\ 15+2xy+6\binom{y}{2},\qquad
7J+7y\ \ge\ 7+2\binom{y}{2}.$$

Sum over all seven-point sets through the chosen point. Each single color contributes to $y$ for 245 sets. For a fixed pair of colors let $U$ count sets in which both are absent, $V$ count sets in which one is absent and the other has three pairs, and $W$ count sets in which both have three pairs. Two perfect matchings form disjoint alternating even cycles of length at least four. Their lengths and the cycle containing the chosen point determine the counts, since relabeling within a cycle can take any point to the chosen one, interchanging the two colors if necessary.

| Alternating cycles, chosen point's cycle first | $U$ | $V$ | $W$ |
| --- | ---: | ---: | ---: |
| 16 | 28 | 56 | 7 |
| 4, 12 | 38 | 76 | 12 |
| 12, 4 | 34 | 68 | 10 |
| 6, 10 | 31 | 50 | 10 |
| 10, 6 | 29 | 54 | 8 |
| 8, 8 | 28 | 56 | 7 |
| 4, 4, 8 | 44 | 88 | 15 |
| 8, 4, 4 | 40 | 80 | 13 |
| 4, 6, 6 | 40 | 72 | 14 |
| 6, 4, 6 | 38 | 60 | 14 |
| 4, 4, 4, 4 | 56 | 112 | 21 |

Every row gives $2V+6W-5U\ge5$ and $W\ge7$. Summing these contributions over the 105 color pairs gives $15\sum I\ge15(5005)-17(15)(245)+105(5)=13,125$ and $7\sum J\ge7(5005)-7(15)(245)+2(105)(7)=10,780$. Division yields the two stated counts.

Lean checks the inequalities, all cyclic templates, and the final arithmetic. The classification by alternating cycles and the double count are the written steps. [Lean verification](SevenMoments.lean) · [What a seven-point start can prove](../k15/endgame/)
