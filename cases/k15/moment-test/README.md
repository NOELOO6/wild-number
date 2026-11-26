# How far the K17 counting idea carries

K17 can be solved by counting single, double and triple failures. On K15, these three totals can miss the information we need even if we also know the total for four failures together. On K16 the first three totals can also miss it.

Consider the cyclic coloring on fifteen points. A grouping has five triples, each joined by two wild lines. For a grouping write $k$ for the number of colors that fail. Lean finds **103,452** groupings with $k=0$. The following two lists give different ways to distribute counts among the possible values of $k$.

| Failing colors $k$ | Actual K15 grouping count | Comparison count |
| ---: | ---: | ---: |
| 0 | 103,452 | 0 |
| 1 | 412,560 | 781,015 |
| 2 | 449,520 | 41,104 |
| 3 | 256,365 | 317,590 |
| 4 | 132,900 | 259,775 |
| 5 | 30,192 | 155 |
| 6 | 9,540 | 0 |
| 7 | 2,670 | 0 |
| 8 | 540 | 0 |
| 9 | 3,570 | 0 |
| 10, 11 | 0 | 0 |
| 12 | 0 | 1,761 |
| 13, 14 | 0 | 0 |
| 15 | 91 | 0 |

Both columns have the same sum. They also give the same totals if each row is multiplied by $k$, $k^2$, $k^3$ or $k^4$ before adding. In particular, they agree on the total number of groups of one, two, three or four failing colors, since $\binom{k}{d}$ is a polynomial of degree $d$. Yet the first row differs. Any bound using only these totals and nonnegative counts must allow zero successful groupings. The comparison column is an integer counting example. Whether a coloring could realize it is a separate question.

For K16, complete the cyclic coloring by adding its missing-color point. Allow any one of the sixteen points to be the untouched root. Of the 22,422,400 resulting layouts, 1,851,792 work. A second integer distribution has zero successes and agrees on the first three failure totals. Lean counts every root and checks both equalities of moments. [Counting algorithm](FailureCounts.lean) · [Lean theorems](CheckMoments.lean)

This explains a concrete difference between the cases. Any attempt to copy the K17 scalar counting step to these graphs needs additional information about the layouts or which colors fail together.
