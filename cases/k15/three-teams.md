# Three teams of five

**At least 2,400 groupings work** whenever the fifteen points can be split into teams A, B and C with the following property. Each color pairs four points of its own team, leaves one point there unmatched, and pairs all five points of the other two teams across. The individual pairings may vary freely subject to proper coloring. Adding an extra point to the fifteen and joining it to each color's unmatched point gives the same ten-line conclusion on sixteen points.

## How to draw the ten lines

Choose three points $T$ in A. The five colors belonging to C each send $T$ to a three-point set in B via their cross-team pairs. Pick any three points $U$ in B different from those images. At least five of the ten choices of $U$ are available.

Use the following five rows as triples. The numbers count how many points to take from each team. Of the three points in $T$, assign one to row 3 and the other two to row 5. Of the three in $U$, assign one to row 5 and the other two to row 3. Put the two B points outside $U$ into rows 1 and 2, in a fixed order. Finish by distributing C's points.

| Row | Points from A | Points from B | Points from C |
| --- | ---: | ---: | ---: |
| 1 | 0 | 1 | 2 |
| 2 | 0 | 1 | 2 |
| 3 | 1 | 2 | 0 |
| 4 | 2 | 0 | 1 |
| 5 | 2 | 1 | 0 |

There are nine ways to choose the single points in rows 3 and 5, then thirty ways to distribute C. At least **48 of these 270** choices work. In each successful row, draw two lines joining its three points. Since the rows are disjoint, that gives ten lines.

## Why at least 48 work

Call a set closed for a color if every point in it stays in the set under that color's pairing, letting the unmatched point stay in place. If a color disconnects the five rows, one or two entire rows form a closed set. The smaller side of any split of five rows has at most two rows.

For each color, count how often a row or pair of rows is closed among the 270 possibilities. The same failed layout can enter the count several times. The following bounds therefore give an upper bound on the number of failed layouts.

| Colors | What pays for closed sets | Maximum total |
| --- | --- | ---: |
| A | Each of the three pairs inside $T$ and each of the three unmatched points in $T$ contributes at most 18 | 108 |
| B | Each of the six pairs joining $U$ to its two outside points contributes at most 9 | 54 |
| C | Each of the five colors contributes at most 12 | 60 |

Each listed pair in A or B belongs to exactly one color, and each point is unmatched in just one color. To check the entries, label the five points of each team from left to right, putting $T$ and $U$ first. Lean generates every possibility for one color, all 270 layouts, and every cut made of one or two rows. It checks the indicated edge-by-edge prices and the C bound whenever the color does not send $T$ to $U$. Thus at most 222 layouts fail. [Lean checks](ThreeTeams.lean)

There are ten possible $T$ and at least five possible $U$ for each. A layout recovers them from rows 3 and 5, which have distinct team counts. The fixed order of the two B points distinguishes rows 1 and 2. Thus the $10\times5\times48=2{,}400$ successful layouts counted here are distinct.

The team reduction and the cut argument are given above. Lean verifies the exhaustive single-color bounds, the layout list, and the subtraction in the normalized model.
