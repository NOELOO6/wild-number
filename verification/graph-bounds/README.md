# From a colored drawing to fourteen wild lines

For every minimum proper coloring of K19, the wild number is either 13 or 14. The theorem `thirteen_or_fourteen` starts with the colored edges. It ends with a list of distinct ordinary edges, paths for every color, and a proof that twelve edges cannot do this. The same method proves the eleven-line upper bounds for arbitrary K15 and K16 colorings. [Lean statements](Bounds.lean)

| Graph | Wild groups before the repair | Lines already drawn | Mean number of closed cuts, counting each color separately |
| --- | --- | ---: | ---: |
| K15 | Five groups of three | 10 | 315/143 |
| K16 | One lone point and five groups of three | 10 | 315/143 |
| K19 | Five groups of three and one group of four | 13 | 5019/2431 |

A **closed cut** means you can divide the wild groups into two nonempty sides and the chosen color puts no line between the sides. Count it once by taking the side away from a designated group. If the graph in that color is disconnected, at least one such cut exists.

Randomly put the points into the groups. For each color, a closed side consists of whole matching pairs and can include that color's unpaired point if it has one. Fix a side of size $s$ in the layout and a side of the same size in the matching. At most $s!(n-s)!$ placements line them up. Add these counts over the colors and possible sides. Each mean in the table is below three, so there is a placement with at most two closed cuts altogether. [Counting arbitrary permutations](UniformCuts.lean) · [Obtaining the color pairs from the original graph](ColorCoordinates.lean)

One new line can cross both cuts. If their selected sides overlap, join a point in the overlap to the designated group outside both. If they are disjoint, join one point from each. This keeps every earlier path available and crosses every remaining obstruction. Lean proves that every pair of points can then reach one another in each color. [Two-cut repair and graph paths](CutRepair.lean) · [Placing the wild lines](GraphLayouts.lean) · [Removing repeated edges](LegalEdges.lean)

Run `./verification/graph-bounds.sh` with Lean 4.19.0. The first run fetches the pinned mathlib release. To reuse an existing checkout, set `MATHLIB_DIR` to its absolute path. All numerical steps in these three graph bounds are checked by Lean's kernel with `decide +kernel`. The three printed dependency lists contain only `propext`, `Classical.choice`, and `Quot.sound`.
