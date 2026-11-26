# Thirteen lines leave at most one color unfinished

**Start with any proper nineteen-color drawing on nineteen points. There is a choice of thirteen wild lines that connects at least eighteen colors. If a color is still disconnected, it has exactly two pieces.** Lean proves this from the original colored edges. [Graph theorem](LastPiece.lean)

Put the points in five groups of three and one group of four. Join every point in a group to its first point. This uses $5\times2+3=13$ wild lines. For each color, count its pieces and subtract one. A connected color scores zero. A color in two pieces scores one.

The proof averages this score over every possible placement of the points. It is enough to show that the average for all nineteen colors together is less than two. At least one placement then scores zero or one, since the scores are whole numbers.

## What Lean counts

For one color, split the six groups into two, three, or four nonempty sets. Count a split when every edge of this color stays within one set. The table counts all such combinations of a split and a placement. Each ordering of the nineteen points counts once.

| Sets in the split | Count |
| ---: | ---: |
| Two | 13,218,228,559,872,000 |
| Three | 468,787,544,064,000 |
| Four | 5,643,509,760,000 |

Add the first count, subtract the second, then add twice the third. This bounds the sum of the one-color scores. For example, if a color has three pieces, it allows three splits into two sets and one split into three sets. It contributes $3-1=2$, exactly its two extra pieces. Lean checks the inequality for every partition of the six groups.

Every color consists of nine pairs and one point missing that color. A split is counted by assigning each pair and the single point to its set, then counting the ways to put named points into those positions. Relabeling a color preserves the total over all placements. After multiplying by nineteen and dividing by the number of placements, the average total score is at most $2609/1309$, just below two.

| Part of the argument | Lean source |
| --- | --- |
| Count permutations with prescribed labels | [Fiber counts](FiberMass.lean) |
| Assign pairs and the singleton to sets | [Counting recurrence](BinMass.lean) |
| Join groups along colored edges | [Group merges](GroupMerges.lean) |
| Check every possible division into pieces | [Partition inequality](PartitionCounts.lean) |
| Check the numerical table | [Exact counts](PieceTotals.lean) |
| Choose a placement shared by all colors | [Averaging](SmallAverage.lean) · [Nineteen-color bound](PieceBudget.lean) |
| Turn a shared group label into a path between actual points | [Paths and thirteen distinct lines](PiecePaths.lean) · [Final theorem](LastPiece.lean) |

Run `./verification/graph-bounds.sh pieces` from the repository root. The proof uses Lean's native evaluator for finite tables. If the last color needs a joining line, the resulting fourteen lines work for every color. The question of whether thirteen always suffice is open in this project.
