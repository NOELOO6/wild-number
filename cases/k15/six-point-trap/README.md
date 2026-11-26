# What happened to the last 19 groupings?

**All 2,800 can fail.** Two examples below defeat every grouping that keeps points 0 through 5 in two triples. Both have many ways to connect all fifteen colors with ten wild lines once the points can mix freely. The question for an arbitrary K15 coloring remains open.

| Coloring | Colors breaking the seven-point rule | Wins out of 2,800 | Wins out of all 1,401,400 |
| --- | ---: | ---: | ---: |
| Original 19-survivor coloring | 0 | 19 | 120,241 |
| Change three colors of the original | 0 | 81, all different from the original 19 | 117,194 |
| First example defeating all 2,800 | 3 | 0 | 127,413 |
| Second example defeating all 2,800 | 2 | 0 | 120,345 |

The seven-point rule uses the chosen six points and an extra point. Join that extra point to each old point in the color missing there. The rule says that each color has at most two lines entirely among those seven points. The strict question is whether all 2,800 can fail while this rule holds. The two zeros leave that question open.

## The seven-point rule

With the original 36 outside lines and nine outside missing colors fixed, changing all 69 ordinary lines touching the six points still leaves a winner. Allowing the outside lines to change as well gives a strict example with 15 winners. The broader search with the outside lines fixed covers 243,143 other choices of outside missing colors. [Results, examples and Lean proofs](../seven-point/)

## How one exchange wins

In the first zero example, the following grouping loses. Exchange **3 and 9** between two triples. The new grouping connects all fifteen colors. In each triple, draw a wild line from the first point to the second and from the second to the third.

| | First triple | Second | Third | Fourth | Fifth |
| --- | --- | --- | --- | --- | --- |
| Before | 0, 1, 2 | **3**, 4, 5 | 6, 7, 8 | **9**, 12, 14 | 10, 11, 13 |
| After | 0, 1, 2 | 4, 5, **9** | 6, 7, 8 | **3**, 12, 14 | 10, 11, 13 |

In both zero examples, every color has a line going from the marked six to somewhere else. The first example also has four initial splits that pass the check on the two inside triples alone. The second has two. In each case all their outside completions still lose. [First coloring](coloring.txt) · [Exchange and cuts](SixTrap.lean) · [First full count](SixTrapCounts.lean) · [Second coloring](two-exceptions.txt) · [Second full count](TwoExceptions.lean)

## What can change under the seven-point rule?

**Exactly three colors are enough to eliminate the original 19.** Changing colors 3, 5 and 14 makes every one of those 19 lose. It also creates 81 different winners. Any redraw confined to two colors keeps at least ten of the original winners if it respects the seven-point rule. With the rule lifted, every two-color redraw still leaves at least three of the original winners. To see why the check covers every redraw, follow the two colors around the drawing with the extra point included. They form loops of even length. Each loop can keep its colors or exchange them. Lean tests all these choices for all 105 pairs of colors. [Three changed rows](three-color-change.txt) · [Lean graph checks](LastNineteen.lean) · [All two-color choices](TwoColors.lean)

**Keeping the lines at the original six points forces at least 19 wins.** Leave the colors of every ordinary line touching points 0 through 5 as they were in the original drawing. Recolor the 36 lines among the other nine points in any way that completes a proper coloring. There are **3,725,456** such completions with the point and color names fixed. In every one, at least 19 of the 2,800 groupings connect every color. The original drawing attains 19, so this bound is sharp. An attempt to get below 19 from that drawing must change a line touching the chosen six. [Original drawing and its 19](../vertex-redraw/FixedSix.lean) · [Completion count](SixBoundaryCounts.lean) · [Theorem for every completion](SixBoundaryResult.lean)

Every one of these completions falls outside the earlier three-point test. That test needs four starting points including the added point. Three colors must pair them internally. Each of the other twelve colors must send them to one of just three disjoint sets of four outside points. Lean checked all 455 starting triples against the known lines at the six points. Every choice of three outside sets leaves a color that cannot fit. [Earlier test](../three-stars/) · [Pattern check](PatternChecks.lean) · [Proof for completions](PatternProof.lean)

## How to check the results

For each of the four full counts, the program starts with the lowest unused point and tries each possible pair of partners for its triple. Repeating this gives each grouping once. For every win it follows the wild and ordinary lines to reach every point in each color. For every loss it finds a nonempty set of points that misses at least one point and has no line of the failed color or wild line leading out. All 1,401,400 groupings receive one of those two verdicts in each example. [Enumerator and graph proofs](SixTrap.lean)

For the 3,725,456 completions, Lean lists the possible pairs of each color on the unfixed points. It builds proper colorings by choosing one matching per color and rejecting overlaps. It carries along the groupings already known to connect every color chosen so far. A separate proof shows that every legal completion occurs on a branch and that each surviving grouping supplies paths in the original K15. [Enumeration](SixBoundary.lean) · [Proof of coverage and paths](BoundaryProof.lean)

Run `./verification/replay.sh six-point-trap` from the repository root with Lean 4.19.0. The finite checks use Lean’s native evaluator. Each coloring file lists the sixteen partners for one color per row, with points and colors numbered from zero.
