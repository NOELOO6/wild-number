# Sixteen points

**Ten wild edges connect all colors exactly when ten work on at least one of the sixteen graphs obtained by deleting a vertex.** Any successful set of ten leaves some vertex untouched. That vertex is a leaf when viewing any single color, so it can be removed and restored. [Lean theorem for arbitrary matchings](Untouched16.lean) · [Illustrated explanation](../../reports/last-color-k15-k16.pdf)

| Result | Scope |
| --- | --- |
| [Redraw any six round-robin colors](recoloring/) | Ten work for every proper redraw, whichever point you leave untouched. |
| [Eight pairs with a common color](paired-colors/) | Ten work whenever exchanging all partners preserves each color. |
| [Protect any five colors](../k15/protected-colors/) | Ten lines connect at least fourteen colors including any five named in advance. Four can be protected if the untouched point is prescribed. |
| [Any two-color switch in a sevenfold coloring](two-color-switch/) | Ten work while avoiding any prescribed point, for every recoloring of the chosen two colors. |
| [Four specified colors](four-colors/) | Four colors in the cube or two-halves pattern suffice for every legal choice of the other eleven. |
| [Seven-point reduction](seven-set.md) | Every coloring has at least 3,040 choices of seven points containing at most two lines of each color. At least 1,330 choices contain any specified point. |
| [Leaf deletion](Delete.lean) | Adding or removing a leaf preserves path connectivity. |
| [Ten-edge equivalence](Untouched16.lean) | A proof for all relevant colorings on sixteen vertices and every list of at most ten wild edges. |
| [Perfect one-factorizations](Perfect16.lean) | Checks 3,155 representatives at each of 16 deletions, totaling 50,480 ten-edge witnesses. |
| [Three exceptional colors](three-exceptions/) | Twelve colors obeying a two-team split suffice on sixteen points. Every specified deletion works as well. |
| [Two exceptional colors](../k15/trade.md) | If thirteen colors obey a two-team split, every possible deletion admits ten wild lines. |
| [Five teams of three](../k15/five-teams.md) | Ten lines work if one deletion has this team structure, even with two exceptional colors. |
| [Three teams of five](../k15/three-teams.md) | Ten lines work if one deletion has this three-team structure. |
| [Two teams of eight](../k15/Teams.lean) | The counting theorem on fifteen points applies at any deletion and lifts back to sixteen. |

In a perfect one-factorization, each pair of colors forms a single loop through all sixteen points. Gill and Wanless supplied the complete list up to relabeling. The Lean theorem checks the supplied representatives and their witnesses. Completeness of the list comes from their published classification. [Authors’ data and format](https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html) · [Classification paper](https://doi.org/10.1017/S0004972719000856)

The source data are in [P1F16catalogue](P1F16catalogue). The corresponding [witnesses](P1F16witnesses) and [independent generator](p1f_witness.cpp) are included. [Verification instructions](../../verification/)

If a fifteen-point deletion admits a rotation of order seven, the [sevenfold rotation theorem](../k15/seven.md) supplies ten lines for the original sixteen points.

At least 1,540 starts through any specified point pass the first seven-point test. The proof also guarantees at least 875 starts using thirteen or more colors. [Counting argument and table](seven-count.md)
