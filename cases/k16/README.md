# Sixteen points

**Ten wild edges connect all colors exactly when ten work on at least one of the sixteen graphs obtained by deleting a vertex.** Any successful set of ten leaves some vertex untouched. That vertex is a leaf when viewing any single color, so it can be removed and restored. [Lean theorem for arbitrary matchings](Untouched16.lean) · [Illustrated explanation](../../reports/last-color-k15-k16.pdf)

| Result | Scope |
| --- | --- |
| [Leaf deletion](Delete.lean) | Adding or removing a leaf preserves path connectivity. |
| [Ten-edge equivalence](Untouched16.lean) | A proof for all relevant colorings on sixteen vertices and every list of at most ten wild edges. |
| [Perfect one-factorizations](Perfect16.lean) | Checks 3,155 representatives at each of 16 deletions, totaling 50,480 ten-edge witnesses. |
| [Two teams of eight](../k15/Teams.lean) | The counting theorem on fifteen points applies at any deletion and lifts back to sixteen. |

In a perfect one-factorization, each pair of colors forms a single loop through all sixteen points. Gill and Wanless supplied the complete list up to relabeling. The Lean theorem checks the supplied representatives and their witnesses. Completeness of the list comes from their published classification. [Authors’ data and format](https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html) · [Classification paper](https://doi.org/10.1017/S0004972719000856)

The source data are in [P1F16catalogue](P1F16catalogue). The corresponding [witnesses](P1F16witnesses) and [independent generator](p1f_witness.cpp) are included. [Verification instructions](../../verification/)

If a fifteen-point deletion admits a rotation of order seven, the [sevenfold rotation theorem](../k15/seven.md) supplies ten lines for the original sixteen points.
