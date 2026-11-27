# A 140-layout test for K15

Fix a triple A and add the usual sixteenth point r. Suppose all six edges among these four points have distinct colors. Label A as 0, 1, 2 and r as 15. The certificate gives 140 ways to divide the remaining twelve points into four triples. The labels on the twelve remaining points may be chosen freely. [Layouts](layouts.txt) · [Lean construction](AnchorExample.lean)

The layouts use 142 distinct triples. Mark a triple T if some color pairs up all of r together with T, or all of A together with T. **If at most seven of the 142 triples are marked, ten wild edges connect all fifteen colors.** No assumption is made on the other triples. [End-to-end theorem](AnchorExample.lean)

| What can remove a layout? | How many layouts can it remove? |
| --- | ---: |
| One marked triple | At most 6 |
| All marked triples when the test passes | At most 42 |
| All six-point sides that a color pairs internally | At most 96 |
| Layouts available | 140 |

A six-point side belongs to at most one layout in this list. In any coloring at most 96 such sides can be paired internally. The two counts remove at most 138 layouts. Any surviving layout, together with A, supplies five triples. Draw two edges in each. [Counting proof](AnchorPacking.lean)

The included example passes all 142 triple tests. Lean reads the partner table, verifies that it defines a proper coloring, and applies the same theorem after deleting point 15. The finite table checks use Lean’s native evaluator. Run `./verification/graph-bounds.sh anchor-packing` from the repository root. [Example coloring](example.json) · [Verification](PackingColoring.lean)
