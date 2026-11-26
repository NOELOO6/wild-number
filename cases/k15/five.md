# Colorings with a rotation of order five

**Ten wild lines suffice for every 15-point coloring whose pattern repeats after a rotation of order five.** The rotation may permute the color names. On sixteen points, the conclusion holds for every coloring with such a symmetry. On deleting a point fixed by the rotation, the resulting fifteen-point coloring also has wild number ten.

Add the usual extra point to the fifteen-point coloring and call it the root. A color is determined by the point it pairs with the root. The rotation therefore acts on colors exactly as it acts on the fifteen root neighbors.

| Moving points | Fixed points on sixteen | How the proof finds a layout |
| --- | ---: | --- |
| Three rings of five | 1 | At least six of 25 layouts work |
| Two rings of five | 6 | A list of 32 layouts covers all compatible starter pairs |

One moving ring would leave fixed colors. A fixed color must pair that ring to another moving ring, since an odd ring has no rotation-invariant pairing within itself. This rules out the remaining possible nonidentity case. Conversely, an order-five symmetry on sixteen points always has a fixed point, which can serve as the root.

## Three rings

Number positions on each ring from 0 to 4. For any two offsets $a,b$, make five triples by putting position $i$ on the first ring with positions $i+a$ and $i+b$ on the other rings, working modulo five. These 25 layouts are invariant under the rotation. For five colors that are rotations of one another, checking a single starter color therefore checks them all.

There are three starters. Select the member of each color orbit that pairs the root with position 0 on its ring. Its other seven edges must come from distinct edge orbits. There are 50,590 possible starters on each ring. If a starter has $q$ edges within individual rings, the following table gives its maximum number of lost layouts.

| $q$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Maximum lost | 7 | 9 | 6 | 5 | 5 | 1 | 1 |

The three $q$ values sum to six, since each ring has two orbits of internal edges. The three entries of the table then sum to at most 23. This alone leaves at least two working layouts. Checking overlaps gives at least six. If at least 20 distinct layouts were lost, some starter would have to lose at least seven. Name its ring first. Lean checks every such starter against the compatible possibilities on the other two rings. Permuting the three ring names preserves the set of 25 layouts. [Lean tables and compatibility checks](Five.lean)

## Two rings

Keep the root fixed. Each of the five fixed colors matches the two rings by a shift. Label the other fixed points by the shift of their root edge's color. For each shift there are just three ways to match the four remaining fixed points. The 32 proposed layouts all work for all fifteen of these possibilities.

The remaining ten colors occur in two orbits. Choose the starters pairing the root to position 0 on the respective rings. These starters together cover sixteen edge orbits, twelve from fixed points to rings and four within the rings. Each starter has 7,920 possibilities. Lean checks that each of the 1,382,400 compatible pairs has a layout on the list that works for all ten rotated colors. Drawing two consecutive edges per triple gives ten wild lines. [Lean starter checks](Five.lean)

The symmetry reductions and the connection from cuts to graph connectivity are given in the text. Lean checks the candidate generation, layout data, bounds and compatibility in the normalized models.
