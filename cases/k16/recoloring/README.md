# Redraw any six round-robin colors

**Start with the standard sixteen-point round-robin coloring. Erase any six of its fifteen colors. Redistribute their lines among six colors in any way that keeps the coloring proper. Ten wild lines still connect every color.** You can choose any point to leave untouched, so the same result holds after deleting that point on K15.

The worked example loses every symmetry. Lean proves that even a renaming allowed to shuffle the colors must fix all sixteen points. The ten lines also connect every color in the old drawing. This last guarantee lets you compare the two drawings using exactly the same wild lines.

A counterexample needing eleven lines would therefore share **at most eight complete color classes** with any relabeling of the round-robin drawing. If nine matched, the remaining six would fall under this theorem.

## The starting drawing

Put points 0 through 14 on a circle and point 15 in the middle. For color $c$, join the middle to $c$. Then join $c-i$ to $c+i$ for $i=1$ through $7$, taking numbers around the circle modulo 15. This assigns every line one color.

There are 5,005 choices of six colors and sixteen choices of the point to omit. Lean checks the relabelings that reduce these **80,080** choices to **712** cases. The finite check covers which point is deleted, not just which colors are erased. [Coordinate checks](Coordinates.lean)

## How much of the new drawing do we need to see?

| Type of case | Cases up to relabeling | How the ten lines are chosen |
| --- | ---: | --- |
| One grouping works for every replacement | 313 | Choose the lines as soon as the six old colors and the omitted point are named. |
| Look at one redrawn color | 399 | Pick a specified ordinary line and see the whole new color containing it. A recorded grouping then works however the other five colors are drawn. |
| Total | 712 | Every proper redraw is covered. |

For the second row, the proof lists every possible new color containing the specified line. Each is a matching, meaning its eight lines cover the sixteen points once each. The certificate checks the proposed ten wild lines against that matching, all the old colors, and **every individual matching** that could accompany the chosen one. This also covers any collection of five other colors that can occur together.

## One drawing you can check

Erase old colors 0 through 5 and omit point 15. In the example all six new matchings differ from every original color. The specified line is 4–6. For the new color containing it, the following five triples work.

| Draw the first line | Draw the second line |
| --- | --- |
| 0–4 | 4–5 |
| 1–3 | 3–9 |
| 2–6 | 6–7 |
| 8–12 | 12–14 |
| 10–11 | 11–13 |

Lean checks the six new matchings, verifies that every line on sixteen points occurs exactly once in the new coloring, and verifies paths on the fifteen remaining points. [Complete example](Example.lean)

## Verification

The graph theorem takes an arbitrary compatible collection of redrawn matchings covering the erased lines. The enumerator includes every legal matching, and the proof uses actual paths on the fifteen-point graph. Putting the omitted point back adds one leaf in each color. The coordinate check verifies the affine changes of names in the round-robin graph. The published lower bound gives the exact value ten. [Graph theorem](SixProof.lean) · [Matching enumeration](Recolor.lean) · [Certificate soundness](PlanSound.lean) · [All finite cases](SixRows.lean) · [Leaf theorem](../Delete.lean) · [Original paper](https://arxiv.org/abs/2610.22142)

The certificates contain 126,852 layout choices using 12,135 different stored layouts. Run `./verification/replay.sh six` from the repository root.
