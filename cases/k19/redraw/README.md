# Thirteen lines after eight colors change

Start with points 0 through 18 on a circle. Color the line between two points with their midpoint around the circle. For example, color 0 pairs 1 with 18, 2 with 17, and so on. Choose any eight colors. Erase their lines and redraw them any way that still gives a proper coloring of the complete graph. **Thirteen wild lines always suffice for the resulting drawing.** The general lower bound shows this is the minimum.

| Part of the proof | What it checks |
| --- | --- |
| [Groupings and paths](MenuProof.lean) | A color connects the whole drawing if it crosses every split between groups. |
| [Weighted list](layout-weights.txt) and [Lean tally](MenuTable.lean) | Take 439 groupings and move them around the nineteen points in 342 ways each. Count how often each split occurs. |
| [Round-robin colors](SevenMore.lean) | All nineteen original colors cross every split in this list. A first count already allows any seven to change. |
| [Search](LossTree.lean), [weights](RawMenu.lean) and [nineteen roots](AllRoots.lean) | For each possible point missing a color, try every partner for the first point still unpaired. Stop a branch once its bound is proved for every completion. |
| [Frequency check](TableLink.lean) and [matching argument](EightBridge.lean) | Connect the short search to all possible matchings of actual vertices and to the frequencies of their splits. |
| [Eight-color theorem](EightMore.lean) | Start with a proper coloring and obtain thirteen distinct lines with paths in every color. |

Each grouping gives one group of four points and five groups of three. Joining points within each group takes thirteen lines. A color can fail only if some group or collection of groups has no colored line going outside it. Charge the color for every occurrence of such a split in the weighted list.

| Quantity | Count with weights |
| --- | ---: |
| Total weight of groupings | 34,197,948 |
| Maximum charge used for any redrawn color | 4,274,742 |
| Maximum charge for eight redrawn colors together | 34,197,936 |
| Weight still available | At least 12 |

The surviving weight guarantees at least one grouping. Repeated groupings and integer weights are allowed, so 12 is a weight, not a count of different solutions.

From the repository root, run `./verification/graph-bounds.sh redraw` with Lean 4.19.0. The graph argument is formalized through to the paths. The largest finite checks also trust Lean's native evaluator, as shown by the axiom list printed at the end.
