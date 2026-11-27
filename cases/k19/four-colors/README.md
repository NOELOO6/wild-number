# Four-color redraws on K19 and K20

Start with the nineteen-point coloring from the two-line repair example. Choose any four colors and redraw their edges in any way that leaves the coloring proper and the other fifteen colors intact. **The resulting wild number is exactly 13.** One set of thirteen wild edges can be chosen in advance for each set of four colors. The same result holds on the twenty-point completion, where each color pairs its missing point with the extra vertex. [Starting coloring](../two-moves/Example19.lean) · [Ordinary K19 theorem](OrdinaryRedraw.lean) · [K20 theorem](PaletteGraph.lean)

## Look up a witness

Colors and ordinary vertices are numbered 0 through 18. Join the smallest point of each group to all the other points of that group. The group of four costs three edges and the five triples cost two edges each.

| Colors that may change | Groups giving thirteen wild edges |
| --- | --- |
| 0, 1, 2, 3 | {3,4,6,15} · {1,11,17} · {5,9,18} · {2,12,16} · {8,10,14} · {0,7,13} |
| 0, 3, 10, 16 | {1,2,4,7} · {6,9,12} · {0,13,15} · {3,10,11} · {5,8,17} · {14,16,18} |
| 15, 16, 17, 18 | {3,9,11,18} · {5,8,16} · {13,14,15} · {2,6,7} · {0,4,10} · {1,12,17} |

Run `python3 cases/k19/four-colors/show.py 0 3 10 16` from the repository root to print the groups and edges for any of the 3,876 choices. The table uses 1,587 different layouts. [Lookup tool](show.py) · [Layouts](layouts.txt) · [Color-to-layout index](palette-layouts.txt)

## How the proof works

After adding the extra vertex, a disconnected color would have to match every point on one side of a cut to another point on that side. The wild edges keep each group together. The side away from the extra vertex is therefore a union of groups, and its size must be even.

For each such cut, Lean checks that every unchanged color has an edge crossing it. For the four colors being redrawn, it finds a single vertex whose four possible partners are all across the cut. Every legal redraw must still pair that vertex across. This rules out every disconnected color. The general lower bound gives thirteen. [Finite checks](PaletteChecks.lean) · [From cuts to graph paths](PaletteGraph.lean)

Run `./verification/graph-bounds.sh palette19` with Lean 4.19.0. The finite table checks use Lean’s native evaluator. The unrestricted cases K19 and K20 still have bounds 13–14.
