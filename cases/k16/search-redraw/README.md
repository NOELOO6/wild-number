# Change six colors in the difficult search example

Start with the supplied coloring on sixteen points. Choose any **six** of its fifteen colors. Erase those colors, then assign the erased lines any six colors that keep the drawing proper. **Ten wild lines still connect every color.** The ten can avoid point 15, so the same result holds on the fifteen remaining points. In particular, changing the last two colors in any way cannot turn this example into a counterexample. [Starting coloring](../../../examples/search-coloring.json)

The starting coloring has 55 pairs of colors forming a single cycle through all sixteen points. The round-robin starting coloring has 60. Relabeling preserves this count, so these are different starting colorings. [Checked counts](RedrawNames.lean)

There are 5,005 choices of the six colors. Ten symmetry maps of the starting drawing all fix point 15. Lean checks the maps preserve edge colors up to a permutation of color names and that they take all 5,005 choices into 508 representative cases.

| Representative cases | How the ten lines are chosen |
| ---: | --- |
| 242 | One grouping works for every new matching that can use the erased lines. |
| 266 | Pick a specified erased line and inspect the new matching containing it. The matching selects a grouping that works for every possible choice of the other five colors. |

The proof reads 81,889 grouping choices using 6,956 different lists of triples. For each representative it enumerates the possible matchings by pairing the first unused point with every allowed partner. In the second row, each actual matching either is the one containing the specified line or shares no edge with it. The checker follows paths in the graph for all the matchings that can accompany it. It checks the ten wild lines are distinct, properly ordered, and connect all the original colors as well.

The graph theorem applies to any edge-disjoint collection of allowed mate lists covering the erased lines on a representative. The coverage and transport lemmas handle relabeling. Restoring point 15 adds a leaf in each color. [Enumeration](SearchRedraw.lean) · [Certificate replay](RedrawRows.lean) · [Graph theorem](RedrawGraph.lean) · [Names and transport](RedrawNames.lean) · [Leaf theorem](../Delete.lean)

Run `./verification/replay.sh search-redraw` from the repository root. This family starts with the counterexample-search coloring. The question for arbitrary K15 and K16 colorings remains open.
