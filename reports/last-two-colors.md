# What the last two colors can do

| Graph | Lines | What works for every coloring | Remaining question |
| --- | ---: | --- | --- |
| K15 | 10 | Name any nine colors. At least 666 groupings connect them and five or six more. | Can all fifteen always connect together? |
| K16 | 10 | Name any thirteen. At least 449,107 groupings connect them. At least 8,527 of those connect a fourteenth color too. | Could the two outside colors take turns blocking every grouping? |
| K19 | 13 | Name any two. At least 26,638,742 groupings connect them and leave at most one color in two pieces. | Can the two pieces always be joined while keeping thirteen lines? |

On K16 there are fifteen possible lists of fourteen colors. At least fourteen of those lists have at least 4,264 groupings connecting the entire list.

On K16, if eleven lines are ever necessary, at least fourteen different colors must each be able to appear as the **only** color that fails. Otherwise leave out two colors that can never fail alone. The new count gives a grouping where at least one of them connects and all thirteen named colors connect. That forces the other one to fail alone, a contradiction. A K16 counterexample would need at least 63,953 distinct groupings that each miss exactly one color. On K15 the corresponding minimum number of different possible sole failures is ten.

One K16 example shows why the two outside colors deserve attention. They spoil 862,621 groupings that pass the thirteen named colors. The same coloring also has 1,731,000 full wins. On a K19 example, every single-line replacement fails from a particular start. Erasing 0–1 and 16–17 and drawing 0–17 and 1–16 connects all nineteen colors with thirteen lines.

All 5,005 ways to choose six colors for redrawing in the K16 search example still admit ten wild lines for every legal redraw. The ten lines can avoid point 15, so they work on K15 as well. [Six-color redraw proof](../cases/k16/search-redraw/)

The general counts combine written arguments with Lean-checked tables and arithmetic. Lean proves the K16 cut test and the concrete K19 example directly about paths in graphs. The exact worst-case values are still 10 or 11 on fifteen and sixteen points, and 13 or 14 on nineteen points.

[K15 counting proof](../cases/k15/nine-named/) · [K16 counting proof and example](../cases/k16/last-two/) · [K19 counting proof](../cases/k19/named/) · [K19 two-line repair](../cases/k19/two-moves/) · [Replay commands](../verification/)

A public literature check on November 26, 2026 found no announcement in the preceding day settling K15, K16 or K19. The November 22 entry in the public research log covers orders at least 155. [Research history](https://itsdavis.com/solved-conjectures/history/)
