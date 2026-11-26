# Five colors already force a solution

**If five colors have the following lines, every legal choice of the other ten colors admits ten wild lines.** The points are numbered 0 through 15. On fifteen points, remove point 15 and its line from each row. You can rename the points and colors. The successful wild lines may depend on how the other colors are drawn.

| Color | Its eight lines |
| --- | --- |
| A | 0–15 · 1–5 · 2–10 · 3–6 · 4–12 · 7–11 · 8–14 · 9–13 |
| B | 0–11 · 1–15 · 2–3 · 4–13 · 5–8 · 6–9 · 7–14 · 10–12 |
| C | 0–9 · 1–3 · 2–13 · 4–6 · 5–12 · 7–15 · 8–11 · 10–14 |
| D | 0–6 · 1–9 · 2–12 · 3–8 · 4–10 · 5–7 · 11–13 · 14–15 |
| E | 0–12 · 1–8 · 2–4 · 3–5 · 6–10 · 7–13 · 9–15 · 11–14 |

## Why all completions work

We chose 507 ways to put points 0 through 14 into five groups of three. Two wild lines in each group join its three points. Point 15 stands alone. For each color, a grouping can fail only if the color pairs up the four points formed by the root and one group, or the six points formed by two groups. Both sides of a disconnected graph are unions of whole groups, and one side has at most two groups of three. [Cut argument](../endgame/)

All five displayed colors pass every one of the 507 tests. Give the tests positive integer weights totaling **99,996**. Now give the unused lines small integer prices totaling **99,469**. For each possible additional color, the tests it can spoil have total weight at most the price of its eight lines. There are exactly **91,446** possible additional colors, and Lean checks the inequality for every one.

Each unused line belongs to just one of the ten remaining colors in a complete coloring. Together, those colors can spoil test weight at most 99,469. This leaves at least **527** units of weight on successful tests. The units are weights, so the conclusion is at least one successful grouping.

## What to check

Lean checks the five disjoint matchings, every candidate grouping, the finite price inequalities, and the general weighted-counting argument. The correspondence between the bit-mask tests and graph connectivity is explained above. An optimizer selected the integer weights and prices. Replaying the proof uses only the stored integers. [Lean checker](Completion.lean) · [507 weighted groupings](layouts.txt) · [Line prices](prices.txt) · [Replay instructions](../../../verification/)

In the data files, a group of points is represented by the sum of the powers of two indexed by its members. For example, 42 stands for points 1, 3 and 5. Each layout row begins with its weight, followed by its five groups.
