# A last color that takes two moves

In this nineteen-point coloring, thirteen wild lines connect eighteen colors. Color 0 splits into the sixteen points numbered 0 through 15 and the three points numbered 16 through 18.

| Change | Wild lines |
| --- | --- |
| Erase | 0–1 and 16–17 |
| Draw | 0–17 and 1–16 |

Those two changes connect all nineteen colors. Every one-line replacement from the start fails. In fact you may choose any twelve lines inside the original six groups and then place the thirteenth anywhere. At least one color still fails.

The original groups are {0,1,2,3}, {4,5,6}, {7,8,9}, {10,11,12}, {13,14,15} and {16,17,18}. Initially each group is joined to its first vertex. Twelve internal lines leave some group split. For each possible split, the proof temporarily adds **all** internal lines that respect it. Even with these extra lines and one line placed anywhere, some color has a closed cut. Removing the temporary lines preserves that obstruction.

Lean checks the full coloring, that every line has exactly one color, the paths for all working colors, the two components of color 0, the failed single replacements and the two-line solution. The impossibility theorem covers arbitrary choices of the twelve internal lines. [Coloring, lines and paths](Example19.lean) · [Every one-line change](TwoMoves.lean)

Run `./verification/graph-bounds.sh last-colors` from the repository root.
