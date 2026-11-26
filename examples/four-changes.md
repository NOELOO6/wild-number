# Four changes to reach the last color

Label the 15 points from 0 to 14. Start with the five paths below. Each path uses two wild lines. Fourteen colors can travel everywhere. Color 6 gets stuck.

| Starting paths | Paths after the repair |
| --- | --- |
| 0–1–2 | 0–1–2 |
| 3–4–5 | 4–3–6 |
| 6–7–8 | 8–5–9 |
| 9–10–11 | 7–10–11 |
| 12–13–14 | 12–13–14 |

Erase **4–5, 6–7, 7–8 and 9–10**. Draw **3–6, 5–8, 5–9 and 7–10**. Every color can now travel everywhere.

**Why four?** Lean tried every way to keep seven of the original ten lines. For each choice it found that even three more lines cannot cross all the necessary cuts. This rules out every direct repair with one, two or three replacements. It allows edges between any two points. [Lean proof](../cases/k15/FourChanges.lean)

A separate program tried all 1,401,400 ways to split the fifteen points into five groups of three. For each grouping that works, the table counts how many of the ten original lines lie inside those groups and can be kept together.

| Original lines that can be kept | Working groupings |
| ---: | ---: |
| 0 | 26,930 |
| 1 | 43,789 |
| 2 | 31,980 |
| 3 | 13,883 |
| 4 | 3,867 |
| 5 | 689 |
| 6 | 86 |
| 7, 8, 9 or 10 | 0 |
| **Total** | **121,224** |

The coloring lies outside the cyclic, two-team and perfect-factorization families checked earlier. A cyclic symmetry would give each point the same number of alternating four-edge loops. Points 0 and 2 have 12 and 8. Even one such loop rules out a perfect factorization. For the two-team test, the program checked every split into two groups of eight after adjoining the extra point. [Coloring data](../cases/k15/four-changes.json) · [Independent checker](../cases/k15/check_four_changes.py)
