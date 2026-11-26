# Ten wild lines from a local pattern

**The 32 specified lines in the table below suffice.** On sixteen points, the other 88 lines can receive any colors that complete a minimum proper coloring. At least four different sets of ten wild lines work, and they all leave point 15 untouched. The same choices work after removing point 15.

On a fifteen-point drawing, a table entry $v$–15 tells you the color missing at $v$. The remaining entries just give the colors of ordinary lines.

| Color | Lines with this prescribed color |
| ---: | --- |
| 0 | 4–7, 0–15 |
| 1 | 0–5, 2–7, 1–15 |
| 2 | 4–5, 1–7, 6–15 |
| 3 | 3–4, 1–5, 0–7 |
| 4 | 0–1, 2–5, 3–6 |
| 5 | 0–2 |
| 6 | 1–2 |
| 7 | 5–6, 2–15 |
| 8 | 1–4, 6–7, 3–15 |
| 9 | None specified |
| 10 | 3–5, 0–6 |
| 11 | 1–6, 3–7, 4–15 |
| 12 | 2–6, 5–15 |
| 13 | 5–7 |
| 14 | 1–3, 4–6, 7–15 |

## The seventy choices

Use 0–1 and 1–2 to connect the first triple. Use 3–4 and 4–5 to connect the second triple. Join points 6 and 7, then add one of the seven remaining points to their group. Divide the other six points into two triples. Connect each triple with two lines. This gives $7 × 10 = 70$ possible sets of ten lines. Lean checks that the seventy edge sets are distinct.

A given color can spoil some of the seventy choices. To see how many, complete **that color alone** in every possible way and take the largest number it can spoil. This allows the other colors an even freer choice than a proper coloring permits.

| Pattern being used | Maximum total spoils | At least this many surviving choices |
| --- | ---: | ---: |
| The 32 prescribed lines above | 66 | 4 |
| First 36-line example | 60 | 10 |
| Second 36-line example, including the four omitted lines of the table above | 48 | 22 |

In the 32-line case the four unassigned pairs among the nine named points are 0–3, 2–3, 0–4 and 2–4. Lean checks every possible subset a color can occupy among those pairs. Each of the two full local examples has an explicit, verified proper coloring extending it. [First pattern](local-table.txt) · [Second pattern](asymmetric-table.txt) · [Genuine extensions and distinctness](Examples.lean)

## A test for other drawings

The same argument applies to any local table on the eight numbered points and point 15. If its fifteen worst spoil counts add to less than seventy, at least one of these ten-line choices connects every color in every completion. A coloring that really requires eleven would have to miss this test for every way of naming the points. [General counting theorem](EightCertificate.lean) · [Thirty-two-line theorem](SparseEight.lean) · [Matching enumeration](EightPoints.lean)

Run `./verification/replay.sh eight` from the repository root.
