# A last color that takes two swaps

**Color 12 starts disconnected. All fourteen other colors start connected. Every one of the 90 swaps between two groups leaves some color disconnected. Two successive swaps connect all fifteen, and the other fourteen stay connected at the intermediate step.** This drawing is outside both previous six-color redraw families, even after arbitrary renaming of points and colors. [The coloring](example.txt) · [Lean proof of the blocked swaps](Repair.lean) · [Lean proof of the separation](Separation.lean)

Each group below uses two wild lines to connect its three points. Reading each triple in increasing order, join the first point to the second and the second to the third.

| Stage | Five groups |
| --- | --- |
| Start | **0,1,2** · **3,4,5** · 6,7,8 · 9,12,13 · 10,11,14 |
| Exchange 1 and 3 | **0,2,3** · **1,4,5** · 6,7,8 · 9,12,13 · 10,11,14 |
| Exchange 2 and 6 | **0,3,6** · **1,4,5** · **2,7,8** · 9,12,13 · 10,11,14 |

The final row gives the ten wild lines 0–3, 3–6, 1–4, 4–5, 2–7, 7–8, 9–12, 12–13, 10–11 and 11–14. Lean checks actual graph paths for the final row and an explicit separating cut for each failed swap. [Positive graph theorem](Outside.lean)

## Why this drawing extends the six-color results

Redrawing six of fifteen colors leaves nine whole color classes in common with the starting drawing. In each older template, following two colors alternately forms either one loop of length 16, loops of lengths 6 and 10, or loops of lengths 4, 6 and 6 on the completed sixteen points. In this example, at most six colors can be selected such that **every pair** has an allowed pattern. Renaming the points preserves the lengths of the loops. The formal separation theorem works for any bijection on points and any injective renaming of colors. Lean also checks that no three ordinary points in this example pass the first step of the newer three-point test. [Proof](Separation.lean)

## Fifty fixed lines suffice for a family

Keep the lines touching points 0, 1, 3 and 8 as shown below and keep each color's missing point. All 55 ordinary lines among the other eleven points can be reassigned in any legally completed coloring. Ten wild lines always suffice. The successful ten can vary with the redraw.

An entry gives the partner of the point at the top of its column. A dash means the color is missing there.

| Color | Missing point | Partner of 0 | Partner of 1 | Partner of 3 | Partner of 8 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 11 | 7 | 3 | 1 | 6 |
| 1 | 9 | 4 | 7 | 5 | 13 |
| 2 | 12 | 9 | 10 | 6 | 2 |
| 3 | 6 | 14 | 11 | 10 | 4 |
| 4 | 3 | 13 | 4 | — | 12 |
| 5 | 13 | 11 | 2 | 4 | 10 |
| 6 | 5 | 3 | 12 | 0 | 9 |
| 7 | 14 | 12 | 8 | 7 | 1 |
| 8 | 0 | — | 13 | 11 | 14 |
| 9 | 1 | 6 | — | 13 | 7 |
| 10 | 10 | 2 | 5 | 8 | 3 |
| 11 | 7 | 10 | 14 | 12 | 5 |
| 12 | 2 | 1 | 0 | 9 | 11 |
| 13 | 8 | 5 | 6 | 14 | — |
| 14 | 4 | 8 | 9 | 2 | 0 |

The proof gives weights totaling 1,000,007 to 176 possible groupings. Even if each color takes its most damaging completion, all fifteen spoil at most 867,981 units of weight together. This leaves at least 132,026 units on winning groupings. Lean enumerates the remaining possibilities for each color and proves graph connectivity for every completion. [Counting and graph proof](FourStars.lean) · [Layout weights](layouts.txt)

## A search for eleven

In a separate coloring, keep points 0 through 5 together as a set and split them into two triples. Split the remaining nine points into three triples. There are 10 ways to do the first split and 280 ways to do the second. Of the 2,800 combinations, **2,781 fail and 19 succeed**. Six first splits have zero wins. The other four have 2, 2, 7 and 8. Each color has at most two pairs among the six selected points and the added root, so the example also passes that preliminary seven-point test.

Lean checks paths on the successful groupings and separating cuts on the failed ones. A counterexample would have to defeat all 1,401,400 groupings on fifteen points. Ten wild lines leave at least five groups. A one-point group fails for the color missing there. A two-point group fails for the color of its internal line. That forces any winning choice of ten to have exactly five groups of three. [Search coloring](six-point-search.txt) · [Checked counts](FixedSix.lean)

Run `./verification/replay.sh stars` from the repository root.
