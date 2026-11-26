# Rearrange any two colors

**Choose a K16 coloring with a symmetry of order seven. Pick any two colors and recolor their lines in any way that leaves a proper coloring. Ten wild lines still work, and they can avoid any point you specify.** Deleting that point gives the corresponding K15 result. Both wild numbers are exactly ten by the published lower bound. [Original paper](https://arxiv.org/abs/2610.22142)

Two colors form a collection of alternating loops. On each loop you can keep both colors or swap them. These are all ways to recolor their combined edges with two colors. The rearrangement can destroy the symmetry of the starting graph.

| What the certificate covers | Count |
| --- | ---: |
| Compatible labeled starting pairs for the original K16 | 797,448 |
| Possible choices of two colors in each coloring | 105 |
| Choices involving the fixed color | 14 |
| Choices within either rotating set of seven | 42 |
| Choices between the two rotating sets | 49 |
| Candidate layouts for each kind of specified point | 512 |

## Why the checks suffice

Normalize the starting graph into the two rings, two fixed points, one fixed color and two sets of seven rotating colors. There are two possible locations for the specified point after relabeling. Name it 15 if it is fixed, or name its ring first and call it 0 if it moves. Make this choice **before** recoloring. [Symmetry reduction](../seven-deletions/)

For each root, the table contains 512 ways to split the other fifteen points into five triples. Give each triple a two-line wild chain. With the root as a sixth block, a color fails if and only if it closes a union of two blocks. Such a cut has four or six points. For each of the 2,027,025 perfect matchings on sixteen labeled points, Lean records which layouts have none of these closed cuts. The index is the rank obtained by repeatedly pairing the smallest unused point with each possible partner in increasing order.

For a compatible starter pair, intersect the layout lists for the original fifteen colors. For a chosen pair of colors, split its union into alternating cycles. For each union of these cycles, form the matching which takes its edges from the first color inside the union and from the second outside. Every possible new color of either name occurs this way. Intersect the original layouts with the lists for **all** these new matchings. The check always leaves a layout for each choice of root. Thus the same layout for a specified root and pair even works for every allowed rearrangement of that pair.

Lean verifies all 105 choices for every compatible starter pair, the validity of the candidate layouts and the size of the matching table. Run `./verification/replay.sh switches` from the repository root. [Lean enumeration](Switches.lean) · [Checked theorems](CheckSwitch.lean) · [Fixed-point layouts](fixed.txt) · [Moving-point layouts](moving.txt)

## An example with no symmetry on sixteen points

Start from the [two rows of explicit pairs](../seven-deletions/#a-k15-example-with-no-symmetry). Take the first starter and the color obtained by rotating it three steps. Exchange their colors on the loop **4–6–5–8–7–9–14–13–4**. The resulting K16 coloring has no nonidentity symmetry, even when color names may change.

Leave 0 untouched. Use the chains **6–8–10**, **3–5–7**, **1–4–9**, **2–12–15** and **11–13–14**. All colors connect on K15 and after restoring point 0 on K16.

To distinguish the sixteen points, at each point sum the cubes of the lengths of the alternating cycles through it over all 105 color pairs. These sixteen numbers are distinct. Any color-preserving relabeling, even one which permutes color names, must preserve this sum and hence fixes every point. Lean checks the distinctness, the proper coloring and the reachable points for the ten lines. [Example verification](../seven-deletions/Example.lean)
