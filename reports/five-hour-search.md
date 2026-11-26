# Five hours on K15 and K16

**November 26, 2026.** Every allowed coloring of either graph needs ten or eleven wild lines. This investigation found more cases where ten always work. The unrestricted question is still open in this project.

| Result | What it tells us |
| --- | --- |
| Every K15 coloring | Choose any eligible first group of three. There are at least four ways to group the rest that leave only one possible split to check. A color can still get stuck across it. [Counting proof](../cases/k15/counting/) |
| Five specified K15 colors | For the five rows in the table, ten wild lines work for every legal choice of the other ten colors. [See the rows](../cases/k15/five-colors/) |
| Four specified K16 colors | If four colors form the four-dimensional cube pattern, ten wild lines work for every legal choice of the other eleven. A second four-color pattern also works. [See both patterns](../cases/k16/four-colors/) |
| Two teams of eight | If at least twelve colors stay entirely within or entirely across the two teams, ten lines work. The result survives deletion of any one point. [Proof and counts](../cases/k16/three-exceptions/) |

## Looking for a coloring that needs eleven

Two searches repeatedly changed a coloring to drive down its number of successful groupings. Together they tried more than 5.5 billion changes. These can revisit the same coloring. Both reached a coloring with 85,250 successful groupings at the chosen deletion. Lean and an independent Python solver counted those groupings for the saved example. A counterexample would have to drive that count to zero on K15, or to zero at **every** deletion on K16. [Coloring, counts, and solver](../examples/search.md)

I also tested moving the untouched point while exchanging points between the other groups. Charging each spoiled candidate separately to a color still left the estimates too large to prove a repair in general. The four-color result succeeds by using the specified color pattern to choose the candidates and their weights.

## What verification means

Each result links to its Lean checks and the argument connecting them to the graph. In particular, checking that ten lines work for one coloring is straightforward. Proving the conjecture requires covering every allowed coloring. The K13 case has a written reduction to a finite impossibility that Lean checks. [K13 proof](../cases/k13/) · [Replay instructions](../verification/)

I found no public proof covering unrestricted K15 or K16 in the literature and public project records I checked. This search does not establish priority. [Original paper](https://arxiv.org/abs/2610.22142) · [Public research record](https://github.com/1337isnot1337/solved-conjectures/issues/155)
