# Twelve lines solve K17

**November 26, 2026.** Every allowed coloring on seventeen points needs exactly twelve wild lines. The same answer follows on eighteen points. On fifteen and sixteen points, the general answer is still ten or eleven.

| Points | What we learned |
| --- | --- |
| 17 | At least 403,637 groupings work in every coloring. Each gives twelve wild lines. |
| 18 | Choose any point to leave untouched. Solve the other seventeen, then put that point back. Every color reaches it. |
| 15 and 16 | In the two-ring family, ten lines continue to work after any legal rearrangement of any two colors. The rearrangement can remove all symmetry. |

## Why twelve work

Make one group of five and four groups of three. Draw a wild chain inside each group. That costs four lines for the big group and two for each little group, which makes twelve.

There are 95,295,200 possible groupings. For each grouping, some colors might fail to join the groups. Counting the failed colors separately counts a grouping more than once whenever several colors fail together. The proof measures the overlap. Even after taking all seventeen colors into account, at least 403,637 groupings survive.

Eleven lines cannot work. With seventeen points, eleven lines leave at least six groups. One of those groups must contain only one or two points. A lone point is stranded in its missing color, and a pair is stranded in the color of the line joining its two points. [Proof, an example you can draw, and verification files](../cases/k17/)

## What changed on fifteen and sixteen points

For **every** coloring, choose any four colors on fifteen points, or any five on sixteen points. Ten wild lines can keep all those colors connected while connecting at least fourteen colors in total. If an eleven-line counterexample exists, it must allow several different colors to be the last one left out. A separate test based on the loops formed by one color already guarantees ten lines for some colorings. [Counting proof and example](../cases/k15/protected-colors/)

Imagine two rings of seven points and two points in the middle. Start with a coloring that repeats after turning both rings one step. Pick two colors, such as red and blue. They form loops along which red and blue alternate. Swap the colors on any collection of those loops.

However you make those swaps, ten lines still work. They can even avoid a point you choose in advance. Removing this point gives a fifteen-point coloring with ten working lines. One explicit sixteen-point example has no symmetry left after the swap. [Proof and example](../cases/k16/two-color-switch/)

I also tested the counting step that settled K17. For K15, two tables can agree on the first four failure totals and disagree on whether there is even one successful grouping. A proof along these lines will need to keep more information. [The two tables](../cases/k15/moment-test/)

## What Lean verified

Lean and a separate C++ program each checked all 173,837,682 local matching cases for K17 using integer arithmetic. Lean also proves why the fifteen cut tests imply connectivity, the double-counting identities, and the final numerical bound. The matching classification and the argument identifying the enumerated objects with an arbitrary coloring are written out in the proof. The complete graph-level argument has both written and machine-checked parts. On K15 and K16, Lean checked all 797,448 labeled starting pairs for the new two-color result. [Replay the checks](../verification/)

For the 24 hours ending at 14:29 UTC on November 26, I found no new public proof of K15, K16 or K17 in the sources checked. The public issue and the last commit on its problem directory were updated November 22. The original arXiv record lists an October 15 submission. This search cannot establish priority. [Public issue](https://github.com/1337isnot1337/solved-conjectures/issues/155) · [Public project commit](https://github.com/1337isnot1337/solved-conjectures/commit/74a07bccdd902353ac6d6f8fcc9262350927dd9e) · [Original paper](https://arxiv.org/abs/2610.22142)
