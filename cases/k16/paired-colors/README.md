# Eight pairs of points

**Ten wild lines suffice whenever the sixteen points can be paired as described below.** You may choose a point to leave untouched. Deleting it gives a fifteen-point coloring with the same ten working lines.

1. Pair up the points. The eight lines inside the pairs must all have the same color.
2. Exchange the two points of every pair at once. Each line must still have its original color.

The rule lets the other fourteen colors vary widely. Each of those colors pairs up the eight pairs in its own way. For any two pairs it joins, it can join their endpoints straight across or crossed.

## Why ten work

Call the eight pairs teams. Between any two teams there are four lines. Each color that joins those teams takes two lines, so exactly two colors join them. Choose the team containing the untouched point and any other team. Look at the two colors joining them. Each color makes four partnerships of teams. The two lists of partnerships can share four, two or one. Sharing exactly three would force their fourth partnerships to agree too.

For each case we supply tickets. A ticket gives five triples on the fifteen remaining points. Drawing two wild lines per triple costs ten. Every ticket connects the color inside the teams and both chosen colors. For the remaining colors, Lean bounds how many tickets each can spoil. Different colors can spoil the same ticket. Even after counting each spoil separately, tickets survive.

| Partnerships shared | Different layouts | Tickets including repetitions | Maximum total spoils | At least this many winning tickets |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 2,304 | 4,608 | 3,072 | 1,536 |
| 2 | 1,408 | 2,304 | 1,856 | 448 |
| 1 | 1,344 | 32,640 | 28,800 | 3,840 |

The counts in the last column refer to tickets. A layout can appear on several tickets. The text files give the weight and the fifteen points in successive triples, with letters a through o denoting points 0 through 14.

## What Lean checks

The normalized graph theorem quantifies over every permitted list of remaining colors. Its hypothesis says that their team partnerships cover exactly the unused partnerships with multiplicity. It even permits orientations for those colors that would reuse an individual line, so all proper choices are included. Lean follows actual graph paths, checks each of the 1,680 oriented partner patterns in each case, adds the ticket bounds and proves that a working ten-line graph exists. It also checks how to name the eight teams in all cases and proves the point-restoration theorem. The two numbered rules above give the written translation from a coloring to these coordinates. [Graph theorem](PairedCertificate.lean) · [Naming and point restoration](NormalForm.lean) · [Path checker](../../k19/EdgeWalk.lean)

Run `./verification/replay.sh paired` from the repository root.
