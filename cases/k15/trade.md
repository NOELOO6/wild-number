# Two teams with two exceptional colors

**Ten wild lines work if at least thirteen of the fifteen colors obey one split into teams of eight.** They work on sixteen points, and after deleting any chosen point. The coloring can have no symmetry at all.

A color obeys the split when each of its lines stays inside a team, or each goes from one team to the other. For a graph on fifteen points, first add the extra point and its missing-color lines. Use the argument below with that extra point as the designated deletion.

## Why two exceptional colors can be handled

If there is an exception, at most six colors can stay entirely inside teams and at most seven can go entirely across. Seven inside colors would already use every within-team edge. Eight across colors would already use every cross-team edge. Thus exactly six are inside, seven are across, and two are exceptional.

Remove the thirteen ordinary colors. Each point has one unused line inside its team and one across. These lines form even cycles alternating between inside and across. Along each cycle, the two exceptional colors must alternate. Thus their only choice is which color goes first on each cycle.

Call the point to delete 0. Name its teammate on an unused line 1 and its opposite-team partner 8. The proposed starting triple is formed by points 1, 8 and another blue point. Lean tries the seven possibilities for that blue point. For each one, there are 1,800 ways to complete the four other triples. These are the same groupings used in the earlier two-team proof. [Catalogue and its cut counts](Teams.lean)

| Step | Guaranteed result |
| --- | ---: |
| Ways to arrange the unused blue matching and the two exceptional colors after labeling | 174 cases checked |
| Choices of the blue point whose count of spoiled groupings is small enough, subject to the anchor test | At least 5 of 7 |
| Choices that can fail the anchor test for an ordinary color | At most 1 |
| Choices passing both tests | At least 4 |
| Working groupings for each such choice | At least 24 of 1,800 |

For the anchor test, an ordinary inside color cannot contain the reserved line 0–1. An ordinary across color cannot contain 0–8. To block the chosen quartet it must therefore contain **1–8** and pair point 0 with the proposed blue point. The edge 1–8 has a unique color, so this spoils at most one choice.

For each remaining starting choice, Lean adds up how many of the 1,800 groupings each color can spoil. The total is at most 1,776. At least 24 groupings survive. The 174 cases describe the two exceptional colors. The thirteen ordinary colors can vary freely subject to being a proper coloring and obeying the split. Different starting choices give different groupings, since the starting triple is the only one with one red point and two blue points.

The reduction to the normalized matchings is written above. Lean proves existence for every admissible normalized exchange and every list of ordinary colors satisfying the forced edge counts. [Lean theorem](Trade.lean) · [Verification instructions](../../verification/)
