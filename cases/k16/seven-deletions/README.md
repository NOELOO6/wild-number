# Choose any point to leave untouched

Start with a K16 coloring whose points and color names can be permuted together by a symmetry of order seven. Pick **any** point. Ten wild lines connect every color and avoid this point. Delete the point and the same ten lines still work on K15.

There are two rings of seven points and two fixed points. A single ring of seven is impossible. Indeed, an edge between two fixed points has a fixed color, and this color would have to match the seven moving points to one another. There are an odd number of them. With two rings, the fixed color pairs the two fixed points and pairs the two rings with each other. Label the paired points on the rings to line up. The other fourteen colors consist of two rotating sets of seven. This gives [the two-starter description](../../k15/seven.md).

A fixed point can be chosen as the root in the original starter theorem. For a point on a ring, name its ring first and label it 0. The new check uses 73 groupings of the other fifteen points into triples. It keeps the lone point as a sixth block. A color disconnects the layout precisely when it pairs up a union of two blocks internally. The cut has either four or six points. Lean checks all rotations of the fifteen cuts for each layout. For every compatible pair of starters, some layout succeeds in all colors.

| Finite check | Count |
| --- | ---: |
| Compatible pairs of labeled starters | 797,448 |
| Candidate groupings for the moving point | 73 |
| Starter pairs with no working grouping | 0 |

The starter pairs can include different labelings of the same coloring. [Lean check](MovedSeven.lean) · [Candidate groupings](groupings.txt)

## A K15 example with no symmetry

Use labels 0–6 on the first ring and 7–13 on the second. Points 14 and 15 stay fixed. The fixed color pairs 14 with 15 and each $i$ on the first ring with $7+i$. The two starting colors below give the other fourteen colors by simultaneous rotation of the two rings.

| Color | Pairs |
| --- | --- |
| First starter | 0–15, 1–10, 2–3, 4–6, 5–8, 7–9, 11–12, 13–14 |
| Second starter | 7–15, 0–13, 1–14, 2–5, 3–11, 4–9, 6–10, 8–12 |

Delete point 0. Draw the five chains **4–14–15**, **5–8–11**, **1–7–10**, **3–6–13** and **2–9–12**. Their ten lines connect every color.

To verify the symmetry claim, put point 0 back by restoring each missing color. Every symmetry of the deletion extends to this completed graph fixing 0. For colors $i,j$, let $w(i,j)$ be the cube of the length of their alternating cycle through 0, setting $w(i,i)=0$. First give color $i$ the score $a_i=\sum_j w(i,j)$, then give it $b_i=\sum_j w(i,j)a_j$. A symmetry preserves these scores. The fifteen final scores are distinct. It must therefore fix each color and each of the fifteen neighbors of 0, one for each color. Lean checks the distinct scores and follows every color in the graph after deletion. [Concrete Lean example](Example.lean)

An additional result allows any two colors of the sixteen-point graph to be rearranged before deleting the chosen point. [Two-color result](../two-color-switch/)
