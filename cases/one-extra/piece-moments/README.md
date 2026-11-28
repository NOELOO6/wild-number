# At most one extra component at the conjectured edge budget

For every minimum proper coloring at the following odd orders, the conjectured number of wild edges connects every color except possibly one. If that color is disconnected, it has exactly two components. The same edge budget gives the same conclusion at the next even order.

| Odd orders | Number of wild edges at the largest listed order |
| --- | ---: |
| 15, 19, 23, 29, 35, 41, 43, 47, 49 | 33 at K49 |
| 53, 55, 59, 61, 65, 67, 69, 71, 73, 75 | 50 at K75 |

At K25 and K37 the corresponding budget connects all but at most one color. The bound there allows more than two components in that color. At every odd order 15 and 19–75, a positive fraction of the checked family has at most two extra components in total. Earlier graph-level Lean proofs give the one-extra-component conclusion at K15 and K19. [K15 bounds](../../k15/) · [K19 graph proof](../../k19/one-piece/)

For example, at K69 at least **1,266 per million** and at K75 at least **13,520 per million** of the layouts in the specified family leave at most one extra component. To obtain these families, take **any** rainbow seven-set containing the added root, divide its other six vertices into any two triples, and partition all remaining vertices into triples. The bounds hold for each such choice. At K43, at least **1,808 per million** work to this extent after a suitable four-set and triple are chosen. These are lower bounds on layouts with a possible last obstruction. Whether that obstruction can always be removed at the same cost is open.

## Component counting

Complete the odd coloring on $n$ vertices by adding its missing root. Use the root as a singleton and partition the ordinary vertices into triples and, when necessary, one block of size four or five. A tree in each ordinary block costs exactly $\lfloor 4\lceil n/2\rceil/3\rfloor$ wild edges. For a layout let $F$ count disconnected colors and let $D$ be the sum, over colors, of the number of components minus one. Both quantities are unchanged by deleting the singleton root, which is a leaf in every color. Conversely, to obtain the even-order conclusion, delete any vertex from the even coloring and restore that leaf in each color.

Choose a set $B$ containing the root and some whole blocks. Fix their division and partition the remaining $u$ vertices uniformly into triples. If $B$ is rainbow, its internal edges have distinct colors. Each pair of specified vertices is the one internal edge of exactly one color. The other $n-\binom{|B|}{2}$ colors have no internal edge. Any set containing the root can be grown one vertex at a time. At size $b$, each used internal color rules out at most $b-2$ new vertices, so $b+\binom b2(b-2)<n+1$ suffices for the next rainbow vertex. In particular a rainbow seven-set through any root exists at K69 and K75. [Lean extension theorem](../../sieve/Rainbow.lean)

For a single color, contract its known internal edges between planted blocks and remove their used endpoints. Let the resulting distinguished blocks have residual degrees $d_1,\ldots,d_k$, with the root component listed first. Under a random permutation of the free vertices, all completions of this partial matching are equally likely. If $h$ free triples and $a$ distinguished endpoints are to be matched on one side, its number of completions is
$$
W(h,a)=(3h)_{a}\,(3h-a-1)!!.
$$
The falling factorial assigns distinct partners to the distinguished endpoints. The remaining free points match among themselves. An impossible size contributes zero, and an empty matching contributes one. For the unplanted versions at K23 and K29 all endpoints can match freely, giving $(3h+a-1)!!$ when $3h+a$ is even.

To count connected completions, subtract all cases in which the component of the first distinguished block is proper. Choose the free triples and other distinguished blocks in that component, multiply its connected count by the unrestricted completion count outside, and sum. If no distinguished block is present, distinguish the first free triple. This gives the failure probability for this color. To count its expected extra components, mark one component away from the root and sum the same product over all possible marked components. A completion with $k$ components occurs exactly $k-1$ times. Summing the two means over colors gives $\mathbb E F$ and $\mathbb E D$. No independence between colors is assumed.

## Credit for several isolated triples

Within the free vertices, mark a triple once for each color closing it together with the root. Its weight is one, two or three. Distinct marked blocks of a layout use disjoint sets of colors because each color has only one root partner. Thus their total weight $Z$ satisfies $Z\le F\le D$. The count improves on the mean whenever a layout must have several failures at once.

For a free region $Q$ of size $q$, exactly $q$ colors have their root partner in $Q$. For any one such color the number of its marked triples in $Q$ equals its number of internal matching edges. This lies between $\max(0,q-(n+1)/2)$ and $\lfloor(q-1)/2\rfloor$. At the initial rainbow frame with $b=|B|$ and $u=n+1-b$, the number of marks is exactly
$$
H=u(u-b)/2+\binom{b-1}{2}.
$$
Indeed the internal edge counts on $Q$ and on its complement differ by $(u-b)/2$. Of the colors with root partner in $Q$, exactly $\binom{b-1}{2}$ have an internal edge in $B$. Consequently $\mathbb E Z=H/\binom{u-1}{2}$.

For a layout let $x_w$ count its blocks of mark weight $w$. Let $T_{w,j}$ be the sum over each choice of one such distinguished block of the $j$-th elementary symmetric polynomial of the weights of the other blocks. For a fixed set of disjoint blocks, conditional on their presence the other vertices have a uniform triple partition. A particular triple on the remaining $q$ vertices has probability $1/\binom{q-1}{2}$ of appearing. Extending one distinguished block and $j$ further marked blocks gives
$$
L_j\,\mathbb E T_{w,j}\ \le\ \mathbb E T_{w,j+1}\ \le\ U_j\,\mathbb E T_{w,j},
$$
where $q=u-3(j+1)$ and $L_j,U_j$ are the lower and upper bounds on the number of marks in $Q$ above, divided by $(j+1)\binom{q-1}{2}$. The factor $j+1$ removes the choice of which nondistinguished block was added last.

Each certificate supplies nonnegative multipliers for these six inequalities in each weight class, plus an affine function $s_0+s_1Z$. The check tests every possible $(x_1,x_2,x_3)$ and verifies that their combined expression is at most $(Z-2)_+$. Taking expectations gives a credit $g=s_0+s_1\mathbb E Z$. For either $Y=D$ or $Y=F$,
$$
\Pr(Y\le1)\ge 1-(\mathbb E Y-g)/2.
$$
This follows by subtracting the credit from the mean to bound $\mathbb E\min(Y,2)$. The third output column also records the direct bound $\Pr(D\le2)\ge1-\mathbb E D/3$.

## Protecting named colors

The nearly winning layout can be chosen to connect some colors specified in advance. With at most one extra component in total, it can protect **any seven colors at K71**, **any five at K73** or **any two at K75**. These results also hold at the following even orders.

Start the rainbow extension with the root and its partners in two named colors. These vertices form a rainbow triangle because two edges of the same matching would need four vertices. The conditional failure probabilities of these two colors come from the root-edge profiles. Bound each further named color by the largest single-color failure probability in any profile. If $P$ is the number of named colors failing, the same surplus bounds $\mathbb E(D+P-2)_+$. Whenever $\mathbb E D+\mathbb E P-g<2$, some layout has $D+P\le1$. In that layout no named color can fail. Replacing $D$ by $F$ gives the corresponding protected-color count when only the number of failing colors is restricted. [Seed extension in Lean](../../sieve/Rainbow.lean)

## Eight points at K37 and K43

Count pairs of same-colored edges inside a planted set. When its size is $b$, the sum of additional pairs over all choices of one exterior vertex is at most $\binom b2(b-2)$. An old edge can match the color of a new edge at only the other $b-2$ old vertices. Choosing an extension at or below the average gives an eight-set through the root with at most four repeated pairs at K37 and three at K43. [Lean growth bound](FrameGrowth.lean)

Divide the seven ordinary vertices into a four-set and a triple in all 35 ways. If some color has $k\ge2$ internal edges, correct the rainbow mean by adding the conditional mean for its entire submatching and $k-1$ empty-color means, and subtracting the $k$ single-edge means. The check covers every edge-disjoint collection of repeated submatchings whose total cost $\sum\binom k2$ is within budget. The first submatching can be relabeled fixing the root. All other submatchings are enumerated. This checks 1,231,495 configurations at K37 and 28,259 at K43, including the empty one. Changes to the means are rounded **up** before addition. The number of marks in the remaining vertices is between $H$ minus the collision budget and $H$, since an ordinary internal edge counted in the rainbow expression is lost only when its color also matches the root inside the frame.

## Verification

From this directory run the two standard-library Python checks. Each output bound is rounded down to a number of layouts per million. The first script prints the odd order, the lower fractions for $D\le1$, $F\le1$ and $D\le2$, followed by the numbers of arbitrary colors that can be protected under the first two guarantees. The eight-point script prints the odd order, the number of configurations checked, and the first two lower fractions. The second script can use different subdivisions for the two latter bounds.

```sh
python3 check.py
python3 eight_point.py
```

The Lean checker independently computes the primary table by a bottom-up recurrence and verifies the rational inequalities using its native evaluator. The frame extension and the deduction of a population bound from a credit use the ordinary kernel. The identification of the recurrence and rooted moments with the graph averages is the counting argument above. The additional eight-point configuration census uses Python integer and rational arithmetic. [Lean arithmetic and averaging](PieceMoments.lean) · [Primary certificates](certificates.json) · [Eight-point check](eight_point.py) · [Eight-point prices](eight-point.json)
