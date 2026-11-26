# Twelve wild lines on seventeen points

**Every minimum proper coloring of K17 has wild number 12.** Of the 95,295,200 ways to divide the points into one group of five and four groups of three, at least **403,637** work for every color of the given coloring. The successful choices can differ between colorings.

Draw a chain of four wild lines in the five-point group and a chain of two in each triple. That uses twelve lines. A color only has to join the five groups. The proof counts how often a color leaves groups cut off, including how often two or three colors do this together. Even after accounting for all seventeen colors, some groupings always survive.

| Graph | Wild lines | Reason |
| --- | ---: | --- |
| K17 | 12 | The counting proof supplies twelve. Smaller choices leave a point or a pair cut off in some color. |
| K18 | 12 | Delete any point, apply K17 and put the point back. Every color already has one line from that point to the others. The published lower bound is twelve. |

## A grouping you can draw

Label the points 0 through 16 around a circle. For color $c$, pair $c-d$ with $c+d$ for $d=1,\ldots,8$, wrapping the numbers around the circle. Color $c$ misses point $c$. Use the following chains. For example, the first row makes 0–1, 1–2, 2–3 and 3–5 wild.

| Group | Draw the chain |
| --- | --- |
| Five points | 0–1–2–3–5 |
| Triple | 4–6–9 |
| Triple | 7–8–12 |
| Triple | 10–11–15 |
| Triple | 13–14–16 |

Lean follows the paths from point 0 and reaches all seventeen points in each of the seventeen colors. [Example check](Example.lean)

## Proof for every coloring

**1. Add a temporary point.** The 136 edges of K17 use seventeen colors. A color has at most eight edges, so each has exactly eight. Each point misses one color, and each color misses one point. Join a new point $r$ to each old point in its missing color. Each color is now a perfect matching on eighteen points. Together the seventeen matchings use each edge exactly once. The new point stays alone when drawing the wild chains. In any one color it has just one incident edge. Removing that leaf preserves connectivity on the other seventeen points.

**2. Check fifteen cuts.** Count the five groups and the lone root as six blocks, all of odd size. After contracting each block, a color fails precisely when a union of blocks has no edge of that color going outside. Each connected component is a union of an even number of blocks, since a matching pairs all its vertices internally. If there is more than one component, one contains exactly two blocks. Conversely, a closed union of two blocks disconnects the color. There are fifteen pairs of blocks. Their sizes in vertices are four, six or eight.

Write $L=95{,}295{,}200$ for the number of groupings. Choose the five points first. The remaining twelve have $12!/((3!)^4 4!)=15{,}400$ partitions into four triples. A fixed single color fails on 8,230,880 groupings. All matchings are equivalent by a relabeling fixing the root.

**3. Count failures together.** For each grouping let $k$ be the number of failing colors. Write $S_1,S_2,S_3$ for the sums over groupings of $k,\binom{k}{2},\binom{k}{3}$. In particular $S_1=17\cdot8{,}230{,}880$. Let $W$ count groupings where $k=0$. For $0\leq k\leq17$,

$$12\mathbf{1}_{k=0}\ \geq\ 12(1-k)+10\binom{k}{2}-6\binom{k}{3}.$$

The expression on the right is $(1-k)(3-k)(4-k)$. It equals twelve at zero and is nonpositive at every positive integer. Summing gives $12W\geq12(L-S_1)+10S_2-6S_3$.

**4. Reduce all pairs to fifteen types.** Two different color matchings alternate around disjoint even cycles of length at least four. Record the length of the cycle containing $r$ first, followed by the other lengths in sorted order. This completely determines the pair up to relabeling fixing $r$. To see this, start both root cycles at $r$, follow the first color then the second, and match successive points. Do the same on each of the remaining cycles of equal length. This also works for an ordered choice of the two colors.

For type $i$, write $P_i$ for the number of groupings on which both colors fail. For a vertex set $s$, let $f_i(s)$ count groupings on which both fail and $s$ is a union of two blocks. Every double failure contributes once to $P_i$. Its fifteen different unions each contribute once to the appropriate $f_i(s)$.

| Root cycle | Other cycles | Groupings where both fail |
| ---: | --- | ---: |
| 4 | 4, 4, 6 | 1,126,856 |
| 6 | 4, 4, 4 | 679,856 |
| 4 | 4, 10 | 1,077,500 |
| 10 | 4, 4 | 646,232 |
| 4 | 6, 8 | 1,111,252 |
| 6 | 4, 8 | 650,752 |
| 8 | 4, 6 | 664,660 |
| 4 | 14 | 1,069,698 |
| 14 | 4 | 631,704 |
| 6 | 6, 6 | 701,612 |
| 6 | 12 | 636,200 |
| 12 | 6 | 656,966 |
| 8 | 10 | 624,870 |
| 10 | 8 | 631,704 |
| 18 | None | 624,440 |

**5. Bound triple failures with the integer certificate.** Fix a representative pair of type $i$. For a third matching $m$ disjoint from both, let $R_i(m)$ be the sum of $f_i(s)$ over all unions $s$ of two, three or four edges of $m$. If all three colors fail on a grouping, the third color closes at least one of its fifteen unions. Each such union is a union of two, three or four matching edges. Therefore the number $T$ of groupings spoiled by all three satisfies $T\le R_i(m)$.

Each pair type has a table of signed integer prices $p_i(e)$ on the unused edges and transfers $h_i(j,k)$ indexed by two pair types. Take $j,k$ to be the types of the two pairs involving $m$. The finite checks establish three inequalities.

1. For **every** possible $m$, $2R_i(m)\le\sum_{e\in m}p_i(e)+h_i(j,k)$.
2. Over all edges unused by the first two colors, $\sum_e p_i(e)\le10P_i-3{,}973{,}540$.
3. Each transfer is symmetric in its last two entries. For every triple of types, $h_i(j,k)+h_j(i,k)+h_k(i,j)\le1$.

For any actual coloring, choose a relabeling to the representative separately for each of its 136 pairs. For that pair, the other fifteen matchings use every unused edge exactly once. Thus summing the first inequality over those fifteen colors charges each edge price exactly once. Across all pairs, each triple of colors occurs three times and contributes at most one unit of transfer. The 680 triples and the second inequality give

$$6S_3\le10S_2-136\cdot3{,}973{,}540+680.$$

Relabelings for different pairs need not agree. Every edge price is summed inside its own pair account, and the transfers depend only on the three cycle types.

**6. Finish.** Substitution gives

$$12W\ge 12(95{,}295{,}200-17\cdot8{,}230{,}880)+136\cdot3{,}973{,}540-680 =4{,}843{,}640.$$

Rounding up gives $W\ge403{,}637$. For the lower bound, each connected component of the wild edges on K17 needs at least three vertices. A lone point would be isolated in its missing color. A two-point component would be cut off in the color of its own edge. Thus at most five components remain, and creating them from seventeen isolated vertices takes at least twelve edges. This proves equality.

Deleting any point from a minimum proper coloring of K18 leaves a minimum proper coloring of K17. Restoring the deleted point as a leaf of each color proves the same upper bound for K18. For a direct lower bound, eleven wild lines on K18 leave at least seven components. No component can be a pair. At most one can be a lone point, because two lone points would be cut off together in the color joining them. One lone point and six components of size at least three would require nineteen points. This also proves that twelve are necessary, in agreement with the original paper. [Dawkins, Nappo, Tong and Zimbizi](https://arxiv.org/abs/2610.22142)

## Reproduce the result

From the repository root run `./verification/replay.sh k17` with Lean 4.19.0 and a C++20 compiler. The two implementations check **173,837,682** possible third matchings across the fifteen pair representatives. Each uses the committed integer prices. An optimizer helped find them. The proof checks the integers directly.

| What is checked | Implementation |
| --- | --- |
| Why the fifteen cut tests suffice for arbitrary matching and connected blocks | [Lean connectivity theorem](Connectivity.lean) |
| Why counting by layout or color subset gives the same number, and each edge price is charged once | [Lean double-counting identities](Incidence.lean) |
| Build the four-triple partitions, both-color counts and cut frequencies | [Lean grouping enumeration](Groupings.lean) |
| Generate all legal third matchings and verify the price inequality | [Lean third-color enumeration](ThirdColors.lean) · [All 15 verified cases](Rows.lean) |
| Verify pair types, price totals, transfer cancellation, the cubic inequality and final count | [Lean counting theorems](Certificate.lean) |
| Independently enumerate the layouts and matchings and recompute the guarantee | [C++ checker](check.cpp) · [Integer certificate](prices.txt) |
| Follow all seventeen colors for a specific set of twelve lines | [Lean example](Example.lean) |

The universal graph argument is the written proof above. The normalization to fifteen types and the identification of the enumerators with arbitrary graph inputs use written arguments. Lean proves the cut criterion, the double-counting identities for arbitrary incidence relations, the finite checks, and the counting implication. The written proof applies these results to the given coloring. An end-to-end formal theorem starting with a properly colored graph remains open in this repository. The finite Lean checks use `native_decide`, which trusts Lean's native evaluator.

### Certificate format

Each pair type occupies seventeen lines of `prices.txt`. The first gives the number of cycles, their lengths in rooted order and $P_i$. The second lists 153 edge prices, with edge $u<v$ at zero-based index $v(v-1)/2+u$. The final fifteen lines form its $15\times15$ transfer table. In the canonical representative write the cycles on consecutive vertices starting at 0. On each cycle the first matching uses positions 0–1, 2–3, and so on. The second uses 1–2, 3–4, and the closing edge. Finally exchange labels 0 and 17 to place the root on the first cycle.
