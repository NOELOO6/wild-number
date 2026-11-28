# Clearing the two-triple cuts on fifteen vertices

In every minimum proper coloring of K₁₅, at least **390,724** of the **1,401,400** unordered partitions into five triples have an edge of every color leaving each union of two triples. At least **27,810** clear all these cuts and connect at least fourteen colors. In the latter partitions, any remaining disconnected color has exactly two components, one of which is a single triple. Each partition uses ten wild edges, two within each triple.

There is also a sufficient condition for the full conjecture. Complete the coloring to a one-factorization of K₁₆ by joining each vertex to the new root in its missing color. If at least **76 of the 105** unordered pairs of colors have union consisting of four 4-cycles, at least **105** of the partitions connect every color. Such K₁₅ colorings have wild number ten. On K₁₆ the same conclusion holds with any singleton root, since this particular cycle type is independent of the root. The unconditional interval at both orders is still 10–11.

## Two types of failure

Keep the root as a singleton block and draw two spokes in each ordinary triple. In any one color, every block has odd size and a closed side of the perfect matching has even size. If the contracted graph is disconnected, there is therefore a closed pair of blocks. Two distinct closed block pairs are disjoint, since their intersection is closed and cannot be one odd block. The complement of two disjoint pairs is the third closed pair. Thus the closed pairs of blocks are either absent, unique, or the three pairs of a partition of the six blocks. Deleting the singleton root preserves ordinary connectivity, since the root has degree one in each color. [Lean cut classification](../../k16/last-two/GraphCuts.lean)

Call a color **P** if it closes an ordinary six-set made of two triples. Call it **R** if it closes a root-four (the root and one ordinary triple) and has no ordinary six-set cut. All other colors are connected. For a fixed color and layout, write $s$ for the number of closed ordinary six-sets, $q$ for the number of closed root-fours and $d$ for the number of partitions into three closed pairs of blocks. The cut classification gives the two indicator functions $1_P=s-d$ and $1_R=q-d$. Over all layouts a given color occurs in mode P exactly 91,000 times and in mode R exactly 100,800 times.

## The cubic count

For a layout write $p,r$ for the numbers of P and R colors. Each certificate specifies a scale $D$, target bounds on $p,r$, and fourteen signed integer coefficients $a_0,\ldots,a_{13}$. Define

$$
S(p,r)=a_0+a_1p+a_2r+
\sum_{k=0}^2 a_{3+k}{p\choose 2-k}{r\choose k}
+\sum_{h=0}^7\frac{a_{6+h}}{{3\choose |h|}}{p\choose 3-|h|}{r\choose |h|}.
$$

Here $|h|$ counts the one bits of the three-bit mask. The checker verifies $S(p,r)\le D$ on the target and $S(p,r)\le0$ outside it, for all $p+r\le15$. The cubic term averages the coefficient of a triple over its three choices of anchor pair. The first two bits refer to the two anchor colors, whose coefficients are symmetric. A one bit means R. Only triples of colors that all fail contribute.

The union of two distinct perfect matchings consists of alternating cycles of even length at least four. Its rooted type $i$ records the length of the root cycle followed by the sorted lengths of the other cycles. These are the eleven types in the price file. For a fixed ordered pair of colors, the first matching steps forward from the root to start its cycle. On the other cycles choose any starting vertex and use the same convention. This gives a relabeling to the row representative that preserves both colors and the root. The relabeling may be chosen separately for each anchor pair.

Let $Q_{ik}$ count layouts where both anchors fail and exactly $k$ of them are R. For a third matching $m$, let $T_h$ count layouts in which all three colors fail, with modes given by $h$. Row $i$ supplies integer edge prices $e_i$, transfers $t_{ijk}$ and a correction $\delta_i$. For every perfect matching $m$ disjoint from the anchors the checker verifies

$$
\sum_h a_{6+h}T_h \;\ge\; \sum_{e\in m} e_i(e)+t_{ijk}-\delta_i,
$$

where $j,k$ are the respective rooted types of the two new pairs. To compute the left side, enumerate the layouts once. If both anchors fail, add their P weight to each ordinary six-set and their R weight to each root-four. Subtract the sum of those weights for each possible decomposition into one root-four and two six-sets. Query these arrays on the unions of edges of $m$. The identities for $1_P$ and $1_R$ give exactly the desired incidence. The check covers **7,408,571** third matchings per certificate. It uses every admissible third matching, whether or not it is part of a full factorization.

In an actual factorization, the thirteen third colors use every edge outside the anchors exactly once. Across the three choices of anchor pair of an unordered color triple the transfers have nonnegative sum, checked for every $i,j,k$. Write $E_i$ for the sum of the prices on the available edges. Define

$$
G_i=105\sum_k a_{3+k}Q_{ik}+35(E_i-13\delta_i),\qquad
B=1401400a_0+15(91000a_1+100800a_2).
$$

If $N_i$ of the 105 color pairs have type $i$, summing the score over all layouts gives at least $B+\sum_i N_iG_i/105$. The coefficient 35 is $105/3$ because each triple contributes in three anchor positions. Dividing by $D$ and rounding upward gives a lower bound on the number of target layouts. For the unconditional results use the smallest $G_i$. For the square-cycle result, credit at least 76 pairs with type $(4,4,4,4)$. The full histogram can always be used in the same inequality.

| Target | Lower bound on target layouts | Certificate |
| --- | ---: | --- |
| All two-triple cuts clear | 390,724 | [Integer prices](two-triples.txt) |
| All two-triple cuts clear, at most one root failure | 27,810 | [Integer prices](one-root-prices.txt) |
| Every color connected, at least 76 square-cycle pairs | 105 | [Integer prices](square-pairs.txt) |

## Replay

From this directory, run the independent C++20 checker. It reads only the price files, enumerates every layout and every admissible third matching for each rooted pair, and checks the integer inequalities and final rounding.

```sh
c++ -O3 -std=c++20 check.cpp -o /tmp/wild-pair-cuts
/tmp/wild-pair-cuts two-triples.txt one-root-prices.txt square-pairs.txt
```

The header stores the scale, maximum R, maximum P, required number of special pairs, their type index and the guaranteed layout count. After the coefficients, each type has four lines giving its cycle lengths, numerical counts and gain, 120 edge prices, and an 11 by 11 transfer table in row-major order. An edge $x<y$ has index $y(y-1)/2+x$ and the root is vertex 15.
