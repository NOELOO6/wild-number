# Choosing the last wild edge after the triples are drawn

Every minimum proper coloring of **K59, K65 and K71** has wild number **40, 44 and 48**, respectively. The construction works for **any prescribed pair of ordinary vertices**. Set aside that pair, partition all remaining vertices into triples and draw a tree in each block. The last wild edge joins the pair to a triple chosen after inspecting the coloring. The same upper bounds transfer to K60, K66 and K72. [Graph lower bound and even-order transfer](../../verification/exact/UniversalLower.lean)

| Odd order | Free triples | Lower bound on repairable partitions per million |
| --- | ---: | ---: |
| K59 | 19 | 4,472 |
| K65 | 21 | 43,846 |
| K71 | 23 | 73,125 |

A sharper count proves K47 and K53 with any prescribed pair, and K73 with any prescribed singleton. The latter gives K74 as well. [Proof, exact bounds and replay](conditioned.md)

Allowing several cuts at a prescribed singleton proves K55–K56, K61–K62 and K67–K68. [Cut accounting and replay](singleton.md)

## What one edge repairs

Complete the odd coloring with an auxiliary root so that each color is a perfect matching. Write $P$ for the prescribed pair and $p$ for the color of its internal edge. Place the root alone. The two vertices of $P$ form a component in color $p$. Removing that component leaves the outside graph of color $p$. In every color other than $p$, the two vertices of $P$ can reach each other along their wild edge.

For every color other than $p$, count its components minus one. Add twice the number of components minus one in the outside graph of $p$, meaning $2(k-1)$ if the outside has $k$ components. Call the resulting nonnegative integer $Y$. If $Y\le1$, the outside of $p$ is connected. At most one other color has two components. Any vertex in its component away from $P$ is a possible endpoint of the final edge. If that component contains the root, it also contains the root's ordinary matching partner. If every other color is connected, any ordinary vertex outside $P$ works. The root is a leaf in every color, so deleting it preserves all ordinary connections. The cost is $2t+2$ for $t=(n-2)/3$ free triples. [Lean graph repair](AbsorbEdge.lean) · [Odd matching completion](../../verification/exact/MatchingModel.lean)

## Removing rooted triples before counting cuts

Let $U$ be the $u=n-2$ free vertices. Let $H$ be the family of distinct triples in $U$ which a color closes together with the root. Write $m=|H|$. We restrict attention to layouts avoiding all of $H$. If their fraction is at least $L$, and the unconditioned mean of $Y$ multiplied by their indicator is at most $T$, then at least a fraction $L-T/2$ of all layouts avoid $H$ and have $Y\le1$.

Count a triple once per closing color to get its labeled multiplicity. On the full set of $n$ ordinary vertices, each pair $x,y$ belongs to exactly three labeled triples. Use the color on the edge $xy$ and the two colors on the root edges to $x$ and $y$. These are precisely the three choices, and they are distinct. Each triple has multiplicity at most three. The full labeled count is $N=\binom n2$ and each vertex has labeled degree $d=3(n-1)/2$. Removing the prescribed pair leaves exactly $w=N-2d+3$ labels. In particular $\lceil w/3\rceil\le m\le w$.

Fix a subregion $Q\subseteq U$ of size $q$, with $k=n-q$. Suppose that $i$ disjoint, previously chosen forbidden triples are known to lie outside $Q$. Writing $b$ for its labeled count, the following bounds are sufficient.

$$
\max\!\left(0,N-dk+2\binom k2,\ q\max(0,q-(n+1)/2),\ w-(u-q)D\right)
\le b\le
\min\!\left(\binom q2,N-dk+3\binom k2-i,w\right),\qquad
D=\lfloor 3(u-1)/2\rfloor.
$$

For the complement identity, inclusion-exclusion gives $b=N-dk+3\binom k2-b_{\rm out}$, where $i\le b_{\rm out}\le\binom k2$. For the other lower bound, each of the $q$ colors whose root partner is in $Q$ has at least $q-(n+1)/2$ internal edges there. The degree bound $D$ follows by counting pairs through one vertex. If $l,h$ are the displayed lower and upper bounds on $b$, the number of distinct forbidden triples in $Q$ lies between

$$
\max(\lceil l/3\rceil,l-(w-m),m-(u-q)D)
\quad\text{and}\quad
\min(\binom q3,h,m-\max(i,\lceil(w-h)/3\rceil)).
$$

To bound the probability of avoiding all forbidden triples in $Q$, use the inclusion-exclusion sums through odd and even depths up to six. Only disjoint triples can occur together. After forcing $i$ of them, a specified next triple occurs with probability $1/\binom{q-3i-1}{2}$. Choosing an ordered next triple introduces a further divisor $i+1$. Thus a normalized remainder at level $i$ is one minus the sum of the child remainders divided by $(i+1)\binom{q-3i-1}{2}$. Start with one at the last level. At each level enclose the product using the distinct-count bounds and the sign of the child endpoint. Odd truncations give lower bounds and even truncations give upper bounds.

The upper estimate also uses a subfamily of exactly $a$ triples, where $a$ is the guaranteed lower count at the start of the region. With vertex degrees $d_v$ and pair degrees $d_e$, its number of ordered disjoint pairs is
$$
a(a-1)-\sum_v d_v(d_v-1)+\sum_e d_e(d_e-1)
\le a(a+8)-\lceil9a^2/q\rceil.
$$
Here $\sum_v d_v=\sum_e d_e=3a$, $d_e\le3$ and $\sum_v d_v^2\ge9a^2/q$. Also use the upper bound $a(a-1)$. After removing $i$ chosen triples, at least $a-3i\lfloor3(q-1)/2\rfloor$ subfamily members remain. The remaining ambient lower count can drop by at most $h-a$ under thinning. These bounds enclose the terms after the initial disjoint pair. If the upper remainder is nonnegative, multiplying it by the upper pair count gives an upper bound for the even truncation. Avoiding the original family implies avoiding the subfamily.

## Counting the other components

Every relevant component contains a free vertex. For a generic color, the root and both vertices of $P$ match to free vertices. For either color joining the root to $P$, the remaining vertex of $P$ matches outside. In the special color $p$, discard $P$ and count components outside it. The root there also has a free partner. In a color with $k$ components at least $k-1$ of them have at most $\lfloor t/2\rfloor$ free triples. Here $t$ is odd. We can charge all closed sides of these sizes, including sides with more than one component.

For $j$ free triples on the side, let $f$ be the total number of forced free partners of marked vertices, and let $a$ of those be required in the side. There are
$$
\binom{(u-f)/2}{(3j-a)/2}
$$
choices of free support, with zero choices for an invalid or nonintegral lower index. The following table enumerates the possibilities. Entries marked with an asterisk put only the root on the marked side and are omitted at $j=1$, since that free triple would belong to $H$.

| Color | Weighted multiplicity | $f$ | Values of $a$ |
| --- | ---: | ---: | --- |
| All three marked vertices match outside | $n-3$ | 3 | $0,1^*,2,3$ |
| Root joined to one member of $P$ | 2 | 1 | $0,1$ |
| Outside graph in color $p$ | 2 | 1 | $0,1^*$ |

For a fixed support of size $3j$, a uniform triple partition respects the cut with probability $W_jW_{t-j}/W_t$, where $W_j=(3j)!/(6^j j!)$. Conditional on respecting it, the complement has a uniform triple partition. Multiply the weighted count of supports by this probability and by the upper bound on avoiding $H$ in the complement. Sum over $j$ to obtain $T$. All estimates apply separately to every possible integer $m$. Taking the least lower bound on $L-T/2$ yields the table.

## Verification

Run the standard-library Python checker in this directory. It tests all three orders and every admissible value of $m$ with exact fractions.

```sh
python3 pair_bounds.py
```

Lean independently generates the cut masses and inclusion-exclusion bounds using integer numerators and a common denominator at each recursion level. It checks the three lower fractions using its native evaluator. The graph repair theorem uses Lean's ordinary kernel. The counting argument linking an arbitrary coloring to these estimates is given above. [Lean arithmetic](PairAbsorbNumbers.lean) · [Python checker](pair_bounds.py)
