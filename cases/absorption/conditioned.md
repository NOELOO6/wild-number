# Absorption at K47, K53 and K73

Every minimum proper coloring of K47, K53 and K73 has wild number 32, 36 and 49, respectively. K74 has wild number 49 by deleting one vertex from an even coloring, solving the resulting odd coloring, then restoring the deleted vertex and its incident matching edges. At K47 and K53 the pair can be prescribed. At K73 any vertex can be prescribed as the last attachment. [Lower bound and even-order transfer](../../verification/exact/UniversalLower.lean)

| Odd order | Reserved ordinary vertices | Repairable layouts per million, at least | Worst distinct count |
| --- | ---: | ---: | ---: |
| 47 | 2 | 1,910 | 945 |
| 53 | 2 | 39,773 | 1,225 |
| 73 | 1 | 6,447 | 4,731 |

## The reserved block and the forbidden family

Complete the odd coloring with root $z$. Put $r=n\bmod 3$ ordinary vertices in the reserved block, and partition the remaining $u=n-r$ into $t=u/3$ triples. For $r=2$ draw the pair's edge. In both constructions draw a tree on each triple, saving one wild edge for the end. In the pair construction the special color is the pair's color. In the singleton construction the special color is the color of the edge from $z$ to the reserved vertex $x$. Discard the isolated pair or isolated edge $zx$ when counting the special color's outside components. Count each ordinary color's components minus one, and twice the special outside's components minus one, i.e. $2(k-1)$ for $k$ outside components. Denote their sum by $Y$.

If $Y\le1$, the special outside is connected. In every other color the reserved vertices already lie in one component. If one other color has two components, choose an ordinary vertex in the component away from the reserved block. It exists even when that component contains $z$, since $z$ has an ordinary matching partner. A wild edge from the reserved block to this vertex repairs both colors. If every other color is connected, any vertex of the outside works. Delete the auxiliary leaf $z$ afterwards. This uses $2t+r$ wild edges. [Graph repair](AbsorbEdge.lean)

For a pair, forbid a free triple whenever a matching closes it with $z$. For a singleton, forbid it whenever a matching closes it with either $z$ or $x$. Write $s=3-r$ for the number of roots used in this definition, $H$ for the resulting simple triple family, $m=|H|$, and $w$ for its count with root and color labels. For each root separately the full labeled family is a $2$-$(n,3,3)$ design. Even with two roots, each free triple has multiplicity at most three. Each label determines an internal edge of the triple, whose color determines the partner of the remaining vertex. Thus different labels need different internal edges.

Write $N=\binom n2$ and $d_0=3(n-1)/2$. For each root exactly $r$ points of its $n$-point design are omitted from the free region. Hence $w=s[N-rd_0+3\binom r2]$. In a $q$-point subregion, write $b$ for the number of labels and $v$ for the number of distinct triples. With $k=n-q$ and $D=\lfloor 3s(u-1)/2\rfloor$, use
$$
\begin{aligned}
b_{\min}&=\max\{0,\ s[N-kd_0+2\tbinom k2],\ sq\max(0,q-(n+1)/2),\ w-(u-q)D\},\\
b_{\max}&=\min\{s\tbinom q2,\ s[N-kd_0+3\tbinom k2],\ w\},\\
\ell&=\max\{0,\lceil b_{\min}/3\rceil,\ b_{\min}-(w-m),\ m-(u-q)D\},\\
h&=\min\{\tbinom q3,\ b_{\max},\ m-\lceil(w-b_{\max})/3\rceil\}.
\end{aligned}
$$
The design complement identity and the color-by-color internal edge bound give the first two lines. The maximum labeled vertex degree in the free region is at most $D$. The third and fourth lines follow by counting missing labels and repeated labels. In particular $\ell\le v\le h$. [Design count](README.md#removing-rooted-triples-before-counting-cuts)

## Enclosing the avoidance probability

A second computation bounds the fraction $P_0(Q)$ of layouts avoiding $H$ on a region $Q$ of size $q$, given its exact distinct count $a$. A vertex in $Q$ has distinct degree between
$$
d=\left\lceil\max(0,s[d_0-3(n-q)])/3\right\rceil,\qquad
D_q=\min\{\tbinom{q-1}2,\lfloor 3s(q-1)/2\rfloor\}.
$$
Each omitted vertex destroys at most three incidences for each root. The distinct pair degrees are at most $K=3s$. Let $d_i$ and $g_e$ be the distinct vertex and pair degrees in $Q$. Each of their sums is $3a$. For $a>0$ remove a uniformly chosen forbidden triple. The expected remaining number $v$ satisfies
$$
a\mathbb E[v]=a(a-1)-\sum_i d_i^2+\sum_e g_e^2.
$$
Two different triples overlap in zero, one or two points. Counting their common vertices and correcting for common pairs gives the formula. For integers in a common interval with a fixed sum, balancing the entries minimizes their sum of squares. Moving entries toward the two endpoints until at most one lies strictly between maximizes it. Use these two extrema to enclose the mean. Pointwise, removal of a member destroys at most $3D_q-2$ triples and at least $\max(1,3d-3K+1)$. These follow by inclusion-exclusion on the three vertex stars.

Truncate inclusion-exclusion at depth $b\le\min(10,q/3)$. At level $i$, start with one when $i=b$, and otherwise take one minus the sum of the child remainders divided by $(i+1)\binom{q-1}2$, where $q$ is the current region size. Forcing a specified triple costs $1/\binom{q-1}2$ of the remaining partitions. The $i+1$ factor removes the ordering of the choices. Equivalently, the coefficients are the binomial moments of the number of hits. Odd truncations bound $P_0$ from below, and even truncations bound it from above. [Lean binomial moments and Bonferroni inequalities](PartitionMoments.lean)

For each possible child size $v$ keep an interval of values $[L_v,U_v]$. For any chosen slope $c$, the lines with intercepts $\min_v(L_v-cv)$ and $\max_v(U_v-cv)$ enclose all child values. Evaluate these linear bounds at the appropriate endpoint of the mean interval above. This propagates tighter bounds than using the worst individual child. The checker rounds every enclosure outward in units of $10^{-8}$, and intersects the bounds from all truncations. It discards a state only when necessary degree, count or child bounds contradict it. [Integer recurrence](avoidance.cpp)

## Charging the components

A color contracts the marked root and reserved block according to its internal matching edges. The exposed ends of the resulting marked blocks have the following profiles. The special outside receives weight two.

| Reserved size | Color count or weight | Exposed ends by block |
| ---: | --- | --- |
| 2 | $n-3$ generic colors | $(1,2)$ for root and pair |
| 2 | 2 colors joining root to pair | $(1)$ for the joined block |
| 2 | special outside, weight 2 | $(1)$ for the root |
| 1 | $n-1$ generic colors | $(1,1)$ for root and singleton |
| 1 | special outside, weight 2 | no marked block |

Each component contains a free triple. Count components containing $j<t/2$ triples at full weight and those containing $j=t/2$ at half weight. At most one component can have more than half the triples, and two exact halves use up the entire graph. Thus the weighted count dominates the number of components minus one. Omit components with one triple and a single forbidden root. Those components force an $H$ hit.

Fix a profile with $f$ exposed ends, a subset of marked blocks with $a$ exposed ends, and a size $j$. A support consists of the $a$ prescribed free partners and a uniform choice of $b=(3j-a)/2$ of the $k=(u-f)/2$ free matching edges. Every such support admits the same number of connected inside partitions, since permutations of the free pairs identify the supports. For a fixed support and a connected interior, the complementary partition is uniform.

The unconditional mean number of components of this shape is computed by fixing the triple partition and uniformly relabeling the free endpoints of the matching. With $f$ prescribed marked endpoints and $t$ triples there are $(3t)_f(3t-f-1)!!$ matching completions, where $(3t)_f$ is a falling factorial. Choose the $j$ inside triples, count the connected completions on those blocks and the selected marked blocks, then multiply by the unrestricted matching completions outside. Divide by the total completions. The connected count follows by subtracting completions according to the component of a distinguished block. The calculation includes the profile multiplicity and the half weight at equality. [Exact connected counts](../one-extra/piece-moments/check.py)

It remains to bound the mean fraction avoiding $H$ outside the component. On its possible complementary counts $v\in[\ell,h]$, take an affine majorant $B+cv$ of the upper avoidance table with $c\le0$. Check the intercept at every feasible integer. A lower bound on $\mathbb E[v]$ yields an upper bound on the mean avoidance. Also take the constant bound given by the worst table entry.

A forbidden triple is eligible if it avoids all $a$ mandatory inside vertices. At least $m-aD$ triples are eligible. For a generic profile, averaging over its $M=n-\binom{r+1}{2}$ colors also leaves at least $m(1-3a/M)$ eligible. For each specified marked endpoint its partners in those colors are distinct, and their total degree in $H$ is at most $3m$. Let $g$ be the larger of the applicable bounds and zero.

Put $p_i=\binom{k-b}{i}/\binom ki$. A triple meeting $i$ distinct free matching edges survives outside with probability $p_i$. For $0\le i\le3$ one has $p_i\ge p_3+(3-i)(p_2-p_3)$. Indeed $p_i-p_{i+1}$ is the probability of avoiding $i$ specified edges and selecting one further specified edge, which decreases with $i$. Each of the $O=f-a$ mandatory outside vertices gives at least $d_u-aK$ eligible incidences, using the minimum distinct vertex degree $d_u$ at $q=u$. Each such incidence decreases by one the maximum number of different free pairs touched by its triple. Consequently
$$
\mathbb E[v]\ \ge\ \max\{\ell,\ g p_3+\max(0,O(d_u-aK))(p_2-p_3)\}.
$$
The shape mass times its complementary avoidance upper bound dominates its contribution to $\mathbb E[Y\,1_{H\text{ avoided}}]$. Summing the contributions gives $T$. For every integer $m$ between $\lceil w/3\rceil$ and $w$, subtract $T/2$ from the full-region avoidance lower bound. The three minima, rounded down per million, give the table. [Exact rational calculation](small_components.py)

## Replay

Run from this directory with Python 3.10+ and a C++17 compiler supporting the undefined-behavior sanitizer.

```sh
python3 small_components.py
```

The replay rebuilds the integer recurrence in a temporary directory and checks every admissible total count. The graph repair and the identities for actual triple partitions have Lean proofs. The inequalities relating the color profiles to the numerical bounds above use the written argument.
