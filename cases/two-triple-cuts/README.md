# Simultaneous two-triple cuts at K75

Every minimum proper coloring of K75 and K76 has wild number **50**. At least **1,500 per million** partitions of the 75 ordinary vertices into triples connect every color when a tree is drawn on each triple. This settles the conjecture at every order $n\ge71$ together with the previous K71–K74 counting results and the Lean theorem for $n\ge77$. [K71](../absorption/) · [K73 and K74](../absorption/conditioned.md) · [Uniform Lean theorem](../sieve/AllLarge.lean)

The argument below uses $n=75$, $k=(n-1)/2$ and $t=n/3$. The finite checker also accepts other odd multiples of three between 21 and 75, so the inequalities can be tested at smaller orders.

## The events to count

Add a root to complete the odd coloring to perfect matchings. In a uniform partition into triples, let $Z$ mean that no block forms a closed set with the root in any color. Let $H$ be the family of these prohibited triples and let $m=|H|$. It has $w=\binom n2$ labels and each triple has at most three. The exact directed-rounding bounds give lower and upper probabilities for avoiding $H$ on any subregion, indexed by its size and its number of distinct triples. Use the region constraints and the upper and lower affine enclosures described in the previous proof. [Rooted design and avoidance recurrence](../absorption/conditioned.md)

Let $J$ be the set of ordinary six-sets closed by at least one color. Write $E=|J|$, $L=n\binom k3$ for its labeled count, and $X$ for the number of members of $J$ that are unions of whole triples of the partition. Each member has at most five labels, since different closing colors use disjoint sets of three of its fifteen edges.

On $Z$, a disconnected color has a component containing $j$ free triples with $2\le j\le\lfloor t/2\rfloor$. Each component must contain a free triple, and the only possible one-triple component would close with the root. A two-triple component is exactly a realized member of $J$. Count components with $j\ge3$ as a separate loss. When $X>0$, charging every one of the $X$ realized six-sets overcharges by $X-1$. We retain this credit.

## The first moments

Write $W_b=(3b)!/(6^b b!)$. One specified six-set is realized with probability $p=10W_{t-2}/W_t$, and two specified disjoint six-sets with probability $p'=100W_{t-4}/W_t$. Conditional on these events, each six-set has ten equally likely subdivisions and the remaining partition is uniform.

For $j$ triples a connected smaller side contains the root when $a=j\bmod2$ is one. The free support uses $b=(3j-a)/2$ of the $k$ ordinary matching edges, together with the root partner when $a=1$. The checker obtains the mean number of such components by choosing $j$ blocks, counting the connected matching completions inside and arbitrary completions outside, then multiplying by $n$. These are the same connected matching counts used in the singleton argument. [Component enumeration](../one-extra/piece-moments/check.py)

Put $p_i=\binom{k-b}i/\binom ki$. The mean number of forbidden triples left outside the chosen support is at least
$$
 m(1-3a/n)p_3 + (p_2-p_3)
 \begin{cases}
   6m/n & a=0,\\
   (3m-w)/n & a=1.
 \end{cases}
$$
For $a=0$, each forbidden triple has three colors matching one of its vertices to the root and three internal edge colors. Each incidence saves one free matching pair that the outside must avoid losing. A triple meeting $i$ such pairs survives with probability $p_i\ge p_3+(3-i)(p_2-p_3)$. For $a=1$ discard every triple containing the mandatory inside partner. This leaves mean $m(1-3/n)$. Exactly $w$ of the $3m$ internal-edge incidences also have the root partner in their triple. Multiply the upper affine avoidance bound at this mean by the component mass. This gives the long loss for $j\ge3$ and an initial labeled upper charge $U$ at $j=2$.

Let $h_S$ count the forbidden triples in a six-set $S$. Summed over labeled closed six-sets it has the exact value
$$
 H_* = m[n-6+3(k-2)]-w(k-3).
$$
For a forbidden triple with $f$ labels, three colors meet the root there and three contain an internal edge. Exactly $f$ do both. Each of the $n-6+f$ colors doing neither extends it to one closed six-set. Each of the $3-f$ internal-edge colors without a root partner there extends it in $k-2$ ways.

For a six-set with multiplicity $s\ge2$, at most $15-3s\le9$ internal edges can label a forbidden triple. Each internal edge determines at most one such triple through the partner of the root in its color. Hence $\sum_{S\in J} h_S\ge h_*:=\max(H_*/5,H_*-9(L-E))$. A random subdivision of $S$ hits one of its forbidden triples with probability at least $h_S/20$. Each forbidden triple occurs in one subdivision and each subdivision contains two triples. With $l_6,u_6$ the minimum lower and maximum upper avoidance bounds on an $(n-6)$-set, the first-moment charge for distinct six-sets on $Z$ is therefore at most
$$
 \min\{U-p l_6(L-E),\ E p u_6\} - p l_6 h_*/20 .
$$
The subtraction for duplicate labels only uses avoidance on the complement, because the initial labeled charge ignored all inside hits.

## Credit from disjoint six-sets

In a layout with $X$ realized six-sets, give each realized $S$ the number $d_S$ of other realized six-sets disjoint from it. Thus $d_S<X$. Let $A$ be the mean of $\sum_S d_S$ times the indicator of $Z$, and $B$ the corresponding mean of $\sum_S d_S(d_S-1)$. For each integer $y\ge0$ the credit is at least
$$
 \mathbb E[(X-1)_+1_Z]\ \ge\ \frac{(2y+1)A-B}{(y+1)(y+2)}.
$$
Indeed $\sum_S d_S/(1+d_S)\le(X-1)_+$. The line $[2(y+1)-d]/[(y+1)(y+2)]$ lies below $1/(1+d)$ for every nonnegative integer $d$, since $(d-y)(d-y-1)\ge0$. Multiply by $d$ and sum. Lean proves the resulting finite inequality without division. [Lean overlap credit](DisjointSixCredit.lean)

For a region of $q$ ordinary points let $J_-(q),J_+(q)$ bound its number of labeled closed six-sets. In each color write $i_c$ for the number of matching edges internal to the region. Then $\sum_c i_c=\binom q2$, with $\max(0,q-(n+1)/2)\le i_c\le\lfloor q/2\rfloor$. The labeled count is $\sum_c\binom{i_c}{3}$. Its lower bound balances the $i_c$ as evenly as possible. Its upper bound takes as many endpoints of their common allowed range as possible, with at most one intermediate entry. These operations follow from the increasing first differences $\binom i2$.

Each $S\in J$ has between $s_-=\max(\lceil J_-(n-6)/5\rceil,J_-(n-6)-(L-E))$ and $s_+=\min(E,J_+(n-6))$ disjoint neighbors. Write $P_-=E s_-$. For ordered disjoint pairs the total interior loss from hitting $H$ in either six-set is at most $D_*=2s_+H_*/10$, in units of pairs. For the outside region of size $n-12$, let $l$ be the minimum of its lower avoidance table, $u$ the maximum of that lower table and $v_0,v_1$ the least and greatest feasible forbidden counts. This already gives $A\ge p'l(P_- - D_*)$.

For a sharper estimate let $c+bv$ be a minorant of that lower table with $b\le0$. The labeled six-sets form a two-design with vertex degree $d_1=(n-1)\binom{k-1}2$ and pair degree $d_2=\binom{k-1}2+(n-3)(k-2)$. For the pair degree, use the edge's own color, the two colors matching a vertex to the root, and the remaining colors. Inclusion-exclusion shows that the number of pairs consisting of a forbidden triple and a disjoint labeled six-set is $mL-m(3d_1-3d_2)-H_*$. Given such a pair, at most $J_+(n-9)$ labeled six-sets avoid both. Let $V$ be the product of these two bounds. Over ordered distinct disjoint six-set pairs, the mean outside forbidden count satisfies
$$
 \bar v\le\min\{v_1,\ v_0+[V-v_0LJ_-(n-6)]/P_-\}.
$$
To see this, sum the nonnegative excess $v-v_0$ over all labeled pairs. The sum of $v$ is at most $V$, and there are at least $LJ_-(n-6)$ labeled pairs. Restrict to one representative for each distinct pair. The resulting sharper lower bound on $A$ is $p'[P_-\max(l,c+b\bar v_{\rm upper})-uD_*]$. The checker takes the better of both lower bounds and zero.

For $B$ fix an ordered pair $(S,T)$ of disjoint realized members. A third member $R$ disjoint from $S$ either avoids $T$ or shares one of its two triples. In the first case there are at most $J_+(n-12)$ choices, each with conditional realization probability $10W_{t-6}/W_{t-4}$. Multiply by the maximum upper avoidance bound on $n-18$ remaining points.

In the second case choose one of the two triples $C$ of $T$. On $Z$ it is not root-marked. There are $n-6$ colors with neither an internal edge of $C$ nor the root partner in $C$, each giving at most one other triple. There are three internal-edge colors, each giving at most $\lfloor(n-12)/2\rfloor$ other triples. Fix one closing color of $T$. It cannot also close $R$, because the odd intersection $C$ would be closed. In four of the ten subdivisions it has no internal edge of $C$, and in six it does. These fractions apply to both triples and follow by choosing one end of each of three matching pairs. Thus the average number of candidates for each shared triple is at most
$$
 n-6-4/10+(3-6/10)\lfloor(n-12)/2\rfloor .
$$
The remaining triple occurs with conditional probability $1/\binom{n-13}2$. Multiply by two choices of shared triple and the upper avoidance bound on $n-15$ other points. The two cases together bound the expected third choices given $S,T$ and their subdivisions. Multiply by $p' E s_+$ to bound $B$.

## Verification

Subtract the long loss and first-moment six-set charge from the full-region avoidance lower bound, then add the disjoint-pair credit. The checker visits every possible integer $m$. For $E$ it bisects the full interval $[\lceil L/5\rceil,L]$ until the bounds hold throughout each subinterval. Lower endpoints bound pair counts and upper endpoints bound charges as indicated in the code. All probabilities outside the directed-rounding avoidance tables are exact fractions.

```sh
python3 six_sets.py --per-million 1500
```

A winning partition uses $2t=50$ wild edges. The augmented root is a leaf in every color, so deleting it preserves connectivity. Restoring the extra vertex of an even coloring transfers the upper bound to K76. The graph lower bound gives equality at both orders. The overlap inequality and partition identities are formalized in Lean. The intervening matching and probability argument is the written proof above. [Exact checker](six_sets.py) · [Partition identities](../absorption/PartitionMoments.lean) · [Lower bound and transfer](../../verification/exact/UniversalLower.lean)
