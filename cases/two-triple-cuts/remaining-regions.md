# Avoiding closed six-sets on both sides at K69

For every minimum proper edge coloring of K69 or K70 the wild number is **46**. We count partitions of the 69 ordinary vertices into 23 triples in the completed one-factorization. The first-moment charges for a rooted triple, an ordinary six-set, and a longer connected component use the notation and bounds of the K75 proof. Three refinements give a lower bound of **1,000 winning partitions per million** at K69. [Basic counting argument](README.md) · [Exact rational bounds](remaining_regions.py)

## Repeated six-sets

Keep one label for each distinct six-set and put $D=L-E$ for the number of discarded labels. For a fixed pair of colors two distinct common six-sets are disjoint. Their intersection and its complement within either six-set are closed under both matchings and have even size. A common two-set would require the same edge in two different colors. At order $n+1=6s+4$ there are thus at most $s$ common ordinary six-sets, and attaining $s$ forces the four remaining vertices, including the root, to be closed in both colors. The number of color pairs admitting such a four-set is $R=\sum_{T\in H}\binom{f_T}{2}$, where $f_T\in\{1,2,3\}$ counts its labels. In fact a pair has only one cycle through the root. Since $\sum f_T=w$, we have $R\le\min(w,3(w-m)/2)$. Summing over color pairs counts a six-set with $h$ labels $\binom h2\ge h-1$ times. Consequently $D\le(s-1)w+R$. Lean proves the disjointness and the implication at equality for arbitrary factorizations. [Lean matching proof](CommonSixes.lean)

Write $s_\pm=J_\pm(n-6)$ and $r_\pm=J_\pm(n-12)$ for the bounds on **labeled** six-sets of a specified region. The number $P$ of ordered disjoint pairs of distinct supports satisfies
$$L s_- - 2D s_+ \le P \le Ls_+ -2D s_- +D^2.$$
Start with all ordered labeled pairs, remove pairs having a discarded label in each position and restore pairs removed twice. For the upper bound on exterior forbidden counts in the K75 argument, write $v_0,v_1$ for their range at $n-12$. Each discarded first label contributes at least
$$\delta=\max\{0,v_{\min}(n-6)J_-(n-9)-v_0s_+\}$$
to the sum of $v-v_0$ over labeled ordered pairs. Each forbidden triple outside its six-set has at least $J_-(n-9)$ second labels avoiding both. Removing both positions and allowing for double removal therefore reduces the earlier upper bound by at least $\max(0,2D\delta-D^2(v_1-v_0))$.

## Three disjoint sets and sets sharing one triple

Write $P_-,P_+$ for lower and upper bounds on $P$. The count of ordered triples of mutually disjoint supports lies in $[Q_-,Q_+]$, where
$$
\begin{aligned}
Q_- &= \max\{P_-\max(\lceil r_-/5\rceil,r_--D),\ Ls_-r_- -3D s_+r_+\},\\
Q_+ &= \min\{P_+\min(E,r_+),\ Ls_+r_+\}.
\end{aligned}
$$
These follow by choosing a third support after two or by removing discarded labels in each position. Write $N$ for the number of disjoint pairs consisting of one forbidden triple and one labeled six-set, computed from the two-design in the basic argument. Summed over the labeled disjoint triples of six-sets, the number $v$ of forbidden triples in their common exterior is at least $V=N J_-(n-9)J_-(n-15)$. Choose a forbidden triple and then the three ordered disjoint labels successively.

Let $v_{\max}$ be the maximum exterior forbidden count at $n-18$. The total of $v_{\max}-v$ over distinct ordered triples is at most $v_{\max}Ls_+r_+-V$, since the summands are nonnegative. Divide by $Q_-$ to obtain a lower bound on the distinct mean $v$ when $Q_->0$. Apply the upper affine avoidance bound there and multiply by $Q_+$. A second bound applies the same affine estimate to all labels with mean at least $V/(Ls_+r_+)$, then subtracts at least $(Ls_-r_--Q_+)_+$ discarded terms times the minimum lower avoidance bound. Multiply the smaller bound by $1000W_{t-6}/W_t$.

For a pair of six-sets meeting in a realized triple $C$, the other two realized triples must be disjoint. On a layout avoiding $H$ there are at most $\binom n3-m$ choices for $C$. Each such $C$ has $g=n-6+3(k-2)$ labeled partner triples. Each of three internal-edge colors provides $k-2$ partners through its forced vertex, so two partners from the same such color cannot be disjoint. This leaves at most $g(g-1)-3(k-2)(k-3)$ ordered choices per $C$. A second upper bound for their total is $(20E-h_*)(g-1)$, by first choosing a support with its shared triple. Each forbidden triple contained in that support removes one of its twenty choices. The third six-set of this configuration avoids all nine vertices and has at most $J_+(n-9)$ choices. Its ten subdivisions account for the factor $10W_{t-5}/W_t$. Use the exterior avoidance upper bound at $n-15$.

## Longer connected components

For a connected side on $j\ge3$ triples, let $q=n-3j$, $r=q/3$, and $p=10W_{r-2}/W_r$. The earlier charge allows the exterior partition to contain closed six-sets. Such layouts were already excluded. For any fixed exterior $Q$ let $X_Q$ count its realized six-sets, and $Z_Q$ denote avoidance of its forbidden triples.

There are at least $e_-=\max(\lceil J_-(q)/5\rceil,J_-(q)-D)$ and at most $e_+=\min(E,J_+(q))$ supports in $Q$. Their total number of internal forbidden triples is at most
$$h=\min\{H_*,v_{\max}(q)[n-3+3\lfloor(q-4)/2\rfloor]\}.$$
In each non-internal-edge color, a triple has at most one extension. In each of its three internal-edge colors an extension chooses a matching edge on the points left after its two forced pairs. A subdivision hits any given internal forbidden triple with probability $1/10$. Thus $A= p\, l(q-6)(e_- - h/10)_+$ bounds $\mathbb E[X_Q1_{Z_Q}]$ from below, where $l$ is the uniform lower avoidance bound. For its second falling factorial moment an upper bound is
$$
 B=p e_+\left[J_+(q-6)\frac{10W_{r-4}}{W_{r-2}}u(q-12)
 +\frac{2[n-6-4/10+(24/10)\lfloor(q-6)/2\rfloor]}{\binom{q-7}{2}}u(q-9)\right],
$$
where $u$ is the uniform upper bound. These are the disjoint and shared-triple cases of the basic proof, now within $Q$. For each nonnegative integer $y$ an integer chord gives
$$\Pr(X_Q>0,Z_Q)\ge I=\max\{0,[(2y+2)A-B]/[(y+1)(y+2)]\}.$$
Indeed $x(2y+3-x)\le(y+1)(y+2)$ for every positive integer $x$ and is zero at $x=0$.

We can also exclude a forbidden triple **inside** the selected component. Let $a=j\bmod2$, $b=(3j-a)/2$ and $p_i=\binom bi/\binom ki$. Conditional on the choice of matching edges in the support, a specified contained forbidden triple is a block with probability $1/\binom{3j-1}{2}$. For a triple with $f$ root labels, $n-6+f$ colors have neither the root mate nor an internal edge there, $3-f$ have just an internal edge and $3-f$ have just the root mate. In the last type the support must include the root. In a color with both incidences the triple and root already form a separate component. The respective probabilities of containment in the first three types are $p_3,p_2,a p_2$.

After fixing this triple as a block, let $C_0,C_1,C_2$ be the probabilities that the inside stays connected for those three types. Count completions on $j-1$ other triples. The distinguished endpoint groups are $(3)$ or $(1,3)$ for the first type, and $(1)$ or $(1,1)$ for the second, with the extra group in the rooted case. For the third type contract the root edge to obtain the group $(2)$ in the rooted case. Distinguished endpoints all match to unmarked endpoints. Divide the connected count by the count of completions for that profile. With $C$ the unconditional connected fraction inside the selected support,
$$
 s=\frac{[m(n-6)+w]p_3 C_0+(3m-w)p_2(C_1+a C_2)}
 {n j\binom{3j-1}{2}C}
$$
bounds the probability of at least one interior forbidden block given a connected side, averaged over its color and support. Division by $j$ allows for every interior block being forbidden. [Matching completion recurrence](../one-extra/piece-moments/check.py)

For each fixed support the interior and exterior partitions are independent. An interior hit eliminates every exterior avoiding $H$, including those without a six-set. Without an interior hit we can still eliminate probability at least $I$ on the exterior. Hence the saving relative to the earlier component charge is its mass times $I+s\max(0,l(q)-I)$. Summing over component sizes gives the final lower bound. Exact interval arithmetic controls the full integer ranges of $m$ and $E$. The finite computations and matching counts are accompanied by the written argument above. The factorization lemmas and the underlying finite-partition inequalities are checked in Lean.

```sh
python3 six_sets.py 69 --per-million 1000
```

A surviving partition gives 46 wild edges. Deleting the added root preserves connectivity of each color, and restoring the vertex after restricting an even coloring gives the same upper bound at K70. The universal lower bound gives equality. [Lower bound and transfer](../../verification/exact/UniversalLower.lean)
