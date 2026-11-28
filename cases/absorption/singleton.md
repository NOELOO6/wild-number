# A prescribed last vertex at K55, K61 and K67

The wild numbers of K55 and K56 are 37, of K61 and K62 are 41, and of K67 and K68 are 45, for every minimum proper coloring. Fix any ordinary vertex $x$ of the odd graph. A uniform partition of the other $n-1$ vertices into triples has the following guaranteed chance of accepting $x$. Draw two wild edges in each triple and one from $x$ to the chosen triple. [Graph lower bound and even-order transfer](../../verification/exact/UniversalLower.lean)

| Odd order | Free triples | Repairable partitions per million, at least |
| ---: | ---: | ---: |
| 55 | 18 | 2,109 |
| 61 | 20 | 37,888 |
| 67 | 22 | 64,864 |

## Which cuts constrain the endpoint?

Add the auxiliary root $z$ to complete the matchings. Keep both $z$ and $x$ as singletons for now. Call a free triple $z$-marked if a color closes it together with $z$, and $x$-marked if a color closes it together with $x$. Work on layouts with no $z$-marked block. Write $H$ for the family of all $z$-marked triples and $m=|H|$.

In the special color $zx$, discard the isolated edge $zx$ and charge twice the outside component count minus two. For every other color with $k$ components charge $k-1$, with one exception. Charge zero when it has exactly two components and the component containing $x$ consists of $x$ and one free triple $T$. Call such a cut easy. If an endpoint lies outside $T$, it repairs this color. Let $D$ be the sum of the charges. Call a block excluded if it is $x$-marked. This includes every block that an easy cut rules out.

If $D=0$, any vertex in a block that is not excluded connects every color. If $D=1$, the special outside is connected and exactly one color has a two-component cut that is not easy. Its component away from $x$ must contain a block that is not excluded for this sufficient test to succeed. Using a vertex there repairs that color and all the easy cuts. On the original graph, adding a single edge from $x$ to $y$ works precisely when every color has at most two components and $y$ lies outside the component of $x$ in every disconnected color. [Lean endpoint criterion](AbsorbEdge.lean)

Let $B$ count closed sides away from $x$ in nonspecial colors with between two and $t-2$ free triples, all excluded, where $t=(n-1)/3$. Each cut with $D=1$ has a far side of these sizes. A single free triple alone is odd and cannot close. Closing one triple with $z$ is forbidden. A complementary single triple with $x$ would be easy. If every triple is excluded, call this event $A$. With $Z$ the event of avoiding $H$, one obtains
$$
\Pr(\mathrm{repairable})\ \ge\ \Pr(Z)-\tfrac12\mathbb E[(D+B)1_Z]-\Pr(A).
$$
Indeed, a failing layout in $Z$ outside $A$ either has $D\ge2$ or has $D=1$ and $B\ge1$. The root is a leaf after attachment, so deleting it preserves connectivity.

## Counting the hard cuts

Use the same connected matching counts and complementary avoidance bounds as in the prescribed-block proof. For each of the $n-1$ nonspecial colors the marked profile has two exposed ends, one for $x$ and one for $z$. For the special outside the profile has no marked end and weight two. Count components with fewer than $t/2$ free blocks at full weight and those with exactly half at half weight. Omit a component consisting of one marked singleton and one triple. The case with $z$ cannot occur on $Z$. Omitting an $x$ component gives the desired zero charge when its outside is connected.

When there is an $x$ component of this form and its outside disconnects, add a correction. For a fixed generic color let $k=(n-3)/2$ be the number of free matching pairs. Its $x$-triple consists of the partner of $x$ and one of the $k$ pairs. The expected number of such components over all generic colors is $(n-1)k/\binom{n-2}{2}$. After fixing one, the outside has $t-1$ free triples and a single exposed end at $z$. Count its small connected components with the same half-weight rule, omitting the forbidden $z$-triple. If this outside is disconnected it contributes at least one on $Z$. Together the two counts dominate $D$ on every layout in $Z$.

For this correction, treat the $x$-triple and the small outside component as one support when applying the avoidance bound to the rest. The combined support has one more triple and one more mandatory matching partner than the small component alone. Its free pairs form a uniform subset of the original $k$ pairs by permutation symmetry. This justifies the same bound on the mean number of forbidden triples left in its complement. [Component weights and exact checker](singleton_cuts.py) · [Complementary avoidance argument](conditioned.md#charging-the-components)

## Counting a fully excluded far side

Write $u=n-1$, $M=n-1$ and $w=Mk$. Both the $z$- and $x$-marked families have $w$ labels. Fix a nonspecial color. A closed far side of $j$ triples excludes $x$ and its partner. It includes $z$ and its partner precisely when $a=j\bmod2$ is one. It uses $b=(3j-a)/2$ of the free matching pairs. The unconditional expected number of such sides is
$$
 M\binom kb\,W_j W_{t-j}/W_t,\qquad W_t=(3t)!/(6^t t!).
$$
Here a closed side may have several components. Conditional on its support, the inside and outside triple partitions are independent.

On $Z$, every excluded block belongs to the family of triples that are $x$-marked and not $z$-marked. If every inside block is excluded, a uniformly chosen inside block belongs to this family. It is uniformly distributed over the $\binom{3j}{3}$ triples of the support. To bound the mean family size on the support, put $p_i=\binom bi/\binom ki$. A triple using three distinct free matching pairs has probability $p_3$ to be included. There are at most $w$ candidate triples.

A candidate can require only two pairs if it contains a matching edge of this color or includes the forced inside partner of $z$. For each candidate there are three internal edge colors. At least one matches its third vertex to $x$ and therefore gives an ineligible triple on the far side. This leaves at most $2w$ internal-edge incidences over the $M$ colors. The partners of $z$ across the generic colors are all distinct, giving at most $3aw$ incidences of the second kind. A candidate cannot have both, since that would close it with $z$. Ineligible candidates can be discarded. Thus the conditional fraction of inside partitions with all blocks excluded, averaged over generic colors and their supports, is at most
$$
 \min\left(1,\frac{w p_3+(2+3a)w(p_2-p_3)/M}{\binom{3j}{3}}\right).
$$
Multiply by the side mass and by the maximum upper avoidance probability on the complement. Sum over $2\le j\le t-2$ to bound $\mathbb E[B1_Z]$.

If all free triples are excluded, the first four blocks of a random ordering are excluded. With $q$ free points left, at most $\binom q2$ distinct triples are $x$-marked, by the pair-degree bound three. The next block is uniform among $\binom q3$ triples. Multiplying these four upper bounds gives the allowance for $\Pr(A)$.

## Replay

From this directory run the following exact checker. It tests every possible $m$ and rounds the resulting lower bounds down.

```sh
python3 small_components.py --singleton
```

The endpoint criterion and the partition moment identities have ordinary-kernel Lean proofs. The cut accounting above connects those identities to the exact rational and directed-rounding calculations. [Numerical replay](small_components.py) · [Partition identities](PartitionMoments.lean)
