# Sixteen wild edges on K24

Every proper coloring of K24 with 23 colors has wild number **16**. At least **33,258,864,925** of the 9,161,680,528,000 unordered partitions into eight triples work for every color. Draw two edges within each triple. The matching of each color connects the eight resulting trees precisely when it crosses every cut of whole triples. The general lower bound gives 16. [Graph reduction](../sieve/EvenTriples.lean) · [Universal lower bound](../../verification/exact/UniversalLower.lean)

Write $W_t=(3t)!/(6^t t!)$ and $p_j=W_{8-j}/W_8$. Prescribing $j$ disjoint triples has probability $p_j$. Every color is a perfect matching, so a smallest component of a disconnected layout has either two or four triples. The following counts bound the loss to six- and twelve-vertex sets together.

## Six-point cuts

Mark a six-set if at least one color closes it. The number of sixes counted with a closing color is $23\binom{12}3=5060$. Let $D$ be the excess of this number over the number of distinct marked sixes. In a layout make a graph on the eight triples by joining two triples when their union is marked. Denote its edge count by $e$ and its numbers of disjoint and adjacent edge pairs by $x,y$. Let $m,i,p,s$ count three-edge subgraphs consisting of a matching, a wedge plus a disjoint edge, a path, or a star, respectively. For every such graph,

$$
42\mathbf1_{e>0}\le 42e-27x-28y+9m+13i+14p+13s.
$$

Lean checks the inequality on small graphs and lifts it by summing over single-edge deletions. For $e\ge7$, the pair penalty is at least $27\binom e2\ge84(e-1)$, which pays for the constant and linear terms in the induction. [Motif inequality on actual colorings](ShortCuts24.lean) · [Eight-vertex inequality](Motifs24.lean) · [Edge deletion](../sieve/EdgeDeletion.lean)

Let $H_r$ count ordered pairs of labelled sixes intersecting in $r$ points, allowing both labels to be the same color. The expected number of graph edges is $10(5060-D)p_2$. A disjoint pair of sixes has 100 compatible pairs of subdivisions. A pair meeting in three points forces those three points and both three-point differences to be blocks. Thus
$$
\mathbb E x\ge 50p_4 H_0-100p_4\cdot780D,\qquad
\mathbb E y\ge p_3 H_3/2-1000p_3 D .
$$
To see the first deduction, remove each surplus copy in turn. In the remaining 18 vertices each color has between six and nine internal edges, and the 23 counts sum to 153. The chord of $\binom j3$ from six to nine gives at most 780 labelled sixes there. For the second deduction there are twenty choices of the common triple. Each triple has at most 50 labelled neighbors. Its three internal-edge colors each give at most ten choices, and the other twenty colors at most one each. [Matching edge counts](../sieve/SixCounts.lean) · [Triple neighbors](../sieve/TripleNeighbors.lean) · [Loss from duplicate labels in both coordinates](DuplicatePairs24.lean)

For a wedge of fixed blocks, 15 vertices remain. Fix a point of a block being extended. There are at most 15 possible external mates for that point among colors with no internal edge in the block. For each of its three internal-edge colors the third point has a forced mate, and at most seven pairs remain available. This gives a bound of 36 extensions. The general bound in a region of size $u$ is $u+3\lfloor u/2\rfloor$. [Restricted neighbors](../sieve/RestrictedNeighbors.lean) Extending either leaf counts each three-edge path twice. Extending the center counts each star three times. Consequently
$$
\mathbb E p\le 36(p_4/p_3)\mathbb E y,\qquad
\mathbb E s\le 12(p_4/p_3)\mathbb E y.
$$

## Disjoint third edges

For a uniformly chosen $u$-set $U$, let $A(U)$ count ordered pairs of distinct marked sixes with union $U$. Let $L(U)$ count labelled sixes contained in $U$. Put $Z_u=\mathbb E[A(U)L(U^c)]$. Counting the possible subdivisions gives
$$
\mathbb E m\le \binom{24}{12}\,1000p_6 Z_{12}/6,\qquad
\mathbb E i\le \binom{24}{9}\,10p_5 Z_9/2.
$$
In the first count the three disjoint edges can be named in six orders. In the second there are two ways to order the edges of the wedge. Each compatible subdivision of the wedge is forced.

For $u=12$, the first six determines its complement inside $U$, so $A(U)\le L(U)$. For $u=9$, the second six must include the other three points of $U$ plus three of the first six. Hence $A(U)\le\min(20L(U),L(U)(L(U)-1))$. Also $\mathbb E A(U)\le H_{12-u}/\binom{24}u$ by counting with labels. The chord bound used above gives $L(U^c)\le220$ for $u=12$ and $L(U^c)\le329$ for $u=9$.

The stronger bound uses the color population $h_j$, the number of colors with $j$ matching edges inside $U$. It satisfies $\sum h_j=23$ and $\sum j h_j=\binom u2$. A color with $j$ inside edges has $j+12-u$ inside the complement. Both $L(U)$ and $L(U^c)$ are therefore linear functions of $h$. For $(u,b)=(12,55),(9,255),(9,270)$ the supplied quadratic polynomial $Q_{u,b}(h)$ dominates
$$
A(U)\max(0,L(U^c)-b).
$$
Lean checks this using the bounds on $A(U)$ for every possible integer population, with 9,820 populations at size twelve and 376 at size nine. It follows that $Z_u\le b\,H_{12-u}/\binom{24}u+\mathbb E Q_{u,b}$. [Polynomials](population-prices.txt) · [Lean population check](Concentration24.lean) · [Regional bound for arbitrary matchings](GraphRegions24.lean) · [Quadratic sum over ordered pairs of colors](PopulationMoments24.lean)

## Two-color counts

Two distinct colors form alternating even cycles. Their half-lengths partition twelve into parts of size at least two, giving 21 types. Let the frequency of each type among ordered pairs of distinct colors be a variable. Conditional on this type, count subsets of size $u$ by the two numbers of internal matching edges. Following the bits around each alternating cycle counts the selected vertices and records an internal edge whenever consecutive bits are one. Multiply the tables of disjoint cycles. This gives the exact means of $h_j$ and $h_j(h_k-\mathbf 1_{j=k})$ needed for the quadratic bounds.

There is also a direct calculation using the two halves of an alternating matching. Choose a subset $X$ of the twelve false endpoints, of size $k$, and let $s$ be the size of its intersection with its cyclic shift. Among the true endpoints, $s$ can complete an edge of either color, $k-s$ each can complete an edge of just the first or just the second, and $12+s-2k$ can complete neither. Selecting true endpoints from these four groups gives the full joint distribution. The Python replay checks all 21 distributions against the cycle recurrence. [Graph-to-subset bijection](HalfProfiles24.lean) · [Four group sizes and subset counts](HalfTable24.lean) · [Exact spectrum of arbitrary color pairs](GraphTable24.lean)

The same types determine $H_0,H_3$. Fix a six made from three edges of the first color. If it contains $j$ full edges of the second color, then $j$, $6-2j$, and $6+j$ second-color edges have two, one, and zero endpoints in the six. Choosing three of them gives every possible partner six. The same-color term uses $j=3$ for each of the 220 first sixes. The Python replay independently forms the two sets of 220 sixes and intersects them directly. [Alternating coordinates for every pair of colors](GraphCycles24.lean) · [Cycle tables](CycleData24.lean) · [Exact overlap count for an arbitrary colored graph](PairCensus24.lean) · [Independent counts](certificate.py)

## Balanced cuts after removing six-point failures

Choose an anchor color and six of its twelve edges uniformly. Their vertices give one side of a cut into two twelve-sets. Choose independent, uniform subdivisions into four triples on each side. Let $Y_0,Y_1,Y_2$ count marked block pairs entirely on the left, across the cut and entirely on the right. The expected number of surviving balanced cut labels per unrestricted layout is
$$
\frac{23\binom{12}6W_4^2}{2W_8}\Pr(Y_0=Y_1=Y_2=0).
$$
The denominator includes two because both sides name the same cut for the closing color. Lean shows that every layout that survives the six-point test but fails a twelve-point test has two distinct oriented witnesses. [Balanced-cut sampling theorem](BalancedSampling24.lean)

Write $X_i$ for the number of colors having $i$ internal edges on the left and $x_i=\mathbb E X_i$. The seven counts sum to 23 and their first moment is 66. The closing anchor has six internal edges on each side. A color of type $i$ has $i$ internal edges on each side and $b=12-2i$ crossing edges. The three numbers of compatible labelled sixes are $\binom i3$, $\binom b3+i^2b$, and $\binom i3$. Their layout factors are $10W_2/W_4$, $(W_3/W_4)^2$, and $10W_2/W_4$, respectively. Denote the products by $f_t(i)$.

For each marked six with $h$ closing colors, assign weight $h-1$ to each of the 23 possible anchors. Let $d_i$ be the total weight where the anchor has $i$ internal edges in the six. Then $\sum d_i=23D$, $\sum i d_i=15D$ and $d_3\ge2D$. The second equality counts the fifteen edges of the six once each. The last inequality holds because every six contributing a surplus has at least two closing colors. For such an anchor its twelve matching edges have two, one or zero ends on the mark with multiplicities $i$, $6-2i$ and $6+i$. Count choices of six edges containing exactly six, three or zero of those ends, divide by $\binom{12}6$ and multiply by the corresponding layout factor. This gives the duplicate weight $b_t(i)$ and the identity $\mathbb E Y_t=\sum_i f_t(i)x_i-\sum_i b_t(i)d_i/23$. The four-region count uses the following facts.

* Expose a marked pair of triples of type $t$ in the sampled layout. Its two triples and the unused vertices on each side form four regions. Record the ten counts of matching edges within and between regions for each color. The sum across colors in each position is exactly the number of edges of the complete graph in that position. At least the anchor has no edge crossing the balanced cut. Counting colors that close the distinguished pair gives the labelled first moments above.
* The unexplored blocks are independent uniform partitions of the unused vertices on each side. Another marked pair either uses two unused blocks or shares exactly one exposed block. A matching closing a union of unused blocks contributes three internal matching edges. For a shared block with no internal edge, all three outside mates are forced. If it has one internal edge, the remaining vertex has a forced mate, and a matching edge supplies the other two points. These alternatives give an upper bound on every factorial second moment $\mathbb E[Y_t(Y_k-\mathbf1_{t=k})]$. When the exposed blocks lie on one side, the other two blocks on that side give at most one distinct complementary marked pair. Remove all its labels in the estimate and add one. The correction applies on either side.
* For a fixed cut, the vector of color counts remaining after setting the anchor aside has total 22 and first moment 60. The vertices of this bounded polytope have at most two occupied coordinates. They give extrema of each $X_i$ and of each labelled first moment. A six can have at most five closing colors, because its fifteen edges contain three per closing color. Dividing the minimum labelled first moment by five bounds the distinct first moment from below. For each of the two quantities, multiply its distances to its lower and upper bounds by those of the other quantity. The four resulting inequalities bound the expected product of $X_i$ and the conditional mean number of hits. The histogram of $(Y_0,Y_1,Y_2)$ is supported on $[0,6]\times[0,16]\times[0,6]$.

The pair-type frequencies supply a further exact constraint on each $x_i$. Restrict the two-color table to twelve-sets with six internal anchor edges. There are $\binom{12}6$ such sets for each anchor. Averaging the companion counts over the 22 other colors and adding the chosen anchor gives $x_i$. [Four-region derivation](../k30/#twelve-point-failures-after-the-six-point-test) · [Balanced-cut rows](CutModel24.lean) · [Independent constraint generator](certificate.py)

The 79 rational multipliers give a total losing fraction at most $78926570703464883969/79214135000000000000$. The remaining fraction times $W_8$, rounded upward, gives the stated number of winning partitions. [Rational multipliers](cut-prices.txt) · [Lean dual certificate and integer rounding](CutPrices24.lean)

## Verification

Run `python3 cases/k24/verify.py` for the exact-arithmetic replay. The Lean target `./verification/graph-bounds.sh k24` checks the eight-vertex inequality, regional population majorants, balanced-cut sampling, cycle arithmetic, linear certificate and rounding. The written argument connects the motif sums and the two-color counts to the rational inequalities. A separate end-to-end Lean theorem proves 16 directly when at least 1,410 of the 5,060 six-set labels are surplus. [Duplicate-label theorem](ShortCuts24.lean) The unrestricted end-to-end Lean theorem for K30 is available separately. [K30 theorem](../k30/Exact30.lean)
