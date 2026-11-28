# Twenty wild edges on K30

Fix any proper 29-coloring of the complete graph on 30 vertices. The counting argument below gives at least **2,211,739,995,828,567** partitions into ten triples for which every color connects the ten triples. Drawing two wild edges in each triple suffices. The universal lower bound gives wild number **20**. The arithmetic certificate uses exact fractions and can be checked with `python3 cases/k30/verify.py`. [Universal lower bound](../../verification/exact/UniversalLower.lean) · [Exact counts](counts.py) · [Certificate](long-prices.txt)

Write $W_t=(3t)!/(6^t t!)$ for the number of unordered partitions into $t$ triples and $p_j=W_{10-j}/W_{10}$ for the probability of prescribing $j$ disjoint triples. Every color is a perfect matching. A closed set is a union of pairs of that matching. If a color disconnects the triples, a smaller component has two or four triples, since each component has an even number of vertices. We first count six-point failures and then twelve-point failures among partitions surviving the first count.

## Six-point failures

Mark a six-set if any color closes it. Counting color labels gives $H=29\binom{15}{3}=13,195$. Let $D$ be the number of surplus labels summed over marked sets, so there are $H-D$ distinct marks. Make a graph on triples by joining disjoint triples whose union is marked. For a uniform partition take the induced graph on its ten triples. Write $e$ for its number of edges, $X$ for the expected number of unordered disjoint edge pairs, and $Y$ for the expected number of unordered adjacent edge pairs. Then $\mathbb E e=10(H-D)p_2$.

The following lower bounds suppress negative right-hand sides by taking the maximum with zero.

$$
 X\ \ge\ 50p_4\big((H-D)3004-3116D\big),\qquad
 Y\ \ge\ \tfrac12 p_3\big(4060\cdot1898-2640D\big).
$$

To check the disjoint bound, for a region of $u$ vertices write $i_c$ for the number of internal pairs of color $c$. Then $\sum_c i_c=\binom u2$, $\max(0,u-15)\le i_c\le\lfloor u/2\rfloor$, and the labelled six-count is $\sum_c\binom{i_c}{3}$. The endpoint chord of the binomial gives upper bounds 3,116, 1,480 and 942 at $u=24,21,18$. The complement of a marked six is closed in at least one color, which has twelve internal pairs there. Distributing the remaining 264 internal edges as evenly as possible among the other 28 colors gives at least $\binom{12}{3}+16\binom{9}{3}+12\binom{10}{3}=3004$ labels. Each surplus label removed is charged to at most 3,116 marks disjoint from its own six. Each ordered pair of disjoint sixes has 100 subdivisions into two prescribed pairs of triples.

For the adjacent bound, fix a triple $A$. Its three internal edges have distinct colors. Each of the other 26 colors contributes one labelled neighboring triple. Each internal-edge color contributes thirteen, consisting of the forced mate of the third point and any of thirteen other outside pairs. This gives 65 labelled neighbors. For an outside vertex $x$ let $b_x$ count the internal-edge colors whose forced mate is $x$. The labelled incidence at $x$ is $6+11b_x$. Indeed three colors send $x$ into $A$, of which $b_x$ are internal-edge colors. Among the three internal-edge colors, one ordinary outside pair contains $x$ unless $x$ is the forced mate, in which case all thirteen neighbors contain it. Thus $\sum b_x=3$ and the sum of squared incidences is at most $27\cdot36+36\cdot11+9\cdot11^2=2457$. For $a$ distinct neighbors at least $a^2+2a-2457$ ordered pairs are disjoint. Counting intersections by a common point overcounts each diagonal pair by two. Since $a\le65$, this is at least $1898-132(65-a)$. Each surplus six-label removes one neighbor for each of its twenty possible center triples. Summing over $\binom{30}{3}=4060$ centers proves the bound. [Lean proof of the K30 incidence bound](WedgeCount30.lean)

Let $M,I,P,S$ count unordered triples of graph edges that form, respectively, a matching, an adjacent pair with a separate edge, a three-edge path, or a three-edge star. Every simple graph on ten vertices satisfies

$$
 {\bf1}_{e>0}\ \le\ e-\tfrac56 x-\tfrac23 y+\tfrac12 M+\tfrac12 I+\tfrac13 P+\tfrac12 S ,
$$

where $x,y$ are its disjoint and adjacent edge-pair counts. For $e>0$, expanding the right side shows this is equivalent to

$$
 2\sum_{uv\in E}(d_u-1)(d_v-1)-\sum_v d_v(d_v-1)
 \ \le\ (e-1)(e-3)(e-4).
$$

For each edge put $a=d_u-1$, $b=d_v-1$. Then $a+b\le e-1$ and $4ab\le(a+b)^2$. For $e\ge8$ the left side is bounded by $e(e-1)(e-3)/2$, which suffices. For $1\le e\le7$ sort the ten degrees. They sum to $2e$, the maximum is smaller than the number of positive degrees, and the largest two sum to at most $e+1$. Bound the sum of the neighboring degrees minus one at each vertex by the sum over its $d_v$ largest other values of $\max(0,d_w-1)$. Enumerating the integer degree lists gives respective upper bounds $0,0,0,0,8,24,30$. [Enumeration](counts.py)

The Lean proof counts the same edge patterns by deletion. Multiply the indicator inequality by six, let $Q=5x+4y$, and let $B=3M+3I+2P+3S$. For a nonempty graph it suffices to prove $6+Q\le6e+B$. Lean checks the graphs with at most five edges up to relabeling. For $e\ge6$, sum the inequality over the $e$ single-edge deletions. Each edge, pair and triple appears in $e-1$, $e-2$ and $e-3$ deletions, respectively. The remaining inequality follows from $Q\ge4\binom e2\ge12(e-1)$. [General deletion lemma](../sieve/EdgeDeletion.lean) · [Five-edge check](MotifFive30.lean) · [Layout bound](LayoutMoments30.lean)

For a fixed wedge of triples, a new adjacent neighbor must lie in the 21 unused points. For an ordinary color its three forced mates must lie there, so there are at most 21 such colors. For each of the three internal-edge colors, the forced mate leaves space for at most ten pairs. Thus at most 51 neighbors are available at any specified triple of the wedge. Prescribing additional disjoint triples now gives

$$
\mathbb E M\le X\,9420p_6/(3p_4),\quad
\mathbb E I\le Y\,14800p_5/p_3,\quad
\mathbb E P\le Y\,51p_4/p_3,\quad
\mathbb E S\le Y\,51p_4/(3p_3).
$$

For $M$ choose two separate edges, then a mark in the remaining eighteen points with one of ten subdivisions. For $I$ choose the wedge, then a subdivided mark in the remaining 21 points. A path extends either leaf and has two wedges. A star extends the center and has three wedges. Substitution in the graph inequality leaves negative coefficients on both $X$ and $Y$, allowing their lower bounds above. Denote the resulting upper bound on six-point loss by $s(D)$. [Exact expression](counts.py)

## Twelve-point failures after the six-point test

Choose a color uniformly and choose six of its fifteen pairs uniformly. Write $L$ for the twelve selected vertices and $R$ for the other eighteen. Partition the sides independently into four and six triples. Let $Y_0,Y_1,Y_2$ count distinct marked pairs of triples having both triples on the left, one on each side, or both on the right. Their ranges are $0$–$6$, $0$–$24$, and $0$–$15$. The calculation below proves

$$
\Pr(Y_0=Y_1=Y_2=0)\le 0.701804+D/18000.
$$

The mixed pairs matter here. A six-set can survive as a union of two triples with three vertices on each side of the twelve-point cut.

For a fixed pair of sides let $X_i$ count colors having $i$ internal edges on the left. The seven counts sum to 29, their first moment is 66, and $X_6\ge1$. For a color of type $i$ write $b=12-2i$ and $j=i+3$ for the number of crossing and right-internal edges. The counts of compatible labelled sixes of the three types are $\binom i3$, $\binom b3+ibj$, and $\binom j3$. Multiply these by $10W_2/W_4$, $(W_3/W_4)(W_5/W_6)$ and $10W_4/W_6$, respectively, to get the three labelled means $f_t(i)$.

Write $x_i=\mathbb E X_i$, $u_t=\mathbb E Y_t$. For a fixed marked six of multiplicity $m$, assign weight $m-1$ to every potential anchor color. Let $d_i$ be the total such weight for anchors with $i$ internal edges on the six. Then $\sum d_i=29D$, $\sum i d_i=15D$, and $d_3\ge2D$. For each such anchor the fifteen edges have endpoint counts $2^i,1^{6-2i},0^{9+i}$ on the six, with exponents denoting multiplicities. Among the six chosen edges of the anchor, count choices having a total of six, three, or zero endpoints on the mark. Divide by $\binom{15}{6}$ and multiply by the corresponding layout factor above. Calling these weights $h_t(i)$ gives $u_t=\sum_i f_t(i)x_i-\sum_i h_t(i)d_i/29$.

For the second moments, distinguish an ordered choice of an outcome and one marked triple-pair of type $t$. Label its two triples by any fixed order within a side, using the left triple first for a mixed pair. The four regions are the two triples and the unused points of the left and right sides. For each color record its matching edge counts $a,b,c,d,f,g,h,x,y,z$ in the upper triangle of the four-region matrix, in row order. Here the lower-case letters name entries of a single signature. Let $v_{t,e}$ be the expected count of colors with signature $e$ summed over distinguished hits of type $t$.

* The $v_{t,e}$ sum to $29u_t$. The sum of each edge-count coordinate is $u_t$ times the number of all graph edges in the corresponding cell. At least $u_t$ of the mass has no edge crossing the original cut.
* For each $i$, the mass of signatures that close the distinguished six and have $i$ left-internal edges is exactly $f_t(i)x_i$. Summing over distinct hits and then over all their closing colors recovers every realized color label.
* Conditional on the two distinguished triples and the sides, the unused triples are uniform on each side. The possible other labelled hits disjoint from the two distinguished triples have counts $\binom{x}{3},\binom{y}{3}+xyz,\binom{z}{3}$. Multiply each by its layout factor on the unused region sizes. A hit sharing one distinguished triple uses its three forced mates if it has no internal matching edge. If it has an internal edge, it uses the one forced mate and an entire matching pair in the chosen region. These counts give $g_k(e)$ in the checker. Hence $\mathbb E[Y_t(Y_k-{\bf1}_{t=k})]\le\sum_e g_k(e)v_{t,e}$. For $t=k=0$, the other six points on the left always form a single pair of triples. Their contribution to the distinct count is at most one. Subtract their labelled term from the bound and add $u_0$ instead. Both upper bounds hold.
* With the sides fixed, put $m_t=\mathbb E[Y_t\mid L,R]$. A six can be closed by at most five colors, since a vertex has only five partners in it. Therefore $\sum_i f_t(i)X_i/5\le m_t\le\sum_i f_t(i)X_i$. The total $v_{t,e}$ over signatures of left type $i$ is $\mathbb E[X_i m_t]$. Bounds on $X_i$ and $m_t$ follow by maximizing or minimizing linear forms on the color-count polytope. After setting aside one closing color, its vertices use at most two other types, with total population 28 and total internal edges 60. For variables $X\in[l,h]$ and $m\in[a,b]$, expand the four products $(X-l)(m-a)$, $(X-h)(m-b)$, $(X-l)(m-b)$ and $(X-h)(m-a)$ with their respective signs. Their expectations give the four product inequalities in the checker.

Finally give each possible integer triple $(Y_0,Y_1,Y_2)$ its probability. These variables are nonnegative and sum to one. Their first and second moments give the left sides of the preceding constraints. The supplied rational prices multiply the constraints with the required signs. After summing, the coefficient of every nonnegative variable dominates its coefficient in $\Pr(Y=0)-D/18000$. The exact sum of the right sides is less than 0.701804. Replay requires no LP solver. [Constraint generator](counts.py) · [Rational prices](long-prices.txt) · [Dual verification](verify.py)

## Final count

The unconditional expected number of twelve-point cuts before deleting any failures is $A=29\binom{15}{6}W_4W_6/W_{10}$. Every partition lost to such a cut after surviving the six-point test is counted at least once by the preceding sampling experiment. The total losing fraction is therefore at most $s(D)+A\min(1,\Pr(Y=0)_{\rm upper})$. The exact calculation for every integer $0\le D\le13,195$ gives a maximum of $605121482350997/606230625000000$, attained by the bound at $D=0$. Multiplying the remaining fraction by $W_{10}$ and rounding up gives the count above.


## Verification

Run `./verification/graph-bounds.sh k30` from the repository root with Lean 4.19.0 and the pinned mathlib release. The theorem `exact_K30` starts from an arbitrary proper 29-coloring. The theorem `winning_partitions_K30` proves the stated count. Both use Lean’s native evaluator for finite tables. The independent command `python3 cases/k30/verify.py` checks the rational prices and the final count using only Python’s standard library. [End-to-end Lean theorems](Exact30.lean) · [Python replay](verify.py)

The proof reconstructs the closed subsets of each matching from its edge counts in four regions. It checks all 705 region signatures and combines the resulting first and second moments with 73 rational prices on 3,520 columns. The graph-to-certificate argument also accounts for repeated closing colors, overlapping marked pairs and the complementary six points on one side. [Matching profiles](CellSpectrum30.lean) · [Local completion counts](ProfileBills30.lean) · [Second moments](SecondMeans30.lean) · [Graph constraints](GraphRows30.lean) · [Price check](CutPrices30.lean)
