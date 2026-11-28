# Clearing every ordinary two-triple cut through a prescribed triple

Fix **any** triple $T$ in **any** minimum proper coloring of K15. At least **844** of the 15,400 partitions containing $T$ clear every ordinary two-triple cut. This allows two other specified triples to be forbidden as blocks and still leaves at least **284** partitions, since each prescribed disjoint triple occurs in 280. The same statements apply on K16 after prescribing the singleton root as well as $T$. Root-four cuts remain possible.

Complete to 16 points with root $z$. Let $f$ be the number of colors closing $T\cup\{z\}$. The bounds for each $f$ are as follows.

| $f$ | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
| Partitions through $T$ clearing all ordinary two-triple cuts | 844 | 1,521 | 2,204 | 2,892 |

## Counting the marks

On the twelve remaining vertices $Z$, mark a triple $U$ if a color closes $T\cup U$. Let $e$ be the number of distinct marked triples. Mark a split of $Z$ into two six-sets if some color closes at least one side, and let $b$ be the number of distinct marked splits. An ordinary cut occurs exactly when a partition uses a marked triple or one of its three induced splits is marked.

There are three colors with a matching edge in $T$ and three with an edge from $T$ to $z$, overlapping in $f$ colors. Each of the $G=9+f$ colors with neither incidence matches $T$ to one partner triple in $Z$. Each of the $3-f$ colors with only an internal edge of $T$ contributes five triples formed by its forced partner and one of five disjoint matching edges. Thus there are $a=24-4f$ labeled triple marks. There are $9+f,6-2f,f$ colors with respectively zero, one and two edges inside the four-point frame $T\cup\{z\}$. Such a color has respectively four, five or six matching pairs in $Z$. Choosing three gives $l=96+4f$ labeled sides before identifying repeated marks of the same split.

For a partition into four triples of $Z$, write $x$ for the number of its marked triples and $y$ for the number of its marked splits. Write $I$ for the number of pairs of a marked triple and a marked split containing that triple on one side. Write $g$ for the number of unordered pairs of marked splits with a three-point intersection of their sides. Then
$$
\sum x=280e,\qquad \sum y=100b,\qquad \sum xy=10I,\qquad \sum\binom y2=g.
$$
One triple leaves nine points to partition. A fixed split gives ten subdivisions on each side. A compatible triple and split fix one side's subdivision and leave ten choices. Two distinct compatible splits determine all four triples by their intersections.

## Lower bounds for the two intersection counts

For a marked triple $U$, fix a color closing $T\cup U$. Among the other nine points of $Z$ this color has four matching edges. Summed over the other fourteen colors the number of matching edges there is $\binom92-4=32$. The least sum of $\binom i3$ at this edge total is four, by the increasing differences $\binom i2$. Including the chosen color gives at least eight labeled sides disjoint from $U$.

The three vertices of $U$ send twelve edges to the frame. At most twelve colors occur among those edges, so at least three colors match all vertices of $U$ inside $Z$. Each of these gives a labeled six-set containing $U$. If no two vertices of $U$ are matched together, its three pairs give the side. If two are matched together, its two forced pairs can be extended by another pair since at least four matching pairs lie in $Z$. This proves a total of at least eleven labeled sides per marked $U$ that contain it or avoid it. If $U$ comes from one of the $G$ colors that match all of $T$ to $U$, three of the twelve edges from $U$ to the frame have the same color. At least five colors then match $U$ inside $Z$, improving eleven to thirteen. At least $(e-(a-G))_+$ distinct $U$ have this improvement.

Passing from labeled sides to distinct splits discards $l-b$ labels. In a fixed split each of the $G$ ordinary partner colors can lose at most one triple incidence. For each forced-partner color, a contained marked triple has to use one of its five disjoint edges in the same half as its forced vertex. At most two such edges fit beside it. Thus a discarded label loses at most $\min(e,G+2(3-f))=\min(e,15-f)$ incidences. In total
$$I\ge\max\{0,11e+2(e-(a-G))_+-(l-b)\min(e,15-f)\}.$$

For $g$ index matrices by all 462 splits and write $A$ for adjacency by three-point intersection. Put $K=21A+420\operatorname{Id}-10J$, where $J$ is the all-ones matrix. For distance $0,1,2,3$ the entries of $K$ are $410,-10,-10,11$. With $V$ having entries $60,-10,4,-3$ at these distances, one has $588K=K^2+378V$ and $V^2=210V$. Every ordered pair of splits at a given distance is equivalent under a permutation of the twelve vertices. Lean sums over all 462 middle splits for a representative at each distance. Both squares have nonnegative quadratic form, so $K$ does too. Applying it to the marked-set indicator yields $42g+420b\ge10b^2$. [Gram checks](PrescribedCuts15.lean) · [Split representatives and the square of V](../TwoCuts.lean)

## Counting survivors

For $0\le x\le4$ and $0\le y\le3$,
$$3\,1_{x=y=0}\ \ge\ 3-3x-3y+2\binom y2+xy.$$
Summing bounds the number of survivors from below by
$$15400-280e-100b+\left\lceil(2g+10I)/3\right\rceil.$$
Substitute the two integer lower bounds, then check $0\le e\le a$, $0\le b\le l$ for each $f$. Lean verifies the pointwise inequality, numerical table and deduction of the four lower bounds. The reduction from an arbitrary coloring to the counts is the argument above. [Lean certificate](PrescribedCuts15.lean)

This complements the unrestricted count of 390,724 clear partitions and the bound of 27,810 that also connect at least fourteen colors. Those counts allow the five triples to vary. [Unrestricted counts](README.md)
