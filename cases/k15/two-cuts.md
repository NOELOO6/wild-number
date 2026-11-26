# When just one split remains

**Choose any eligible first triple. If at most 63 triples are forbidden among the other twelve points, at least seventeen groupings clear all the first checks and at least two of the final three splits.** If at most 84 splits are marked, at least 22 groupings do this, however many triples are forbidden. A single split can still disconnect colors.

This test uses two numbers. Count a triple or split only once, even if several colors rule it out. A forbidden triple is one that a color seals together with the root or together with the chosen triple. A marked split divides the twelve points into two groups of six, at least one of which a color pairs entirely inside itself. [Definitions and first counts](half-splits.md)

| Number of forbidden triples | Largest number of marked splits covered here |
| ---: | ---: |
| At most 63 | 96, the maximum possible |
| 64 | 94 |
| 65 | 93 |
| 66–70 | 91 |
| 71 | 90 |
| 72 | 89 |
| 73 | 88 |
| 74 | 86 |
| 75 | 84 |

## Why a pair of bad splits is expensive

Two different ways of splitting twelve points into halves can occur in the same four-triple grouping only if one side of the first meets one side of the second in three points. In that case their four intersections are exactly the four triples. A pair of such splits can therefore ruin at most one grouping. Write $B$ for the number of marked splits. The number of pairs meeting in this way is at most

$$\left\lfloor\frac{192B^2/462+8B}{2}\right\rfloor.$$

For $B=84$ this is 1,802. There are at least 1,824 groupings clearing the first checks, leaving at least 22 with at most one marked split. Even at $B=96$ the upper bound is just 2,299.

To verify the bound, index a matrix $A$ by the 462 splits and give it a 1 wherever two splits meet in threes. Let $J$ be the all-ones matrix. The matrix $8I-A+(192/462)J$ has a nonnegative quadratic form. Indeed, define symmetric integer matrices $U,V$ by the table. The distance counts the smaller of the two possible intersection sizes of a side from each split.

| Distance | 0 | 1 | 2 | 3 |
| --- | ---: | ---: | ---: | ---: |
| Entry of $U$ | 90 | 35 | 2 | −9 |
| Entry of $V$ | 60 | −10 | 4 | −3 |

The identities are $U^2=770U$, $V^2=210V$, and $2310(8I-A)+960J=84U+198V$. After a relabeling of the twelve points, a pair of splits depends only on its distance. Lean checks all four representative entries of each identity, summing over all 462 possible middle splits. For any vector $x$, the quadratic form of $U^2$ is the sum of the squares of the entries of $Ux$, and likewise for $V$. Apply the resulting inequality to the vector with ones at the marked splits and zeros elsewhere. Its quadratic form for $A$ counts each compatible pair twice. [Lean matrix and arithmetic checks](TwoCuts.lean)

## The count when some forbidden triples coincide

The two numerical prices in the [half-split proof](half-splits.md) give stronger counts if fewer distinct triples are forbidden. One small improvement is enough for the table. Let $h$ count surplus occurrences, $z$ be the maximum number lost at one point, and $c=\min(z,h+9-z)$. The losses at the other eleven points sum to $v=3h-z$ and are at most $c$ each. Their squared sum is at most $\lfloor v/c\rfloor c^2+(v\bmod c)^2$ for $c>0$. Moving a unit from a smaller positive entry to a larger entry below capacity increases the sum of squares. When $c=0$ all these losses vanish. Also $z\le27$ by the original degree bound.

Lean checks the resulting finite bounds for every possible number of forbidden triples. For up to 63 it gives at least 2,316 groupings passing the first checks. Subtracting 2,299 leaves at least seventeen. The other rows follow from the same comparison. The reduction from color connectivity and the sum-of-squares argument are written here. [Lean verification](TwoCuts.lean)
