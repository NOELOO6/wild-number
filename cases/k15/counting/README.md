# Every starting triple can get down to one possible bad split

**In every coloring on fifteen points, keep any eligible starting triple. At least two groupings of the remaining points pass every connectivity check except possibly one split.** The statement holds on sixteen points after any prescribed choice of the isolated root. It still allows a color to be disconnected across the last split.

| Count on the remaining twelve points | Guaranteed number |
| --- | ---: |
| Groupings into four triples | 15,400 in total |
| Groupings that clear the cuts involving the first triple and all single-group cuts | At least 2,301 |
| Groupings that can contain two or more marked splits | At most 2,299 |
| Groupings passing both tests | At least 2 |

A **marked split** divides the twelve points into two halves, one of which a color pairs entirely inside itself. Each grouping into four triples has three such divisions to check. Two different divisions determine all four triples if their sides meet in threes. This limits the number of groupings that have two marked splits to 2,299, as shown in the [pair-count proof](../two-cuts.md).

The lower bound of 2,301 is the new part. It also means you can rule out any 23 particular splits in advance and still have at least one grouping clearing the first checks. Each particular split occurs in just 100 groupings.

## What Lean checked

A **forbidden triple** is one that a color seals together with the root or together with the chosen first triple. Write $F$ for their set and $m$ for its size. There are 75 occurrences before repetitions are removed. At a point $v$ the original number is $18+3k_v$, where the twelve integers $k_v$ are nonnegative and sum to three. Removing repeat occurrences lowers a point's degree by at most $75-m$. [Derivation from the matching colors](../first-triple.md)

We count partitions into four triples that avoid $F$. For $m\le63$, the earlier two-price calculation already gives at least 2,316. For each of the remaining twelve values of $m$, a finite certificate proves the count is strictly greater than 2,300. Lean rebuilds the 83 patterns used in the count, verifies the integer square expansions, and checks the final inequalities. These are exact integer computations. The counting argument connecting those computations to the graph is given below. [Pattern and price checker](Counting.lean) · [Square checker](Squares.lean)

## How a count can cover every coloring

Take a pattern $H$ of at most four different triples on twelve points. Let $p_H$ be the proportion of relabelings for which every triple of $H$ belongs to $F$. In particular $p_\varnothing=1$ and $0\le p_H\le1$. Write $D_j$ for the pattern of $j$ disjoint triples. Inclusion and exclusion on the four triples of a random grouping gives the exact count

$$N=15400\sum_{j=0}^4(-1)^j\binom4j p_{D_j}.$$

These probabilities obey four kinds of constraints.

1. **Extend a pattern.** Once all its $r$ triples are in $F$, exactly $m-r$ other triples are in $F$. Summing the extended pattern probabilities gives $(m-r)p_H$. When the extra triple must contain a given point, the corresponding number lies between $18-(75-m)$ and 27, less the number of existing pattern triples at that point. This remains valid if the pattern has probability zero.
2. **Prescribe absence.** The probability that some specified pattern triples are present and the others are absent is nonnegative. Expanding the absence conditions gives a sum of signed $p_H$.
3. **Count through a point.** Let $n_{k,d}$ count points with original degree $18+3k$ and final degree $d$. Their total number is 12, their $k$ values sum to three and their degrees sum to $3m$. For $j$ from one to four, $\sum_{k,d}n_{k,d}\binom dj$ counts the choices of $j$ different forbidden triples and a point they all share. On the pattern side the same count sums the number of labeled copies times $p_H$ times the number of common points. Each $n_{k,d}$ is between zero and twelve.
4. **Sum squares.** Mark two disjoint sets of points of prescribed sizes, allowing the first to be empty. Count occurrences of patterns having zero, one or two triples in $F$, distinguishing how their points meet the two marked sets. An integer-weighted sum of these counts has nonnegative square. Summing its square over all placements and averaging over relabelings gives a linear inequality in the $p_H$, because each product uses at most four different triples.

To verify pattern identity, record for each point which pattern triples contain it. Two patterns agree up to relabeling precisely when their twelve records agree as a multiset after a permutation of the triple names. The checker starts with the empty pattern and verifies that adding any new triple to any listed pattern of at most three triples reaches a listed pattern. For a pattern with $s_I$ points of each record $I$ and $a$ permutations of its triple names preserving those counts, the number of distinct labeled copies is $12!/(a\prod_I s_I!)$.

For the square checks, the type of a one-triple pattern records its two marked-set intersection sizes. For two triples it records the size of their intersection and the marked-set counts on their common points and on each separate part. The checker enumerates the placements of the marked sets. For each union pattern $H$, it counts every ordered pair of its subpatterns of size at most two whose union is $H$. Multiplying their two integer weights and the number of labeled copies reconstructs the coefficient of $p_H$. Lean checks all 248 supplied square expansions by this procedure.

The price checker takes a signed linear combination of the identities and nonnegative inequalities. It checks the allowed sign of each multiplier. It charges any negative remaining coefficient at the largest possible value of its variable, either one for $p_H$ or twelve for $n_{k,d}$. Even after this charge, the resulting lower bound exceeds $2300\times10^{44}$, with $10^{44}$ the common denominator. Finding the prices used numerical optimization. Replaying them requires only Lean and the supplied integer data. [Replay instructions](../../../verification/)
